#lang scribble/manual

@require[@for-label[zippers
                    racket]]
@(require scribble/eval
          scriblib/autobib)
@(define-cite ~cite citet generate-bibliography)

@(define zipper-paper
   (make-bib
    #:title    "Functional Pearl: The Zipper"
    #:author   (authors (author-name "Gérard" "Huet"))
    #:date     (date 0 0 0 1 9 1997 0 0 #f 0)
    #:location (journal-location "Journal of Functional Programming"
                                 #:pages '(549 554)
                                 #:number 5
                                 #:volume 7)))

@(define derivative-paper
   (make-bib
    #:title    "The Derivative of a Regular Type is its Type of One-Hole Contexts"
    #:date     (date 0 0 0 1 1 2001 0 0 #f 0)
    #:author   (authors (author-name "Conor" "McBride"))
    #:location @list["Unpublished, available " @hyperlink["http://strictlypositive.org/diff.pdf"]{from author}]))

@title{Zippers for Racket}
@author{David Christiansen}

@defmodule[zippers]

A "zipper" is a cursor into an immutable datatype that supports
efficient updates in the immediate vicinity of the focus of
the cursor, and where moving the cursor elsewhere takes time
and allocation linear in the distance moved.

@local-table-of-contents[]

@section[#:tag "zippers-guide"]{Guide}

Huet's Zipper @~cite[zipper-paper] is based on
splitting a datatype into a @italic{focused substructure}
and the @italic{one-hole context} within which the focused
substructure was found. Contexts are represented as reversed
lists, each element of which is analogous to a stack frame
if the focus had been found by a series of recursive calls.

The @racketmodname[zippers] library provides:
@itemlist[@item{A general-purpose zipper abstraction}
          @item{Struct properties for zipper context frames}
          @item{Automated generation of context frames for
           structs}]


Zippers are represented using the struct @racket[zipper].
These zippers can traverse tree structures made up of
structs (or any other value for which the appropriate frame
structures are defined --- see @racket[prop:zipper-frame]
for details). Each type of object that occurs in the tree
structure can provide a means of refocusing the zipper on
one of its child nodes. The refocusing procedures for 
@racket[car] and @racket[cdr] are provided with this library
as @racket[down/car] and @racket[down/cdr]. Additionally,
the focus can be moved upwards to the parent node using 
@racket[up].

@subsection{Implementing Zippers for New Types}
If your datatype is a tree in which the nodes are 
@racket[struct]s, then you can use 
@racket[define-struct-zipper-frames] to generate the
necessary code for instances of that struct to participate
in zippers. If your datatype is not a struct, the you need
to do a bit more work:
@itemlist[@item{Define frame structs for each direction of
           descent. Each frame struct type must have the 
           @racket[prop:zipper-frame] property with an
           appropriate hole-filling procedure.}
          @item{Define descent procedures that place the
           appropriate frame onto a zipper's context stack,
           extracting the relevant substructure to the
           focus. These procedures should raise an exception
           if they are applied to something other than a
           zipper focused on the right kind of value.
           Consider putting the descent procedure into a 
           @racket[zipper-movement] to enable more checks.}
          @item{Optionally define other movements, such as 
           @racket[left/list] and @racket[right/list].}]

@section[#:tag "zippers-reference"]{Reference}

 @(define helper-eval (make-base-eval))
@interaction-eval[#:eval helper-eval
                   (require racket/match racket/set zippers)]

@subsection{Zippers}
@defstruct*[zipper ((focus any/c) (context (list-of zipper-frame?)))]{
 A zipper consists of a focus and a context. The context is
 a list of frames, each of which can reconstruct one level
 of the original tree structure. The frame representing the
 top of the tree is at the end of the list.

 Because it must be possible to reconstruct the original
 tree, the frames must be instances of a @racket[struct] 
 type with property @racket[prop:zipper-frame]. }

@defproc[(zip (focus any/c))
         zipper?]{
 Creates a @racket[zipper] with the identity context and
 the provided value at the focus.

 @examples[
     #:eval helper-eval
     (zip (list 1 2 3))
     (zip '(set (list 1 2) (list 2 3)))
 ]}


@defproc[(edit (f (-> any/c any/c)) (z zipper?))
         zipper?]{
 Returns a new zipper in which the focused value has been
 replaced by the result of applying @racket[f] to the
 previous focused value.

 @examples[
     #:eval helper-eval
     (edit add1
           (zip 1))
 ]}

@defstruct*[zipper-movement ((move (-> zipper? zipper?))
                             (possible? (-> zipper? boolean?)))]{
 A structure representing a zipper movement. A zipper movement consists
 of two procedures: one that implements the movement, and a predicate
 that recognizes zippers within which the movement is possible.
 @racket[zipper-movement] implements the @racket[prop:procedure] type
 property in such a manner as to apply the @racket[move] procedure,
 which means that movements can be applied.

 See @racket[can-move?] for a friendly way to recognize whether a
 @racket[zipper-movement?] can be applied.
 
 All of the movements exported by this package as well as all of those
 generated by @racket[define-struct-zipper-frames] satsify
 @racket[zipper-movement?].

 }

@defproc[(can-move? (move zipper-movement?)
                    (z zipper?))
         boolean?]{
 Recognizes whether the movement @racket[move] is applicable to
 the @racket[zipper] @racket[z] by applying its recognizer procedure.
}

@defproc[(up (z zipper-not-at-top?))
         zipper?]{
 Moves the focus of the @racket[z] one level upward,
 "popping" the context stack.

 @examples[
     #:eval helper-eval
     (define sandwich (zip '(bread peanut-butter jam)))
     sandwich
     (define fillings (down/cdr sandwich))
     fillings
     (up fillings)
 ]
}

@defproc[(rebuild (z zipper?))
         any/c]{
 Reconstructs the value represented by the zipper @racket[z].

 @examples[
     #:eval helper-eval
     fillings
     (rebuild fillings)
     (rebuild (edit reverse fillings))
 ]
}

@defproc[(zipper-at-top? (z any/c))
         boolean?]{
 Returns @racket[#t] if @racket[z] is a zipper with the
 identity context, or @racket[#f] if it is any other value.

 @examples[
     #:eval helper-eval
     sandwich
     fillings
     (zipper-at-top? fillings)
     (zipper-at-top? sandwich)
     (zipper-at-top? 'not-a-zipper)
 ]
}

@defproc[(zipper-not-at-top? (z any/c))
         boolean?]{
 Returns @racket[#t] if @racket[z] is a zipper with a
 non-identity context, or @racket[#f] if it is any other
 value.

 @examples[
     #:eval helper-eval
     sandwich
     fillings
     (zipper-not-at-top? fillings)
     (zipper-not-at-top? sandwich)
     (zipper-not-at-top? 'not-a-zipper)
 ]}

@defproc[(zipper-of/c (c contract?))
         contract?]{
 Takes a contract @racket[c] and returns a new contract that
 accepts zippers focused on values accepted by @racket[c].}

@defproc[(zipper-in/c (c contract?))
         contract?]{
 Takes a contract @racket[c] and returns a new contract that
 accepts zippers whose top-level context frame is accepted by
 by @racket[c].}


@subsection{Context Frames}

@defthing[prop:zipper-frame struct-type-property?]{
 Zipper frames are structs that have an associated method
 for reconstructing the layer of the original tree that they
 represent. The structure type property 
 @racket[prop:zipper-frame] should be set to a two argument
 procedure that, when called with the struct value that
 represents a frame and the old focus, returns the tree node. }

@defproc[(zipper-frame? (obj any/c))
         boolean?]{
 Returns @racket[#t] if @racket[obj] is an instance of a
 structure type with property @racket[prop:zipper-frame], or
 @racket[#f] otherwise.}

@defform[(define-struct-zipper-frames [struct-name ...])
         #:contracts ((struct-name identifier?))]{
 Automatically derives all of the infrastructure necessary
 for the structures named by @racket[struct-name ...] to
 participate in zippers.

 In particular, for each accessor named @racketid[acc]
 associated with each of the structs named in 
 @racket[struct-name ...], a struct @racketid[acc-frame] is
 generated that has every field of @racket[struct-name]
 except the one accessed by @racketid[acc]. The 
 @racket[prop:zipper-frame] structure type property will
 reconstruct the original instance, with the former focus
 replacing the field accessed by @racketid[acc].
 Additionally, a zipper movement @racket[down/acc] is
 generated to descend a zipper along that accessor.

 This is an instance of the product rule 
 @~cite[derivative-paper] when we construe a datatype as
 being the fixed point of a coproduct of functors given by
 @racket[struct]s.

 @examples[
     #:eval helper-eval
     (struct branch (left value right) #:transparent)
     (struct leaf () #:transparent)
     (define-struct-zipper-frames branch leaf)
     (define a-tree (zip (branch (branch (leaf) 12 (leaf)) 15 (leaf))))
     (zipper-focus a-tree)
     (define left-subtree (down/branch-left a-tree))
     (zipper-focus left-subtree)
     (define with-new-left-subtree
       (edit (match-lambda
                [(branch l v r) (branch l (* v v) r)])
             left-subtree))
     (rebuild with-new-left-subtree)
 ]
}

@defform[(struct-zipper-out [struct-name ...])
         #:contracts ((struct-name identifier?))]{

 A provide transformer that exports the identifiers that are generated
 using @racket[define-struct-zipper-frames].  }

@subsection{Zippers for Pairs}

@defstruct*[pair-car-frame ((cdr any/c))]{
 A zipper frame that represents the fact that the previous
 focus was a pair and the zipper descended into its 
 @racket[car].}

@defstruct*[pair-cdr-frame ((car any/c))]{
 A zipper frame that represents the fact that the previous
 focus was a pair and the zipper descended into its 
 @racket[cdr].}

@defproc[(down/car (p (zipper-of/c pair?)))
         zipper?]{
Descend into the @racket[car] of a focused pair.
}

@defproc[(down/cdr (p (zipper-of/c pair?)))
         zipper?]{
Descend into the @racket[cdr] of a focused pair.
}

@subsection{Zippers for Proper Lists}

@defstruct*[list-item-frame ((to-left list?) (to-right list?))]{
 A zipper frame that represents the fact that the previous focus was a
 proper list and that the elements in @racket[to-left] were in reverse
 order to the left of the current focus and the elements in
 @racket[to-right] were in their present order to the right of the
 current focus.
}

@defproc[(down/list-first (l (zipper-of/c pair?)))
         zipper?]{
 Descend into the first element of a focused list.
}

@defproc[(down/list-ref (i exact-nonnegative-integer?))
         zipper-movement?]{
 Descend into element @racket[i] of a focused list.
}

@defproc[(left/list (z (zipper-in/c list-item-frame?)))
         (zipper-in/c list-item-frame?)]{
 When focused on an element of a list, move the focus to the element
 immediately to its left.
}

@defproc[(right/list (z (zipper-in/c list-item-frame?)))
         (zipper-in/c list-item-frame?)]{
 When focused on an element of a list, move the focus to the element
 immediately to its right.
}


@subsection{Zippers for Immutable Sets}

@defstruct*[set-member-frame ((other-members set?))]{
 A zipper frame that represents the fact that the previous
 focus was a set and the zipper descended into one of its
 members.}

@defproc[(down/set-member (element any/c))
         zipper-movement?]{
Descend into @racket[element] in a focused set.
}

@(generate-bibliography)
