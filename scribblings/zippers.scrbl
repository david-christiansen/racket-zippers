#lang scribble/manual

@require[@for-label[zippers
                    racket/base]]
@(require scriblib/autobib)
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

@title{Zippers for Racket}
@author{David Christiansen}

@defmodule[zippers]

A "zipper" is a cursor into a pure datatype that supports
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
If your datatype is a struct, then you can use 
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
           zipper focused on the right kind of value.}]

@section[#:tag "zippers-reference"]{Reference}

@subsection{Zippers}
@defstruct[zipper ((focus any/c) (context (list-of zipper-frame?)))]{
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
 the provided value at the focus. }

@defproc[(edit (f (-> any/c any/c)) (z zipper?))
         zipper?]{
 Returns a new zipper in which the focused value has been
 replaced by the result of applying @racket[f] to the
 previous focused value.}

@defproc[(up (z zipper-not-at-top?))
         zipper?]{
 Moves the focus of the @racket[z] one level upward,
 "popping" the context stack.}

@defproc[(rebuild (z zipper?))
         any/c]{
 Reconstructs the value represented by the zipper @racket[z].}

@defproc[(zipper-at-top? (z any/c))
         boolean?]{
 Returns @racket[#t] if @racket[z] is a zipper with the
 identity context, or @racket[#f] if it is any other value.
}

@defproc[(zipper-not-at-top? (z any/c))
         boolean?]{
 Returns @racket[#t] if @racket[z] is a zipper with a
 non-identity context, or @racket[#f] if it is any other
 value. }

@defproc[(zipper-of/c (c contract?))
         contract?]{
 Takes a contract @racket[c] and returns a new contract that
 accepts zippers focused on values accepted by @racket[c].}

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
 Additionally, a procedure @racket[down/acc] is generated to
 descend a zipper along that accessor.}

@subsection{Zippers for Pairs}

@defstruct[pair-car-frame ((cdr any/c))]{
 A zipper frame that represents the fact that the previous
 focus was a pair and the zipper descended into its 
 @racket[car].}

@defstruct[pair-cdr-frame ((car any/c))]{
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
@(generate-bibliography)
