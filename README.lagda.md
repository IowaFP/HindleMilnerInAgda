# Algorithms 𝒲 and ℳ in Agda
Implementation of Hindley-Milner type inference algorithms 𝒲 (Milner 1978) and ℳ (Lee
and Yi 1998). Available for reference as algorithms.

## Notices

The algorithm is (probably) sound but not strictly safe.

- I use a named variable representation, which is prettier to write but not exactly kosher. In particular:
  - Variable freshening is unsafe (must be either non-terminating, obtuse, or non-exhaustive)
  - Have to rename under bindings to avoid variable capture
  It might be interesting to formalize with a locally nameless representation (see Charguéraud (2012)),
  as algorithms 𝒲 and ℳ require the generation of "new" type variables, which the
  locally nameless style provides via "atoms".
- The [unification algorithm](./agda/Unification) is not structurally recursive, and so requires a TERMINATING pragma.

## Todo
- Refactor to either De Bruijn or locally-nameless. 
  - May be interesting to have intrinsically-scoped locally nameless syntax. Has anyone tried that?
- Implement algorithm ℳ. (Woops.)
- Find a way to make 𝒰 structurally recursive.
- None of the data are intrinsically verified; might be worthwhile to see if the output can produce
  an intrinsically-typed derivation.
- Add recursive functions via a LFP operator.
- Refactor away from `Vars = List Var` to a Set (avoids uniqueness check).

# Relevant literature 

- Lee and Yi. Proofs about a Folklore Let-Polymorphic Type Inference Algorithm. 1998.
  - https://kwangkeunyi.snu.ac.kr/paper/98-toplas-leyi.pdf
- Robin Milner. A theory of type polymorphism in programming. Journal of
  Computer and System Sciences, pages 348–375, 1978
- Luis Damas and Robin Milner. Principal type schemes for functional programs.
  In Proceedings of the 9th ACM SIGPLAN-SIGACT symposium on Principles of
  programming languages, POPL ’82, pages 207–212, Albuquerque, NM, 1982. ACM
- Simplifying and Improving Qualified Types, Mark P. Jones, Research Report
  YALEU/DCS/RR-1040, Yale University, New Haven, Connecticut, USA, June
  1994.
- Mark P. Jones. Formal properties of the Hindley-Milner type system. Personal
  communication, 1995.
- Oukseh Lee and Kwangkeun Yi. Proofs about a folklore let-polymorphic type
  inference algorithm. ACM Trans. Program. Lang. Syst., 20(4):707–723, 1998.
  doi: 10.1145/291891.291892. URL https://doi.org/10.1145/291891.291892
- Arthur Charguéraud. The locally nameless representation. J. Autom. Reason., 49 (3):363–408, 2012. doi: 10.1007/s10817-011-9225-2
- John C. Reynolds. The meaning of types from intrinsic to extrinsic semantics.
  BRICS Report Series, 7(32), Jun. 2000. doi: 10.7146/brics.v7i32.20167. URL
  https: //tidsskrift.dk/brics/article/view/20167
- Mitchell Wand. Type inference for record concatenation and multiple
  inheritance.  Inf. Comput., 93(1):1–15, 1991
