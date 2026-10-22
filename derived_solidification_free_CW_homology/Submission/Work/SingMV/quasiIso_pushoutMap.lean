import Mathlib
import Submission.Blueprint.Interfaces
import Submission.Work.SINGMV.QuasiIso
import Submission.Work.SingMV.acyclic_coker_pushout

/-!
# The Mayer–Vietoris comparison map for an open cover is a quasi-isomorphism

For a topological space `X` and open subsets `U V ⊆ X` with `U ∪ V = X`, the canonical map

`pushoutMap X U V : pushout (C(U∩V) → C(U)) (C(U∩V) → C(V)) ⟶ C(X)`

of `Submission.Work.SINGMV.Defs` (with `C = singC` the integral singular chain complex) is a
quasi-isomorphism. This is Hatcher, Proposition 2.21 ("small simplices"), in the form needed by
area SINGMV.

## Proof

The map is a monomorphism (`mono_pushout_desc`) whose image is the subcomplex of `(U,V)`-small
chains, and its cokernel is acyclic (`acyclic_coker_pushout`, proved by the barycentric
subdivision / Lebesgue number argument). By `quasiIso_of_acyclic_coker`, a monomorphism of chain
complexes of modules with acyclic cokernel is a quasi-isomorphism: the long exact homology
sequence of the short exact sequence `0 → P → C → Q → 0` degenerates, so the homology map is both
mono and epi.

Both ingredients are already available in the shared library, so the present file only records
the composition as a single named statement.
-/

namespace Work.SingMV

/-- **Mayer–Vietoris (small simplices) for singular chains, one open cover at a time.** For open
`U, V ⊆ X` with `U ∪ V = X`, the canonical comparison map from the pushout of the singular chain
complexes of `U` and `V` along `U ∩ V` to the singular chain complex of `X` is a
quasi-isomorphism. -/
theorem quasiIso_pushoutMap (X : TopCat) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = Set.univ) : QuasiIso (Work.SingMV.pushoutMap X U V) :=
  quasiIso_of_acyclic_coker X U V (acyclic_coker_pushout X U V hU hV hUV)

end Work.SingMV
