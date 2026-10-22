import Mathlib
import Submission.Blueprint.Interfaces
import Submission.Work.SINGMV.Defs
import Submission.Work.SINGMV.QuasiIso
import Submission.Work.SingMV.quasiIso_pushoutMap

/-!
# AREA SINGMV — small simplices: singular Mayer–Vietoris

This is the main file of the area. It contains the deliverable

`Work.SingMV.singMV_prop : Submission.Blueprint.SingMVProp`

i.e. Hatcher's Proposition 2.21 ("small simplices"): for open `U, V ⊆ X` with `U ∪ V = X`, the
map from the pushout of the singular chain complexes of `U` and `V` (glued along `U ∩ V`) to the
singular chain complex of `X` is a quasi-isomorphism.

The mathematical content, and where it lives:

* `Submission/Work/SINGMV/Defs.lean` sets up the barycentric subdivision of the fundamental
  simplex (`Sd`), the subdivision operator on singular chains (`sddeg`), the coning operator
  (`coneChain`), the chain homotopy between `sd` and the identity (`homChain`, `homdeg`,
  `homPow`) and the submodule of `(U,V)`-small chains (`smallSpan`, `smallChain`), as well as the
  pushout map `pushoutMap`.
* `SingMV/sdIter_mesh.lean`, `SingMV/exists_delta_small.lean`, `SingMV/exists_small_chain.lean`:
  the mesh of the iterated barycentric subdivision tends to `0`, and, by the Lebesgue number
  lemma, every chain becomes `(U,V)`-small after sufficiently many subdivisions.
* `SingMV/homPow_spec.lean`, `SingMV/sd_preserves_small.lean`,
  `SingMV/homdeg_preserves_small.lean`, `SingMV/exists_small_cycle_rep.lean`,
  `SingMV/exists_small_boundary.lean`: the chain homotopy `sd ≃ id` preserves small chains, which
  gives the two halves of the comparison with the small-chain complex.
* `SingMV/mono_pushout_desc.lean`: the pushout map is injective, i.e. its image is exactly the
  subcomplex of small chains.
* `SingMV/acyclic_coker_pushout.lean`: the cokernel of the pushout map is acyclic.
* `Submission/Work/SINGMV/QuasiIso.lean`: an acyclic cokernel of a monomorphism is a
  quasi-isomorphism.
-/

open CategoryTheory Limits

noncomputable section

namespace Work.SingMV

/-- **Singular Mayer–Vietoris via small simplices.** For open `U, V ⊆ X` covering `X`, the
pushout of the singular chain complexes of `U` and `V` along `U ∩ V` computes the singular chains
of `X`: the canonical map is a quasi-isomorphism. -/
theorem singMV_quasiIso (X : TopCat) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = Set.univ) : QuasiIso (pushoutMap X U V) :=
  quasiIso_pushoutMap X U V hU hV hUV

/-- **AREA SINGMV.** Mayer–Vietoris (small simplices) for singular chains on open covers:
the chains of `U` and `V` glued along `U ∩ V` compute the chains of `X`. -/
theorem singMV_prop : Submission.Blueprint.SingMVProp :=
  fun X U V hU hV hUV => singMV_quasiIso X U V hU hV hUV

end Work.SingMV
