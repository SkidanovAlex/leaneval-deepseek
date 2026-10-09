import Mathlib
import Submission.Work.SSGRoute.ExtChain.homCoindFreeT_H1_subgroup
import Submission.Work.SSGRoute.ExtChain.deltaH2_restriction
import Submission.Work.SSGRoute.PT.e1cDelta_beta_relation_gen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Injectivity of the connecting map of the canonical resolution, restricted to a subgroup

The reviewed input (P2) of the E1a landing clause (`Work.SSGRoute.E1aClean.NOTE_levelChangeRoute`
§2g, `Work.SSGRoute.PT.NOTE_e1a_square_session10` §2 input 1): for a closed subgroup
`D ≤ Gal(Ω/k)`, the connecting map `δ` of the *dualised canonical resolution*
`e1aSESgen N : 0 → Hom(M, Ωˣ) → Hom(ℤ[G]^n, Ωˣ) → Hom(syzygy, Ωˣ) → 0` restricted to `D` is
injective.  Its kernel is `H¹(D, homCoindFreeT k Ω K N.V)`, which vanishes by the subgroup
Hilbert 90 `Work.SSGRoute.ExtChain.homCoindFreeT_H1_subgroup`
(Shapiro at `D ⊓ Gal(Ω/K)` plus Hilbert 90 at that closed subgroup).
-/

namespace Work.SSGRoute.ExtChain

open SSGRoute.PTExt CategoryTheory

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-- **Injectivity of the restricted connecting map.** -/
theorem deltaH2_restrictSES_e1aSES_injective {k : Type} [Field k] [CharZero k] {Ω : Type}
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] {K : IntermediateField k Ω}
    [FiniteDimensional k K] [IsGalois k K] (N : Rep SSGRoute.PTExt.Coeff (K ≃ₐ[k] K))
    [Finite N.V] (D : Subgroup (Ω ≃ₐ[k] Ω)) (hD : IsClosed (D : Set (Ω ≃ₐ[k] Ω))) :
    Function.Injective
      ((Work.SSGRoute.ExtChain.restrictSES
        (Work.SSGRoute.PT.e1aSESgen (k := k) (Ω := Ω) (K := K) N) D).deltaH2) := by
  haveI hsub : Subsingleton (Work.AbsoluteKummer.H1 ↥D
      (Work.SSGRoute.ExtChain.homCoindFreeT k Ω K N.V)) :=
    Work.SSGRoute.ExtChain.homCoindFreeT_H1_subgroup (k := k) (Ω := Ω) (K := K)
      (ι := N.V) D hD
  have hker := (Work.AbsoluteKummer.SES.range_mapH1_eq_ker_deltaH2
    (Work.SSGRoute.ExtChain.restrictSES
      (Work.SSGRoute.PT.e1aSESgen (k := k) (Ω := Ω) (K := K) N) D)).symm
  intro x y hxy
  have hmem : x - y ∈ ((Work.SSGRoute.ExtChain.restrictSES
      (Work.SSGRoute.PT.e1aSESgen (k := k) (Ω := Ω) (K := K) N) D).deltaH2).ker := by
    rw [AddMonoidHom.mem_ker, map_sub, hxy, sub_self]
  rw [hker] at hmem
  obtain ⟨z, hz⟩ := hmem
  have hz0 : z = 0 := Subsingleton.elim z 0
  rw [hz0, map_zero] at hz
  exact sub_eq_zero.mp hz.symm

/-- The `e1aSES`-spelling of the same statement (the two resolutions are the same
`Classical.choose` witness, so this is definitionally the previous statement). -/
theorem deltaH2_restrictSES_e1aSES_injective' {k : Type} [Field k] [NumberField k] {Ω : Type}
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] {K : IntermediateField k Ω}
    [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (N : Rep SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite N.V]
    (D : Subgroup (Ω ≃ₐ[k] Ω)) (hD : IsClosed (D : Set (Ω ≃ₐ[k] Ω))) :
    Function.Injective
      ((Work.SSGRoute.ExtChain.restrictSES
        (Work.SSGRoute.ExtChain.e1aSES (k := k) (Ω := Ω) (K := K) N) D).deltaH2) :=
  Work.SSGRoute.ExtChain.deltaH2_restrictSES_e1aSES_injective (k := k) (Ω := Ω) (K := K) N D hD

end Work.SSGRoute.ExtChain
