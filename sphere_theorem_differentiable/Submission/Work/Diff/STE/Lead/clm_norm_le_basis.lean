import Mathlib
import Submission.Work.Diff.EXT.splice_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A uniform bound on a continuous linear map from its values on a basis

`Work.Diff.STE.Lead.clm_norm_le_basis`: for a finite dimensional real normed space `E` there is a
constant `K ≥ 0` such that, for every continuous linear map `T : E →L[ℝ] F` and every `R ≥ 0`,
if `‖T (bB i)‖ ≤ R` for all vectors `bB i` of the canonical basis `Module.finBasis ℝ E` of `E`
(the basis used throughout the DeTurck/restart area as `Work.Diff.EXT.bB`), then `‖T‖ ≤ K * R`.

The proof is the coordinate estimate: writing `x = ∑ i, (b.equivFun x i) • bB i` and using
`|b.equivFun x i| ≤ ‖b.equivFun x‖` together with `‖b.equivFun x‖ ≤ D * ‖x‖` for
`D := ‖b.equivFunL‖` (all coordinate functionals of a basis of a finite dimensional space are
bounded, with a bound uniform in `i` since there are finitely many of them), one gets
`‖T x‖ ≤ (finrank ℝ E * D * R) * ‖x‖`, and hence `‖T‖ ≤ finrank ℝ E * D * R` by
`ContinuousLinearMap.opNorm_le_bound`.
-/

open scoped BigOperators

namespace Work.Diff.STE.Lead

theorem clm_norm_le_basis {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
      (T : E →L[ℝ] F) (R : ℝ), 0 ≤ R →
      (∀ p : Fin (Module.finrank ℝ E), ‖T (Work.Diff.EXT.bB (E := E) p)‖ ≤ R) → ‖T‖ ≤ K * R := by
  classical
  -- the canonical basis, and the norm of the coordinate functional of `b`
  set b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := Work.Diff.EXT.bB (E := E) with hb
  set D : ℝ := ‖(b.equivFunL : E →L[ℝ] (Fin (Module.finrank ℝ E) → ℝ))‖ with hD
  have hDnn : 0 ≤ D := by rw [hD]; positivity
  refine ⟨max (Module.finrank ℝ E * D) 0, le_max_right _ _, ?_⟩
  intro F _ _ T R hR hB
  have hK : 0 ≤ Module.finrank ℝ E * D := mul_nonneg (Nat.cast_nonneg _) hDnn
  rw [max_eq_left hK]
  refine ContinuousLinearMap.opNorm_le_bound T (by positivity) (fun x => ?_)
  -- the expansion of `x` in the basis and the bound on its coordinate vector
  have hrepr : x = ∑ i, (b.equivFun x i) • b i := (Module.Basis.sum_equivFun b x).symm
  have hcoe : ‖b.equivFun x‖ ≤ D * ‖x‖ := by
    have h1 := ContinuousLinearMap.le_opNorm
      (b.equivFunL : E →L[ℝ] (Fin (Module.finrank ℝ E) → ℝ)) x
    rw [← hD] at h1
    exact h1
  calc ‖T x‖ = ‖∑ i, (b.equivFun x i) • T (b i)‖ := by
        rw [hrepr, map_sum]; simp
    _ ≤ ∑ i, ‖(b.equivFun x i) • T (b i)‖ := norm_sum_le _ _
    _ = ∑ i, |b.equivFun x i| * ‖T (b i)‖ := by simp [norm_smul]
    _ ≤ ∑ i, |b.equivFun x i| * R :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hB i) (abs_nonneg _))
    _ = (∑ i, |b.equivFun x i|) * R := (Finset.sum_mul _ _ _).symm
    _ ≤ (Module.finrank ℝ E * ‖b.equivFun x‖) * R := by
        apply mul_le_mul_of_nonneg_right _ hR
        have h2 := Pi.sum_norm_apply_le_norm (b.equivFun x)
        calc (∑ i, |b.equivFun x i|) = ∑ i, ‖b.equivFun x i‖ := by simp
          _ ≤ Fintype.card (Fin (Module.finrank ℝ E)) • ‖b.equivFun x‖ := h2
          _ = Module.finrank ℝ E * ‖b.equivFun x‖ := by
              rw [Fintype.card_fin, nsmul_eq_mul]
    _ ≤ (Module.finrank ℝ E * D * R) * ‖x‖ := by
        have h1 : Module.finrank ℝ E * ‖b.equivFun x‖ ≤ Module.finrank ℝ E * (D * ‖x‖) :=
          mul_le_mul_of_nonneg_left hcoe (Nat.cast_nonneg _)
        calc (Module.finrank ℝ E * ‖b.equivFun x‖) * R
            ≤ (Module.finrank ℝ E * (D * ‖x‖)) * R := mul_le_mul_of_nonneg_right h1 hR
          _ = (Module.finrank ℝ E * D * R) * ‖x‖ := by ring

end Work.Diff.STE.Lead
