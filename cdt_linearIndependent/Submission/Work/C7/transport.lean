import Mathlib
import Submission.Work.C7.xdefs
import Submission.Work.C7.trans
import Submission.Work.Pure.pure_facts

/-!
# Area C7 — transport of the `y`-ODEs of the pure functions to the `x`-variable

With `y = yps = x²/(x−1)` and `g i = Bᵢ₊₁ ∘ y`, the chain rule
`(Bᵢ ∘ y)' = (Bᵢ' ∘ y)·y'` turns the three `y`-relations of the pure functions

* `2y(4−y)·B₅' = (4−y)B₅ − 2B₂ + 4y`  (`Work.Pure.relation_B5`),
* `y·B₆' = B₃`                         (`Work.Pure.relation_B6`),
* `y·B₇' = B₄`                         (`Work.Pure.relation_B7`),

into the identities announced by the requester (used upstream to reduce the `ℚ(x)`-relation
among `1, L, L², Li₂, J` by removing the two integrals).
-/

namespace Work.C7

open PowerSeries

private lemma yps_hasSubst : PowerSeries.HasSubst Work.C7.yps := Submission.CDT.sympY_hasSubst

private lemma g4_eq : Work.C7.g 4 = Submission.CDTPlan.B5.subst Work.C7.yps := by
  simp [Work.C7.g, Submission.CDTPlan.pureB]
private lemma g1_eq : Work.C7.g 1 = Submission.CDTPlan.B2.subst Work.C7.yps := by
  simp [Work.C7.g, Submission.CDTPlan.pureB]
private lemma g2_eq : Work.C7.g 2 = Submission.CDTPlan.B3.subst Work.C7.yps := by
  simp [Work.C7.g, Submission.CDTPlan.pureB]
private lemma g3_eq : Work.C7.g 3 = Submission.CDTPlan.B4.subst Work.C7.yps := by
  simp [Work.C7.g, Submission.CDTPlan.pureB]
private lemma g5_eq : Work.C7.g 5 = Submission.CDTPlan.B6.subst Work.C7.yps := by
  simp [Work.C7.g, Submission.CDTPlan.pureB]
private lemma g6_eq : Work.C7.g 6 = Submission.CDTPlan.B7.subst Work.C7.yps := by
  simp [Work.C7.g, Submission.CDTPlan.pureB]

/-- `Work.Pure.relation_B5` after substituting `X ↦ yps`. -/
private lemma subst_B5rel :
    2 * Work.C7.yps * (4 - Work.C7.yps) * (PowerSeries.derivative (R := ℚ) Submission.CDTPlan.B5).subst Work.C7.yps
      = (4 - Work.C7.yps) * (Submission.CDTPlan.B5).subst Work.C7.yps
        - 2 * (Submission.CDTPlan.B2).subst Work.C7.yps + 4 * Work.C7.yps := by
  have h := congrArg (PowerSeries.substAlgHom yps_hasSubst) Work.Pure.relation_B5
  simp only [map_mul, map_sub, map_add, PowerSeries.substAlgHom_X, PowerSeries.coe_substAlgHom,
    map_ofNat] at h
  exact h

private lemma two_four_sub_X_ne_zero : (2 : PowerSeries ℚ) * (4 - PowerSeries.X) ≠ 0 := by
  intro hh
  have hc := congrArg PowerSeries.constantCoeff hh
  rw [map_mul, map_sub, map_ofNat, map_ofNat, PowerSeries.constantCoeff_X, map_zero] at hc
  norm_num at hc

/-- `X·B₆' = B₃`, extracted from `Work.Pure.relation_B6` by cancelling the (nonzero) factor
`2(4−X)`. -/
private lemma X_deriv_B6 :
    (PowerSeries.X : PowerSeries ℚ) * PowerSeries.derivative (R := ℚ) Submission.CDTPlan.B6
      = Submission.CDTPlan.B3 := by
  refine mul_left_cancel₀ two_four_sub_X_ne_zero ?_
  rw [← Work.Pure.relation_B6]
  ring

/-- `X·B₇' = B₄`, extracted from `Work.Pure.relation_B7`. -/
private lemma X_deriv_B7 :
    (PowerSeries.X : PowerSeries ℚ) * PowerSeries.derivative (R := ℚ) Submission.CDTPlan.B7
      = Submission.CDTPlan.B4 := by
  refine mul_left_cancel₀ two_four_sub_X_ne_zero ?_
  rw [← Work.Pure.relation_B7]
  ring

/-- `y·(B₆' ∘ y) = B₃ ∘ y`. -/
private lemma subst_B6 :
    Work.C7.yps * (PowerSeries.derivative (R := ℚ) Submission.CDTPlan.B6).subst Work.C7.yps
      = (Submission.CDTPlan.B3).subst Work.C7.yps := by
  have h := congrArg (PowerSeries.substAlgHom yps_hasSubst) X_deriv_B6
  simpa only [map_mul, PowerSeries.substAlgHom_X, PowerSeries.coe_substAlgHom] using h

/-- `y·(B₇' ∘ y) = B₄ ∘ y`. -/
private lemma subst_B7 :
    Work.C7.yps * (PowerSeries.derivative (R := ℚ) Submission.CDTPlan.B7).subst Work.C7.yps
      = (Submission.CDTPlan.B4).subst Work.C7.yps := by
  have h := congrArg (PowerSeries.substAlgHom yps_hasSubst) X_deriv_B7
  simpa only [map_mul, PowerSeries.substAlgHom_X, PowerSeries.coe_substAlgHom] using h

theorem transport :
    (2 * Work.C7.yps * (4 - Work.C7.yps) * PowerSeries.derivative (R := ℚ) (Work.C7.g 4)
        = ((4 - Work.C7.yps) * (Work.C7.g 4) - 2 * (Work.C7.g 1) + 4 * Work.C7.yps)
          * PowerSeries.derivative (R := ℚ) Work.C7.yps) ∧
    (Work.C7.yps * PowerSeries.derivative (R := ℚ) (Work.C7.g 5)
        = (Work.C7.g 2) * PowerSeries.derivative (R := ℚ) Work.C7.yps) ∧
    (Work.C7.yps * PowerSeries.derivative (R := ℚ) (Work.C7.g 6)
        = (Work.C7.g 3) * PowerSeries.derivative (R := ℚ) Work.C7.yps) := by
  refine ⟨?_, ?_, ?_⟩
  · calc 2 * Work.C7.yps * (4 - Work.C7.yps) * PowerSeries.derivative (R := ℚ) (Work.C7.g 4)
        = 2 * Work.C7.yps * (4 - Work.C7.yps)
            * ((PowerSeries.derivative (R := ℚ) Submission.CDTPlan.B5).subst Work.C7.yps
              * PowerSeries.derivative (R := ℚ) Work.C7.yps) := by
          rw [g4_eq, PowerSeries.derivative_subst yps_hasSubst]
      _ = (2 * Work.C7.yps * (4 - Work.C7.yps)
            * (PowerSeries.derivative (R := ℚ) Submission.CDTPlan.B5).subst Work.C7.yps)
              * PowerSeries.derivative (R := ℚ) Work.C7.yps := by ring
      _ = ((4 - Work.C7.yps) * (Submission.CDTPlan.B5).subst Work.C7.yps
            - 2 * (Submission.CDTPlan.B2).subst Work.C7.yps + 4 * Work.C7.yps)
              * PowerSeries.derivative (R := ℚ) Work.C7.yps := by rw [subst_B5rel]
      _ = ((4 - Work.C7.yps) * (Work.C7.g 4) - 2 * (Work.C7.g 1) + 4 * Work.C7.yps)
              * PowerSeries.derivative (R := ℚ) Work.C7.yps := by rw [g4_eq, g1_eq]
  · calc Work.C7.yps * PowerSeries.derivative (R := ℚ) (Work.C7.g 5)
        = Work.C7.yps * ((PowerSeries.derivative (R := ℚ) Submission.CDTPlan.B6).subst Work.C7.yps
              * PowerSeries.derivative (R := ℚ) Work.C7.yps) := by
          rw [g5_eq, PowerSeries.derivative_subst yps_hasSubst]
      _ = (Work.C7.yps * (PowerSeries.derivative (R := ℚ) Submission.CDTPlan.B6).subst Work.C7.yps)
              * PowerSeries.derivative (R := ℚ) Work.C7.yps := by ring
      _ = (Submission.CDTPlan.B3).subst Work.C7.yps * PowerSeries.derivative (R := ℚ) Work.C7.yps := by
          rw [subst_B6]
      _ = (Work.C7.g 2) * PowerSeries.derivative (R := ℚ) Work.C7.yps := by rw [g2_eq]
  · calc Work.C7.yps * PowerSeries.derivative (R := ℚ) (Work.C7.g 6)
        = Work.C7.yps * ((PowerSeries.derivative (R := ℚ) Submission.CDTPlan.B7).subst Work.C7.yps
              * PowerSeries.derivative (R := ℚ) Work.C7.yps) := by
          rw [g6_eq, PowerSeries.derivative_subst yps_hasSubst]
      _ = (Work.C7.yps * (PowerSeries.derivative (R := ℚ) Submission.CDTPlan.B7).subst Work.C7.yps)
              * PowerSeries.derivative (R := ℚ) Work.C7.yps := by ring
      _ = (Submission.CDTPlan.B4).subst Work.C7.yps * PowerSeries.derivative (R := ℚ) Work.C7.yps := by
          rw [subst_B7]
      _ = (Work.C7.g 3) * PowerSeries.derivative (R := ℚ) Work.C7.yps := by rw [g3_eq]

end Work.C7
