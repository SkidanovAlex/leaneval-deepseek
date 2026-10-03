/-
# The `ℓ¹` (Young) bound for the smoothing operator `smoothOp`

The smoothing operator of Proposition `lip` of Krause--Mirek--Tao is

`F x = (smoothOp w G Q) x = ∑_m w(m) G(x - Q m)`.

This module proves that if `w` and `G` are absolutely summable then so is `x ↦ ‖F x‖`, and
that its `ℓ¹` mass is bounded by the product of the `ℓ¹` masses of `w` and `G`:

`∑_x ‖F x‖ ≤ (∑_m ‖w m‖) (∑_x ‖G x‖)`.

This is Young's inequality for the (dilated) convolution, and it is what makes the smoothing
step of Proposition `lip` an `ℓ¹`-bounded operation.  The proof is the classical one: bound
`‖F x‖` by the absolutely convergent series `∑_m ‖w m‖ ‖G (x - Q m)‖`, interchange the two
summations (the inner one is a finite sum over a `Finset`, so the interchange is
`Summable.tsum_finsetSum`), and finally use the translation invariance
`∑_x ‖G (x - a)‖ = ∑_x ‖G x‖` of the `tsum`.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.lipDefs

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory

theorem lipSmoothOpTsumLe {w G : ℤ → ℂ} (hw : Summable fun m : ℤ => ‖w m‖)
    (hG : Summable fun x : ℤ => ‖G x‖) (Q : ℤ) :
    Summable (fun x : ℤ => ‖Work.KMTAreas.A4.smoothOp w G Q x‖) ∧
      (∑' x : ℤ, ‖Work.KMTAreas.A4.smoothOp w G Q x‖) ≤ (∑' m : ℤ, ‖w m‖) * (∑' x : ℤ, ‖G x‖) := by
  classical
  set Sg : ℝ := ∑' x : ℤ, ‖G x‖ with hSg
  set Sw : ℝ := ∑' m : ℤ, ‖w m‖ with hSw
  -- `‖G y‖ ≤ Sg` for every `y`
  have hGle : ∀ y : ℤ, ‖G y‖ ≤ Sg := by
    intro y
    rw [hSg]
    exact Summable.le_tsum hG y (fun j _ => norm_nonneg _)
  -- the summand series is absolutely convergent for every `x`
  have hφsum : ∀ x : ℤ, Summable (fun m : ℤ => ‖w m‖ * ‖G (x - Q * m)‖) := by
    intro x
    have hthis : Summable (fun m : ℤ => ‖w m‖ * Sg) := hw.mul_right Sg
    refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_) hthis
    · exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
    · exact mul_le_mul_of_nonneg_left (hGle _) (norm_nonneg _)
  -- pointwise bound on the operator
  have hpt : ∀ x : ℤ,
      ‖Work.KMTAreas.A4.smoothOp w G Q x‖ ≤ ∑' m : ℤ, ‖w m‖ * ‖G (x - Q * m)‖ := by
    intro x
    have hnorm : Summable (fun m : ℤ => ‖w m * G (x - Q * m)‖) :=
      (hφsum x).congr (fun m => (norm_mul _ _).symm)
    have h1 := norm_tsum_le_tsum_norm hnorm
    have h2 : (∑' m : ℤ, ‖w m * G (x - Q * m)‖)
        = ∑' m : ℤ, ‖w m‖ * ‖G (x - Q * m)‖ :=
      tsum_congr (fun m => norm_mul _ _)
    change ‖∑' m : ℤ, w m * G (x - Q * m)‖ ≤ ∑' m : ℤ, ‖w m‖ * ‖G (x - Q * m)‖
    exact h1.trans_eq h2
  -- the `ℓ¹` bound, tested on finite sets
  have hkey : ∀ u : Finset ℤ, ∑ x ∈ u, ‖Work.KMTAreas.A4.smoothOp w G Q x‖ ≤ Sw * Sg := by
    intro u
    have hGsum_le : ∀ m : ℤ, ∑ x ∈ u, ‖G (x - Q * m)‖ ≤ Sg := by
      intro m
      have hshift : Summable (fun x : ℤ => ‖G (x - Q * m)‖) :=
        (Equiv.summable_iff (Equiv.subRight (Q * m))).mpr hG
      calc ∑ x ∈ u, ‖G (x - Q * m)‖ ≤ ∑' x : ℤ, ‖G (x - Q * m)‖ :=
            Summable.sum_le_tsum u (fun i _ => norm_nonneg _) hshift
        _ = ∑' x : ℤ, ‖G x‖ := Equiv.tsum_eq (Equiv.subRight (Q * m)) (fun x => ‖G x‖)
        _ = Sg := hSg.symm
    have hsu : Summable (fun m : ℤ => ‖w m‖ * ∑ x ∈ u, ‖G (x - Q * m)‖) :=
      (summable_finset_sum u (fun x _ => hφsum x)).congr
        (fun m => (Finset.mul_sum u (fun x => ‖G (x - Q * m)‖) (‖w m‖)).symm)
    calc ∑ x ∈ u, ‖Work.KMTAreas.A4.smoothOp w G Q x‖
        ≤ ∑ x ∈ u, ∑' m : ℤ, ‖w m‖ * ‖G (x - Q * m)‖ := Finset.sum_le_sum (fun x _ => hpt x)
      _ = ∑' m : ℤ, ∑ x ∈ u, ‖w m‖ * ‖G (x - Q * m)‖ :=
            (Summable.tsum_finsetSum (fun x _ => hφsum x)).symm
      _ = ∑' m : ℤ, ‖w m‖ * (∑ x ∈ u, ‖G (x - Q * m)‖) :=
            tsum_congr (fun m =>
              (Finset.mul_sum u (fun x => ‖G (x - Q * m)‖) (‖w m‖)).symm)
      _ ≤ ∑' m : ℤ, ‖w m‖ * Sg := by
            refine Summable.tsum_le_tsum (fun m => ?_) hsu (hw.mul_right Sg)
            exact mul_le_mul_of_nonneg_left (hGsum_le m) (norm_nonneg _)
      _ = Sw * Sg := by
            rw [hSw]
            exact Summable.tsum_mul_right Sg hw
  exact ⟨summable_of_sum_le (fun x => norm_nonneg _) hkey,
         Real.tsum_le_of_sum_le (fun x => norm_nonneg _) hkey⟩

end Work.KMTAreas.A4
