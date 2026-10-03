/-
# The spatial tail bound for the smoothing operator `smoothOp`

The smoothing operator of Proposition `lip` of Krause--Mirek--Tao is

`F x = (smoothOp w G Q) x = ∑_m w(m) G(x - Q m)`.

This module proves the **tail estimate** used in the `N`-large case of `peluseLipL1Tail`:
for every `B : ℕ`,

`∑_{|x| > B} ‖F x‖ ≤ ∑_m ‖w m‖ (∑_{|y + Q m| > B} ‖G y‖)`,

i.e. the mass of `F` outside the ball of radius `B` is controlled by the mass of `G` outside
the *shifted* balls, weighted by the absolutely summable weight `w`.

The proof is the elementary one: bound `‖F x‖` pointwise by `∑_m ‖w m‖ ‖G (x - Q m)‖`
(absolute convergence), restrict the sum over `x` with `|x| > B`, interchange the two
summations and reindex the spatial variable by the translation `x ↦ x - Q m`.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.lipDefs

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators

namespace Work.KMTAreas.A4

/-- The pointwise bound on the smoothing operator: `‖smoothOp w G Q x‖` is bounded by the
absolutely convergent series `∑_m ‖w m‖ ‖G (x - Q m)‖`. -/
theorem norm_smoothOp_pointwise_le {w G : ℤ → ℂ} (hw : Summable fun m : ℤ => ‖w m‖)
    (hG : Summable fun x : ℤ => ‖G x‖) (Q : ℤ) (x : ℤ) :
    ‖smoothOp w G Q x‖ ≤ ∑' m : ℤ, ‖w m‖ * ‖G (x - Q * m)‖ := by
  classical
  set Sg : ℝ := ∑' y : ℤ, ‖G y‖ with hSg
  have hGle : ∀ y : ℤ, ‖G y‖ ≤ Sg := by
    intro y
    rw [hSg]
    exact Summable.le_tsum hG y (fun j _ => norm_nonneg _)
  have hφsum : Summable (fun m : ℤ => ‖w m‖ * ‖G (x - Q * m)‖) := by
    refine Summable.of_nonneg_of_le (fun m => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun m => mul_le_mul_of_nonneg_left (hGle _) (norm_nonneg _)) (hw.mul_right Sg)
  have hnorm : Summable (fun m : ℤ => ‖w m * G (x - Q * m)‖) :=
    hφsum.congr (fun m => (norm_mul _ _).symm)
  have h1 := norm_tsum_le_tsum_norm hnorm
  have h2 : (∑' m : ℤ, ‖w m * G (x - Q * m)‖) = ∑' m : ℤ, ‖w m‖ * ‖G (x - Q * m)‖ :=
    tsum_congr (fun m => norm_mul _ _)
  rw [smoothOp]
  exact h1.trans_eq h2

theorem smoothOpTailLe {w G : ℤ → ℂ} (hw : Summable fun m : ℤ => ‖w m‖)
    (hG : Summable fun x : ℤ => ‖G x‖) (Q : ℤ) (B : ℕ) :
    (∑' x : ℤ, (if B < x.natAbs then ‖Work.KMTAreas.A4.smoothOp w G Q x‖ else 0))
      ≤ ∑' m : ℤ, ‖w m‖ * (∑' y : ℤ, (if B < (y + Q * m).natAbs then ‖G y‖ else 0)) := by
  classical
  set Sg : ℝ := ∑' y : ℤ, ‖G y‖ with hSg
  set S : ℤ → ℝ := fun m => ∑' y : ℤ, (if B < (y + Q * m).natAbs then ‖G y‖ else 0)
    with hSdef
  -- the tail mass is nonnegative, summable and bounded by the total mass of `G`
  have hSsumm : ∀ m : ℤ,
      Summable (fun y : ℤ => (if B < (y + Q * m).natAbs then ‖G y‖ else 0)) := by
    intro m
    refine Summable.of_nonneg_of_le (fun y => ?_) (fun y => ?_) hG
    · by_cases h : B < (y + Q * m).natAbs <;> simp [h]
    · by_cases h : B < (y + Q * m).natAbs <;> simp [h]
  have hSnonneg : ∀ m : ℤ, 0 ≤ S m := by
    intro m
    rw [hSdef]
    exact tsum_nonneg (fun y => by by_cases h : B < (y + Q * m).natAbs <;> simp [h])
  have hSle : ∀ m : ℤ, S m ≤ Sg := by
    intro m
    have h := hSsumm m
    rw [hSdef, hSg]
    exact Summable.tsum_le_tsum (fun y => by
      by_cases h' : B < (y + Q * m).natAbs <;> simp [h']) h hG
  have hTsumm : Summable (fun m : ℤ => ‖w m‖ * S m) :=
    Summable.of_nonneg_of_le (fun m => mul_nonneg (norm_nonneg _) (hSnonneg m))
      (fun m => mul_le_mul_of_nonneg_left (hSle m) (norm_nonneg _)) (hw.mul_right Sg)
  -- the pointwise absolute-convergence bound, for fixed `x`
  have hmulsumm : ∀ x : ℤ, Summable (fun m : ℤ => ‖w m‖ * ‖G (x - Q * m)‖) := by
    intro x
    refine Summable.of_nonneg_of_le (fun m => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun m => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)) (hw.mul_right Sg)
    rw [hSg]
    exact Summable.le_tsum hG (x - Q * m) (fun j _ => norm_nonneg _)
  -- the finitary version of the tail bound
  have hkey : ∀ u : Finset ℤ,
      ∑ x ∈ u, (if B < x.natAbs then ‖smoothOp w G Q x‖ else 0)
        ≤ ∑' m : ℤ, ‖w m‖ * S m := by
    intro u
    -- (1) pointwise bound on `‖smoothOp w G Q x‖`
    have h1 : ∑ x ∈ u, (if B < x.natAbs then ‖smoothOp w G Q x‖ else 0)
        ≤ ∑ x ∈ u,
            (if B < x.natAbs then ∑' m : ℤ, ‖w m‖ * ‖G (x - Q * m)‖ else 0) := by
      refine Finset.sum_le_sum (fun x _ => ?_)
      by_cases h : B < x.natAbs
      · rw [if_pos h, if_pos h]
        exact norm_smoothOp_pointwise_le hw hG Q x
      · rw [if_neg h, if_neg h]
    -- (2) push the indicator inside the inner `tsum`
    have h2 : ∀ x : ℤ,
        (if B < x.natAbs then ∑' m : ℤ, ‖w m‖ * ‖G (x - Q * m)‖ else 0)
          = ∑' m : ℤ, (if B < x.natAbs then ‖w m‖ * ‖G (x - Q * m)‖ else 0) := by
      intro x
      by_cases h : B < x.natAbs
      · rw [if_pos h]
        exact (tsum_congr (fun m => if_pos h)).symm
      · rw [if_neg h]
        exact ((tsum_congr (fun m => if_neg h)).trans tsum_zero).symm
    -- (3) interchange the two summations
    have h3 : ∑ x ∈ u, ∑' m : ℤ, (if B < x.natAbs then ‖w m‖ * ‖G (x - Q * m)‖ else 0)
        = ∑' m : ℤ, ∑ x ∈ u,
            (if B < x.natAbs then ‖w m‖ * ‖G (x - Q * m)‖ else 0) :=
      (Summable.tsum_finsetSum
        (f := fun x m => (if B < x.natAbs then ‖w m‖ * ‖G (x - Q * m)‖ else 0))
        (fun x _ => by
          by_cases h : B < x.natAbs
          · simpa [h] using hmulsumm x
          · simpa [h] using (summable_zero : Summable (fun _ : ℤ => (0 : ℝ))))).symm
    -- (4) factor out `‖w m‖`
    have h4 : ∑' m : ℤ, ∑ x ∈ u,
            (if B < x.natAbs then ‖w m‖ * ‖G (x - Q * m)‖ else 0)
        = ∑' m : ℤ, ‖w m‖ *
            ∑ x ∈ u, (if B < x.natAbs then ‖G (x - Q * m)‖ else 0) := by
      refine tsum_congr (fun m => ?_)
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun x _ => by
        by_cases h : B < x.natAbs <;> simp [h])
    -- (5) the shifted window sum is bounded by the tail mass
    have h5 : ∀ m : ℤ,
        ∑ x ∈ u, (if B < x.natAbs then ‖G (x - Q * m)‖ else 0) ≤ S m := by
      intro m
      have hshift : Summable (fun x : ℤ =>
          (if B < ((x - Q * m) + Q * m).natAbs then ‖G (x - Q * m)‖ else 0)) := by
        have hc := (hSsumm m).comp_injective (Equiv.subRight (Q * m)).injective
        exact hc.congr (fun x => by simp [Function.comp_apply, Equiv.subRight_apply])
      calc ∑ x ∈ u, (if B < x.natAbs then ‖G (x - Q * m)‖ else 0)
          = ∑ x ∈ u,
              (if B < ((x - Q * m) + Q * m).natAbs then ‖G (x - Q * m)‖ else 0) := by
            refine Finset.sum_congr rfl (fun x _ => ?_)
            rw [show (x - Q * m) + Q * m = x by ring]
        _ ≤ ∑' x : ℤ,
              (if B < ((x - Q * m) + Q * m).natAbs then ‖G (x - Q * m)‖ else 0) :=
            Summable.sum_le_tsum u (fun i _ => by
              by_cases h : B < i.natAbs <;> simp [h]) hshift
        _ = S m := by
            rw [hSdef]
            exact Equiv.tsum_eq (Equiv.subRight (Q * m))
              (fun y : ℤ => (if B < (y + Q * m).natAbs then ‖G y‖ else 0))
    -- summability of the intermediate terms
    have hmidsumm : Summable (fun m : ℤ => ‖w m‖ *
        ∑ x ∈ u, (if B < x.natAbs then ‖G (x - Q * m)‖ else 0)) :=
      Summable.of_nonneg_of_le
        (fun m => mul_nonneg (norm_nonneg _) (Finset.sum_nonneg (fun x _ => by
          by_cases h : B < x.natAbs <;> simp [h])))
        (fun m => mul_le_mul_of_nonneg_left (h5 m) (norm_nonneg _)) hTsumm
    calc ∑ x ∈ u, (if B < x.natAbs then ‖smoothOp w G Q x‖ else 0)
        ≤ ∑ x ∈ u,
            (if B < x.natAbs then ∑' m : ℤ, ‖w m‖ * ‖G (x - Q * m)‖ else 0) := h1
      _ = ∑ x ∈ u, ∑' m : ℤ,
            (if B < x.natAbs then ‖w m‖ * ‖G (x - Q * m)‖ else 0) :=
            Finset.sum_congr rfl (fun x _ => h2 x)
      _ = ∑' m : ℤ, ∑ x ∈ u,
            (if B < x.natAbs then ‖w m‖ * ‖G (x - Q * m)‖ else 0) := h3
      _ = ∑' m : ℤ, ‖w m‖ *
            ∑ x ∈ u, (if B < x.natAbs then ‖G (x - Q * m)‖ else 0) := h4
      _ ≤ ∑' m : ℤ, ‖w m‖ * S m :=
            Summable.tsum_le_tsum (fun m => mul_le_mul_of_nonneg_left (h5 m) (norm_nonneg _))
              hmidsumm hTsumm
  have hfin : (∑' x : ℤ, (if B < x.natAbs then ‖smoothOp w G Q x‖ else 0))
      ≤ ∑' m : ℤ, ‖w m‖ * S m :=
    Real.tsum_le_of_sum_le
      (f := fun x : ℤ => (if B < x.natAbs then ‖smoothOp w G Q x‖ else 0))
      (fun x => by by_cases h : B < x.natAbs <;> simp [h]) hkey
  simpa [hSdef] using hfin

end Work.KMTAreas.A4
