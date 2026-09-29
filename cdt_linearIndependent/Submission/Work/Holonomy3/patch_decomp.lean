import Mathlib
import Submission.Work.Holonomy3.blocks
import Submission.Work.Holonomy3.intervalIntegrable_comp_div

/-!
# Decomposition of the integral of `h ∘ patched w φ` into its weighted blocks

For weights `w k > 0` summing to `1`, the patched function `patched w φ` is, on the `k`-th block
`[blockStart w k, blockStart w k + w k)`, equal to `circleLog (φ k)` composed with the affine
rescaling of the block onto `[0,1]`.  Consequently, for any test function `h : ℝ → ℝ` whose
composites `h ∘ circleLog (φ k)` are interval integrable on `[0,1]`,

`∫₀¹ h (patched w φ s) ds = ∑ k, w k * ∫₀¹ h (circleLog (φ k) u) du`.

The proof splits `[0,1]` along the prefix sums `bstart w` of the weights (pure additivity of the
interval integral, needing interval integrability of `h ∘ patched w φ`, transferred from the
hypotheses through the affine change of variables `intervalIntegrable_comp_div`), rewrites
`h ∘ patched w φ` on each block up to a null set (`patched_eq_on_Ioo`, `ae_eq_of_eqOn_Ioo`) and
substitutes `u = (s - blockStart w k)/w k` (`integral_comp_add_div`).
-/

open MeasureTheory Set
open scoped BigOperators
open Submission.CDTPlan


namespace Work.Holonomy3

/-- Splitting `∫_{bstart w 0}^{bstart w m}` as the sum of the integrals over the consecutive
blocks `[bstart w k, bstart w (k+1)]`. -/
lemma integral_bstart_eq_sum {n : ℕ} (w : Fin n → ℝ) (f : ℝ → ℝ)
    (hint : ∀ k < n, IntervalIntegrable f volume (bstart w k) (bstart w (k + 1))) :
    ∀ m ≤ n, ∫ x in bstart w 0..bstart w m, f x
      = ∑ k ∈ Finset.range m, ∫ x in bstart w k..bstart w (k + 1), f x := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have hrec := ih (Nat.le_of_succ_le hj)
    have hfirst : IntervalIntegrable f volume (bstart w 0) (bstart w j) :=
      IntervalIntegrable.trans_iterate (a := fun k => bstart w k)
        (fun k hk => hint k (lt_of_lt_of_le hk (Nat.le_of_succ_le hj)))
    have hlast : IntervalIntegrable f volume (bstart w j) (bstart w (j + 1)) :=
      hint j (lt_of_lt_of_le (Nat.lt_succ_self j) hj)
    rw [← intervalIntegral.integral_add_adjacent_intervals hfirst hlast, hrec,
      Finset.sum_range_succ]

/-- **Block decomposition** of the integral of `h ∘ patched w φ`; see the module docstring. -/
theorem integral_patched_eq_blocks {l : ℕ} (w : Fin (l + 1) → ℝ) (φ : Fin (l + 1) → ℂ → ℂ)
    (hw : ∀ k, 0 < w k) (hsum : ∑ k, w k = 1) (h : ℝ → ℝ)
    (hint : ∀ k : Fin (l + 1),
      IntervalIntegrable (fun u : ℝ => h (circleLog (φ k) u)) volume 0 1) :
    ∫ s in (0 : ℝ)..1, h (patched w φ s)
      = ∑ k : Fin (l + 1), w k * ∫ u in (0 : ℝ)..1, h (circleLog (φ k) u) := by
  have hpiece : ∀ k : Fin (l + 1),
      IntervalIntegrable (fun s : ℝ => h (patched w φ s)) volume (bstart w (k:ℕ))
        (bstart w ((k:ℕ)+1)) := by
    intro k
    have hk : IntervalIntegrable (fun s : ℝ => h (circleLog (φ k) ((s - blockStart w k)/w k)))
        volume (blockStart w k) (blockStart w k + w k) :=
      intervalIntegrable_comp_div (fun u => h (circleLog (φ k) u)) (hw k) (hint k)
    have hae : (fun s : ℝ => h (circleLog (φ k) ((s - blockStart w k)/w k)))
        =ᵐ[volume.restrict (Set.uIoc (blockStart w k) (blockStart w k + w k))]
        (fun s : ℝ => h (patched w φ s)) := by
      rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
      refine (ae_eq_of_eqOn_Ioo (a := blockStart w k) (b := blockStart w k + w k)
        (by linarith [hw k]) (fun t ht => patched_eq_on_Ioo w φ hw k ht)).mono ?_
      intro x hx hxu
      exact (congrArg h (hx hxu)).symm
    have hk' : IntervalIntegrable (fun s : ℝ => h (patched w φ s)) volume (blockStart w k)
        (blockStart w k + w k) := hk.congr_ae hae
    rw [blockStart_add_self w k] at hk'
    rw [blockStart_eq_bstart] at hk'
    exact hk'
  have hpieces : ∀ k < l + 1, IntervalIntegrable (fun s : ℝ => h (patched w φ s)) volume
      (bstart w k) (bstart w (k + 1)) := fun k hk => hpiece ⟨k, hk⟩
  have hsplit := integral_bstart_eq_sum w (fun s : ℝ => h (patched w φ s)) hpieces (l + 1) le_rfl
  rw [bstart_zero, bstart_top, hsum] at hsplit
  have hpieceval : ∀ k : Fin (l + 1),
      ∫ x in bstart w (k:ℕ)..bstart w ((k:ℕ)+1), h (patched w φ x)
        = w k * ∫ u in (0:ℝ)..1, h (circleLog (φ k) u) := by
    intro k
    have hwk : (w k : ℝ) ≠ 0 := ne_of_gt (hw k)
    have hA : ∫ x in blockStart w k..(blockStart w k + w k), h (patched w φ x)
        = ∫ x in blockStart w k..(blockStart w k + w k),
            h (circleLog (φ k) ((x - blockStart w k)/w k)) := by
      refine intervalIntegral.integral_congr_ae ?_
      refine (ae_eq_of_eqOn_Ioo (a := blockStart w k) (b := blockStart w k + w k)
        (by linarith [hw k]) (fun t ht => patched_eq_on_Ioo w φ hw k ht)).mono ?_
      intro x hx hxu
      exact congrArg h (hx hxu)
    have hB : ∫ x in blockStart w k..(blockStart w k + w k),
          h (circleLog (φ k) ((x - blockStart w k)/w k))
        = w k * ∫ u in (0:ℝ)..1, h (circleLog (φ k) u) := by
      have key := intervalIntegral.integral_comp_add_div (a := blockStart w k)
        (b := blockStart w k + w k) (c := w k) (d := -(blockStart w k)/w k)
        (f := fun u => h (circleLog (φ k) u)) hwk
      have hfun : (fun x : ℝ => h (circleLog (φ k) ((x - blockStart w k)/w k)))
          = (fun x : ℝ =>
              (fun u => h (circleLog (φ k) u)) (-(blockStart w k)/w k + x/(w k))) := by
        funext x
        have hx : (x - blockStart w k)/w k = -(blockStart w k)/w k + x/(w k) := by
          field_simp
          ring
        rw [hx]
      rw [hfun, key]
      rw [show -(blockStart w k)/w k + blockStart w k/(w k) = 0 by field_simp; ring]
      rw [show -(blockStart w k)/w k + (blockStart w k + w k)/(w k) = 1 by field_simp; ring]
      rw [smul_eq_mul]
    rw [← blockStart_eq_bstart w k, ← blockStart_add_self w k, hA, hB]
  calc ∫ s in (0:ℝ)..1, h (patched w φ s)
      = ∑ k ∈ Finset.range (l + 1), ∫ x in bstart w k..bstart w (k + 1), h (patched w φ x) :=
        hsplit
    _ = ∑ k : Fin (l + 1), ∫ x in bstart w (k:ℕ)..bstart w ((k:ℕ)+1), h (patched w φ x) :=
        (Fin.sum_univ_eq_sum_range
          (fun k => ∫ x in bstart w k..bstart w (k + 1), h (patched w φ x)) (l + 1)).symm
    _ = ∑ k : Fin (l + 1), w k * ∫ u in (0:ℝ)..1, h (circleLog (φ k) u) :=
        Finset.sum_congr rfl (fun k _ => hpieceval k)

end Work.Holonomy3
