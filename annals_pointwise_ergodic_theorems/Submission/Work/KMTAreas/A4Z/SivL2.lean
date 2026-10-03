
/-
# `l2` bookkeeping for the proof of `siv-second`
-/
import Mathlib
import Submission.Work.KMTAreas.A4Z.SivGeom
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators

namespace Work.KMTAreas.A4Z

def l2sq (g : ℤ → ℂ) : ℝ := ∑' x : ℤ, ‖g x‖ ^ 2

def l2norm (g : ℤ → ℂ) : ℝ := Real.sqrt (l2sq g)

theorem l2norm_nonneg (g : ℤ → ℂ) : 0 ≤ l2norm g := Real.sqrt_nonneg _

theorem l2sq_nonneg (g : ℤ → ℂ) : 0 ≤ l2sq g := tsum_nonneg fun x => sq_nonneg _

theorem l2sq_zPiece {L : ℤ} (hL : 0 < L) (f : ℤ → ℂ) (i : ℤ) :
    l2sq (zPiece L f i) = ∑ x ∈ Finset.Ico (i * L) ((i + 1) * L), ‖f x‖ ^ 2 := by
  rw [l2sq, tsum_eq_sum (s := Finset.Ico (i * L) ((i + 1) * L))]
  · refine Finset.sum_congr rfl fun x hx => ?_
    rw [zPiece_eq_self (ediv_eq_of_mem_Ico hL (Finset.mem_Ico.mp hx).1 (Finset.mem_Ico.mp hx).2)]
  · intro x hx
    rw [zPiece_eq_zero_of_not_mem hL hx]
    simp

theorem summable_norm_sq_zPiece {L : ℤ} (hL : 0 < L) (f : ℤ → ℂ) (i : ℤ) :
    Summable (fun x : ℤ => ‖zPiece L f i x‖ ^ 2) :=
  summable_of_ne_finset_zero (s := Finset.Ico (i * L) ((i + 1) * L)) fun x hx => by
    rw [zPiece_eq_zero_of_not_mem hL hx]
    norm_num

theorem eLpNorm_two_eq_ofReal_l2norm {g : ℤ → ℂ} (hg : Summable (fun x : ℤ => ‖g x‖ ^ 2)) :
    eLpNorm g 2 Measure.count = ENNReal.ofReal (l2norm g) := by
  have hnn : ∀ x : ℤ, (0 : ℝ) ≤ ‖g x‖ ^ 2 := fun x => sq_nonneg _
  have hstep : eLpNorm g 2 Measure.count
      = (∑' x : ℤ, ENNReal.ofReal (‖g x‖ ^ 2)) ^ (1 / 2 : ℝ) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) (by norm_num) (by norm_num)]
    norm_num
    rw [lintegral_count]
  rw [hstep, ← ENNReal.ofReal_tsum_of_nonneg hnn hg, l2norm, l2sq,
    ENNReal.ofReal_rpow_of_nonneg (tsum_nonneg hnn) (by norm_num : (0 : ℝ) ≤ 1 / 2),
    Real.sqrt_eq_rpow]

theorem sq_l2norm {g : ℤ → ℂ} (hg : Summable (fun x : ℤ => ‖g x‖ ^ 2)) :
    l2norm g ^ 2 = ∑' x : ℤ, ‖g x‖ ^ 2 := by
  rw [l2norm, l2sq, Real.sq_sqrt (tsum_nonneg fun x => sq_nonneg _)]


/-! ## Reflection invariance of the `ℓ²` norm -/

theorem l2sq_neg (g : ℤ → ℂ) : l2sq (fun x : ℤ => g (-x)) = l2sq g := by
  simpa only [l2sq, Equiv.neg_apply] using Equiv.tsum_eq (Equiv.neg ℤ) (fun z : ℤ => ‖g z‖ ^ 2)

theorem summable_norm_sq_neg {g : ℤ → ℂ} (hg : Summable (fun x : ℤ => ‖g x‖ ^ 2)) :
    Summable (fun x : ℤ => ‖g (-x)‖ ^ 2) := by
  have h := (Equiv.summable_iff (f := fun z : ℤ => ‖g z‖ ^ 2) (Equiv.neg ℤ)).mpr hg
  have h2 : ((fun z : ℤ => ‖g z‖ ^ 2) ∘ ⇑(Equiv.neg ℤ)) = fun x : ℤ => ‖g (-x)‖ ^ 2 := by
    funext x
    simp [Function.comp, Equiv.neg_apply]
  rwa [h2] at h

/-- **The `ℓ²` norm is invariant under reflection** `x ↦ -x` (for functions of finite `ℓ²`
norm). -/
theorem eLpNorm_neg_count {g : ℤ → ℂ} (hg : Summable (fun x : ℤ => ‖g x‖ ^ 2)) :
    eLpNorm (fun x : ℤ => g (-x)) 2 Measure.count = eLpNorm g 2 Measure.count := by
  rw [eLpNorm_two_eq_ofReal_l2norm (summable_norm_sq_neg hg), eLpNorm_two_eq_ofReal_l2norm hg]
  simp only [l2norm]
  rw [l2sq_neg g]

/-! ## The block decomposition of the `ℓ²` norm -/

theorem sum_l2sq_zPiece_le {L : ℤ} (hL : 0 < L) {f : ℤ → ℂ}
    (hf : Summable (fun x : ℤ => ‖f x‖ ^ 2)) (S : Finset ℤ) :
    ∑ i ∈ S, l2sq (zPiece L f i) ≤ l2sq f := by
  have hdisj : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      Disjoint (Finset.Ico (i * L) ((i + 1) * L)) (Finset.Ico (j * L) ((j + 1) * L)) := by
    intro i _ j _ hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    have h1 : i = x / L :=
      ediv_eq_of_mem_Ico hL (Finset.mem_Ico.mp hxi).1 (Finset.mem_Ico.mp hxi).2
    have h2 : j = x / L :=
      ediv_eq_of_mem_Ico hL (Finset.mem_Ico.mp hxj).1 (Finset.mem_Ico.mp hxj).2
    exact hij (h1.trans h2.symm)
  rw [Finset.sum_congr rfl (fun i _ => l2sq_zPiece hL f i)]
  rw [← Finset.sum_biUnion hdisj]
  exact hf.sum_le_tsum _ (fun x _ => sq_nonneg _)

theorem summable_l2sq_zPiece {L : ℤ} (hL : 0 < L) {f : ℤ → ℂ}
    (hf : Summable (fun x : ℤ => ‖f x‖ ^ 2)) :
    Summable (fun i : ℤ => l2sq (zPiece L f i)) := by
  exact summable_of_sum_le (f := fun i : ℤ => l2sq (zPiece L f i)) (c := l2sq f)
    (fun i => l2sq_nonneg _) (fun S => sum_l2sq_zPiece_le hL hf S)

theorem tsum_l2sq_zPiece {L : ℤ} (hL : 0 < L) {f : ℤ → ℂ}
    (hf : Summable (fun x : ℤ => ‖f x‖ ^ 2)) :
    (∑' i : ℤ, l2sq (zPiece L f i)) = l2sq f := by
  have hblocks := tsum_eq_sum_blocks hL (g := fun x : ℤ => ‖f x‖ ^ 2)
    (hf.congr (fun x => (Real.norm_of_nonneg (sq_nonneg (‖f x‖))).symm))
  have hR : l2sq f = ∑' m : ℤ, ∑ x ∈ Finset.Ico (m * L) ((m + 1) * L), ‖f x‖ ^ 2 := by
    rw [l2sq]
    exact hblocks
  rw [hR]
  exact tsum_congr fun i => l2sq_zPiece hL f i

end Work.KMTAreas.A4Z
