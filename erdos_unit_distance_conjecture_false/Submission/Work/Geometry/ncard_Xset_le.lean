import Mathlib
import Submission.Work.Geometry.Basic
import Submission.Work.Geometry.Counts
import Submission.Work.Geometry.WindowScale
import Submission.Work.Geometry.finite_Xset
import Submission.Work.Geometry.volume_window_one

/-!
# The counting bound `|Xset| ≤ (4 R D)^[K:ℚ]`

Points of the coset `a + Λ` (where `Λ = Lattice K I` is the lattice of the fractional ideal
`I`) lying in the window `B_R` are `1/D`-separated in the sup-norm: the difference of two
distinct such points is the image of `0 ≠ β ∈ I`, hence is at least `1/D` at some infinite
place by the hypothesis `hsep`, and the sup-norm dominates every placewise norm.

Consequently the open balls of radius `r = 1/(2D)` about the points are pairwise disjoint,
they all lie in `B_{R + r}`, and comparing Haar volumes gives

`|Xset| · vol B_r ≤ vol B_{R + r}`,  i.e.  `|Xset| ≤ ((R + r)/r)^[K:ℚ] = (2 R D + 1)^[K:ℚ]`,

which is bounded by `(4 R D)^[K:ℚ]` because `1 ≤ 2 R D`.
-/

set_option linter.unusedSectionVars false

open MeasureTheory NumberField
open scoped Classical nonZeroDivisors Pointwise

namespace Work.Geometry

/-- Translation invariance of the Haar measure: every ball of radius `r` in the mixed space
has the same volume as the window `B_r`. -/
theorem volume_ball_eq_volume_window (K : Type*) [Field K] [NumberField K]
    (x : mixedEmbedding.mixedSpace K) (r : ℝ) :
    volume (Metric.ball x r) = volume (Window K r) := by
  have h : Metric.ball (0 : mixedEmbedding.mixedSpace K) r = (x + ·) ⁻¹' Metric.ball x r := by
    ext y
    simp only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero]
  rw [Window_eq_ball (K := K) r, h, measure_preimage_add]

theorem ncard_Xset_le (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (R D : ℝ) (hD : 0 < D) (hRD : 1 ≤ R * D)
    (hsep : ∀ β ∈ (I : Set K), β ≠ 0 → ∃ w : InfinitePlace K,
      1/D ≤ mixedEmbedding.normAtPlace w (mixedEmbedding K β))
    (a : mixedEmbedding.mixedSpace K) :
    ((Xset K I R a).ncard : ℝ) ≤ (4 * R * D) ^ (Module.finrank ℚ K) := by
  classical
  have hD' : D ≠ 0 := hD.ne'
  -- `R` is positive since `1 ≤ R * D` and `D > 0`
  have hR : 0 < R := by
    by_contra h
    push Not at h
    nlinarith [mul_nonpos_of_nonpos_of_nonneg h hD.le, hRD]
  -- the separation radius
  set r := (2 * D)⁻¹ with hr_def
  have hr : 0 < r := by
    rw [hr_def]; exact inv_pos.mpr (mul_pos zero_lt_two hD)
  have hRr : 0 < R + r := add_pos hR hr
  have hSfin : (Xset K I R a).Finite := finite_Xset K I R a
  -- **every two distinct points of the coset inside the window are `1/D` apart**
  have hdist : ∀ x ∈ hSfin.toFinset, ∀ y ∈ hSfin.toFinset, x ≠ y → (1 : ℝ)/D ≤ dist x y := by
    intro x hx y hy hxy
    rw [Set.Finite.mem_toFinset] at hx hy
    obtain ⟨hxa, -⟩ := mem_Xset.mp hx
    obtain ⟨hya, -⟩ := mem_Xset.mp hy
    have hsub : x - y ∈ Lattice K I := by
      have hmem := (Lattice K I).sub_mem hxa hya
      convert hmem using 1
      abel
    rw [mem_lattice] at hsub
    obtain ⟨β, hβI, hβ⟩ := hsub
    have hβ0 : β ≠ 0 := by
      intro hb
      rw [hb, map_zero] at hβ
      exact hxy (sub_eq_zero.mp hβ.symm)
    obtain ⟨w, hw⟩ := hsep β hβI hβ0
    rw [hβ] at hw
    refine hw.trans ?_
    rw [dist_eq_norm, mixedEmbedding.norm_eq_sup'_normAtPlace]
    exact Finset.le_sup' (fun w : InfinitePlace K => mixedEmbedding.normAtPlace w (x - y))
      (Finset.mem_univ w)
  have h2r : r + r = 1 / D := by
    rw [hr_def]
    field_simp
    ring
  -- **the balls of radius `r` about the points are pairwise disjoint**
  have hdisj : (↑hSfin.toFinset : Set (mixedEmbedding.mixedSpace K)).PairwiseDisjoint
      (fun x => Metric.ball x r) := by
    intro x hx y hy hxy
    rw [Finset.mem_coe] at hx hy
    apply Metric.ball_disjoint_ball
    rw [h2r]
    exact hdist x hx y hy hxy
  -- **they all lie in the window of radius `R + r`**
  have hsub : (⋃ x ∈ hSfin.toFinset, Metric.ball x r) ⊆ Window K (R + r) := by
    rw [Window_eq_ball]
    intro z hz
    obtain ⟨x, hx, hzx⟩ := Set.mem_iUnion₂.mp hz
    rw [Metric.mem_ball, dist_zero_right]
    have hxS : x ∈ Xset K I R a := (Set.Finite.mem_toFinset hSfin).mp hx
    obtain ⟨-, hxw⟩ := mem_Xset.mp hxS
    rw [Window_eq_ball, Metric.mem_ball, dist_zero_right] at hxw
    rw [Metric.mem_ball, dist_eq_norm] at hzx
    calc ‖z‖ = ‖z - x + x‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - x‖ + ‖x‖ := norm_add_le _ _
      _ < r + R := add_lt_add hzx hxw
      _ = R + r := add_comm _ _
  have hmeas : ∀ x ∈ hSfin.toFinset, MeasurableSet (Metric.ball x r) :=
    fun x _ => Metric.isOpen_ball.measurableSet
  have hvol : ∀ x ∈ hSfin.toFinset, volume (Metric.ball x r) = volume (Window K r) :=
    fun x _ => volume_ball_eq_volume_window K x r
  -- **the volume comparison**
  have key : (hSfin.toFinset.card : ENNReal) * volume (Window K r)
      ≤ volume (Window K (R + r)) := by
    have h1 := measure_biUnion_finset (μ := volume) hdisj hmeas
    rw [Finset.sum_congr rfl hvol] at h1
    rw [Finset.sum_const, nsmul_eq_mul] at h1
    rw [← h1]
    exact measure_mono hsub
  rw [volume_Window_smul r hr, volume_Window_smul (R + r) hRr] at key
  have hvol1pos : 0 < volume (Window K (1:ℝ)) := by
    rw [volume_window_one K]
    exact ENNReal.ofReal_pos.mpr (pow_pos Real.pi_pos _)
  have hvol1top : volume (Window K (1:ℝ)) ≠ ⊤ := by
    rw [volume_window_one K]
    exact ENNReal.ofReal_ne_top
  -- cancel the volume of the unit window
  have key' : (hSfin.toFinset.card : ENNReal) * ENNReal.ofReal (r ^ Module.finrank ℚ K)
      ≤ ENNReal.ofReal ((R + r) ^ Module.finrank ℚ K) := by
    rw [← mul_assoc] at key
    exact (ENNReal.mul_le_mul_iff_left hvol1pos.ne' hvol1top).mp key
  -- descend to `ℝ`
  have key'' : (hSfin.toFinset.card : ℝ) * r ^ Module.finrank ℚ K
      ≤ (R + r) ^ Module.finrank ℚ K := by
    rw [← ENNReal.ofReal_le_ofReal_iff (pow_nonneg hRr.le _),
      ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    exact key'
  have hrn : (0:ℝ) < r ^ Module.finrank ℚ K := pow_pos hr _
  have hle1 : (hSfin.toFinset.card : ℝ) ≤ ((R + r) / r) ^ Module.finrank ℚ K := by
    have h := (le_div_iff₀ hrn).mpr key''
    rw [← div_pow] at h
    exact h
  have h2RD1 : (R + r) / r = 2 * R * D + 1 := by
    rw [hr_def]
    field_simp
  rw [h2RD1] at hle1
  have hle2 : (2:ℝ) * R * D + 1 ≤ 4 * R * D := by nlinarith [hRD]
  have hpos : (0:ℝ) ≤ 2 * R * D + 1 := by nlinarith [hRD, hD]
  have hfinal : (hSfin.toFinset.card : ℝ) ≤ (4 * R * D) ^ Module.finrank ℚ K :=
    hle1.trans (pow_le_pow_left₀ hpos hle2 _)
  rw [Set.ncard_eq_toFinset_card _ hSfin]
  exact hfinal

end Work.Geometry
