/-
# `Work.FIArea3.JointCount.convex_sweep_volume`

Sweeping a bounded convex set `K ⊆ ℂ` along the segment `[0,z]` increases its area by at most the
measure of its projection onto the direction perpendicular to `z`.

The proof reduces to the "axis aligned" normal form `volume_add_unitSeg` below, using the sheared
rotation `hmap z` (`Submission/Work/FIArea3/JointCount/sweep_defs.lean`), which is measure
preserving (`volume_image_hmap`), sends `[0,z]` onto the real unit segment (`hmap_image_segz`) and
satisfies `(hmap z w).im = wid z w` (`hmap_im`).  The normal form itself is proved by slicing `ℂ`
along the imaginary direction (`volume_eq_lintegral_fiber`), where the fibre of the swept set is
the fibre of the original set thickened by `[0,1]` (`fiber_add_unitSeg`,
`convex_volume_add_Icc_one`).
-/
import Mathlib
import Submission.Work.FIArea3.JointCount.sweep_defs
import Submission.Work.FIArea3.JointCount.convex_volume_eq
import Submission.Work.FIArea3.JointCount.convex_volume_add_Icc_one
import Submission.Work.FIArea3.JointCount.volume_eq_lintegral_fiber
import Submission.Work.FIArea3.JointCount.volume_image_hmap

namespace Work.FIArea3.JointCount

open MeasureTheory Set
open scoped ENNReal Pointwise

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ### elementary geometric lemmas -/

lemma convex_unitSeg : Convex ℝ unitSeg := by
  rw [unitSeg]
  intro x hx y hy a b ha hb hab
  obtain ⟨tx, htx, rfl⟩ := hx
  obtain ⟨ty, hty, rfl⟩ := hy
  refine ⟨a * tx + b * ty, ⟨?_, ?_⟩, ?_⟩
  · nlinarith [mul_nonneg ha htx.1, mul_nonneg hb hty.1]
  · nlinarith [mul_le_mul_of_nonneg_left htx.2 ha, mul_le_mul_of_nonneg_left hty.2 hb]
  · rw [Complex.real_smul, Complex.real_smul]
    push_cast
    ring

lemma convex_fiber {Z : Set ℂ} (hZ : Convex ℝ Z) (y : ℝ) :
    Convex ℝ {x : ℝ | (x : ℂ) + (y : ℂ) * Complex.I ∈ Z} := by
  intro x hx x' hx' a b ha hb hab
  have h := hZ hx hx' ha hb hab
  have hab' : (a : ℂ) + (b : ℂ) = 1 := by exact_mod_cast hab
  have heq : a • ((x : ℂ) + (y : ℂ) * Complex.I) + b • ((x' : ℂ) + (y : ℂ) * Complex.I)
      = ((a • x + b • x' : ℝ) : ℂ) + (y : ℂ) * Complex.I := by
    simp only [Complex.real_smul, smul_eq_mul, Complex.ofReal_add, Complex.ofReal_mul]
    linear_combination ((y : ℂ) * Complex.I) * hab'
  rwa [heq] at h

lemma norm_le_norm_add_mul_I (x y : ℝ) : ‖x‖ ≤ ‖(x : ℂ) + (y : ℂ) * Complex.I‖ := by
  have hsq : (x : ℝ) ^ 2 ≤ ‖(x : ℂ) + (y : ℂ) * Complex.I‖ ^ 2 := by
    have hval : Complex.normSq ((x : ℂ) + (y : ℂ) * Complex.I) = x ^ 2 + y ^ 2 := by
      simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
    rw [← Complex.normSq_eq_norm_sq, hval]
    nlinarith [sq_nonneg y]
  calc ‖x‖ = Real.sqrt (x ^ 2) := by rw [Real.sqrt_sq_eq_abs, Real.norm_eq_abs]
    _ ≤ Real.sqrt (‖(x : ℂ) + (y : ℂ) * Complex.I‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖(x : ℂ) + (y : ℂ) * Complex.I‖ := Real.sqrt_sq (norm_nonneg _)

lemma isBounded_fiber {Z : Set ℂ} (hZb : Bornology.IsBounded Z) (y : ℝ) :
    Bornology.IsBounded {x : ℝ | (x : ℂ) + (y : ℂ) * Complex.I ∈ Z} := by
  obtain ⟨R, hR⟩ := Metric.isBounded_iff_subset_closedBall (0 : ℂ) |>.mp hZb
  refine Metric.isBounded_iff_subset_closedBall (0 : ℝ) |>.mpr ⟨R, fun x hx => ?_⟩
  have h1 : ‖(x : ℂ) + (y : ℂ) * Complex.I‖ ≤ R := by
    have := hR hx
    rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero] at this
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  exact le_trans (norm_le_norm_add_mul_I x y) h1

lemma fiber_add_unitSeg (Z : Set ℂ) (y : ℝ) :
    {x : ℝ | (x : ℂ) + (y : ℂ) * Complex.I ∈ Z + unitSeg}
      = {x : ℝ | (x : ℂ) + (y : ℂ) * Complex.I ∈ Z} + Set.Icc (0:ℝ) 1 := by
  ext x
  constructor
  · intro hx
    obtain ⟨z, hz, u, hu, hzu⟩ := Set.mem_add.mp hx
    obtain ⟨t, ht, rfl⟩ := hu
    refine Set.mem_add.mpr ⟨x - t, ?_, t, ht, by ring⟩
    have h1 : z = ((x - t : ℝ) : ℂ) + (y : ℂ) * Complex.I := by
      have h2 : ((x - t : ℝ) : ℂ) + (y : ℂ) * Complex.I
          = ((x : ℂ) + (y : ℂ) * Complex.I) - (t : ℂ) := by
        push_cast; ring
      rw [h2, ← hzu]; ring
    change ((x - t : ℝ) : ℂ) + (y : ℂ) * Complex.I ∈ Z
    rw [← h1]; exact hz
  · intro hx
    obtain ⟨x', hx', t, ht, rfl⟩ := Set.mem_add.mp hx
    refine Set.mem_add.mpr ⟨(x' : ℂ) + (y : ℂ) * Complex.I, hx', (t : ℂ), ⟨t, ht, rfl⟩, ?_⟩
    push_cast
    ring

lemma image_add_linear (f : ℂ →ₗ[ℝ] ℂ) (A B : Set ℂ) : f '' (A + B) = f '' A + f '' B := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.mp hy
    exact Set.mem_add.mpr ⟨f a, ⟨a, ha, rfl⟩, f b, ⟨b, hb, rfl⟩, (map_add f a b).symm⟩
  · rintro ⟨p, ⟨a, ha, rfl⟩, q, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨a + b, Set.mem_add.mpr ⟨a, ha, b, hb, rfl⟩, map_add f a b⟩

lemma hmap_image_segz (z : ℂ) (hz : z ≠ 0) : hmap z '' segz z = unitSeg := by
  ext w
  constructor
  · rintro ⟨v, ⟨t, ht, rfl⟩, rfl⟩
    refine ⟨t, ht, ?_⟩
    rw [map_smul, hmap_self z hz, Complex.real_smul, mul_one]
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t • z, ⟨t, ht, rfl⟩, by rw [map_smul, hmap_self z hz, Complex.real_smul, mul_one]⟩

lemma lipschitz_wid (z : ℂ) : LipschitzWith ‖z‖₊ (wid z) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro a b
  have h : wid z a - wid z b = wid z (a - b) := by
    rw [wid, wid, wid, Complex.sub_re, Complex.sub_im]
    ring
  rw [Real.dist_eq, h, wid_eq_im_mul_conj]
  calc |((a - b) * star z).im| ≤ ‖(a - b) * star z‖ := Complex.abs_im_le_norm _
    _ = ‖a - b‖ * ‖z‖ := by rw [norm_mul, norm_star]
    _ = (↑‖z‖₊ : ℝ) * dist a b := by
        rw [show (↑‖z‖₊ : ℝ) = ‖z‖ from by simp, dist_eq_norm]; ring

lemma isBounded_wid_image (z : ℂ) {X : Set ℂ} (hX : Bornology.IsBounded X) :
    Bornology.IsBounded (wid z '' X) :=
  (lipschitz_wid z).isBounded_image hX

/-! ### the normal form -/

lemma volume_add_unitSeg (Z : Set ℂ) (hZ : Convex ℝ Z) (hZb : Bornology.IsBounded Z) :
    volume (Z + unitSeg) = volume Z + volume (Complex.im '' Z) := by
  have hZs : Convex ℝ (Z + unitSeg) := hZ.add convex_unitSeg
  have hIm_conv : Convex ℝ (Complex.im '' Z) := hZ.linear_image Complex.imCLM.toLinearMap
  have hIm_null : NullMeasurableSet (Complex.im '' Z) volume := hIm_conv.nullMeasurableSet volume
  have step1 : ∫⁻ y : ℝ, volume {x : ℝ | (x : ℂ) + (y : ℂ) * Complex.I ∈ Z + unitSeg}
      = ∫⁻ y : ℝ, volume ({x : ℝ | (x : ℂ) + (y : ℂ) * Complex.I ∈ Z} + Set.Icc (0:ℝ) 1) := by
    refine lintegral_congr (fun y => ?_)
    rw [fiber_add_unitSeg]
  have step2 : ∫⁻ y : ℝ, volume ({x : ℝ | (x : ℂ) + (y : ℂ) * Complex.I ∈ Z} + Set.Icc (0:ℝ) 1)
      = ∫⁻ y : ℝ, (volume {x : ℝ | (x : ℂ) + (y : ℂ) * Complex.I ∈ Z}
          + (Complex.im '' Z).indicator (1 : ℝ → ℝ≥0∞) y) := by
    refine lintegral_congr (fun y => ?_)
    have hform : ({x : ℝ | (x : ℂ) + (y : ℂ) * Complex.I ∈ Z} + Set.Icc (0:ℝ) 1)
        = Set.image2 (· + ·) {x : ℝ | (x : ℂ) + (y : ℂ) * Complex.I ∈ Z} (Set.Icc (0:ℝ) 1) := rfl
    rw [hform, convex_volume_add_Icc_one _ (convex_fiber hZ y) (isBounded_fiber hZb y)]
    by_cases h : {x : ℝ | (x : ℂ) + (y : ℂ) * Complex.I ∈ Z} = ∅
    · rw [if_pos h, Set.indicator_of_notMem]
      intro hy
      obtain ⟨v, hv, hvim⟩ := hy
      have hmem : ((v.re : ℝ) : ℂ) + (y : ℂ) * Complex.I ∈ Z := by
        have hz' : ((v.re : ℝ) : ℂ) + (y : ℂ) * Complex.I = v := by
          rw [← hvim]
          apply Complex.ext <;> simp
        rw [hz']; exact hv
      exact (Set.Nonempty.ne_empty ⟨v.re, hmem⟩) h
    · rw [if_neg h, Set.indicator_of_mem (by
        obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr h
        exact ⟨_, hx, by simp [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.I_im,
          Complex.ofReal_re, Complex.I_re]⟩)]
      simp
  have step3 : ∫⁻ y : ℝ, (volume {x : ℝ | (x : ℂ) + (y : ℂ) * Complex.I ∈ Z}
        + (Complex.im '' Z).indicator (1 : ℝ → ℝ≥0∞) y)
      = (∫⁻ y : ℝ, volume {x : ℝ | (x : ℂ) + (y : ℂ) * Complex.I ∈ Z})
        + volume (Complex.im '' Z) := by
    rw [lintegral_add_right'
      (f := fun y : ℝ => volume {x : ℝ | (x : ℂ) + (y : ℂ) * Complex.I ∈ Z})
      (g := (Complex.im '' Z).indicator (1 : ℝ → ℝ≥0∞))
      ((aemeasurable_const).indicator₀ hIm_null), lintegral_indicator_one₀ hIm_null]
  calc volume (Z + unitSeg)
      = ∫⁻ y : ℝ, volume {x : ℝ | (x : ℂ) + (y : ℂ) * Complex.I ∈ Z + unitSeg} :=
        volume_eq_lintegral_fiber _ hZs
    _ = ∫⁻ y : ℝ, volume ({x : ℝ | (x : ℂ) + (y : ℂ) * Complex.I ∈ Z} + Set.Icc (0:ℝ) 1) := step1
    _ = ∫⁻ y : ℝ, (volume {x : ℝ | (x : ℂ) + (y : ℂ) * Complex.I ∈ Z}
          + (Complex.im '' Z).indicator (1 : ℝ → ℝ≥0∞) y) := step2
    _ = (∫⁻ y : ℝ, volume {x : ℝ | (x : ℂ) + (y : ℂ) * Complex.I ∈ Z})
          + volume (Complex.im '' Z) := step3
    _ = volume Z + volume (Complex.im '' Z) := by rw [volume_eq_lintegral_fiber Z hZ]

/-! ### the target theorem -/

theorem convex_sweep_volume (K : Set ℂ) (hK : Convex ℝ K) (hKb : Bornology.IsBounded K) (z : ℂ) :
    (MeasureTheory.volume (Set.image2 (· + ·) K {w : ℂ | ∃ t ∈ Set.Icc (0:ℝ) 1, w = t • z})).toReal
      ≤ (MeasureTheory.volume K).toReal
        + (MeasureTheory.volume ((fun w : ℂ => w.re * (z * Complex.I).re + w.im * (z * Complex.I).im) '' K)).toReal := by
  show (volume (Set.image2 (· + ·) K (segz z))).toReal
      ≤ (volume K).toReal + (volume (wid z '' K)).toReal
  rcases eq_or_ne z 0 with hz | hz
  · subst hz
    have hseg : segz 0 = {0} := by
      ext w
      constructor
      · rintro ⟨t, ht, rfl⟩
        simp
      · intro hw
        exact ⟨0, ⟨le_refl 0, zero_le_one⟩, by simpa using hw⟩
    have hK0 : Set.image2 (· + ·) K (segz 0) = K := by
      rw [hseg]
      ext x
      constructor
      · rintro ⟨k, hk, e, rfl, rfl⟩
        simpa using hk
      · intro hx
        exact ⟨x, hx, 0, rfl, by simp⟩
    have hwid : (wid 0 '' K) ⊆ {0} := by
      rintro v ⟨w, hw, rfl⟩
      have h : w.re * ((0 : ℂ) * Complex.I).re + w.im * ((0 : ℂ) * Complex.I).im = (0 : ℝ) := by
        rw [zero_mul]
        simp
      simpa only [wid, Set.mem_singleton_iff] using h
    have hwid0 : volume (wid 0 '' K) = 0 := measure_mono_null hwid (by simp)
    rw [hK0, hwid0]
    simp
  · have hZK_conv : Convex ℝ (hmap z '' K) := hK.linear_image (hmap z)
    have hZK_bd : Bornology.IsBounded (hmap z '' K) := isBounded_hmap z hKb
    have himg : Complex.im '' (hmap z '' K) = wid z '' K := by
      rw [Set.image_image]
      exact congrArg (fun f : ℂ → ℝ => f '' K) (funext fun v => hmap_im z v)
    have hstep : volume (Set.image2 (· + ·) K (segz z)) = volume K + volume (wid z '' K) := by
      calc volume (Set.image2 (· + ·) K (segz z))
          = volume (K + segz z) := rfl
        _ = volume (hmap z '' (K + segz z)) := (volume_image_hmap z hz (K + segz z)).symm
        _ = volume (hmap z '' K + hmap z '' segz z) := by rw [image_add_linear]
        _ = volume (hmap z '' K + unitSeg) := by rw [hmap_image_segz z hz]
        _ = volume (hmap z '' K) + volume (Complex.im '' (hmap z '' K)) :=
            volume_add_unitSeg _ hZK_conv hZK_bd
        _ = volume K + volume (wid z '' K) := by rw [himg, volume_image_hmap z hz K]
    have hto := congrArg ENNReal.toReal hstep
    rw [ENNReal.toReal_add hKb.measure_lt_top.ne (isBounded_wid_image z hKb).measure_lt_top.ne] at hto
    exact le_of_eq hto

end

end Work.FIArea3.JointCount
