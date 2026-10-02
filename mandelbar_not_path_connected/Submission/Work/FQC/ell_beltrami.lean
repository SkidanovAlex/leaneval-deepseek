/-
# `Work.FQC.ell_beltrami`

The complex dilatation of the MNS piecewise-affine cylinder twist `ell t` is bounded a.e. by
`|t| / √(1 + t²)` (Hubbard–Schleicher, *Multicorns are not Path Connected*, §2;
Nakane–Schleicher, *On multicorns and unicorns II*).

Off the images of the corner lines `Re w ∈ 1/4 + (1/2)ℤ`, the triangle wave `saw` is locally
affine with slope `±2`; consequently `ell t` is locally a real-affine map
`w ↦ a w + b w̄ + c` with `a = 1 ± i t`, `b = ± i t`, whose complex dilatation is
`b / a = ± i t / (1 ± i t)`, of modulus `|t| / √(1 + t²)`.
-/
import Mathlib
import Submission.Work.FQC.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter MeasureTheory
open scoped Topology

noncomputable section

namespace Work.FQC

/-! ## 1. `saw` is locally affine off the corner lines -/

lemma saw_eventually_affine {x : ℝ} (h0 : Int.fract (x + 1/4) ≠ 0)
    (h2 : Int.fract (x + 1/4) ≠ 1/2) :
    ∃ s : ℝ, |s| = 2 ∧ ∀ᶠ y in 𝓝 x, saw y = saw x + s * (y - x) := by
  have hxfl : x + 1/4 = Int.fract (x + 1/4) + (⌊x + 1/4⌋ : ℝ) := by rw [Int.fract_add_floor]
  have h0le : 0 ≤ Int.fract (x + 1/4) := Int.fract_nonneg _
  have h1lt : Int.fract (x + 1/4) < 1 := Int.fract_lt_one _
  have h0pos : 0 < Int.fract (x + 1/4) := lt_of_le_of_ne h0le (Ne.symm h0)
  rcases lt_trichotomy (Int.fract (x + 1/4)) (1/2) with hlt | heq | hgt
  · refine ⟨2, by norm_num, ?_⟩
    have hopen : IsOpen {y : ℝ | (⌊x+1/4⌋ : ℝ) < y + 1/4 ∧ y + 1/4 < (⌊x+1/4⌋ : ℝ) + 1/2} :=
      IsOpen.inter (isOpen_lt continuous_const (continuous_id.add continuous_const))
        (isOpen_lt (continuous_id.add continuous_const) continuous_const)
    have hmem : x ∈ {y : ℝ | (⌊x+1/4⌋ : ℝ) < y + 1/4 ∧ y + 1/4 < (⌊x+1/4⌋ : ℝ) + 1/2} := by
      refine ⟨by linarith, by linarith⟩
    filter_upwards [hopen.mem_nhds hmem] with y hy
    have hfloor : ⌊y + 1/4⌋ = ⌊x + 1/4⌋ := by
      rw [Int.floor_eq_iff]; exact ⟨le_of_lt hy.1, by linarith [hy.2]⟩
    have hfr : Int.fract (y + 1/4) = y + 1/4 - (⌊x+1/4⌋ : ℝ) := by
      have := Int.fract_add_floor (y + 1/4); rw [hfloor] at this; linarith
    have hxsaw : saw x = 2 * x - 2 * (⌊x+1/4⌋ : ℝ) := by
      rw [saw_apply, abs_of_nonpos (show Int.fract (x + 1/4) - 1/2 ≤ 0 by linarith),
        show Int.fract (x + 1/4) = x + 1/4 - (⌊x+1/4⌋:ℝ) by linarith]
      ring
    have hysaw : saw y = 2 * y - 2 * (⌊x+1/4⌋ : ℝ) := by
      rw [saw_apply, hfr, abs_of_nonpos (show y + 1/4 - (⌊x+1/4⌋:ℝ) - 1/2 ≤ 0 by linarith)]
      ring
    rw [hysaw, hxsaw]; ring
  · exact absurd heq h2
  · refine ⟨-2, by norm_num, ?_⟩
    have hopen : IsOpen {y : ℝ | (⌊x+1/4⌋ : ℝ) + 1/2 < y + 1/4 ∧ y + 1/4 < (⌊x+1/4⌋ : ℝ) + 1} :=
      IsOpen.inter (isOpen_lt continuous_const (continuous_id.add continuous_const))
        (isOpen_lt (continuous_id.add continuous_const) continuous_const)
    have hmem : x ∈ {y : ℝ | (⌊x+1/4⌋ : ℝ) + 1/2 < y + 1/4 ∧ y + 1/4 < (⌊x+1/4⌋ : ℝ) + 1} := by
      refine ⟨by linarith, by linarith⟩
    filter_upwards [hopen.mem_nhds hmem] with y hy
    have hfloor : ⌊y + 1/4⌋ = ⌊x + 1/4⌋ := by
      rw [Int.floor_eq_iff]; exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have hfr : Int.fract (y + 1/4) = y + 1/4 - (⌊x+1/4⌋ : ℝ) := by
      have := Int.fract_add_floor (y + 1/4); rw [hfloor] at this; linarith
    have hxsaw : saw x = 1 - 2 * x + 2 * (⌊x+1/4⌋ : ℝ) := by
      rw [saw_apply, abs_of_nonneg (show 0 ≤ Int.fract (x + 1/4) - 1/2 by linarith),
        show Int.fract (x + 1/4) = x + 1/4 - (⌊x+1/4⌋:ℝ) by linarith]
      ring
    have hysaw : saw y = 1 - 2 * y + 2 * (⌊x+1/4⌋ : ℝ) := by
      rw [saw_apply, hfr, abs_of_nonneg (show 0 ≤ y + 1/4 - (⌊x+1/4⌋:ℝ) - 1/2 by linarith)]
      ring
    rw [hysaw, hxsaw]; ring

/-! ## 2. The complex dilatation of a real-affine map -/

end Work.FQC

namespace Work.MRMT

lemma fderiv_affine_star (a b c : ℂ) (w : ℂ) :
    fderiv ℝ (fun v : ℂ => a * v + b * star v + c) w
      = a • (1 : ℂ →L[ℝ] ℂ) + b • (Complex.conjCLE : ℂ →L[ℝ] ℂ) := by
  set L : ℂ →L[ℝ] ℂ := a • (1 : ℂ →L[ℝ] ℂ) + b • (Complex.conjCLE : ℂ →L[ℝ] ℂ) with hL
  have hLapply : ∀ v : ℂ, L v = a * v + b * star v := by
    intro v
    simp only [hL, add_apply, smul_apply, one_apply_eq_self, smul_eq_mul]; simp
  have hfun : (fun v : ℂ => a * v + b * star v + c) = fun v => L v + c := by
    funext v; rw [hLapply]
  rw [hfun]
  exact (L.hasFDerivAt.add_const c).fderiv

lemma dz_affine_star (a b c : ℂ) (w : ℂ) :
    dz (fun v : ℂ => a * v + b * star v + c) w = a := by
  have hL1 : (a • (1 : ℂ →L[ℝ] ℂ) + b • (Complex.conjCLE : ℂ →L[ℝ] ℂ)) (1:ℂ) = a + b := by
    have hkey : (Complex.conjCLE : ℂ →L[ℝ] ℂ) (1:ℂ) = 1 := by simp
    simp only [add_apply, smul_apply, one_apply_eq_self, smul_eq_mul, hkey]; ring
  have hLI : (a • (1 : ℂ →L[ℝ] ℂ) + b • (Complex.conjCLE : ℂ →L[ℝ] ℂ)) Complex.I
      = Complex.I * (a - b) := by
    have hkey : (Complex.conjCLE : ℂ →L[ℝ] ℂ) Complex.I = -Complex.I := by simp
    simp only [add_apply, smul_apply, one_apply_eq_self, smul_eq_mul, hkey]; ring
  rw [dz, fderiv_affine_star, hL1, hLI]
  rw [show Complex.I * (Complex.I * (a - b)) = -(a - b) by
    rw [← mul_assoc, Complex.I_mul_I]; ring]
  ring

lemma dzbar_affine_star (a b c : ℂ) (w : ℂ) :
    dzbar (fun v : ℂ => a * v + b * star v + c) w = b := by
  have hL1 : (a • (1 : ℂ →L[ℝ] ℂ) + b • (Complex.conjCLE : ℂ →L[ℝ] ℂ)) (1:ℂ) = a + b := by
    have hkey : (Complex.conjCLE : ℂ →L[ℝ] ℂ) (1:ℂ) = 1 := by simp
    simp only [add_apply, smul_apply, one_apply_eq_self, smul_eq_mul, hkey]; ring
  have hLI : (a • (1 : ℂ →L[ℝ] ℂ) + b • (Complex.conjCLE : ℂ →L[ℝ] ℂ)) Complex.I
      = Complex.I * (a - b) := by
    have hkey : (Complex.conjCLE : ℂ →L[ℝ] ℂ) Complex.I = -Complex.I := by simp
    simp only [add_apply, smul_apply, one_apply_eq_self, smul_eq_mul, hkey]; ring
  rw [dzbar, fderiv_affine_star, hL1, hLI]
  rw [show Complex.I * (Complex.I * (a - b)) = -(a - b) by
    rw [← mul_assoc, Complex.I_mul_I]; ring]
  ring

lemma beltramiOf_affine_star (a b c : ℂ) (w : ℂ) :
    beltramiOf (fun v : ℂ => a * v + b * star v + c) w = b / a := by
  rw [beltramiOf, dzbar_affine_star, dz_affine_star]

end Work.MRMT

namespace Work.FQC

/-- The complex dilatation depends only on the germ of the map. -/
lemma beltramiOf_congr {f g : ℂ → ℂ} {w : ℂ} (h : f =ᶠ[𝓝 w] g) :
    Work.MRMT.beltramiOf f w = Work.MRMT.beltramiOf g w := by
  rw [Work.MRMT.beltramiOf, Work.MRMT.beltramiOf, Work.MRMT.dzbar, Work.MRMT.dz,
    Work.MRMT.dzbar, Work.MRMT.dz, h.fderiv_eq]

/-- The modulus of `± i t / (1 ± i t)`. -/
lemma norm_I_mul_div (t s : ℝ) (hs : |s| = 2) :
    ‖(Complex.I * ((t * s / 2 : ℝ) : ℂ)) / (1 + Complex.I * ((t * s / 2 : ℝ) : ℂ))‖
      = |t| / Real.sqrt (1 + t ^ 2) := by
  set u : ℝ := t * s / 2 with hu
  have huc : ((t * s / 2 : ℝ) : ℂ) = (u : ℂ) := by rw [hu]
  rw [huc]
  have hu2 : u ^ 2 = t ^ 2 := by
    have hs2 : s ^ 2 = 4 := by rw [← sq_abs s, hs]; norm_num
    rw [hu, show (t * s / 2 : ℝ)^2 = t^2 * s^2 / 4 by ring, hs2]; ring
  have habs : |u| = |t| := by rw [← Real.sqrt_sq_eq_abs u, ← Real.sqrt_sq_eq_abs t, hu2]
  rw [norm_div]
  have hbnorm : ‖Complex.I * (u : ℂ)‖ = |u| := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_def, Complex.normSq_ofReal,
      show u * u = u^2 by ring, Real.sqrt_sq_eq_abs]
  have hAnorm : ‖(1:ℂ) + Complex.I * ((u:ℝ):ℂ)‖ = Real.sqrt (1 + u^2) := by
    rw [show (1:ℂ) + Complex.I * ((u:ℝ):ℂ) = ((1:ℝ):ℂ) + ((u:ℝ):ℂ) * Complex.I by
      rw [mul_comm]; norm_num]
    rw [Complex.norm_def]; congr 1; rw [Complex.normSq_apply]; push_cast; simp; ring
  rw [hbnorm, hAnorm, hu2, habs]

/-- Pointwise bound: away from the corner lines of `saw`, the dilatation of `ell t` is
exactly `± i t / (1 ± i t)`. -/
lemma ell_beltrami_of_good (t : ℝ) {w : ℂ}
    (h0 : Int.fract (w.re + 1/4) ≠ 0) (h2 : Int.fract (w.re + 1/4) ≠ 1/2) :
    ‖Work.MRMT.beltramiOf (ell t) w‖ ≤ |t| / Real.sqrt (1 + t ^ 2) := by
  obtain ⟨s, hsabs, hs⟩ := saw_eventually_affine h0 h2
  set a : ℂ := 1 + Complex.I * ((t * s / 2 : ℝ) : ℂ) with ha
  set b : ℂ := Complex.I * ((t * s / 2 : ℝ) : ℂ) with hb
  set c : ℂ := Complex.I * (t : ℂ) * ((saw w.re : ℂ) - (s : ℂ) * (w.re : ℂ)) with hc
  have hcast : ∀ z : ℂ, ((z.re : ℝ) : ℂ) = (z + star z) / 2 := by
    intro z
    rw [show z + star z = ((2 * z.re : ℝ) : ℂ) from Complex.add_conj z]
    push_cast; ring
  have hev : ell t =ᶠ[𝓝 w] fun v => a * v + b * star v + c := by
    have hs' : saw =ᶠ[𝓝 w.re] (fun y : ℝ => saw w.re + s * (y - w.re)) := hs
    have hcomp : (fun v : ℂ => saw v.re) =ᶠ[𝓝 w] fun v => saw w.re + s * (v.re - w.re) := by
      simpa [Function.comp_def] using hs'.comp_tendsto Complex.continuous_re.continuousAt
    filter_upwards [hcomp] with v hv
    rw [ell_apply, hv]
    simp only [ha, hb, hc]
    push_cast
    rw [hcast v, hcast w]
    ring
  rw [beltramiOf_congr hev, Work.MRMT.beltramiOf_affine_star, ha, hb, norm_I_mul_div t s hsabs]

/-! ## 3. The exceptional set has measure zero -/

lemma volume_re_eq_zero (c : ℝ) : volume {w : ℂ | w.re = c} = 0 := by
  have hs : MeasurableSet ({c} ×ˢ (Set.univ : Set ℝ)) :=
    (MeasurableSet.singleton c).prod MeasurableSet.univ
  have hpre : {w : ℂ | w.re = c}
      = Complex.measurableEquivRealProd ⁻¹' ({c} ×ˢ (Set.univ : Set ℝ)) := by
    ext w; simp [Complex.measurableEquivRealProd_apply]
  rw [hpre, Complex.volume_preserving_equiv_real_prod.measure_preimage hs.nullMeasurableSet]
  change (volume.prod volume) ({c} ×ˢ (Set.univ : Set ℝ)) = 0
  rw [Measure.prod_prod]
  simp

/-- The union of the corner lines `Re w ∈ 1/4 + (1/2)ℤ`. -/
def badRe : Set ℝ := Set.range (fun k : ℤ => (k:ℝ)/2 - 1/4)

lemma mem_badRe_of_fract_zero {x : ℝ} (h : Int.fract (x + 1/4) = 0) : x ∈ badRe := by
  refine ⟨2 * ⌊x + 1/4⌋, ?_⟩
  have hfl := Int.fract_add_floor (x + 1/4)
  rw [h, zero_add] at hfl
  push_cast; linarith

lemma mem_badRe_of_fract_half {x : ℝ} (h : Int.fract (x + 1/4) = 1/2) : x ∈ badRe := by
  refine ⟨2 * ⌊x + 1/4⌋ + 1, ?_⟩
  have hfl := Int.fract_add_floor (x + 1/4)
  rw [h] at hfl
  push_cast; linarith

lemma volume_re_mem_bad : volume {w : ℂ | w.re ∈ badRe} = 0 := by
  have hset : {w : ℂ | w.re ∈ badRe} = ⋃ k : ℤ, {w : ℂ | w.re = ((k:ℝ)/2 - 1/4)} := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨k, hk⟩; exact ⟨k, hk.symm⟩
    · rintro ⟨k, hk⟩; exact ⟨k, hk.symm⟩
  rw [hset]
  exact measure_iUnion_null (fun k => volume_re_eq_zero _)

/-! ## 4. The theorem -/

theorem ell_beltrami (t : ℝ) : ∀ᵐ w ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), ‖Work.MRMT.beltramiOf (Work.FQC.ell t) w‖ ≤ |t| / Real.sqrt (1 + t ^ 2) := by
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null (fun w hw => ?_) volume_re_mem_bad
  by_contra hbad
  exact hw (ell_beltrami_of_good t
    (fun h => hbad (mem_badRe_of_fract_zero h))
    (fun h => hbad (mem_badRe_of_fract_half h)))

end Work.FQC

end
