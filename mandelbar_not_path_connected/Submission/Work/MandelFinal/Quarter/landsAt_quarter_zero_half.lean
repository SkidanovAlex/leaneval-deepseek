import Mathlib
import Submission.Work.LandLeaves.All
import Submission.Work.LandLeaves.periodicRaysLand
import Submission.Work.LandLeaves.rayArgConjAux
import Submission.Work.ParamRays.MbDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MandelFinal.Quarter

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)
open Work.ParamRays (Escaping escapingSet IsDynBottcher)
open scoped ComplexConjugate

/-! ## Conjugation symmetry of the ray of angle `0` for a real parameter

The ray of angle `0` of `T_r` (`r` real) is the positive real axis `{r' : 1 < r'}` in the
Böttcher coordinate.  Complex conjugation fixes it, and the Böttcher coordinate of a real
parameter commutes with conjugation (`Work.LandLeaves.phi_conj_ofReal`), so the truncation level
sets of `R_r(0)` — and hence their closures and the accumulation set — are conjugation
invariant.  Consequently a landing point of `R_r(0)` is real. -/

/-- A point of `radialRay 0` is a positive real number larger than `1`. -/
theorem mem_radialRay_zero {w : ℂ} :
    w ∈ Work.Landing.radialRay 0 ↔ ∃ r : ℝ, 1 < r ∧ w = (r : ℂ) := by
  simp only [Work.Landing.radialRay, Work.Landing.rayDirection]
  constructor
  · rintro ⟨r, hr, hw⟩
    exact ⟨r, hr, by simpa using hw⟩
  · rintro ⟨r, hr, hw⟩
    exact ⟨r, hr, by simpa using hw⟩

/-- `radialRay 0` is invariant under complex conjugation. -/
theorem conj_mem_radialRay_zero {w : ℂ} :
    (starRingEnd ℂ) w ∈ Work.Landing.radialRay 0 ↔ w ∈ Work.Landing.radialRay 0 := by
  rw [mem_radialRay_zero, mem_radialRay_zero]
  constructor
  · rintro ⟨r, hr, hw⟩
    refine ⟨r, hr, ?_⟩
    rw [show w = (starRingEnd ℂ) ((starRingEnd ℂ) w) by simp, hw]
    simp
  · rintro ⟨r, hr, hw⟩
    refine ⟨r, hr, ?_⟩
    rw [hw]
    simp

/-- For a real parameter the truncation level set of the ray of angle `0` is invariant under
complex conjugation. -/
theorem conj_mem_trunc_zero {r : ℝ} {φ : ℂ → ℂ} (hφ : IsDynBottcher (r : ℂ) φ) (ρ : ℝ)
    {w : ℂ} (hw : w ∈ {z : ℂ | z ∈ Work.Landing.dynRay (r : ℂ) φ 0 ∧ ‖φ z‖ ≤ ρ}) :
    (starRingEnd ℂ) w
      ∈ {z : ℂ | z ∈ Work.Landing.dynRay (r : ℂ) φ 0 ∧ ‖φ z‖ ≤ ρ} := by
  obtain ⟨⟨hesc, hray⟩, hρ⟩ := hw
  have hesc' : Escaping (r : ℂ) ((starRingEnd ℂ) w) :=
    Work.LandLeaves.escaping_conj_ofReal.mpr hesc
  have hconj : φ ((starRingEnd ℂ) w) = (starRingEnd ℂ) (φ w) :=
    Work.LandLeaves.phi_conj_ofReal hφ hesc
  refine ⟨⟨hesc', ?_⟩, ?_⟩
  · rw [hconj]
    exact conj_mem_radialRay_zero.mpr hray
  · rw [hconj, Complex.norm_conj]
    exact hρ

/-- Conjugation preserves the closure of the truncation level set of the ray of angle `0`. -/
theorem conj_mem_closure_trunc_zero {r : ℝ} {φ : ℂ → ℂ} (hφ : IsDynBottcher (r : ℂ) φ) (ρ : ℝ)
    {w : ℂ}
    (hw : w ∈ closure {z : ℂ | z ∈ Work.Landing.dynRay (r : ℂ) φ 0 ∧ ‖φ z‖ ≤ ρ}) :
    (starRingEnd ℂ) w
      ∈ closure {z : ℂ | z ∈ Work.Landing.dynRay (r : ℂ) φ 0 ∧ ‖φ z‖ ≤ ρ} := by
  rw [Metric.mem_closure_iff] at hw ⊢
  intro ε hε
  obtain ⟨v, hv, hdist⟩ := hw ε hε
  exact ⟨(starRingEnd ℂ) v, conj_mem_trunc_zero hφ ρ hv, by
    rw [Complex.dist_conj_conj]; exact hdist⟩

/-- **A landing point of the ray of angle `0` of a real parameter is real.** -/
theorem landsAt_zero_conj_self {r : ℝ} {z : ℂ} (hz : Work.Landing.landsAt (r : ℂ) 0 z) :
    (starRingEnd ℂ) z = z := by
  obtain ⟨φ, hφ, hland⟩ := hz
  have hzmem : z ∈ Work.Landing.rayAccum (r : ℂ) φ 0 := by
    rw [hland]; exact Set.mem_singleton z
  have hconjmem : (starRingEnd ℂ) z ∈ Work.Landing.rayAccum (r : ℂ) φ 0 :=
    fun ρ hρ => conj_mem_closure_trunc_zero hφ ρ (hzmem ρ hρ)
  have : (starRingEnd ℂ) z ∈ ({(z : ℂ)} : Set ℂ) := by
    rw [← hland]; exact hconjmem
  simpa using this

/-- **The ray of angle `0` of `T_{1/4}` lands at the cusp `1/2`.**

The angle `0` is periodic (`angDouble 0 = 0`), so the landing theorem
`Work.LandLeaves.periodicRaysLand` (Milnor 18.1, proved for `c ∈ M*`; `1/4 ∈ M*` by
`Work.ParamRays.quarter_mem`) gives a point `z` with `landsAt (1/4) 0 z`. That point is a fixed
point of `T_{1/4}` (`Work.Landing.landsAt_periodic`, since `(angDouble)^[1] 0 = 0`), and the
accumulation set of the ray of angle `0` is invariant under complex conjugation (for real `c` the
map `z ↦ conj (φ (conj z))` is again a Böttcher coordinate, so it equals `φ` by
`Work.ParamRays.isDynBottcher_unique`; hence `conj (dynRay c φ 0) = dynRay c φ 0` and the level
sets are preserved), so `z = conj z` is real. But the only real fixed point of `T_{1/4}` is
`1/2`: `T x = x` with `x` real reads `x^2 + 1/4 = x`, i.e. `(x - 1/2)^2 = 0`. -/
theorem landsAt_quarter_zero_half : Work.Landing.landsAt (1 / 4 : ℂ) 0 (1 / 2) := by
  have hc : ((1 / 4 : ℝ) : ℂ) = (1 / 4 : ℂ) := by norm_num
  have hmem : ((1 / 4 : ℝ) : ℂ) ∈ Mandelbar := by
    rw [hc]; exact Work.ParamRays.quarter_mem
  -- the angle `0` is periodic of period `1`
  have hper : Work.Landing.PeriodicAngle 0 1 := by
    simp [Work.Landing.PeriodicAngle, Work.Landing.angDouble]
  obtain ⟨z, hz⟩ :=
    Work.LandLeaves.periodicRaysLand ((1 / 4 : ℝ) : ℂ) hmem 0 ⟨1, one_pos, hper⟩
  -- the landing point is a fixed point of `T_{1/4}`
  have hfix : Tantibar ((1 / 4 : ℝ) : ℂ) z = z := by
    have := Work.Landing.landsAt_periodic hz hper
    simpa using this
  -- and it is real, by conjugation symmetry of the ray
  have hconj : (starRingEnd ℂ) z = z := landsAt_zero_conj_self hz
  have him : z.im = 0 := by
    have h := congrArg Complex.im hconj
    simp only [Complex.conj_im] at h
    linarith
  have hzre : z = ((z.re : ℝ) : ℂ) := Complex.ext (by simp) (by simpa using him)
  -- the real fixed point equation `x ^ 2 + 1/4 = x`
  have hreal_eq : z.re ^ 2 + 1 / 4 = z.re := by
    have h := hfix
    rw [hzre, Work.Landing.Tantibar_apply] at h
    rw [show star (((z.re : ℝ)) : ℂ) = ((z.re : ℝ) : ℂ) by simp] at h
    have h2 : (((z.re) ^ 2 + 1 / 4 : ℝ) : ℂ) = ((z.re : ℝ) : ℂ) := by
      push_cast
      simpa using h
    exact Complex.ofReal_inj.mp h2
  -- whose only solution is `1/2`
  have hx : z.re = 1 / 2 := by
    have hsq : (z.re - 1 / 2) ^ 2 = 0 := by nlinarith
    have := sq_eq_zero_iff.mp hsq
    linarith
  have hz_half : z = (1 / 2 : ℂ) := by
    rw [hzre, hx]
    norm_num
  have hz' : Work.Landing.landsAt ((1 / 4 : ℝ) : ℂ) 0 (1 / 2) := hz_half ▸ hz
  exact hc ▸ hz'

end Work.MandelFinal.Quarter
