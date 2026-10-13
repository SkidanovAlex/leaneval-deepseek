import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.mul_w_sin_rpow_sq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.FTS.EllipticEst.Honest.slice_bdd_of_sq_mul_sEta

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngAWeak

set_option autoImplicit false

/-!
# Slicewise boundedness and `σ`-weighted square-integrability for `AeData`

For data `AeData α u G` (the almost-everywhere class of the level-`0` elliptic estimate, whose
slices are allowed to jump at `θ = 0, π/2`), we prove that every `θ`-slice of `u` is

* bounded on the closed interval `Iθ = [0, π/2]`, and
* square-integrable against the angular weight `σ = sEta = sin(2θ)^{-η}`.

The mathematics is two applications of the fundamental theorem of calculus.  The class `AeData`
requires honesty of the level-`0` `ℋ⁰` integrand of `∂_θθu`, i.e. for every `z > 0`

`∫_{Iθ} (∂_θθu(z,·))² σ < ∞`.

Since `σ ≥ 1` on the open interval, this is *stronger* than the plain `L¹`-integrability of
`∂_θθu`; on the open interval `(0, π/2)` the slice `θ ↦ u(z,θ)` is `C²`, so
`∂_θu(θ) = ∂_θu(π/4) + ∫_{π/4}^{θ}∂_θθu`, and once more for `u` itself: the slice is bounded on
`(0, π/2)`.  At the endpoints the *values* `u z 0 = 0`, `u z (π/2) = 0` are part of `AeData`, so
the bound extends to all of `Iθ`.  The second conjunct then follows from the first because `σ` is
integrable on `Iθ` (`η = 99/100 < 1`).
-/

/-! ## Elementary facts about the angular weight `σ = sEta = sin(2θ)^{-η}` on `Iθ` -/

private theorem sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

private theorem sEta_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.sEta θ :=
  Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _

private theorem measurable_sEta :
    Measurable (fun θ : ℝ => Work.FTS.EllipticEst.sEta θ) := by
  have h : Measurable (fun θ : ℝ => Real.sin (2 * θ)) :=
    Real.measurable_sin.comp (measurable_const.mul measurable_id)
  simpa only [Work.FTS.EllipticEst.sEta] using h.pow measurable_const

private theorem sEta_integrableOn_Iθ :
    IntegrableOn (fun θ : ℝ => Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
  have h := (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta)) (by norm_num [Work.Spaces.eta])
    (by norm_num [Work.Spaces.eta])).1
  simpa only [Work.FTS.EllipticEst.sEta] using h

/-- On `Iθ` the level-`0` `HkIntegrand` is the single weighted square `g² w² σ` (the
mixed-derivative sum of `HkIntegrand` is empty at level `0`). -/
private theorem HkIntegrand_zero_eq_sEta (α : ℝ) (g : ℝ → ℝ → ℝ) (z : ℝ) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
  have hkey : Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    simp [Work.Spaces.HkIntegrand]
  rw [hkey]
  exact Work.FTS.EllipticEst.mul_w_sin_rpow_sq (g z θ) (Work.Spaces.w z) hθ

/-- The `θ`-slices of a function smooth on the open quadrant are smooth on the open interval
`(0, π/2)`. -/
private theorem contDiffOn_slice_of_strip {u : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {z : ℝ} (hz : 0 < z) (n : ℕ) :
    ContDiffOn ℝ n (fun θ => u z θ) (Set.Ioo 0 (Real.pi / 2)) := by
  have hmap : Set.MapsTo (fun θ : ℝ => (z, θ)) (Set.Ioo 0 (Real.pi / 2))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := fun θ hθ => ⟨hz, hθ⟩
  exact (hsm n).comp (by fun_prop) hmap

/-- `HkMem α 0 (∂_θθu)` gives the slicewise `σ`-weighted integrability of `∂_θθu`: for every
`z > 0` the function `θ ↦ (∂_θθu(z,θ))² σ θ` is integrable on `Iθ` (the square `(w z)²` of the
radial weight is a nonzero constant). -/
private theorem integrableOn_pthIter2_sEta_of_HkMem {α : ℝ} {u : ℝ → ℝ → ℝ}
    (hm : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 u)) {z : ℝ} (hz : 0 < z) :
    IntegrableOn
      (fun θ => (Work.Spaces.pthIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have h1 := hm.1 z hzI
  have h2 : IntegrableOn
      (fun θ => (Work.Spaces.pthIter 2 u z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
    h1.congr_fun (fun θ hθ => HkIntegrand_zero_eq_sEta α (Work.Spaces.pthIter 2 u) z hθ)
      measurableSet_Icc
  have hw' : Work.Spaces.w z ≠ 0 := by
    rw [Work.Spaces.w]
    exact div_ne_zero (pow_ne_zero _ (by linarith)) (pow_ne_zero _ (ne_of_gt hz))
  have h3 := h2.mul_const ((Work.Spaces.w z) ^ 2)⁻¹
  refine h3.congr (Eventually.of_forall (fun θ => ?_))
  show ((Work.Spaces.pthIter 2 u z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.sEta θ) * ((Work.Spaces.w z) ^ 2)⁻¹
      = (Work.Spaces.pthIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
  field_simp

/-- **The second conjunct, abstractly**: a slice which is continuous on the open interval and
bounded on `Iθ` has `σ`-weighted square-integrable on `Iθ`.  (The two endpoints are a null set,
so only continuity on `(0, π/2)` is needed; `σ` is integrable on `Iθ` because `η < 1`.) -/
private theorem integrableOn_sq_mul_sEta_of_bdd {u : ℝ → ℝ} {M : ℝ} (hM0 : 0 ≤ M)
    (hMg : ∀ θ ∈ Work.Spaces.Iθ, |u θ| ≤ M)
    (hcont : ContinuousOn u (Set.Ioo 0 (Real.pi / 2))) :
    IntegrableOn (fun θ => (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
  -- `Iθ` and `(0, π/2)` agree up to the null set `{0, π/2}`
  have hpair : volume ({(0 : ℝ), Real.pi / 2} : Set ℝ) = 0 :=
    Set.Finite.measure_zero (by simp) volume
  have hpairab : ∀ᵐ x : ℝ, x ∉ ({(0 : ℝ), Real.pi / 2} : Set ℝ) := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using hpair
  have hst : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    filter_upwards [hpairab] with x hx
    refine propext ⟨?_, ?_⟩
    · intro h
      rw [Work.Spaces.Iθ, Set.mem_Icc] at h
      rw [Set.mem_Ioo]
      exact ⟨lt_of_le_of_ne h.1 (fun hc => hx (Or.inl hc.symm)),
             lt_of_le_of_ne h.2 (fun hc => hx (Or.inr hc))⟩
    · intro h
      rw [Work.Spaces.Iθ, Set.mem_Icc]
      rw [Set.mem_Ioo] at h
      exact ⟨le_of_lt h.1, le_of_lt h.2⟩
  have hms : volume.restrict Work.Spaces.Iθ
      = volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    Measure.restrict_congr_set hst
  rw [IntegrableOn, hms]
  -- strong measurability of the integrand on the open interval
  have haesm : AEStronglyMeasurable (fun θ => (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    ((hcont.aestronglyMeasurable measurableSet_Ioo).pow 2).mul
      measurable_sEta.aestronglyMeasurable
  -- the majorant `M² σ` is integrable
  have hmaj : Integrable (fun θ => M ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
    have h := sEta_integrableOn_Iθ.const_mul (M ^ 2)
    simpa only [IntegrableOn, hms] using h
  refine hmaj.mono' haesm ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hsnn : 0 ≤ Work.FTS.EllipticEst.sEta θ := sEta_nonneg_Iθ hθI
  have hsq : (u θ) ^ 2 ≤ M ^ 2 := by
    have h1 := hMg θ hθI
    nlinarith [abs_nonneg (u θ), sq_abs (u θ), hM0]
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hsnn)]
  exact mul_le_mul_of_nonneg_right hsq hsnn

/-- **Slicewise boundedness and `σ`-weighted square-integrability for the a.e. class.**
The quantifier order matters: `z` is fixed first and `M` may depend on it (no uniformity in `z`
is claimed).  Both conjuncts come from the honesty of the level-`0` `ℋ⁰`-integrand of `∂_θθu`,
which forces `∫_{Iθ}|u''| < ∞` on each slice, plus the Dirichlet *values* `u z 0 = u z (π/2) = 0`
of `AeData` for the two endpoints. -/
theorem aeSliceBdd : ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
    (∀ z : ℝ, 0 < z → ∃ M : ℝ, 0 ≤ M ∧ ∀ θ ∈ Work.Spaces.Iθ, |u z θ| ≤ M) ∧
    (∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
        (fun θ => (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ) := by
  intro α u G h
  have hbdd : ∀ z : ℝ, 0 < z → ∃ M : ℝ, 0 ≤ M ∧ ∀ θ ∈ Work.Spaces.Iθ, |u z θ| ≤ M := by
    intro z hz
    -- the `σ`-weighted `L²`-integrability of `∂_θθu` on the slice
    have hint := integrableOn_pthIter2_sEta_of_HkMem (u := u) h.memAng2 hz
    have hint' : IntegrableOn
        (fun θ => (deriv (fun t : ℝ => deriv (fun θ' : ℝ => u z θ') t) θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
      hint
    -- the fundamental-theorem-of-calculus bound on the open interval
    obtain ⟨C, hC0, hC⟩ :=
      Work.FTS.EllipticEst.Honest.slice_bdd_of_sq_mul_sEta
        (contDiffOn_slice_of_strip h.smooth hz 2) hint'
    refine ⟨C, hC0, fun θ hθ => ?_⟩
    rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
    rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · rw [← h0, h.dirZero z]
      simpa using hC0
    rcases eq_or_lt_of_le hθ.2 with h1 | h1
    · rw [h1, h.dirPi z]
      simpa using hC0
    · exact (hC θ ⟨h0, h1⟩).1
  refine ⟨hbdd, fun z hz => ?_⟩
  obtain ⟨M, hM0, hMg⟩ := hbdd z hz
  exact integrableOn_sq_mul_sEta_of_bdd hM0 hMg (contDiffOn_slice_of_strip h.smooth hz 1).continuousOn

end Work.FTS.EllipticEst.AngAWeak
