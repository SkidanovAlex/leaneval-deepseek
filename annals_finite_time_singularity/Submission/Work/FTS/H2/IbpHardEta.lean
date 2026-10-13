/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `D_z`-slot angular integration by parts

This file discharges the four smoothness hypotheses of the general angular integration by
parts `Work.FTS.H2.ibp_hard` in the case `q = η = 99/100` of the `D_z`-slot weight
`sin(2θ)^{-η}`, obtaining `Work.FTS.H2.IbpHardEta`:

  `∫_θ f·D_θ(v)·v·sin(2θ)^{-η} = -∫_θ v²·(D_θf/2 + (1-η)cos(2θ)·f)·sin(2θ)^{-η}`

for `f`, `v` smooth on a neighbourhood of the closed quadrant and `z > 0`.

The content is:

* `slice_continuousAt`: the angular slice `θ ↦ g z θ` of a `SmoothNbhd` function is
  continuous at every point of `(-1, π/2+1)`, in particular at the two endpoints `0`, `π/2`
  of `Iθ` (where `Work.Coercivity.slice_continuousOn` alone is not enough);
* `eta_van_left`, `eta_van_right`: the boundary term `sin(2θ)^{1-η}·f·v²` of the integration
  by parts tends to `0` at `θ → 0⁺` and `θ → π/2⁻`, because `sin(2θ)^{1-η} → 0`
  (the exponent `1-η = 1/100` is positive) while `f z ··` and `v z ··` are continuous, hence
  bounded, near the endpoints;
* `integrableOn_eta_hint`, `integrableOn_eta_K`: the two interval-integrability hypotheses.
  The key point is that on `Iθ` the singular factor `sin(2θ)^{-η}` splits as
  `sin(2θ)^{-η}·sin(2θ) = sin(2θ)^{1-η}` on the `D_θv` summand (where the `sin(2θ)` carried
  by `D_θ` cancels the singularity: `eta_hint_pointwise`), leaving a continuous integrand on
  the compact `Iθ`; the remaining piece has the *integrable* factor `sin(2θ)^{-η`
  (`Work.Coercivity.integrableOn_sin_two_eta_neg`, from `Work.Spaces.sin_two_rpow` with
  `-1 < -η ≤ 0`) times a function continuous on the compact `Iθ`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.H2.IBPWeight
import Submission.Work.Spaces.Defs
import Submission.Work.Coercivity.sliceEtaAux
import Submission.Work.Coercivity.slice_ibp_eta
import Submission.Work.Spaces.sin_two_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Continuity of the angular slices at the endpoints of `Iθ` -/

/-- The angular slice `θ ↦ g z θ` of a function smooth on a neighbourhood of the closed
quadrant is continuous at every point of the open interval `(-1, π/2+1)` — in particular at
the endpoints `0` and `π/2` of `Iθ`, which is what the boundary terms of the integration by
parts need. -/
theorem slice_continuousAt (g : ℝ → ℝ → ℝ) (hg : Spaces.SmoothNbhd g) {z : ℝ}
    (hz : 0 < z) {θ : ℝ} (hθ : θ ∈ Set.Ioo (-1) (π / 2 + 1)) :
    ContinuousAt (fun θ' => g z θ') θ := by
  have hmem : (z, θ) ∈ (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π / 2 + 1) : Set (ℝ × ℝ)) :=
    ⟨by simp only [Set.mem_Ioi]; linarith, hθ⟩
  have hopen : IsOpen (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π / 2 + 1) : Set (ℝ × ℝ)) :=
    isOpen_Ioi.prod isOpen_Ioo
  have hcd : ContDiffAt ℝ ⊤ (Function.uncurry g) (z, θ) := hg.contDiffAt (hopen.mem_nhds hmem)
  have hcur : ContinuousAt (fun θ' : ℝ => (z, θ')) θ :=
    continuousAt_const.prodMk continuousAt_id
  have hcomp : ContinuousAt (Function.uncurry g ∘ fun θ' : ℝ => (z, θ')) θ :=
    hcd.continuousAt.comp hcur
  have heq : (Function.uncurry g ∘ fun θ' : ℝ => (z, θ')) = fun θ' : ℝ => g z θ' := rfl
  rw [heq] at hcomp
  exact hcomp

/-- `θ ↦ sin(2θ)^p` is continuous on `ℝ` for `p ≥ 0`. -/
theorem sin_two_rpow_continuous (p : ℝ) (hp : 0 ≤ p) :
    Continuous fun θ : ℝ => (Real.sin (2 * θ)) ^ p :=
  (Real.continuous_rpow_const hp).comp
    (Real.continuous_sin.comp (continuous_const.mul continuous_id))

/-- The elementary `rpow` identity behind the splitting of the singular weight: for `x ≥ 0`,
`x^{-η}·x = x^{1-η}`.  (Both exponents are nonzero, so the identity also holds at `x = 0`.) -/
theorem rpow_neg_eta_mul_self {x : ℝ} (hx : 0 ≤ x) :
    x ^ (-Spaces.eta) * x = x ^ (1 - Spaces.eta) := by
  have hne1 : (-Spaces.eta) ≠ 0 := by
    have h := Spaces.eta_pos
    intro h'
    rw [neg_eq_zero] at h'
    linarith
  have hne2 : (1 - Spaces.eta) ≠ 0 := by
    have h := Spaces.eta_lt_one
    intro h'
    linarith
  rcases eq_or_lt_of_le hx with h | h
  · rw [← h, Real.zero_rpow hne1, Real.zero_rpow hne2]
    ring
  · have h2 : x ^ (-Spaces.eta) * x = x ^ (-Spaces.eta) * x ^ (1 : ℝ) := by
      rw [Real.rpow_one]
    rw [h2, ← Real.rpow_add h (-Spaces.eta) 1,
      show -Spaces.eta + 1 = 1 - Spaces.eta by ring]

/-! ## Vanishing of the boundary terms -/

/-- The boundary term `sin(2θ)^{1-η}·f(z,θ)·v(z,θ)²` of the `η`-weighted angular integration
by parts tends to `0` as `θ → 0⁺`: the exponent `1-η = 1/100` is positive so the first factor
tends to `0`, while `f(z,·)·v(z,·)²` is continuous (hence bounded) near `0`. -/
theorem eta_van_left (f v : ℝ → ℝ → ℝ) (hsmf : Spaces.SmoothNbhd f)
    (hsmv : Spaces.SmoothNbhd v) {z : ℝ} (hz : 0 < z) :
    Filter.Tendsto (fun θ : ℝ => (Real.sin (2 * θ)) ^ (1 - Spaces.eta) * (f z θ * (v z θ) ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h1m : (0 : ℝ) ≤ 1 - Spaces.eta := by
    have h := Spaces.eta_lt_one
    linarith
  have hne : (1 - Spaces.eta) ≠ 0 := by
    have h := Spaces.eta_lt_one
    intro h'
    linarith
  have hmem0 : (0 : ℝ) ∈ Set.Ioo (-1) (π / 2 + 1) :=
    ⟨by norm_num, by linarith [Real.pi_pos]⟩
  have hw : Filter.Tendsto (fun θ : ℝ => (Real.sin (2 * θ)) ^ (1 - Spaces.eta))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : ContinuousAt (fun θ : ℝ => (Real.sin (2 * θ)) ^ (1 - Spaces.eta)) 0 :=
      (sin_two_rpow_continuous (1 - Spaces.eta) h1m).continuousAt
    have hz1 : (0 : ℝ) ^ (1 - Spaces.eta) = 0 := Real.zero_rpow hne
    have hz2 : Real.sin (2 * (0 : ℝ)) ^ (1 - Spaces.eta) = 0 := by
      rw [show (2 : ℝ) * 0 = 0 by ring, Real.sin_zero]
      exact Real.zero_rpow hne
    have hz3 : Real.sin 0 ^ (1 - Spaces.eta) = 0 := by
      rw [Real.sin_zero]
      exact Real.zero_rpow hne
    simpa [hz1, hz2, hz3] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hr : Filter.Tendsto (fun θ : ℝ => f z θ * (v z θ) ^ 2) (𝓝[>] (0 : ℝ))
      (𝓝 (f z 0 * (v z 0) ^ 2)) :=
    (((slice_continuousAt f hsmf hz hmem0).mul
        ((slice_continuousAt v hsmv hz hmem0).pow 2)).tendsto).mono_left nhdsWithin_le_nhds
  simpa using hw.mul hr

/-- The boundary term `sin(2θ)^{1-η}·f(z,θ)·v(z,θ)²` tends to `0` as `θ → π/2⁻`, since
`sin(2θ) → sin π = 0` and the exponent `1-η` is positive. -/
theorem eta_van_right (f v : ℝ → ℝ → ℝ) (hsmf : Spaces.SmoothNbhd f)
    (hsmv : Spaces.SmoothNbhd v) {z : ℝ} (hz : 0 < z) :
    Filter.Tendsto (fun θ : ℝ => (Real.sin (2 * θ)) ^ (1 - Spaces.eta) * (f z θ * (v z θ) ^ 2))
      (𝓝[<] (π / 2)) (𝓝 0) := by
  have h1m : (0 : ℝ) ≤ 1 - Spaces.eta := by
    have h := Spaces.eta_lt_one
    linarith
  have hne : (1 - Spaces.eta) ≠ 0 := by
    have h := Spaces.eta_lt_one
    intro h'
    linarith
  have hmemp : (π / 2) ∈ Set.Ioo (-1) (π / 2 + 1) :=
    ⟨by linarith [Real.pi_pos], by linarith⟩
  have hw : Filter.Tendsto (fun θ : ℝ => (Real.sin (2 * θ)) ^ (1 - Spaces.eta))
      (𝓝[<] (π / 2)) (𝓝 0) := by
    have hc : ContinuousAt (fun θ : ℝ => (Real.sin (2 * θ)) ^ (1 - Spaces.eta)) (π / 2) :=
      (sin_two_rpow_continuous (1 - Spaces.eta) h1m).continuousAt
    have hz1 : (0 : ℝ) ^ (1 - Spaces.eta) = 0 := Real.zero_rpow hne
    have hz2 : Real.sin (2 * (π / 2)) ^ (1 - Spaces.eta) = 0 := by
      rw [show (2 : ℝ) * (π / 2) = π by ring, Real.sin_pi]
      exact Real.zero_rpow hne
    have hz3 : Real.sin π ^ (1 - Spaces.eta) = 0 := by
      rw [Real.sin_pi]
      exact Real.zero_rpow hne
    simpa [hz1, hz2, hz3] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hr : Filter.Tendsto (fun θ : ℝ => f z θ * (v z θ) ^ 2) (𝓝[<] (π / 2))
      (𝓝 (f z (π / 2) * (v z (π / 2)) ^ 2)) :=
    (((slice_continuousAt f hsmf hz hmemp).mul
        ((slice_continuousAt v hsmv hz hmemp).pow 2)).tendsto).mono_left nhdsWithin_le_nhds
  simpa using hw.mul hr

/-! ## The two integrability hypotheses -/

/-- Continuity on `Iθ` of `θ ↦ v(z,θ)²·(D_θf(z,θ)/2 + (1-η)cos(2θ)·f(z,θ))`, the factor by
which the integrable weight `sin(2θ)^{-η}` is multiplied on the right-hand side. -/
theorem continuousOn_eta_Kcont (f v : ℝ → ℝ → ℝ) (hsmf : Spaces.SmoothNbhd f)
    (hsmv : Spaces.SmoothNbhd v) {z : ℝ} (hz : 0 < z) :
    ContinuousOn (fun θ => (v z θ) ^ 2 * (Spaces.Dth f z θ / 2
      + (1 - Spaces.eta) * Real.cos (2 * θ) * f z θ)) Spaces.Iθ := by
  have hpth : ContinuousOn (fun θ => Spaces.pth f z θ) Spaces.Iθ :=
    Coercivity.slice_pth_continuousOn f hsmf hz
  have hf : ContinuousOn (fun θ => f z θ) Spaces.Iθ := Coercivity.slice_continuousOn f hsmf hz
  have hv : ContinuousOn (fun θ => v z θ) Spaces.Iθ := Coercivity.slice_continuousOn v hsmv hz
  have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) Spaces.Iθ :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have hcos : ContinuousOn (fun θ : ℝ => Real.cos (2 * θ)) Spaces.Iθ :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn
  have hcη : ContinuousOn (fun _ : ℝ => (1 - Spaces.eta)) Spaces.Iθ := continuousOn_const
  have hDthf : ContinuousOn (fun θ => Spaces.Dth f z θ) Spaces.Iθ :=
    hsin.mul hpth
  have hinner : ContinuousOn (fun θ => Spaces.Dth f z θ / 2
      + (1 - Spaces.eta) * Real.cos (2 * θ) * f z θ) Spaces.Iθ :=
    (hDthf.div_const 2).add ((hcη.mul hcos).mul hf)
  exact (hv.pow 2).mul hinner

/-- Continuity on `Iθ` of `θ ↦ sin(2θ)^{1-η}·f(z,θ)·∂_θv(z,θ)·v(z,θ)`: the singular weight
has been absorbed by the `sin(2θ)` carried by `D_θ`, and `1-η ≥ 0`. -/
theorem continuousOn_eta_Acont (f v : ℝ → ℝ → ℝ) (hsmf : Spaces.SmoothNbhd f)
    (hsmv : Spaces.SmoothNbhd v) {z : ℝ} (hz : 0 < z) :
    ContinuousOn (fun θ => (Real.sin (2 * θ)) ^ (1 - Spaces.eta)
      * (f z θ * Spaces.pth v z θ * v z θ)) Spaces.Iθ := by
  have h1m : (0 : ℝ) ≤ 1 - Spaces.eta := by
    have h := Spaces.eta_lt_one
    linarith
  have hf : ContinuousOn (fun θ => f z θ) Spaces.Iθ := Coercivity.slice_continuousOn f hsmf hz
  have hv : ContinuousOn (fun θ => v z θ) Spaces.Iθ := Coercivity.slice_continuousOn v hsmv hz
  have hpthv : ContinuousOn (fun θ => Spaces.pth v z θ) Spaces.Iθ :=
    Coercivity.slice_pth_continuousOn v hsmv hz
  have h := ((sin_two_rpow_continuous (1 - Spaces.eta) h1m).continuousOn).mul
    ((hf.mul hpthv).mul hv)
  exact h

/-- The integrand of the `hint` hypothesis of `ibp_hard` splits, at every point of `Iθ`, into
the continuous-with-respect-to-the-weight pieces `sin(2θ)^{1-η}·f·∂_θv·v` and
`sin(2θ)^{-η}·v²·(D_θf/2 + (1-η)cos(2θ)·f)`. -/
theorem eta_hint_pointwise (f v : ℝ → ℝ → ℝ) (z θ : ℝ) (hθ : θ ∈ Spaces.Iθ) :
    (Real.sin (2 * θ)) ^ (-Spaces.eta)
        * (f z θ * Spaces.Dth v z θ * v z θ
          + (v z θ) ^ 2 * (Spaces.Dth f z θ / 2
              + (1 - Spaces.eta) * Real.cos (2 * θ) * f z θ))
      = (Real.sin (2 * θ)) ^ (1 - Spaces.eta) * (f z θ * Spaces.pth v z θ * v z θ)
        + (Real.sin (2 * θ)) ^ (-Spaces.eta)
            * ((v z θ) ^ 2 * (Spaces.Dth f z θ / 2
                + (1 - Spaces.eta) * Real.cos (2 * θ) * f z θ)) := by
  have hsin : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hDv : Spaces.Dth v z θ = Real.sin (2 * θ) * Spaces.pth v z θ := rfl
  have hDf : Spaces.Dth f z θ = Real.sin (2 * θ) * Spaces.pth f z θ := rfl
  have h1 : (Real.sin (2 * θ)) ^ (-Spaces.eta)
        * (f z θ * (Real.sin (2 * θ) * Spaces.pth v z θ) * v z θ
          + (v z θ) ^ 2 * ((Real.sin (2 * θ) * Spaces.pth f z θ) / 2
              + (1 - Spaces.eta) * Real.cos (2 * θ) * f z θ))
      = ((Real.sin (2 * θ)) ^ (-Spaces.eta) * Real.sin (2 * θ))
          * (f z θ * Spaces.pth v z θ * v z θ)
        + (Real.sin (2 * θ)) ^ (-Spaces.eta)
            * ((v z θ) ^ 2 * ((Real.sin (2 * θ) * Spaces.pth f z θ) / 2
                + (1 - Spaces.eta) * Real.cos (2 * θ) * f z θ)) := by
    ring
  rw [hDv, hDf, h1, rpow_neg_eta_mul_self hsin]

/-- The integrand of the `hint` hypothesis of `ibp_hard` — i.e. of
`sin(2θ)^{-η}·(f·D_θv·v + v²·(D_θf/2 + (1-η)cos(2θ)f))` — is integrable on `Iθ`. -/
theorem integrableOn_eta_hint (f v : ℝ → ℝ → ℝ) (hsmf : Spaces.SmoothNbhd f)
    (hsmv : Spaces.SmoothNbhd v) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-Spaces.eta)
      * (f z θ * Spaces.Dth v z θ * v z θ
        + (v z θ) ^ 2 * (Spaces.Dth f z θ / 2
            + (1 - Spaces.eta) * Real.cos (2 * θ) * f z θ))) Spaces.Iθ := by
  have hA : MeasureTheory.IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (1 - Spaces.eta)
      * (f z θ * Spaces.pth v z θ * v z θ)) Spaces.Iθ :=
    (continuousOn_eta_Acont f v hsmf hsmv hz).integrableOn_Icc
  have hB : MeasureTheory.IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-Spaces.eta)
      * ((v z θ) ^ 2 * (Spaces.Dth f z θ / 2
          + (1 - Spaces.eta) * Real.cos (2 * θ) * f z θ))) Spaces.Iθ :=
    Coercivity.integrableOn_sin_two_eta_neg.mul_continuousOn
      (continuousOn_eta_Kcont f v hsmf hsmv hz) isCompact_Icc
  have hsum : MeasureTheory.IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (1 - Spaces.eta)
        * (f z θ * Spaces.pth v z θ * v z θ)
      + (Real.sin (2 * θ)) ^ (-Spaces.eta) * ((v z θ) ^ 2 * (Spaces.Dth f z θ / 2
          + (1 - Spaces.eta) * Real.cos (2 * θ) * f z θ))) Spaces.Iθ := hA.add hB
  refine hsum.congr_fun (fun θ hθ => ?_) measurableSet_Icc
  exact (eta_hint_pointwise f v z θ hθ).symm

/-- The integrand of the `hK` hypothesis of `ibp_hard`,
`v²·(D_θf/2 + (1-η)cos(2θ)f)·sin(2θ)^{-η}`, is integrable on `Iθ`. -/
theorem integrableOn_eta_K (f v : ℝ → ℝ → ℝ) (hsmf : Spaces.SmoothNbhd f)
    (hsmv : Spaces.SmoothNbhd v) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => (v z θ) ^ 2 * (Spaces.Dth f z θ / 2
        + (1 - Spaces.eta) * Real.cos (2 * θ) * f z θ)
        * (Real.sin (2 * θ)) ^ (-Spaces.eta)) Spaces.Iθ := by
  have h := Coercivity.integrableOn_sin_two_eta_neg.mul_continuousOn
    (continuousOn_eta_Kcont f v hsmf hsmv hz) isCompact_Icc
  refine h.congr_fun (fun θ _ => ?_) measurableSet_Icc
  ring

/-- The angular integration by parts for the `D_z`-slot weight `sin(2θ)^{-η}` (`η = 99/100 < 1`),
with every hypothesis of `Work.FTS.H2.ibp_hard` discharged from smoothness of `f`, `v` on a
neighbourhood of the closed quadrant: for `z > 0`,
`∫_θ f·D_θ(v)·v·sin(2θ)^{-η} = -∫_θ v²·(D_θf/2 + (1-η)cos(2θ)·f)·sin(2θ)^{-η}`.
Route: `ibp_hard η f v hsmf hsmv eta_pos (by norm_num : η < 2) hz`; the boundary terms vanish
because `sin(2θ)^{1-η} → 0` at `θ = 0, π/2` while `f·v²` is continuous (hence bounded) there,
and both interval-integrability hypotheses follow because the integrands are `sin(2θ)^{1-η}`
(resp. `sin(2θ)^{-η}`) times a function continuous on the compact `Iθ`:
`sin(2θ)^{-η}·f·D_θv·v = sin(2θ)^{1-η}·f·(∂_θv)·v`, while `sin(2θ)^{-η}` is integrable since
`-1 < -η`; use `Work.Spaces.sin_two_rpow`, `MeasureTheory.IntegrableOn.mul_continuousOn`,
`ContinuousOn.integrableOn_compact`, `Work.Coercivity.slice_pth_continuousOn`, and mirror
`Work.Coercivity.slice_ibp_eta`. -/
theorem IbpHardEta (f v : ℝ → ℝ → ℝ) (hsmf : Work.Spaces.SmoothNbhd f)
    (hsmv : Work.Spaces.SmoothNbhd v) {z : ℝ} (hz : 0 < z) :
    ∫ θ in Work.Spaces.Iθ, f z θ * Work.Spaces.Dth v z θ * v z θ
        * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)
      = -∫ θ in Work.Spaces.Iθ, (v z θ) ^ 2 * (Work.Spaces.Dth f z θ / 2
          + (1 - Work.Spaces.eta) * Real.cos (2 * θ) * f z θ)
          * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) := by
  have hpi : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  refine ibp_hard Work.Spaces.eta f v hsmf hsmv Work.Spaces.eta_pos
    (by norm_num [Work.Spaces.eta]) hz ?_ ?_ ?_ ?_
  · exact eta_van_left f v hsmf hsmv hz
  · exact eta_van_right f v hsmf hsmv hz
  · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hpi).mpr
      ((integrableOn_eta_hint f v hsmf hsmv hz).mono_set Set.Ioc_subset_Icc_self)
  · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hpi).mpr
      ((integrableOn_eta_K f v hsmf hsmv hz).mono_set Set.Ioc_subset_Icc_self)

end Work.FTS.H2
