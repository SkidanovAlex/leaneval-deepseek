/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS_EllLimOK.Decay.decay_of_hkMem0_jetBound`

`Work.Spaces.HkMem α 0 Ψ` is the honest `ℋ⁰`-membership: the weighted integrand
`(Ψ·w/sin(2θ)^{η/2})²` is integrable on the domain `[0,∞) × [0,π/2]`.  Together with the
pointwise jet bounds `|Ψ|`, `|D_zΨ|`, `|D_θΨ| ≤ C` on the open quadrant (and the closed-box
regularity `BoxReg`, which makes the slices differentiable), it forces the *pointwise* decay
`Ψ z θ → 0` as `z → +∞` at every interior angle `θ ∈ (0,π/2)`.

The proof is a contradiction argument.  If `|Ψ z θ₀| ≥ ε` happened infinitely often, then — since
`|z ∂_zΨ| ≤ C` forbids a tall spike of width `o(z)` — the weighted angular energy
`∫_θ HkIntegrand α 0 Ψ z' θ` would stay `≥ c > 0` on every window `[z, z+1]`, and
`∫_t HkIntegrand α 0 Ψ` would be non-integrable in `t`, contradicting `HkMem`.

The localised lower bound on the angular energy is
`Work.FTS.EllLimOK.Decay.local_energy_lower_bound`; the Lipschitz bounds on the slices and the
collapse of the `k = 0` integrand are in `Work.FTS.EllLimOK.Decay.DecayTools`.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Submission.Work.FTS_EllLimOK.BoxReg
import Submission.Work.FTS_EllLimOK.Defs3
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.Decay.local_energy_lower_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.Decay

set_option linter.unusedVariables false

theorem decay_of_hkMem0_jetBound {α C : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hbox : Work.FTS_EllLimOK.BoxReg Ψ)
    (hHk : Work.Spaces.HkMem α 0 Ψ)
    (hsup : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 → |Ψ z θ| ≤ C)
    (hDz : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      |Work.Spaces.mixed 1 0 Ψ z θ| ≤ C)
    (hDth : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      |Work.Spaces.mixed 0 1 Ψ z θ| ≤ C) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Filter.Tendsto (fun z => Ψ z θ) Filter.atTop (nhds 0) := by
  intro θ₀ hθ₀
  by_cases hC : C ≤ 0
  · -- the pointwise bound `|Ψ| ≤ C ≤ 0` kills the whole slice on the open quadrant
    have hzero : ∀ z : ℝ, 0 < z → Ψ z θ₀ = 0 := by
      intro z hz
      have h1 : |Ψ z θ₀| ≤ C :=
        hsup z θ₀ (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ₀.1, hθ₀.2⟩)
      exact abs_eq_zero.mp (le_antisymm (le_trans h1 hC) (abs_nonneg _))
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with z hz
    exact (hzero z (by linarith)).symm
  · have hCpos : 0 < C := not_le.mp hC
    rw [Metric.tendsto_atTop]
    intro ε hε
    by_contra hcon
    push_neg at hcon
    -- `hcon` says that `|Ψ z θ₀| ≥ ε` happens for arbitrarily large `z`
    have hbad : ∀ N : ℝ, ∃ z : ℝ, N ≤ z ∧ ε ≤ |Ψ z θ₀| := by
      intro N
      obtain ⟨z, hz, h⟩ := hcon N
      refine ⟨z, hz, ?_⟩
      rwa [Real.dist_eq, sub_zero] at h
    -- the localised lower bound for the angular energy
    obtain ⟨c, hcpos, hcbound⟩ :=
      local_energy_lower_bound hbox hHk hDz hDth hCpos hε hθ₀
    -- ... and the tail of the outer `z`-integral tends to `0`
    have hlim : Tendsto (fun Z : ℝ => ∫ z in Set.Ioi Z,
        ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 Ψ z θ) atTop (nhds 0) :=
      MeasureTheory.tendsto_integral_Ioi_zero
        (f := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 Ψ z θ)
        (b := fun Z : ℝ => Z) tendsto_id
    have hev : ∀ᶠ Z : ℝ in atTop,
        (∫ z in Set.Ioi Z, ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 0 Ψ z θ) < c :=
      hlim.eventually (isOpen_Iio.mem_nhds (Set.mem_Iio.mpr hcpos))
    have hZ0 : 0 ≤ max (1 : ℝ) (4 * C / ε) := le_trans zero_le_one (le_max_left _ _)
    obtain ⟨Z, hZev, hZge⟩ :=
      (hev.and (eventually_ge_atTop (max (1 : ℝ) (4 * C / ε)))).exists
    obtain ⟨z, hzge, hzval⟩ := hbad (max Z (max (1 : ℝ) (4 * C / ε)))
    have hzgeZ : Z ≤ z := le_trans (le_max_left _ _) hzge
    have hzgeZ0 : max (1 : ℝ) (4 * C / ε) ≤ z := le_trans (le_max_right _ _) hzge
    have hZnn : 0 ≤ Z := le_trans hZ0 hZge
    -- the window `[z, z+1]` carries an energy `≥ c` while lying inside `(Z,∞)`
    have hlow : c ≤ ∫ z in Set.Ioi Z,
        ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 Ψ z θ :=
      integral_Ioi_ge_of_lower_bound (Z := Z) (z := z) hzgeZ
        (hHk.2.mono_set (fun t ht => le_of_lt (lt_of_le_of_lt hZnn ht)))
        (fun t => integral_nonneg (fun θ => Work.Spaces.HkIntegrand_nonneg α 0 Ψ t θ))
        (fun t ht => hcbound z hzgeZ0 hzval t ht)
    linarith

end Work.FTS_EllLimOK.Decay
