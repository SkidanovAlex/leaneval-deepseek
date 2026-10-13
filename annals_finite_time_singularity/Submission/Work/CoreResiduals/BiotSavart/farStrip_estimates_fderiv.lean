import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.CoreResiduals.Defs
import Submission.Work.LWP.FarField
import Submission.Work.StabilityFar.Decay.fderiv_timeHolder
import Submission.Work.StabilityFar.Decay.farField_fderiv_sub_le
import Submission.Work.CoreResiduals.BiotSavart.bsDeriv_sub_le_of_close

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

open MeasureTheory

/-- **The far-field estimates for the spatial block `D(x,t) = fderiv ℝ (BS (ω·t)) x` on the strip**
`Icc 0 S` (one-sided in `t`).

This is the strip version of the three far-field inputs that `Work.StabilityFar.St4` consumes
(`Work.StabilityFar.fderiv_decay`, `Work.StabilityFar.Decay.fderiv_timeHolder`,
`Work.StabilityFar.FarDerivLipschitz`), with the *window* `Icc (-1) (T+1)`-indexed hypotheses
replaced by the strip bundle `BSAdmissibleStripFull α ω R S` restricted to `Icc 0 S` (all three
proofs are per-slice, so they adapt verbatim; the `t`-Hölder clause of the bundle is global in `y`,
which is stronger than the `TimeHolderOnBall` hypothesis of the window version).

* *bound*: `‖D(x,t)‖ ≤ 2^20 · M · R³ / ‖x‖³` for `2R ≤ ‖x‖`, `t ∈ Icc 0 S` — per-slice
  `Work.LWP.BiotSavart.farField_decay_fderiv_const` with the slice's bound and support;
* *`t`-Hölder*: `‖D(x,t) - D(x,τ)‖ ≤ At · |t-τ|^α` for `2R < ‖x‖` and `t,τ ∈ Icc 0 S` — the
  difference of the two kernels is the kernel of the difference vorticity, which is supported in
  `B(0,R)` and bounded by `H|t-τ|^α` there (bundle's time-Hölder clause);
* *`x`-Lipschitz*: `‖D(x,t) - D(y,t)‖ ≤ A‖x-y‖` for `2R < ‖x‖, 2R < ‖y‖` and `t ∈ Icc 0 S` —
  the second-order far-field estimate `Work.StabilityFar.Decay.farField_fderiv_sub_le`, per slice.

No hypothesis `0 < S` is needed (the estimates make sense for every `S`). -/
theorem farStrip_estimates_fderiv {α : NNReal} (hα : 0 < (α : ℝ)) (hα1 : (α : ℝ) < 1)
    {ω : Work.LWP.R3 → ℝ → Work.LWP.R3} {R S : ℝ}
    (hbun : Work.CoreResiduals.BSAdmissibleStripFull α ω R S) :
    ∃ M At A : ℝ, 0 ≤ M ∧ 0 ≤ At ∧ 0 ≤ A ∧
      (∀ t ∈ Set.Icc (0:ℝ) S, ∀ x : Work.LWP.R3, 2 * R ≤ ‖x‖ →
        ‖fderiv ℝ (Work.LWP.biotSavart (fun y => ω y t)) x‖
          ≤ 2 ^ 20 * M * R ^ 3 / ‖x‖ ^ 3) ∧
      (∀ x : Work.LWP.R3, 2 * R < ‖x‖ → ∀ t ∈ Set.Icc (0:ℝ) S, ∀ τ ∈ Set.Icc (0:ℝ) S,
        ‖fderiv ℝ (Work.LWP.biotSavart (fun y => ω y t)) x
          - fderiv ℝ (Work.LWP.biotSavart (fun y => ω y τ)) x‖ ≤ At * |t - τ| ^ (α : ℝ)) ∧
      (∀ t ∈ Set.Icc (0:ℝ) S, ∀ x y : Work.LWP.R3, 2 * R < ‖x‖ → 2 * R < ‖y‖ →
        ‖fderiv ℝ (Work.LWP.biotSavart (fun z => ω z t)) x
          - fderiv ℝ (Work.LWP.biotSavart (fun z => ω z t)) y‖ ≤ A * ‖x - y‖) := by
  obtain ⟨⟨hR, hsupp, ⟨M, hM⟩, ⟨H, hH⟩, ⟨N, hN⟩, hmeas⟩,
    ⟨hdc, ⟨M₁, hM₁⟩, hmeasd⟩, ⟨N₁, hN₁⟩⟩ := hbun
  -- the exponent lies in `(0,1)`; the estimates below are in fact exponent-free
  have hαpos : (0 : ℝ) < (α : ℝ) := hα
  have hαlt : (α : ℝ) < 1 := hα1
  -- positive parts of the two constants the bundle supplies
  set M₀ : ℝ := max M 0 with hM₀def
  have hM₀nn : 0 ≤ M₀ := by rw [hM₀def]; exact le_max_right M 0
  have hMle : M ≤ M₀ := by rw [hM₀def]; exact le_max_left M 0
  set N₀ : ℝ := max N 0 with hN₀def
  have hN₀nn : 0 ≤ N₀ := by rw [hN₀def]; exact le_max_right N 0
  have hNle : N ≤ N₀ := by rw [hN₀def]; exact le_max_left N 0
  -- the uniform bound and the support, per time slice of the strip
  have hslice_bdd : ∀ t ∈ Set.Icc (0:ℝ) S, ∀ a : Work.LWP.R3, ‖ω a t‖ ≤ M₀ :=
    fun t ht a => le_trans (hM t ht a) hMle
  -- the two constants of the statements
  set At : ℝ := (4 * Real.pi)⁻¹ * (N₀ * (4 / R ^ 3) * (R ^ 3 * (Real.pi * 4 / 3))) with hAtdef
  set A : ℝ := (4 * Real.pi)⁻¹ * ((M₀ * 64 / R ^ 4) * (R ^ 3 * (Real.pi * 4 / 3))) with hAdef
  have hAtnn : 0 ≤ At := by
    rw [hAtdef]
    exact mul_nonneg (by positivity)
      (mul_nonneg (mul_nonneg hN₀nn (div_nonneg (by norm_num) (pow_nonneg hR.le 3)))
        (mul_nonneg (pow_nonneg hR.le 3) (by positivity)))
  have hAnn : 0 ≤ A := by
    rw [hAdef]
    exact mul_nonneg (by positivity)
      (mul_nonneg (div_nonneg (by positivity) (pow_nonneg hR.le 4))
        (mul_nonneg (pow_nonneg hR.le 3) (by positivity)))
  refine ⟨M₀, At, A, hM₀nn, hAtnn, hAnn, ?_, ?_, ?_⟩
  · -- far-field decay of the derivative, per slice
    intro t ht x hx
    exact Work.LWP.BiotSavart.farField_decay_fderiv_const hR hM₀nn
      (hslice_bdd t ht) (hsupp t ht) x hx
  · -- time-Hölder continuity of the spatial block
    intro x hx t ht τ hτ
    have hx2 : 2 * R ≤ ‖x‖ := le_of_lt hx
    have hdt := Work.StabilityFar.Decay.biotSavart_hasFDerivAt_far (ω := fun y => ω y t)
      hR hM₀nn (hslice_bdd t ht) (hsupp t ht) (hmeas t ht) hx2
    have hdτ := Work.StabilityFar.Decay.biotSavart_hasFDerivAt_far (ω := fun y => ω y τ)
      hR hM₀nn (hslice_bdd τ hτ) (hsupp τ hτ) (hmeas τ hτ) hx2
    rw [hdt.2.fderiv, hdτ.2.fderiv]
    have hCnn : 0 ≤ N₀ * |t - τ| ^ (α : ℝ) :=
      mul_nonneg hN₀nn (Real.rpow_nonneg (abs_nonneg _) _)
    have hdiff : ∀ a ∈ Metric.closedBall (0 : Work.LWP.R3) R,
        ‖(fun y => ω y t) a - (fun y => ω y τ) a‖ ≤ N₀ * |t - τ| ^ (α : ℝ) := by
      intro a _
      exact le_trans (hN a t ht τ hτ)
        (mul_le_mul_of_nonneg_right hNle (Real.rpow_nonneg (abs_nonneg _) _))
    have hmain := bsDeriv_sub_le_of_close hR hM₀nn hCnn (hslice_bdd t ht) (hslice_bdd τ hτ)
      (hsupp t ht) (hsupp τ hτ) (hmeas t ht) (hmeas τ hτ) hdiff hx2
    calc ‖Work.StabilityFar.Decay.bsDeriv (fun y => ω y t) x
            - Work.StabilityFar.Decay.bsDeriv (fun y => ω y τ) x‖
        ≤ (4 * Real.pi)⁻¹ * ((N₀ * |t - τ| ^ (α : ℝ)) * (4 / R ^ 3))
            * (R ^ 3 * (Real.pi * 4 / 3)) := hmain
      _ = At * |t - τ| ^ (α : ℝ) := by rw [hAtdef]; ring
  · -- the far-field `x`-Lipschitz bound, per slice
    intro t ht x y hx hy
    have hx2 : 2 * R ≤ ‖x‖ := le_of_lt hx
    have hy2 : 2 * R ≤ ‖y‖ := le_of_lt hy
    have hdx := Work.StabilityFar.Decay.biotSavart_hasFDerivAt_far (ω := fun z => ω z t)
      hR hM₀nn (hslice_bdd t ht) (hsupp t ht) (hmeas t ht) hx2
    have hdy := Work.StabilityFar.Decay.biotSavart_hasFDerivAt_far (ω := fun z => ω z t)
      hR hM₀nn (hslice_bdd t ht) (hsupp t ht) (hmeas t ht) hy2
    rw [hdx.2.fderiv, hdy.2.fderiv]
    exact Work.StabilityFar.Decay.norm_bsDeriv_sub_le hR hM₀nn
      (hslice_bdd t ht) (hsupp t ht) (hmeas t ht) hx2 hy2

end Work.CoreResiduals.BiotSavart
