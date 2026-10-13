import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Submission.Work.Spaces.Defs
import Submission.Work.FM.Defs
import Submission.Work.Construction.Defs
import Submission.Work.FTS.StrongEps.EpsMem

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.StrongEps.E5Aux

/-!
# Dominated convergence of the `θ`-integral defining `L₁₂^K`, from a pointwise slot bound

The angular density of the fundamental model is

`L12dens K f s = ∫_θ K(θ) f(s,θ) / s`   (`θ` over `Iθ = [0,π/2]`),

with `K(θ) = 3 sin θ cos²θ`.  This file shows that a *pointwise* domination of the
`(z,θ)`-slots `Yk k` by `C / sin(2θ)` — together with a.e. strong measurability and pointwise
convergence *on the open quadrant* `Qd = (0,∞) × (0,π/2)` — yields both the integrability of
every angular density `θ ↦ K θ * Yk k s θ` (for `s > 0`) and the convergence of the densities
`L12dens K (Yk k) s` at every `s > 0`, by the dominated convergence theorem.

The mechanism: on `Iθ` the domination collapses,

`K θ * (C / sin 2θ) = (3C/2) cos θ`   (`θ ∈ (0,π/2)`),

and `θ ↦ (3C/2) cos θ` is bounded (hence integrable on the finite measure `Iθ`).  At the two
endpoints `K` vanishes, so the pointwise bounds and the pointwise convergence extend to all of
`Iθ` without hypotheses; the only thing the pointwise convergence needs on the open quadrant is
continuity of multiplication by the constant `K θ`.
-/

/-- `[0,π/2]` is measurable. -/
private lemma Iθ_measurableSet : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc

/-- `cos θ ≥ 0` on `[0,π/2]`. -/
private lemma cos_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.cos θ :=
  Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩

/-- `K θ ≥ 0` on `[0,π/2]`. -/
private lemma K_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Work.Spaces.K θ := by
  have hsin : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have h2 : 0 ≤ Real.cos θ ^ 2 := sq_nonneg _
  rw [Work.Spaces.K]
  nlinarith [hsin, h2]

/-- A pointwise property of all points of `Iθ` holds a.e. for the restricted measure. -/
private lemma ae_restrict_Iθ_of_forall {p : ℝ → Prop} (hp : ∀ θ ∈ Work.Spaces.Iθ, p θ) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), p θ :=
  (MeasureTheory.ae_restrict_iff' Iθ_measurableSet).2
    (Filter.Eventually.of_forall fun θ hθ => hp θ hθ)

/-- **The collapsing domination.**  On `Iθ`, if `|y| ≤ C / sin(2θ)` (a bound that is only
assumed on the open interval, the endpoints being handled by `K = 0`), then
`|K θ * y| ≤ (3C/2) cos θ`. -/
private lemma abs_K_mul_le {C : ℝ} (hC : 0 ≤ C) {θ y : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    (hy : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) → |y| ≤ C / Real.sin (2 * θ)) :
    |Work.Spaces.K θ * y| ≤ 3 * C / 2 * Real.cos θ := by
  rcases eq_or_lt_of_le hθ.1 with h0 | h0
  · have hθ0 : θ = 0 := h0.symm
    subst hθ0
    rw [Work.Spaces.K]
    simp only [Real.sin_zero, Real.cos_zero, mul_zero, one_pow, zero_mul, abs_zero, mul_one]
    linarith [hC]
  · rcases eq_or_lt_of_le hθ.2 with h2 | h2
    · subst h2
      rw [Work.Spaces.K]
      simp
    · have hIoo : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨h0, h2⟩
      have hsin : 0 < Real.sin θ :=
        Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [h2, Real.pi_pos])
      have hcos : 0 < Real.cos θ :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith [h0, Real.pi_pos], h2⟩
      have hKnn : 0 ≤ Work.Spaces.K θ := K_nonneg_of_mem_Iθ hθ
      have hkey : Work.Spaces.K θ * (C / Real.sin (2 * θ)) = 3 * C / 2 * Real.cos θ := by
        rw [Work.Spaces.K, Real.sin_two_mul]
        field_simp
      calc |Work.Spaces.K θ * y| = Work.Spaces.K θ * |y| := by
            rw [abs_mul, abs_of_nonneg hKnn]
        _ ≤ Work.Spaces.K θ * (C / Real.sin (2 * θ)) :=
            mul_le_mul_of_nonneg_left (hy hIoo) hKnn
        _ = 3 * C / 2 * Real.cos θ := hkey

theorem dens_tendsto_of_slot_tendsto {Yk : ℕ → ℝ → ℝ → ℝ} {Y : ℝ → ℝ → ℝ} {C : ℝ}
    (hC : 0 ≤ C)
    (hmeas : ∀ k : ℕ, ∀ s ∈ Set.Ioi (0 : ℝ),
      MeasureTheory.AEStronglyMeasurable (fun θ => Work.Spaces.K θ * Yk k s θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hmeasl : ∀ s ∈ Set.Ioi (0 : ℝ),
      MeasureTheory.AEStronglyMeasurable (fun θ => Work.Spaces.K θ * Y s θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hdom : ∀ k : ℕ, ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      |Yk k z θ| ≤ C / Real.sin (2 * θ))
    (hdoml : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      |Y z θ| ≤ C / Real.sin (2 * θ))
    (hconv : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Filter.Tendsto (fun k : ℕ => Yk k z θ) Filter.atTop (nhds (Y z θ))) :
    (∀ k : ℕ, ∀ s ∈ Set.Ioi (0 : ℝ),
      MeasureTheory.IntegrableOn (fun θ => Work.Spaces.K θ * Yk k s θ) Work.Spaces.Iθ) ∧
    (∀ s ∈ Set.Ioi (0 : ℝ),
      MeasureTheory.IntegrableOn (fun θ => Work.Spaces.K θ * Y s θ) Work.Spaces.Iθ) ∧
    (∀ s ∈ Set.Ioi (0 : ℝ), Filter.Tendsto
      (fun k : ℕ => Work.FM.L12dens Work.Spaces.K (Yk k) s) Filter.atTop
      (nhds (Work.FM.L12dens Work.Spaces.K Y s))) := by
  -- The dominating function: `K θ / sin(2θ) = (3C/2) cos θ` on the open interval.
  have hbound : MeasureTheory.Integrable (fun θ : ℝ => 3 * C / 2 * Real.cos θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (continuous_const.mul Real.continuous_cos).continuousOn.integrableOn_compact isCompact_Icc
  -- Its norm is itself on `Iθ`.
  have hnorm : ∀ θ ∈ Work.Spaces.Iθ,
      ‖3 * C / 2 * Real.cos θ‖ = 3 * C / 2 * Real.cos θ := by
    intro θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (by linarith [hC]) (cos_nonneg_of_mem_Iθ hθ))]
  -- The a.e. domination of the angular density of any slot family satisfying the slot bound.
  have habs : ∀ (Z : ℕ → ℝ → ℝ → ℝ),
      (∀ k : ℕ, ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
        |Z k z θ| ≤ C / Real.sin (2 * θ)) →
      ∀ k : ℕ, ∀ s ∈ Set.Ioi (0 : ℝ),
        ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
          ‖Work.Spaces.K θ * Z k s θ‖ ≤ 3 * C / 2 * Real.cos θ := by
    intro Z hdm k s hs
    refine ae_restrict_Iθ_of_forall fun θ hθ => ?_
    rw [Real.norm_eq_abs]
    exact abs_K_mul_le hC hθ (fun hh => hdm k s θ ⟨hs, hh⟩)
  -- Integrability of the angular densities.
  have key : ∀ (Z : ℕ → ℝ → ℝ → ℝ),
      (∀ k : ℕ, ∀ s ∈ Set.Ioi (0 : ℝ),
        MeasureTheory.AEStronglyMeasurable (fun θ => Work.Spaces.K θ * Z k s θ)
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) →
      (∀ k : ℕ, ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
        |Z k z θ| ≤ C / Real.sin (2 * θ)) →
      ∀ k : ℕ, ∀ s ∈ Set.Ioi (0 : ℝ),
        MeasureTheory.IntegrableOn (fun θ => Work.Spaces.K θ * Z k s θ) Work.Spaces.Iθ := by
    intro Z hms hdm k s hs
    refine MeasureTheory.Integrable.mono hbound (hms k s hs) ?_
    filter_upwards [habs Z hdm k s hs, MeasureTheory.ae_restrict_mem Iθ_measurableSet]
      with θ h1 h2
    rwa [hnorm θ h2]
  refine ⟨?_, ?_, ?_⟩
  · exact fun k s hs => key Yk hmeas hdom k s hs
  · intro s hs
    exact key (fun _ : ℕ => Y) (fun _ s' hs' => hmeasl s' hs')
      (fun _ z θ hzθ => hdoml z θ hzθ) 0 s hs
  · intro s hs
    have hconvae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        Filter.Tendsto (fun k : ℕ => Work.Spaces.K θ * Yk k s θ) Filter.atTop
          (nhds (Work.Spaces.K θ * Y s θ)) := by
      refine ae_restrict_Iθ_of_forall fun θ hθ => ?_
      rcases eq_or_lt_of_le hθ.1 with h0 | h0
      · have hθ0 : θ = 0 := h0.symm
        subst hθ0
        simp [Work.Spaces.K]
      · rcases eq_or_lt_of_le hθ.2 with h2 | h2
        · subst h2
          simp [Work.Spaces.K]
        · exact (hconv s θ ⟨hs, ⟨h0, h2⟩⟩).const_mul (Work.Spaces.K θ)
    have hmain := MeasureTheory.tendsto_integral_of_dominated_convergence
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (F := fun (k : ℕ) (θ : ℝ) => Work.Spaces.K θ * Yk k s θ)
      (f := fun θ : ℝ => Work.Spaces.K θ * Y s θ)
      (fun θ : ℝ => 3 * C / 2 * Real.cos θ)
      (fun k => hmeas k s hs) hbound (fun k => habs Yk hdom k s hs) hconvae
    simpa only [Work.FM.L12dens, Work.Spaces.Iθ, MeasureTheory.integral_div]
      using hmain.div_const s

end Work.FTS.StrongEps.E5Aux
