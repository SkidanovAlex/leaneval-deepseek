import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.CoreResiduals.Defs
import Submission.Work.CoreResiduals.BiotSavart.biotSavart_contDiff_one
import Submission.Work.CoreResiduals.BiotSavart.DerivDefs
import Submission.Work.CoreResiduals.BiotSavart.norm_sub_le_of_timeDeriv_bound
import Submission.Work.CoreResiduals.BiotSavart.hasFDerivAt_biotSavart_slice
import Submission.Work.CoreResiduals.BiotSavart.biotSavart_add
import Submission.Work.CoreResiduals.BiotSavart.bsDerivCLM_bound_arith
import Submission.Work.CoreResiduals.BiotSavart.norm_bsDerivCLM_le_of_bdd_holder

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

open MeasureTheory Metric Filter
open scoped Topology
open Work.StabilityFar.Decay (kf kDerivCLM crossL)

/-! ### The mean-value/two-slice Hölder bound in the norm form -/

/-- `HolderWith` in the `dist` form, rewritten as a norm inequality. -/
theorem holder_norm_le {α : NNReal} {H : NNReal} {f : Work.LWP.R3 → Work.LWP.R3}
    (h : HolderWith H α f) (x y : Work.LWP.R3) :
    ‖f x - f y‖ ≤ (H : ℝ) * ‖x - y‖ ^ (α : ℝ) := by
  have h1 := h.dist_le x y
  rw [dist_eq_norm, dist_eq_norm] at h1
  exact h1

/-- **The `t`-Hölder continuity of the spatial block of the derivative, for a bundled strip vorticity.**

Let `0 < α < 1` and let `ω` satisfy the full strip bundle `BSAdmissibleStripFull α ω R S`
(`BSAdmissibleStrip α ω R S`: support in `closedBall 0 R`, uniform bound `M`, uniform `x`-Hölder with
constant `H`, uniform `t`-Hölder with constant `N`, measurable slices; `TimeDerivStrip ω S`: slices
`t`-differentiable with uniformly bounded `∂ₜω`, bound `M₁`, measurable; `TimeDerivStripHolder α ω S`:
`∂ₜω` is `α`-Hölder in `t`, uniformly in `x`, constant `N₁`).

Claim: on any ball `‖x‖ ≤ R'` the spatial block `x ↦ fderiv ℝ (BS (ω · t)) x` is `α`-Hölder in `t`,
uniformly in `x`: `∃ C ≥ 0, ∀ x, ‖x‖ ≤ R' → ∀ t t' ∈ Icc 0 S,
‖fderiv ℝ (BS (ω·t)) x - fderiv ℝ (BS (ω·t')) x‖ ≤ C |t-t'|^α`.

This is the crux of the space-time Schauder statement.  **Suggested route** (reportedly it closes):
write `g := ω(·,t) - ω(·,t')`, `δ := |t-t'|`.  By linearity the quantity is `‖fderiv ℝ (BS g) x‖`, and
the bundle gives, *uniformly in `t,t'`*: `supp g ⊆ closedBall 0 R`, `[g]_{C^α} ≤ 2H`,
`A := ‖g‖_∞ ≤ min(Nδ^α, M₁δ)` (the second from the mean-value bound
`norm_sub_le_of_timeDerivBound` applied to the uniform `∂ₜω`-bound `M₁` — this is the ingredient that
makes the estimate true; without it the corresponding "order-`0` CZ is `L^∞`-bounded" claim is false).
For `R + ‖x‖ < ρ` we have `fderiv ℝ (BS g) x = (4π)⁻¹ bsDerivCLM g ρ x`, i.e. the peeled integral
`∫_{B(x,ρ)} crossL (g a - g x) ∘ kDerivCLM (x-a) da + (4π/3) crossL (g x)`, whose norm is at most
`(4π)⁻¹(16π ∫_0^ρ min(2A, 2H r^α) r⁻¹ dr + (4π/3) A)`.  Splitting the integral at `λ := (A/(2H))^{1/α}`
(so `2Hλ^α = A`) gives the bound `C(α) A (1 + log(ρ/λ)) = C(α) A (1 + log ρ + (1/α) log(2H/A))`.
Since `A ↦ A log(2H/A)` is increasing for small `A` and `A ≤ min(Nδ^α, M₁δ)`, there are two regimes:
`δ ≥ (N/M₁)^{1/(1-α)}` gives `C(α)N log(2H/(Nδ^α))·δ^α ≤ C(α,data) δ^α`, and
`δ < (N/M₁)^{1/(1-α)}` gives `C(α)M₁δ(1+log(ρ/(M₁δ)^{1/α})) ≤ C(α,data) δ^α` by the classical
`δ log(1/δ) ≤ C(α)δ^α` for `α < 1`.  Hence the claimed estimate with a constant depending only on
`α, R, R', M, H, N, M₁, N₁, S`.  (The `x`-direction, the whole `t`-block and the `C¹` clause are
separate; the far field `2R < ‖x‖` is handled by the decay estimates.)

**Actual route used** (avoids the logarithmic split entirely): the bound on the peeled integral is
obtained by interpolating the two pointwise bounds `‖g a - g x‖ ≤ 2A` and
`‖g a - g x‖ ≤ 2H‖a - x‖^α` as
`min(2A, 2H‖a-x‖^α) ≤ (2A)^α (2H‖a-x‖^α)^{1-α}`, which upgrades the singular weight `‖a-x‖^{-3}`
to the integrable `‖a-x‖^{α(1-α)-3}`; the ball integral is then
`4(2A)^α(2H)^{1-α}·4π(ρ+‖x‖)^{α(1-α)}/(α(1-α))` (`integral_ball_sub_norm_rpow`).  With `A = M₀·δ`
(`M₀ = max M₁ 0`) this is `O(δ^α)` directly.  The two ingredients are
`norm_bsDerivCLM_le_of_bdd_holder` and `bsDerivCLM_bound_arith` (delegated, in this directory). -/
theorem biotSavart_fderiv_timeHolder_of_bundle {α : NNReal} (hα : 0 < (α : ℝ)) (hα1 : (α : ℝ) < 1)
    {ω : Work.LWP.R3 → ℝ → Work.LWP.R3} {R S R' : ℝ}
    (hbun : Work.CoreResiduals.BSAdmissibleStripFull α ω R S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Work.LWP.R3, ‖x‖ ≤ R' →
      ∀ t ∈ Set.Icc (0:ℝ) S, ∀ t' ∈ Set.Icc (0:ℝ) S,
        ‖fderiv ℝ (Work.LWP.biotSavart (fun a => ω a t)) x
          - fderiv ℝ (Work.LWP.biotSavart (fun a => ω a t')) x‖
          ≤ C * |t - t'| ^ (α : ℝ) := by
  obtain ⟨⟨hR, hsupp, ⟨M, hM⟩, ⟨H, hH⟩, ⟨N, hN⟩, hmeas⟩, ⟨hdc, ⟨M₁, hM₁⟩, hmeasd⟩, ⟨N₁, hN₁⟩⟩ :=
    hbun
  set M₀ : ℝ := max M₁ 0 with hM₀def
  have hM₀nn : 0 ≤ M₀ := by rw [hM₀def]; exact le_max_right M₁ 0
  set H₀ : ℝ := (H : ℝ) with hH₀def
  have hH₀nn : 0 ≤ H₀ := by rw [hH₀def]; positivity
  set P : ℝ := max 0 (R + 2 * R' + 1) with hPdef
  have hPnn : 0 ≤ P := by rw [hPdef]; exact le_max_left 0 (R + 2 * R' + 1)
  set C₀ : ℝ := 4 * (2 * M₀) ^ (α : ℝ) * (2 * H₀) ^ (1 - (α : ℝ)) *
        (4 * Real.pi * P ^ ((α : ℝ) * (1 - (α : ℝ))) / ((α : ℝ) * (1 - (α : ℝ))))
      + (4 * Real.pi / 3) * (M₀ * max 1 S) with hC₀def
  refine ⟨(4 * Real.pi)⁻¹ * C₀, ?_, ?_⟩
  · have h4π : (0:ℝ) < 4 * Real.pi := by positivity
    have hnum : (0:ℝ) < (α : ℝ) * (1 - (α : ℝ)) := mul_pos hα (by linarith)
    have h2M : 0 ≤ 2 * M₀ := by linarith
    have h2H : 0 ≤ 2 * H₀ := by linarith
    have h1 : 0 ≤ (2 * M₀) ^ (α : ℝ) := Real.rpow_nonneg h2M _
    have h2 : 0 ≤ (2 * H₀) ^ (1 - (α : ℝ)) := Real.rpow_nonneg h2H _
    have h3 : 0 ≤ P ^ ((α : ℝ) * (1 - (α : ℝ))) := Real.rpow_nonneg hPnn _
    have h5 : 0 ≤ M₀ * max 1 S := by positivity
    have hC0 : 0 ≤ C₀ := by
      rw [hC₀def]
      have h6 : (0:ℝ) ≤ 4 * Real.pi * P ^ ((α:ℝ) * (1 - (α:ℝ))) / ((α:ℝ) * (1 - (α:ℝ))) :=
        div_nonneg (by positivity) hnum.le
      have h7 : (0:ℝ) ≤ 4 * (2 * M₀) ^ (α:ℝ) * (2 * H₀) ^ (1 - (α:ℝ)) :=
        mul_nonneg (by positivity) h2
      have h8 : (0:ℝ) ≤ 4 * (2 * M₀) ^ (α:ℝ) * (2 * H₀) ^ (1 - (α:ℝ)) *
          (4 * Real.pi * P ^ ((α:ℝ) * (1 - (α:ℝ))) / ((α:ℝ) * (1 - (α:ℝ)))) :=
        mul_nonneg h7 h6
      have h9 : (0:ℝ) ≤ 4 * Real.pi / 3 * (M₀ * max 1 S) := mul_nonneg (by positivity) h5
      linarith
    have : (0:ℝ) ≤ (4 * Real.pi)⁻¹ := by positivity
    exact mul_nonneg this hC0
  · intro x hx t ht t' ht'
    have ht0 : 0 ≤ t := ht.1
    have htS : t ≤ S := ht.2
    have ht'0 : 0 ≤ t' := ht'.1
    have ht'S : t' ≤ S := ht'.2
    set δ : ℝ := |t - t'| with hδdef
    have hδnn : 0 ≤ δ := by rw [hδdef]; exact abs_nonneg _
    have hδS : δ ≤ S := by
      rw [hδdef, abs_le]
      exact ⟨by linarith, by linarith⟩
    -- the vorticity bundle facts for the slices
    have hMnn : 0 ≤ M := le_trans (norm_nonneg (ω 0 t)) (hM t ht 0)
    have hslice : ∀ s ∈ Set.Icc (0:ℝ) S, ∀ a b : Work.LWP.R3,
        ‖ω a s - ω b s‖ ≤ H₀ * ‖a - b‖ ^ (α : ℝ) := by
      intro s hs a b
      rw [hH₀def]
      exact holder_norm_le (hH s hs) a b
    -- the difference field
    set g : Work.LWP.R3 → Work.LWP.R3 := fun a => ω a t - ω a t' with hgdef
    have hg_bdd : ∀ a, ‖g a‖ ≤ M₀ * δ := by
      intro a
      have h := norm_sub_le_of_timeDeriv_bound hM₀nn (convex_Icc (0:ℝ) S)
        (fun s hs y => hdc s hs y) (fun s hs y => le_trans (hM₁ s hs y) (le_max_left M₁ 0))
        t ht t' ht' a
      rw [hδdef]
      simpa only [hgdef] using h
    have hg_holder : ∀ a b : Work.LWP.R3, ‖g a - g b‖ ≤ 2 * H₀ * ‖a - b‖ ^ (α : ℝ) := by
      intro a b
      have h1 := hslice t ht a b
      have h2 := hslice t' ht' a b
      have hkey : g a - g b = (ω a t - ω b t) - (ω a t' - ω b t') := by
        simp only [hgdef]; abel
      rw [hkey]
      calc ‖(ω a t - ω b t) - (ω a t' - ω b t')‖
          ≤ ‖ω a t - ω b t‖ + ‖ω a t' - ω b t'‖ := norm_sub_le _ _
        _ ≤ H₀ * ‖a - b‖ ^ (α : ℝ) + H₀ * ‖a - b‖ ^ (α : ℝ) := add_le_add h1 h2
        _ = 2 * H₀ * ‖a - b‖ ^ (α : ℝ) := by ring
    have hg_supp : ∀ a, g a ≠ 0 → a ∈ Metric.closedBall 0 R := by
      intro a ha
      by_cases h1 : ω a t = 0
      · refine hsupp t' ht' a ?_
        intro hc
        exact ha (by simp only [hgdef, h1, hc, sub_zero])
      · exact hsupp t ht a h1
    have hg_meas : AEStronglyMeasurable g volume := by
      have h := (hmeas t ht).sub (hmeas t' ht')
      have h' : AEStronglyMeasurable (fun a : Work.LWP.R3 => ω a t - ω a t') volume := h
      rwa [hgdef]
    -- the ball radius
    set ρ : ℝ := R + ‖x‖ + 1 with hρdef
    have hρx : R + ‖x‖ < ρ := by rw [hρdef]; linarith
    have hρnn : 0 ≤ ρ := by rw [hρdef]; linarith [norm_nonneg x, hR]
    have hA : 0 ≤ M₀ * δ := mul_nonneg hM₀nn hδnn
    -- derivatives of the three fields
    have hfd_g : HasFDerivAt (Work.LWP.biotSavart g) ((4 * Real.pi)⁻¹ • bsDerivCLM g ρ x) x :=
      hasFDerivAt_biotSavart_slice (ω := g) (R := R) (M := M₀ * δ) (C := 2 * H₀)
        (c := (α : ℝ)) (ρ := ρ) hR hA hα hg_bdd hg_supp hg_meas hg_holder hρx
    have hfd_t : HasFDerivAt (Work.LWP.biotSavart (fun a => ω a t))
        ((4 * Real.pi)⁻¹ • bsDerivCLM (fun a => ω a t) ρ x) x :=
      hasFDerivAt_biotSavart_slice (ω := fun a => ω a t) (R := R) (M := M) (C := H₀)
        (c := (α : ℝ)) (ρ := ρ) hR hMnn hα (hM t ht) (hsupp t ht) (hmeas t ht)
        (hslice t ht) hρx
    have hfd_t' : HasFDerivAt (Work.LWP.biotSavart (fun a => ω a t'))
        ((4 * Real.pi)⁻¹ • bsDerivCLM (fun a => ω a t') ρ x) x :=
      hasFDerivAt_biotSavart_slice (ω := fun a => ω a t') (R := R) (M := M) (C := H₀)
        (c := (α : ℝ)) (ρ := ρ) hR hMnn hα (hM t' ht') (hsupp t' ht') (hmeas t' ht')
        (hslice t' ht') hρx
    -- linearity: `BS g = BS(ω·t) - BS(ω·t')`
    have hpt : ∀ y : Work.LWP.R3,
        Work.LWP.biotSavart (fun a => ω a t) y - Work.LWP.biotSavart (fun a => ω a t') y
          = Work.LWP.biotSavart g y := by
      intro y
      have h1 : Work.LWP.biotSavart (fun a => g a + ω a t') y
          = Work.LWP.biotSavart g y + Work.LWP.biotSavart (fun a => ω a t') y :=
        biotSavart_add hg_bdd (hM t' ht') hg_supp (hsupp t' ht') hg_meas (hmeas t' ht') y
      have h2 : (fun a => g a + ω a t') = fun a => ω a t := by
        funext a; simp only [hgdef]; abel
      rw [h2] at h1
      rw [h1]; abel
    have hfd_eq : fderiv ℝ (Work.LWP.biotSavart g) x
        = fderiv ℝ (Work.LWP.biotSavart (fun a => ω a t)) x
          - fderiv ℝ (Work.LWP.biotSavart (fun a => ω a t')) x := by
      have heq : (fun y => Work.LWP.biotSavart (fun a => ω a t) y
            - Work.LWP.biotSavart (fun a => ω a t') y)
          =ᶠ[𝓝 x] Work.LWP.biotSavart g := Filter.Eventually.of_forall hpt
      have h1 : fderiv ℝ (fun y => Work.LWP.biotSavart (fun a => ω a t) y
            - Work.LWP.biotSavart (fun a => ω a t') y) x
          = fderiv ℝ (Work.LWP.biotSavart g) x := Filter.EventuallyEq.fderiv_eq heq
      rw [← h1]
      change fderiv ℝ ((Work.LWP.biotSavart (fun a => ω a t))
        - (Work.LWP.biotSavart (fun a => ω a t'))) x
          = fderiv ℝ (Work.LWP.biotSavart (fun a => ω a t)) x
            - fderiv ℝ (Work.LWP.biotSavart (fun a => ω a t')) x
      rw [fderiv_sub hfd_t.differentiableAt hfd_t'.differentiableAt]
    -- the CLM bound for the difference field
    have hQnn : 0 ≤ ρ + ‖x‖ := by linarith [norm_nonneg x, hρnn]
    have hQP : ρ + ‖x‖ ≤ P := by
      rw [hρdef, hPdef]
      refine le_trans ?_ (le_max_right 0 (R + 2 * R' + 1))
      linarith [norm_nonneg x]
    have hbound : ‖bsDerivCLM g ρ x‖ ≤ C₀ * δ ^ (α : ℝ) := by
      have hL := norm_bsDerivCLM_le_of_bdd_holder hα hα1 hA hH₀nn hρnn hg_bdd hg_holder x
      have harith := bsDerivCLM_bound_arith hα hα1 hδnn hδS hM₀nn hH₀nn hQnn hQP hPnn
      rw [hC₀def]
      exact le_trans hL harith
    calc ‖fderiv ℝ (Work.LWP.biotSavart (fun a => ω a t)) x
            - fderiv ℝ (Work.LWP.biotSavart (fun a => ω a t')) x‖
        = ‖(4 * Real.pi)⁻¹ • bsDerivCLM g ρ x‖ := by
          rw [← hfd_eq, hfd_g.fderiv]
      _ = (4 * Real.pi)⁻¹ * ‖bsDerivCLM g ρ x‖ := by
          rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      _ ≤ (4 * Real.pi)⁻¹ * (C₀ * δ ^ (α : ℝ)) :=
          mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = ((4 * Real.pi)⁻¹ * C₀) * |t - t'| ^ (α : ℝ) := by
          rw [hδdef]; ring

end Work.CoreResiduals.BiotSavart
