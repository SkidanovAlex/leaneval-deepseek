import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Tactic.Have
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.FTS.StrongEps.EpsE4Thr.Repair.aestronglyMeasurable_Jker_mul_epsRHSP

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr

open MeasureTheory Set Filter
open scoped Topology

set_option autoImplicit false

/-!
# `Jeps_family_deriv` — differentiation of the mollifier along a differentiable family

`Jeps ρ ε f z θ = ∫ p, Jker ρ ε p · f (z e^{-p₁}) (arctan (tan θ e^{-p₂}))` is an integral over
`p ∈ ℝ²`, so the derivative in the family parameter `s` of `s ↦ Jeps ρ ε (W s) z θ` is obtained
from the parametric differentiation lemma
`MeasureTheory.hasDerivAt_integral_of_dominated_loc_of_deriv_le`.

The four hypotheses it consumes:

* the pointwise differentiability of the slices (`hW`, on the open interval `(0,T)`);
* integrability of the integrand at the base time (`hint`, at `τ ∈ (0,T)`);
* a uniform bound on `Wdot` at the shifted points (`hbd`) — this dominates the derivative
  integrand by `C · ‖Jker ρ ε p‖`, which is integrable because `Jker ρ ε` is;
* a.e. strong measurability of the *derivative* integrand.  This last one is **not** free: `Wdot τ`
  is an arbitrary function (only bounded through `hbd`), and `Jker ρ ε` carries the measurability of
  `ρ` only through its support/continuity, so we recover measurability of
  `Jker ρ ε p · Wdot τ (zShift z p₁) (thShift θ p₂)` as the a.e. limit of the difference quotients
  `(Jker ρ ε p · W (τ + hₙ) (…) − Jker ρ ε p · W τ (…)) / hₙ`, each of which is a.e. strongly
  measurable by `hint` (the lemma `aestronglyMeasurable_Jker_mul_Wdot` below).

This is the exact repair of the false sibling `hasDerivWithinAt_Jeps_slice` (see
`NOTES_hasDerivWithinAt_Jeps_slice_FALSE.md`): the missing integrability hypothesis is present here
under the name `hint`.
-/

/-- **The measurability half of the parametric differentiation.**  If every slice integrand
`p ↦ Jker ρ ε p · W s (zShift z p₁) (thShift θ p₂)` is integrable for `s ∈ [0,T]`, then the
derivative integrand `p ↦ Jker ρ ε p · Wdot τ (zShift z p₁) (thShift θ p₂)` is a.e. strongly
measurable at every interior time `τ ∈ (0,T)` — no measurability of the family `Wdot` is assumed,
only its appearance as the derivative of `s ↦ W s` along the sequence `τ + (T-τ)/2/(n+1) ↓ τ`. -/
theorem aestronglyMeasurable_Jker_mul_Wdot {ρ : ℝ × ℝ → ℝ} {T ε : ℝ}
    {W Wdot : ℝ → Work.FTS.Galerkin.Fn} {z θ τ : ℝ}
    (hW : ∀ s ∈ Set.Ioo 0 T, ∀ y φ : ℝ, 0 < y → φ ∈ Set.Ioo 0 (Real.pi / 2) →
      HasDerivAt (fun x => W x y φ) (Wdot s y φ) s)
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (hτ : τ ∈ Set.Ioo 0 T)
    (hint : ∀ s ∈ Set.Icc 0 T, Integrable (fun p : ℝ × ℝ => Jker ρ ε p *
      W s (zShift z p.1) (thShift θ p.2)) volume) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => Jker ρ ε p *
      Wdot τ (zShift z p.1) (thShift θ p.2)) volume := by
  have hτ0 : 0 < τ := hτ.1
  have hτT : τ < T := hτ.2
  have hTτ : 0 < T - τ := by linarith
  -- the sequence of times approaching `τ` from the interior
  set sq : ℕ → ℝ := fun n => τ + ((T - τ) / 2) / ((n : ℝ) + 1) with hsq
  have hspos : ∀ n : ℕ, 0 < sq n - τ := by
    intro n
    have hpos : 0 < ((T - τ) / 2) / ((n : ℝ) + 1) := by positivity
    simp only [hsq]
    linarith
  have hsmem : ∀ n : ℕ, sq n ∈ Set.Icc 0 T := by
    intro n
    have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hle : ((T - τ) / 2) / ((n : ℝ) + 1) ≤ (T - τ) / 2 := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < (n : ℝ) + 1)]
      nlinarith [hTτ, hn1]
    have h1 : 0 ≤ sq n := by have := hspos n; linarith
    have h2 : sq n ≤ T := by simp only [hsq]; linarith
    exact ⟨h1, h2⟩
  have hstend : Tendsto sq atTop (𝓝 τ) := by
    have hc : Tendsto (fun n : ℕ => ((T - τ) / 2) / ((n : ℝ))) atTop (𝓝 (0 : ℝ)) :=
      tendsto_const_div_atTop_nhds_zero_nat ((T - τ) / 2)
    have hcomp : Tendsto (fun n : ℕ => ((T - τ) / 2) / (((n + 1 : ℕ) : ℝ))) atTop (𝓝 (0 : ℝ)) :=
      hc.comp (tendsto_add_atTop_nat 1)
    have hcomp' : Tendsto (fun n : ℕ => ((T - τ) / 2) / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
      Tendsto.congr' (Eventually.of_forall fun n => by push_cast; ring) hcomp
    have := hcomp'.const_add τ
    simpa only [hsq, add_zero] using this
  have hseq : Tendsto sq atTop (𝓝[≠] τ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within sq hstend ?_
    refine Eventually.of_forall fun n => ?_
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact sub_ne_zero.mp (hspos n).ne'
  -- the slopes of the slices converge to `Wdot τ` at the shifted points
  have hlim : ∀ p : ℝ × ℝ, Tendsto (fun n : ℕ =>
      (W (sq n) (zShift z p.1) (thShift θ p.2) - W τ (zShift z p.1) (thShift θ p.2))
        / (sq n - τ)) atTop
      (𝓝 (Wdot τ (zShift z p.1) (thShift θ p.2))) := by
    intro p
    have hd := (hW τ hτ (zShift z p.1) (thShift θ p.2)
      (zShift_pos hz) (thShift_mem hθ)).tendsto_slope
    have hcomp := hd.comp hseq
    refine Tendsto.congr' (Eventually.of_forall fun n => ?_) hcomp
    rw [Function.comp_apply, slope_def_field]
  -- the difference quotients of the integrand
  set F : ℕ → ℝ × ℝ → ℝ := fun n p =>
      (sq n - τ)⁻¹ * (Jker ρ ε p * W (sq n) (zShift z p.1) (thShift θ p.2)
        - Jker ρ ε p * W τ (zShift z p.1) (thShift θ p.2)) with hF
  have hFasm : ∀ n : ℕ, AEStronglyMeasurable (F n) volume := by
    intro n
    have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => Jker ρ ε p *
        W (sq n) (zShift z p.1) (thShift θ p.2)) volume :=
      (hint (sq n) (hsmem n)).aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ => Jker ρ ε p *
        W τ (zShift z p.1) (thShift θ p.2)) volume :=
      (hint τ ⟨hτ.1.le, hτ.2.le⟩).aestronglyMeasurable
    have h3 : AEStronglyMeasurable (fun p : ℝ × ℝ =>
        Jker ρ ε p * W (sq n) (zShift z p.1) (thShift θ p.2)
          - Jker ρ ε p * W τ (zShift z p.1) (thShift θ p.2)) volume := h1.sub h2
    have h4 : AEStronglyMeasurable (fun p : ℝ × ℝ => (sq n - τ)⁻¹ *
        (Jker ρ ε p * W (sq n) (zShift z p.1) (thShift θ p.2)
          - Jker ρ ε p * W τ (zShift z p.1) (thShift θ p.2))) volume :=
      h3.const_mul _
    rw [hF]
    exact h4
  have hFlim : ∀ᵐ p ∂volume, Tendsto (fun n : ℕ => F n p) atTop
      (𝓝 (Jker ρ ε p * Wdot τ (zShift z p.1) (thShift θ p.2))) := by
    refine Eventually.of_forall fun p => ?_
    have hc : Tendsto (fun n : ℕ => Jker ρ ε p *
        ((W (sq n) (zShift z p.1) (thShift θ p.2)
          - W τ (zShift z p.1) (thShift θ p.2)) / (sq n - τ))) atTop
        (𝓝 (Jker ρ ε p * Wdot τ (zShift z p.1) (thShift θ p.2))) :=
      (hlim p).const_mul _
    refine Tendsto.congr' (Eventually.of_forall fun n => ?_) hc
    simp only [hF]
    ring
  exact aestronglyMeasurable_of_tendsto_ae atTop hFasm hFlim

theorem Jeps_family_deriv {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    {T ε : ℝ} {W Wdot : ℝ → Work.FTS.Galerkin.Fn} (hε : 0 < ε)
    (hW : ∀ s ∈ Set.Ioo 0 T, ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      HasDerivAt (fun x => W x z θ) (Wdot s z θ) s)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hint : ∀ s ∈ Set.Icc 0 T, MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      Work.FTS.StrongEps.Jker ρ ε p * W s (Work.FTS.StrongEps.zShift z p.1)
        (Work.FTS.StrongEps.thShift θ p.2)) MeasureTheory.volume)
    (hbd : ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ℝ × ℝ, ‖p‖ ≤ ε → ∀ s ∈ Set.Icc 0 T,
      |Wdot s (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)| ≤ C)
    {τ : ℝ} (hτ : τ ∈ Set.Ioo 0 T) :
    HasDerivWithinAt (fun s => Work.FTS.StrongEps.Jeps ρ ε (W s) z θ)
      (Work.FTS.StrongEps.Jeps ρ ε (Wdot τ) z θ) (Set.Icc 0 T) τ := by
  obtain ⟨C, hC0, hCbd⟩ := hbd
  have hτmem : τ ∈ Set.Icc (0 : ℝ) T := ⟨hτ.1.le, hτ.2.le⟩
  have hs : Set.Ioo (0 : ℝ) T ∈ 𝓝 τ := isOpen_Ioo.mem_nhds hτ
  -- the two hypotheses of the parametric lemma that only use `hint`
  have hF_meas : ∀ᶠ x in 𝓝 τ, AEStronglyMeasurable (fun p : ℝ × ℝ =>
      Jker ρ ε p * W x (zShift z p.1) (thShift θ p.2)) volume := by
    filter_upwards [hs] with x hx
    exact (hint x ⟨hx.1.le, hx.2.le⟩).aestronglyMeasurable
  have hF_int : Integrable (fun p : ℝ × ℝ =>
      Jker ρ ε p * W τ (zShift z p.1) (thShift θ p.2)) volume :=
    hint τ hτmem
  -- the a.e. strong measurability of the derivative integrand
  have hF'_meas : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      Jker ρ ε p * Wdot τ (zShift z p.1) (thShift θ p.2)) volume :=
    aestronglyMeasurable_Jker_mul_Wdot hW hz hθ hτ hint
  -- the domination, from `hbd`
  have h_bound : ∀ᵐ a ∂volume, ∀ x ∈ Set.Ioo (0 : ℝ) T,
      ‖Jker ρ ε a * Wdot x (zShift z a.1) (thShift θ a.2)‖
        ≤ (fun p : ℝ × ℝ => C * ‖Jker ρ ε p‖) a := by
    refine Eventually.of_forall fun a x hx => ?_
    by_cases ha : ‖a‖ ≤ ε
    · have hb : |Wdot x (zShift z a.1) (thShift θ a.2)| ≤ C :=
        hCbd a ha x ⟨hx.1.le, hx.2.le⟩
      have h1 : |Jker ρ ε a * Wdot x (zShift z a.1) (thShift θ a.2)| ≤ C * |Jker ρ ε a| := by
        rw [abs_mul]
        exact (mul_le_mul_of_nonneg_left hb (abs_nonneg _)).trans (le_of_eq (by ring))
      simpa only [Real.norm_eq_abs] using h1
    · have ha' : a ∉ Metric.closedBall (0 : ℝ × ℝ) ε := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using ha
      have hz0 : Jker ρ ε a = 0 := Jker_eq_zero_of_not_mem hρ hε ha'
      rw [hz0, zero_mul, norm_zero]
      exact mul_nonneg hC0 (norm_nonneg _)
  have hbound_int : Integrable (fun p : ℝ × ℝ => C * ‖Jker ρ ε p‖) volume :=
    (Jker_integrable hρ hε).norm.const_mul C
  -- the pointwise derivative of the slices
  have h_diff : ∀ᵐ a ∂volume, ∀ x ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt (fun x => Jker ρ ε a * W x (zShift z a.1) (thShift θ a.2))
        (Jker ρ ε a * Wdot x (zShift z a.1) (thShift θ a.2)) x := by
    refine Eventually.of_forall fun a x hx => ?_
    exact (hW x hx (zShift z a.1) (thShift θ a.2)
      (zShift_pos hz) (thShift_mem hθ)).const_mul (Jker ρ ε a)
  have hmain := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (𝕜 := ℝ)
      (F := fun x p => Jker ρ ε p * W x (zShift z p.1) (thShift θ p.2))
      (F' := fun x p => Jker ρ ε p * Wdot x (zShift z p.1) (thShift θ p.2))
      (bound := fun p : ℝ × ℝ => C * ‖Jker ρ ε p‖)
      (x₀ := τ) (s := Set.Ioo 0 T) hs
      hF_meas hF_int hF'_meas h_bound hbound_int h_diff).2
  rw [show (fun s : ℝ => Jeps ρ ε (W s) z θ)
        = fun s : ℝ => ∫ p : ℝ × ℝ, Jker ρ ε p * W s (zShift z p.1) (thShift θ p.2) from
        funext (fun s => Jeps_eq_integral ρ ε (W s) hz hθ),
      show Jeps ρ ε (Wdot τ) z θ
        = ∫ p : ℝ × ℝ, Jker ρ ε p * Wdot τ (zShift z p.1) (thShift θ p.2)
        from Jeps_eq_integral ρ ε (Wdot τ) hz hθ]
  exact hmain.hasDerivWithinAt

end Work.FTS.StrongEps.EpsE4Thr
