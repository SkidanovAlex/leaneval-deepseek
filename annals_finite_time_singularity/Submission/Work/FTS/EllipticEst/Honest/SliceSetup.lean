/-
Work module: the honest `θ`-slice tools of
`Work.FTS.EllipticEst.Honest.step3PsiBar`.

The `step3PsiBar` estimate bounds the `σ`-weighted `L²`-norm of `sin θ · ∂_θ(Ψ/cos θ)` by
those of `Ψ` and `∂_θθΨ` (`σ θ = sin(2θ)^{-η}`, `η = 99/100`).  On a single `z`-slice the
paper's `I₄` computation (Elgindi, Annals **194** (2021), Step 2 of `prop:H2`, tex 890--905)
reduces it to an integration by parts in `θ` against the weight
`ρ θ = sin θ · cos θ · σ θ = (1/2) sin(2θ)^{1-η}` (whose derivative is
`ρ' θ = (1 - η) cos 2θ · σ θ`, `Work.FTS.EllipticEst.TanTheta.wrhoD`).

This module collects the tools shared by the proof and by the auxiliary lemmas proved in
sibling files:

* `integral_Ioo_eq_sub_of_tendsto`, `integral_Ioo_mul_deriv_eq_neg_half`: the fundamental
  theorem of calculus and the integration by parts against `ρ` on the *open* interval
  `(0, π/2)`, with one-sided boundary limits (this is the honest replacement of the
  `C²`-on-a-neighbourhood hypotheses of the paper's strong class);
* `exists_tendsto_nhdsLT_of_integrableOn_deriv`: a differentiable function with integrable
  derivative has a finite limit at the *right* endpoint (the companion, at `π/2`, of
  `Work.FTS.EllipticEst.exists_tendsto_nhdsGT_zero_of_integrableOn_deriv`);
* `not_integrableOn_div_of_ge_const`: the elementary consequence of the divergence of
  `∫ dt/t` at `0` that turns an integrability statement into a `liminf` statement.

Nothing here contains a `sorry`.
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.AngSecond.Defs
import Submission.Work.FTS.EllipticEst.AngSecond.I4_aux_defs
import Submission.Work.FTS.EllipticEst.AngSecond.slice_ftc_zero
import Submission.Work.FTS.EllipticEst.TanTheta.Defs
import Submission.Work.FTS.EllipticEst.TanTheta.wrho_deriv
import Submission.Work.FTS.EllipticEst.exists_tendsto_nhdsGT_zero_of_integrableOn_deriv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-! ## The fundamental theorem of calculus and integration by parts on `(a,b)` -/

/-- **FTC-2 on an open interval.**  If `G` is differentiable on `(a,b)` with derivative `G'`,
`G'` is integrable there, and `G` has limits `m` at `a⁺` and `l` at `b⁻`, then
`∫_a^b G' = l - m`. -/
theorem integral_Ioo_eq_sub_of_tendsto {a b m l : ℝ} (hab : a < b) {G G' : ℝ → ℝ}
    (hderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt G (G' x) x)
    (hint : IntegrableOn G' (Set.Ioo a b))
    (hbot : Tendsto G (𝓝[>] a) (𝓝 m)) (htop : Tendsto G (𝓝[<] b) (𝓝 l)) :
    ∫ x in Set.Ioo a b, G' x = l - m := by
  have hle : a ≤ b := le_of_lt hab
  have hI : IntervalIntegrable G' volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hle).mpr hint
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hab hderiv hI hbot htop
  rw [intervalIntegral.integral_of_le hle, MeasureTheory.integral_Ioc_eq_integral_Ioo] at h
  exact h

/-- **Integration by parts against a weight vanishing at both endpoints.**  If
`(ρ f²) → 0` at `a⁺` and at `b⁻`, then `∫ ρ f f' = -(1/2) ∫ ρ' f²` on `(a,b)`. -/
theorem integral_Ioo_mul_deriv_eq_neg_half {a b : ℝ} (hab : a < b) {ρ ρ' f f' : ℝ → ℝ}
    (hρ : ∀ x ∈ Set.Ioo a b, HasDerivAt ρ (ρ' x) x)
    (hf : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x)
    (hint1 : IntegrableOn (fun x => ρ' x * f x ^ 2) (Set.Ioo a b))
    (hint2 : IntegrableOn (fun x => ρ x * f x * f' x) (Set.Ioo a b))
    (hbot : Tendsto (fun x => ρ x * f x ^ 2) (𝓝[>] a) (𝓝 0))
    (htop : Tendsto (fun x => ρ x * f x ^ 2) (𝓝[<] b) (𝓝 0)) :
    ∫ x in Set.Ioo a b, ρ x * f x * f' x = -(1 / 2) * ∫ x in Set.Ioo a b, ρ' x * f x ^ 2 := by
  have hderivG : ∀ x ∈ Set.Ioo a b,
      HasDerivAt (fun y => (1 / 2) * (ρ y * f y ^ 2))
        (ρ x * f x * f' x + (1 / 2) * (ρ' x * f x ^ 2)) x := by
    intro x hx
    have h := ((hρ x hx).mul ((hf x hx).pow 2)).const_mul (1 / 2)
    have h2 : (2 : ℕ) - 1 = 1 := rfl
    rw [h2, pow_one] at h
    convert h using 1
    simp only [Pi.pow_apply]
    ring
  have hInt : IntegrableOn
      (fun x => ρ x * f x * f' x + (1 / 2) * (ρ' x * f x ^ 2)) (Set.Ioo a b) :=
    hint2.add (hint1.const_mul (1 / 2))
  have hlim1 : Tendsto (fun y => (1 / 2) * (ρ y * f y ^ 2)) (𝓝[>] a) (𝓝 0) := by
    simpa using hbot.const_mul (1 / 2 : ℝ)
  have hlim2 : Tendsto (fun y => (1 / 2) * (ρ y * f y ^ 2)) (𝓝[<] b) (𝓝 0) := by
    simpa using htop.const_mul (1 / 2 : ℝ)
  have hFTC := integral_Ioo_eq_sub_of_tendsto hab hderivG hInt hlim1 hlim2
  simp only [sub_zero] at hFTC
  have hsplit : ∫ x in Set.Ioo a b, (ρ x * f x * f' x + (1 / 2) * (ρ' x * f x ^ 2))
      = (∫ x in Set.Ioo a b, ρ x * f x * f' x)
        + (1 / 2) * ∫ x in Set.Ioo a b, ρ' x * f x ^ 2 := by
    rw [integral_add hint2 (hint1.const_mul (1 / 2)), integral_const_mul]
  rw [hsplit] at hFTC
  linarith [hFTC]

/-! ## A limit at the right endpoint, from the integrability of the derivative -/

/-- **A differentiable function with integrable derivative has a limit at the right endpoint.**

If `f` is differentiable on the open interval `(a,b)` with derivative `f'`, and `f'` is
integrable on `(a,b)`, then `f` has a finite limit as `x → b⁻`.  (Companion, at the right
endpoint, of `Work.FTS.EllipticEst.exists_tendsto_nhdsGT_zero_of_integrableOn_deriv`.) -/
theorem exists_tendsto_nhdsLT_of_integrableOn_deriv {f f' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x)
    (hint : IntegrableOn f' (Set.Ioo a b)) :
    ∃ L : ℝ, Tendsto f (𝓝[<] b) (𝓝 L) := by
  set c : ℝ := (a + b) / 2 with hcdef
  have hac : a < c := by rw [hcdef]; linarith
  have hcb : c < b := by rw [hcdef]; linarith
  have hIoo_cb : IntegrableOn f' (Set.Ioo c b) :=
    hint.mono_set fun x hx => ⟨lt_trans hac hx.1, hx.2⟩
  have hIcc : IntegrableOn f' (Set.Icc c b) :=
    hIoo_cb.congr_set_ae (MeasureTheory.Ioo_ae_eq_Icc (a := c) (b := b)).symm
  have hcont : ContinuousOn (fun x => ∫ t in c..x, f' t) (Set.Icc c b) := by
    have h := intervalIntegral.continuousOn_primitive_interval (a := c) (b := b) (by
      rw [Set.uIcc_of_le hcb.le]; exact hIcc)
    rwa [Set.uIcc_of_le hcb.le] at h
  refine ⟨f c + ∫ t in c..b, f' t, ?_⟩
  have hcontAt : ContinuousWithinAt (fun x => ∫ t in c..x, f' t) (Set.Icc c b) b :=
    hcont.continuousWithinAt (Set.right_mem_Icc.mpr hcb.le)
  have hlimprim : Tendsto (fun x => ∫ t in c..x, f' t) (𝓝[<] b) (𝓝 (∫ t in c..b, f' t)) := by
    have hle : 𝓝[<] b ≤ 𝓝[Set.Icc c b] b := by
      rw [← nhdsWithin_Ioo_eq_nhdsLT hcb]
      exact nhdsWithin_mono b (fun x hx => ⟨hx.1.le, hx.2.le⟩)
    exact hcontAt.mono_left hle
  have hlim : Tendsto (fun x => f c + ∫ t in c..x, f' t) (𝓝[<] b) (𝓝 (f c + ∫ t in c..b, f' t)) :=
    hlimprim.const_add (f c)
  refine hlim.congr' ?_
  have hmem : Set.Ioo c b ∈ 𝓝[<] b := by
    rw [← nhdsWithin_Ioo_eq_nhdsLT hcb]
    exact self_mem_nhdsWithin
  filter_upwards [hmem] with x hx
  have hFTC : ∫ t in c..x, f' t = f x - f c :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun y hy => hderiv y (by
        have hy' : y ∈ Set.Icc c x := by rwa [Set.uIcc_of_le hx.1.le] at hy
        exact ⟨lt_of_lt_of_le hac hy'.1, lt_of_le_of_lt hy'.2 hx.2⟩))
      ((show IntegrableOn f' (Set.uIcc c x) volume from by
          rw [Set.uIcc_of_le hx.1.le]
          exact hIcc.mono_set (Set.Icc_subset_Icc le_rfl hx.2.le)).intervalIntegrable)
  linarith [hFTC]

/-! ## A `liminf` consequence of the divergence of `∫ dt/t` at `0` -/

/-- **If `F ≥ c > 0` on `(0,δ)` then `F t / t` is not integrable there** (because `∫_0^δ dt/t`
diverges).  Contrapositively: an integrable `F t / t` must have arbitrarily small values of
`F` arbitrarily close to `0`. -/
theorem not_integrableOn_div_of_ge_const {F : ℝ → ℝ} {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    (hF : ∀ t ∈ Set.Ioo (0 : ℝ) δ, c ≤ F t) :
    ¬ IntegrableOn (fun t => F t / t) (Set.Ioo (0 : ℝ) δ) := by
  intro hint
  have hmeas : AEStronglyMeasurable (fun t : ℝ => c / t)
      ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) δ)) :=
    (measurable_const.div measurable_id).aestronglyMeasurable
  have hdom : IntegrableOn (fun t : ℝ => c / t) (Set.Ioo (0 : ℝ) δ) := by
    refine hint.mono' hmeas ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
    have ht0 : 0 < t := ht.1
    have h1 : c ≤ F t := hF t ht
    rw [Real.norm_of_nonneg (div_nonneg hc.le ht0.le)]
    exact div_le_div_of_nonneg_right h1 ht0.le
  have hpow : IntegrableOn (fun t : ℝ => t ^ (-1 : ℝ)) (Set.Ioo (0 : ℝ) δ) := by
    have h := hdom.const_mul (c⁻¹)
    have h1 : (fun t : ℝ => c⁻¹ * (c / t))
        =ᵐ[volume.restrict (Set.Ioo (0 : ℝ) δ)] (fun t : ℝ => t ^ (-1 : ℝ)) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
      have ht0 : 0 < t := ht.1
      simp only [div_eq_mul_inv, Real.rpow_neg_one]
      field_simp
    exact h.congr h1
  rw [intervalIntegral.integrableOn_Ioo_rpow_iff hδ] at hpow
  norm_num at hpow

end Work.FTS.EllipticEst.Honest
