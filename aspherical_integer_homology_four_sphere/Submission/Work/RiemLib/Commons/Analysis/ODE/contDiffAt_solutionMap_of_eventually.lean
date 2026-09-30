import Mathlib
import Submission.Work.RiemLib.Commons.Analysis.ODE.contDiffAt_solutionMap

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped _root_.ContDiff
open Set Filter

/-!
# Smooth dependence of ODE solutions on a parameter (local version)

This file proves `Commons.Analysis.ODE.contDiffAt_solutionMap_of_eventually`: if `f : ℝ → E → E`
is smooth, `c : X → E` is a smooth family of initial conditions, and `u : X → ℝ → E` is a family of
curves which, for every parameter `x` in a neighbourhood of a base point `x₀`, is the unique solution
on `Set.Ioo a b` of `y' = f t y` with `y 0 = c x`, then `(x, t) ↦ u x t` is `C^∞` at `(x₀, t₀)` for
every `t₀ ∈ Set.Ioo a b`.

This generalises `Commons.Analysis.ODE.contDiffAt_solutionMap` (the case `X = E`, `c = id`, with
global hypotheses) in two independent directions: the family of initial conditions is an arbitrary
smooth map, and the hypotheses only have to hold *eventually* in the parameter.

## Proof

The proof follows the strategy of `Commons.Analysis.ODE.contDiffAt_solutionMap`, whose machinery
(`Feq`, `Phieq`, `IntCLM`, `Mlam`, `nem`, `comb`, `emb`, `isInvertible_one_sub`, ...) we import.
The implicit function theorem is applied to

`Feq lam (hfun lam f) ((c x₀, t₀), y) = 0`

in the Banach space `C(K, E)` (`K = [0,1]`) at the base point `((c x₀, t₀), η₀)`, where `η₀` comes
from the trajectory `σ ↦ u x₀ (t₀ * σ)`.  The partial derivative in the second variable is `1 - A`
with `‖A‖ ≤ |t₀| * C₀ / lam < 1`, hence invertible.  The implicit solution `ψ` gives curves
`σ ↦ Real.exp (lam * σ) • ψ y σ` solving the `t₀`-rescaled equation with initial value `y.1`;
`ODE_solution_unique_of_mem_Icc_right` (with the Lipschitz constant of the field along the segments
joining the two candidate trajectories, obtained from continuity on the compact square `K × K`)
identifies such a curve with the *given* solution `u x` when `y = (c x, t)`.  This only uses the
hypotheses at parameters `x` close to `x₀`, which is why the `∀ᶠ` versions suffice.

The final step pulls the resulting local smoothness in `(y, t)` back along the smooth map
`x ↦ (c x, t) : X × ℝ → E × ℝ`.
-/


namespace Commons.Analysis.ODE

noncomputable section

open scoped Topology ContDiff
open SmoothDep

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {f : ℝ → E → E} {a b : ℝ} {t₀ : ℝ} {v : ℝ → E}

omit [CompleteSpace E] in
/-- Rescaling a solution of `y' = f t y` by `t ↦ t₀ * t` gives a solution of the rescaled
equation `z' = t₀ • f (t₀ * t) z` (this is the `t₀`-parametrisation of the trajectory, used to
reduce the ODE on `Set.Ioo a b` to an equation on `K = [0,1]`). -/
lemma hasDerivAt_rescale {a b t₀ : ℝ} {f : ℝ → E → E} {v : ℝ → E}
    (hv : ∀ t ∈ Set.Ioo a b, HasDerivAt v (f t (v t)) t)
    {r : ℝ} (hr : t₀ * r ∈ Set.Ioo a b) :
    HasDerivAt (fun r : ℝ => v (t₀ * r)) (t₀ • f (t₀ * r) (v (t₀ * r))) r := by
  have h1 : HasDerivAt (fun r : ℝ => t₀ * r) t₀ r := hasDerivAt_const_mul t₀
  have h2 := ((hv (t₀ * r) hr).hasFDerivAt).comp_hasDerivAt r h1
  simpa only [Function.comp_def, ContinuousLinearMap.toSpanSingleton_apply] using h2

/-- The rescaled trajectory is continuous on `K = [0,1]`. -/
lemma continuous_rescale {a b t₀ : ℝ} {f : ℝ → E → E} {v : ℝ → E}
    (ha : a < 0) (hb : 0 < b) (ht₀ : t₀ ∈ Set.Ioo a b)
    (hv : ∀ t ∈ Set.Ioo a b, HasDerivAt v (f t (v t)) t) :
    Continuous fun σ : K => v (t₀ * (σ:ℝ)) := by
  rw [continuous_iff_continuousAt]
  intro σ
  exact ((hasDerivAt_rescale hv (t_mul_mem_Ioo ha hb ht₀ σ.2)).continuousAt).comp
    continuous_subtype_val.continuousAt

/-- Fundamental theorem of calculus for the rescaled trajectory: for `σ ∈ K`,
`∫_0^σ t₀ • f (t₀ r) (v (t₀ r)) dr = v (t₀ σ) - v 0`. -/
lemma integral_rescale {a b t₀ : ℝ} {f : ℝ → E → E} {v : ℝ → E}
    (ha : a < 0) (hb : 0 < b) (ht₀ : t₀ ∈ Set.Ioo a b)
    (hf : ContDiff ℝ ∞ (fun p : ℝ × E => f p.1 p.2))
    (hv : ∀ t ∈ Set.Ioo a b, HasDerivAt v (f t (v t)) t)
    {σ : ℝ} (hσ : σ ∈ K) :
    ∫ r in (0:ℝ)..σ, t₀ • f (t₀ * r) (v (t₀ * r)) = v (t₀ * σ) - v 0 := by
  have hle : (0:ℝ) ≤ σ := hσ.1
  have hderiv' : ∀ r ∈ Icc (0:ℝ) σ, HasDerivAt (fun r : ℝ => v (t₀ * r))
      (t₀ • f (t₀ * r) (v (t₀ * r))) r := fun r hr =>
    hasDerivAt_rescale hv (t_mul_mem_Ioo ha hb ht₀ ⟨hr.1, le_trans hr.2 hσ.2⟩)
  have hcont : ContinuousOn (fun r : ℝ => v (t₀ * r)) (Icc 0 σ) := HasDerivAt.continuousOn hderiv'
  have hint : IntervalIntegrable (fun r : ℝ => t₀ • f (t₀ * r) (v (t₀ * r)))
      MeasureTheory.volume 0 σ := by
    apply ContinuousOn.intervalIntegrable
    have h1 : ContinuousOn (fun r : ℝ => ((t₀ * r), v (t₀ * r))) (uIcc 0 σ) := by
      refine ContinuousOn.prodMk ?_ ?_
      · exact (continuous_const.mul continuous_id).continuousOn
      · exact hcont.mono (by rw [uIcc_of_le hle])
    exact (continuous_const.smul hf.continuous).comp_continuousOn h1
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle hcont
      (fun r hr => hderiv' r ⟨le_of_lt hr.1, le_of_lt hr.2⟩) hint
  rw [h, mul_zero]

/-- **Smooth dependence of ODE solutions on a parameter, local version.**

Let `f : ℝ → E → E` be smooth (as a function of `(t, y)`), let `a < 0 < b`, let `c : X → E` be a
smooth family of initial conditions and let `u : X → ℝ → E` be a family of curves which, *for every
parameter `x` near `x₀`*, is the unique solution on `Set.Ioo a b` of `y' = f t y` with
`y 0 = c x` (uniqueness being required only among solutions on `Set.Ioo a b`). Then
`(x, t) ↦ u x t` is `C^∞` at every point `(x₀, t₀)` with `t₀ ∈ Set.Ioo a b`.

This is the standard smooth dependence of solutions of an ODE on a parameter; because the solutions
exist on the *fixed* interval around `0` for all `x` near `x₀`, the classical proof applies the
implicit function principle in the Banach space of continuous functions on `Set.Ioo a b` to the
integral equation `y t = c x + int_0^t f (s, y s) ds`, and then bootstraps regularity.  The point
of the `∀ᶠ` in the hypotheses is that `u x` may be an arbitrary junk curve for `x` far from `x₀`. -/
theorem contDiffAt_solutionMap_of_eventually
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E → E} (hf : ContDiff ℝ ∞ (fun p : ℝ × E => f p.1 p.2))
    {a b : ℝ} (ha : a < 0) (hb : 0 < b)
    {c : X → E} (hc : ContDiff ℝ ∞ c) {x₀ : X} {u : X → ℝ → E}
    (h0 : ∀ᶠ x in nhds x₀, u x 0 = c x)
    (hsol : ∀ᶠ x in nhds x₀, ∀ t ∈ Set.Ioo a b, HasDerivAt (u x) (f t (u x t)) t)
    (huniq : ∀ᶠ x in nhds x₀, ∀ y : ℝ → E, (∀ t ∈ Set.Ioo a b, HasDerivAt y (f t (y t)) t) →
      y 0 = c x → ∀ t ∈ Set.Ioo a b, y t = u x t)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo a b) :
    ContDiffAt ℝ ∞ (fun p : X × ℝ => u p.1 p.2) (x₀, t₀) := by
  classical
  -- The three hypotheses hold on a common neighbourhood `S` of `x₀`.
  obtain ⟨S, hSmem, hS⟩ := Filter.eventually_iff_exists_mem.mp (h0.and (hsol.and huniq))
  have hx₀S : x₀ ∈ S := mem_of_mem_nhds hSmem
  have h0x₀ : u x₀ 0 = c x₀ := (hS x₀ hx₀S).1
  have hsolx₀ : ∀ t ∈ Set.Ioo a b, HasDerivAt (u x₀) (f t (u x₀ t)) t := (hS x₀ hx₀S).2.1
  have hf' : ContDiff ℝ ∞ (fun p : ℝ × E => f p.1 p.2) := hf
  set γ₀ : C(K,E) := ⟨fun σ => u x₀ (t₀ * (σ:ℝ)), continuous_rescale ha hb ht₀ hsolx₀⟩ with hγ₀def
  have hγ₀ : ∀ σ : K, γ₀ σ = u x₀ (t₀ * (σ:ℝ)) := fun σ => rfl
  have hDccont : Continuous fun σ : K => D2 (fun p : ℝ × E => f p.1 p.2) (t₀*(σ:ℝ), γ₀ σ) :=
    ((D2_contDiff (fun p : ℝ × E => f p.1 p.2) hf').continuous.comp
      (by fun_prop : Continuous fun σ : K => ((t₀*(σ:ℝ)), γ₀ σ)))
  set Dc : C(K, E →L[ℝ] E) := ⟨fun σ => D2 (fun p : ℝ × E => f p.1 p.2) (t₀*(σ:ℝ), γ₀ σ), hDccont⟩
    with hDcdef
  set C₀ : ℝ := ‖Dc‖ with hC₀def
  have hDcbound : ∀ σ : K, ‖D2 (fun p : ℝ × E => f p.1 p.2) (t₀*(σ:ℝ), γ₀ σ)‖ ≤ C₀ :=
    fun σ => ContinuousMap.norm_coe_le_norm Dc σ
  have hC₀nn : 0 ≤ C₀ := hC₀def.symm ▸ norm_nonneg Dc
  set lam : ℝ := 1 + |t₀| * C₀ with hlamdef
  have hlam_pos : 0 < lam := by rw [hlamdef]; positivity
  have hlam_ne : lam ≠ 0 := ne_of_gt hlam_pos
  have hlam_gt : |t₀| * C₀ < lam := by rw [hlamdef]; linarith
  have hh : ContDiff ℝ ∞ (hfun lam f) := hfun_contDiff lam hf
  set η₀ : C(K,E) := Mlam lam γ₀ with hη₀def
  set u0 : E × ℝ := (c x₀, t₀) with hu0def
  set p₀ : (E × ℝ) × C(K,E) := (u0, η₀) with hp₀def
  have hbase : Feq lam (hfun lam f) hh p₀ = 0 := by
    ext σ
    have h1 : (Feq lam (hfun lam f) hh p₀) σ
        = η₀ σ - Real.exp (-(lam * (σ:ℝ))) • c x₀
          - Real.exp (-(lam * (σ:ℝ))) • ∫ r in (0:ℝ)..(σ:ℝ),
              (nem (E := ℝ×E) E (hfun lam f) hh (comb lam (t₀, η₀))) (clampK r) := by
      simp only [Feq, Phieq, ContinuousMap.sub_apply, Mlam_apply, constCLM_apply,
        IntCLM_apply, hp₀def, hu0def]
    rw [h1]
    have hcongr : ∫ r in (0:ℝ)..(σ:ℝ),
          (nem (E := ℝ×E) E (hfun lam f) hh (comb lam (t₀, η₀))) (clampK r)
        = ∫ r in (0:ℝ)..(σ:ℝ), t₀ • f (t₀ * r) (u x₀ (t₀ * r)) := by
      apply intervalIntegral.integral_congr
      intro r hr
      rw [uIcc_of_le σ.2.1] at hr
      have hrK : r ∈ K := ⟨hr.1, le_trans hr.2 σ.2.2⟩
      show (nem (E := ℝ×E) E (hfun lam f) hh (comb lam (t₀, η₀))) (clampK r)
        = t₀ • f (t₀ * r) (u x₀ (t₀ * r))
      rw [nem_apply, comb_apply, clampK_of_mem hrK]
      simp only [hfun, Subtype.coe_mk]
      congr 1
      rw [hη₀def, Mlam_apply]
      simp only [Subtype.coe_mk]
      rw [smul_smul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_smul]
      exact congrArg (fun z => f (t₀ * r) z) (hγ₀ ⟨r, hrK⟩)
    rw [hcongr, integral_rescale ha hb ht₀ hf' hsolx₀ σ.2, ← h0x₀]
    rw [hη₀def, Mlam_apply, hγ₀ σ]
    simp only [ContinuousMap.zero_apply]
    rw [smul_sub]
    abel

  set Xc : C(K, (ℝ × E) →L[ℝ] E) := nem (E := ℝ × E) ((ℝ × E) →L[ℝ] E) (D2 (hfun lam f))
    (D2_contDiff (hfun lam f) hh) (comb lam (t₀, η₀)) with hXcdef
  set A : C(K,E) →L[ℝ] C(K,E) :=
    (Mlam lam).comp (IntCLM.comp ((mulClm (E := ℝ × E) (G := E) Xc).comp (emb lam))) with hAdef
  have hA_has : HasFDerivAt (fun η : C(K,E) => Phieq lam (hfun lam f) hh (u0, η)) A η₀ := by
    have hinr : HasFDerivAt (fun η : C(K,E) => (t₀, η)) (ContinuousLinearMap.inr ℝ ℝ C(K,E)) η₀ :=
      (hasFDerivAt_const (𝕜 := ℝ) (x := η₀) (c := t₀)).prodMk (hasFDerivAt_id η₀)
    have hcomb : HasFDerivAt (fun η : C(K,E) => comb lam (t₀, η)) (emb lam) η₀ := by
      have hh1 := (comb (E := E) lam).hasFDerivAt.comp η₀ hinr
      simpa only [emb, Function.comp_def] using hh1
    have hnem : HasFDerivAt (fun ζ : C(K, ℝ×E) => nem (E := ℝ×E) E (hfun lam f) hh ζ)
        (mulClm (E := ℝ × E) (G := E) Xc) (comb lam (t₀, η₀)) :=
      nem_hasFDerivAt (E := ℝ×E) (G := E) (hfun lam f) hh (comb lam (t₀, η₀))
    have h4 := hnem.comp η₀ hcomb
    have h5 := IntCLM.hasFDerivAt.comp η₀ h4
    have h6 := (Mlam lam).hasFDerivAt.comp η₀ h5
    simpa only [A, Phieq, Function.comp_def, hu0def, hAdef, hXcdef] using h6
  have hA_pt : ∀ δ : C(K,E), ‖A δ‖ ≤ (|t₀| * C₀ / lam) * ‖δ‖ := by
    intro δ
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro σ
    have hAap : (A δ) σ = Real.exp (-(lam * (σ:ℝ))) • ∫ r in (0:ℝ)..(σ:ℝ),
        Xc (clampK r) ((emb lam δ) (clampK r)) := by
      simp only [A, hAdef, ContinuousLinearMap.comp_apply, Mlam_apply, IntCLM_apply,
        mulClm_apply, mulLin_apply]
    rw [hAap, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hint : IntervalIntegrable (fun r : ℝ => |t₀| * C₀ * Real.exp (lam * r) * ‖δ‖)
        MeasureTheory.volume 0 (σ:ℝ) := by
      apply Continuous.intervalIntegrable
      fun_prop
    have hle : ‖∫ r in (0:ℝ)..(σ:ℝ), Xc (clampK r) ((emb lam δ) (clampK r))‖
        ≤ ∫ r in (0:ℝ)..(σ:ℝ), |t₀| * C₀ * Real.exp (lam * r) * ‖δ‖ := by
      apply intervalIntegral.norm_integral_le_of_norm_le σ.2.1
      · filter_upwards with r hr
        have hrK : r ∈ K := ⟨le_of_lt hr.1, le_trans hr.2 σ.2.2⟩
        have hXc : Xc (clampK r) = D2 (hfun lam f) (clampK r, (t₀, η₀ (clampK r))) := by
          simp only [Xc, hXcdef, nem_apply, comb_apply]
        rw [hXc, emb_apply, clampK_of_mem hrK]
        simp only [Subtype.coe_mk]
        rw [D2_hfun hf lam t₀ r (η₀ ⟨r, hrK⟩) (δ ⟨r, hrK⟩)]
        have hη : Real.exp (lam * r) • η₀ ⟨r, hrK⟩ = u x₀ (t₀ * r) := by
          rw [hη₀def, Mlam_apply]
          simp only [Subtype.coe_mk]
          rw [smul_smul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_smul]
          exact hγ₀ ⟨r, hrK⟩
        rw [hη]
        rw [norm_smul, Real.norm_eq_abs, ContinuousLinearMap.map_smul, norm_smul,
          Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        have h1 : ‖D2 (fun p : ℝ × E => f p.1 p.2) (t₀ * r, u x₀ (t₀ * r))‖ ≤ C₀ := by
          have hh1 := hDcbound ⟨r, hrK⟩
          rwa [hγ₀ ⟨r, hrK⟩] at hh1
        have h2 : ‖δ ⟨r, hrK⟩‖ ≤ ‖δ‖ := ContinuousMap.norm_coe_le_norm δ ⟨r, hrK⟩
        have h1' : ‖(D2 (fun p : ℝ × E => f p.1 p.2) (t₀ * r, u x₀ (t₀ * r))) (δ ⟨r, hrK⟩)‖
            ≤ C₀ * ‖δ‖ := by
          calc ‖(D2 (fun p : ℝ × E => f p.1 p.2) (t₀ * r, u x₀ (t₀ * r))) (δ ⟨r, hrK⟩)‖
              ≤ ‖D2 (fun p : ℝ × E => f p.1 p.2) (t₀ * r, u x₀ (t₀ * r))‖ * ‖δ ⟨r, hrK⟩‖ :=
                (D2 (fun p : ℝ × E => f p.1 p.2) (t₀ * r, u x₀ (t₀ * r))).le_opNorm _
            _ ≤ C₀ * ‖δ‖ := mul_le_mul h1 h2 (norm_nonneg _) hC₀nn
        have h3 : 0 ≤ Real.exp (lam * r) := le_of_lt (Real.exp_pos _)
        have h5 : 0 ≤ |t₀| := abs_nonneg t₀
        calc |t₀| * (Real.exp (lam * r) * ‖(D2 (fun p : ℝ × E => f p.1 p.2) (t₀ * r,
                u x₀ (t₀ * r))) (δ ⟨r, hrK⟩)‖)
            ≤ |t₀| * (Real.exp (lam * r) * (C₀ * ‖δ‖)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1' h3) h5
          _ = |t₀| * C₀ * Real.exp (lam * r) * ‖δ‖ := by ring
      · exact hint
    have hInt : ∫ r in (0:ℝ)..(σ:ℝ), |t₀| * C₀ * Real.exp (lam * r) * ‖δ‖
        = |t₀| * C₀ * (Real.exp (lam * (σ:ℝ)) - 1) / lam * ‖δ‖ := by
      rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul,
        integral_exp_mul lam hlam_ne 0 (σ:ℝ)]
      rw [mul_zero, Real.exp_zero]
      ring
    have hexp : Real.exp (-(lam * (σ:ℝ))) * (|t₀| * C₀ * (Real.exp (lam * (σ:ℝ)) - 1) / lam * ‖δ‖)
        = |t₀| * C₀ * (1 - Real.exp (-(lam * (σ:ℝ)))) / lam * ‖δ‖ := by
      have hh1 : Real.exp (-(lam * (σ:ℝ))) * Real.exp (lam * (σ:ℝ)) = 1 := by
        rw [← Real.exp_add]
        have hh2 : -(lam * (σ:ℝ)) + lam * (σ:ℝ) = 0 := by ring
        rw [hh2, Real.exp_zero]
      calc Real.exp (-(lam * (σ:ℝ))) * (|t₀| * C₀ * (Real.exp (lam * (σ:ℝ)) - 1) / lam * ‖δ‖)
          = (Real.exp (-(lam * (σ:ℝ))) * (Real.exp (lam * (σ:ℝ)) - 1)) * (|t₀| * C₀ / lam * ‖δ‖) := by
            ring
        _ = (1 - Real.exp (-(lam * (σ:ℝ)))) * (|t₀| * C₀ / lam * ‖δ‖) := by
            rw [mul_sub, hh1, mul_one]
        _ = |t₀| * C₀ * (1 - Real.exp (-(lam * (σ:ℝ)))) / lam * ‖δ‖ := by ring
    have h10 : |t₀| * C₀ * (1 - Real.exp (-(lam * (σ:ℝ)))) / lam * ‖δ‖
        ≤ |t₀| * C₀ / lam * ‖δ‖ := by
      have h12 : (1 - Real.exp (-(lam * (σ:ℝ)))) ≤ 1 := by
        have := Real.exp_pos (-(lam * (σ:ℝ))); linarith
      have h13 : 0 ≤ |t₀| * C₀ := mul_nonneg (abs_nonneg t₀) hC₀nn
      have h14 : 0 ≤ ‖δ‖ := norm_nonneg _
      have hh1 : |t₀| * C₀ * (1 - Real.exp (-(lam * (σ:ℝ)))) / lam ≤ |t₀| * C₀ / lam := by
        apply div_le_div_of_nonneg_right _ (le_of_lt hlam_pos)
        exact mul_le_of_le_one_right (mul_nonneg (abs_nonneg t₀) hC₀nn) h12
      exact mul_le_mul_of_nonneg_right hh1 h14
    calc Real.exp (-(lam * (σ:ℝ))) * ‖∫ r in (0:ℝ)..(σ:ℝ), Xc (clampK r) ((emb lam δ) (clampK r))‖
        ≤ Real.exp (-(lam * (σ:ℝ))) * ∫ r in (0:ℝ)..(σ:ℝ), |t₀| * C₀ * Real.exp (lam * r) * ‖δ‖ :=
          mul_le_mul_of_nonneg_left hle (le_of_lt (Real.exp_pos _))
      _ = Real.exp (-(lam * (σ:ℝ))) * (|t₀| * C₀ * (Real.exp (lam * (σ:ℝ)) - 1) / lam * ‖δ‖) := by
          rw [hInt]
      _ = |t₀| * C₀ * (1 - Real.exp (-(lam * (σ:ℝ)))) / lam * ‖δ‖ := hexp
      _ ≤ |t₀| * C₀ / lam * ‖δ‖ := h10
  have hA_bound : ‖A‖ ≤ |t₀| * C₀ / lam :=
    ContinuousLinearMap.opNorm_le_bound A (by positivity) hA_pt
  have hA_lt : ‖A‖ < 1 := by
    have h1 : |t₀| * C₀ / lam < 1 := by
      rw [div_lt_one hlam_pos]; exact hlam_gt
    linarith
  have hsub : HasFDerivAt (fun η : C(K,E) => Feq lam (hfun lam f) hh (u0, η)) (1 - A) η₀ := by
    have h1 : HasFDerivAt (fun η : C(K,E) => η) (1 : C(K,E) →L[ℝ] C(K,E)) η₀ :=
      hasFDerivAt_id (𝕜 := ℝ) (x := η₀)
    have h2 : HasFDerivAt (fun _ : C(K,E) => Mlam lam (constCLM (c x₀))) 0 η₀ :=
      hasFDerivAt_const (𝕜 := ℝ) (c := Mlam lam (constCLM (c x₀))) (x := η₀)
    have h3 := (h1.sub h2).sub hA_has
    have heq : (fun η : C(K,E) => Feq lam (hfun lam f) hh (u0, η))
        = ((fun η : C(K,E) => η) - (fun _ : C(K,E) => Mlam lam (constCLM (c x₀)))
           - (fun η : C(K,E) => Phieq lam (hfun lam f) hh (u0, η))) := by
      funext η
      simp only [Feq, Phieq, hu0def, Pi.sub_apply]
    rw [heq]
    simpa only [sub_zero] using h3
  have hFeq_at : HasFDerivAt (Feq lam (hfun lam f) hh)
      (fderiv ℝ (Feq lam (hfun lam f) hh) p₀) p₀ :=
    ((Feq_contDiff lam (hfun lam f) hh).differentiable (by simp)).differentiableAt.hasFDerivAt
  have hinr2 : HasFDerivAt (fun η : C(K,E) => (u0, η))
      (ContinuousLinearMap.inr ℝ (E × ℝ) C(K,E)) η₀ :=
    (hasFDerivAt_const (𝕜 := ℝ) (x := η₀) (c := u0)).prodMk (hasFDerivAt_id (𝕜 := ℝ) (x := η₀))
  have hcomp := hFeq_at.comp η₀ hinr2
  have hEq : ((fderiv ℝ (Feq lam (hfun lam f) hh) p₀) ∘L
      ContinuousLinearMap.inr ℝ (E × ℝ) C(K,E)) = 1 - A := by
    rw [← hcomp.fderiv]
    exact hsub.fderiv
  have hif : ((fderiv ℝ (Feq lam (hfun lam f) hh) p₀) ∘L
      ContinuousLinearMap.inr ℝ (E × ℝ) C(K,E)).IsInvertible := by
    rw [hEq]
    exact isInvertible_one_sub A hA_lt
  have hFeq_cd : ContDiffAt ℝ ∞ (Feq lam (hfun lam f) hh) p₀ :=
    (Feq_contDiff lam (hfun lam f) hh).contDiffAt
  let ψ : E × ℝ → C(K,E) := hFeq_cd.implicitFunction (by simp) hif
  have hψ_cd : ContDiffAt ℝ ∞ ψ u0 := hFeq_cd.contDiffAt_implicitFunction (by simp) hif
  have hψ0 : ψ u0 = η₀ := hFeq_cd.implicitFunction_apply_self (by simp) hif
  have hev : ∀ᶠ y in 𝓝 u0, Feq lam (hfun lam f) hh (y, ψ y) = Feq lam (hfun lam f) hh p₀ :=
    hFeq_cd.eventually_apply_implicitFunction (by simp) hif

  have key : ∀ᶠ y in 𝓝 u0, ∀ x : X, c x = y.1 → x ∈ S →
      u x y.2 = Real.exp lam • (ψ y) ⟨1, by norm_num⟩ := by
    have hmem : ∀ᶠ y : E × ℝ in 𝓝 u0, y.2 ∈ Ioo a b := by
      have h1 : IsOpen {y : E × ℝ | y.2 ∈ Ioo a b} := isOpen_Ioo.preimage continuous_snd
      have h2 : u0 ∈ {y : E × ℝ | y.2 ∈ Ioo a b} := by rw [hu0def]; exact ht₀
      exact h1.mem_nhds h2
    filter_upwards [hev, hmem] with y hy hyab
    intro x hcx hxS
    have h0x : u x 0 = c x := (hS x hxS).1
    have hsolx : ∀ t ∈ Ioo a b, HasDerivAt (u x) (f t (u x t)) t := (hS x hxS).2.1
    rw [hbase] at hy
    set W := ψ y with hW
    have hint_eq : ∀ σ : K, W σ = Real.exp (-(lam * (σ:ℝ))) • (y.1 + ∫ r in (0:ℝ)..(σ:ℝ),
        hfun lam f (clampK r, (y.2, W (clampK r)))) := by
      intro σ
      have h := congrArg (fun w : C(K,E) => w σ) hy
      simp only [Feq, Phieq, ContinuousMap.sub_apply, ContinuousMap.zero_apply, Mlam_apply,
        constCLM_apply, IntCLM_apply, nem_apply, comb_apply] at h
      rw [smul_add]
      have h1 : W σ - Real.exp (-(lam * (σ:ℝ))) • y.1
          = Real.exp (-(lam * (σ:ℝ))) • (∫ r in (0:ℝ)..(σ:ℝ), hfun lam f (clampK r, (y.2, W (clampK r)))) :=
        sub_eq_zero.mp h
      rw [sub_eq_iff_eq_add] at h1
      rw [h1, add_comm]
    set GR : ℝ → E := fun r => Real.exp (lam * r) • W (clampK r) with hGRdef
    have hGReq : ∀ σ : K, GR (σ:ℝ) = y.1 + ∫ r in (0:ℝ)..(σ:ℝ),
        hfun lam f (clampK r, (y.2, W (clampK r))) := by
      intro σ
      have h := hint_eq σ
      have h2 : Real.exp (lam * (σ:ℝ)) • W σ
          = Real.exp (lam * (σ:ℝ)) • (Real.exp (-(lam * (σ:ℝ))) • (y.1 + ∫ r in (0:ℝ)..(σ:ℝ),
              hfun lam f (clampK r, (y.2, W (clampK r))))) := by rw [h]
      rw [smul_smul] at h2
      have h3 : Real.exp (lam * (σ:ℝ)) * Real.exp (-(lam * (σ:ℝ))) = 1 := by
        rw [← Real.exp_add, show lam * (σ:ℝ) + -(lam * (σ:ℝ)) = 0 from by ring, Real.exp_zero]
      rw [h3, one_smul] at h2
      have h4 : GR (σ:ℝ) = Real.exp (lam * (σ:ℝ)) • W σ := by
        simp only [hGRdef, clampK_coe]
      rw [h4, h2]
    have hGR_cont : Continuous GR := by
      simp only [hGRdef]
      exact (by fun_prop : Continuous fun r : ℝ => Real.exp (lam * r)).smul
        (W.continuous.comp continuous_clampK)
    have hfun_apply : ∀ r ∈ Set.Icc (0:ℝ) 1,
        hfun lam f (clampK r, (y.2, W (clampK r))) = y.2 • f (y.2 * r) (GR r) := by
      intro r hr
      rw [clampK_of_mem hr]
      simp only [hfun, Subtype.coe_mk]
      congr 1
      rw [hGRdef]
      simp only [clampK_of_mem hr]
    have hGR_deriv : ∀ σ ∈ Ioo (0:ℝ) 1, HasDerivAt GR (y.2 • f (y.2 * σ) (GR σ)) σ := by
      intro σ hσ
      have hcont : Continuous fun r : ℝ => y.2 • f (y.2 * r) (GR r) :=
        continuous_const.smul (hf'.continuous.comp
          (by fun_prop : Continuous fun r : ℝ => (y.2 * r, GR r)))
      have h1 : GR =ᶠ[𝓝 σ] fun σ' => y.1 + ∫ r in (0:ℝ)..σ', y.2 • f (y.2 * r) (GR r) := by
        filter_upwards [isOpen_Ioo.mem_nhds hσ] with σ' hσ'
        rw [hGReq ⟨σ', ⟨le_of_lt hσ'.1, le_of_lt hσ'.2⟩⟩]
        congr 1
        apply intervalIntegral.integral_congr
        intro r hr
        rw [uIcc_of_le hσ'.1.le] at hr
        exact hfun_apply r ⟨hr.1, hr.2.trans hσ'.2.le⟩
      have h2 : HasDerivAt (fun σ' => y.1 + ∫ r in (0:ℝ)..σ', y.2 • f (y.2 * r) (GR r))
          (y.2 • f (y.2 * σ) (GR σ)) σ := by
        have h3 := intervalIntegral.integral_hasDerivAt_right
          (hcont.intervalIntegrable 0 σ)
          (hcont.stronglyMeasurableAtFilter MeasureTheory.volume (𝓝 σ))
          hcont.continuousAt
        simpa using h3.const_add y.1
      exact h2.congr_of_eventuallyEq h1
    have hGR_apply : ∀ σ : K, GR (σ:ℝ) = Real.exp (lam * (σ:ℝ)) • W σ :=
      fun σ => by simp only [hGRdef, clampK_coe]
    by_cases h0 : y.2 = 0
    · have hz : (∫ r in (0:ℝ)..(1:ℝ), hfun lam f (clampK r, (y.2, W (clampK r)))) = 0 := by
        rw [h0]
        simp [hfun]
      have hW1 : W ⟨1, by norm_num⟩ = Real.exp (-(lam * 1)) • y.1 := by
        have h := hint_eq ⟨1, by norm_num⟩
        rw [h, hz, add_zero]
      rw [h0, h0x, hcx, hW1, smul_smul]
      have hexp : Real.exp lam * Real.exp (-(lam * 1)) = 1 := by
        rw [← Real.exp_add]
        have h2 : lam + -(lam * 1) = 0 := by ring
        rw [h2, Real.exp_zero]
      rw [hexp, one_smul]
    · have hIcc_mem : Set.Icc (0:ℝ) 1 ∈ 𝓝[Set.Ici 0] 0 := by
        have h : Set.Ici (0:ℝ) ∩ Set.Iic (1:ℝ) ∈ 𝓝[Set.Ici (0:ℝ)] (0:ℝ) :=
          inter_mem_nhdsWithin _ (Iic_mem_nhds (by norm_num : (0:ℝ) < 1))
        rwa [Set.Ici_inter_Iic] at h
      have hdiff : DifferentiableOn ℝ (u x) (Set.Ioo a b) :=
        fun t ht => (hsolx t ht).differentiableAt.differentiableWithinAt (s := Set.Ioo a b)
      have hu_cont : ContinuousOn (u x) (Set.Ioo a b) := hdiff.continuousOn
      have hscale : ∀ r ∈ Set.Icc (0:ℝ) 1, y.2 * r ∈ Set.Ioo a b := by
        intro r hr
        rcases lt_or_gt_of_ne h0 with h | h
        · exact ⟨lt_of_lt_of_le hyab.1 (by simpa using mul_le_mul_of_nonpos_left hr.2 (le_of_lt h)),
            lt_of_le_of_lt (mul_nonpos_of_nonpos_of_nonneg (le_of_lt h) hr.1) hb⟩
        · exact ⟨lt_of_lt_of_le ha (mul_nonneg (le_of_lt h) hr.1),
            lt_of_le_of_lt (mul_le_of_le_one_right (le_of_lt h) hr.2) hyab.2⟩
      have hg_cont : ContinuousOn (fun r : ℝ => u x (y.2 * r)) (Set.Icc (0:ℝ) 1) :=
        hu_cont.comp (continuous_const.mul continuous_id).continuousOn hscale
      have hUcont : Continuous fun t : Set.Icc (0:ℝ) 1 => u x (y.2 * (t:ℝ)) :=
        hg_cont.domRestrict
      have hGcont : Continuous fun t : Set.Icc (0:ℝ) 1 => GR (t:ℝ) :=
        hGR_cont.continuousOn.domRestrict
      haveI : CompactSpace (Set.Icc (0:ℝ) 1) := isCompact_iff_compactSpace.mp isCompact_Icc
      let Φ : Set.Icc (0:ℝ) 1 × Set.Icc (0:ℝ) 1 → ℝ × E := fun q =>
        (y.2 * (q.1:ℝ), (1 - (q.2:ℝ)) • GR (q.1:ℝ) + (q.2:ℝ) • u x (y.2 * (q.1:ℝ)))
      have hΦcont : Continuous Φ := by
        have hv2 : Continuous fun q : Set.Icc (0:ℝ) 1 × Set.Icc (0:ℝ) 1 =>
            ((q.2 : Set.Icc (0:ℝ) 1) : ℝ) := continuous_subtype_val.comp continuous_snd
        exact Continuous.prodMk
          (continuous_const.mul (continuous_subtype_val.comp continuous_fst))
          (((continuous_const.sub hv2).smul (hGcont.comp continuous_fst)).add
            (hv2.smul (hUcont.comp continuous_fst)))
      have hFcont : Continuous fun q : Set.Icc (0:ℝ) 1 × Set.Icc (0:ℝ) 1 =>
          y.2 • D2 (fun p : ℝ × E => f p.1 p.2) (Φ q) :=
        (continuous_const : Continuous fun _ : Set.Icc (0:ℝ) 1 × Set.Icc (0:ℝ) 1 => y.2).smul
          ((D2_contDiff (fun p : ℝ × E => f p.1 p.2) hf').continuous.comp hΦcont)
      let Fc : C(Set.Icc (0:ℝ) 1 × Set.Icc (0:ℝ) 1, E →L[ℝ] E) :=
        ⟨fun q => y.2 • D2 (fun p : ℝ × E => f p.1 p.2) (Φ q), hFcont⟩
      let M : ℝ := ‖Fc‖
      have hMnn : 0 ≤ M := norm_nonneg Fc
      have hMbound : ∀ q : Set.Icc (0:ℝ) 1 × Set.Icc (0:ℝ) 1,
          ‖y.2 • D2 (fun p : ℝ × E => f p.1 p.2) (Φ q)‖ ≤ M :=
        fun q => ContinuousMap.norm_coe_le_norm Fc q
      have hGR_deriv' : ∀ t ∈ Set.Ico (0:ℝ) 1,
          HasDerivWithinAt GR (y.2 • f (y.2 * t) (GR t)) (Set.Ici t) t := by
        intro t ht
        rcases eq_or_lt_of_le ht.1 with h0' | hpos
        · subst h0'
          have hcont : Continuous fun r : ℝ => y.2 • f (y.2 * r) (GR r) :=
            continuous_const.smul (hf'.continuous.comp
              (by fun_prop : Continuous fun r : ℝ => (y.2 * r, GR r)))
          have h2 : HasDerivAt (fun σ' => y.1 + ∫ r in (0:ℝ)..σ', y.2 • f (y.2 * r) (GR r))
              (y.2 • f (y.2 * 0) (GR 0)) 0 := by
            have h3 := intervalIntegral.integral_hasDerivAt_right
              (hcont.intervalIntegrable 0 0)
              (hcont.stronglyMeasurableAtFilter MeasureTheory.volume (𝓝 0))
              hcont.continuousAt
            simpa using h3.const_add y.1
          have h1 : GR =ᶠ[𝓝[Set.Ici 0] (0:ℝ)]
              fun σ' => y.1 + ∫ r in (0:ℝ)..σ', y.2 • f (y.2 * r) (GR r) := by
            filter_upwards [hIcc_mem] with r hr
            have hinteg : (∫ r' in (0:ℝ)..r, hfun lam f (clampK r', (y.2, W (clampK r'))))
                = ∫ r' in (0:ℝ)..r, y.2 • f (y.2 * r') (GR r') := by
              apply intervalIntegral.integral_congr
              intro r' hr'
              rw [uIcc_of_le hr.1] at hr'
              exact hfun_apply r' ⟨hr'.1, hr'.2.trans hr.2⟩
            rw [show GR r = y.1 + ∫ r' in (0:ℝ)..r,
                hfun lam f (clampK r', (y.2, W (clampK r'))) from hGReq ⟨r, hr⟩, hinteg]
          have hpt : GR 0 = (fun σ' => y.1 + ∫ r in (0:ℝ)..σ', y.2 • f (y.2 * r) (GR r)) 0 := by
            rw [show GR 0 = y.1 + ∫ r in (0:ℝ)..0,
                hfun lam f (clampK r, (y.2, W (clampK r))) from hGReq ⟨0, by norm_num⟩]
            simp
          exact (h2.hasDerivWithinAt).congr_of_eventuallyEq h1 hpt
        · exact (hGR_deriv t ⟨hpos, ht.2⟩).hasDerivWithinAt
      have hg_deriv : ∀ t ∈ Set.Ico (0:ℝ) 1,
          HasDerivWithinAt (fun r : ℝ => u x (y.2 * r))
            (y.2 • f (y.2 * t) (u x (y.2 * t))) (Set.Ici t) t := by
        intro t ht
        have h1 : HasDerivAt (fun r : ℝ => y.2 * r) y.2 t := by
          simpa using (hasDerivAt_id t).const_mul y.2
        have h2 : HasDerivAt (u x) (f (y.2 * t) (u x (y.2 * t))) (y.2 * t) :=
          hsolx (y.2 * t) (hscale t ⟨ht.1, le_of_lt ht.2⟩)
        exact (h2.scomp t h1).hasDerivWithinAt
      have hlip : ∀ t ∈ Set.Ico (0:ℝ) 1, LipschitzOnWith ⟨M, hMnn⟩
          (fun z : E => y.2 • f (y.2 * t) z) (segment ℝ (GR t) (u x (y.2 * t))) := by
        intro t ht
        refine LipschitzOnWith.of_dist_le_mul (fun z₁ hz₁ z₂ hz₂ => ?_)
        rw [dist_eq_norm, dist_eq_norm]
        have hbd : ∀ z ∈ segment ℝ (GR t) (u x (y.2 * t)),
            ‖fderiv ℝ (fun z' : E => y.2 • f (y.2 * t) z') z‖ ≤ M := by
          intro z hz
          have hfz : HasFDerivAt (fun z' : E => f (y.2 * t) z')
              ((fderiv ℝ (fun p : ℝ × E => f p.1 p.2) (y.2 * t, z)).comp
                (ContinuousLinearMap.inr ℝ ℝ E)) z :=
            ((hf'.differentiable (by simp) (y.2 * t, z)).hasFDerivAt.comp z
              (hasFDerivAt_prodMk_right (y.2 * t) z))
          have hfd : fderiv ℝ (fun z' : E => y.2 • f (y.2 * t) z') z
              = y.2 • D2 (fun p : ℝ × E => f p.1 p.2) (y.2 * t, z) := by
            rw [show fderiv ℝ (fun z' : E => y.2 • f (y.2 * t) z') z
                = y.2 • (fderiv ℝ (fun p : ℝ × E => f p.1 p.2) (y.2 * t, z)).comp
                    (ContinuousLinearMap.inr ℝ ℝ E) from (hfz.const_smul y.2).fderiv]
            congr 1
            rw [D2_apply, fderiv_snd_eq _ hf']
          rw [hfd]
          rw [segment_eq_image] at hz
          obtain ⟨θ, hθ, hzθ⟩ := hz
          have hΦq : Φ ((⟨t, ⟨ht.1, le_of_lt ht.2⟩⟩ : Set.Icc (0:ℝ) 1),
              (⟨θ, hθ⟩ : Set.Icc (0:ℝ) 1)) = (y.2 * t, z) := by
            show (y.2 * t, (1 - θ) • GR t + θ • u x (y.2 * t)) = (y.2 * t, z)
            rw [show (1 - θ) • GR t + θ • u x (y.2 * t) = z from hzθ]
          have hq := hMbound ((⟨t, ⟨ht.1, le_of_lt ht.2⟩⟩ : Set.Icc (0:ℝ) 1),
            (⟨θ, hθ⟩ : Set.Icc (0:ℝ) 1))
          rw [hΦq] at hq
          exact hq
        have hdiffseg : ∀ z ∈ segment ℝ (GR t) (u x (y.2 * t)),
            DifferentiableAt ℝ (fun z' : E => y.2 • f (y.2 * t) z') z := by
          intro z hz
          exact (((hf'.differentiable (by simp) (y.2 * t, z)).hasFDerivAt.comp z
            (hasFDerivAt_prodMk_right (y.2 * t) z)).differentiableAt).const_smul y.2
        have hmain : ‖y.2 • f (y.2 * t) z₂ - y.2 • f (y.2 * t) z₁‖ ≤ M * ‖z₂ - z₁‖ :=
          Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (E := E) (G := E)
            (f := fun z : E => y.2 • f (y.2 * t) z) (C := M)
            (s := segment ℝ (GR t) (u x (y.2 * t)))
            hdiffseg hbd (convex_segment (𝕜 := ℝ) (E := E) (GR t) (u x (y.2 * t))) hz₁ hz₂
        calc ‖y.2 • f (y.2 * t) z₁ - y.2 • f (y.2 * t) z₂‖
            = ‖y.2 • f (y.2 * t) z₂ - y.2 • f (y.2 * t) z₁‖ :=
              norm_sub_rev (y.2 • f (y.2 * t) z₁) (y.2 • f (y.2 * t) z₂)
          _ ≤ M * ‖z₂ - z₁‖ := hmain
          _ = (⟨M, hMnn⟩ : NNReal) * ‖z₁ - z₂‖ := by
              rw [norm_sub_rev z₁ z₂]
      have h0eq : GR 0 = u x (y.2 * 0) := by
        rw [show GR 0 = y.1 + ∫ r in (0:ℝ)..0,
            hfun lam f (clampK r, (y.2, W (clampK r))) from hGReq ⟨0, by norm_num⟩,
          mul_zero, h0x, hcx]
        simp
      have hEqOn : Set.EqOn GR (fun r : ℝ => u x (y.2 * r)) (Set.Icc (0:ℝ) 1) :=
        ODE_solution_unique_of_mem_Icc_right
          (v := fun t z => y.2 • f (y.2 * t) z)
          (s := fun t => segment ℝ (GR t) (u x (y.2 * t)))
          (K := ⟨M, hMnn⟩) hlip hGR_cont.continuousOn hGR_deriv'
          (fun t ht => left_mem_segment ℝ _ _) hg_cont hg_deriv
          (fun t ht => right_mem_segment ℝ _ _) h0eq
      have hG1 : GR 1 = u x (y.2 * 1) := hEqOn (by norm_num)
      have hGR1 : GR 1 = Real.exp lam • W (⟨1, by norm_num⟩ : K) := by
        have h := hGR_apply ⟨1, by norm_num⟩
        simpa using h
      rw [hGR1] at hG1
      simpa using hG1.symm
  -- Pull `key` back along `p ↦ (c p.1, p.2) : X × ℝ → E × ℝ`.
  have keyX : (fun p : X × ℝ => u p.1 p.2) =ᶠ[𝓝 (x₀, t₀)]
      (fun p : X × ℝ => Real.exp lam • (ψ (c p.1, p.2)) ⟨1, by norm_num⟩) := by
    have hFcont : Continuous fun p : X × ℝ => ((c p.1, p.2) : E × ℝ) :=
      (hc.continuous.comp continuous_fst).prodMk continuous_snd
    have hFu : (fun p : X × ℝ => ((c p.1, p.2) : E × ℝ)) (x₀, t₀) = u0 := by
      simp only [hu0def]
    have hQ : ∀ᶠ p : X × ℝ in 𝓝 (x₀, t₀),
        ∀ x : X, c x = c p.1 → x ∈ S →
          u x p.2 = Real.exp lam • (ψ (c p.1, p.2)) ⟨1, by norm_num⟩ := by
      have hkey : ∀ᶠ y in 𝓝 ((fun p : X × ℝ => ((c p.1, p.2) : E × ℝ)) (x₀, t₀)),
          ∀ x : X, c x = y.1 → x ∈ S →
            u x y.2 = Real.exp lam • (ψ y) ⟨1, by norm_num⟩ := by
        rw [hFu]; exact key
      exact Filter.Tendsto.eventually hFcont.continuousAt hkey
    have hSc : ∀ᶠ p : X × ℝ in 𝓝 (x₀, t₀), p.1 ∈ S :=
      Filter.Tendsto.eventually (continuous_fst.tendsto (x₀, t₀)) hSmem
    filter_upwards [hQ, hSc] with p hp hpS
    exact hp p.1 rfl hpS
  have hcd : ContDiffAt ℝ ∞ (fun p : X × ℝ => Real.exp lam • (ψ (c p.1, p.2)) ⟨1, by norm_num⟩)
      (x₀, t₀) := by
    have h1 : ContDiffAt ℝ ∞ (fun p : X × ℝ => ((c p.1, p.2) : E × ℝ)) (x₀, t₀) :=
      (hc.contDiffAt.comp (x₀, t₀) contDiffAt_fst).prodMk contDiffAt_snd
    have h2 : ContDiffAt ℝ ∞ (fun p : X × ℝ => ψ (c p.1, p.2)) (x₀, t₀) :=
      hψ_cd.comp (x₀, t₀) h1
    have h3 : ContDiffAt ℝ ∞ (fun p : X × ℝ => (ψ (c p.1, p.2)) ⟨1, by norm_num⟩) (x₀, t₀) := by
      have heval : ContDiff ℝ ∞ (fun w : C(K,E) => w ⟨1, by norm_num⟩) := by
        have hlin : IsBoundedLinearMap ℝ (fun w : C(K,E) => w ⟨1, by norm_num⟩) :=
          ⟨⟨fun a b => rfl, fun c a => rfl⟩, ⟨1, one_pos, fun w => by
            rw [one_mul]; exact ContinuousMap.norm_coe_le_norm w ⟨1, by norm_num⟩⟩⟩
        exact hlin.contDiff
      exact heval.contDiffAt.comp (x₀, t₀) h2
    exact (contDiffAt_const (c := Real.exp lam)).smul h3
  exact hcd.congr_of_eventuallyEq keyX

end

end Commons.Analysis.ODE
