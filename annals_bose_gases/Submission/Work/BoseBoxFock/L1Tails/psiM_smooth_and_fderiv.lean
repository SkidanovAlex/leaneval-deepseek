import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.L1Tails.chiChiCoulAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.L1Tails.psiM_smooth_and_fderiv`

`psiM ℓ m G z = ∫_{y ∈ halfBall ℓ} χ_ℓ(y)·χ_ℓ(z+y−ℓ•latVec m)·G (z+y−ℓ•latVec m) y`

is a *parametric integral* over the compact set `halfBall ℓ` of a `C^∞` family: it is therefore
`C^∞` (with the derivative given by differentiating under the integral sign), it has compact
support (the second `χ_ℓ` factor confines `z` to a bounded set when `ℓ > 0`), and for `ℓ ≤ 0` its
domain `halfBall ℓ = closedBall 0 (ℓ/2)` is Lebesgue-null, so `psiM ℓ m G = 0`.

The two mathematical ingredients are proved in §1 in the general form in which they are used:

* `fderiv_section` — the derivative of a section `z ↦ Ψ z y` is the partial derivative;
* `hasFDerivAt_integral_of_compactSupport` — differentiation under the integral sign;
* `contDiff_integral_of_compactSupport` — the parametric integral of a `C^n` family supported in a
  fixed compact set is `C^n` (proved by induction on `n`, the induction step using the previous
  lemma and the fact that the derivative family is again of the same shape).
-/

noncomputable section

open MeasureTheory
open scoped Topology

namespace Work.BoseBoxFock.L1Tails

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

universe u

/-! ## 1. Parametric integrals over a fixed compact set -/

/-- The derivative of the *section* `z ↦ Ψ z y` of a two-variable function at a point where the
uncurried function is differentiable is the first partial derivative,
`(fderiv (uncurry Ψ) (z,y)) ∘ inl`. -/
theorem fderiv_section {E Y F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Ψ : E → Y → F} {z : E} {y : Y} (h : DifferentiableAt ℝ (Function.uncurry Ψ) (z, y)) :
    fderiv ℝ (fun z' => Ψ z' y) z
      = (fderiv ℝ (Function.uncurry Ψ) (z, y)).comp (ContinuousLinearMap.inl ℝ E Y) := by
  have hsec : HasFDerivAt (fun z' : E => (z', y)) (ContinuousLinearMap.inl ℝ E Y) z :=
    hasFDerivAt_prodMk_left z y
  have hcomp := h.hasFDerivAt.comp z hsec
  have heq : (fun z' : E => Ψ z' y) = (Function.uncurry Ψ) ∘ (fun z' : E => (z', y)) := rfl
  rw [heq, hcomp.fderiv]

/-- **Differentiation under the integral sign** for a family `Ψ : E → Y → F` which is `C^1` and
whose sections `Ψ z` are all supported in a fixed compact set `k`.  The derivative of
`z ↦ ∫ y, Ψ z y` is the integral of the partial derivatives. -/
theorem hasFDerivAt_integral_of_compactSupport {E Y F : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [ProperSpace E] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasureSpace Y]
    [BorelSpace Y] [SecondCountableTopology Y] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] [IsFiniteMeasureOnCompacts (volume : Measure Y)]
    {k : Set Y} (hk : IsCompact k) {Ψ : E → Y → F} (hsupp : ∀ z y, y ∉ k → Ψ z y = 0)
    (hΨ : ContDiff ℝ 1 (Function.uncurry Ψ)) (z : E) :
    HasFDerivAt (fun z => ∫ y, Ψ z y) (∫ y, fderiv ℝ (fun z' => Ψ z' y) z) z ∧
      ∀ w : E, fderiv ℝ (fun z => ∫ y, Ψ z y) z w
        = ∫ y, fderiv ℝ (fun z' => Ψ z' y) z w := by
  have hdiff : Differentiable ℝ (Function.uncurry Ψ) := hΨ.differentiable one_ne_zero
  have hcont : Continuous (Function.uncurry Ψ) := hΨ.continuous
  have hderiv_cont : Continuous (fderiv ℝ (Function.uncurry Ψ)) :=
    hΨ.continuous_fderiv one_ne_zero
  obtain ⟨C, hC⟩ := ((isCompact_closedBall z 1).prod hk).exists_bound_of_continuousOn
    hderiv_cont.continuousOn
  have hderiv_zero : ∀ x y, y ∉ k → fderiv ℝ (Function.uncurry Ψ) (x, y) = 0 := by
    intro x y hy
    have hconst : (Function.uncurry Ψ) =ᶠ[𝓝 (x, y)] fun _ => 0 := by
      rw [nhds_prod_eq]
      filter_upwards [Filter.prod_mem_prod Filter.univ_mem (hk.isClosed.isOpen_compl.mem_nhds hy)]
      rintro ⟨x', y'⟩ ⟨-, hy'⟩
      exact hsupp x' y' hy'
    exact (hasFDerivAt_zero_of_eventually_const (0 : F) hconst).fderiv
  have hbnd_int : Integrable (k.indicator fun _ => C) volume :=
    (ContinuousOn.integrableOn_compact hk continuousOn_const).integrable_indicator hk.measurableSet
  have hsec_eq : ∀ y : Y, fderiv ℝ (fun z' => Ψ z' y) z
      = (fderiv ℝ (Function.uncurry Ψ) (z, y)).comp (ContinuousLinearMap.inl ℝ E Y) :=
    fun y => fderiv_section (hdiff.differentiableAt)
  have hmeas : AEStronglyMeasurable (fun y => fderiv ℝ (fun z' => Ψ z' y) z) volume := by
    rw [show (fun y : Y => fderiv ℝ (fun z' => Ψ z' y) z)
        = fun y => (fderiv ℝ (Function.uncurry Ψ) (z, y)).comp
            (ContinuousLinearMap.inl ℝ E Y) from funext hsec_eq]
    exact ((hderiv_cont.comp (continuous_const.prodMk continuous_id)).clm_comp
      continuous_const).aestronglyMeasurable
  have hbound_ball : ∀ᵐ y ∂volume, ∀ x ∈ Metric.ball z 1,
      ‖fderiv ℝ (fun z' => Ψ z' y) x‖ ≤ (k.indicator fun _ => C) y := by
    filter_upwards with y
    intro x hx
    rw [show fderiv ℝ (fun z' => Ψ z' y) x
        = (fderiv ℝ (Function.uncurry Ψ) (x, y)).comp
            (ContinuousLinearMap.inl ℝ E Y) from fderiv_section (hdiff.differentiableAt)]
    by_cases hy : y ∈ k
    · rw [Set.indicator_of_mem hy]
      calc ‖(fderiv ℝ (Function.uncurry Ψ) (x, y)).comp (ContinuousLinearMap.inl ℝ E Y)‖
          ≤ ‖fderiv ℝ (Function.uncurry Ψ) (x, y)‖ * ‖ContinuousLinearMap.inl ℝ E Y‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ ‖fderiv ℝ (Function.uncurry Ψ) (x, y)‖ * 1 := by
            gcongr
            exact ContinuousLinearMap.norm_inl_le_one ℝ E Y
        _ = ‖fderiv ℝ (Function.uncurry Ψ) (x, y)‖ := mul_one _
        _ ≤ C := hC (x, y) ⟨Metric.ball_subset_closedBall hx, hy⟩
    · rw [Set.indicator_of_notMem hy, hderiv_zero x y hy, ContinuousLinearMap.zero_comp]
      simp
  have hphi_int : Integrable (fun y => fderiv ℝ (fun z' => Ψ z' y) z) volume :=
    hbnd_int.mono' hmeas (hbound_ball.mono fun y hy => hy z (Metric.mem_ball_self one_pos))
  have hFD : HasFDerivAt (fun z => ∫ y, Ψ z y) (∫ y, fderiv ℝ (fun z' => Ψ z' y) z) z := by
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (E := F) (H := E) (μ := volume)
      (F := fun x y => Ψ x y) (F' := fun x y => fderiv ℝ (fun z' => Ψ z' y) x)
      (s := Metric.ball z 1) (bound := k.indicator fun _ => C) (Metric.ball_mem_nhds z one_pos)
      ?_ ?_ ?_ ?_ ?_ ?_
    · exact Filter.Eventually.of_forall fun x =>
        (hcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    · exact (hcont.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
        (HasCompactSupport.intro hk fun y hy => hsupp z y hy)
    · exact hmeas
    · exact hbound_ball
    · exact hbnd_int
    · filter_upwards with y
      intro x hx
      have h := (hdiff.differentiableAt.hasFDerivAt.comp x (hasFDerivAt_prodMk_left x y))
      rw [show fderiv ℝ (fun z' => Ψ z' y) x
          = (fderiv ℝ (Function.uncurry Ψ) (x, y)).comp
              (ContinuousLinearMap.inl ℝ E Y) from fderiv_section (hdiff.differentiableAt)]
      exact h
  refine ⟨hFD, fun w => ?_⟩
  rw [hFD.fderiv]
  exact ContinuousLinearMap.integral_apply hphi_int w

/-- **The parametric integral of a `C^n` family supported in a fixed compact set is `C^n`.**
(Proved by induction on `n`: the induction step differentiates under the integral sign with
`hasFDerivAt_integral_of_compactSupport` and observes that the derivative family
`(z,y) ↦ (fderiv (uncurry Ψ) (z,y)) ∘ inl` is again of the same shape with codomain `E →L[ℝ] F`.) -/
theorem contDiff_integral_of_compactSupport {E Y : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [ProperSpace E] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasureSpace Y]
    [BorelSpace Y] [SecondCountableTopology Y] [IsFiniteMeasureOnCompacts (volume : Measure Y)]
    {k : Set Y} (hk : IsCompact k) {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] {Ψ : E → Y → F} (hsupp : ∀ z y, y ∉ k → Ψ z y = 0) :
    ∀ n : ℕ, ContDiff ℝ (n : WithTop ℕ∞) (Function.uncurry Ψ) →
      ContDiff ℝ (n : WithTop ℕ∞) (fun z => ∫ y, Ψ z y) := by
  intro n
  induction n generalizing F Ψ with
  | zero =>
    intro hΨ
    have hcont : Continuous (Function.uncurry Ψ) := contDiff_zero.mp hΨ
    refine contDiff_zero.mpr ?_
    rw [continuous_iff_continuousAt]
    intro z
    obtain ⟨C, hC⟩ := ((isCompact_closedBall z 1).prod hk).exists_bound_of_continuousOn
      hcont.continuousOn
    refine tendsto_integral_filter_of_dominated_convergence (l := 𝓝 z) (k.indicator fun _ => C)
      ?_ ?_ ?_ ?_
    · exact Filter.Eventually.of_forall fun x =>
        (hcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    · filter_upwards [Metric.ball_mem_nhds z one_pos] with x hx
      filter_upwards with y
      by_cases hy : y ∈ k
      · rw [Set.indicator_of_mem hy]
        exact hC (x, y) ⟨Metric.ball_subset_closedBall hx, hy⟩
      · rw [hsupp x y hy, Set.indicator_of_notMem hy]
        simp
    · exact (ContinuousOn.integrableOn_compact hk continuousOn_const).integrable_indicator
        hk.measurableSet
    · filter_upwards with y
      exact (hcont.comp (continuous_id.prodMk continuous_const)).continuousAt
  | succ n ih =>
    intro hΨ
    have hΨ1 : ContDiff ℝ 1 (Function.uncurry Ψ) :=
      hΨ.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ((n : ℕ) : WithTop ℕ∞) + 1)
    let Φ : E → Y → (E →L[ℝ] F) := fun z y =>
      (fderiv ℝ (Function.uncurry Ψ) (z, y)).comp (ContinuousLinearMap.inl ℝ E Y)
    have hΦdiff : ContDiff ℝ ((n : ℕ) : WithTop ℕ∞) (Function.uncurry Φ) := by
      have hfd : ContDiff ℝ ((n : ℕ) : WithTop ℕ∞) (fderiv ℝ (Function.uncurry Ψ)) :=
        hΨ.fderiv_right (m := (n : WithTop ℕ∞)) (le_refl _)
      have hclm := hfd.clm_comp (contDiff_const :
        ContDiff ℝ ((n : ℕ) : WithTop ℕ∞) (fun _ : E × Y => (ContinuousLinearMap.inl ℝ E Y)))
      exact hclm
    have hsuppΦ : ∀ z y, y ∉ k → Φ z y = 0 := by
      intro z y hy
      have hzero : fderiv ℝ (Function.uncurry Ψ) (z, y) = 0 := by
        have hconst : (Function.uncurry Ψ) =ᶠ[𝓝 (z, y)] fun _ => 0 := by
          rw [nhds_prod_eq]
          filter_upwards [Filter.prod_mem_prod Filter.univ_mem
            (hk.isClosed.isOpen_compl.mem_nhds hy)]
          rintro ⟨x', y'⟩ ⟨-, hy'⟩
          exact hsupp x' y' hy'
        exact (hasFDerivAt_zero_of_eventually_const (0 : F) hconst).fderiv
      show (fderiv ℝ (Function.uncurry Ψ) (z, y)).comp (ContinuousLinearMap.inl ℝ E Y) = 0
      rw [hzero, ContinuousLinearMap.zero_comp]
    have ihΦ : ContDiff ℝ ((n : ℕ) : WithTop ℕ∞) (fun z => ∫ y, Φ z y) := ih hsuppΦ hΦdiff
    have hF' : ∀ z, HasFDerivAt (fun z => ∫ y, Ψ z y)
        (∫ y, fderiv ℝ (fun z' => Ψ z' y) z) z :=
      fun z => (hasFDerivAt_integral_of_compactSupport hk hsupp hΨ1 z).1
    have hcontF' : ContDiff ℝ ((n : ℕ) : WithTop ℕ∞)
        (fun z => ∫ y, fderiv ℝ (fun z' => Ψ z' y) z) := by
      have heq : (fun z => ∫ y, fderiv ℝ (fun z' => Ψ z' y) z) = fun z => ∫ y, Φ z y := by
        funext z
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        exact fderiv_section ((hΨ1.differentiable one_ne_zero).differentiableAt)
      rw [heq]
      exact ihΦ
    exact contDiff_succ_iff_hasFDerivAt.mpr
      ⟨(fun z => ∫ y, fderiv ℝ (fun z' => Ψ z' y) z), hcontF', hF'⟩

/-! ## 2. The window `χ_ℓ` and the domain `halfBall ℓ` -/

/-- The complexified window `χ_ℓ` is `C^∞` (for `ℓ ≠ 0`). -/
lemma chiC_contDiff {ℓ : ℝ} (hℓ : ℓ ≠ 0) : ContDiff ℝ (⊤ : ℕ∞) (chiC ℓ) :=
  Complex.ofRealCLM.contDiff.comp (Submission.BoseGases.chiScale_contDiff hℓ)

/-- `χ_ℓ` vanishes outside the ball of radius `ℓ/2` (for `ℓ > 0`). -/
lemma chiScale_eq_zero_of_half_lt_norm {ℓ : ℝ} (hℓ : 0 < ℓ) {x : E3} (hx : ℓ / 2 < ‖x‖) :
    Submission.BoseGases.chiScale ℓ x = 0 := by
  rw [Submission.BoseGases.chiScale]
  refine Submission.BoseGases.chi_eq_zero_of_norm_gt _ ?_
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hℓ.le), inv_mul_eq_div,
    lt_div_iff₀ hℓ]
  linarith

/-- `χ_ℓ`, complexified, vanishes outside the ball of radius `ℓ/2` (for `ℓ > 0`). -/
lemma chiC_eq_zero_of_half_lt_norm {ℓ : ℝ} (hℓ : 0 < ℓ) {x : E3} (hx : ℓ / 2 < ‖x‖) :
    chiC ℓ x = 0 := by
  rw [chiC, chiScale_eq_zero_of_half_lt_norm hℓ hx, Complex.ofReal_zero]

/-- Membership in the integration domain `halfBall ℓ`. -/
lemma mem_halfBall_iff {ℓ : ℝ} {y : E3} : y ∈ halfBall ℓ ↔ ‖y‖ ≤ ℓ / 2 := by
  rw [halfBall, Metric.mem_closedBall, dist_eq_norm, sub_zero]

/-- The integrand of `psiM`, as a function of the two variables `(z, y)`. -/
def psiG (ℓ : ℝ) (m : Fin 3 → ℤ) (G : E3 → E3 → ℂ) : E3 → E3 → ℂ :=
  fun z y => chiC ℓ y * chiC ℓ (z + y - ℓ • Work.BoseBoxFock.latVec m)
    * G (z + y - ℓ • Work.BoseBoxFock.latVec m) y

/-- `psiM` is the set integral of `psiG` over `halfBall ℓ` (definitionally). -/
lemma psiM_eq_setIntegral (ℓ : ℝ) (m : Fin 3 → ℤ) (G : E3 → E3 → ℂ) :
    psiM ℓ m G = fun z => ∫ y in halfBall ℓ, psiG ℓ m G z y := rfl

/-- The uncurried integrand of `psiM` is `C^∞` when `G` is. -/
lemma contDiff_uncurry_psiG {ℓ : ℝ} {m : Fin 3 → ℤ} {G : E3 → E3 → ℂ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry G)) (hℓ : ℓ ≠ 0) :
    ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (psiG ℓ m G)) := by
  have hchi : ContDiff ℝ (⊤ : ℕ∞) (chiC ℓ) := chiC_contDiff hℓ
  have hT : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : E3 × E3 => p.1 + p.2 - ℓ • Work.BoseBoxFock.latVec m) :=
    (contDiff_fst.add contDiff_snd).sub contDiff_const
  have hA : ContDiff ℝ (⊤ : ℕ∞) (fun p : E3 × E3 => chiC ℓ p.2) := hchi.comp contDiff_snd
  have hB : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : E3 × E3 => chiC ℓ (p.1 + p.2 - ℓ • Work.BoseBoxFock.latVec m)) := hchi.comp hT
  have hC : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : E3 × E3 => G (p.1 + p.2 - ℓ • Work.BoseBoxFock.latVec m) p.2) :=
    hG.comp (hT.prodMk contDiff_snd)
  have h := hA.mul hB |>.mul hC
  have hgoal : Function.uncurry (psiG ℓ m G) = fun p : E3 × E3 =>
      (chiC ℓ p.2 * chiC ℓ (p.1 + p.2 - ℓ • Work.BoseBoxFock.latVec m))
        * G (p.1 + p.2 - ℓ • Work.BoseBoxFock.latVec m) p.2 := by
    funext p
    rfl
  rw [hgoal]
  exact h

/-- The derivative of the section `z ↦ psiG ℓ m G z y`. -/
lemma fderiv_psiG_apply {ℓ : ℝ} {m : Fin 3 → ℤ} {G : E3 → E3 → ℂ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry G)) (hℓ : ℓ ≠ 0) (z y w : E3) :
    fderiv ℝ (fun z' => psiG ℓ m G z' y) z w
      = chiC ℓ y * fderiv ℝ (fun w' => chiC ℓ w' * G w' y)
          (z + y - ℓ • Work.BoseBoxFock.latVec m) w := by
  have hGy : ContDiff ℝ (⊤ : ℕ∞) (fun u : E3 => G u y) :=
    hG.comp (contDiff_id.prodMk contDiff_const)
  have hFdiff : DifferentiableAt ℝ (fun u : E3 => chiC ℓ u * G u y)
      (z + y - ℓ • Work.BoseBoxFock.latVec m) :=
    (((chiC_contDiff hℓ).mul hGy).differentiable (by simp)).differentiableAt
  have h1 : HasFDerivAt (fun z' : E3 => z' + y - ℓ • Work.BoseBoxFock.latVec m)
      (ContinuousLinearMap.id ℝ E3) z :=
    ((hasFDerivAt_id z).add_const y).add_const (-(ℓ • Work.BoseBoxFock.latVec m))
  have h2 : HasFDerivAt (fun u : E3 => chiC ℓ u * G u y)
      (fderiv ℝ (fun u : E3 => chiC ℓ u * G u y) (z + y - ℓ • Work.BoseBoxFock.latVec m))
      (z + y - ℓ • Work.BoseBoxFock.latVec m) := hFdiff.hasFDerivAt
  have h3 := h2.comp z h1
  have h4 := h3.const_mul (chiC ℓ y)
  have hfun : (fun z' => psiG ℓ m G z' y) = fun z' =>
      chiC ℓ y * ((fun u : E3 => chiC ℓ u * G u y)
        ∘ (fun z' : E3 => z' + y - ℓ • Work.BoseBoxFock.latVec m)) z' := by
    funext z'
    simp only [Function.comp_apply, psiG, mul_assoc]
  rw [hfun, h4.fderiv, ContinuousLinearMap.comp_id]
  simp [smul_eq_mul]

/-! ## 3. The target -/

theorem psiM_smooth_and_fderiv {ℓ : ℝ} {m : Fin 3 → ℤ} {G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry G)) :
    ContDiff ℝ (⊤ : ℕ∞) (Work.BoseBoxFock.L1Tails.psiM ℓ m G) ∧
      HasCompactSupport (Work.BoseBoxFock.L1Tails.psiM ℓ m G) ∧
      (∀ z w : EuclideanSpace ℝ (Fin 3), fderiv ℝ (Work.BoseBoxFock.L1Tails.psiM ℓ m G) z w
        = ∫ y in Work.BoseBoxFock.L1Tails.halfBall ℓ,
            Work.BoseBoxFock.L1Tails.chiC ℓ y *
              fderiv ℝ (fun w' => Work.BoseBoxFock.L1Tails.chiC ℓ w' * G w' y)
                (z + y - ℓ • Work.BoseBoxFock.latVec m) w) := by
  by_cases hℓ : 0 < ℓ
  · -- The domain `halfBall ℓ` has positive radius: `χ_ℓ` vanishes outside it.
    have hℓne : ℓ ≠ 0 := ne_of_gt hℓ
    have hsupp_y : ∀ z y, y ∉ halfBall ℓ → psiG ℓ m G z y = 0 := by
      intro z y hy
      have hy' : ℓ / 2 < ‖y‖ := by
        rw [mem_halfBall_iff, not_le] at hy
        exact hy
      simp [psiG, chiC_eq_zero_of_half_lt_norm hℓ hy']
    have hpsi : psiM ℓ m G = fun z => ∫ y, psiG ℓ m G z y := by
      funext z
      show (∫ y in halfBall ℓ, psiG ℓ m G z y) = ∫ y, psiG ℓ m G z y
      exact setIntegral_eq_integral_of_forall_compl_eq_zero (hsupp_y z)
    have hsupp_c : ∀ z, z ∉ Metric.closedBall (0 : E3) (ℓ * (1 + ‖Work.BoseBoxFock.latVec m‖)) →
        psiM ℓ m G z = 0 := by
      intro z hz
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, not_le] at hz
      have hz' : (∫ y, psiG ℓ m G z y) = 0 := by
        rw [show (∫ y, psiG ℓ m G z y) = ∫ y in halfBall ℓ, psiG ℓ m G z y from
          (setIntegral_eq_integral_of_forall_compl_eq_zero (hsupp_y z)).symm]
        refine setIntegral_eq_zero_of_ae_eq_zero (Filter.Eventually.of_forall fun y hy => ?_)
        have hy' : ‖y‖ ≤ ℓ / 2 := mem_halfBall_iff.mp hy
        have hnorm : ℓ / 2 < ‖z + y - ℓ • Work.BoseBoxFock.latVec m‖ := by
          have hs : ‖z‖ ≤ ‖z + y - ℓ • Work.BoseBoxFock.latVec m‖
              + ‖y - ℓ • Work.BoseBoxFock.latVec m‖ := by
            have hz_eq : z = (z + y - ℓ • Work.BoseBoxFock.latVec m)
                - (y - ℓ • Work.BoseBoxFock.latVec m) := by abel
            calc ‖z‖ = ‖(z + y - ℓ • Work.BoseBoxFock.latVec m)
                  - (y - ℓ • Work.BoseBoxFock.latVec m)‖ := congrArg norm hz_eq
              _ ≤ ‖z + y - ℓ • Work.BoseBoxFock.latVec m‖
                    + ‖y - ℓ • Work.BoseBoxFock.latVec m‖ := norm_sub_le _ _
          have ht : ‖y - ℓ • Work.BoseBoxFock.latVec m‖
              ≤ ‖y‖ + ℓ * ‖Work.BoseBoxFock.latVec m‖ := by
            calc ‖y - ℓ • Work.BoseBoxFock.latVec m‖ ≤ ‖y‖ + ‖ℓ • Work.BoseBoxFock.latVec m‖ :=
                  norm_sub_le _ _
              _ = ‖y‖ + ℓ * ‖Work.BoseBoxFock.latVec m‖ := by
                  rw [norm_smul, Real.norm_of_nonneg hℓ.le]
          linarith
        simp [psiG, chiC_eq_zero_of_half_lt_norm hℓ hnorm]
      simpa [hpsi] using hz'
    have huncurry : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (psiG ℓ m G)) :=
      contDiff_uncurry_psiG hG hℓne
    have hcd : ContDiff ℝ (⊤ : ℕ∞) (psiM ℓ m G) := by
      rw [hpsi, contDiff_iff_forall_nat_le]
      intro n _
      exact contDiff_integral_of_compactSupport (isCompact_closedBall (0 : E3) (ℓ / 2)) hsupp_y n
        (huncurry.of_le (WithTop.coe_le_coe.mpr le_top))
    have hcs : HasCompactSupport (psiM ℓ m G) :=
      HasCompactSupport.intro (isCompact_closedBall (0 : E3) (ℓ * (1 + ‖Work.BoseBoxFock.latVec m‖)))
        hsupp_c
    refine ⟨hcd, hcs, fun z w => ?_⟩
    have hΨ1 : ContDiff ℝ 1 (Function.uncurry (psiG ℓ m G)) := huncurry.of_le (by norm_num)
    have hfd := (hasFDerivAt_integral_of_compactSupport
      (isCompact_closedBall (0 : E3) (ℓ / 2)) hsupp_y hΨ1 z).2 w
    rw [hpsi, hfd]
    rw [integral_congr_ae (Filter.Eventually.of_forall fun y => fderiv_psiG_apply hG hℓne z y w)]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun y hy => by simp [chiC_eq_zero_of_half_lt_norm hℓ (by
        rw [mem_halfBall_iff, not_le] at hy; exact hy)])).symm
  · -- `ℓ ≤ 0`: the domain `halfBall ℓ` is Lebesgue-null, so `psiM ℓ m G = 0`.
    have hℓle : ℓ ≤ 0 := le_of_not_gt hℓ
    have hvol : volume (halfBall ℓ) = 0 := by
      refine measure_mono_null ?_ (measure_singleton (0 : E3))
      intro y hy
      rw [Set.mem_singleton_iff]
      have hy' : ‖y‖ ≤ ℓ / 2 := mem_halfBall_iff.mp hy
      exact norm_eq_zero.mp (le_antisymm (by linarith) (norm_nonneg y))
    have hzero : psiM ℓ m G = 0 := by
      funext z
      rw [psiM]
      exact setIntegral_measure_zero _ hvol
    refine ⟨?_, ?_, ?_⟩
    · rw [hzero]
      exact contDiff_const
    · rw [hzero]
      exact HasCompactSupport.zero
    · intro z w
      rw [hzero]
      have hz : fderiv ℝ (0 : E3 → ℂ) z w = 0 := by
        rw [show (0 : E3 → ℂ) = Function.const E3 (0 : ℂ) from rfl, fderiv_const]
        simp
      rw [hz]
      exact (setIntegral_measure_zero _ hvol).symm

end Work.BoseBoxFock.L1Tails
