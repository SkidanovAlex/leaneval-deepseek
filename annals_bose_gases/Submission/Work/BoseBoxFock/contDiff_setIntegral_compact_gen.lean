import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Commons.Analysis.Calculus.contDiff_setIntegral_isCompact
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Smoothness of a parametric integral over a compact set, generically

We prove that for a jointly `C^n` family `F : P → G → ℂ`, where `G` is an arbitrary real normed
space whose volume measure is finite on compact sets, the function `p ↦ ∫ x in k, F p x` (`k`
compact) is `C^n`.

This is the general-space version of `Commons.Analysis.Calculus.contDiff_setIntegral_isCompact`
(which is the ℝ-valued case on `EuclideanSpace ℝ (Fin 3)`) and of `..._pi`.

The two ingredients are

* the compactness of `k` in `G` (used through the uniform-continuity lemma
  `IsCompact.mem_uniformity_of_prod`, the tube lemma, and
  `ContinuousOn.integrableOn_compact`, which needs no second countability of the target),
* the dominated-differentiation theorem `hasFDerivAt_integral_of_dominated_of_fderiv_le`.

The `ℂ`-valuation is handled by the induction recorded in the corpus for a general value space, run
at the value spaces `P →L[ℝ] (⋯ →L[ℝ] ℂ)` (which all live in the universe of `P`), with `ℂ` as the
base case.
-/

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Metric Filter Function Set
open scoped Topology ContDiff ENNReal

namespace Work.BoseBoxFock

universe u v

/-- `BorelSpace` implies `OpensMeasurableSpace`: if the measurable space *is* the Borel one, then
every Borel set is measurable.  (Mathlib does not register this direction as an instance, since
the opposite direction is available under a second-countability assumption.) -/
local instance instOpensMeasurableSpaceOfBorelSpace {α : Type*} [TopologicalSpace α]
    [MeasurableSpace α] [BorelSpace α] : OpensMeasurableSpace α :=
  ⟨by rw [← BorelSpace.measurable_eq]⟩

section Main

variable {P : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
variable {G : Type v} [NormedAddCommGroup G] [NormedSpace ℝ G] [MeasureSpace G] [BorelSpace G]
variable [IsFiniteMeasureOnCompacts (volume : Measure G)]

/-- A function which is continuous on a compact set is integrable there, for the Lebesgue measure
of a space whose measure is finite on compacts.  (No second countability assumption on the value
space is needed.) -/
lemma integrable_restrict_of_continuousOn {V : Type*} [NormedAddCommGroup V] {k : Set G}
    (hk : IsCompact k) {f : G → V} (hf : ContinuousOn f k) :
    Integrable f ((volume : Measure G).restrict k) :=
  ContinuousOn.integrableOn_compact (μ := (volume : Measure G)) hk hf

/-- **Continuity of a parametric integral over a compact set** (arbitrary value space). -/
lemma continuousAt_setIntegral_compact_gen {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {k : Set G} (hk : IsCompact k) {F : P → G → V} (hF : Continuous (Function.uncurry F))
    (p₀ : P) : ContinuousAt (fun p => ∫ x in k, F p x) p₀ := by
  rw [Metric.continuousAt_iff']
  intro ε hε
  have hCnn : 0 ≤ (volume : Measure G).real k := ENNReal.toReal_nonneg
  obtain ⟨ε', hε'pos, hε'le⟩ :
      ∃ ε' : ℝ, 0 < ε' ∧ ε' * (volume : Measure G).real k < ε := by
    have hden : 0 < 2 * ((volume : Measure G).real k + 1) := by linarith
    refine ⟨ε / (2 * ((volume : Measure G).real k + 1)), div_pos hε hden, ?_⟩
    rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
    nlinarith
  obtain ⟨v, hv_nhds, hv⟩ : ∃ v ∈ 𝓝 p₀, ∀ q ∈ v, ∀ x ∈ k, dist (F q x) (F p₀ x) < ε' := by
    have hu : {z : V × V | dist z.1 z.2 < ε'} ∈ uniformity V :=
      Metric.dist_mem_uniformity hε'pos
    obtain ⟨v, hv, hv'⟩ := hk.mem_uniformity_of_prod (s := Set.univ) (q := p₀)
      (f := fun (q : P) (x : G) => F q x) (u := {z : V × V | dist z.1 z.2 < ε'})
      hF.continuousOn (Set.mem_univ p₀) hu
    exact ⟨v, by simpa using hv, fun q hq x hx => by simpa using hv' q hq x hx⟩
  filter_upwards [hv_nhds] with q hq
  have hint : ∀ p : P, Integrable (fun x : G => F p x) ((volume : Measure G).restrict k) := fun p =>
    integrable_restrict_of_continuousOn hk
      ((hF.comp (continuous_const.prodMk continuous_id)).continuousOn)
  have hsub : (∫ x in k, (F q x - F p₀ x))
      = (∫ x in k, F q x) - (∫ x in k, F p₀ x) := integral_sub (hint q) (hint p₀)
  rw [dist_eq_norm, ← hsub]
  calc ‖∫ x in k, (F q x - F p₀ x)‖ ≤ ε' * (volume : Measure G).real k :=
        norm_setIntegral_le_of_norm_le_const hk.measure_lt_top fun x hx => by
          have h := hv q hq x hx
          rw [dist_eq_norm] at h
          exact h.le
    _ < ε := hε'le
/-- **Differentiation under the integral sign** over a compact set, in the "composed" form of the
derivative (the `fderiv` of the uncurried family composed with the inclusion of the parameter
space).  This is the form required by Mathlib's parametric-integral theorem. -/
lemma hasFDerivAt_setIntegral_compact_gen_aux {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {k : Set G} (hk : IsCompact k) {F : P → G → V}
    (hF : ContDiff ℝ 1 (Function.uncurry F)) (p₀ : P) :
    HasFDerivAt (fun p => ∫ x in k, F p x)
      (∫ x in k, (fderiv ℝ (Function.uncurry F) (p₀, x)).comp
        (ContinuousLinearMap.inl ℝ P G)) p₀ := by
  have hcont : Continuous (Function.uncurry F) := hF.continuous
  have hdiff : Differentiable ℝ (Function.uncurry F) := hF.differentiable_one
  have hfdcont : Continuous (fderiv ℝ (Function.uncurry F)) :=
    hF.continuous_fderiv one_ne_zero
  obtain ⟨C, hCpos, hCbnd⟩ :
      ∃ C : ℝ, 0 < C ∧ ∀ x ∈ k, ‖fderiv ℝ (Function.uncurry F) (p₀, x)‖ < C := by
    obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ, ∀ x ∈ k, ‖fderiv ℝ (Function.uncurry F) (p₀, x)‖ ≤ C₁ := by
      obtain ⟨C, hC⟩ := (isCompact_singleton (x := p₀)).prod hk |>.exists_bound_of_continuousOn
        (hfdcont.continuousOn.mono (subset_univ _))
      exact ⟨C, fun x hx => hC (p₀, x) ⟨rfl, hx⟩⟩
    exact ⟨max C₁ 0 + 1, by positivity, fun x hx => by
      have := hC₁ x hx
      linarith [le_max_left C₁ (0 : ℝ)]⟩
  have hVopen : IsOpen {q : P × G | ‖fderiv ℝ (Function.uncurry F) q‖ < C} :=
    isOpen_lt hfdcont.norm continuous_const
  have hKV : ({p₀} ×ˢ k : Set (P × G)) ⊆ {q | ‖fderiv ℝ (Function.uncurry F) q‖ < C} := by
    rintro ⟨p, x⟩ ⟨hp, hx⟩
    rw [mem_singleton_iff] at hp
    subst hp
    exact hCbnd x hx
  obtain ⟨u, v, hu_open, hv_open, hu_sub, hv_sub, huv⟩ :=
    generalized_tube_lemma (isCompact_singleton (x := p₀)) hk hVopen hKV
  have hu_nhds : u ∈ 𝓝 p₀ := hu_open.mem_nhds (hu_sub rfl)
  have hbound : ∀ p ∈ u, ∀ x ∈ k, ‖fderiv ℝ (Function.uncurry F) (p, x)‖ ≤ C :=
    fun p hp x hx => (huv ⟨hp, hv_sub hx⟩).le
  have hFmeas : ∀ᶠ p in 𝓝 p₀,
      AEStronglyMeasurable (fun a : G => F p a) ((volume : Measure G).restrict k) :=
    Eventually.of_forall fun p =>
      (integrable_restrict_of_continuousOn hk
        ((hcont.comp (continuous_const.prodMk continuous_id)).continuousOn)).aestronglyMeasurable
  have hfdcont' : Continuous fun a : G =>
      (fderiv ℝ (Function.uncurry F) (p₀, a)).comp (ContinuousLinearMap.inl ℝ P G) :=
    (hfdcont.comp (continuous_const.prodMk continuous_id)).clm_comp
      (continuous_const : Continuous fun _ : G => ContinuousLinearMap.inl ℝ P G)
  have hF'int : Integrable (fun a : G =>
      (fderiv ℝ (Function.uncurry F) (p₀, a)).comp (ContinuousLinearMap.inl ℝ P G))
      ((volume : Measure G).restrict k) :=
    integrable_restrict_of_continuousOn hk hfdcont'.continuousOn
  have hres := hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ)
    (μ := (volume : Measure G).restrict k)
    (F := fun (p : P) (a : G) => F p a)
    (F' := fun (p : P) (a : G) =>
      (fderiv ℝ (Function.uncurry F) (p, a)).comp (ContinuousLinearMap.inl ℝ P G))
    (x₀ := p₀) (s := u) (bound := fun _ => C)
    hu_nhds hFmeas
    (integrable_restrict_of_continuousOn hk
      ((hcont.comp (continuous_const.prodMk continuous_id)).continuousOn))
    hF'int.aestronglyMeasurable
    (ae_restrict_of_forall_mem hk.measurableSet fun a ha p hp => by
      have h2 : ‖ContinuousLinearMap.inl ℝ P G‖ ≤ 1 :=
        ContinuousLinearMap.norm_inl_le_one ℝ P G
      have h3 : ‖fderiv ℝ (Function.uncurry F) (p, a)‖ * ‖ContinuousLinearMap.inl ℝ P G‖ ≤ C := by
        calc ‖fderiv ℝ (Function.uncurry F) (p, a)‖ * ‖ContinuousLinearMap.inl ℝ P G‖
            ≤ ‖fderiv ℝ (Function.uncurry F) (p, a)‖ * 1 :=
              mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
          _ = ‖fderiv ℝ (Function.uncurry F) (p, a)‖ := mul_one _
          _ ≤ C := hbound p hp a ha
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans h3)
    (integrableOn_const hk.measure_ne_top)
    (ae_restrict_of_forall_mem hk.measurableSet fun a _ p _ => by
      have h2 : HasFDerivAt (Function.uncurry F) (fderiv ℝ (Function.uncurry F) (p, a)) (p, a) :=
        (hdiff (p, a)).hasFDerivAt
      have h3 := h2.comp (f := fun e : P => (e, a)) (x := p) (hasFDerivAt_prodMk_left p a)
      rw [show ((Function.uncurry F) ∘ fun q : P => (q, a)) = fun q : P => F q a from rfl] at h3
      exact h3)
  simpa using hres

/-- **Differentiation under the integral sign** over a compact set. -/
lemma hasFDerivAt_setIntegral_compact_gen {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {k : Set G} (hk : IsCompact k) {F : P → G → V}
    (hF : ContDiff ℝ 1 (Function.uncurry F)) (p₀ : P) :
    HasFDerivAt (fun p => ∫ x in k, F p x)
      (∫ x in k, fderiv ℝ (fun q : P => F q x) p₀) p₀ := by
  have hpt : (fun x : G => fderiv ℝ (fun q : P => F q x) p₀)
      = fun x : G => (fderiv ℝ (Function.uncurry F) (p₀, x)).comp
          (ContinuousLinearMap.inl ℝ P G) := by
    funext x
    have h2 : HasFDerivAt (Function.uncurry F) (fderiv ℝ (Function.uncurry F) (p₀, x))
        (p₀, x) := (hF.differentiable_one (p₀, x)).hasFDerivAt
    have h3 := h2.comp (f := fun e : P => (e, x)) (x := p₀) (hasFDerivAt_prodMk_left p₀ x)
    rw [show ((Function.uncurry F) ∘ fun q : P => (q, x)) = fun q : P => F q x from rfl] at h3
    exact h3.fderiv
  have hmain := hasFDerivAt_setIntegral_compact_gen_aux (P := P) (G := G) hk hF p₀
  rw [← hpt] at hmain
  exact hmain

/-- **The induction.**  For every natural `m` and every value space `V` (in the universe of the
parameter space `P`), the parametric integral over a compact set of a jointly `C^m` family
`F : P → G → V` is `C^m`. -/
theorem contDiff_setIntegral_compact_aux {k : Set G} (hk : IsCompact k) :
    ∀ (m : ℕ) (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
      (F : P → G → V),
      ContDiff ℝ (m : ℕ∞) (Function.uncurry F) →
      ContDiff ℝ (m : ℕ∞) (fun p => ∫ x in k, F p x) := by
  intro m
  induction m with
  | zero =>
    intro V _ _ _ F hF
    have hcont : Continuous (Function.uncurry F) := contDiff_zero.mp hF
    exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr fun p₀ =>
      continuousAt_setIntegral_compact_gen hk hcont p₀)
  | succ m ih =>
    intro V _ _ _ F hF
    have hF' : ContDiff ℝ ((m : ℕ∞) + 1) (Function.uncurry F) := hF
    have hj : ContDiff ℝ (m : ℕ∞)
        (Function.uncurry fun (p : P) (x : G) => fderiv ℝ (fun q : P => F q x) p) :=
      Commons.Analysis.Calculus.contDiff_uncurry_partialFDeriv (X := G) hF'
    have hint : ContDiff ℝ (m : ℕ∞)
        (fun p => ∫ x in k, fderiv ℝ (fun q : P => F q x) p) :=
      ih (P →L[ℝ] V) (fun p x => fderiv ℝ (fun q : P => F q x) p) hj
    have hderiv : ∀ p₀ : P, HasFDerivAt (fun p => ∫ x in k, F p x)
        (∫ x in k, fderiv ℝ (fun q : P => F q x) p₀) p₀ :=
      fun p₀ => hasFDerivAt_setIntegral_compact_gen hk (hF'.of_le (by simp)) p₀
    exact (contDiff_succ_iff_hasFDerivAt (n := m)).mpr
      ⟨fun p => ∫ x in k, fderiv ℝ (fun q : P => F q x) p, hint, hderiv⟩

/-- **The induction at the value space `ℂ`.**  The parametric integral over a compact set of a
jointly `C^m` `ℂ`-valued family is `C^m`. -/
theorem contDiff_setIntegral_compact_cplx {k : Set G} (hk : IsCompact k) :
    ∀ m : ℕ, ∀ {F : P → G → ℂ},
      ContDiff ℝ (m : ℕ∞) (Function.uncurry F) →
      ContDiff ℝ (m : ℕ∞) (fun p => ∫ x in k, F p x) := by
  intro m
  induction m with
  | zero =>
    intro F hF
    have hcont : Continuous (Function.uncurry F) := contDiff_zero.mp hF
    exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr fun p₀ =>
      continuousAt_setIntegral_compact_gen hk hcont p₀)
  | succ m ih =>
    intro F hF
    have hF' : ContDiff ℝ ((m : ℕ∞) + 1) (Function.uncurry F) := hF
    have hj : ContDiff ℝ (m : ℕ∞)
        (Function.uncurry fun (p : P) (x : G) => fderiv ℝ (fun q : P => F q x) p) :=
      Commons.Analysis.Calculus.contDiff_uncurry_partialFDeriv (X := G) hF'
    have hint : ContDiff ℝ (m : ℕ∞)
        (fun p => ∫ x in k, fderiv ℝ (fun q : P => F q x) p) :=
      contDiff_setIntegral_compact_aux (P := P) (G := G) hk m (P →L[ℝ] ℂ)
        (fun p x => fderiv ℝ (fun q : P => F q x) p) hj
    exact (contDiff_succ_iff_hasFDerivAt (n := m)).mpr
      ⟨fun p => ∫ x in k, fderiv ℝ (fun q : P => F q x) p, hint,
        fun p₀ => hasFDerivAt_setIntegral_compact_gen hk (hF'.of_le (by simp)) p₀⟩

end Main

/-- The parametric integral `p ↦ ∫ x in k, F p x` over a compact set `k` is `C^n` for jointly
`C^n` `F`, in an arbitrary real normed integration space `G` with volume finite on compacts and
`ℂ`-valued integrand.  Corpus models to transcribe (their proofs are generic in the integration
space): `Commons.Analysis.Calculus.contDiff_setIntegral_isCompact` and `..._pi`; the `ℂ`-valuation
is obtained from the ℝ-valued case via `Complex.reCLM`/`Complex.imCLM` +
`ContinuousLinearMap.integral_comp_comm` + `Complex.ext`. -/
theorem contDiff_setIntegral_compact_gen
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [MeasureTheory.MeasureSpace G]
    [BorelSpace G]
    [MeasureTheory.IsFiniteMeasureOnCompacts (MeasureTheory.volume : MeasureTheory.Measure G)]
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {k : Set G} (hk : IsCompact k) {n : ℕ∞}
    {F : P → G → ℂ} (hF : ContDiff ℝ n (Function.uncurry F)) :
    ContDiff ℝ n (fun p => ∫ x in k, F p x) := by
  by_cases hn : n = ⊤
  · subst hn
    rw [contDiff_infty]
    intro m
    exact contDiff_setIntegral_compact_cplx (P := P) (G := G) hk m (contDiff_infty.mp hF m)
  · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hn
    subst hm
    exact contDiff_setIntegral_compact_cplx (P := P) (G := G) hk m hF

end Work.BoseBoxFock
