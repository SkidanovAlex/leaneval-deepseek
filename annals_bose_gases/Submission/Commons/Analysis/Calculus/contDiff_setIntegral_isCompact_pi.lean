import Mathlib.Tactic.Have
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Metric Filter Function Set
open scoped Topology ContDiff ENNReal

namespace Commons.Analysis.Calculus

universe u v

/-- The space `Fin d → ℝ³`, i.e. `d` particles in three-dimensional space. -/
abbrev EuclidSpace (d : ℕ) := Fin d → EuclideanSpace ℝ (Fin 3)

section Continuity

/-- The parametric integral of a continuous function over a compact set is continuous. -/
theorem contDiff_zero_setIntegral_isCompact_pi
    {P : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P] (d : ℕ)
    {k : Set (EuclidSpace d)} (hk : IsCompact k)
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : P → EuclidSpace d → E} (hF : ContDiff ℝ 0 (Function.uncurry F)) :
    ContDiff ℝ 0 (fun p => ∫ x in k, F p x) := by
  rw [contDiff_zero]
  rw [continuous_iff_continuousAt]
  intro p₀
  have hcont : Continuous (Function.uncurry F) := contDiff_zero.mp hF
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ, ∀ x ∈ k, ‖Function.uncurry F (p₀, x)‖ ≤ C₁ := by
    obtain ⟨C, hC⟩ := (isCompact_singleton (x := p₀)).prod hk |>.exists_bound_of_continuousOn
      (hcont.continuousOn.mono (subset_univ _))
    exact ⟨C, fun x hx => hC (p₀, x) ⟨rfl, hx⟩⟩
  obtain ⟨C, hCpos, hCbnd⟩ : ∃ C : ℝ, 0 < C ∧ ∀ x ∈ k, ‖Function.uncurry F (p₀, x)‖ < C := by
    refine ⟨max C₁ 0 + 1, by positivity, fun x hx => ?_⟩
    have := hC₁ x hx
    linarith [le_max_left C₁ (0 : ℝ)]
  have hVopen : IsOpen {q : P × EuclidSpace d | ‖Function.uncurry F q‖ < C} :=
    isOpen_lt hcont.norm continuous_const
  have hKV : ({p₀} ×ˢ k : Set (P × EuclidSpace d)) ⊆
      {q | ‖Function.uncurry F q‖ < C} := by
    rintro ⟨p, x⟩ ⟨hp, hx⟩
    rw [mem_singleton_iff] at hp
    subst hp
    exact hCbnd x hx
  obtain ⟨u, v, hu_open, hv_open, hu_sub, hv_sub, huv⟩ :=
    generalized_tube_lemma (isCompact_singleton (x := p₀)) hk hVopen hKV
  have hu_nhds : u ∈ 𝓝 p₀ := hu_open.mem_nhds (hu_sub rfl)
  have hbound : ∀ p ∈ u, ∀ x ∈ k, ‖Function.uncurry F (p, x)‖ ≤ C := by
    intro p hp x hx
    exact (huv ⟨hp, hv_sub hx⟩).le
  have hmain : ContinuousAt (fun p => ∫ x, F p x ∂(volume.restrict k)) p₀ := by
    refine continuousAt_of_dominated (μ := volume.restrict k)
      (F := fun (p : P) (x : EuclidSpace d) => F p x)
      (bound := fun _ => C) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun p =>
        (hcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    · filter_upwards [hu_nhds] with p hp
      exact ae_restrict_of_forall_mem hk.measurableSet fun x hx => hbound p hp x hx
    · exact integrableOn_const hk.measure_ne_top
    · exact Eventually.of_forall fun x =>
        (hcont.comp (continuous_id.prodMk continuous_const)).continuousAt
  exact hmain

end Continuity

section Derivative

/-- Differentiation under the integral sign, over a compact set. -/
theorem hasFDerivAt_setIntegral_isCompact_pi
    {P : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P] (d : ℕ)
    {k : Set (EuclidSpace d)} (hk : IsCompact k)
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : P → EuclidSpace d → E} (hF : ContDiff ℝ 1 (Function.uncurry F)) (p₀ : P) :
    HasFDerivAt (fun p => ∫ x in k, F p x)
      (∫ x in k, (fderiv ℝ (Function.uncurry F) (p₀, x)).comp
        (ContinuousLinearMap.inl ℝ P (EuclidSpace d))) p₀ := by
  have hcont : Continuous (Function.uncurry F) := hF.continuous
  have hdiff : Differentiable ℝ (Function.uncurry F) := hF.differentiable_one
  have hfderivcont : Continuous (fderiv ℝ (Function.uncurry F)) :=
    hF.continuous_fderiv one_ne_zero
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ, ∀ x ∈ k,
      ‖fderiv ℝ (Function.uncurry F) (p₀, x)‖ ≤ C₁ := by
    obtain ⟨C, hC⟩ := (isCompact_singleton (x := p₀)).prod hk |>.exists_bound_of_continuousOn
      (hfderivcont.continuousOn.mono (subset_univ _))
    exact ⟨C, fun x hx => hC (p₀, x) ⟨rfl, hx⟩⟩
  obtain ⟨C, hCpos, hCbnd⟩ : ∃ C : ℝ, 0 < C ∧ ∀ x ∈ k,
      ‖fderiv ℝ (Function.uncurry F) (p₀, x)‖ < C := by
    refine ⟨max C₁ 0 + 1, by positivity, fun x hx => ?_⟩
    have := hC₁ x hx
    linarith [le_max_left C₁ (0 : ℝ)]
  have hVopen : IsOpen {q : P × EuclidSpace d | ‖fderiv ℝ (Function.uncurry F) q‖ < C} :=
    isOpen_lt hfderivcont.norm continuous_const
  have hKV : ({p₀} ×ˢ k : Set (P × EuclidSpace d)) ⊆
      {q | ‖fderiv ℝ (Function.uncurry F) q‖ < C} := by
    rintro ⟨p, x⟩ ⟨hp, hx⟩
    rw [mem_singleton_iff] at hp
    subst hp
    exact hCbnd x hx
  obtain ⟨u, v, hu_open, hv_open, hu_sub, hv_sub, huv⟩ :=
    generalized_tube_lemma (isCompact_singleton (x := p₀)) hk hVopen hKV
  have hu_nhds : u ∈ 𝓝 p₀ := hu_open.mem_nhds (hu_sub rfl)
  have hbound : ∀ p ∈ u, ∀ x ∈ k, ‖fderiv ℝ (Function.uncurry F) (p, x)‖ ≤ C := by
    intro p hp x hx
    exact (huv ⟨hp, hv_sub hx⟩).le
  have hbound' : ∀ x ∈ k, ∀ p ∈ u, ‖(fderiv ℝ (Function.uncurry F) (p, x)).comp
      (ContinuousLinearMap.inl ℝ P (EuclidSpace d))‖ ≤ C := by
    intro x hx p hp
    refine (ContinuousLinearMap.opNorm_comp_le (fderiv ℝ (Function.uncurry F) (p, x))
      (ContinuousLinearMap.inl ℝ P (EuclidSpace d))).trans ?_
    have h1 : ‖ContinuousLinearMap.inl ℝ P (EuclidSpace d)‖ ≤ 1 :=
      ContinuousLinearMap.norm_inl_le_one ℝ P (EuclidSpace d)
    calc ‖fderiv ℝ (Function.uncurry F) (p, x)‖ * ‖ContinuousLinearMap.inl ℝ P (EuclidSpace d)‖
        ≤ ‖fderiv ℝ (Function.uncurry F) (p, x)‖ * 1 := by gcongr
      _ = ‖fderiv ℝ (Function.uncurry F) (p, x)‖ := mul_one _
      _ ≤ C := hbound p hp x hx
  have hFmeas : ∀ᶠ p in 𝓝 p₀,
      AEStronglyMeasurable (fun a : EuclidSpace d => F p a) (volume.restrict k) :=
    Eventually.of_forall fun p =>
      (hcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hΦcont : Continuous (fun a : EuclidSpace d =>
      (fderiv ℝ (Function.uncurry F) (p₀, a)).comp
        (ContinuousLinearMap.inl ℝ P (EuclidSpace d))) := by
    fun_prop
  have hres := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := volume.restrict k)
    (F := fun (p : P) (a : EuclidSpace d) => F p a)
    (F' := fun (p : P) (a : EuclidSpace d) =>
      (fderiv ℝ (Function.uncurry F) (p, a)).comp (ContinuousLinearMap.inl ℝ P (EuclidSpace d)))
    (x₀ := p₀) (bound := fun _ => C) (s := u)
    hu_nhds hFmeas
    ((hcont.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact hk)
    hΦcont.aestronglyMeasurable
    (ae_restrict_of_forall_mem hk.measurableSet fun x hx => hbound' x hx)
    (integrableOn_const hk.measure_ne_top)
    (ae_restrict_of_forall_mem hk.measurableSet fun a _ => fun p _ => by
      have h2 : HasFDerivAt (Function.uncurry F)
          (fderiv ℝ (Function.uncurry F) (p, a)) (p, a) :=
        (hdiff (p, a)).hasFDerivAt
      have h3 : HasFDerivAt (fun p' : P => F p' a)
          ((fderiv ℝ (Function.uncurry F) (p, a)).comp
            (ContinuousLinearMap.inl ℝ P (EuclidSpace d))) p := by
        have h4 : HasFDerivAt ((Function.uncurry F) ∘ (fun p' : P => (p', a)))
            ((fderiv ℝ (Function.uncurry F) (p, a)).comp
              (ContinuousLinearMap.inl ℝ P (EuclidSpace d))) p :=
          HasFDerivAt.comp (f := fun p' : P => (p', a)) (x := p) h2
            (hasFDerivAt_prodMk_left p a)
        have heq : ((Function.uncurry F) ∘ (fun p' : P => (p', a))) = fun p' : P => F p' a := by
          funext p'; rfl
        rwa [heq] at h4
      exact h3)
  simpa using hres

end Derivative

/-- The parametric integral of a `C^n` function over a compact set is `C^n`
(the target space lives in the same universe as the parameter space). -/
theorem contDiff_setIntegral_isCompact_pi_nat
    {P : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P] (d : ℕ)
    {k : Set (EuclidSpace d)} (hk : IsCompact k) :
    ∀ n : ℕ, ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      (F : P → EuclidSpace d → E),
      ContDiff ℝ n (Function.uncurry F) → ContDiff ℝ n (fun p => ∫ x in k, F p x) := by
  intro n
  induction n with
  | zero =>
    intro E _ _ _ F hF
    exact contDiff_zero_setIntegral_isCompact_pi (P := P) d hk hF
  | succ n ih =>
    intro E _ _ _ F hF
    have hcast : ((n + 1 : ℕ) : ℕ∞ω) = ((n : ℕ∞ω) + 1) := by simp
    rw [hcast] at hF
    have hfderiv : ContDiff ℝ (n : ℕ∞ω) (fderiv ℝ (Function.uncurry F)) :=
      hF.fderiv_right le_rfl
    set Φ : P → EuclidSpace d → (P →L[ℝ] E) :=
      Function.curry (fun q : P × EuclidSpace d =>
        (fderiv ℝ (Function.uncurry F) q).comp (ContinuousLinearMap.inl ℝ P (EuclidSpace d)))
      with hΦdef
    have hΦ : ContDiff ℝ (n : ℕ∞ω) (Function.uncurry Φ) := by
      rw [hΦdef, Function.uncurry_curry]
      exact hfderiv.clm_comp (contDiff_const (c := ContinuousLinearMap.inl ℝ P (EuclidSpace d)))
    have hΦint : ContDiff ℝ (n : ℕ∞ω) (fun p => ∫ x in k, Φ p x) :=
      ih (E := P →L[ℝ] E) (F := Φ) hΦ
    have hderiv : ∀ p₀ : P,
        HasFDerivAt (fun p => ∫ x in k, F p x) (∫ x in k, Φ p₀ x) p₀ := by
      intro p₀
      have h1 : ContDiff ℝ 1 (Function.uncurry F) := hF.of_le (by simp)
      have h2 := hasFDerivAt_setIntegral_isCompact_pi (P := P) d hk h1 p₀
      simpa only [hΦdef, Function.curry] using h2
    rw [show ((n + 1 : ℕ) : ℕ∞ω) = ((n : ℕ∞ω) + 1) from by simp]
    rw [contDiff_succ_iff_hasFDerivAt]
    exact ⟨fun p => ∫ x in k, Φ p x, hΦint, hderiv⟩

/-- The parametric integral of a `C^m` function over a compact set is `C^m`. -/
theorem contDiff_setIntegral_isCompact_pi
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] (d : ℕ)
    {F : P → (Fin d → EuclideanSpace ℝ (Fin 3)) → ℝ}
    {k : Set (Fin d → EuclideanSpace ℝ (Fin 3))}
    {m : ℕ∞} (hk : IsCompact k) (hF : ContDiff ℝ m (Function.uncurry F)) :
    ContDiff ℝ m (fun p => ∫ x in k, F p x) := by
  rw [contDiff_iff_forall_nat_le]
  intro n hn
  cases n with
  | zero =>
    have h0 : ContDiff ℝ (↑(0 : ℕ) : ℕ∞ω) (Function.uncurry F) := hF.of_le (by exact_mod_cast hn)
    have h0' : ContDiff ℝ 0 (Function.uncurry F) := by simpa using h0
    exact contDiff_zero_setIntegral_isCompact_pi (P := P) d hk h0'
  | succ j =>
    have hk1 : ContDiff ℝ (((j + 1 : ℕ) : ℕ∞ω)) (Function.uncurry F) := hF.of_le (by exact_mod_cast hn)
    rw [show ((j + 1 : ℕ) : ℕ∞ω) = ((j : ℕ∞ω) + 1) from by simp] at hk1
    have hfderiv : ContDiff ℝ (j : ℕ∞ω) (fderiv ℝ (Function.uncurry F)) :=
      hk1.fderiv_right le_rfl
    set Φ : P → EuclidSpace d → (P →L[ℝ] ℝ) :=
      Function.curry (fun q : P × EuclidSpace d =>
        (fderiv ℝ (Function.uncurry F) q).comp (ContinuousLinearMap.inl ℝ P (EuclidSpace d)))
      with hΦdef
    have hΦ : ContDiff ℝ (j : ℕ∞ω) (Function.uncurry Φ) := by
      rw [hΦdef, Function.uncurry_curry]
      exact hfderiv.clm_comp (contDiff_const (c := ContinuousLinearMap.inl ℝ P (EuclidSpace d)))
    have hΦint : ContDiff ℝ (j : ℕ∞ω) (fun p => ∫ x in k, Φ p x) :=
      contDiff_setIntegral_isCompact_pi_nat (P := P) d hk j (E := P →L[ℝ] ℝ) (F := Φ) hΦ
    have hderiv : ∀ p₀ : P,
        HasFDerivAt (fun p => ∫ x in k, F p x) (∫ x in k, Φ p₀ x) p₀ := by
      intro p₀
      have h1 : ContDiff ℝ 1 (Function.uncurry F) := hk1.of_le (by simp)
      have h2 := hasFDerivAt_setIntegral_isCompact_pi (P := P) d hk h1 p₀
      simpa only [hΦdef, Function.curry] using h2
    rw [show ((j + 1 : ℕ) : ℕ∞ω) = ((j : ℕ∞ω) + 1) from by simp]
    rw [contDiff_succ_iff_hasFDerivAt]
    exact ⟨fun p => ∫ x in k, Φ p x, hΦint, hderiv⟩

end Commons.Analysis.Calculus