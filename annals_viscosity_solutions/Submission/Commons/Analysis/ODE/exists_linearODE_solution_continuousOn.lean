import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Topology.Compactness.CompactlyGeneratedSpace

noncomputable section
open Set Filter Metric intervalIntegral Function MeasureTheory
open scoped Topology NNReal

namespace Commons.Analysis.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Existence for a time-dependent ODE with a field that is continuous in `(t, x)` and
(globally) Lipschitz in `x`.**  This is the non-autonomous version of
`Commons.Analysis.ODE.exists_global_solution_of_lipschitz`.

The existence is proved by a Picard iteration: the map
`Φ y t = x₀ + ∫_{t₀}^{t} f s (y s) ds` on the complete space `C([a,b], E)` (with the sup metric)
satisfies
`dist (Φ^[n] y) (Φ^[n] z) ≤ (K (b-a))^n / n! * dist y z`,
so some iterate of `Φ` is a contraction; its fixed point is the required solution. -/
theorem exists_solution_Icc_of_continuousOn_of_lipschitzWith
    [CompleteSpace E]
    {f : ℝ → E → E} {a b : ℝ} (hab : a ≤ b) {K : ℝ≥0} {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Icc a b) (x₀ : E)
    (hcont : ContinuousOn (Function.uncurry f) (Set.Icc a b ×ˢ Set.univ))
    (hlip : ∀ t ∈ Set.Icc a b, LipschitzWith K (f t)) :
    ∃ y : ℝ → E, y t₀ = x₀ ∧ ContinuousOn y (Set.Icc a b) ∧
      (∀ t ∈ Set.Ioo a b, HasDerivAt y (f t (y t)) t) ∧
      (∀ t ∈ Set.Icc a b, y t = x₀ + ∫ s in t₀..t, f s (y s)) := by
  classical
  have hP : Continuous (projIcc a b hab) := continuous_projIcc
  have hcG : ∀ y : C(Set.Icc a b, E),
      Continuous (fun τ : ℝ => f (projIcc a b hab τ) (y (projIcc a b hab τ))) := by
    intro y
    have hφ : Continuous (fun τ : ℝ => (((projIcc a b hab τ : Set.Icc a b) : ℝ),
        y (projIcc a b hab τ))) :=
      (continuous_subtype_val.comp hP).prodMk (y.continuous.comp hP)
    have h := hcont.comp_continuous hφ (fun τ => ⟨(projIcc a b hab τ).2, trivial⟩)
    simpa only [Function.comp_def, Function.uncurry_apply_pair] using h
  let Φ : C(Set.Icc a b, E) → C(Set.Icc a b, E) := fun y =>
    { toFun := fun σ => x₀ + ∫ τ in t₀..(σ:ℝ), f (projIcc a b hab τ) (y (projIcc a b hab τ))
      continuous_toFun :=
        (continuous_const.add (differentiable_integral_of_continuous (hcG y)).continuous).comp
          continuous_subtype_val }
  have hΦ_apply : ∀ (y : C(Set.Icc a b, E)) (σ : Set.Icc a b),
      Φ y σ = x₀ + ∫ τ in t₀..(σ:ℝ), f (projIcc a b hab τ) (y (projIcc a b hab τ)) := fun _ _ => rfl
  have key : ∀ (n : ℕ) (y z : C(Set.Icc a b, E)) (σ : Set.Icc a b),
      dist ((Φ^[n]) y σ) ((Φ^[n]) z σ) ≤ (K * |(σ:ℝ) - t₀|)^n / n.factorial * dist y z := by
    intro n
    induction n with
    | zero =>
        intro y z σ
        simpa using ContinuousMap.dist_apply_le_dist (f := y) (g := z) σ
    | succ n hn =>
        intro y z σ
        simp only [Function.iterate_succ_apply']
        set D : ℝ := dist y z with hD
        have hkey : ∀ σ : Set.Icc a b,
            dist ((Φ^[n]) y σ) ((Φ^[n]) z σ) ≤ (K * |(σ:ℝ) - t₀|)^n / n.factorial * D :=
          fun σ => hn y z σ
        have hYc : Continuous (fun τ : ℝ => f (projIcc a b hab τ) ((Φ^[n]) y (projIcc a b hab τ))) :=
          hcG ((Φ^[n]) y)
        have hZc : Continuous (fun τ : ℝ => f (projIcc a b hab τ) ((Φ^[n]) z (projIcc a b hab τ))) :=
          hcG ((Φ^[n]) z)
        have hmain : dist (Φ ((Φ^[n]) y) σ) (Φ ((Φ^[n]) z) σ) =
            ‖∫ τ in t₀..(σ:ℝ), (f (projIcc a b hab τ) ((Φ^[n]) y (projIcc a b hab τ))
              - f (projIcc a b hab τ) ((Φ^[n]) z (projIcc a b hab τ)))‖ := by
          rw [dist_eq_norm, hΦ_apply, hΦ_apply,
            integral_sub (hYc.intervalIntegrable _ _) (hZc.intervalIntegrable _ _)]
          rw [add_sub_add_left_eq_sub]
        have hgc : Continuous (fun τ : ℝ => ((K:ℝ)^(n+1) / n.factorial * D) * |τ - t₀|^n) := by
          fun_prop
        have hae : ∀ᵐ τ ∂(volume.restrict (uIoc t₀ (σ:ℝ))),
            ‖f (projIcc a b hab τ) ((Φ^[n]) y (projIcc a b hab τ))
              - f (projIcc a b hab τ) ((Φ^[n]) z (projIcc a b hab τ))‖
              ≤ ((K:ℝ)^(n+1) / n.factorial * D) * |τ - t₀|^n := by
          refine (MeasureTheory.ae_restrict_mem measurableSet_uIoc).mono (fun τ hτ => ?_)
          have hτIcc : τ ∈ Set.Icc a b := uIcc_subset_Icc ht₀ σ.2 (uIoc_subset_uIcc hτ)
          have hPτ : (projIcc a b hab τ : ℝ) = τ := by rw [projIcc_of_mem hab hτIcc]
          have hlip' := ((hlip (projIcc a b hab τ) (projIcc a b hab τ).2).dist_le_mul
            ((Φ^[n]) y (projIcc a b hab τ)) ((Φ^[n]) z (projIcc a b hab τ)))
          rw [dist_eq_norm] at hlip'
          calc ‖f (projIcc a b hab τ) ((Φ^[n]) y (projIcc a b hab τ)) - f (projIcc a b hab τ) ((Φ^[n]) z (projIcc a b hab τ))‖
              ≤ (K:ℝ) * dist ((Φ^[n]) y (projIcc a b hab τ)) ((Φ^[n]) z (projIcc a b hab τ)) := hlip'
            _ ≤ (K:ℝ) * ((K * |(projIcc a b hab τ : ℝ) - t₀|)^n / n.factorial * D) := by
                apply mul_le_mul_of_nonneg_left _ (NNReal.coe_nonneg K)
                exact hkey (projIcc a b hab τ)
            _ = ((K:ℝ)^(n+1) / n.factorial * D) * |τ - t₀|^n := by
                rw [hPτ, mul_pow]; ring
        rw [hmain, norm_intervalIntegral_eq]
        calc ‖∫ τ in uIoc t₀ (σ:ℝ), (f (projIcc a b hab τ) ((Φ^[n]) y (projIcc a b hab τ))
              - f (projIcc a b hab τ) ((Φ^[n]) z (projIcc a b hab τ)))‖
            ≤ ∫ τ in uIoc t₀ (σ:ℝ), ((K:ℝ)^(n+1) / n.factorial * D) * |τ - t₀|^n :=
              MeasureTheory.norm_integral_le_of_norm_le
                (g := fun τ : ℝ => ((K:ℝ)^(n+1) / n.factorial * D) * |τ - t₀|^n)
                (show Integrable (fun τ : ℝ => ((K:ℝ)^(n+1) / n.factorial * D) * |τ - t₀|^n)
                  (volume.restrict (uIoc t₀ (σ:ℝ))) from hgc.integrableOn_uIoc) hae
          _ = ((K:ℝ)^(n+1) / n.factorial * D) * ∫ τ in uIoc t₀ (σ:ℝ), |τ - t₀|^n := by
              rw [MeasureTheory.integral_const_mul]
          _ = ((K:ℝ)^(n+1) / n.factorial * D) * (|(σ:ℝ) - t₀|^(n+1) / (n+1)) := by
              rw [integral_pow_abs_sub_uIoc]
          _ = (K * |(σ:ℝ) - t₀|)^(n+1) / (n+1).factorial * D := by
              rw [Nat.factorial_succ, mul_pow]
              push_cast
              field_simp
  have key2 : ∀ (n : ℕ) (y z : C(Set.Icc a b, E)),
      dist ((Φ^[n]) y) ((Φ^[n]) z) ≤ (K * (b - a))^n / n.factorial * dist y z := by
    intro n y z
    rw [ContinuousMap.dist_le]
    · intro σ
      refine le_trans (key n y z σ) ?_
      have h1 : |(σ:ℝ) - t₀| ≤ b - a := by
        rw [abs_sub_le_iff]
        exact ⟨by linarith [σ.2.2, ht₀.1], by linarith [ht₀.2, σ.2.1]⟩
      have h2 : (0:ℝ) ≤ (K:ℝ) := NNReal.coe_nonneg K
      gcongr
    · have h1 : (0:ℝ) ≤ (K:ℝ) := NNReal.coe_nonneg K
      have h2 : (0:ℝ) ≤ b - a := by linarith
      positivity
  obtain ⟨n, hn⟩ := ((FloorSemiring.tendsto_pow_div_factorial_atTop (K * (b - a))).eventually
      (gt_mem_nhds zero_lt_one)).exists
  have hnonneg : (0:ℝ) ≤ (K * (b - a))^n / n.factorial := by positivity
  have hcontract : ContractingWith ⟨(K * (b - a))^n / n.factorial, hnonneg⟩ (Φ^[n]) := by
    refine ⟨hn, LipschitzWith.of_dist_le_mul (fun y z => ?_)⟩
    exact key2 n y z
  let Y : C(Set.Icc a b, E) := ContractingWith.fixedPoint (Φ^[n]) hcontract
  have hYeq : ∀ σ : Set.Icc a b,
      Y σ = x₀ + ∫ τ in t₀..(σ:ℝ), f (projIcc a b hab τ) (Y (projIcc a b hab τ)) := by
    intro σ
    have hfix : Φ Y = Y := ContractingWith.isFixedPt_fixedPoint_iterate (f := Φ) hcontract
    have h : Φ Y σ = Y σ := congrArg (fun w : C(Set.Icc a b, E) => w σ) hfix
    exact h.symm.trans (hΦ_apply Y σ)
  let y : ℝ → E := fun t => Y (projIcc a b hab t)
  have hy_eq_V : ∀ u ∈ Set.Icc a b,
      y u = x₀ + ∫ τ in t₀..u, f (projIcc a b hab τ) (Y (projIcc a b hab τ)) := by
    intro u hu
    have h := hYeq ⟨u, hu⟩
    change Y (projIcc a b hab u) = x₀ + ∫ τ in t₀..u, f (projIcc a b hab τ) (Y (projIcc a b hab τ))
    rw [projIcc_of_mem hab hu]
    exact h
  refine ⟨y, ?_, ?_, ?_, ?_⟩
  · show Y (projIcc a b hab t₀) = x₀
    rw [projIcc_of_mem hab ht₀]
    rw [hYeq ⟨t₀, ht₀⟩]
    simp
  · exact (Y.continuous.comp continuous_projIcc).continuousOn
  · intro t ht
    have hPt : (projIcc a b hab t : ℝ) = t := by
      rw [projIcc_of_mem hab ⟨le_of_lt ht.1, le_of_lt ht.2⟩]
    have hV : HasDerivAt (fun u : ℝ => x₀ + ∫ τ in t₀..u,
        f (projIcc a b hab τ) (Y (projIcc a b hab τ))) (f t (y t)) t := by
      have h := (intervalIntegral.integral_hasDerivAt_right ((hcG Y).intervalIntegrable t₀ t)
        ((hcG Y).stronglyMeasurableAtFilter volume (𝓝 t)) ((hcG Y).continuousAt)).const_add x₀
      refine h.congr_deriv ?_
      rw [hPt]
    have hev : y =ᶠ[𝓝 t] (fun u : ℝ => x₀ + ∫ τ in t₀..u,
        f (projIcc a b hab τ) (Y (projIcc a b hab τ))) := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
      exact hy_eq_V u (Ioo_subset_Icc_self hu)
    exact hV.congr_of_eventuallyEq hev
  · intro t ht
    have h := hy_eq_V t ht
    rw [h]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    have hsIcc : s ∈ Set.Icc a b := uIcc_subset_Icc ht₀ ht hs
    simp only [y]
    rw [projIcc_of_mem hab hsIcc]


section Helpers

/-- **One-sided differentiability at the left endpoint.**  If `w` is continuous on `[a,b]`,
differentiable on `(a,b)` with derivative `g`, and `g` is continuous at `a` from the right, then `w`
has right derivative `g a` at `a`. -/
theorem hasDerivWithinAt_Ici_of_continuousOn_of_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {w g : ℝ → E} {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn w (Set.Icc a b))
    (hderiv : ∀ t ∈ Set.Ioo a b, HasDerivAt w (g t) t)
    (hg : ContinuousWithinAt g (Set.Ioo a b) a) :
    HasDerivWithinAt w (g a) (Set.Ici a) a := by
  have hs : Set.Ioo a b ∈ 𝓝[>] a := Ioo_mem_nhdsGT hab
  have hiff : 𝓝[Set.Ioi a] a = 𝓝[Set.Ioo a b] a := by
    refine nhdsWithin_eq_nhdsWithin' (s := Set.Iio b) (Iio_mem_nhds hab) ?_
    ext x; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Iio, Set.mem_Ioo]; tauto
  have hdiff : DifferentiableOn ℝ w (Set.Ioo a b) :=
    fun t ht => (hderiv t ht).differentiableAt.differentiableWithinAt
  have hlim : ContinuousWithinAt w (Set.Ioo a b) a :=
    (hcont a ⟨le_rfl, le_of_lt hab⟩).mono Set.Ioo_subset_Icc_self
  have hg' : Tendsto g (𝓝[>] a) (𝓝 (g a)) := by rw [hiff]; exact hg
  have hd : Tendsto (deriv w) (𝓝[>] a) (𝓝 (g a)) := by
    have hev : deriv w =ᶠ[𝓝[>] a] g := by
      filter_upwards [hs] with t ht
      exact (hderiv t ht).deriv
    exact Tendsto.congr' hev.symm hg'
  exact hasDerivWithinAt_Ici_of_tendsto_deriv hdiff hlim hs hd

/-- **One-sided differentiability at the right endpoint.**  If `w` is continuous on `[a,b]`,
differentiable on `(a,b)` with derivative `g`, and `g` is continuous at `b` from the left, then `w`
has left derivative `g b` at `b`. -/
theorem hasDerivWithinAt_Iic_of_continuousOn_of_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {w g : ℝ → E} {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn w (Set.Icc a b))
    (hderiv : ∀ t ∈ Set.Ioo a b, HasDerivAt w (g t) t)
    (hg : ContinuousWithinAt g (Set.Ioo a b) b) :
    HasDerivWithinAt w (g b) (Set.Iic b) b := by
  have hs : Set.Ioo a b ∈ 𝓝[<] b := Ioo_mem_nhdsLT hab
  have hiff : 𝓝[Set.Iio b] b = 𝓝[Set.Ioo a b] b := by
    refine nhdsWithin_eq_nhdsWithin' (s := Set.Ioi a) (Ioi_mem_nhds hab) ?_
    ext x; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Iio, Set.mem_Ioo]; tauto
  have hdiff : DifferentiableOn ℝ w (Set.Ioo a b) :=
    fun t ht => (hderiv t ht).differentiableAt.differentiableWithinAt
  have hlim : ContinuousWithinAt w (Set.Ioo a b) b :=
    (hcont b ⟨le_of_lt hab, le_rfl⟩).mono Set.Ioo_subset_Icc_self
  have hg' : Tendsto g (𝓝[<] b) (𝓝 (g b)) := by rw [hiff]; exact hg
  have hd : Tendsto (deriv w) (𝓝[<] b) (𝓝 (g b)) := by
    have hev : deriv w =ᶠ[𝓝[<] b] g := by
      filter_upwards [hs] with t ht
      exact (hderiv t ht).deriv
    exact Tendsto.congr' hev.symm hg'
  exact hasDerivWithinAt_Iic_of_tendsto_deriv hdiff hlim hs hd

end Helpers

section Main

/-- A solution of `y' = A t (y t)`, continuous on `[a,b]` and differentiable on `(a,b)`, has a
right derivative at every `t ∈ [t₀, b)`. -/
theorem hasDerivWithinAt_Ici_of_mem_Ico
    {A : ℝ → E →L[ℝ] E} {a b t₀ : ℝ} (hab : a < b) (ht₀ : t₀ ∈ Set.Icc a b)
    {z : ℝ → E} (hzcont : ContinuousOn z (Set.Icc a b))
    (hzderiv : ∀ t ∈ Set.Ioo a b, HasDerivAt z (A t (z t)) t)
    (hAz : ContinuousOn (fun x => A x (z x)) (Set.Icc a b))
    {t : ℝ} (ht : t ∈ Set.Ico t₀ b) :
    HasDerivWithinAt z (A t (z t)) (Set.Ici t) t := by
  rcases eq_or_lt_of_le ht.1 with heq | hlt
  · rw [← heq]
    rcases lt_or_eq_of_le ht₀.1 with hlt' | heq'
    · exact (hzderiv t₀ ⟨hlt', lt_of_eq_of_lt heq ht.2⟩).hasDerivWithinAt
    · rw [← heq']
      exact hasDerivWithinAt_Ici_of_continuousOn_of_hasDerivAt hab hzcont hzderiv
        ((hAz.continuousWithinAt ⟨le_rfl, le_of_lt hab⟩).mono Set.Ioo_subset_Icc_self)
  · exact (hzderiv t ⟨lt_of_le_of_lt ht₀.1 hlt, ht.2⟩).hasDerivWithinAt

/-- A solution of `y' = A t (y t)`, continuous on `[a,b]` and differentiable on `(a,b)`, has a
left derivative at every `t ∈ (a, t₀]`. -/
theorem hasDerivWithinAt_Iic_of_mem_Ioc
    {A : ℝ → E →L[ℝ] E} {a b t₀ : ℝ} (hab : a < b) (ht₀ : t₀ ∈ Set.Icc a b)
    {z : ℝ → E} (hzcont : ContinuousOn z (Set.Icc a b))
    (hzderiv : ∀ t ∈ Set.Ioo a b, HasDerivAt z (A t (z t)) t)
    (hAz : ContinuousOn (fun x => A x (z x)) (Set.Icc a b))
    {t : ℝ} (ht : t ∈ Set.Ioc a t₀) :
    HasDerivWithinAt z (A t (z t)) (Set.Iic t) t := by
  rcases lt_or_eq_of_le ht.2 with hlt | heq
  · exact (hzderiv t ⟨ht.1, lt_of_lt_of_le hlt ht₀.2⟩).hasDerivWithinAt
  · rw [heq]
    rcases lt_or_eq_of_le ht₀.2 with hlt' | heq'
    · exact (hzderiv t₀ ⟨lt_of_lt_of_le ht.1 (le_of_eq heq), hlt'⟩).hasDerivWithinAt
    · rw [heq']
      exact hasDerivWithinAt_Iic_of_continuousOn_of_hasDerivAt hab hzcont hzderiv
        ((hAz.continuousWithinAt ⟨le_of_lt hab, le_rfl⟩).mono Set.Ioo_subset_Icc_self)

/-- **Existence and uniqueness for the linear ODE `y' = A t (y t)`, corrected form.**

The requested lemma `Commons.Analysis.ODE.exists_linearODE_solution` is *false* as stated: the
conclusion `Set.EqOn z y (Set.Icc a b)` cannot hold because a solution is only constrained on the
*open* interval `Set.Ioo a b`, so its endpoint values are free (e.g. change the value of `y` at
`b`; differentiability on `(a,b)` gives continuity only on `(a,b)`, not at the endpoints).  The
correct hypothesis, matching the intended mathematical statement, is continuity of the solutions
on the closed interval `[a, b]`.

With that added, existence follows by clamping `A` to `[a, b]` (giving a field that is continuous
in `(t, x)` and globally Lipschitz in `x`, cf.
`Commons.Analysis.ODE.exists_solution_Icc_of_continuousOn_of_lipschitzWith`) and uniqueness by
`ODE_solution_unique_of_mem_Icc_right`/`_left` (split on whether `t₀ = a`, `t₀ = b` or
`a < t₀ < b`). -/
theorem exists_linearODE_solution_continuousOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {A : ℝ → E →L[ℝ] E} {a b t₀ : ℝ} (hab : a < b)
    (hA : ContinuousOn A (Set.Icc a b)) (ht₀ : t₀ ∈ Set.Icc a b) (y₀ : E) :
    ∃ y : ℝ → E, y t₀ = y₀ ∧ ContinuousOn y (Set.Icc a b) ∧
      (∀ t ∈ Set.Ioo a b, HasDerivAt y (A t (y t)) t) ∧
      ∀ z : ℝ → E, z t₀ = y₀ → ContinuousOn z (Set.Icc a b) →
        (∀ t ∈ Set.Ioo a b, HasDerivAt z (A t (z t)) t) → Set.EqOn z y (Set.Icc a b) := by
  classical
  have hab' : a ≤ b := le_of_lt hab
  obtain ⟨K, hK0, hK⟩ : ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Set.Icc a b, ‖A t‖ ≤ K := by
    obtain ⟨x, _, hmax⟩ :=
      isCompact_Icc.exists_isMaxOn (⟨t₀, ht₀⟩ : (Set.Icc a b).Nonempty) hA.norm
    exact ⟨‖A x‖, norm_nonneg _, fun t ht => hmax ht⟩
  let Knn : ℝ≥0 := ⟨K, hK0⟩
  let f : ℝ → E → E := fun t x => A (projIcc a b hab' t) x
  have hAp : Continuous (fun t : ℝ => A (projIcc a b hab' t)) :=
    hA.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
      (fun t => (projIcc a b hab' t).2)
  have hcontC : Continuous (Function.uncurry f) :=
    (hAp.comp continuous_fst).clm_apply continuous_snd
  have hcont : ContinuousOn (Function.uncurry f) (Set.Icc a b ×ˢ Set.univ) := hcontC.continuousOn
  have hAlip : ∀ t ∈ Set.Icc a b, LipschitzWith Knn (A t) := by
    intro t ht
    refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
    rw [dist_eq_norm, dist_eq_norm]
    show ‖A t x - A t y‖ ≤ K * ‖x - y‖
    calc ‖A t x - A t y‖ = ‖A t (x - y)‖ := by rw [map_sub]
      _ ≤ ‖A t‖ * ‖x - y‖ := (A t).le_opNorm _
      _ ≤ K * ‖x - y‖ := by gcongr; exact hK t ht
  have hflip : ∀ t ∈ Set.Icc a b, LipschitzWith Knn (f t) := by
    intro t ht
    have hft : f t = fun x => A t x := by
      funext x
      simp only [f]
      rw [projIcc_of_mem hab' ht]
    rw [hft]
    exact hAlip t ht
  obtain ⟨y, hy0, hycont, hyderiv, hyint⟩ :=
    exists_solution_Icc_of_continuousOn_of_lipschitzWith (f := f) hab' ht₀ y₀ hcont hflip
  have hyderiv' : ∀ t ∈ Set.Ioo a b, HasDerivAt y (A t (y t)) t := by
    intro t ht
    have hft : f t (y t) = A t (y t) := by
      simp only [f]
      rw [projIcc_of_mem hab' ⟨le_of_lt ht.1, le_of_lt ht.2⟩]
    exact (hyderiv t ht).congr_deriv hft
  have hyint' : ∀ t ∈ Set.Icc a b, y t = y₀ + ∫ s in t₀..t, A s (y s) := by
    intro t ht
    rw [hyint t ht]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    have hsIcc : s ∈ Set.Icc a b := uIcc_subset_Icc ht₀ ht hs
    simp only [f]
    rw [projIcc_of_mem hab' hsIcc]
  refine ⟨y, hy0, hycont, hyderiv', ?_⟩
  intro z hz0 hzcont hzderiv
  have hAz : ContinuousOn (fun x => A x (z x)) (Set.Icc a b) := hA.clm_apply hzcont
  have hAy : ContinuousOn (fun x => A x (y x)) (Set.Icc a b) := hA.clm_apply hycont
  have hright : Set.EqOn z y (Set.Icc t₀ b) := by
    refine ODE_solution_unique_of_mem_Icc_right (v := fun t x => A t x) (s := fun _ => Set.univ)
      (K := Knn) (a := t₀) (b := b) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro t ht
      exact (hAlip t (Set.Icc_subset_Icc ht₀.1 le_rfl (Set.Ico_subset_Icc_self ht))).lipschitzOnWith
    · exact hzcont.mono (Set.Icc_subset_Icc ht₀.1 le_rfl)
    · exact fun t ht => hasDerivWithinAt_Ici_of_mem_Ico hab ht₀ hzcont hzderiv hAz ht
    · intro t _; trivial
    · exact hycont.mono (Set.Icc_subset_Icc ht₀.1 le_rfl)
    · exact fun t ht => hasDerivWithinAt_Ici_of_mem_Ico hab ht₀ hycont hyderiv' hAy ht
    · intro t _; trivial
    · rw [hz0, hy0]
  have hleft : Set.EqOn z y (Set.Icc a t₀) := by
    refine ODE_solution_unique_of_mem_Icc_left (v := fun t x => A t x) (s := fun _ => Set.univ)
      (K := Knn) (a := a) (b := t₀) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro t ht
      exact (hAlip t (Set.Icc_subset_Icc le_rfl ht₀.2 (Set.Ioc_subset_Icc_self ht))).lipschitzOnWith
    · exact hzcont.mono (Set.Icc_subset_Icc le_rfl ht₀.2)
    · exact fun t ht => hasDerivWithinAt_Iic_of_mem_Ioc hab ht₀ hzcont hzderiv hAz ht
    · intro t _; trivial
    · exact hycont.mono (Set.Icc_subset_Icc le_rfl ht₀.2)
    · exact fun t ht => hasDerivWithinAt_Iic_of_mem_Ioc hab ht₀ hycont hyderiv' hAy ht
    · intro t _; trivial
    · rw [hz0, hy0]
  intro t ht
  rcases le_total t t₀ with h | h
  · exact hleft ⟨ht.1, h⟩
  · exact hright ⟨h, ht.2⟩

end Main

end Commons.Analysis.ODE