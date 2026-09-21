import Mathlib
import Submission.Work.OddRadon.Chapter
import Submission.Work.OddRadon.abelTrans_radonInverse_eq_abelDatum

namespace Work.OddRadon

noncomputable section

open MeasureTheory Set Filter
open scoped Interval Topology

/-!
# Inversion of `radonProfile` in odd dimensions: the right-inverse direction

The target `radonProfile_radonInverse` says that for an even `C^∞` datum `F` on `[0,1]`,
`radonProfile (2n+1) (fun u => radonInverse n F |u|)` agrees with `F` on `(0,1)`.

Through the (unconditional form of) `radonProfile_eq_abelTrans` this is equivalent to the
**right-inverse (surjectivity) half** of the odd-dimensional Abel inversion,

`abelTrans α (abelInvert (abelReduceIter α (n-1) Ψ)) c = Ψ c`,  `α = n - 3/2`, `Ψ = abelDatum n F`,

the left-inverse half being `abel_inversion_odd`.  We build the right-inverse half here.
-/

/-! ## The trigonometric form of the Abel inversion -/

/-- A simultaneous bound for `Ψ` and `deriv Ψ` on `(0,1)`. -/
lemma exists_bound_deriv {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ 1 Ψ) :
    ∃ C : ℝ, ∀ x ∈ Set.Ioo (0:ℝ) 1, ‖Ψ x‖ ≤ C ∧ ‖deriv Ψ x‖ ≤ C := by
  have h1 : ContinuousOn Ψ (Set.Icc (0:ℝ) 1) := hΨ.continuous.continuousOn
  have h2 : ContinuousOn (deriv Ψ) (Set.Icc (0:ℝ) 1) :=
    (hΨ.continuous_deriv le_rfl).continuousOn
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn h1
  obtain ⟨C₂, hC₂⟩ := isCompact_Icc.exists_bound_of_continuousOn h2
  refine ⟨max C₁ C₂, fun x hx => ⟨?_, ?_⟩⟩
  · exact (hC₁ x ⟨hx.1.le, hx.2.le⟩).trans (le_max_left _ _)
  · exact (hC₂ x ⟨hx.1.le, hx.2.le⟩).trans (le_max_right _ _)

/-- **The trigonometric form of the derivative of the inner Abel integral.**
For smooth `Ψ` and `u ∈ (0,1)`,

`d/du ∫_0^u c Ψ c / √(u²-c²) dc = ∫_0^{π/2} sin θ (Ψ (u sin θ) + u sin θ Ψ' (u sin θ)) dθ`. -/
lemma deriv_abelIntegral {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ 1 Ψ) {u : ℝ}
    (hu : u ∈ Set.Ioo (0:ℝ) 1) :
    deriv (fun v : ℝ => ∫ c in (0:ℝ)..v, c * Ψ c / Real.sqrt (v ^ 2 - c ^ 2)) u
      = ∫ θ in (0:ℝ)..(Real.pi / 2),
          Real.sin θ * (Ψ (u * Real.sin θ) + u * Real.sin θ * deriv Ψ (u * Real.sin θ)) := by
  obtain ⟨C, hC⟩ := exists_bound_deriv hΨ
  have hΨc : Continuous Ψ := hΨ.continuous
  have hdΨc : Continuous (deriv Ψ) := hΨ.continuous_deriv le_rfl
  -- the integrand of the trigonometric form and its parameter derivative
  set F : ℝ → ℝ → ℝ := fun v θ => v * Real.sin θ * Ψ (v * Real.sin θ) with hF
  set F' : ℝ → ℝ → ℝ := fun v θ =>
    Real.sin θ * (Ψ (v * Real.sin θ) + v * Real.sin θ * deriv Ψ (v * Real.sin θ)) with hF'
  -- derivative of the parametrised integral
  have htrig : HasDerivAt (fun v : ℝ => ∫ θ in (0:ℝ)..(Real.pi / 2), F v θ)
      (∫ θ in (0:ℝ)..(Real.pi / 2), F' u θ) u := by
    have hcontF : ∀ v : ℝ, Continuous fun θ : ℝ => F v θ := by
      intro v
      have h1 : Continuous fun θ : ℝ => v * Real.sin θ := by fun_prop
      exact h1.mul (hΨc.comp h1)
    have hcontF' : Continuous fun θ : ℝ => F' u θ := by
      have h1 : Continuous fun θ : ℝ => u * Real.sin θ := by fun_prop
      exact (Real.continuous_sin.mul ((hΨc.comp h1).add (h1.mul (hdΨc.comp h1))))
    refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (a := (0:ℝ)) (b := Real.pi / 2) (bound := fun _ => C + C)
      (F := F) (F' := F') (x₀ := u) (s := Set.Ioo (0:ℝ) 1)
      (isOpen_Ioo.mem_nhds hu) ?_ ?_ ?_ ?_ intervalIntegrable_const ?_).2
    · filter_upwards with v
      exact (hcontF v).aestronglyMeasurable
    · exact (hcontF u).continuousOn.intervalIntegrable
    · exact hcontF'.aestronglyMeasurable
    · filter_upwards with θ hθ v hv
      have hθ' : θ ∈ Set.Ioo (0:ℝ) Real.pi := by
        rw [Set.uIoc_of_le (by positivity : (0:ℝ) ≤ Real.pi / 2)] at hθ
        exact ⟨hθ.1, by linarith [Real.pi_pos, hθ.2]⟩
      have hsinpos : 0 < Real.sin θ := Real.sin_pos_of_mem_Ioo hθ'
      have hvsin : v * Real.sin θ ∈ Set.Ioo (0:ℝ) 1 := by
        refine ⟨mul_pos hv.1 hsinpos, ?_⟩
        nlinarith [Real.sin_le_one θ, hv.1.le, hv.2]
      obtain ⟨hC1, hC2⟩ := hC _ hvsin
      have h1 : |v * Real.sin θ| ≤ 1 := by
        rw [abs_of_pos (mul_pos hv.1 hsinpos)]
        exact le_of_lt hvsin.2
      have h2 : |deriv Ψ (v * Real.sin θ)| ≤ C := by
        simpa only [Real.norm_eq_abs] using hC2
      have h3 : |Ψ (v * Real.sin θ)| ≤ C := by
        simpa only [Real.norm_eq_abs] using hC1
      have h4 : |Ψ (v * Real.sin θ) + v * Real.sin θ * deriv Ψ (v * Real.sin θ)| ≤ C + C := by
        calc |Ψ (v * Real.sin θ) + v * Real.sin θ * deriv Ψ (v * Real.sin θ)|
            ≤ |Ψ (v * Real.sin θ)| + |v * Real.sin θ * deriv Ψ (v * Real.sin θ)| := abs_add_le _ _
          _ = |Ψ (v * Real.sin θ)| + |v * Real.sin θ| * |deriv Ψ (v * Real.sin θ)| := by
                rw [abs_mul]
          _ ≤ C + 1 * C := add_le_add h3 (mul_le_mul h1 h2 (abs_nonneg _) zero_le_one)
          _ = C + C := by ring
      simp only [hF, hF']
      calc ‖Real.sin θ * (Ψ (v * Real.sin θ) + v * Real.sin θ * deriv Ψ (v * Real.sin θ))‖
          = |Real.sin θ| * |Ψ (v * Real.sin θ) + v * Real.sin θ * deriv Ψ (v * Real.sin θ)| := by
              rw [Real.norm_eq_abs, abs_mul]
        _ ≤ 1 * (C + C) := mul_le_mul (Real.abs_sin_le_one θ) h4 (abs_nonneg _) (by norm_num)
        _ = C + C := one_mul _
    · filter_upwards with θ hθ v hv
      simp only [hF, hF']
      have h1 : HasDerivAt (fun v : ℝ => v * Real.sin θ) (Real.sin θ) v := by
        simpa using (hasDerivAt_id v).mul_const (Real.sin θ)
      have h2 : HasDerivAt (fun v : ℝ => Ψ (v * Real.sin θ))
          (deriv Ψ (v * Real.sin θ) * Real.sin θ) v :=
        (((hΨ.differentiable (by norm_num)).differentiableAt).hasDerivAt.comp v h1).congr_deriv
          (by ring)
      have h3 : HasDerivAt (fun v : ℝ => v * Real.sin θ * Ψ (v * Real.sin θ))
          (Real.sin θ * Ψ (v * Real.sin θ)
            + (v * Real.sin θ) * (deriv Ψ (v * Real.sin θ) * Real.sin θ)) v :=
        (h1.mul h2).congr_of_eventuallyEq (by filter_upwards with y; rfl)
      exact h3.congr_deriv (by ring)
  -- the inner Abel integral agrees with the trigonometric form on `(0,1)`
  have hcontΨ : ContinuousOn Ψ (Set.Ioo (0:ℝ) 1) := hΨc.continuousOn
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hΨc.continuousOn
  have hbdd : ∀ c ∈ Set.Ioo (0:ℝ) 1, ‖Ψ c‖ ≤ M := fun c hc => hM c ⟨hc.1.le, hc.2.le⟩
  have hEq : Set.EqOn (fun v : ℝ => ∫ c in (0:ℝ)..v, c * Ψ c / Real.sqrt (v ^ 2 - c ^ 2))
      (fun v : ℝ => ∫ θ in (0:ℝ)..(Real.pi / 2), F v θ) (Set.Ioo (0:ℝ) 1) := by
    intro v hv
    simpa only [hF] using abel_integral_trig_substitution hv.1 hv.2 hcontΨ hbdd
  rw [(hEq.deriv isOpen_Ioo) hu, htrig.deriv]

/-- The trigonometric representative is continuous. -/
lemma continuous_abelInvertTrig {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ⊤ Ψ) :
    Continuous (fun u : ℝ => (2 / Real.pi) * ∫ θ in (0:ℝ)..(Real.pi / 2),
      Real.sin θ * (Ψ (u * Real.sin θ) + u * Real.sin θ * deriv Ψ (u * Real.sin θ))) := by
  refine Continuous.const_mul ?_ _
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous ?_ continuous_const
  have hΨc : Continuous Ψ := hΨ.continuous
  have hdΨc : Continuous (deriv Ψ) := hΨ.continuous_deriv le_top
  have h1 : Continuous fun p : ℝ × ℝ => p.1 * Real.sin p.2 := by fun_prop
  have h2 : Continuous fun p : ℝ × ℝ => Ψ (p.1 * Real.sin p.2) := hΨc.comp h1
  have h3 : Continuous fun p : ℝ × ℝ => deriv Ψ (p.1 * Real.sin p.2) := hdΨc.comp h1
  show Continuous (fun p : ℝ × ℝ => Real.sin p.2 *
    (Ψ (p.1 * Real.sin p.2) + p.1 * Real.sin p.2 * deriv Ψ (p.1 * Real.sin p.2)))
  exact (Real.continuous_sin.comp continuous_snd).mul (h2.add (h1.mul h3))

/-- The trigonometric representative of `abelInvert Ψ`: the derivative of the trigonometric
form of the inner Abel integral. -/
def abelInvertTrig (Ψ : ℝ → ℝ) (u : ℝ) : ℝ :=
  (2 / Real.pi) * ∫ θ in (0 : ℝ)..(Real.pi / 2),
    Real.sin θ * (Ψ (u * Real.sin θ) + u * Real.sin θ * deriv Ψ (u * Real.sin θ))

/-- The trigonometric form `∫_0^{π/2} G (c sin θ) dθ` of the half-Abel transform
`∫_0^c G s / √(c²-s²) ds`. -/
def trigAbel (G : ℝ → ℝ) (c : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..(Real.pi / 2), G (c * Real.sin θ)

/-- `abelInvert Ψ` in trigonometric form on `(0,1)`. -/
theorem abelInvert_eq_abelInvertTrig {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ 1 Ψ) {u : ℝ}
    (hu : u ∈ Set.Ioo (0:ℝ) 1) : abelInvert Ψ u = abelInvertTrig Ψ u := by
  unfold abelInvert abelInvertTrig
  rw [deriv_abelIntegral hΨ hu]

/-- Smoothness of the trigonometric representative. -/
lemma contDiff_abelInvertTrig {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ⊤ Ψ) (n : ℕ) :
    ContDiff ℝ n (abelInvertTrig Ψ) := by
  unfold abelInvertTrig
  refine contDiff_const.mul ?_
  refine Work.Analysis.Calculus.contDiff_intervalIntegral_fixed n ?_
  have hd : ContDiff ℝ ⊤ (deriv Ψ) := by simpa using hΨ.deriv'
  have h1 : ContDiff ℝ n (fun p : ℝ × ℝ => p.1 * Real.sin p.2) := by fun_prop
  have hsin : ContDiff ℝ n (fun p : ℝ × ℝ => Real.sin p.2) := by fun_prop
  have h2 : ContDiff ℝ n (fun p : ℝ × ℝ => Ψ (p.1 * Real.sin p.2)) :=
    (hΨ.of_le le_top).comp h1
  have h3 : ContDiff ℝ n (fun p : ℝ × ℝ => deriv Ψ (p.1 * Real.sin p.2)) :=
    (hd.of_le le_top).comp h1
  exact hsin.mul (h2.add (h1.mul h3))

/-- Smoothness of `trigAbel G`. -/
lemma contDiff_trigAbel {G : ℝ → ℝ} (hG : ∀ n : ℕ, ContDiff ℝ n G) (n : ℕ) :
    ContDiff ℝ n (trigAbel G) := by
  unfold trigAbel
  refine Work.Analysis.Calculus.contDiff_intervalIntegral_fixed n ?_
  have h1 : ContDiff ℝ n (fun p : ℝ × ℝ => p.1 * Real.sin p.2) := by fun_prop
  exact (hG n).comp h1

/-- The half-Abel transform in trigonometric form. -/
lemma abelTrans_neg_half_eq_trigAbel {G : ℝ → ℝ} {c : ℝ} (hc : 0 < c) :
    abelTrans (-(1 / 2)) G c = trigAbel G c := by
  rw [abelTrans_neg_half_eq hc.le]
  have hpi2 : (0:ℝ) < Real.pi / 2 := by positivity
  have hc' : ContinuousOn (fun θ : ℝ => c * Real.sin θ) (Set.uIcc (0:ℝ) (Real.pi / 2)) :=
    (continuous_const.mul Real.continuous_sin).continuousOn
  have hd : ∀ x ∈ Set.Ioo (min (0:ℝ) (Real.pi / 2)) (max (0:ℝ) (Real.pi / 2)),
      HasDerivAt (fun θ : ℝ => c * Real.sin θ) (c * Real.cos x) x := by
    intro x _
    exact (Real.hasDerivAt_sin x).const_mul c
  have hn : ∀ x ∈ Set.Ioo (min (0:ℝ) (Real.pi / 2)) (max (0:ℝ) (Real.pi / 2)),
      0 ≤ c * Real.cos x := by
    intro x hx
    rw [min_eq_left hpi2.le, max_eq_right hpi2.le] at hx
    exact mul_nonneg hc.le (Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, hx.1],
      by linarith [Real.pi_pos, hx.2]⟩)
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (f := fun θ : ℝ => c * Real.sin θ) (f' := fun θ : ℝ => c * Real.cos θ)
    (g := fun s : ℝ => G s / Real.sqrt (c ^ 2 - s ^ 2)) (a := (0:ℝ)) (b := Real.pi / 2)
    hc' hd hn
  simp only [Function.comp_apply, Real.sin_zero, mul_zero, Real.sin_pi_div_two, mul_one] at hsub
  rw [← hsub]
  unfold trigAbel
  apply intervalIntegral.integral_congr_ae
  have hcompl : ∀ᵐ x ∂(volume : Measure ℝ), x ∉ ({Real.pi / 2} : Set ℝ) := by
    have hfin : ({Real.pi / 2} : Set ℝ).Finite := Set.finite_singleton _
    exact MeasureTheory.compl_mem_ae_iff.mpr (hfin.measure_zero volume)
  filter_upwards [hcompl] with θ hθ hθm
  rw [Set.uIoc_of_le hpi2.le] at hθm
  simp only [Set.mem_singleton_iff] at hθ
  have hθ0 : 0 < θ := hθm.1
  have hθlt : θ < Real.pi / 2 := lt_of_le_of_ne hθm.2 hθ
  have hcos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ0], by linarith [Real.pi_pos, hθlt]⟩
  have hsq : c ^ 2 - (c * Real.sin θ) ^ 2 = (c * Real.cos θ) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hsqrt : Real.sqrt (c ^ 2 - (c * Real.sin θ) ^ 2) = c * Real.cos θ := by
    rw [hsq, Real.sqrt_sq (by positivity)]
  rw [hsqrt]
  have hne : c * Real.cos θ ≠ 0 := by positivity
  field_simp

/-- The parameterised derivative of the trigonometric form of the inner Abel integral. -/
lemma hasDerivAt_trigInner {h : ℝ → ℝ} (hh : ContDiff ℝ 1 h) {u : ℝ}
    (hu : u ∈ Set.Ioo (0:ℝ) 1) :
    HasDerivAt (fun u : ℝ => ∫ θ in (0:ℝ)..(Real.pi / 2), u * Real.sin θ * h (u * Real.sin θ))
      (∫ θ in (0:ℝ)..(Real.pi / 2),
        Real.sin θ * (h (u * Real.sin θ) + u * Real.sin θ * deriv h (u * Real.sin θ))) u := by
  have hhc : Continuous h := hh.continuous
  have hdc : Continuous (deriv h) := hh.continuous_deriv le_rfl
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hhc.continuousOn
  obtain ⟨C₂, hC₂⟩ := isCompact_Icc.exists_bound_of_continuousOn hdc.continuousOn
  set F : ℝ → ℝ → ℝ := fun v θ => v * Real.sin θ * h (v * Real.sin θ) with hF
  set F' : ℝ → ℝ → ℝ := fun v θ =>
    Real.sin θ * (h (v * Real.sin θ) + v * Real.sin θ * deriv h (v * Real.sin θ)) with hF''
  have hcontF : ∀ v : ℝ, Continuous fun θ : ℝ => F v θ := by
    intro v
    have h1 : Continuous fun θ : ℝ => v * Real.sin θ := by fun_prop
    exact h1.mul (hhc.comp h1)
  have hcontF' : Continuous fun θ : ℝ => F' u θ := by
    have h1 : Continuous fun θ : ℝ => u * Real.sin θ := by fun_prop
    exact Real.continuous_sin.mul ((hhc.comp h1).add (h1.mul (hdc.comp h1)))
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := (0:ℝ)) (b := Real.pi / 2) (bound := fun _ => C₁ + C₂)
    (F := F) (F' := F') (x₀ := u) (s := Set.Ioo (-1:ℝ) 1)
    (isOpen_Ioo.mem_nhds ⟨by linarith [hu.1], by linarith [hu.2]⟩) ?_ ?_ ?_ ?_
    intervalIntegrable_const ?_).2
  · filter_upwards with v
    exact (hcontF v).aestronglyMeasurable
  · exact (hcontF u).continuousOn.intervalIntegrable
  · exact hcontF'.aestronglyMeasurable
  · filter_upwards with θ hθ v hv
    have hsin1 : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
    have hv1 : |v| ≤ 1 := by rw [abs_le]; exact ⟨hv.1.le, hv.2.le⟩
    have hmem : v * Real.sin θ ∈ Set.Icc (-2:ℝ) 2 := by
      rw [Set.mem_Icc, ← abs_le, abs_mul]
      nlinarith [hv1, Real.abs_sin_le_one θ, abs_nonneg v, abs_nonneg (Real.sin θ)]
    have h1 : |h (v * Real.sin θ)| ≤ C₁ := by
      simpa only [Real.norm_eq_abs] using hC₁ _ hmem
    have h2 : |deriv h (v * Real.sin θ)| ≤ C₂ := by
      simpa only [Real.norm_eq_abs] using hC₂ _ hmem
    have h3 : |v * Real.sin θ| ≤ 1 := by
      rw [abs_mul]
      calc |v| * |Real.sin θ| ≤ 1 * 1 :=
            mul_le_mul hv1 hsin1 (abs_nonneg _) (by norm_num)
        _ = 1 := by ring
    simp only [hF, hF'']
    rw [Real.norm_eq_abs, abs_mul]
    calc |Real.sin θ| * |h (v * Real.sin θ) + v * Real.sin θ * deriv h (v * Real.sin θ)|
        ≤ 1 * (C₁ + C₂) := by
          refine mul_le_mul hsin1 ?_ (abs_nonneg _) (by norm_num)
          calc |h (v * Real.sin θ) + v * Real.sin θ * deriv h (v * Real.sin θ)|
              ≤ |h (v * Real.sin θ)| + |v * Real.sin θ * deriv h (v * Real.sin θ)| :=
                abs_add_le _ _
            _ = |h (v * Real.sin θ)| + |v * Real.sin θ| * |deriv h (v * Real.sin θ)| := by
                rw [abs_mul]
            _ ≤ C₁ + 1 * C₂ := add_le_add h1 (mul_le_mul h3 h2 (abs_nonneg _) zero_le_one)
            _ = C₁ + C₂ := by ring
      _ = C₁ + C₂ := one_mul _
      _ = C₁ + C₂ := by ring
  · filter_upwards with θ hθ v hv
    simp only [hF, hF'']
    have h1 : HasDerivAt (fun v : ℝ => v * Real.sin θ) (Real.sin θ) v := by
      simpa using (hasDerivAt_id v).mul_const (Real.sin θ)
    have h2 : HasDerivAt (fun v : ℝ => h (v * Real.sin θ))
        (deriv h (v * Real.sin θ) * Real.sin θ) v :=
      (((hh.differentiable (by norm_num)).differentiableAt).hasDerivAt.comp v h1).congr_deriv
        (by ring)
    have h3 : HasDerivAt (fun v : ℝ => v * Real.sin θ * h (v * Real.sin θ))
        (Real.sin θ * h (v * Real.sin θ)
          + (v * Real.sin θ) * (deriv h (v * Real.sin θ) * Real.sin θ)) v :=
      (h1.mul h2).congr_of_eventuallyEq (by filter_upwards with y; rfl)
    exact h3.congr_deriv (by ring)

/-- The trigonometric form of the inner Abel integral (with the weight `c`). -/
lemma trigInner_eq_abelIntegral {h : ℝ → ℝ} (hh : ContDiff ℝ ⊤ h) {u : ℝ}
    (hu : u ∈ Set.Ioo (0:ℝ) 1) :
    (fun u : ℝ => ∫ θ in (0:ℝ)..(Real.pi / 2), u * Real.sin θ * h (u * Real.sin θ)) u
      = ∫ c in (0:ℝ)..u, c * h c / Real.sqrt (u ^ 2 - c ^ 2) := by
  have hcont : ContinuousOn h (Set.Ioo (0:ℝ) 1) := hh.continuous.continuousOn
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hh.continuous.continuousOn
  exact (abel_integral_trig_substitution hu.1 hu.2 hcont
    (fun c hc => hM c ⟨hc.1.le, hc.2.le⟩)).symm

/-- **Injectivity of the Abel inversion on smooth functions.**  If `abelInvert h` vanishes on
`(0,1)` and `h` is `C¹` with an `L^∞` bound, then `h` vanishes on `(0,1)`. -/
lemma abelInvert_eq_zero_imp {h : ℝ → ℝ} (hh : ContDiff ℝ 1 h)
    (hzero : ∀ u ∈ Set.Ioo (0:ℝ) 1, abelInvert h u = 0) :
    ∀ c ∈ Set.Ioo (0:ℝ) 1, h c = 0 := by
  have hhc : Continuous h := hh.continuous
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hhc.continuousOn
  set ψ : ℝ → ℝ := fun u => ∫ θ in (0:ℝ)..(Real.pi / 2), u * Real.sin θ * h (u * Real.sin θ)
    with hψ
  -- ψ and the weighted inner Abel integral agree on (0,1)
  have hEqOn : Set.EqOn ψ (fun v : ℝ => ∫ c in (0:ℝ)..v, c * h c / Real.sqrt (v ^ 2 - c ^ 2))
      (Set.Ioo (0:ℝ) 1) := by
    intro v hv
    show (∫ θ in (0:ℝ)..(Real.pi / 2), v * Real.sin θ * h (v * Real.sin θ))
      = ∫ c in (0:ℝ)..v, c * h c / Real.sqrt (v ^ 2 - c ^ 2)
    exact (abel_integral_trig_substitution hv.1 hv.2 hhc.continuousOn
      (fun c hc => hM c ⟨hc.1.le, hc.2.le⟩)).symm
  -- the derivative of ψ vanishes on (0,1)
  have hderiv0 : ∀ u ∈ Set.Ioo (0:ℝ) 1, deriv ψ u = 0 := by
    intro u hu
    have h1 : deriv ψ u
        = deriv (fun v : ℝ => ∫ c in (0:ℝ)..v, c * h c / Real.sqrt (v ^ 2 - c ^ 2)) u :=
      (hEqOn.deriv isOpen_Ioo) hu
    rw [h1]
    have h2 := hzero u hu
    unfold abelInvert at h2
    have hne : (2 / Real.pi : ℝ) ≠ 0 := by positivity
    exact (mul_eq_zero.mp h2).resolve_left hne
  -- ψ differentiable on (0,1)
  have hdiff : DifferentiableOn ℝ ψ (Set.Ioo (0:ℝ) 1) := by
    intro u hu
    exact (hasDerivAt_trigInner hh hu).differentiableAt.differentiableWithinAt
  -- hence ψ is constant on (0,1)
  have hconst : ∀ a b, a ∈ Set.Ioo (0:ℝ) 1 → b ∈ Set.Ioo (0:ℝ) 1 → ψ a = ψ b := by
    have key : ∀ x y, x ∈ Set.Ioo (0:ℝ) 1 → y ∈ Set.Ioo (0:ℝ) 1 → x < y → ψ x = ψ y := by
      intro x y hx hy hxy
      obtain ⟨ξ, hξ, hξeq⟩ := exists_deriv_eq_slope ψ hxy
        (hdiff.continuousOn.mono (Set.Icc_subset_Ioo hx.1 hy.2))
        (hdiff.mono (Set.Ioo_subset_Ioo hx.1.le hy.2.le))
      rw [hderiv0 ξ ⟨lt_trans hx.1 hξ.1, lt_trans hξ.2 hy.2⟩] at hξeq
      have hyn : y - x ≠ 0 := ne_of_gt (sub_pos.mpr hxy)
      have hz : ψ x - ψ y = 0 := by
        field_simp at hξeq
        linarith
      exact sub_eq_zero.mp hz
    intro a b ha hb
    by_cases hab : a ≤ b
    · rcases eq_or_lt_of_le hab with h | h
      · rw [← h]
      · exact key a b ha hb h
    · rcases eq_or_lt_of_le (le_of_lt (lt_of_not_ge hab)) with h | h
      · rw [h]
      · exact (key b a hb ha h).symm
  -- ψ vanishes on `(0,1)`
  have hψbound : ∀ u ∈ Set.Ioo (0:ℝ) 1, |ψ u| ≤ M * u := by
    intro u hu
    rw [hψ]
    have h1 : |∫ θ in (0:ℝ)..(Real.pi / 2), u * Real.sin θ * h (u * Real.sin θ)|
        ≤ ∫ θ in (0:ℝ)..(Real.pi / 2), |u * Real.sin θ * h (u * Real.sin θ)| :=
      intervalIntegral.abs_integral_le_integral_abs (by positivity)
    have h2 : (∫ θ in (0:ℝ)..(Real.pi / 2), |u * Real.sin θ * h (u * Real.sin θ)|)
        ≤ ∫ θ in (0:ℝ)..(Real.pi / 2), u * Real.sin θ * M := by
      apply intervalIntegral.integral_mono_on (by positivity)
      · exact (((continuous_const.mul Real.continuous_sin).mul
          (hhc.comp (continuous_const.mul Real.continuous_sin))).abs).continuousOn.intervalIntegrable
      · exact (((continuous_const.mul Real.continuous_sin).mul
          continuous_const)).continuousOn.intervalIntegrable
      · intro θ hθ
        have hsin : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc
          ⟨hθ.1, by linarith [Real.pi_pos, hθ.2]⟩
        have hmem : u * Real.sin θ ∈ Set.Icc (0:ℝ) 1 := by
          refine ⟨mul_nonneg hu.1.le hsin, ?_⟩
          nlinarith [Real.sin_le_one θ, hu.1.le, hu.2]
        have hb := hM _ hmem
        rw [Real.norm_eq_abs] at hb
        rw [abs_mul, abs_of_nonneg (mul_nonneg hu.1.le hsin)]
        exact mul_le_mul_of_nonneg_left hb (mul_nonneg hu.1.le hsin)
    have h3 : (∫ θ in (0:ℝ)..(Real.pi / 2), u * Real.sin θ * M) = M * u := by
      rw [show (fun θ : ℝ => u * Real.sin θ * M) = (fun θ : ℝ => (M * u) * Real.sin θ) by
        funext θ; ring]
      rw [intervalIntegral.integral_const_mul, integral_sin]
      simp [Real.cos_pi_div_two, Real.cos_zero]
    rw [h3] at h2
    exact le_trans h1 h2
  have hψzero : ∀ u ∈ Set.Ioo (0:ℝ) 1, ψ u = 0 := by
    intro u hu
    by_contra hne
    have hpos : 0 < |ψ u| := abs_pos.mpr hne
    have hMnn : 0 ≤ M := le_trans (abs_nonneg _) (hM 0 ⟨le_rfl, zero_le_one⟩)
    by_cases hM0 : M = 0
    · have hle : |ψ u| ≤ 0 := by
        have := hψbound u hu
        rwa [hM0, zero_mul] at this
      exact hne (abs_eq_zero.mp (le_antisymm hle (abs_nonneg _)))
    · have hMpos : 0 < M := lt_of_le_of_ne hMnn (Ne.symm hM0)
      set u₀ : ℝ := min (u / 2) (|ψ u| / (2 * M)) with hu₀def
      have hu₀pos : 0 < u₀ := lt_min (by linarith [hu.1]) (by positivity)
      have hu₀lt : u₀ < 1 := lt_of_le_of_lt (min_le_left _ _) (by linarith [hu.2])
      have hu₀ : u₀ ∈ Set.Ioo (0:ℝ) 1 := ⟨hu₀pos, hu₀lt⟩
      have h1 : |ψ u| ≤ M * u₀ := by
        rw [hconst u u₀ hu hu₀]
        exact hψbound u₀ hu₀
      have h2 : M * u₀ ≤ |ψ u| / 2 := by
        calc M * u₀ ≤ M * (|ψ u| / (2 * M)) :=
              mul_le_mul_of_nonneg_left (min_le_right _ _) hMpos.le
          _ = |ψ u| / 2 := by field_simp
      linarith
  -- the weighted function `c ↦ c * h c` is continuous, and its Abel transform vanishes
  have hMcont : ContinuousOn (fun c : ℝ => c * h c) (Set.Icc (0:ℝ) 1) :=
    (continuousOn_id.mul hhc.continuousOn)
  have hinner : Set.EqOn (fun c : ℝ => ∫ s in (0:ℝ)..c, (s * h s) / Real.sqrt (c ^ 2 - s ^ 2))
      (0 : ℝ → ℝ) (Set.Ioo (0:ℝ) 1) := by
    intro c hc
    rw [Pi.zero_apply]
    show (∫ s in (0:ℝ)..c, (s * h s) / Real.sqrt (c ^ 2 - s ^ 2)) = 0
    have h1 : (∫ s in (0:ℝ)..c, (s * h s) / Real.sqrt (c ^ 2 - s ^ 2)) = ψ c := (hEqOn hc).symm
    rw [h1, hψzero c hc]
  intro c hc
  have hleft := Commons.Analysis.Radon.abel_inversion_hemisphere_final (G := fun c : ℝ => c * h c)
    hMcont hc
  have hz : abelInvert (0 : ℝ → ℝ) c = 0 := by
    unfold abelInvert
    simp
  have hf : c * h c = 0 := by
    have h2 : (2 / Real.pi) * deriv (fun u => ∫ c' in (0:ℝ)..u,
          c' * (∫ s in (0:ℝ)..c', s * h s / Real.sqrt (c' ^ 2 - s ^ 2)) /
            Real.sqrt (u ^ 2 - c' ^ 2)) c
        = abelInvert (fun c' : ℝ => ∫ s in (0:ℝ)..c',
            s * h s / Real.sqrt (c' ^ 2 - s ^ 2)) c := rfl
    rw [hleft, h2, abelInvert_congr_of_eqOn hc.1 hc.2 hinner, hz]
  exact (mul_eq_zero.mp hf).resolve_left (ne_of_gt hc.1)

/-- Linearity of the Abel inversion on smooth functions. -/
lemma abelInvert_sub {f g : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) {u : ℝ}
    (hu : u ∈ Set.Ioo (0:ℝ) 1) :
    abelInvert (f - g) u = abelInvert f u - abelInvert g u := by
  have hfg : ContDiff ℝ 1 (f - g) := hf.sub hg
  rw [abelInvert_eq_abelInvertTrig hfg hu, abelInvert_eq_abelInvertTrig hf hu,
    abelInvert_eq_abelInvertTrig hg hu]
  unfold abelInvertTrig
  rw [← mul_sub]
  congr 1
  rw [← intervalIntegral.integral_sub]
  · apply intervalIntegral.integral_congr
    intro θ _
    have hderivfun : deriv (f - g) = fun x => deriv f x - deriv g x := by
      funext x
      exact deriv_sub ((hf.differentiable (by norm_num)).differentiableAt)
        ((hg.differentiable (by norm_num)).differentiableAt)
    rw [hderivfun]
    simp only [Pi.sub_apply]
    ring
  · have h1 : Continuous fun θ : ℝ => u * Real.sin θ := by fun_prop
    have h2 : Continuous fun θ : ℝ =>
        Real.sin θ * (f (u * Real.sin θ) + u * Real.sin θ * deriv f (u * Real.sin θ)) :=
      Real.continuous_sin.mul ((hf.continuous.comp h1).add
        (h1.mul ((hf.continuous_deriv le_rfl).comp h1)))
    exact h2.intervalIntegrable (0:ℝ) (Real.pi / 2)
  · have h1 : Continuous fun θ : ℝ => u * Real.sin θ := by fun_prop
    have h2 : Continuous fun θ : ℝ =>
        Real.sin θ * (g (u * Real.sin θ) + u * Real.sin θ * deriv g (u * Real.sin θ)) :=
      Real.continuous_sin.mul ((hg.continuous.comp h1).add
        (h1.mul ((hg.continuous_deriv le_rfl).comp h1)))
    exact h2.intervalIntegrable (0:ℝ) (Real.pi / 2)

/-- **The right-inverse (surjectivity) half of the half-Abel transform**, for smooth data:
`∫_0^c (abelInvert Ψ) s / √(c²-s²) ds = Ψ c` on `(0,1)`. -/
theorem abelTrans_neg_half_abelInvert {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ⊤ Ψ) {c : ℝ}
    (hc : c ∈ Set.Ioo (0:ℝ) 1) :
    abelTrans (-(1 / 2)) (abelInvert Ψ) c = Ψ c := by
  set Bc : ℝ → ℝ := abelInvertTrig Ψ with hBc
  set T₂ : ℝ → ℝ := trigAbel Bc with hT₂
  have hBcinf : ∀ n : ℕ, ContDiff ℝ n Bc := fun n => contDiff_abelInvertTrig hΨ n
  have hBccont : ContinuousOn Bc (Set.Icc (0:ℝ) 1) := (hBcinf 1).continuous.continuousOn
  have hT₂sm : ContDiff ℝ 1 T₂ := contDiff_trigAbel hBcinf 1
  -- `T₂` is the half-Abel transform of `Bc`
  have hT₂abel : ∀ u ∈ Set.Ioo (0:ℝ) 1, abelTrans (-(1 / 2)) Bc u = T₂ u := by
    intro u hu
    rw [abelTrans_neg_half_eq_trigAbel hu.1]
  -- the left inverse of the half-Abel transform, applied to `Bc`
  have hleft : ∀ u ∈ Set.Ioo (0:ℝ) 1, abelInvert T₂ u = Bc u := by
    intro u hu
    have hinner : Set.EqOn (fun c : ℝ => ∫ s in (0:ℝ)..c, Bc s / Real.sqrt (c ^ 2 - s ^ 2))
        T₂ (Set.Ioo (0:ℝ) 1) := by
      intro c hc'
      show (∫ s in (0:ℝ)..c, Bc s / Real.sqrt (c ^ 2 - s ^ 2)) = T₂ c
      rw [← abelTrans_neg_half_eq hc'.1.le, hT₂abel c hc']
    have h := Commons.Analysis.Radon.abel_inversion_hemisphere_final (G := Bc) hBccont hu
    calc abelInvert T₂ u
        = abelInvert (fun c : ℝ => ∫ s in (0:ℝ)..c, Bc s / Real.sqrt (c ^ 2 - s ^ 2)) u :=
          (abelInvert_congr_of_eqOn hu.1 hu.2 hinner).symm
      _ = (2 / Real.pi) * deriv (fun u' : ℝ => ∫ c in (0:ℝ)..u',
            c * (∫ s in (0:ℝ)..c, Bc s / Real.sqrt (c ^ 2 - s ^ 2)) /
              Real.sqrt (u' ^ 2 - c ^ 2)) u := rfl
      _ = Bc u := h.symm
  -- hence `abelInvert (T₂ - Ψ)` vanishes
  have hzero : ∀ u ∈ Set.Ioo (0:ℝ) 1, abelInvert (T₂ - Ψ) u = 0 := by
    intro u hu
    rw [abelInvert_sub hT₂sm (hΨ.of_le le_top) hu, hleft u hu,
      abelInvert_eq_abelInvertTrig (hΨ.of_le le_top) hu]
    ring
  have hT₂Ψ : ∀ u ∈ Set.Ioo (0:ℝ) 1, (T₂ - Ψ) u = 0 :=
    abelInvert_eq_zero_imp (hT₂sm.sub (hΨ.of_le le_top)) hzero
  -- conclude
  have h1 : trigAbel (abelInvert Ψ) c = T₂ c := by
    show (∫ θ in (0:ℝ)..(Real.pi / 2), (abelInvert Ψ) (c * Real.sin θ))
      = (∫ θ in (0:ℝ)..(Real.pi / 2), Bc (c * Real.sin θ))
    apply intervalIntegral.integral_congr_ae
    filter_upwards with θ hθm
    rw [Set.uIoc_of_le (by positivity : (0:ℝ) ≤ Real.pi / 2)] at hθm
    have hsinpos : 0 < Real.sin θ :=
      Real.sin_pos_of_mem_Ioo ⟨hθm.1, by linarith [Real.pi_pos, hθm.2]⟩
    have hmem : c * Real.sin θ ∈ Set.Ioo (0:ℝ) 1 := by
      refine ⟨mul_pos hc.1 hsinpos, ?_⟩
      nlinarith [Real.sin_le_one θ, hc.1.le, hc.2]
    rw [abelInvert_eq_abelInvertTrig (hΨ.of_le le_top) hmem]
  rw [abelTrans_neg_half_eq_trigAbel hc.1, h1]
  exact sub_eq_zero.mp (hT₂Ψ c hc)

/-! ## The exponent-raising recursion in integrated form -/

/-- `abelTrans a G c` depends on `G` only on `(0,c)`. -/
lemma abelTrans_congr {a : ℝ} {f g : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (h : Set.EqOn f g (Set.Ioo (0:ℝ) c)) : abelTrans a f c = abelTrans a g c := by
  unfold abelTrans
  apply intervalIntegral.integral_congr_ae
  have hcompl : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ c := by
    rw [MeasureTheory.ae_iff]; simp [measure_singleton]
  filter_upwards [hcompl] with x hxc hx
  rw [Set.uIoc_of_le hc.le] at hx
  rw [h ⟨hx.1, lt_of_le_of_ne hx.2 hxc⟩]

/-- **Pointwise bound on the Abel transform.**  For `a > -1`, a function `G` bounded by `M` on
`(0,1)` and `s ∈ (0,1)`,
`‖abelTrans a G s‖ ≤ M · (∫_0^1 (1-v²)^a dv) · s^{2a+1}`. -/
lemma abelTrans_le_mul {a : ℝ} (ha : -1 < a) {G : ℝ → ℝ} {M : ℝ}
    (hM : ∀ x ∈ Set.Ioo (0:ℝ) 1, ‖G x‖ ≤ M) {s : ℝ} (hs : s ∈ Set.Ioo (0:ℝ) 1) :
    ‖abelTrans a G s‖ ≤ M * (∫ v in (0:ℝ)..1, (1 - v^2)^a) * s ^ (2*a + 1) := by
  have htrig : abelTrans a G s
      = s ^ (2*a + 1) * ∫ v in (0:ℝ)..1, G (s*v) * (1 - v^2)^a :=
    AbelDirect.abelTrans_eq_integral_comp_mul a G hs.1
  have hmain : ‖∫ v in (0:ℝ)..1, G (s*v) * (1 - v^2)^a‖
      ≤ ∫ v in (0:ℝ)..1, M * (1 - v^2)^a := by
    refine intervalIntegral.norm_integral_le_of_norm_le (by norm_num) ?_ ?_
    · filter_upwards with v hv
      rw [Set.mem_Ioc] at hv
      have hv0 : 0 < v := hv.1
      have hv1 : v ≤ 1 := hv.2
      have hnn : 0 ≤ (1 - v^2)^a := Real.rpow_nonneg (by nlinarith [hv0, hv1]) a
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnn]
      exact mul_le_mul_of_nonneg_right
        (hM _ ⟨mul_pos hs.1 hv0, by nlinarith [hs.2, hv0, hv1]⟩) hnn
    · exact (AbelDirect.intervalIntegrable_one_sub_sq_rpow ha).const_mul M
  have hconst : (∫ v in (0:ℝ)..1, M * (1 - v^2)^a) = M * (∫ v in (0:ℝ)..1, (1 - v^2)^a) :=
    intervalIntegral.integral_const_mul M _
  rw [htrig, norm_mul, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hs.1 (2*a+1))]
  calc s ^ (2*a+1) * ‖∫ v in (0:ℝ)..1, G (s*v) * (1 - v^2)^a‖
      ≤ s ^ (2*a+1) * (∫ v in (0:ℝ)..1, M * (1 - v^2)^a) :=
        mul_le_mul_of_nonneg_left hmain (Real.rpow_nonneg hs.1.le _)
    _ = s ^ (2*a+1) * (M * (∫ v in (0:ℝ)..1, (1 - v^2)^a)) := by rw [hconst]
    _ = M * (∫ v in (0:ℝ)..1, (1 - v^2)^a) * s ^ (2*a+1) := by ring

/-! ## The unconditional form of the profile transform identity and the final assembly -/

set_option linter.unusedVariables false in
/-- **The one-variable profile transform is an Abel transform** (no continuity hypothesis on the
profile: only its evenness is used). -/
theorem radonProfile_eq_abelTrans' (n : ℕ) (hn : 1 ≤ n) {γ : ℝ → ℝ}
    (heven : ∀ t, γ (-t) = γ t) {c : ℝ} (hc : 0 < c) :
    radonProfile (2 * n + 1) γ c
      = 2 * sphereArea (2 * n - 2) * (c ^ (2 * n - 2))⁻¹
          * abelTrans ((n : ℝ) - 3 / 2) γ c := by
  set α : ℝ := (n : ℝ) - 3 / 2 with hαdef
  have hcast : ((2 * n + 1 : ℕ) : ℝ) = 2 * (n : ℝ) + 1 := by push_cast; ring
  have hexp : ((2 * n + 1 : ℕ) : ℝ) / 2 - 2 = α := by rw [hαdef, hcast]; ring
  have hsub : 2 * n + 1 - 3 = 2 * n - 2 := by omega
  have hnat : ((2 * n - 2 : ℕ) : ℝ) = 2 * (n : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ 2 * n)]
    push_cast
    ring
  have h2a : 2 * α + 1 = ((2 * n - 2 : ℕ) : ℝ) := by rw [hαdef, hnat]; ring
  have hpow : c ^ (-(2 * α + 1)) = (c ^ (2 * n - 2))⁻¹ := by
    rw [Real.rpow_neg hc.le, h2a, Real.rpow_natCast]
  have habel : (∫ u in (0:ℝ)..c, (c ^ 2 - u ^ 2) ^ α * γ u) = abelTrans α γ c := by
    rw [abelTrans]
    exact intervalIntegral.integral_congr fun x _ => by ring
  simp only [radonProfile, hsub, hexp]
  rw [integral_neg_one_one_eq (G := γ) (α := α) hc]
  rw [integral_even_neg_eq_two_mul (f := fun u => (c ^ 2 - u ^ 2) ^ α * γ u) ?_ hc]
  · rw [habel, hpow]
    ring
  · intro t
    rw [neg_sq, heven t]

/-- **The composite `radonProfile (2n+1) ∘ radonInverse n` is the identity** on even `C^∞`
data: the spherical Radon transform in odd dimensions is onto. -/
theorem radonProfile_radonInverse (n : ℕ) (hn : 1 ≤ n) {F : ℝ → ℝ}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F (Set.Icc (0 : ℝ) 1))
    (heven : ∀ t : ℝ, F (-t) = F t) :
    ∀ c : ℝ, c ∈ Set.Ioo (0 : ℝ) 1 →
      Work.OddRadon.radonProfile (2 * n + 1)
        (fun u : ℝ => Work.OddRadon.radonInverse n F |u|) c = F c := by
  intro c hc
  have hγeven : ∀ t : ℝ,
      (fun u : ℝ => radonInverse n F |u|) (-t) = (fun u : ℝ => radonInverse n F |u|) t := by
    intro t; simp only [abs_neg]
  rw [radonProfile_eq_abelTrans' n hn hγeven hc.1]
  have habs : abelTrans ((n : ℝ) - 3 / 2) (fun u : ℝ => radonInverse n F |u|) c
      = abelTrans ((n : ℝ) - 3 / 2) (radonInverse n F) c := by
    apply abelTrans_congr hc.1
    intro x hx
    simp only [abs_of_pos hx.1]
  rw [habs, abelTrans_radonInverse_eq_abelDatum n hn hF c hc]
  unfold abelDatum
  have hS : sphereArea (2 * n - 2) ≠ 0 := ne_of_gt (sphereArea_pos _)
  have hc0 : c ≠ 0 := ne_of_gt hc.1
  have hcpow : c ^ (2 * n - 2) ≠ 0 := pow_ne_zero _ hc0
  field_simp

end

end Work.OddRadon
