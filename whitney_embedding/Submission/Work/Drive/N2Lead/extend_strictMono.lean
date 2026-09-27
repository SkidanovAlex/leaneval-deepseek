import Mathlib

namespace Work.Drive.N2Lead

/-- A continuous real function that is positive on a closed interval `[a,b]` with `a < b`
is positive on a slightly larger closed interval `[a - δ, b + δ]`. -/
theorem exists_pos_of_pos_on_Icc {g : ℝ → ℝ} (hg : Continuous g) {a b : ℝ} (hab : a < b)
    (hpos : ∀ x ∈ Set.Icc a b, 0 < g x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Set.Icc (a - δ) (b + δ), 0 < g x := by
  have ha : 0 < g a := hpos a ⟨le_rfl, hab.le⟩
  have hb : 0 < g b := hpos b ⟨hab.le, le_rfl⟩
  obtain ⟨ε₁, hε₁, hsub₁⟩ := Metric.mem_nhds_iff.mp ((isOpen_lt continuous_const hg).mem_nhds ha)
  obtain ⟨ε₂, hε₂, hsub₂⟩ := Metric.mem_nhds_iff.mp ((isOpen_lt continuous_const hg).mem_nhds hb)
  have hsub₁' : ∀ x : ℝ, dist x a < ε₁ → 0 < g x := fun x hx => hsub₁ (by rwa [Metric.mem_ball])
  have hsub₂' : ∀ x : ℝ, dist x b < ε₂ → 0 < g x := fun x hx => hsub₂ (by rwa [Metric.mem_ball])
  refine ⟨min ε₁ ε₂ / 2, by positivity, ?_⟩
  intro x hx
  have hδ₁ : min ε₁ ε₂ / 2 < ε₁ := by have := min_le_left ε₁ ε₂; linarith
  have hδ₂ : min ε₁ ε₂ / 2 < ε₂ := by have := min_le_right ε₁ ε₂; linarith
  rcases le_or_gt x a with hxa | hxa
  · apply hsub₁'
    rw [Real.dist_eq, abs_of_nonpos (by linarith [hx.1])]
    linarith [hx.1]
  · rcases le_or_gt b x with hxb | hxb
    · apply hsub₂'
      rw [Real.dist_eq, abs_of_nonneg (by linarith)]
      linarith [hx.2]
    · exact hpos x ⟨hxa.le, hxb.le⟩

/-- A smooth real function that is positive on `[a,b]` (`a < b`) extends to a smooth function
that is positive on all of `ℝ` and agrees with it on `[a,b]`. -/
theorem exists_contDiff_pos_extension {g : ℝ → ℝ}
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) {a b : ℝ} (hab : a < b)
    (hpos : ∀ x ∈ Set.Icc a b, 0 < g x) :
    ∃ v : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v ∧ (∀ x, 0 < v x) ∧
      (∀ x ∈ Set.Icc a b, v x = g x) := by
  obtain ⟨δ, hδ, hδpos⟩ := exists_pos_of_pos_on_Icc hg.continuous hab hpos
  let η : ℝ → ℝ := fun x => Real.smoothTransition ((x - (a - δ)) / δ) *
    Real.smoothTransition (((b + δ) - x) / δ)
  have hη_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η := by
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : ℝ => Real.smoothTransition ((x - (a - δ)) / δ)) :=
      Real.smoothTransition.contDiff.comp (by fun_prop)
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : ℝ => Real.smoothTransition (((b + δ) - x) / δ)) :=
      Real.smoothTransition.contDiff.comp (by fun_prop)
    exact h1.mul h2
  have hη_nonneg : ∀ x, 0 ≤ η x := fun x =>
    mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  have hη_le_one : ∀ x, η x ≤ 1 := fun x => by
    have A := Real.smoothTransition.nonneg ((x - (a - δ)) / δ)
    have B := Real.smoothTransition.le_one ((x - (a - δ)) / δ)
    have C := Real.smoothTransition.nonneg (((b + δ) - x) / δ)
    have D := Real.smoothTransition.le_one (((b + δ) - x) / δ)
    simp only [η]
    nlinarith [A, B, C, D]
  have hη_one : ∀ x ∈ Set.Icc a b, η x = 1 := by
    intro x hx
    have h1 : (1 : ℝ) ≤ (x - (a - δ)) / δ := by rw [le_div_iff₀ hδ]; linarith [hx.1]
    have h2 : (1 : ℝ) ≤ ((b + δ) - x) / δ := by rw [le_div_iff₀ hδ]; linarith [hx.2]
    simp only [η]
    rw [Real.smoothTransition.one_of_one_le h1, Real.smoothTransition.one_of_one_le h2, mul_one]
  have hη_supp : ∀ x, 0 < η x → x ∈ Set.Ioo (a - δ) (b + δ) := by
    intro x hx
    have h1 : 0 < Real.smoothTransition ((x - (a - δ)) / δ) :=
      pos_of_mul_pos_left hx (Real.smoothTransition.nonneg _)
    have h2 : 0 < Real.smoothTransition (((b + δ) - x) / δ) :=
      pos_of_mul_pos_right hx (Real.smoothTransition.nonneg _)
    have ht1 : 0 < (x - (a - δ)) / δ := by
      by_contra h
      rw [not_lt] at h
      rw [Real.smoothTransition.zero_of_nonpos h] at h1
      exact lt_irrefl _ h1
    have ht2 : 0 < ((b + δ) - x) / δ := by
      by_contra h
      rw [not_lt] at h
      rw [Real.smoothTransition.zero_of_nonpos h] at h2
      exact lt_irrefl _ h2
    exact ⟨by have := (div_pos_iff_of_pos_right hδ).mp ht1; linarith,
           by have := (div_pos_iff_of_pos_right hδ).mp ht2; linarith⟩
  refine ⟨fun x => η x * g x + (1 - η x), ?_, ?_, ?_⟩
  · exact (hη_smooth.mul hg).add (contDiff_const.sub hη_smooth)
  · intro x
    by_cases hx : η x = 0
    · simp [hx]
    · have hxpos : 0 < η x := lt_of_le_of_ne (hη_nonneg x) (Ne.symm hx)
      have hmem := hη_supp x hxpos
      have hgx : 0 < g x := hδpos x ⟨le_of_lt hmem.1, le_of_lt hmem.2⟩
      have hp : 0 < η x * g x := mul_pos hxpos hgx
      have hq : 0 ≤ 1 - η x := by linarith [hη_le_one x]
      linarith
  · intro x hx
    show η x * g x + (1 - η x) = g x
    rw [hη_one x hx]
    ring

/-- A smooth primitive of a smooth function is smooth, and its derivative is the function. -/
theorem contDiff_primitive {v : ℝ → ℝ} (hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v) (c a : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => c + ∫ t in a..x, v t) ∧
      ∀ x, deriv (fun x => c + ∫ t in a..x, v t) x = v x := by
  have hv_cont : Continuous v := hv.continuous
  have hderiv : ∀ x, HasDerivAt (fun x => c + ∫ t in a..x, v t) (v x) x := by
    intro x
    exact (intervalIntegral.integral_hasDerivAt_right (hv_cont.intervalIntegrable a x)
      (hv_cont.stronglyMeasurableAtFilter MeasureTheory.volume (nhds x)) hv_cont.continuousAt).const_add c
  have hderiv_eq : deriv (fun x => c + ∫ t in a..x, v t) = v := by
    funext x
    exact (hderiv x).deriv
  constructor
  · rw [contDiff_infty_iff_deriv]
    refine ⟨fun x => (hderiv x).differentiableAt, ?_⟩
    rw [hderiv_eq]
    exact hv
  · intro x
    exact (hderiv x).deriv

/-- A smooth function whose derivative is positive on a closed interval agrees there with a smooth strictly increasing function of the line. -/
theorem extend_strictMono {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hmono : ∀ x ∈ Set.Icc a b, 0 < deriv f x) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ ∧ (∀ x : ℝ, 0 < deriv ψ x) ∧
      (∀ x ∈ Set.Icc a b, ψ x = f x) := by
  have hg_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv f) :=
    (contDiff_infty_iff_deriv.mp hsm).2
  obtain ⟨v, hv_smooth, hv_pos, hv_eq⟩ := exists_contDiff_pos_extension hg_smooth hab hmono
  have hprim := contDiff_primitive hv_smooth (f a) a
  refine ⟨fun x => f a + ∫ t in a..x, v t, hprim.1, ?_, ?_⟩
  · intro x
    rw [hprim.2 x]
    exact hv_pos x
  · intro x hx
    have hdiff : Differentiable ℝ f := (contDiff_infty_iff_deriv.mp hsm).1
    have hcongr : ∫ t in a..x, v t = ∫ t in a..x, deriv f t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hx.1] at ht
      exact hv_eq t ⟨ht.1, ht.2.trans hx.2⟩
    have hFTC : ∫ t in a..x, deriv f t = f x - f a :=
      intervalIntegral.integral_deriv_eq_sub (fun y _ => hdiff.differentiableAt)
        (hg_smooth.continuous.intervalIntegrable a x)
    show f a + ∫ t in a..x, v t = f x
    rw [hcongr, hFTC]
    ring

end Work.Drive.N2Lead
