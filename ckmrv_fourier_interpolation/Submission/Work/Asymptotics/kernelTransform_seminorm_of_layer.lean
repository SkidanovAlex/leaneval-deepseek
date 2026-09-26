import Mathlib
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Asymptotics.junction_iteratedDeriv
import Submission.Work.Asymptotics.Basic

noncomputable section

open MeasureTheory Filter Topology
open scoped Topology

namespace Work.Asymptotics

/-! ## Generic one-sided vanishing and agreement lemmas for `iteratedDeriv` -/

/-- If `g` vanishes on a left-neighbourhood of `ρ`, then `deriv g ρ = 0`. -/
lemma deriv_eq_zero_of_eventually_eq_zero_nhdsLT {g : ℝ → ℂ} {ρ : ℝ}
    (h : ∀ᶠ y in 𝓝[<] ρ, g y = 0) : deriv g ρ = 0 := by
  by_cases hd : DifferentiableAt ℝ g ρ
  · have hρ : g ρ = 0 := by
      have h1 : Tendsto g (𝓝[<] ρ) (𝓝 (g ρ)) :=
        hd.continuousAt.mono_left nhdsWithin_le_nhds
      have h2 : Tendsto g (𝓝[<] ρ) (𝓝 0) :=
        tendsto_const_nhds.congr' (h.mono (fun y hy => hy.symm))
      exact tendsto_nhds_unique h1 h2
    have hslope : Tendsto (slope g ρ) (𝓝[≠] ρ) (𝓝 (deriv g ρ)) :=
      hd.hasDerivAt.tendsto_slope
    have hmono : 𝓝[<] ρ ≤ 𝓝[≠] ρ :=
      nhdsWithin_mono ρ (fun y hy => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact ne_of_lt hy)
    have h0 : Tendsto (slope g ρ) (𝓝[<] ρ) (𝓝 0) := by
      have hev0 : slope g ρ =ᶠ[𝓝[<] ρ] (fun _ => 0) :=
        h.mono (fun y hy => by simp [slope_def_module, hy, hρ])
      exact tendsto_const_nhds.congr' hev0.symm
    exact tendsto_nhds_unique (hslope.mono_left hmono) h0
  · exact deriv_zero_of_not_differentiableAt hd

/-- If `g` vanishes on a right-neighbourhood of `ρ`, then `deriv g ρ = 0`. -/
lemma deriv_eq_zero_of_eventually_eq_zero_nhdsGT {g : ℝ → ℂ} {ρ : ℝ}
    (h : ∀ᶠ y in 𝓝[>] ρ, g y = 0) : deriv g ρ = 0 := by
  by_cases hd : DifferentiableAt ℝ g ρ
  · have hρ : g ρ = 0 := by
      have h1 : Tendsto g (𝓝[>] ρ) (𝓝 (g ρ)) :=
        hd.continuousAt.mono_left nhdsWithin_le_nhds
      have h2 : Tendsto g (𝓝[>] ρ) (𝓝 0) :=
        tendsto_const_nhds.congr' (h.mono (fun y hy => hy.symm))
      exact tendsto_nhds_unique h1 h2
    have hslope : Tendsto (slope g ρ) (𝓝[≠] ρ) (𝓝 (deriv g ρ)) :=
      hd.hasDerivAt.tendsto_slope
    have hmono : 𝓝[>] ρ ≤ 𝓝[≠] ρ :=
      nhdsWithin_mono ρ (fun y hy => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact ne_of_gt hy)
    have h0 : Tendsto (slope g ρ) (𝓝[>] ρ) (𝓝 0) := by
      have hev0 : slope g ρ =ᶠ[𝓝[>] ρ] (fun _ => 0) :=
        h.mono (fun y hy => by simp [slope_def_module, hy, hρ])
      exact tendsto_const_nhds.congr' hev0.symm
    exact tendsto_nhds_unique (hslope.mono_left hmono) h0
  · exact deriv_zero_of_not_differentiableAt hd

/-- If `f` vanishes on the open interval `(a, ρ)` then every positive-order iterated derivative
of `f` at `ρ` vanishes.  (`deriv` is a local notion, so only the one-sided vanishing is used.) -/
lemma iteratedDeriv_succ_eq_zero_of_eqOn_Ioo_left {f : ℝ → ℂ} {a ρ : ℝ} (ha : a < ρ)
    (hf : ∀ y ∈ Set.Ioo a ρ, f y = 0) : ∀ j, iteratedDeriv (j + 1) f ρ = 0 := by
  have hvanish : ∀ j, ∀ y ∈ Set.Ioo a ρ, iteratedDeriv j f y = 0 := by
    intro j
    induction j with
    | zero => intro y hy; rw [iteratedDeriv_zero]; exact hf y hy
    | succ k ih =>
        intro y hy
        rw [iteratedDeriv_succ]
        have hev : iteratedDeriv k f =ᶠ[𝓝 y] (fun _ => (0 : ℂ)) :=
          Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hy) (fun z hz => ih z hz)
        rw [hev.deriv_eq]
        simp
  intro j
  rw [iteratedDeriv_succ]
  refine deriv_eq_zero_of_eventually_eq_zero_nhdsLT ?_
  exact Filter.eventually_of_mem (Ioo_mem_nhdsLT ha) (fun y hy => hvanish j y hy)

/-- Right-hand version: if `f` vanishes on `(ρ, b)` then every positive-order iterated
derivative of `f` at `ρ` vanishes. -/
lemma iteratedDeriv_succ_eq_zero_of_eqOn_Ioo_right {f : ℝ → ℂ} {ρ b : ℝ} (hb : ρ < b)
    (hf : ∀ y ∈ Set.Ioo ρ b, f y = 0) : ∀ j, iteratedDeriv (j + 1) f ρ = 0 := by
  have hvanish : ∀ j, ∀ y ∈ Set.Ioo ρ b, iteratedDeriv j f y = 0 := by
    intro j
    induction j with
    | zero => intro y hy; rw [iteratedDeriv_zero]; exact hf y hy
    | succ k ih =>
        intro y hy
        rw [iteratedDeriv_succ]
        have hev : iteratedDeriv k f =ᶠ[𝓝 y] (fun _ => (0 : ℂ)) :=
          Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hy) (fun z hz => ih z hz)
        rw [hev.deriv_eq]
        simp
  intro j
  rw [iteratedDeriv_succ]
  refine deriv_eq_zero_of_eventually_eq_zero_nhdsGT ?_
  exact Filter.eventually_of_mem (Ioo_mem_nhdsGT hb) (fun y hy => hvanish j y hy)

/-- If `f` agrees with `G` on a neighbourhood of `x`, their iterated derivatives agree at `x`. -/
lemma iteratedDeriv_congr_of_eventuallyEq {f G : ℝ → ℂ} {x : ℝ} (h : f =ᶠ[𝓝 x] G) :
    ∀ j, iteratedDeriv j f x = iteratedDeriv j G x := by
  have halleq : ∀ j, iteratedDeriv j f =ᶠ[𝓝 x] iteratedDeriv j G := by
    intro j
    induction j with
    | zero => simpa [iteratedDeriv_zero] using h
    | succ k ih =>
        rw [iteratedDeriv_succ, iteratedDeriv_succ]
        exact ih.deriv
  intro j
  exact (halleq j).eq_of_nhds

/-- The zero function has vanishing iterated derivatives. -/
lemma iteratedDeriv_zeroFun (l : ℕ) (x : ℝ) :
    iteratedDeriv l (fun _ : ℝ => (0 : ℂ)) x = 0 :=
  iteratedDeriv_const_zero

/-! ## Monotonicity of the integrability of the contour integrand in `|r|` -/

/-- For a fixed kernel `K` and a fixed `τ`, the contour integrand
`t ↦ Work.Kernels.Kaxis K τ t · e^{-π r² t}` is pointwise dominated in norm, on `(0,∞)`, by the same
integrand at a smaller `|r|`; hence its integrability is monotone in `|r|`: if it is integrable
at `r`, it is integrable at every `r'` with `|r| ≤ |r'|`. -/
lemma integrableOn_kaxis_exp_mono_abs {K : UpperHalfPlane → UpperHalfPlane → ℂ} (τ : UpperHalfPlane) {r r' : ℝ} (hr : |r| ≤ |r'|)
    (h : IntegrableOn (fun t : ℝ => Work.Kernels.Kaxis K τ t
      * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0)) :
    IntegrableOn (fun t : ℝ => Work.Kernels.Kaxis K τ t
      * Complex.exp (-(Real.pi * (r' : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0) := by
  have hsq : r ^ 2 ≤ r' ^ 2 := sq_le_sq.mpr hr
  have hcont : Continuous (fun t : ℝ => -(Real.pi * ((r' : ℂ) ^ 2 - (r : ℂ) ^ 2) * (t : ℂ))) := by
    have h1 : Continuous (fun t : ℝ => (Real.pi : ℂ) * ((r' : ℂ) ^ 2 - (r : ℂ) ^ 2) * (t : ℂ)) :=
      continuous_const.mul Complex.continuous_ofReal
    exact h1.neg
  have hCmeas : AEStronglyMeasurable
      (fun t : ℝ => Complex.exp (-(Real.pi * ((r' : ℂ) ^ 2 - (r : ℂ) ^ 2) * (t : ℂ))))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (Complex.continuous_exp.comp hcont).aestronglyMeasurable
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => Work.Kernels.Kaxis K τ t * Complex.exp (-(Real.pi * (r' : ℂ) ^ 2 * (t : ℂ))))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    refine (h.aestronglyMeasurable.mul hCmeas).congr (Filter.Eventually.of_forall (fun t => ?_))
    simp only [Pi.mul_apply]
    have harg : -(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))
        + -(Real.pi * ((r' : ℂ) ^ 2 - (r : ℂ) ^ 2) * (t : ℂ))
        = -(Real.pi * (r' : ℂ) ^ 2 * (t : ℂ)) := by ring
    rw [mul_assoc, ← Complex.exp_add, harg]
  have hbnd : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ‖Work.Kernels.Kaxis K τ t * Complex.exp (-(Real.pi * (r' : ℂ) ^ 2 * (t : ℂ)))‖
        ≤ ‖Work.Kernels.Kaxis K τ t * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))‖ := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 ≤ t := le_of_lt ht
    have harg' : -(Real.pi * (r' : ℂ) ^ 2 * (t : ℂ)) = ((-(Real.pi * r' ^ 2 * t) : ℝ) : ℂ) := by
      push_cast; ring
    have hargr : -(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)) = ((-(Real.pi * r ^ 2 * t) : ℝ) : ℂ) := by
      push_cast; ring
    have hexp : Real.exp (-(Real.pi * r' ^ 2 * t)) ≤ Real.exp (-(Real.pi * r ^ 2 * t)) := by
      apply Real.exp_le_exp.mpr
      have h1 : Real.pi * r ^ 2 * t ≤ Real.pi * r' ^ 2 * t := by
        apply mul_le_mul_of_nonneg_right _ ht0
        exact mul_le_mul_of_nonneg_left hsq (le_of_lt Real.pi_pos)
      linarith
    rw [norm_mul, norm_mul, harg', hargr, Complex.norm_exp_ofReal, Complex.norm_exp_ofReal]
    exact mul_le_mul_of_nonneg_left hexp (norm_nonneg _)
  exact MeasureTheory.Integrable.mono h hmeas hbnd

/-- **Transfer of the seminorm bound from the layer to the naive contour integral.**  Suppose
`F₂` is a layer for `K = Kfun ℓ d` on `𝒟` in the sense of CKMRV Proposition 4.6: it agrees with
the naive Bochner integral `kernelTransform K τ r` on the absolutely convergent range
`r = 0 ∨ d = 8 ∨ 2 < r²`, and — more generally — at every `(τ,r) ∈ 𝒟 × ℝ` at which the contour
integrand `t ↦ K(τ,it)e^{-πr²t}` is integrable; and suppose its `r`-seminorms have moderate
growth on `𝒟`.  Then the same bound holds for the naive contour integral
`r ↦ kernelTransform K τ r` itself, with the *same* constants.

The point is that `kernelTransform` is `0` wherever the integrand is not integrable (Mathlib's
Bochner integral is `0` on non-integrable functions), and the set of `r` at which the integrand
is integrable is a threshold set in `|r|` (increasing `|r|` only decreases the integrand
pointwise).  Hence the naive transform agrees with `F₂` strictly outside a threshold `ρ` and
vanishes strictly inside it; away from `±ρ` one is in the interior of one of the two pieces so
the iterated derivatives agree, and at `±ρ` the function vanishes on a whole side, which forces
*all* its iterated derivatives at `±ρ` to be `0` (`deriv` is a local notion, so only the
one-sided vanishing is needed), while the value at `±ρ` is either `0` or `F₂`'s, hence bounded
by the seminorm bound at `r = ±ρ`. -/
theorem kernelTransform_seminorm_of_layer (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (F₂ : UpperHalfPlane → ℝ → ℂ)
    (hagree : ∀ (τ : UpperHalfPlane) (r : ℝ), τ ∈ Work.Asymptotics.DomainD →
      (r = 0 ∨ d = 8 ∨ 2 < r ^ 2) →
        F₂ τ r = Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) τ r)
    (hagree' : ∀ (τ : UpperHalfPlane) (r : ℝ), τ ∈ Work.Asymptotics.DomainD →
      MeasureTheory.IntegrableOn (fun t : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
          * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0) →
        F₂ τ r = Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) τ r)
    (hsemi : ∀ k l : ℕ, ∃ α β γ δ : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ 0 ≤ δ ∧
      ∀ (τ : UpperHalfPlane) (r : ℝ), τ ∈ Work.Asymptotics.DomainD →
        (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => F₂ τ s) r‖
          ≤ α * (τ.im) ^ (-β) + γ * (‖(τ : ℂ)‖) ^ δ) :
    ∀ k l : ℕ, ∃ α β γ δ : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ 0 ≤ δ ∧
      ∀ (τ : UpperHalfPlane) (r : ℝ), τ ∈ Work.Asymptotics.DomainD →
        (|r| ^ k) * ‖iteratedDeriv l
            (fun s : ℝ => Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) τ s) r‖
          ≤ α * (τ.im) ^ (-β) + γ * (‖(τ : ℂ)‖) ^ δ := by
  have _hd : d = 8 ∨ d = 24 := hd
  intro k l
  obtain ⟨α, β, γ, δ, hα, hβ, hγ, hδ, hbound⟩ := hsemi k l
  refine ⟨α, β, γ, δ, hα, hβ, hγ, hδ, ?_⟩
  intro τ r hτ
  set K : UpperHalfPlane → UpperHalfPlane → ℂ := Work.Kernels.Kfun ℓ d with hK
  set G : ℝ → ℂ := fun s => F₂ τ s with hG
  set gg : ℝ → ℂ := fun s => Work.Kernels.kernelTransform K τ s with hgg
  set P : ℝ → Prop := fun s => MeasureTheory.IntegrableOn
      (fun t : ℝ => Work.Kernels.Kaxis K τ t
        * Complex.exp (-(Real.pi * (s : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0) with hP
  have hPdef : ∀ s, P s = MeasureTheory.IntegrableOn
      (fun t : ℝ => Work.Kernels.Kaxis K τ t
        * Complex.exp (-(Real.pi * (s : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0) := fun s => rfl
  have hRHSnn : (0:ℝ) ≤ α * (τ.im) ^ (-β) + γ * (‖(τ : ℂ)‖) ^ δ := by
    have h1 : 0 ≤ α * (τ.im) ^ (-β) := mul_nonneg hα (Real.rpow_nonneg τ.im_pos.le _)
    have h2 : 0 ≤ γ * (‖(τ : ℂ)‖) ^ δ := mul_nonneg hγ (Real.rpow_nonneg (norm_nonneg _) _)
    linarith
  have hboundG : ∀ s : ℝ, (|s| ^ k) * ‖iteratedDeriv l G s‖
      ≤ α * (τ.im) ^ (-β) + γ * (‖(τ : ℂ)‖) ^ δ := fun s => hbound τ s hτ
  have hP0 : ∀ s, ¬ P s → gg s = 0 := by
    intro s hs
    have hI : ¬ MeasureTheory.IntegrableOn
        (fun t : ℝ => Work.Kernels.Kaxis K τ t
          * Complex.exp (-(Real.pi * (s : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0) := by
      rwa [hPdef s] at hs
    have hz : (∫ t in Set.Ioi (0:ℝ), Work.Kernels.Kaxis K τ t
        * Complex.exp (-(Real.pi * (s : ℂ) ^ 2 * (t : ℂ)))) = 0 :=
      integral_undef hI
    rw [hgg]
    simp only [Work.Kernels.kernelTransform, hz, mul_zero]
  have hP1 : ∀ s, P s → gg s = G s := by
    intro s hs
    rw [hgg, hG]
    exact (hagree' τ s hτ hs).symm
  have hgg0 : gg 0 = G 0 := by
    rw [hgg, hG]
    exact (hagree τ 0 hτ (Or.inl rfl)).symm
  have hmono : ∀ s s', P s → |s| ≤ |s'| → P s' := by
    intro s s' hs hsle
    rw [hPdef s'] 
    exact integrableOn_kaxis_exp_mono_abs (K := K) τ hsle (by rwa [hPdef s] at hs)
  by_cases hne : ∃ s, P s
  · set S : Set ℝ := {b | ∃ s, P s ∧ b = |s|} with hS
    have hmemS : ∀ b, b ∈ S ↔ ∃ s, P s ∧ b = |s| := fun b => Iff.rfl
    have hSne : S.Nonempty := by
      obtain ⟨s, hs⟩ := hne; exact ⟨|s|, s, hs, rfl⟩
    have hSbdd : BddBelow S := ⟨0, by rintro b ⟨s, _, rfl⟩; positivity⟩
    set ρ : ℝ := sInf S with hρ
    have hρnn : 0 ≤ ρ := by
      rw [hρ]
      exact le_csInf hSne (by rintro b ⟨s, _, rfl⟩; positivity)
    have hbig : ∀ s, ρ < |s| → P s := by
      intro s hs
      have hlt : sInf S < |s| := by rw [← hρ]; exact hs
      obtain ⟨b, hbS, hblt⟩ := (csInf_lt_iff hSbdd hSne).mp hlt
      obtain ⟨s₀, hPs₀, hb_eq⟩ := hbS
      exact hmono s₀ s hPs₀ (le_of_lt (by rw [hb_eq] at hblt; exact hblt))
    have hsmall : ∀ s, |s| < ρ → ¬ P s := by
      intro s hs hPs
      have hle : ρ ≤ |s| := by
        rw [hρ]
        exact csInf_le hSbdd ⟨s, hPs, rfl⟩
      linarith
    have hzero : ∀ s, |s| < ρ → gg s = 0 := fun s hs => hP0 s (hsmall s hs)
    have hgood : ∀ s, ρ < |s| → gg s = G s := fun s hs => hP1 s (hbig s hs)
    rcases eq_or_lt_of_le hρnn with hρ0 | hρpos
    · -- threshold 0: the transform agrees with `F₂` everywhere
      have hggG : gg = G := by
        funext s
        rcases eq_or_ne s 0 with h | h
        · subst h; exact hgg0
        · exact hgood s (by rw [← hρ0]; exact abs_pos.mpr h)
      rw [hggG]
      exact hboundG r
    · -- threshold `ρ > 0`
      rcases lt_trichotomy r ρ with hr | hr | hr
      · rcases lt_trichotomy r (-ρ) with hr' | hr' | hr'
        · -- r < -ρ : interior of the "good" half-line
          have habs : ρ < |r| := by rw [abs_of_neg (by linarith)]; linarith
          have hGG : gg =ᶠ[𝓝 r] G := by
            refine Filter.eventually_of_mem ?_ (fun s hs => hgood s hs)
            exact IsOpen.mem_nhds (isOpen_lt continuous_const continuous_abs) habs
          rw [iteratedDeriv_congr_of_eventuallyEq hGG l]
          exact hboundG r
        · -- r = -ρ
          subst hr'
          rcases l with _ | l'
          · simp only [iteratedDeriv_zero]
            by_cases hP : P (-ρ)
            · rw [hP1 (-ρ) hP]
              simpa only [iteratedDeriv_zero] using hboundG (-ρ)
            · rw [hP0 (-ρ) hP, norm_zero, mul_zero]
              exact hRHSnn
          · have hz : iteratedDeriv (l' + 1) gg (-ρ) = 0 :=
              iteratedDeriv_succ_eq_zero_of_eqOn_Ioo_right (by linarith : -ρ < ρ)
                (fun y hy => hzero y (by
                  rw [abs_lt]; exact ⟨by linarith [hy.1], hy.2⟩)) l'
            rw [hz, norm_zero, mul_zero]
            exact hRHSnn
        · -- -ρ < r < ρ : interior of the vanishing interval
          have habs : |r| < ρ := by rw [abs_lt]; exact ⟨by linarith, hr⟩
          have hGG : gg =ᶠ[𝓝 r] (fun _ => (0:ℂ)) := by
            refine Filter.eventually_of_mem ?_ (fun s hs => hzero s hs)
            exact IsOpen.mem_nhds (isOpen_lt continuous_abs continuous_const) habs
          rw [iteratedDeriv_congr_of_eventuallyEq hGG l, iteratedDeriv_zeroFun]
          simp only [norm_zero, mul_zero]
          exact hRHSnn
      · -- r = ρ
        subst hr
        rcases l with _ | l'
        · simp only [iteratedDeriv_zero]
          by_cases hP : P ρ
          · rw [hP1 ρ hP]
            simpa only [iteratedDeriv_zero] using hboundG ρ
          · rw [hP0 ρ hP, norm_zero, mul_zero]
            exact hRHSnn
        · have hz : iteratedDeriv (l' + 1) gg ρ = 0 :=
            iteratedDeriv_succ_eq_zero_of_eqOn_Ioo_left hρpos
              (fun y hy => hzero y (by rw [abs_of_pos hy.1]; exact hy.2)) l'
          rw [hz, norm_zero, mul_zero]
          exact hRHSnn
      · -- r > ρ : interior of the "good" half-line
        have habs : ρ < |r| := by rw [abs_of_pos (by linarith)]; linarith
        have hGG : gg =ᶠ[𝓝 r] G := by
          refine Filter.eventually_of_mem ?_ (fun s hs => hgood s hs)
          exact IsOpen.mem_nhds (isOpen_lt continuous_const continuous_abs) habs
        rw [iteratedDeriv_congr_of_eventuallyEq hGG l]
        exact hboundG r
  · -- no integrable point at all: the transform vanishes identically
    have hnone : ∀ s, ¬ P s := fun s hs => hne ⟨s, hs⟩
    have hg0 : gg = fun _ => (0:ℂ) := funext (fun s => hP0 s (hnone s))
    rw [hg0, iteratedDeriv_zeroFun]
    simp only [norm_zero, mul_zero]
    exact hRHSnn


end Work.Asymptotics
