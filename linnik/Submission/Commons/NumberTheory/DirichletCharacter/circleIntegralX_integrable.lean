import Mathlib.NumberTheory.LSeries.DirichletContinuation

noncomputable section
open Complex Filter Metric Set Function MeasureTheory Topology
open scoped Real Topology Interval
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 0

namespace Commons.NumberTheory.DirichletCharacter

variable {N : ℕ} [NeZero N]

private def Λ (χ : DirichletCharacter ℂ N) : ℂ → ℂ :=
  DirichletCharacter.completedLFunction χ

private def sx (T : ℝ) (x : ℝ) : ℂ := (x : ℂ) + Complex.I * (T : ℂ)
private def c0 (T : ℝ) : ℂ := (2 : ℂ) + Complex.I * (T : ℂ)
private def wθ (R : ℝ) (θ : ℝ) : ℂ := circleMap (0 : ℂ) R θ

private def F_ci (χ : DirichletCharacter ℂ N) (T R x θ : ℝ) : ℂ :=
  deriv (circleMap (0 : ℂ) R) θ •
    (logDeriv (Λ χ) (wθ R θ) *
      (((1 : ℂ) / (sx T x - wθ R θ)) - ((1 : ℂ) / (c0 T - wθ R θ))))

private lemma ne_of_norm_lt {a b : ℂ} {R : ℝ} (ha : ‖a‖ < R) (hb : ‖b‖ = R) : a ≠ b := by
  intro h
  have hlt : ‖b‖ < ‖b‖ := by
    have : ‖a‖ < ‖b‖ := by simpa [hb] using ha
    rwa [h] at this
  exact (lt_irrefl _) hlt

private lemma norm_circleMap {R : ℝ} (hR : 0 < R) (θ : ℝ) : ‖wθ R θ‖ = R := by
  dsimp [wθ]
  rw [norm_circleMap_zero, abs_of_nonneg hR.le]

private lemma cont_deriv_circleMap (R : ℝ) : Continuous (fun θ : ℝ => deriv (circleMap (0 : ℂ) R) θ) := by
  have h : (fun θ : ℝ => deriv (circleMap (0 : ℂ) R) θ) = fun θ : ℝ => circleMap 0 R θ * I := by
    funext θ
    rw [deriv_circleMap]
  rw [h]
  fun_prop

private lemma continuousOn_F_ci (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    {T R : ℝ} (hR : 0 < R)
    (hcirc : ∀ w : ℂ, ‖w‖ = R → Λ χ w ≠ 0)
    (hc0 : ‖c0 T‖ < R) {U : Set ℝ} (hU : ∀ x ∈ U, ‖sx T x‖ < R) :
    ContinuousOn (fun p : ℝ × ℝ => F_ci χ T R p.1 p.2) (U ×ˢ univ) := by
  intro p₀ hp₀
  have hx₀ : ‖sx T p₀.1‖ < R := hU p₀.1 hp₀.1
  have h_dv : ContinuousAt (fun p : ℝ × ℝ => deriv (circleMap (0 : ℂ) R) p.2) p₀ :=
    (cont_deriv_circleMap R).continuousAt.comp (f := fun p : ℝ × ℝ => p.2) (x := p₀)
      (continuousAt_snd (p := p₀))
  have h_w : ContinuousAt (fun p : ℝ × ℝ => wθ R p.2) p₀ := by
    dsimp [wθ]
    have hc : Continuous (fun θ : ℝ => circleMap (0 : ℂ) R θ) := continuous_circleMap (0 : ℂ) R
    exact hc.continuousAt.comp (f := fun p : ℝ × ℝ => p.2) (x := p₀)
      (continuousAt_snd (p := p₀))
  have hldAt : ContinuousAt (fun z : ℂ => logDeriv (Λ χ) z) (wθ R p₀.2) := by
    have hdF : Differentiable ℂ (Λ χ) := by
      simpa [Λ] using (DirichletCharacter.differentiable_completedLFunction (χ := χ) hχ)
    have hderv_c : ContinuousAt (deriv (Λ χ)) (wθ R p₀.2) := (hdF.deriv (wθ R p₀.2)).continuousAt
    have hF_c : ContinuousAt (Λ χ) (wθ R p₀.2) := (hdF (wθ R p₀.2)).continuousAt
    have hdiv : ContinuousAt (fun u : ℂ => deriv (Λ χ) u / Λ χ u) (wθ R p₀.2) :=
      hderv_c.div hF_c (hcirc (wθ R p₀.2) (norm_circleMap hR p₀.2))
    simpa [logDeriv] using hdiv
  have h_ld : ContinuousAt (fun p : ℝ × ℝ => logDeriv (Λ χ) (wθ R p.2)) p₀ :=
    hldAt.comp (f := fun p : ℝ × ℝ => wθ R p.2) (x := p₀) h_w
  have h_sxw : ContinuousAt (fun p : ℝ × ℝ => sx T p.1 - wθ R p.2) p₀ := by
    dsimp [sx, wθ]
    fun_prop
  have h_sxw_ne : sx T p₀.1 - wθ R p₀.2 ≠ 0 :=
    sub_ne_zero.mpr (ne_of_norm_lt hx₀ (norm_circleMap hR p₀.2))
  have h_C1_inv : ContinuousAt (fun p : ℝ × ℝ => (sx T p.1 - wθ R p.2)⁻¹) p₀ :=
    h_sxw.inv₀ h_sxw_ne
  have h_C1 : ContinuousAt (fun p : ℝ × ℝ => (1 : ℂ) / (sx T p.1 - wθ R p.2)) p₀ := by
    simpa [one_div] using h_C1_inv
  have h_c0w : ContinuousAt (fun p : ℝ × ℝ => c0 T - wθ R p.2) p₀ := by
    dsimp [c0, wθ]
    fun_prop
  have h_c0w_ne : c0 T - wθ R p₀.2 ≠ 0 :=
    sub_ne_zero.mpr (ne_of_norm_lt hc0 (norm_circleMap hR p₀.2))
  have h_C2_inv : ContinuousAt (fun p : ℝ × ℝ => (c0 T - wθ R p.2)⁻¹) p₀ :=
    h_c0w.inv₀ h_c0w_ne
  have h_C2 : ContinuousAt (fun p : ℝ × ℝ => (1 : ℂ) / (c0 T - wθ R p.2)) p₀ := by
    simpa [one_div] using h_C2_inv
  have h_diff : ContinuousAt (fun p : ℝ × ℝ =>
      ((1 : ℂ) / (sx T p.1 - wθ R p.2)) - ((1 : ℂ) / (c0 T - wθ R p.2))) p₀ :=
    h_C1.sub h_C2
  have hprod : ContinuousAt (fun p : ℝ × ℝ =>
      logDeriv (Λ χ) (wθ R p.2) * (((1 : ℂ) / (sx T p.1 - wθ R p.2)) -
        ((1 : ℂ) / (c0 T - wθ R p.2)))) p₀ := h_ld.mul h_diff
  have hsmul : ContinuousAt (fun p : ℝ × ℝ =>
      deriv (circleMap (0 : ℂ) R) p.2 •
        (logDeriv (Λ χ) (wθ R p.2) * (((1 : ℂ) / (sx T p.1 - wθ R p.2)) -
          ((1 : ℂ) / (c0 T - wθ R p.2))))) p₀ := h_dv.smul hprod
  have hcat : ContinuousAt (fun p : ℝ × ℝ => F_ci χ T R p.1 p.2) p₀ := by
    simpa [F_ci, sx, c0, wθ] using hsmul
  exact hcat.continuousWithinAt

/-- norm of F_ci is bounded on the rectangle K × [0, 2π] near x0 -/
private lemma F_ci_bounded_rect (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    {T R : ℝ} (hR : 0 < R)
    (hcirc : ∀ w : ℂ, ‖w‖ = R → Λ χ w ≠ 0)
    (hc0 : ‖c0 T‖ < R) {x0 δ : ℝ} (hU : ∀ x ∈ Icc (x0 - δ) (x0 + δ), ‖sx T x‖ < R) :
    ∃ C : ℝ, ∀ x ∈ Icc (x0 - δ) (x0 + δ), ∀ θ ∈ Icc (0 : ℝ) (2 * π),
      ‖F_ci χ T R x θ‖ ≤ C := by
  let K : Set ℝ := Icc (x0 - δ) (x0 + δ)
  let R0 : Set (ℝ × ℝ) := K ×ˢ Icc (0 : ℝ) (2 * π)
  have hcontK : ContinuousOn (fun p : ℝ × ℝ => F_ci χ T R p.1 p.2) (K ×ˢ univ) := by
    exact (continuousOn_F_ci χ hχ hR hcirc hc0 (U := K) hU)
  have hnorm : ContinuousOn (fun p : ℝ × ℝ => ‖F_ci χ T R p.1 p.2‖) R0 := by
    have hsub : R0 ⊆ K ×ˢ univ := by
      intro p hp
      exact ⟨hp.1, trivial⟩
    exact ((hcontK.mono hsub).norm)
  have hcpct : IsCompact R0 := by
    dsimp [R0, K]
    exact isCompact_Icc.prod isCompact_Icc
  rcases hcpct.exists_bound_of_continuousOn hnorm with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro x hx θ hθ
  have hle := hC ⟨x, θ⟩ ⟨hx, hθ⟩
  -- hle : ‖‖F x θ‖‖ ≤ C, and ‖y‖ = y for 0 ≤ y : ℝ
  simpa [Real.norm_eq_abs] using hle

/-- continuity at a point of the parameter integral (DCT) -/
private lemma continuousAt_int_F_ci (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    {T R : ℝ} (hR : 0 < R)
    (hcirc : ∀ w : ℂ, ‖w‖ = R → Λ χ w ≠ 0)
    (hc0 : ‖c0 T‖ < R) {x0 : ℝ} (hx0 : ‖sx T x0‖ < R) :
    ContinuousAt (fun x : ℝ => ∫ θ : ℝ in 0..2 * π, F_ci χ T R x θ) x0 := by
  let gap : ℝ := R - ‖sx T x0‖
  let δ : ℝ := gap / 2
  have hgap : 0 < gap := by
    dsimp [gap]
    linarith
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  let K : Set ℝ := Icc (x0 - δ) (x0 + δ)
  have hU : ∀ x ∈ K, ‖sx T x‖ < R := by
    intro x hx
    have hxd : |x - x0| ≤ δ := by
      rw [abs_le]
      constructor <;> linarith [hx.1, hx.2]
    have hnorm_sub : ‖sx T x - sx T x0‖ ≤ δ := by
      calc
        ‖sx T x - sx T x0‖ = |x - x0| := by
          dsimp [sx]
          have hcast : ((x : ℂ) + Complex.I * (T : ℂ)) -
              ((x0 : ℂ) + Complex.I * (T : ℂ)) = (x - x0 : ℂ) := by ring
          rw [hcast]
          rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ δ := hxd
    have hbnd : ‖sx T x‖ ≤ ‖sx T x0‖ + δ := by
      calc
        ‖sx T x‖ = ‖sx T x0 + (sx T x - sx T x0)‖ := by congr 1; abel
        _ ≤ ‖sx T x0‖ + ‖sx T x - sx T x0‖ := norm_add_le _ _
        _ ≤ ‖sx T x0‖ + δ := by linarith
    -- show ‖sx‖ < R
    have hδ_gap : δ < R - ‖sx T x0‖ := by
      dsimp [δ]
      nlinarith
    nlinarith [hbnd, hδ_gap]
  have hcontK : ContinuousOn (fun p : ℝ × ℝ => F_ci χ T R p.1 p.2) (K ×ˢ univ) :=
    continuousOn_F_ci χ hχ hR hcirc hc0 (U := K) hU
  rcases F_ci_bounded_rect χ hχ hR hcirc hc0 (x0 := x0) (δ := δ) hU with ⟨C, hC⟩
  let V : Set ℝ := Ioo (x0 - δ) (x0 + δ)
  have hV : V ∈ 𝓝 x0 := Ioo_mem_nhds (by linarith) (by linarith)
  have hsubVK : V ⊆ K := by
    intro x hx
    rw [Set.mem_Icc]
    constructor <;> linarith [hx.1, hx.2]
  have hcontV : ContinuousOn (fun p : ℝ × ℝ => F_ci χ T R p.1 p.2) (V ×ˢ univ) :=
    continuousOn_F_ci χ hχ hR hcirc hc0 (U := V) (fun x hx => hU x (hsubVK hx))
  have hθcont : ∀ x ∈ V, Continuous (fun θ : ℝ => F_ci χ T R x θ) := by
    intro x hx
    refine continuous_iff_continuousAt.mpr ?_
    intro θ₀
    have hAt : ContinuousAt (fun p : ℝ × ℝ => F_ci χ T R p.1 p.2) (x, θ₀) :=
      hcontV.continuousAt (prod_mem_nhds (isOpen_Ioo.mem_nhds hx) univ_mem)
    have hcur : ContinuousAt (fun θ : ℝ => (x, θ)) θ₀ := by fun_prop
    exact hAt.comp (f := fun θ : ℝ => (x, θ)) (x := θ₀) hcur
  -- DCT ingredients
  have hF_meas : ∀ᶠ x in 𝓝 x0,
      AEStronglyMeasurable (fun θ : ℝ => F_ci χ T R x θ) (volume.restrict (Ι 0 (2 * π))) := by
    filter_upwards [hV] with x hx
    exact ((hθcont x hx).aestronglyMeasurable.restrict)
  have h_bound : ∀ᶠ x in 𝓝 x0, ∀ᵐ θ : ℝ ∂(volume : Measure ℝ),
      θ ∈ Ι 0 (2 * π) → ‖F_ci χ T R x θ‖ ≤ C := by
    filter_upwards [hV] with x hx
    refine Filter.Eventually.of_forall ?_
    intro θ hθ
    have hθI : θ ∈ Icc (0 : ℝ) (2 * π) := by
      have hle01 : (0 : ℝ) ≤ 2 * π := by positivity
      have : Ι 0 (2 * π) ⊆ Icc 0 (2 * π) := by
        rw [uIoc_of_le hle01]
        exact Set.Ioc_subset_Icc_self
      exact this hθ
    have hxK : x ∈ Icc (x0 - δ) (x0 + δ) := by
      rw [Set.mem_Icc]
      constructor <;> linarith [hx.1, hx.2]
    exact hC x hxK θ hθI
  have bound_int : IntervalIntegrable (fun _ : ℝ => C) volume 0 (2 * π) := intervalIntegrable_const
  have h_cont : ∀ᵐ θ : ℝ ∂(volume : Measure ℝ), θ ∈ Ι 0 (2 * π) →
      ContinuousAt (fun x : ℝ => F_ci χ T R x θ) x0 := by
    refine Filter.Eventually.of_forall ?_
    intro θ hθ
    have hAt : ContinuousAt (fun p : ℝ × ℝ => F_ci χ T R p.1 p.2) (x0, θ) :=
      hcontV.continuousAt (prod_mem_nhds hV univ_mem)
    have hcur : ContinuousAt (fun x : ℝ => (x, θ)) x0 := by fun_prop
    exact hAt.comp (f := fun x : ℝ => (x, θ)) (x := x0) hcur
  exact intervalIntegral.continuousAt_of_dominated_interval (F := fun x θ => F_ci χ T R x θ)
    (x₀ := x0) (bound := fun _ : ℝ => C) (a := 0) (b := 2 * π)
    (μ := (volume : Measure ℝ)) hF_meas h_bound bound_int h_cont

private def CI_int (χ : DirichletCharacter ℂ N) (T R x : ℝ) : ℂ :=
  ∫ θ : ℝ in 0..2 * π, F_ci χ T R x θ

private def CIχ (χ : DirichletCharacter ℂ N) (T R x : ℝ) : ℂ :=
  circleIntegral (fun w : ℂ =>
    (deriv (Λ χ) w / (Λ χ) w) *
      (((1 : ℂ) / (sx T x - w)) - ((1 : ℂ) / (c0 T - w)))) 0 R

private lemma CIχ_eq_integral (χ : DirichletCharacter ℂ N) (T R x : ℝ) :
    CIχ χ T R x = CI_int χ T R x := by
  unfold CIχ CI_int F_ci sx c0 wθ
  -- circleIntegral is ∫ θ of deriv • f(circleMap θ)
  simp [circleIntegral, logDeriv]

private lemma continuousOn_CI_int (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    {T R : ℝ} (hR : 0 < R)
    (hcirc : ∀ w : ℂ, ‖w‖ = R → Λ χ w ≠ 0)
    (hc0 : ‖c0 T‖ < R) :
    ContinuousOn (fun x : ℝ => CI_int χ T R x) {x | ‖sx T x‖ < R} := by
  intro x hx
  exact (continuousAt_int_F_ci χ hχ hR hcirc hc0 hx).continuousWithinAt


/-- the norm of the circle term is continuous on the segment [0, 2] -/
private lemma continuousOn_target_seg (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    {T R : ℝ} (hR : 0 < R)
    (hcirc : ∀ w : ℂ, ‖w‖ = R → Λ χ w ≠ 0)
    (hc0 : ‖c0 T‖ < R)
    (hxU : ∀ x ∈ Set.Icc (0 : ℝ) 2, ‖sx T x‖ < R) :
    ContinuousOn (fun x : ℝ =>
      ‖(((1 : ℂ) / (2 * (Real.pi : ℂ) * Complex.I)) • CIχ χ T R x)‖)
      (Set.Icc (0 : ℝ) 2) := by
  let sc : ℂ := (1 : ℂ) / (2 * (Real.pi : ℂ) * Complex.I)
  have hcontCI : ContinuousOn (fun x : ℝ => CI_int χ T R x) (Set.Icc (0 : ℝ) 2) := by
    exact (continuousOn_CI_int χ hχ hR hcirc hc0).mono (by intro x hx; exact hxU x hx)
  have hnorm : ContinuousOn (fun x : ℝ => ‖CI_int χ T R x‖) (Set.Icc (0 : ℝ) 2) := hcontCI.norm
  have hsmul : (fun x : ℝ => ‖sc • CIχ χ T R x‖) = fun x : ℝ => ‖sc‖ * ‖CI_int χ T R x‖ := by
    funext x
    rw [CIχ_eq_integral, norm_smul]
  rw [hsmul]
  exact continuousOn_const.mul hnorm

private lemma hRbig_two {T R : ℝ} (hRbig : ∀ x ∈ Set.Icc (0 : ℝ) 2, ‖(x : ℂ) + Complex.I * (T : ℂ)‖ < R) :
    ‖c0 T‖ < R := by
  have htwo : (2 : ℝ) ∈ Set.Icc (0 : ℝ) 2 := by rw [Set.mem_Icc]; constructor <;> norm_num
  simpa [c0] using (hRbig 2 htwo)

theorem circleIntegralX_integrable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) (T R : ℝ)
    (hR : 0 < R)
    (hRbig : ∀ x ∈ Set.Icc (0 : ℝ) 2, ‖(x : ℂ) + Complex.I * (T : ℂ)‖ < R)
    (hcirc : ∀ w : ℂ, ‖w‖ = R → DirichletCharacter.completedLFunction χ w ≠ 0) :
    IntervalIntegrable (fun x : ℝ =>
      ‖(((1 : ℂ) / (2 * (Real.pi : ℂ) * Complex.I)) •
        circleIntegral (fun w : ℂ =>
          (deriv (DirichletCharacter.completedLFunction χ) w /
            DirichletCharacter.completedLFunction χ w) *
            (1 / (((x : ℂ) + Complex.I * (T : ℂ)) - w) -
             1 / (((2 : ℂ) + Complex.I * (T : ℂ)) - w))) 0 R)‖)
      MeasureTheory.volume 0 2 := by
  have hc0 : ‖c0 T‖ < R := hRbig_two hRbig
  have hxU : ∀ x ∈ Set.Icc (0 : ℝ) 2, ‖sx T x‖ < R := by
    intro x hx
    simpa [sx] using (hRbig x hx)
  have hcont := continuousOn_target_seg χ hχ hR (by intro w hw; simpa [Λ] using hcirc w hw)
    hc0 hxU
  exact (ContinuousOn.intervalIntegrable_of_Icc (by norm_num : (0 : ℝ) ≤ 2)
    (by simpa [CIχ, Λ, sx, c0] using hcont))

end Commons.NumberTheory.DirichletCharacter