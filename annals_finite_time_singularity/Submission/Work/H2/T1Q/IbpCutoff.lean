import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.Spaces.Defs
import Submission.Work.H2.T1Q.IbpCutoffDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.H2.T1Q.IbpCutoff`

The angular integration by parts that localises the "hard" (order-five) angular terms of
Elgindi's `Transport1`/`SpecialTransport` pairing to a compact subinterval of `(0, π/2)`.

For `χ` smooth and vanishing off `[δ, π/2-δ]` (`0 < δ ≤ π/4`) and `hf`, `hv` of class `C¹` on
the open interval `(0, π/2)`, the identity

  `∫_θ sin(2θ)^{-q}·(χ hf)·(sin(2θ)·hv')·hv
      = -∫_θ sin(2θ)^{-q}·(χ·((1/2) sin(2θ) hf' + (1-q) cos(2θ) hf)
                              + (1/2) sin(2θ) χ' hf)·hv²`

holds with *both* sides integrable.  Because the cutoff `χ` vanishes identically off
`[δ, π/2-δ] ⊂ (0, π/2)`, the boundary terms of the integration by parts vanish exactly (not
merely in the limit) and no boundary regularity of `hf`, `hv` is needed at `0` or `π/2`.

The proof has three parts, all in the file:

* `ibpCutoff_integrable` — both integrands are supported in `[δ, π/2-δ]` (`χ` vanishes off it,
  and `deriv χ` vanishes wherever `χ` is locally `0`) and continuous there, hence integrable on
  `Iθ = [0, π/2]`;
* `ibpCutoff_deriv` — on `(0, π/2)` the primitive `IbpPrim q χ hf hv` has derivative
  `IbpG q χ hf hv + IbpK q χ hf hv`;
* the fundamental theorem of calculus on `[0, π/2]` in its one-sided/tendsto form, the boundary
  terms of the primitive vanishing (`ibpCutoff_prim_tendsto_zero_right/left`).

The objects `IbpG`, `IbpK`, `IbpPrim` live in `Submission.Work.H2.T1Q.IbpCutoffDefs`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.H2.T1Q

/-- `sin (2θ) > 0` on the open interval `(0, π/2)`. -/
lemma ibpCutoff_sin_two_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- A function vanishing off the compact interval `[a,b] ⊂ (0, π/2)` and continuous there is
integrable on `Iθ = [0, π/2]`. -/
lemma ibpCutoff_integrableOn_Iθ_of_continuousOn_Icc {a b : ℝ} (ha : 0 < a) (hb : b < π / 2)
    {f : ℝ → ℝ} (hvan : ∀ θ : ℝ, θ ∉ Set.Icc a b → f θ = 0)
    (hcont : ContinuousOn f (Set.Icc a b)) : IntegrableOn f Work.Spaces.Iθ := by
  have hsub : Set.Icc a b ⊆ Set.Icc (0 : ℝ) (π / 2) :=
    fun θ hθ => ⟨by linarith [hθ.1, ha], by linarith [hθ.2, hb, Real.pi_pos]⟩
  have h1 : IntegrableOn f (Set.Icc a b) := hcont.integrableOn_compact isCompact_Icc
  have h2 : IntegrableOn f (Set.Icc (0 : ℝ) (π / 2) \ Set.Icc a b) := by
    refine IntegrableOn.congr_fun (f := fun _ : ℝ => (0 : ℝ)) integrableOn_zero ?_ ?_
    · intro x hx
      exact (hvan x hx.2).symm
    · exact measurableSet_Icc.diff measurableSet_Icc
  have h3 : IntegrableOn f (Set.Icc a b ∪ (Set.Icc (0 : ℝ) (π / 2) \ Set.Icc a b)) :=
    h1.union h2
  rwa [Set.union_sdiff_cancel hsub] at h3

/-- `deriv χ` vanishes at every point where `χ` is locally `0`. -/
lemma ibpCutoff_deriv_eq_zero_of_eventually_eq_zero {χ : ℝ → ℝ} {θ : ℝ}
    (h : χ =ᶠ[𝓝 θ] (fun _ : ℝ => (0 : ℝ))) : deriv χ θ = 0 := by
  rw [h.deriv_eq, deriv_const]

/-- **The primitive.**  On the open interval `(0, π/2)` the derivative of the primitive
`IbpPrim q χ hf hv` is `IbpG q χ hf hv + IbpK q χ hf hv`. -/
lemma ibpCutoff_deriv {q : ℝ} {χ hf hv : ℝ → ℝ} {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2))
    (hχ : DifferentiableAt ℝ χ θ) (hhf : DifferentiableAt ℝ hf θ) (hhv : DifferentiableAt ℝ hv θ) :
    HasDerivAt (IbpPrim q χ hf hv) (IbpG q χ hf hv θ + IbpK q χ hf hv θ) θ := by
  have hsin : 0 < Real.sin (2 * θ) := ibpCutoff_sin_two_pos hθ
  have hsinne : Real.sin (2 * θ) ≠ 0 := ne_of_gt hsin
  have hs2 : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (2 * Real.cos (2 * θ)) θ := by
    have h1 : HasDerivAt (fun t : ℝ => 2 * t) (2 : ℝ) θ := by
      simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
    have h := (Real.hasDerivAt_sin (2 * θ)).comp θ h1
    simpa only [Function.comp_def, mul_comm] using h
  have hpow : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ (1 - q))
      ((1 - q) * (Real.sin (2 * θ)) ^ (1 - q - 1) * (2 * Real.cos (2 * θ))) θ := by
    have h := (Real.hasDerivAt_rpow_const (x := Real.sin (2 * θ)) (p := 1 - q)
      (Or.inl hsinne)).comp θ hs2
    simpa only [Function.comp_def] using h
  have hdχ : HasDerivAt χ (deriv χ θ) θ := hχ.hasDerivAt
  have hdhf : HasDerivAt hf (deriv hf θ) θ := hhf.hasDerivAt
  have hdhv : HasDerivAt hv (deriv hv θ) θ := hhv.hasDerivAt
  have hχhf : HasDerivAt (fun t => χ t * hf t) (deriv χ θ * hf θ + χ θ * deriv hf θ) θ :=
    hdχ.mul hdhf
  have hv2 : HasDerivAt (fun t : ℝ => (hv t) ^ 2) (2 * hv θ * deriv hv θ) θ := by
    have h : HasDerivAt (fun t : ℝ => hv t * hv t)
        (deriv hv θ * hv θ + hv θ * deriv hv θ) θ := hdhv.mul hdhv
    convert h using 1
    · funext t; ring
    · ring
  have h1 : HasDerivAt (fun t => (1 / 2) * (Real.sin (2 * t)) ^ (1 - q))
      ((1 / 2) * ((1 - q) * (Real.sin (2 * θ)) ^ (1 - q - 1) * (2 * Real.cos (2 * θ)))) θ :=
    hpow.const_mul (1 / 2)
  have h2 : HasDerivAt (fun t => (1 / 2) * (Real.sin (2 * t)) ^ (1 - q) * (χ t * hf t))
      ((1 / 2) * ((1 - q) * (Real.sin (2 * θ)) ^ (1 - q - 1) * (2 * Real.cos (2 * θ)))
          * (χ θ * hf θ)
        + (1 / 2) * (Real.sin (2 * θ)) ^ (1 - q) * (deriv χ θ * hf θ + χ θ * deriv hf θ)) θ :=
    h1.mul hχhf
  have h3 : HasDerivAt
      (fun t => (1 / 2) * (Real.sin (2 * t)) ^ (1 - q) * (χ t * hf t) * (hv t) ^ 2)
      (((1 / 2) * ((1 - q) * (Real.sin (2 * θ)) ^ (1 - q - 1) * (2 * Real.cos (2 * θ)))
            * (χ θ * hf θ)
          + (1 / 2) * (Real.sin (2 * θ)) ^ (1 - q) * (deriv χ θ * hf θ + χ θ * deriv hf θ))
          * (hv θ) ^ 2
        + ((1 / 2) * (Real.sin (2 * θ)) ^ (1 - q) * (χ θ * hf θ))
            * (2 * hv θ * deriv hv θ)) θ :=
    h2.mul hv2
  have hA : (Real.sin (2 * θ)) ^ (-q) = (Real.sin (2 * θ)) ^ (1 - q - 1) := by
    rw [show (1 : ℝ) - q - 1 = -q by ring]
  have hB : (Real.sin (2 * θ)) ^ (1 - q)
      = (Real.sin (2 * θ)) ^ (1 - q - 1) * Real.sin (2 * θ) := by
    have h1 : (Real.sin (2 * θ)) ^ (1 - q - 1) * Real.sin (2 * θ)
        = (Real.sin (2 * θ)) ^ (1 - q - 1) * (Real.sin (2 * θ)) ^ (1 : ℝ) := by
      rw [Real.rpow_one]
    rw [h1, ← Real.rpow_add hsin, show (1 : ℝ) - q - 1 + 1 = 1 - q by ring]
  have hval : ((1 / 2) * ((1 - q) * (Real.sin (2 * θ)) ^ (1 - q - 1) * (2 * Real.cos (2 * θ)))
          * (χ θ * hf θ)
        + (1 / 2) * (Real.sin (2 * θ)) ^ (1 - q) * (deriv χ θ * hf θ + χ θ * deriv hf θ))
        * (hv θ) ^ 2
        + ((1 / 2) * (Real.sin (2 * θ)) ^ (1 - q) * (χ θ * hf θ))
            * (2 * hv θ * deriv hv θ)
      = IbpG q χ hf hv θ + IbpK q χ hf hv θ := by
    simp only [IbpG, IbpK]
    rw [hA, hB]
    ring
  rw [hval] at h3
  exact h3

/-- **Integrability.**  Both integrands of `IbpCutoff` are integrable on `Iθ`: the cutoff `χ`
localises them to the compact subinterval `[δ, π/2-δ] ⊂ (0, π/2)`, on which every factor is
continuous. -/
lemma ibpCutoff_integrable {q : ℝ} {χ hf hv : ℝ → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    {δ : ℝ} (hδ : 0 < δ) (hδ4 : δ ≤ π / 4)
    (hχ0 : ∀ θ : ℝ, θ ≤ δ → χ θ = 0)
    (hχ2 : ∀ θ : ℝ, π / 2 - δ ≤ θ → χ θ = 0)
    (hf' : ContDiffOn ℝ 1 hf (Set.Ioo 0 (π / 2)))
    (hv' : ContDiffOn ℝ 1 hv (Set.Ioo 0 (π / 2))) :
    IntegrableOn (IbpG q χ hf hv) Work.Spaces.Iθ
      ∧ IntegrableOn (IbpK q χ hf hv) Work.Spaces.Iθ := by
  set K : Set ℝ := Set.Icc δ (π / 2 - δ) with hK
  have : δ ≤ π / 2 - δ := by linarith [hδ4, Real.pi_pos]
  have hbpi : π / 2 - δ < π / 2 := by linarith [hδ]
  have hIcc_sub : K ⊆ Set.Ioo (0 : ℝ) (π / 2) := by
    intro θ hθ
    exact ⟨by linarith [hθ.1, hδ], by linarith [hθ.2, hδ]⟩
  have hχvan : ∀ θ : ℝ, θ ∉ K → χ θ = 0 := by
    intro θ hθ
    rw [hK, Set.mem_Icc, not_and_or] at hθ
    rcases hθ with h | h
    · exact hχ0 θ (le_of_lt (not_le.mp h))
    · exact hχ2 θ (le_of_lt (not_le.mp h))
  have hdχvan : ∀ θ : ℝ, θ ∉ K → deriv χ θ = 0 := by
    intro θ hθ
    rw [hK, Set.mem_Icc, not_and_or] at hθ
    refine ibpCutoff_deriv_eq_zero_of_eventually_eq_zero ?_
    rcases hθ with h | h
    · filter_upwards [isOpen_Iio.mem_nhds (not_le.mp h)] with t ht
      exact hχ0 t (le_of_lt ht)
    · filter_upwards [isOpen_Ioi.mem_nhds (not_le.mp h)] with t ht
      exact hχ2 t (le_of_lt ht)
  have hsin2 : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) K :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have hcos2 : ContinuousOn (fun θ : ℝ => Real.cos (2 * θ)) K :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn
  have hA : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-q)) K :=
    hsin2.rpow_const (fun x hx => Or.inl (ne_of_gt (ibpCutoff_sin_two_pos (hIcc_sub hx))))
  have hχcont : ContinuousOn χ K := hχ.continuous.continuousOn
  have hχdcont : ContinuousOn (deriv χ) K := (hχ.continuous_deriv (by simp)).continuousOn
  have hfcont : ContinuousOn hf K := hf'.continuousOn.mono hIcc_sub
  have hvcont : ContinuousOn hv K := hv'.continuousOn.mono hIcc_sub
  have hdhfcont : ContinuousOn (fun θ : ℝ => deriv hf θ) K :=
    (hf'.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl).mono hIcc_sub
  have hdhvcont : ContinuousOn (fun θ : ℝ => deriv hv θ) K :=
    (hv'.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl).mono hIcc_sub
  have hv2cont : ContinuousOn (fun θ : ℝ => (hv θ) ^ 2) K := hvcont.pow 2
  have hvanG : ∀ θ : ℝ, θ ∉ K → IbpG q χ hf hv θ = 0 := by
    intro θ hθ
    show (Real.sin (2 * θ)) ^ (-q) * (χ θ * hf θ) * (Real.sin (2 * θ) * deriv hv θ) * hv θ = 0
    rw [hχvan θ hθ]
    ring
  have hvanK : ∀ θ : ℝ, θ ∉ K → IbpK q χ hf hv θ = 0 := by
    intro θ hθ
    show (Real.sin (2 * θ)) ^ (-q)
        * (χ θ * ((1 / 2) * (Real.sin (2 * θ) * deriv hf θ)
              + (1 - q) * Real.cos (2 * θ) * hf θ)
            + (1 / 2) * (Real.sin (2 * θ) * deriv χ θ) * hf θ)
        * (hv θ) ^ 2 = 0
    rw [hχvan θ hθ, hdχvan θ hθ]
    ring
  have ht1 : ContinuousOn (fun θ : ℝ => (1 / 2) * (Real.sin (2 * θ) * deriv hf θ)
      + (1 - q) * Real.cos (2 * θ) * hf θ) K :=
    ((hsin2.mul hdhfcont).const_mul (1 / 2)).add ((hcos2.const_mul (1 - q)).mul hfcont)
  have ht2 : ContinuousOn (fun θ : ℝ => (1 / 2) * (Real.sin (2 * θ) * deriv χ θ) * hf θ) K :=
    ((hsin2.mul hχdcont).const_mul (1 / 2)).mul hfcont
  have hcontG : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-q) * (χ θ * hf θ)
      * (Real.sin (2 * θ) * deriv hv θ) * hv θ) K :=
    ((hA.mul (hχcont.mul hfcont)).mul (hsin2.mul hdhvcont)).mul hvcont
  have hcontK : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-q)
      * (χ θ * ((1 / 2) * (Real.sin (2 * θ) * deriv hf θ)
            + (1 - q) * Real.cos (2 * θ) * hf θ)
          + (1 / 2) * (Real.sin (2 * θ) * deriv χ θ) * hf θ)
      * (hv θ) ^ 2) K :=
    (hA.mul ((hχcont.mul ht1).add ht2)).mul hv2cont
  exact ⟨ibpCutoff_integrableOn_Iθ_of_continuousOn_Icc hδ hbpi hvanG hcontG,
    ibpCutoff_integrableOn_Iθ_of_continuousOn_Icc hδ hbpi hvanK hcontK⟩

/-- The primitive vanishes at `0⁺`, because `χ = 0` on `[0, δ]`. -/
lemma ibpCutoff_prim_tendsto_zero_right {q : ℝ} {χ hf hv : ℝ → ℝ}
    {δ : ℝ} (hδ : 0 < δ) (hχ0 : ∀ θ : ℝ, θ ≤ δ → χ θ = 0) :
    Tendsto (IbpPrim q χ hf hv) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝[>] (0 : ℝ)] (IbpPrim q χ hf hv) := by
    filter_upwards [Ioo_mem_nhdsGT hδ] with θ hθ
    simp only [IbpPrim]
    rw [hχ0 θ (le_of_lt hθ.2)]
    ring
  exact Tendsto.congr' hev tendsto_const_nhds

/-- The primitive vanishes at `(π/2)⁻`, because `χ = 0` on `[π/2-δ, π/2]`. -/
lemma ibpCutoff_prim_tendsto_zero_left {q : ℝ} {χ hf hv : ℝ → ℝ}
    {δ : ℝ} (hδ : 0 < δ) (hχ2 : ∀ θ : ℝ, π / 2 - δ ≤ θ → χ θ = 0) :
    Tendsto (IbpPrim q χ hf hv) (𝓝[<] (π / 2)) (𝓝 0) := by
  have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝[<] (π / 2)] (IbpPrim q χ hf hv) := by
    filter_upwards [Ioo_mem_nhdsLT (show π / 2 - δ < π / 2 by linarith [hδ])] with θ hθ
    simp only [IbpPrim]
    rw [hχ2 θ (le_of_lt hθ.1)]
    ring
  exact Tendsto.congr' hev tendsto_const_nhds

theorem IbpCutoff {q : ℝ} (hq : 0 < q) {χ hf hv : ℝ → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    {δ : ℝ} (hδ : 0 < δ) (hδ4 : δ ≤ π / 4)
    (hχ0 : ∀ θ : ℝ, θ ≤ δ → χ θ = 0)
    (hχ2 : ∀ θ : ℝ, π / 2 - δ ≤ θ → χ θ = 0)
    (hf' : ContDiffOn ℝ 1 hf (Set.Ioo 0 (π / 2)))
    (hv' : ContDiffOn ℝ 1 hv (Set.Ioo 0 (π / 2))) :
    MeasureTheory.IntegrableOn (fun θ => (Real.sin (2 * θ)) ^ (-q) * (χ θ * hf θ)
          * (Real.sin (2 * θ) * deriv hv θ) * hv θ) Work.Spaces.Iθ
      ∧ ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q) * (χ θ * hf θ)
            * (Real.sin (2 * θ) * deriv hv θ) * hv θ
        = -∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
            * (χ θ * ((1 / 2) * (Real.sin (2 * θ) * deriv hf θ)
                + (1 - q) * Real.cos (2 * θ) * hf θ)
              + (1 / 2) * (Real.sin (2 * θ) * deriv χ θ) * hf θ)
            * (hv θ) ^ 2 := by
  have hpi : (0 : ℝ) < π / 2 := by positivity
  have : 0 < q := hq
  obtain ⟨hIntG, hIntK⟩ := ibpCutoff_integrable (q := q) hχ hδ hδ4 hχ0 hχ2 hf' hv'
  have hIcc : ∀ u : ℝ → ℝ, ∫ θ in Work.Spaces.Iθ, u θ = ∫ θ in (0 : ℝ)..(π / 2), u θ := by
    intro u
    rw [show Work.Spaces.Iθ = Set.Icc 0 (π / 2) from rfl,
      MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hpi.le]
  have hderiv : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      HasDerivAt (IbpPrim q χ hf hv) (IbpG q χ hf hv θ + IbpK q χ hf hv θ) θ := by
    intro θ hθ
    exact ibpCutoff_deriv hθ (hχ.contDiffAt.differentiableAt (by simp))
      ((hf'.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hθ))
      ((hv'.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hθ))
  have hint : IntervalIntegrable (fun θ => IbpG q χ hf hv θ + IbpK q χ hf hv θ)
      volume 0 (π / 2) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hpi.le]
    exact hIntG.add hIntK
  have hFTC : ∫ θ in (0 : ℝ)..(π / 2), (IbpG q χ hf hv θ + IbpK q χ hf hv θ) = 0 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hpi hderiv hint
      (ibpCutoff_prim_tendsto_zero_right hδ hχ0) (ibpCutoff_prim_tendsto_zero_left hδ hχ2)
    simpa using h
  have hsplit : ∫ θ in Work.Spaces.Iθ, (IbpG q χ hf hv θ + IbpK q χ hf hv θ)
      = (∫ θ in Work.Spaces.Iθ, IbpG q χ hf hv θ)
        + ∫ θ in Work.Spaces.Iθ, IbpK q χ hf hv θ :=
    MeasureTheory.integral_add hIntG hIntK
  have hsum : (∫ θ in Work.Spaces.Iθ, IbpG q χ hf hv θ)
      + ∫ θ in Work.Spaces.Iθ, IbpK q χ hf hv θ = 0 := by
    rw [← hsplit, hIcc, hFTC]
  change IntegrableOn (IbpG q χ hf hv) Work.Spaces.Iθ
      ∧ ∫ θ in Work.Spaces.Iθ, IbpG q χ hf hv θ = -∫ θ in Work.Spaces.Iθ, IbpK q χ hf hv θ
  exact ⟨hIntG, by linarith⟩

end Work.H2.T1Q
