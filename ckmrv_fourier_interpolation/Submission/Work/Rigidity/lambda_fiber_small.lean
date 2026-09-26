/-
# The fibres of `λ` over small values are `Γ(2)`-orbits

The modular lambda function `λ = θ₁₀⁴/θ₀₀⁴ = Work.Kernels.lambdaFun` is invariant under the
principal congruence subgroup `Γ(2)`, so its fibres are unions of `Γ(2)`-orbits.  This file
proves that *near the cusp* the fibres are single orbits, which is the input needed to start
the "open and closed" argument of `Work.Rigidity.lambda_fiber_orbit` at the cusp.

The argument has three ingredients, all available in the workspace:

* `lambdaSeries_locally_injective`: the `q`-expansion `lambdaSeries` is injective in a
  neighbourhood of `q = 0`, because it is strictly differentiable there with derivative
  `16 ≠ 0`.
* `lambdaFun_injective_of_im_large`: consequently `λ` is injective up to `Γ(2)` far up in the
  cusp: `λ τ = λ τ'` and `Im τ, Im τ' > Y` force `e^{π i τ} = e^{π i τ'}`, i.e. `τ' = τ + 2k`,
  and the translation `eA (-k) ∈ Γ(2)` moves `τ` to `τ'`.
* `lambda_FDom_lower_bound_zero`: on the fundamental domain `FDom`, small values of `λ`
  force a large imaginary part (the `w = 0` companion of `FDom_im_lower_bound`), so every
  point of a small fibre can be moved by `Γ(2)` into the region where the second ingredient
  applies.

Combining the three with the reduction `lambda_fdom_reduction` to the fundamental domain
gives `lambda_fiber_small`.
-/
import Mathlib
import Submission.Work.Rigidity.LambdaFiberDefs
import Submission.Work.Rigidity.lambda_fdom_reduction
import Submission.Work.Rigidity.lambdaFun_eq_lambdaSeries
import Submission.Work.Rigidity.lambda_local_surjective
import Submission.Work.Rigidity.lambdaFun_div_qParam_tendsto
import Submission.Work.Rigidity.lambda_local_inverse
import Submission.Work.Rigidity.lambda_fiber_close

namespace Work.Rigidity

open UpperHalfPlane ModularGroup Matrix Filter Topology
open scoped MatrixGroups

noncomputable section

open Work.Kernels Work.Kernels.LogLambda

/-! ## The `q`-expansion is injective near the origin -/

/-- **`lambdaSeries` is injective near `0`.**  It is strictly differentiable at the origin
with derivative `16 ≠ 0`, so its local inverse is a left inverse on a neighbourhood of `0`
and two sufficiently small arguments with the same value must be equal. -/
lemma lambdaSeries_locally_injective :
    ∃ r : ℝ, 0 < r ∧ ∀ z z' : ℂ, ‖z‖ < r → ‖z'‖ < r →
      lambdaSeries z = lambdaSeries z' → z = z' := by
  have h := lambdaSeries_hasStrictDerivAt
  have h16 : (16 : ℂ) ≠ 0 := by norm_num
  have hleft : ∀ᶠ z in 𝓝 (0 : ℂ),
      HasStrictDerivAt.localInverse lambdaSeries 16 0 h h16 (lambdaSeries z) = z :=
    h.eventually_left_inverse h16
  obtain ⟨r, hr, hrf⟩ := Metric.eventually_nhds_iff.mp hleft
  refine ⟨r, hr, fun z z' hz hz' heq => ?_⟩
  have h1 := hrf (by simpa using hz)
  have h2 := hrf (by simpa using hz')
  rw [heq, h2] at h1
  exact h1.symm

/-! ## Injectivity of `λ` far up in the cusp -/

/-- **`λ` is injective up to `Γ(2)` far up in the cusp.**  For `Y` large enough that
`e^{-πY}` lies inside the radius of injectivity of the `q`-expansion, two points of imaginary
part `> Y` with the same `λ`-value have the same `q`-value `e^{π i τ}`, hence differ by a
translation `eA k = [[1, 2k], [0, 1]] ∈ Γ(2)` (equivalently `τ - τ' ∈ 2ℤ`). -/
theorem lambdaFun_injective_of_im_large :
    ∃ Y : ℝ, 0 < Y ∧ ∀ τ τ' : UpperHalfPlane, Y < τ.im → Y < τ'.im →
      lambdaFun τ = lambdaFun τ' →
        ∃ γ ∈ CongruenceSubgroup.Gamma 2, γ • τ = τ' := by
  obtain ⟨r, hr, hinj⟩ := lambdaSeries_locally_injective
  -- `Y` with `exp (-(π Y)) < r`
  have hYexists : ∃ Y : ℝ, 0 < Y ∧ Real.exp (-(Real.pi * Y)) < r := by
    refine ⟨max 1 (Real.log r⁻¹ / Real.pi + 1), lt_max_of_lt_left one_pos, ?_⟩
    have hlog : Real.exp (-(Real.pi * (Real.log r⁻¹ / Real.pi + 1))) = r / Real.exp Real.pi := by
      have h1 : -(Real.pi * (Real.log r⁻¹ / Real.pi + 1)) = Real.log r - Real.pi := by
        rw [Real.log_inv, neg_div]
        field_simp
        ring
      rw [h1, Real.exp_sub, Real.exp_log hr]
    have hexp_le : Real.exp (-(Real.pi * max 1 (Real.log r⁻¹ / Real.pi + 1)))
        ≤ r / Real.exp Real.pi := by
      rw [← hlog]
      exact Real.exp_le_exp.mpr
        (by nlinarith [Real.pi_pos, le_max_right (1 : ℝ) (Real.log r⁻¹ / Real.pi + 1)])
    refine lt_of_le_of_lt hexp_le ?_
    rw [div_lt_iff₀ (Real.exp_pos Real.pi)]
    nlinarith [Real.one_lt_exp_iff.mpr Real.pi_pos]
  obtain ⟨Y, hYpos, hYr⟩ := hYexists
  refine ⟨Y, hYpos, fun τ τ' hτ hτ' heq => ?_⟩
  -- the two `q`-values `e^{π i τ}`, `e^{π i τ'}` are in the injectivity radius of `lambdaSeries`
  have hnorm : ∀ σ : ℍ, ‖Complex.exp (Real.pi * Complex.I * (σ : ℂ))‖
      = Real.exp (-(Real.pi * σ.im)) := by
    intro σ
    rw [Complex.norm_exp]
    congr 1
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, UpperHalfPlane.coe_im]
    ring
  have hsmall : ∀ σ : ℍ, Y < σ.im →
      ‖Complex.exp (Real.pi * Complex.I * (σ : ℂ))‖ < r := by
    intro σ hσ
    rw [hnorm σ]
    exact lt_of_lt_of_le (Real.exp_lt_exp.mpr (by nlinarith [Real.pi_pos, hσ])) hYr.le
  have hζ : ‖Complex.exp (Real.pi * Complex.I * (τ : ℂ))‖ < r := hsmall τ hτ
  have hζ' : ‖Complex.exp (Real.pi * Complex.I * (τ' : ℂ))‖ < r := hsmall τ' hτ'
  have hval : lambdaSeries (Complex.exp (Real.pi * Complex.I * (τ : ℂ)))
      = lambdaSeries (Complex.exp (Real.pi * Complex.I * (τ' : ℂ))) := by
    rw [← lambdaFun_eq_lambdaSeries τ, ← lambdaFun_eq_lambdaSeries τ', heq]
  have heqexp : Complex.exp (Real.pi * Complex.I * (τ : ℂ))
      = Complex.exp (Real.pi * Complex.I * (τ' : ℂ)) := hinj _ _ hζ hζ' hval
  -- hence `τ - τ' ∈ 2ℤ`
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp heqexp
  have hpiI : (Real.pi : ℂ) * Complex.I ≠ 0 := by
    simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero, Complex.I_ne_zero]
  have hsub : (τ : ℂ) - (τ' : ℂ) = (n : ℂ) * 2 := by
    have h2 : (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) / ((Real.pi : ℂ) * Complex.I)
        = (n : ℂ) * 2 := by
      field_simp
    have := congrArg (fun z : ℂ => z / ((Real.pi : ℂ) * Complex.I)) hn
    simp only [add_div, mul_div_cancel_left₀ _ hpiI] at this
    rw [h2] at this
    rw [this]; ring
  refine ⟨eA (-n), eA_mem_Gamma (-n), UpperHalfPlane.ext ?_⟩
  rw [fdom_eA_smul_coe]
  push_cast
  have hcoe : (τ : ℂ) = (τ' : ℂ) + (n : ℂ) * 2 := by
    have := sub_eq_iff_eq_add.mp hsub
    rw [this]; ring
  rw [hcoe]
  ring

/-! ## Small values on the fundamental domain force a large imaginary part -/

/-- **On `FDom` small values of `λ` force a large imaginary part.**  This is the `w = 0`
companion of `FDom_im_lower_bound`: if a sequence of points of `FDom` with `λ → 0` had
bounded imaginary part it would have a subsequence converging to a point `p` of the compact
set `KF 0 M`; since `λ` is continuous and non-vanishing (`lambdaFun_ne_zero`) and tends to
`1` resp. `∞` at the cusps `0` and `±1` (where `p` would have to lie), this is impossible. -/
lemma lambda_FDom_lower_bound_zero (Y : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ τ : UpperHalfPlane, τ ∈ FDom → ‖lambdaFun τ‖ < δ → Y < τ.im := by
  by_contra hcon
  push Not at hcon
  have hseq : ∀ n : ℕ, ∃ τ : ℍ, τ ∈ FDom ∧ ‖lambdaFun τ‖ < 1 / ((n : ℝ) + 1) ∧ τ.im ≤ Y := by
    intro n
    obtain ⟨τ, h1, h2, h3⟩ := hcon (1 / ((n : ℝ) + 1)) (by positivity)
    exact ⟨τ, h1, h2, h3⟩
  choose τ hFD hsmall him using hseq
  set M : ℝ := max Y 1 with hM
  have hmem : ∀ n, (((τ n : ℍ) : ℂ)) ∈ KF 0 M := by
    intro n
    refine ⟨(hFD n).1, ?_, ?_, ?_⟩
    · rw [Complex.normSq_eq_norm_sq]; exact (hFD n).2
    · rw [UpperHalfPlane.coe_im]; exact le_of_lt (τ n).im_pos
    · rw [UpperHalfPlane.coe_im]; exact le_trans (him n) (le_max_left Y 1)
  obtain ⟨p, hpK, ψ, hψmono, hψtend⟩ :=
    (isCompact_KF 0 M).tendsto_subseq (x := fun n => ((τ n : ℍ) : ℂ)) hmem
  -- the norms `‖λ (τ (ψ n))‖` tend to `0`
  have hnorm0 : Tendsto (fun n => ‖lambdaFun (τ (ψ n))‖) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => (hsmall (ψ n)).le) ?_
    exact (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hψmono.tendsto_atTop
  have hval0 : Tendsto (fun n => lambdaFun (τ (ψ n))) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnorm0
  rcases lt_or_ge 0 p.im with hpim | hpim
  · -- the limit lies in the upper half plane: `λ p = 0`, contradicting non-vanishing
    have htendz : Tendsto (fun n => τ (ψ n)) atTop (𝓝 (⟨p, hpim⟩ : ℍ)) := by
      rw [nhds_induced, tendsto_comap_iff]
      simpa [Function.comp_def] using hψtend
    have hcont : Tendsto (fun n => lambdaFun (τ (ψ n))) atTop (𝓝 (lambdaFun ⟨p, hpim⟩)) := by
      have := (mdifferentiable_lambdaFun.continuous.tendsto (⟨p, hpim⟩ : ℍ)).comp htendz
      simpa [Function.comp_def] using this
    exact lambdaFun_ne_zero ⟨p, hpim⟩ (tendsto_nhds_unique hcont hval0)
  · -- the limit lies on the real axis, hence is one of the cusps `0, ±1`
    have hpim0 : p.im = 0 := le_antisymm hpim hpK.2.2.1
    have hpre : |p.re| ≤ 1 := hpK.1
    have hns : Complex.normSq p ≥ |p.re| := hpK.2.1
    have hre2 : p.re ^ 2 ≥ |p.re| := by
      rw [Complex.normSq_apply] at hns
      simpa [hpim0, pow_two] using hns
    have habs : |p.re| = 0 ∨ |p.re| = 1 := by
      have h1 : |p.re| ≤ 1 := hpre
      have h3 : 0 ≤ |p.re| := abs_nonneg _
      have h4 : |p.re| ^ 2 ≥ |p.re| := by simpa [sq_abs] using hre2
      rcases eq_or_lt_of_le h3 with h | h
      · exact Or.inl h.symm
      · refine Or.inr (le_antisymm h1 ?_)
        by_contra hlt
        push Not at hlt
        nlinarith
    rcases habs with h0 | h1
    · -- `p = 0`: `λ` tends to `1`
      have hp0 : p = 0 := by
        have hre : p.re = 0 := abs_eq_zero.mp h0
        rw [Complex.ext_iff]
        exact ⟨by simpa using hre, by simpa using hpim0⟩
      have htend0 : Tendsto (fun n => (((τ (ψ n) : ℍ)) : ℂ)) atTop (𝓝 0) := by
        rw [hp0] at hψtend; exact hψtend
      have hone := lambdaFun_tendsto_one_of_FDom_tendsto_zero (fun n => τ (ψ n))
        (fun n => hFD (ψ n)) htend0
      have huniq : (1 : ℂ) = 0 := tendsto_nhds_unique hone hval0
      norm_num at huniq
    · rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp h1 with h1' | h1'
      · -- `p = 1`: `‖λ‖` tends to `∞`
        have hp1 : p = 1 := by
          have hre : p.re = 1 := by simpa using h1'
          rw [Complex.ext_iff]
          exact ⟨by simpa using hre, by simpa using hpim0⟩
        have htend1 : Tendsto (fun n => (((τ (ψ n) : ℍ)) : ℂ)) atTop (𝓝 1) := by
          rw [hp1] at hψtend; exact hψtend
        have hinf := lambdaFun_norm_tendsto_atTop_of_FDom_tendsto_one (fun n => τ (ψ n))
          (fun n => hFD (ψ n)) htend1
        exact (not_tendsto_atTop_of_tendsto_nhds hnorm0) hinf
      · -- `p = -1`: `‖λ‖` tends to `∞` as well
        have hp1 : p = -1 := by
          have hre : p.re = -1 := by simpa using h1'
          rw [Complex.ext_iff]
          exact ⟨by simpa using hre, by simpa using hpim0⟩
        have htend1 : Tendsto (fun n => (((τ (ψ n) : ℍ)) : ℂ)) atTop (𝓝 (-1)) := by
          rw [hp1] at hψtend; exact hψtend
        have hinf := lambdaFun_norm_tendsto_atTop_of_FDom_tendsto_neg_one (fun n => τ (ψ n))
          (fun n => hFD (ψ n)) htend1
        exact (not_tendsto_atTop_of_tendsto_nhds hnorm0) hinf

/-! ## The target -/

theorem lambda_fiber_small :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w : ℂ, ‖w‖ < δ → ∀ τ τ' : UpperHalfPlane,
      Work.Kernels.lambdaFun τ = w → Work.Kernels.lambdaFun τ' = w →
        ∃ γ ∈ CongruenceSubgroup.Gamma 2, γ • τ = τ' := by
  obtain ⟨Y₀, _hY₀pos, hY₀⟩ := lambdaFun_injective_of_im_large
  obtain ⟨δ, hδpos, hδ⟩ := lambda_FDom_lower_bound_zero Y₀
  refine ⟨δ, hδpos, ?_⟩
  intro w hw τ τ' hτ hτ'
  -- move both points into the fundamental domain
  obtain ⟨γ₁, hγ₁, hτ₁⟩ := lambda_fdom_reduction τ
  obtain ⟨γ₂, hγ₂, hτ₂⟩ := lambda_fdom_reduction τ'
  have hlτ₁ : lambdaFun (γ₁ • τ) = w := by
    rw [lambdaFun_gamma2_invariant γ₁ hγ₁ τ, hτ]
  have hlτ₂ : lambdaFun (γ₂ • τ') = w := by
    rw [lambdaFun_gamma2_invariant γ₂ hγ₂ τ', hτ']
  have him₁ : Y₀ < (γ₁ • τ).im := hδ (γ₁ • τ) hτ₁ (by rw [hlτ₁]; exact hw)
  have him₂ : Y₀ < (γ₂ • τ').im := hδ (γ₂ • τ') hτ₂ (by rw [hlτ₂]; exact hw)
  obtain ⟨γ, hγ, hγeq⟩ := hY₀ (γ₁ • τ) (γ₂ • τ') him₁ him₂ (hlτ₁.trans hlτ₂.symm)
  refine ⟨γ₂⁻¹ * γ * γ₁, mul_mem (mul_mem (inv_mem hγ₂) hγ) hγ₁, ?_⟩
  rw [mul_smul, mul_smul, hγeq, inv_smul_smul]

end

end Work.Rigidity
