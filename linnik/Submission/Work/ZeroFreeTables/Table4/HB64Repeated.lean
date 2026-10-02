import Mathlib
import Submission.Work.NumberTheory.Linnik.scratch_hzero2
import Submission.Work.ZeroFreeTables.hb6Repeated

open Complex DirichletCharacter Metric
open scoped BigOperators

set_option maxHeartbeats 4000000

namespace Work.ZeroFreeTables.Table4

/-- **Window sum with a doubled zero.**

If `χ` is a non-principal Dirichlet character, `u ↦ Re u ≤ β₁` for every zero `u` of the
completed `L`-function of `χ` inside the window `‖1 - u‖ ≤ δ`, and `β₁` itself is a window zero
of multiplicity `≥ 2`, then the window sum of Heath-Brown §6 at `β₁` dominates `2 F(0)`, where
`F(0) = ∫₀^{x₀} f`.

This is the multiplicity-`2` version of `Commons.NumberTheory.Linnik.le_windowSum_of_mem`: the
single term at `β₁` now equals `(mult) · F(0) ≥ 2 F(0)` and every other window term is
non-negative. -/
private theorem winSumTwoMulAux {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {f : ℝ → ℝ} {x₀ L δ β₁ : ℝ} (hL : 0 ≤ L)
    (hF : ∀ z : ℂ, 0 ≤ z.re →
      0 ≤ (∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
    (hβδ : ‖(1:ℂ) + (((β₁ : ℂ)).im : ℂ) * Complex.I - (β₁ : ℂ)‖ ≤ δ)
    (hmult : (2 : ℤ) ≤ (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|(((β₁ : ℂ)).im)| + 2))) (β₁ : ℂ))
    (hzero : ∀ u : ℂ, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|(((β₁ : ℂ)).im)| + 2))) u ≠ 0 →
        ‖(1:ℂ) + (((β₁ : ℂ)).im : ℂ) * Complex.I - u‖ ≤ δ → u.re ≤ β₁) :
    2 * (∫ t in (0:ℝ)..x₀, f t) ≤
      Commons.NumberTheory.Linnik.winSum χ f x₀ L δ (β₁ : ℂ) := by
  classical
  have han : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall 0 (|(((β₁ : ℂ)).im)| + 2)) :=
    fun z _ => (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z
  have hDnn : ∀ u : ℂ, (0:ℤ) ≤ (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall 0 (|(((β₁ : ℂ)).im)| + 2))) u := fun u =>
    (MeromorphicOn.AnalyticOnNhd.divisor_nonneg han) u
  let T : ℂ → ℝ := fun u =>
    ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|(((β₁ : ℂ)).im)| + 2))) u : ℤ) *
      (if ‖(1:ℂ) + (((β₁ : ℂ)).im : ℂ) * Complex.I - u‖ ≤ δ then
        ((∫ t in (0:ℝ)..x₀, Complex.exp (-((((β₁ : ℂ) - u) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
        else 0)
  simp only [Commons.NumberTheory.Linnik.winSum]
  change 2 * (∫ t in (0:ℝ)..x₀, f t) ≤ ∑ᶠ u : ℂ, T u
  have hzshift : ∀ u : ℂ, u.re ≤ ((β₁ : ℂ)).re → 0 ≤ (((((β₁ : ℂ)) - u) * L : ℂ)).re := by
    intro u hu
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    have : 0 ≤ (((β₁ : ℂ)) - u).re := by rw [Complex.sub_re]; linarith
    exact mul_nonneg this hL
  have hTnn : ∀ u : ℂ, 0 ≤ T u := by
    intro u
    simp only [T]
    by_cases hdu : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|(((β₁ : ℂ)).im)| + 2))) u = 0
    · rw [hdu]; norm_num
    · by_cases hw : ‖(1:ℂ) + (((β₁ : ℂ)).im : ℂ) * Complex.I - u‖ ≤ δ
      · rw [if_pos hw]
        refine mul_nonneg ?_ (hF _ (hzshift u ?_))
        · exact_mod_cast hDnn u
        · simpa using hzero u hdu hw
      · rw [if_neg hw, mul_zero]
  have hIf : 0 ≤ ∫ t in (0:ℝ)..x₀, f t := by
    have h := hF 0 (le_refl 0)
    simp only [zero_mul, neg_zero, Complex.exp_zero, one_mul] at h
    rwa [intervalIntegral.integral_ofReal, Complex.ofReal_re] at h
  have hTρ : 2 * (∫ t in (0:ℝ)..x₀, f t) ≤ T (β₁ : ℂ) := by
    have hzig : ((∫ t in (0:ℝ)..x₀,
          Complex.exp (-((((β₁ : ℂ) - (β₁ : ℂ)) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
        = ∫ t in (0:ℝ)..x₀, f t := by
      simp only [sub_self, zero_mul, neg_zero, Complex.exp_zero, one_mul]
      rw [intervalIntegral.integral_ofReal, Complex.ofReal_re]
    have hDge : (2:ℝ) ≤ ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|(((β₁ : ℂ)).im)| + 2))) (β₁ : ℂ) : ℤ) := by
      have h := hmult; exact_mod_cast h
    simp only [T]
    rw [if_pos hβδ, hzig]
    exact mul_le_mul_of_nonneg_right hDge hIf
  have hTfin : (Function.support T).Finite := by
    have hDfin : (Function.support (fun u : ℂ => MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|(((β₁ : ℂ)).im)| + 2)) u)).Finite :=
      MeromorphicOn.divisor_support_finite_of_subset
        (f := DirichletCharacter.completedLFunction χ)
        (U := Metric.closedBall (0:ℂ) (|(((β₁ : ℂ)).im)| + 2))
        (V := Metric.closedBall (0:ℂ) (|(((β₁ : ℂ)).im)| + 2))
        (fun z _ => ((DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z).meromorphicAt)
        (isCompact_closedBall 0 (|(((β₁ : ℂ)).im)| + 2)) (subset_refl _)
    refine hDfin.subset ?_
    intro u hu
    rw [Function.mem_support] at hu ⊢
    intro h0
    apply hu
    simp only [T]
    rw [h0]
    norm_num
  rcases eq_or_lt_of_le (hTnn (β₁ : ℂ)) with h0 | h0
  · exact le_trans hTρ (le_trans (le_of_eq h0.symm) (finsum_nonneg hTnn))
  · have hmem : (β₁ : ℂ) ∈ Function.support T := Function.mem_support.mpr (ne_of_gt h0)
    have heq := finsum_eq_sum_of_support_subset T (s := hTfin.toFinset)
      (fun x hx => hTfin.mem_toFinset.mpr hx)
    rw [heq]
    exact le_trans hTρ (Finset.single_le_sum (fun i _ => hTnn i) (hTfin.mem_toFinset.mpr hmem))

/-- **Heath-Brown Lemma 6.4, repeated-zero case.**

With HB's Conditions 1–2 on the test function `f`, a real non-principal character `χ`, a real
`β₁` in the §6 region which is a zero of `L(·, χ*)` (`χ*` the primitive character inducing `χ`)
of multiplicity `≥ 2` and rightmost among the zeros with `|Im| ≤ 1`, one has
`2F(−λ₁) − 4F(0) + f(0)(2c + 4ε) ≥ 0`, where `F(−λ₁) = ∫₀^{x₀} e^{L(1−β₁)t} f(t) dt`,
`F(0) = ∫₀^{x₀} f(t) dt` and `L = log q`.

The route is the §6 window argument at `s = β₁`: the window sum at `β₁` carries the zero `β₁`
with multiplicity `≥ 2` (`winSumTwoMulAux`), so HB's Lemma 5.2 at `β₁` reads
`K(β₁,χ) ≤ −2L·F(0) + f(0)(c+ε)L`; combining with the principal-character bound
(`Ksum_principal_le_complex`) and the positivity (6.11) (`Ksum_positivity_real`) yields
`2F(−λ₁) − 4F(0) + f(0)(2c + 3ε) ≥ 0` (`Work.ZeroFreeTables.hb6Repeated`), whence the stated
`4ε` form. -/
theorem HB64Repeated (x₀ B : ℝ) (c : ℝ) (hx₀ : 0 < x₀) (hB : 0 ≤ B) :
    ∀ {f : ℝ → ℝ} (hcont : ContinuousOn f (Set.Ici 0)) (hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0)
      (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
      (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B) (hf0 : 0 < f 0)
      (hfnn : ∀ t : ℝ, 0 ≤ f t)
      (hFnn : ∀ z : ℂ, 0 ≤ z.re →
        0 ≤ (∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
      {ε : ℝ} (hε : 0 < ε) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1),
      ∃ q₀ : ℕ, ∀ {q : ℕ} [NeZero q], q₀ ≤ q →
      ∀ (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hreal : χ * χ = 1) [NeZero χ.conductor]
        {β₁ : ℝ}
        (hβ₁ : |1 - β₁| ≤ δ) (hβ₁le : β₁ ≤ 1)
        (hβ₁pt : |1 - β₁| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ))
        (hdiv₁ : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
            (Metric.closedBall 0 2)) (β₁ : ℂ) ≠ 0)
        (hmult₁ : 2 ≤ (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
            (Metric.closedBall 0 2)) (β₁ : ℂ))
        (hmax : ∀ u : ℂ, DirichletCharacter.LFunction χ.primitiveCharacter u = 0 →
            |u.im| ≤ 1 → u.re ≤ β₁)
        (H : Commons.NumberTheory.Linnik.L52Hyp χ c ε δ),
      0 ≤ 2 * (∫ t in (0:ℝ)..x₀, Real.exp ((Real.log (q : ℝ) * (1 - β₁)) * t) * f t)
        - 4 * (∫ t in (0:ℝ)..x₀, f t)
        + f 0 * (2 * c + 4 * ε) := by
  intro f hcont hsupp hf2 hBnd hf0 hfnn hFnn ε hε δ hδ0 hδ1
  obtain ⟨q₀, hq₀⟩ := Work.ZeroFreeTables.hb6Repeated (x₀ := x₀) (B := B) (c := c)
    (ε := ε) (δ := δ) hx₀ hB hε hδ0 hδ1 hcont hsupp hf2 hBnd hf0 hfnn hFnn
  refine ⟨max q₀ 2, ?_⟩
  intro q _inst hq χ hχ hreal _ic β₁ hβ₁ hβ₁le hβ₁pt hdiv₁ hmult₁ hmax H
  have hq₀' : q₀ ≤ q := le_trans (le_max_left _ _) hq
  have hq2 : 2 ≤ q := le_trans (le_max_right _ _) hq
  have hLnn : (0 : ℝ) ≤ Real.log (q : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ q))
  -- the primitive character is non-principal
  have hχ' : χ.primitiveCharacter ≠ 1 := by
    intro h
    apply hχ
    rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h]
    exact DirichletCharacter.changeLevel_one χ.conductor_dvd_level
  -- window-maximality: every window zero of `χ.primitiveCharacter` has real part `≤ β₁`
  have hzero' : ∀ u : ℂ, (MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall 0 (|(((β₁ : ℂ)).im)| + 2))) u ≠ 0 →
        ‖(1:ℂ) + (((β₁ : ℂ)).im : ℂ) * Complex.I - u‖ ≤ δ → u ≠ (β₁ : ℂ) → u.re ≤ β₁ := by
    have hwin10 : |((β₁ : ℂ)).im| + δ ≤ 10 * (1/10 : ℝ) := by
      simp only [Complex.ofReal_im, abs_zero, zero_add]
      linarith [hδ1]
    have hmax' : ∀ u : ℂ, DirichletCharacter.LFunction χ.primitiveCharacter u = 0 →
        |u.im| ≤ 10 * (1/10 : ℝ) → u = (β₁ : ℂ) ∨ u.re ≤ β₁ := by
      intro u hzu him
      exact Or.inr (hmax u hzu (by linarith [him]))
    have h := Commons.NumberTheory.Linnik.window_hzero_of_Lzero' χ.primitiveCharacter hχ'
      (L := (1/10 : ℝ)) (A := β₁) (δ := δ) (s := (β₁ : ℂ)) (σ := (β₁ : ℂ))
      hδ1 hwin10 le_rfl hmax'
    intro u hu hw hne
    simpa using h u hu hw hne
  have hzero2 : ∀ u : ℂ, (MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall 0 (|(((β₁ : ℂ)).im)| + 2))) u ≠ 0 →
        ‖(1:ℂ) + (((β₁ : ℂ)).im : ℂ) * Complex.I - u‖ ≤ δ → u.re ≤ β₁ := by
    intro u hu hw
    by_cases hb : u = (β₁ : ℂ)
    · rw [hb]; simp
    · exact hzero' u hu hw hb
  have hmult₁' : (2 : ℤ) ≤ (MeromorphicOn.divisor
      (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall 0 (|(((β₁ : ℂ)).im)| + 2))) (β₁ : ℂ) := by
    rw [show Metric.closedBall (0:ℂ) (|(((β₁ : ℂ)).im)| + 2) = Metric.closedBall (0:ℂ) 2 by
      simp [Complex.ofReal_im]]
    exact hmult₁
  have hβδ : ‖(1:ℂ) + (((β₁ : ℂ)).im : ℂ) * Complex.I - (β₁ : ℂ)‖ ≤ δ := by
    simpa only [Complex.ofReal_im, Complex.ofReal_zero, zero_mul, add_zero]
      using (show ‖(1:ℂ) - (β₁ : ℂ)‖ ≤ δ by
        rw [show (1:ℂ) - (β₁ : ℂ) = ((1 - β₁ : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_real, Real.norm_eq_abs]
        exact hβ₁)
  -- the window sum carries the doubled zero at `β₁`
  have hwin := winSumTwoMulAux χ.primitiveCharacter hχ' hLnn hFnn hβδ hmult₁' hzero2
  -- HB §6, repeated-zero case
  have hcore := hq₀ hq₀' χ hχ hreal hβ₁ hβ₁pt H hwin
  have hε' : 0 < f 0 * ε := mul_pos hf0 hε
  nlinarith [hcore, hε']

end Work.ZeroFreeTables.Table4
