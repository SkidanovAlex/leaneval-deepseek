/-
# `KsumChiTwoZerosWindow` — the corrected `KsumChiTwoZeros`

`Work.ZeroFreeTables.XY.KsumChiTwoZeros` hard-codes the window radius `δ = 1/2` and derives the
two-term `F`-method bound from a hypothesis `L52Hyp χ (1/8) (1/10000) (1/2)`.  That hypothesis is
not obtainable: the window radius of the constant-`1/8` bound is *produced* by HB's Lemma 3.1
(see `Work.ZeroFreeTables.XY.L52HypEighthDelta`), never prescribed; and its weaker hypotheses
(`s.re < ρ.re`, `s.re < ρ'.re`) do *not* place `ρ`, `ρ'` inside the window, which is what the
derivation actually uses.

This file provides the corrected statement, in the pattern of Xylouris's Lemma 3.4 (his
"Arbeitsversion" of HB Lemma 5.2): the window radius `δ` is free, `L52Hyp χ (1/8) ε δ` is
hypothesised at that same `δ`, the two retained zeros are explicitly assumed to lie in the window,
and every *other* window zero is assumed to lie to the left of `s` (so that its kernel contributes
non-negatively, by Condition 2 on the test function).  The conclusion keeps the *divisor weights*
(`ord ρ`, `ord ρ'`) of the retained zeros, exactly as the proved
`Work.ZeroFreeTables.Ksum_le_single_mult` does; the unweighted form of `KsumChiTwoZeros` follows
when both retained zeros are simple.

The proof is a direct corollary of `Commons.NumberTheory.Linnik.lemma5_2_of_logDeriv_bound_phi_imprim`
plus the two-term window bound `windowSum_ge_two` proved below.
-/
import Mathlib
import Submission.Work.NumberTheory.Linnik.scratch_l62app_phi
import Submission.Work.NumberTheory.Linnik.scratch_l52phi_imprim
import Submission.Commons.Analysis.Complex.circleLogDerivContour_bound

open DirichletCharacter

namespace Work.ZeroFreeTables.XY

/-- **Two-term divisor-explicit window bound.**  If two distinct zeros `ρ`, `ρ'` of
`Λ(·,χ)` lie in the Lemma-5.2 window `‖1 + i·Im s - u‖ ≤ δ` of `s`, every other window zero has
`Re u ≤ Re s`, and `f` has non-negative Laplace transform on `Re z ≥ 0` (Condition 2), then the
sum of the two *divisor-weighted* retained terms is at most the full window sum.  This is
`Work.ZeroFreeTables.windowSum_ge_div_mul_kernel` extended from one retained zero to two. -/
theorem windowSum_ge_two (x₀ L : ℝ) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {f : ℝ → ℝ} {s ρ ρ' : ℂ} {δ : ℝ} (hL : 0 ≤ L)
    (hF : ∀ z : ℂ, 0 ≤ z.re →
      0 ≤ (∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
    (hdiv : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|s.im| + 2))) ρ ≠ 0)
    (hdiv' : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|s.im| + 2))) ρ' ≠ 0)
    (hne : ρ ≠ ρ')
    (hwin : ‖(1:ℂ) + (s.im : ℂ) * Complex.I - ρ‖ ≤ δ)
    (hwin' : ‖(1:ℂ) + (s.im : ℂ) * Complex.I - ρ'‖ ≤ δ)
    (hzw : ∀ u : ℂ, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|s.im| + 2))) u ≠ 0 →
        ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ → u ≠ ρ → u ≠ ρ' → u.re ≤ s.re) :
    (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 (|s.im| + 2))) ρ : ℤ) : ℝ) *
        ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - ρ) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
      + (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 (|s.im| + 2))) ρ' : ℤ) : ℝ) *
        ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - ρ') * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
      ≤ ∑ᶠ u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) *
        (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then
          ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - u) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
          else 0) := by
  classical
  set D : ℂ → ℤ := fun u => MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall 0 (|s.im| + 2)) u with hDdef
  set Fv : ℂ → ℝ := fun u =>
      (∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - u) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re with hFvdef
  set G : ℂ → ℝ := fun u => ((D u : ℤ) : ℝ) *
      (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then Fv u else 0) with hGdef
  have hDval : ∀ u : ℂ, D u = MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall 0 (|s.im| + 2)) u := fun u => rfl
  have hDnn : ∀ u : ℂ, (0:ℝ) ≤ ((D u : ℤ) : ℝ) := by
    intro u
    have hAn : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|s.im| + 2)) :=
      fun z _ => (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z
    simpa [hDdef] using Commons.Analysis.Complex.divisor_nonneg_on_closedBall hAn u
  have hGnn : ∀ u : ℂ, u ≠ ρ → u ≠ ρ' → 0 ≤ G u := by
    intro u hu hu'
    by_cases hDu : D u = 0
    · rw [hGdef]; simp [hDu]
    · by_cases hc : ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ
      · rw [hGdef]; simp only [hc, if_true]
        have hre : u.re ≤ s.re := hzw u (by rw [← hDval u]; exact hDu) hc hu hu'
        have hznn : 0 ≤ (((s - u) * L : ℂ)).re := by
          rw [Complex.mul_re]
          simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
          have : 0 ≤ (s - u).re := by rw [Complex.sub_re]; linarith
          exact mul_nonneg this hL
        exact mul_nonneg (hDnn u) (hF ((s - u) * L) hznn)
      · rw [hGdef]; simp only [hc, if_false, mul_zero, le_refl]
  have hDfin : (Function.support (fun u : ℂ => D u)).Finite := by
    have hmer : MeromorphicOn (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall (0:ℂ) (|s.im| + 2)) :=
      fun z _ => ((DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z).meromorphicAt
    have h := MeromorphicOn.divisor_support_finite_of_subset
      (f := DirichletCharacter.completedLFunction χ)
      (U := Metric.closedBall (0:ℂ) (|s.im| + 2))
      (V := Metric.closedBall (0:ℂ) (|s.im| + 2))
      hmer (isCompact_closedBall 0 (|s.im| + 2)) (subset_refl _)
    simpa [hDdef] using h
  have hGfin : Function.HasFiniteSupport G := hDfin.subset (by
    intro u hu
    rw [Function.mem_support] at hu ⊢
    intro h0
    exact hu (by rw [hGdef]; simp [h0]))
  -- split off the two retained points: `H₂ = G` away from `ρ, ρ'`, and `0` at them
  set H₂ : ℂ → ℝ := fun u => G u -
      ((if u = ρ then G ρ else 0) + (if u = ρ' then G ρ' else 0)) with hH₂def
  have hH₂nn : ∀ u : ℂ, 0 ≤ H₂ u := by
    intro u
    by_cases h1 : u = ρ
    · subst h1
      rw [hH₂def]
      simp only [if_true, if_pos rfl, if_neg hne, add_zero, sub_self, le_refl]
    · by_cases h2 : u = ρ'
      · subst h2
        rw [hH₂def]
        simp only [if_true, if_neg (Ne.symm hne), if_pos rfl, zero_add, sub_self, le_refl]
      · rw [hH₂def]
        simp only [if_true, if_neg h1, if_neg h2, add_zero, sub_zero]
        exact hGnn u h1 h2
  have hind1 : Function.HasFiniteSupport (fun u : ℂ => if u = ρ then G ρ else 0) := by
    refine (Set.finite_singleton ρ).subset ?_
    intro u hu
    rw [Function.mem_support] at hu
    simp only [Set.mem_singleton_iff]
    by_contra h
    exact hu (by simp [h])
  have hind2 : Function.HasFiniteSupport (fun u : ℂ => if u = ρ' then G ρ' else 0) := by
    refine (Set.finite_singleton ρ').subset ?_
    intro u hu
    rw [Function.mem_support] at hu
    simp only [Set.mem_singleton_iff]
    by_contra h
    exact hu (by simp [h])
  have hind : Function.HasFiniteSupport (fun u : ℂ =>
      (if u = ρ then G ρ else 0) + (if u = ρ' then G ρ' else 0)) := hind1.add hind2
  have hH₂fin : Function.HasFiniteSupport H₂ := hGfin.subset (by
    intro u hu
    rw [Function.mem_support] at hu ⊢
    intro h0
    refine hu ?_
    by_cases h1 : u = ρ
    · subst h1
      rw [hH₂def]
      simp only [if_true, if_pos rfl, if_neg hne, add_zero, sub_self]
    · by_cases h2 : u = ρ'
      · subst h2
        rw [hH₂def]
        simp only [if_true, if_neg (Ne.symm hne), if_pos rfl, zero_add, sub_self]
      · rw [hH₂def]
        simp only [if_true, if_neg h1, if_neg h2, add_zero, sub_zero, h0])
  have hsplit : (∑ᶠ u : ℂ, H₂ u) = (∑ᶠ u : ℂ, G u) - G ρ - G ρ' := by
    rw [hH₂def]
    rw [finsum_sub_distrib hGfin hind]
    rw [finsum_add_distrib hind1 hind2]
    rw [finsum_eq_single (fun u : ℂ => if u = ρ then G ρ else 0) ρ
          (by intro x hx; simp [hx])]
    rw [finsum_eq_single (fun u : ℂ => if u = ρ' then G ρ' else 0) ρ'
          (by intro x hx; simp [hx])]
    simp only [if_true]
    ring
  have hkey : G ρ + G ρ' ≤ ∑ᶠ u : ℂ, G u := by
    have h1 := finsum_nonneg hH₂nn
    linarith only [h1, hsplit]
  have hGρ : G ρ = ((D ρ : ℤ) : ℝ) * Fv ρ := by
    simp only [hGdef, if_pos hwin]
  have hGρ' : G ρ' = ((D ρ' : ℤ) : ℝ) * Fv ρ' := by
    simp only [hGdef, if_pos hwin']
  have hW : (∑ᶠ u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) *
        (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then
          ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - u) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
          else 0)) = ∑ᶠ u : ℂ, G u := by
    apply finsum_congr
    intro u
    simp only [hGdef, hDval, hFvdef]
  have hρeq : (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|s.im| + 2))) ρ : ℤ) : ℝ) *
        ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - ρ) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
      = G ρ := by
    rw [hGρ, ← hDval ρ, hFvdef]
  have hρ'eq : (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|s.im| + 2))) ρ' : ℤ) : ℝ) *
        ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - ρ') * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
      = G ρ' := by
    rw [hGρ', ← hDval ρ', hFvdef]
  rw [hW, hρeq, hρ'eq]
  exact hkey

open scoped Classical in
/-- **The corrected two-zero `F`-method bound** (Xylouris Lemma 3.4 pattern): the window radius is
free and comes from the provider, the two retained zeros are explicitly in the window, and the
divisor (multiplicity) factors of the retained zeros are kept on the right-hand side. -/
theorem KsumChiTwoZerosWindow (x₀ B : ℝ) (hx₀ : 0 < x₀) (hB : 0 ≤ B) :
    ∀ {f : ℝ → ℝ} (hcont : ContinuousOn f (Set.Ici 0)) (hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0)
      (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
      (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B) (hf0 : 0 < f 0)
      (hF : ∀ z : ℂ, 0 ≤ z.re →
        0 ≤ (∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
      {ε : ℝ} (hε : 0 < ε) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1),
      ∃ q₀ : ℕ, ∀ {q : ℕ} [NeZero q], q₀ ≤ q →
      ∀ (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hχ : χ ≠ 1) {s ρ ρ' : ℂ},
        |s.re - 1| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) →
        |s.im| ≤ 10 * Real.log (q : ℝ) →
        1 - Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) ≤ s.re →
        Commons.NumberTheory.Linnik.L52Hyp χ (1/8) ε δ →
        (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
            (Metric.closedBall 0 (|s.im| + 2))) ρ ≠ 0 →
        (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
            (Metric.closedBall 0 (|s.im| + 2))) ρ' ≠ 0 →
        ρ ≠ ρ' →
        ‖(1:ℂ) + (s.im : ℂ) * Complex.I - ρ‖ ≤ δ →
        ‖(1:ℂ) + (s.im : ℂ) * Complex.I - ρ'‖ ≤ δ →
        (∀ u : ℂ, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
            (Metric.closedBall 0 (|s.im| + 2))) u ≠ 0 →
            ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ → u ≠ ρ → u ≠ ρ' → u.re ≤ s.re) →
        (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
            ((χ (n : ZMod q) / (n : ℂ) ^ s).re) * f (Real.log n / Real.log (q : ℝ)))
          ≤ -(Real.log (q : ℝ)) *
              ((((MeromorphicOn.divisor
                  (DirichletCharacter.completedLFunction χ.primitiveCharacter)
                  (Metric.closedBall 0 (|s.im| + 2))) ρ : ℤ) : ℝ) *
                (∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - ρ) * (Real.log q)) * (t : ℂ))) *
                  ((f t : ℝ) : ℂ)).re)
            - (Real.log (q : ℝ)) *
              ((((MeromorphicOn.divisor
                  (DirichletCharacter.completedLFunction χ.primitiveCharacter)
                  (Metric.closedBall 0 (|s.im| + 2))) ρ' : ℤ) : ℝ) *
                (∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - ρ') * (Real.log q)) * (t : ℂ))) *
                  ((f t : ℝ) : ℂ)).re)
            + f 0 * (1/8 + ε) * Real.log (q : ℝ) := by
  intro f hcont hsupp hf2 hBnd hf0 hF ε hε δ hδ0 hδ1
  obtain ⟨q₀, hq₀⟩ := (Commons.NumberTheory.Linnik.lemma5_2_of_logDeriv_bound_phi_imprim
    x₀ B (1/8) hx₀ hB) hcont hsupp hf2 hBnd hf0 hε hδ0 hδ1
  refine ⟨q₀, ?_⟩
  intro q _inst hq χ _instc hχ s ρ ρ' hsre hsim hs1 hH hdiv hdiv' hne hwin hwin' hzw
  have hLnn : (0:ℝ) ≤ Real.log (q : ℝ) := Real.log_nonneg (by
    have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    exact_mod_cast hq1)
  have hHraw : ∀ s : ℂ, 1 + 1 / (Real.log (q : ℝ) * Real.log (Real.log (q : ℝ))) ≤ s.re →
      s.re ≤ 1 + Real.log (Real.log (q : ℝ)) / Real.log (q : ℝ) →
      |s.im| ≤ 10 * Real.log (q : ℝ) →
      (-logDeriv (DirichletCharacter.LFunction χ.primitiveCharacter) s).re
        + (∑ᶠ u : ℂ, ((MeromorphicOn.divisor
            (DirichletCharacter.completedLFunction χ.primitiveCharacter)
            (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) *
            (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then ((1/(s-u)).re) else 0))
        ≤ ((1/8) + ε/4) * Real.log (q : ℝ) := hH
  have hK := hq₀ hq χ hχ hHraw s hsre hsim hs1
  have hlow := windowSum_ge_two x₀ (Real.log (q : ℝ)) χ.primitiveCharacter
    (by intro h; exact hχ (by
      rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h]
      exact DirichletCharacter.changeLevel_one χ.conductor_dvd_level))
    (f := f) (s := s) (ρ := ρ) (ρ' := ρ') (δ := δ) hLnn hF hdiv hdiv' hne hwin hwin' hzw
  have hmul := mul_le_mul_of_nonpos_left (c := -(Real.log (q : ℝ))) hlow
    (by linarith only [hLnn])
  have hring : -(Real.log (q : ℝ)) *
        ((((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
              (Metric.closedBall 0 (|s.im| + 2))) ρ : ℤ) : ℝ) *
            (∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - ρ) * (Real.log q)) * (t : ℂ))) *
              ((f t : ℝ) : ℂ)).re
          + (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
              (Metric.closedBall 0 (|s.im| + 2))) ρ' : ℤ) : ℝ) *
            (∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - ρ') * (Real.log q)) * (t : ℂ))) *
              ((f t : ℝ) : ℂ)).re)
      = -(Real.log (q : ℝ)) *
              ((((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
                  (Metric.closedBall 0 (|s.im| + 2))) ρ : ℤ) : ℝ) *
                (∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - ρ) * (Real.log q)) * (t : ℂ))) *
                  ((f t : ℝ) : ℂ)).re)
        - (Real.log (q : ℝ)) *
              ((((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
                  (Metric.closedBall 0 (|s.im| + 2))) ρ' : ℤ) : ℝ) *
                (∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - ρ') * (Real.log q)) * (t : ℂ))) *
                  ((f t : ℝ) : ℂ)).re) := by ring
  rw [hring] at hmul
  refine hK.trans ?_
  exact add_le_add hmul le_rfl

end Work.ZeroFreeTables.XY
