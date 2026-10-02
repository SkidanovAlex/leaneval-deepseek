import Mathlib
import Submission.Work.LinnikAreas.DhRepel.dhTrianglePt

open Complex DirichletCharacter Metric Filter Set Topology MeasureTheory
open scoped Real Topology BigOperators

set_option maxHeartbeats 4000000

namespace Commons.NumberTheory.Linnik

/-- **Window-maximality transfer with an arbitrary height cut-off.**

Variant of `Commons.NumberTheory.Linnik.window_hzero_of_Lzero'` in which the maximality hypothesis
is only assumed for zeros of height `|u.im| ≤ K` and the window condition reads
`|s.im| + δ ≤ K`.  The proof is that of `window_hzero_of_Lzero'` with the height estimate
`|u.im| ≤ |Im s| + δ ≤ K` in place of `|u.im| ≤ 10 L`. -/
theorem window_hzero_of_Lzero_local {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {K A δ : ℝ} {s σ : ℂ} (hδ1 : δ < 1) (hwinK : |s.im| + δ ≤ K) (hA : A ≤ s.re)
    (hmax : ∀ u : ℂ, DirichletCharacter.LFunction χ u = 0 → |u.im| ≤ K →
      u = σ ∨ u.re ≤ A) :
    ∀ u : ℂ, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|s.im| + 2))) u ≠ 0 →
        ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ → u ≠ σ → u.re ≤ s.re := by
  intro u hdiv hwin hne
  have hmem : u ∈ Metric.closedBall (0:ℂ) (|s.im| + 2) :=
    Commons.Analysis.Complex.divisor_mem_of_ne_zero hdiv
  -- positivity of `Re u`
  have hre1 : |1 - u.re| ≤ δ := by
    have h := Complex.abs_re_le_norm ((1:ℂ) + (s.im : ℂ) * Complex.I - u)
    have h' : (((1:ℂ) + (s.im : ℂ) * Complex.I - u).re) = 1 - u.re := by simp
    rw [h'] at h
    linarith only [h, hwin]
  have hure : 0 < u.re := by
    have := (abs_le.mp hre1).2
    linarith only [this, hδ1]
  -- `u` is a zero of `LFunction χ`
  have hzero : DirichletCharacter.LFunction χ u = 0 := by
    have han : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall (0:ℂ) (|s.im| + 2)) :=
      fun z _ => (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z
    have hcast : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|s.im| + 2))) u =
        ((analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℕ) : ℤ) :=
      Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast han hmem
    have hnat : analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u ≠ 0 := by
      intro h0
      exact hdiv (by rw [hcast, h0]; rfl)
    have hz0 : DirichletCharacter.completedLFunction χ u = 0 :=
      apply_eq_zero_of_analyticOrderNatAt_ne_zero hnat
    have hgf : DirichletCharacter.gammaFactor χ u ≠ 0 := by
      have key : ∀ z : ℂ, 0 < z.re → z.Gammaℝ ≠ 0 := by
        intro z hz h0
        obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp h0
        rw [hn] at hz
        have hre : ((-(2 * (n : ℂ)) : ℂ)).re = -(2 * (n : ℝ)) := by simp
        rw [hre] at hz
        have h2 : (0 : ℝ) ≤ 2 * (n : ℝ) := by positivity
        linarith only [hz]
      unfold DirichletCharacter.gammaFactor
      split_ifs with h
      · exact key u hure
      · exact key (u + 1) (by rw [Complex.add_re, Complex.one_re]; linarith only [hure])
    have hune : u ≠ 0 := fun h => by rw [h] at hure; simp at hure
    have h0 := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ u (Or.inl hune)
    have hprod : DirichletCharacter.completedLFunction χ u =
        DirichletCharacter.LFunction χ u * DirichletCharacter.gammaFactor χ u := by
      rw [h0, div_eq_mul_inv, inv_mul_cancel_right₀ hgf]
    rw [hz0] at hprod
    exact (mul_eq_zero.mp hprod.symm).resolve_right hgf
  -- the imaginary part is small
  have him : |u.im| ≤ K := by
    have h := Complex.abs_im_le_norm ((1:ℂ) + (s.im : ℂ) * Complex.I - u)
    have h' : (((1:ℂ) + (s.im : ℂ) * Complex.I - u).im) = s.im - u.im := by simp
    rw [h'] at h
    have h2 : |u.im| ≤ |s.im| + |s.im - u.im| := by
      calc |u.im| = |s.im - (s.im - u.im)| := by ring_nf
        _ ≤ |s.im| + |s.im - u.im| := abs_sub _ _
    linarith only [h, h2, hwin, hwinK]
  rcases hmax u hzero him with h | h
  · exact absurd h hne
  · exact le_trans h hA

/-- **Heath-Brown Lemma 6.3, divisor form, with a bounded-height maximality hypothesis.**

Copy of `Commons.NumberTheory.Linnik.lemma6_3_full_widePt` in which the test zero's height is
bounded by `|γ'| ≤ 1` and the maximality hypothesis `hmax` is assumed only for zeros of height
`|u.im| ≤ |γ'| + 1` (instead of `≤ 10 log q`).  The window-maximality transfer is
`window_hzero_of_Lzero_local` with `K = |γ'| + 1`; since the only characters entering the two
window sums are the points `s = β'` and `s = β' + iγ'`, the two window conditions
`δ ≤ |γ'| + 1` and `|γ'| + δ ≤ |γ'| + 1` are immediate from `δ < 1`.  The height hypothesis
`|γ'| ≤ 10 log q` needed by `lemma6_3_widePt` follows from `|γ'| ≤ 1 ≤ log q` (`q ≥ 3`). -/
theorem lemma6_3_fullLocal (x₀ B : ℝ) (c : ℝ) (hx₀ : 0 < x₀) (hB : 0 ≤ B) :
    ∀ {f : ℝ → ℝ} (hcont : ContinuousOn f (Set.Ici 0)) (hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0)
      (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
      (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B) (hf0 : 0 < f 0)
      (hfnn : ∀ t : ℝ, 0 ≤ f t)
      (hFnn : ∀ z : ℂ, 0 ≤ z.re →
        0 ≤ (∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
      {ε : ℝ} (hε : 0 < ε) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1),
      ∃ q₀ : ℕ, ∀ {q : ℕ} [NeZero q], q₀ ≤ q →
      ∀ (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hreal : χ * χ = 1) [NeZero χ.conductor]
        {β₁ β' γ' : ℝ}
        (hβ₁ : |1 - β₁| ≤ δ) (hβ' : |1 - β'| ≤ δ) (hβ'β₁ : β' ≤ β₁)
        (hβ₁le : β₁ ≤ 1) (hβ'le : β' ≤ 1)
        (hγ' : |γ'| ≤ 1)
        (hβ₁pt : |1 - β₁| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ))
        (hβ'pt : |1 - β'| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ))
        (hdiv₁ : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
            (Metric.closedBall 0 (|γ'| + 2))) (β₁ : ℂ) ≠ 0)
        (hdiv' : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
            (Metric.closedBall 0 (|γ'| + 2))) ((β' : ℂ) + (γ' : ℂ) * Complex.I) ≠ 0)
        (hne : ((β' : ℂ) + (γ' : ℂ) * Complex.I) ≠ (β₁ : ℂ))
        (hmult₁ : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
            (Metric.closedBall 0 (|γ'| + 2))) (β₁ : ℂ) = 1)
        (hmax : ∀ u : ℂ, DirichletCharacter.LFunction χ.primitiveCharacter u = 0 →
            |u.im| ≤ |γ'| + 1 → u = (β₁ : ℂ) ∨ u.re ≤ β')
        (hrect₁ : Real.log (q : ℝ) * (1 - β₁) ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3)
        (hrect' : Real.log (q : ℝ) * (1 - β') ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3)
        (H : L52Hyp χ c ε δ),
      0 ≤ 2 * (∫ t in (0:ℝ)..x₀,
            Real.exp ((Real.log (q : ℝ) * (1 - β')) * t) * f t)
        - 2 * (∫ t in (0:ℝ)..x₀,
            Real.exp (-((Real.log (q : ℝ) * (1 - β₁)) - (Real.log (q : ℝ) * (1 - β'))) * t) * f t)
        - (∫ t in (0:ℝ)..x₀, f t)
        + f 0 * (2 * c + 4 * ε) := by
  intro f hcont hsupp hf2 hBnd hf0 hfnn hFnn ε hε δ hδ0 hδ1
  -- the far-decay threshold
  obtain ⟨Lfar, hLfar1, hfar⟩ := far_term_le_real (x₀ := x₀) (B := B) (δ := δ) hx₀ hB hδ0
    (hcont.mono Set.Icc_subset_Ici_self) (contDiffOn_ofReal_comp hf2)
    (fun t ht => by rw [iteratedDeriv_ofReal_comp]; exact_mod_cast hBnd t ht)
    (fun t ht => hsupp t ht) (ε := f 0 * ε) (mul_pos hf0 hε)
  -- the threshold making `loglog L ≤ (3δ/2) L`
  obtain ⟨Lthr, hLthr1, hthr⟩ := exists_loglog_le_mul (c := 3 * δ / 2) (by positivity)
  obtain ⟨q₀, hq₀⟩ := lemma6_3_widePt x₀ B c hx₀ hB (f := f) hcont hsupp hf2 hBnd hf0 hfnn hFnn hε hδ0 hδ1
  refine ⟨max (max (max q₀ 3) (Nat.ceil (Real.exp Lfar) + 1))
      (Nat.ceil (Real.exp Lthr) + 1), ?_⟩
  intro q _inst hq χ hχ hreal _ic β₁ β' γ' hβ₁ hβ' hβ'β₁ hβ₁le hβ'le hγ' hβ₁pt hβ'pt
    hdiv₁ hdiv' hne hmult₁ hmax hrect₁ hrect' H
  have hqq₀ : q₀ ≤ q := by omega
  have hq3 : 3 ≤ q := by omega
  have hqfar : Nat.ceil (Real.exp Lfar) + 1 ≤ q := by omega
  have hqthr : Nat.ceil (Real.exp Lthr) + 1 ≤ q := by omega
  have hqpos : 0 < q := by omega
  have hlogq : (0 : ℝ) < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hLnn : (0 : ℝ) ≤ Real.log (q : ℝ) := le_of_lt hlogq
  have hlogq1 : (1 : ℝ) ≤ Real.log (q : ℝ) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have h3 : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq3
    linarith only [Real.exp_one_lt_three, h3]
  have hLfar_le : Lfar ≤ Real.log (q : ℝ) := by
    rw [← Real.log_exp Lfar]
    refine Real.log_le_log (Real.exp_pos Lfar) ?_
    refine le_trans (Nat.le_ceil _) ?_
    exact_mod_cast (by omega : Nat.ceil (Real.exp Lfar) ≤ q)
  have hLthr_le : Lthr ≤ Real.log (q : ℝ) := by
    rw [← Real.log_exp Lthr]
    refine Real.log_le_log (Real.exp_pos Lthr) ?_
    refine le_trans (Nat.le_ceil _) ?_
    exact_mod_cast (by omega : Nat.ceil (Real.exp Lthr) ≤ q)
  have hχ' : χ.primitiveCharacter ≠ 1 := by
    intro h
    apply hχ
    rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h]
    exact DirichletCharacter.changeLevel_one χ.conductor_dvd_level
  have hβ₁lo : 1 - δ ≤ β₁ := by have := (abs_le.mp hβ₁).2; linarith only [this]
  have hβ₁hi : β₁ ≤ 1 + δ := by have := (abs_le.mp hβ₁).1; linarith only [hδ0, hβ₁le]
  have hβ'lo : 1 - δ ≤ β' := by have := (abs_le.mp hβ').2; linarith only [this]
  have hβ'hi : β' ≤ 1 + δ := by have := (abs_le.mp hβ').1; linarith only [hδ0, hβ'β₁, hβ₁le]
  have hβ₁pos : 0 < β₁ := by linarith only [hδ1, hβ₁lo]
  have hβ'pos : 0 < β' := by linarith only [hδ1, hβ'lo]
  have himρ : (((β' : ℂ) + (γ' : ℂ) * Complex.I)).im = γ' := by simp
  have hmem₂ : (β₁ : ℂ) ∈ Metric.closedBall (0 : ℂ) (|((β' : ℂ)).im| + 2) := by
    have him0 : ((β' : ℂ)).im = 0 := by simp
    rw [Metric.mem_closedBall, dist_zero_right, him0, abs_zero, zero_add,
      Complex.norm_real, Real.norm_eq_abs, abs_le]
    exact ⟨by linarith only [hδ0, hδ1, hβ₁lo], by linarith only [hδ0, hδ1, hβ₁le]⟩
  have hmemR : (β₁ : ℂ) ∈ Metric.closedBall (0 : ℂ) (|γ'| + 2) := by
    rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_le]
    exact ⟨by linarith only [abs_nonneg γ', hδ0, hδ1, hβ₁lo], by linarith only [abs_nonneg γ', hδ0, hδ1, hβ₁le]⟩
  have han : ∀ z : ℂ, AnalyticAt ℂ (DirichletCharacter.completedLFunction χ.primitiveCharacter) z :=
    fun z => (DirichletCharacter.differentiable_completedLFunction hχ').analyticAt z
  have hdiv₁₂ : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall 0 (|((β' : ℂ)).im| + 2))) (β₁ : ℂ) ≠ 0 := by
    have heq : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall 0 (|((β' : ℂ)).im| + 2))) (β₁ : ℂ)
        = (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall 0 (|γ'| + 2))) (β₁ : ℂ) :=
      divisor_closedBall_congr han hmem₂ hmemR
    intro h0
    exact hdiv₁ (by rw [← heq]; exact h0)
  have hmemρ : ((β' : ℂ) + (γ' : ℂ) * Complex.I) ∈ Metric.closedBall (0 : ℂ) (|γ'| + 2) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖(β' : ℂ) + (γ' : ℂ) * Complex.I‖
        ≤ ‖(β' : ℂ)‖ + ‖(γ' : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = |β'| + |γ'| := by
          rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one,
            Complex.norm_real, Real.norm_eq_abs]
      _ ≤ |γ'| + 2 := by
          have h2 : |β'| ≤ 2 := by
            rw [abs_le]; exact ⟨by linarith only [hδ0, hδ1, hβ'lo], by linarith only [hδ0, hδ1, hβ'β₁, hβ₁le]⟩
          linarith only [abs_nonneg γ', h2]
  have hzero₁' : DirichletCharacter.LFunction χ.primitiveCharacter (β₁ : ℂ) = 0 :=
    LFunction_eq_zero_of_divisor_completedL_ne_zero
      χ.primitiveCharacter hχ' (a := 0) (ρ := |γ'| + 2) hmemR (by simpa using hβ₁pos) hdiv₁
  have hzero₁ : DirichletCharacter.LFunction χ (β₁ : ℂ) = 0 := by
    simp only [Commons.NumberTheory.DirichletCharacter.LFunction_eq_primitiveCharacter_mul χ hχ,
      hzero₁', zero_mul]
  have hzero'' : DirichletCharacter.LFunction χ.primitiveCharacter
      ((β' : ℂ) + (γ' : ℂ) * Complex.I) = 0 :=
    LFunction_eq_zero_of_divisor_completedL_ne_zero
      χ.primitiveCharacter hχ' (a := 0) (ρ := |γ'| + 2) hmemρ (by simpa using hβ'pos) hdiv'
  have hzero' : DirichletCharacter.LFunction χ ((β' : ℂ) + (γ' : ℂ) * Complex.I) = 0 := by
    simp only [Commons.NumberTheory.DirichletCharacter.LFunction_eq_primitiveCharacter_mul χ hχ,
      hzero'', zero_mul]
  have hwinK₁ : |((β' : ℂ)).im| + δ ≤ |γ'| + 1 := by
    have him0 : ((β' : ℂ)).im = 0 := by simp
    rw [him0, abs_zero, zero_add]
    linarith only [hδ1, abs_nonneg γ']
  have hwinK' : |(((β' : ℂ) + (γ' : ℂ) * Complex.I)).im| + δ ≤ |γ'| + 1 := by
    rw [himρ]
    linarith only [hδ1]
  have hzw1 : ∀ u : ℂ, (MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall 0 (|((β' : ℂ)).im| + 2))) u ≠ 0 →
      ‖(1:ℂ) + (((β' : ℂ)).im : ℂ) * Complex.I - u‖ ≤ δ → u ≠ (β₁ : ℂ) → u.re ≤ β' := by
    intro u hu hw hne'
    have h := window_hzero_of_Lzero_local χ.primitiveCharacter hχ' (K := |γ'| + 1)
      (A := β') (δ := δ) (s := (β' : ℂ)) (σ := (β₁ : ℂ)) hδ1 hwinK₁ (le_of_eq rfl) hmax
    simpa using h u hu hw hne'
  have hzw2 : ∀ u : ℂ, (MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall 0 (|(((β' : ℂ) + (γ' : ℂ) * Complex.I)).im| + 2))) u ≠ 0 →
      ‖(1:ℂ) + ((((β' : ℂ) + (γ' : ℂ) * Complex.I)).im : ℂ) * Complex.I - u‖ ≤ δ →
      u ≠ ((β' : ℂ) + (γ' : ℂ) * Complex.I) → u ≠ (β₁ : ℂ) → u.re ≤ β' := by
    intro u hu hw _ hne'
    have h := window_hzero_of_Lzero_local χ.primitiveCharacter hχ' (K := |γ'| + 1)
      (A := β') (δ := δ) (s := ((β' : ℂ) + (γ' : ℂ) * Complex.I)) (σ := (β₁ : ℂ))
      hδ1 hwinK' (by simp) hmax
    simpa [himρ] using h u hu hw hne'
  have hfnn' : ∀ t ∈ Set.Icc (0:ℝ) x₀, 0 ≤ f t := fun t _ => hfnn t
  have hRρ : |(((β' : ℂ) + (γ' : ℂ) * Complex.I)).im| + 2 = |γ'| + 2 := by rw [himρ]
  have hdiv₁q : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall 0 (|(((β' : ℂ) + (γ' : ℂ) * Complex.I)).im| + 2))) (β₁ : ℂ) ≠ 0 := by
    rw [hRρ]; exact hdiv₁
  have hdivq : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall 0 (|(((β' : ℂ) + (γ' : ℂ) * Complex.I)).im| + 2)))
      ((β' : ℂ) + (γ' : ℂ) * Complex.I) ≠ 0 := by
    rw [hRρ]; exact hdiv'
  have hmult₁q : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall 0 (|(((β' : ℂ) + (γ' : ℂ) * Complex.I)).im| + 2))) (β₁ : ℂ) = 1 := by
    rw [hRρ]; exact hmult₁
  have hw13 : ((∫ t in (0:ℝ)..x₀,
        Complex.exp (-((((β' : ℂ) - (β₁ : ℂ)) * (Real.log (q : ℝ))) * (t : ℂ))) *
          ((f t : ℝ) : ℂ)).re)
      ≤ winSum χ.primitiveCharacter f x₀ (Real.log (q : ℝ)) δ (β' : ℂ) := by
    have hwin₁ : ‖(1:ℂ) + (((β' : ℂ)).im : ℂ) * Complex.I - (β₁ : ℂ)‖ ≤ δ := by
      have h1 : (1:ℂ) + (((β' : ℂ)).im : ℂ) * Complex.I - (β₁ : ℂ) = ((1 - β₁ : ℝ) : ℂ) := by
        simp
      rw [h1, Complex.norm_real, Real.norm_eq_abs]
      exact hβ₁
    simpa only [winSum] using windowSum_ge_single_real χ.primitiveCharacter hχ'
      (f := f) (x₀ := x₀) hx₀ hfnn' hFnn (L := Real.log (q : ℝ)) (δ := δ) hLnn hβ'β₁
      hdiv₁₂ hwin₁ hzw1
  have h614 : ‖(1:ℂ) + (((β' : ℂ) + (γ' : ℂ) * Complex.I).im : ℂ) * Complex.I - (β₁ : ℂ)‖ ≤ δ ∨
      (∫ t in (0:ℝ)..x₀,
        Complex.exp (-(((((β' : ℂ) + (γ' : ℂ) * Complex.I) - (β₁ : ℂ)) *
          (Real.log (q : ℝ))) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re ≤ f 0 * ε := by
    by_cases hnear : ‖(1:ℂ) + (((β' : ℂ) + (γ' : ℂ) * Complex.I).im : ℂ) * Complex.I - (β₁ : ℂ)‖ ≤ δ
    · exact Or.inl hnear
    · push Not at hnear
      right
      have hfar1 : δ / 2 < |γ'| := by
        refine gt_half_delta_of_far (δ := δ) (β₁ := β₁) (γ' := γ')
          (lam₁ := Real.log (q : ℝ) * (1 - β₁)) (L := Real.log (q : ℝ)) hlogq ?_ ?_ ?_
        · have h1 : Real.log (q : ℝ) * (1 - β₁) / Real.log (q : ℝ) = 1 - β₁ := by
            field_simp
          rw [h1, abs_of_nonneg (by linarith only [hβ₁le] : (0:ℝ) ≤ 1 - β₁)]
        · refine le_trans hrect₁ ?_
          have h := hthr (Real.log (q : ℝ)) hLthr_le
          linarith only [h]
        · have h' : (1:ℂ) - (β₁ : ℂ) + (γ' : ℂ) * Complex.I
              = (1:ℂ) + (((β' : ℂ) + (γ' : ℂ) * Complex.I).im : ℂ) * Complex.I - (β₁ : ℂ) := by
            rw [himρ]; ring
          rw [h']
          exact hnear
      have hfar_apply := hfar (L := Real.log (q : ℝ))
        (a := (β' - β₁) * Real.log (q : ℝ)) (η := γ' * Real.log (q : ℝ))
        hLfar_le hlogq1
        (by
          rw [abs_mul, abs_of_pos hlogq]
          have h2 : β₁ - β' ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 / Real.log (q : ℝ) := by
            rw [le_div_iff₀ hlogq]
            nlinarith only [hrect', hδ0, hδ1, hβ₁le, hlogq]
          rw [abs_of_nonpos (by linarith only [hβ'β₁] : β' - β₁ ≤ 0)]
          nlinarith only [h2, hlogq, hrect', hδ0, hδ1, hβ₁le])
        (by
          rw [abs_mul, abs_of_pos hlogq]
          nlinarith only [hfar1, hlogq, hδ0, hδ1])
      have heqint : (∫ t in (0:ℝ)..x₀,
            Complex.exp (-(((((β' : ℂ) + (γ' : ℂ) * Complex.I) - (β₁ : ℂ)) *
              (Real.log (q : ℝ))) * (t : ℂ))) * ((f t : ℝ) : ℂ))
          = ∫ t in (0:ℝ)..x₀,
            Complex.exp (-(((((β' - β₁) * Real.log (q : ℝ) : ℝ) : ℂ) +
              (((γ' * Real.log (q : ℝ) : ℝ)) : ℂ) * Complex.I) * (t : ℂ))) *
              ((f t : ℝ) : ℂ) := by
        apply intervalIntegral.integral_congr
        intro t _
        congr 2
        push_cast
        ring
      rw [heqint]
      exact le_trans (Complex.re_le_norm _) hfar_apply
  have hw15 : ((∫ t in (0:ℝ)..x₀,
        Complex.exp (-(((((β' : ℂ) + (γ' : ℂ) * Complex.I) -
          ((β' : ℂ) + (γ' : ℂ) * Complex.I)) * (Real.log (q : ℝ))) * (t : ℂ))) *
          ((f t : ℝ) : ℂ)).re)
      + (∫ t in (0:ℝ)..x₀,
        Complex.exp (-(((((β' : ℂ) + (γ' : ℂ) * Complex.I) - (β₁ : ℂ)) *
          (Real.log (q : ℝ))) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re - f 0 * ε
      ≤ winSum χ.primitiveCharacter f x₀ (Real.log (q : ℝ)) δ
          ((β' : ℂ) + (γ' : ℂ) * Complex.I) := by
    have h0nn : 0 ≤ (∫ t in (0:ℝ)..x₀,
        Complex.exp (-(((((β' : ℂ) + (γ' : ℂ) * Complex.I) -
          ((β' : ℂ) + (γ' : ℂ) * Complex.I)) * (Real.log (q : ℝ))) * (t : ℂ))) *
          ((f t : ℝ) : ℂ)).re := by
      have hpt : ∀ t : ℝ, Complex.exp (-(((((β' : ℂ) + (γ' : ℂ) * Complex.I) -
            ((β' : ℂ) + (γ' : ℂ) * Complex.I)) * (Real.log (q : ℝ))) * (t : ℂ))) *
            ((f t : ℝ) : ℂ) = ((f t : ℝ) : ℂ) := by
        intro t; simp
      simp only [hpt]
      rw [intervalIntegral.integral_ofReal, Complex.ofReal_re]
      exact intervalIntegral.integral_nonneg hx₀.le (fun t _ => hfnn t)
    simpa only [winSum] using windowSum_ge_pair χ.primitiveCharacter hχ'
      (f := f) (x₀ := x₀) hx₀ hfnn' hFnn (L := Real.log (q : ℝ)) hLnn hε.le hβ' hne hf0.le
      hdiv₁q hdivq hmult₁q h0nn h614 hzw2
  have hγ10 : |γ'| ≤ 10 * Real.log (q : ℝ) := by linarith only [hγ', hlogq1, hδ0, hδ1]
  exact hq₀ hqq₀ χ hχ hreal hβ₁ hβ' hβ'β₁ hβ₁le hβ'le hγ10 hβ₁pt hβ'pt hzero₁ hzero'
    H hw13 hw15

end Commons.NumberTheory.Linnik

namespace Work.LinnikAreas.OtherCharRepel

open DirichletCharacter Complex
open scoped Classical

/-- The primitive character inducing a non-principal character is non-principal. -/
private lemma primitiveCharacter_ne_one' {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) : χ.primitiveCharacter ≠ 1 := by
  intro h1
  refine hχ ?_
  rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h1]
  exact DirichletCharacter.changeLevel_one χ.conductor_dvd_level

/-- A zero of the ordinary `L`-function of a non-principal character has real part `< 1`. -/
private lemma re_lt_one_of_LFunction_zero {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) {u : ℂ} (hu : DirichletCharacter.LFunction χ u = 0) : u.re < 1 := by
  by_contra h
  exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (not_lt.mp h)) hu

/-- On `(0,x)` the triangle `t ↦ max (x-t) 0` agrees with the affine function `x - t`, so its
second derivative vanishes there (the `B = 0` bound on the test function). -/
private lemma iteratedDeriv_two_tent {x t : ℝ} (ht : t ∈ Set.Ioo (0:ℝ) x) :
    iteratedDeriv 2 (fun s : ℝ => max (x - s) 0) t = 0 := by
  have hcongr : Set.EqOn (fun s : ℝ => max (x - s) 0) (fun s : ℝ => x - s)
      (Set.Ioo (0:ℝ) x) :=
    fun s hs => max_eq_left (by linarith only [hs.2, hs])
  have h1 := Set.EqOn.iteratedDeriv_of_isOpen hcongr isOpen_Ioo 2 ht
  rw [h1]
  simp [iteratedDeriv_succ, iteratedDeriv_const, iteratedDeriv_id]

/-- The integral of the triangle `t ↦ max (x-t) 0` over `[0,x]` is `x²/2`. -/
private lemma integral_tent (x : ℝ) (hx : 0 ≤ x) :
    (∫ t in (0:ℝ)..x, max (x - t) 0) = x ^ 2 / 2 := by
  have hcongr : (∫ t in (0:ℝ)..x, max (x - t) 0) = ∫ t in (0:ℝ)..x, (x - t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    exact max_eq_left (by linarith only [ht.2, ht])
  rw [hcongr]
  have hsub : (∫ t in (0:ℝ)..x, (x - t))
      = (∫ t in (0:ℝ)..x, (fun _ : ℝ => x) t) - ∫ t in (0:ℝ)..x, t :=
    intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
      (continuous_id.intervalIntegrable _ _)
  rw [hsub, intervalIntegral.integral_const, integral_id]
  ring


/-- **The `§6` triangle inequality with the bounded-height maximality hypothesis.**

Same statement as `Work.LinnikAreas.DhRepel.dhTrianglePt`, with the height bound `|Im ρ'| ≤ 1` in
place of `|Im ρ'| ≤ 10 log q - 1` and `hmax` assumed only for zeros of height `|u.im| ≤ |ρ'.im|+1`.
Proof: instantiate `lemma6_3_fullLocal` at the triangle test function `f t = max (x-t) 0`. -/
theorem dhTrianglePtLocal :
    ∀ x : ℝ, 0 < x → ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ c : ℝ,
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
      ∀ [NeZero q] (χ : DirichletCharacter ℂ q)
      (hχ : χ ≠ 1) (hreal : χ ^ 2 = 1) [NeZero χ.conductor] {β₁ : ℝ} {ρ' : ℂ}
      (hβ₁ : |1 - β₁| ≤ δ)
      (hβ' : |1 - ρ'.re| ≤ δ) (hβ'β₁ : ρ'.re ≤ β₁)
      (hγ' : |ρ'.im| ≤ 1)
      (hβ₁pt : |1 - β₁| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ))
      (hρ'pt : |1 - ρ'.re| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ))
      (hdiv₁ : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
          (Metric.closedBall 0 (|ρ'.im| + 2))) (β₁ : ℂ) ≠ 0)
      (hdiv' : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
          (Metric.closedBall 0 (|ρ'.im| + 2))) ρ' ≠ 0)
      (hne : ρ' ≠ (β₁ : ℂ))
      (hmult₁ : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
          (Metric.closedBall 0 (|ρ'.im| + 2))) (β₁ : ℂ) = 1)
      (hmax : ∀ u : ℂ, DirichletCharacter.LFunction χ.primitiveCharacter u = 0 →
          |u.im| ≤ |ρ'.im| + 1 → u = (β₁ : ℂ) ∨ u.re ≤ ρ'.re)
      (hrect₁ : Work.LinnikContract.lamOf q (β₁ : ℂ)
          ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3)
      (hrect' : Work.LinnikContract.lamOf q ρ'
          ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3)
      (H : Commons.NumberTheory.Linnik.L52Hyp χ c ε δ),
      0 ≤ 2 * (∫ t in (0:ℝ)..x, Real.exp ((Work.LinnikContract.lamOf q ρ') * t) * (x - t))
        - 2 * (∫ t in (0:ℝ)..x, Real.exp ((Work.LinnikContract.lamOf q ρ'
            - Work.LinnikContract.lamOf q (β₁ : ℂ)) * t) * (x - t))
        - x ^ 2 / 2 + (2 * c + 4 * ε) * x := by
  intro x hx ε hε δ hδ0 hδ1 c
  obtain ⟨q₀, hq₀⟩ := Commons.NumberTheory.Linnik.lemma6_3_fullLocal x 0 c hx le_rfl
    (f := fun t : ℝ => max (x - t) 0)
    (by fun_prop)
    (fun t ht => max_eq_right (by linarith only [ht]))
    (by
      have haff : ContDiffOn ℝ 2 (fun t : ℝ => x - t) (Set.Ioo 0 x) :=
        (contDiffOn_const (c := x)).sub contDiffOn_id
      exact haff.congr (fun t ht => max_eq_left (by linarith only [ht.2, ht])))
    (fun t ht => by rw [iteratedDeriv_two_tent ht]; norm_num)
    (by rw [sub_zero, max_eq_left hx.le]; exact hx)
    (fun t => le_max_right _ _)
    (triangle_hFnn hx)
    (ε := ε) hε (δ := δ) hδ0 hδ1
  refine ⟨q₀, ?_⟩
  intro q hq inst χ hχ hreal instc β₁ ρ' hβ₁ hβ' hβ'β₁ hγ' hβ₁pt hρ'pt hdiv₁ hdiv' hne hmult₁ hmax
    hrect₁ hrect' H
  have hχ' : χ.primitiveCharacter ≠ 1 := primitiveCharacter_ne_one' hχ
  -- the two `re < 1` facts for the zeros, via the critical strip
  have hβ₁lo : 1 - δ ≤ β₁ := by have := (abs_le.mp hβ₁).2; linarith only [this]
  have hβ₁hi : β₁ ≤ 1 + δ := by have := (abs_le.mp hβ₁).1; linarith only [this]
  have hβ₁pos : 0 < β₁ := by linarith only [hδ1, hβ₁lo]
  have hβ'lo : 1 - δ ≤ ρ'.re := by have := (abs_le.mp hβ').2; linarith only [this]
  have hρ'pos : 0 < ρ'.re := by linarith only [hδ1, hβ'lo]
  have hmem₁ : (β₁ : ℂ) ∈ Metric.closedBall (0 : ℂ) (|ρ'.im| + 2) := by
    rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> [linarith only [abs_nonneg ρ'.im, hδ0, hδ1, hβ₁lo]; linarith only [abs_nonneg ρ'.im, hδ1, hβ₁hi]]
  have hmem' : ρ' ∈ Metric.closedBall (0 : ℂ) (|ρ'.im| + 2) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    refine le_trans (Complex.norm_le_abs_re_add_abs_im ρ') ?_
    have h1 : |ρ'.re| ≤ 2 := by
      rw [abs_le]; constructor <;> linarith only [abs_nonneg ρ'.im, hδ0, hδ1, hβ'lo, hβ'β₁, hβ₁hi]
    linarith only [abs_nonneg ρ'.im, h1]
  have hL₁ : DirichletCharacter.LFunction χ.primitiveCharacter (β₁ : ℂ) = 0 :=
    Commons.NumberTheory.Linnik.LFunction_eq_zero_of_divisor_completedL_ne_zero
      χ.primitiveCharacter hχ' hmem₁ (by simpa using hβ₁pos) hdiv₁
  have hL' : DirichletCharacter.LFunction χ.primitiveCharacter ρ' = 0 :=
    Commons.NumberTheory.Linnik.LFunction_eq_zero_of_divisor_completedL_ne_zero
      χ.primitiveCharacter hχ' hmem' (by simpa using hρ'pos) hdiv'
  have hβ₁le : β₁ ≤ 1 := (re_lt_one_of_LFunction_zero hχ' hL₁).le
  have hβ'le : ρ'.re ≤ 1 := (re_lt_one_of_LFunction_zero hχ' hL').le
  -- the `λ`-form of the rectangle hypotheses
  have hrect₁' : Real.log (q : ℝ) * (1 - β₁)
      ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 := by
    rw [Work.LinnikContract.lamOf, Complex.ofReal_re] at hrect₁
    rw [mul_comm]; exact hrect₁
  have hrect'' : Real.log (q : ℝ) * (1 - ρ'.re)
      ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 := by
    rw [Work.LinnikContract.lamOf] at hrect'
    rw [mul_comm]; exact hrect'
  have h := hq₀ hq χ hχ (by simpa only [pow_two] using hreal) hβ₁ hβ' hβ'β₁ hβ₁le hβ'le hγ' hβ₁pt hρ'pt
    hdiv₁ (by rw [Complex.re_add_im]; exact hdiv') (by rw [Complex.re_add_im]; exact hne)
    hmult₁ hmax hrect₁' hrect'' H
  -- rewrite the conclusion of Lemma 6.3 into the shape of the statement
  have hF : ∀ t ∈ Set.uIcc (0:ℝ) x, max (x - t) 0 = x - t := by
    intro t ht
    rw [Set.uIcc_of_le hx.le] at ht
    exact max_eq_left (by linarith only [ht.2, ht])
  have heq1 : (∫ t in (0:ℝ)..x,
        Real.exp (Real.log (q : ℝ) * (1 - ρ'.re) * t) * max (x - t) 0)
      = ∫ t in (0:ℝ)..x, Real.exp ((Work.LinnikContract.lamOf q ρ') * t) * (x - t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    simp only
    rw [hF t ht, Work.LinnikContract.lamOf]
    congr 2
    ring
  have heq2 : (∫ t in (0:ℝ)..x,
        Real.exp (-(Real.log (q : ℝ) * (1 - β₁) - Real.log (q : ℝ) * (1 - ρ'.re)) * t)
          * max (x - t) 0)
      = ∫ t in (0:ℝ)..x,
          Real.exp ((Work.LinnikContract.lamOf q ρ' - Work.LinnikContract.lamOf q (β₁ : ℂ)) * t)
            * (x - t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    simp only
    rw [hF t ht, Work.LinnikContract.lamOf, Work.LinnikContract.lamOf, Complex.ofReal_re]
    congr 2
    ring
  have heq4 : max (x - 0) 0 * (2 * c + 4 * ε) = (2 * c + 4 * ε) * x := by
    rw [sub_zero, max_eq_left hx.le, mul_comm]
  rw [heq1, heq2, integral_tent x hx.le, heq4] at h
  linarith only [h]

end Work.LinnikAreas.OtherCharRepel
