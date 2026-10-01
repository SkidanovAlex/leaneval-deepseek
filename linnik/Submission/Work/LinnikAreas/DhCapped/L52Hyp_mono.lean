import Mathlib
import Submission.Work.NumberTheory.Linnik.scratch_l62app_phi
import Submission.Commons.NumberTheory.Linnik.completedL_zero_strip

open DirichletCharacter Complex

namespace Work.LinnikAreas.DhCapped

set_option maxHeartbeats 1000000

/-- The divisor of an analytic function vanishes at a point of the set where the function is
non-zero. -/
private lemma divisor_eq_zero_of_analytic_ne_zero {f : ℂ → ℂ} {U : Set ℂ} {z : ℂ}
    (hAnU : AnalyticOnNhd ℂ f U) (hz : z ∈ U) (hfz : f z ≠ 0) :
    MeromorphicOn.divisor f U z = 0 := by
  rw [MeromorphicOn.divisor_apply hAnU.meromorphicOn hz]
  have hAn : AnalyticAt ℂ f z := hAnU z hz
  have hord : meromorphicOrderAt f z = 0 := by
    rw [hAn.meromorphicOrderAt_eq]
    have h0 : analyticOrderAt f z = 0 := analyticOrderAt_eq_zero.mpr (Or.inr hfz)
    simp [h0]
  simp [hord]

/-- The divisor of any function vanishes outside the set on which it is considered. -/
private lemma divisor_eq_zero_of_notMem {f : ℂ → ℂ} {U : Set ℂ} {z : ℂ} (hz : z ∉ U) :
    MeromorphicOn.divisor f U z = 0 := by
  rw [MeromorphicOn.divisor_def]
  simp [hz]

/-- A non-principal character mod `N` forces `3 ≤ N`: for `N ≤ 2` the unit group `(ZMod N)ˣ`
is trivial, so every multiplicative character is principal. -/
private lemma three_le_of_char_ne_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) : 3 ≤ N := by
  by_contra h
  have hN1 : 1 ≤ N := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne N))
  have hN2 : N ≤ 2 := by omega
  have hχne : ¬ (∀ a : (ZMod N)ˣ, χ ↑a = (1 : DirichletCharacter ℂ N) ↑a) := by
    intro hh
    exact hχ (MulChar.ext hh)
  push Not at hχne
  rcases hχne with ⟨a, hne⟩
  have hs : Subsingleton (ZMod N)ˣ := by
    interval_cases N <;> infer_instance
  have ha : a = 1 := Subsingleton.elim a 1
  subst a
  simp at hne

theorem L52Hyp_mono {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor]
    (hχ : χ ≠ 1) {c ε δ δ' : ℝ} (hδ : δ' ≤ δ)
    (H : Commons.NumberTheory.Linnik.L52Hyp χ c ε δ) :
    Commons.NumberTheory.Linnik.L52Hyp χ c ε δ' := by
  classical
  intro s hs1 hs2 hs3
  -- The range of `s.re` forces `1 ≤ s.re`.
  have hq3 : 3 ≤ q := three_le_of_char_ne_one χ hχ
  have hlogq1 : (1 : ℝ) ≤ Real.log (q : ℝ) := by
    have h3 : (0 : ℝ) < 3 := by norm_num
    have h13 : (1 : ℝ) ≤ Real.log 3 := (Real.le_log_iff_exp_le h3).mpr Real.exp_one_lt_three.le
    have h3q : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq3
    have hmono : Real.log 3 ≤ Real.log (q : ℝ) := Real.log_le_log h3 h3q
    linarith
  have hlogq_pos : (0 : ℝ) ≤ Real.log (q : ℝ) := le_trans zero_le_one hlogq1
  have hfrac : (0 : ℝ) ≤ 1 / (Real.log (q : ℝ) * Real.log (Real.log (q : ℝ))) := by
    rw [one_div_nonneg]
    exact mul_nonneg hlogq_pos (Real.log_nonneg hlogq1)
  have hsre : 1 ≤ s.re := by linarith
  -- The primitive character inducing `χ`.
  have hψne : χ.primitiveCharacter ≠ 1 := by
    intro h
    apply hχ
    rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h]
    exact DirichletCharacter.changeLevel_one χ.conductor_dvd_level
  have hψprim : (χ.primitiveCharacter).IsPrimitive := χ.primitiveCharacter_isPrimitive
  have hAn : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall 0 (|s.im| + 2)) :=
    fun z _ => (DirichletCharacter.differentiable_completedLFunction hψne).analyticAt z
  -- Divisor multiplicities are non-negative.
  have hDnn : ∀ u : ℂ, (0 : ℤ) ≤ MeromorphicOn.divisor
      (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall 0 (|s.im| + 2)) u :=
    fun u => (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAn) u
  -- Every zero of `Λ(·,χ*)` has real part `< 1`.
  have hzero_lt : ∀ u : ℂ, MeromorphicOn.divisor
      (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall 0 (|s.im| + 2)) u ≠ 0 → u.re < 1 := by
    intro u hdu
    have huB : u ∈ Metric.closedBall 0 (|s.im| + 2) := by
      by_contra hmem
      exact hdu (divisor_eq_zero_of_notMem hmem)
    have huz : DirichletCharacter.completedLFunction χ.primitiveCharacter u = 0 := by
      by_contra hfz
      exact hdu (divisor_eq_zero_of_analytic_ne_zero hAn huB hfz)
    exact (Commons.NumberTheory.Linnik.completedL_zero_strip χ.primitiveCharacter hψne hψprim
      huz).2
  -- `Re (1/(s-u)) ≥ 0` for every zero of `Λ(·,χ*)`.
  have hRnn : ∀ u : ℂ, MeromorphicOn.divisor
      (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall 0 (|s.im| + 2)) u ≠ 0 → 0 ≤ (1/(s-u)).re := by
    intro u hdu
    have hult : u.re < 1 := hzero_lt u hdu
    have hre : 0 ≤ (s-u).re := by rw [Complex.sub_re]; linarith
    calc (0 : ℝ) ≤ (s-u).re / Complex.normSq (s-u) :=
          div_nonneg hre (Complex.normSq_nonneg _)
      _ = (1/(s-u)).re := by rw [one_div, Complex.inv_re]
  -- hence every summand, multiplied by the multiplicity, is non-negative.
  have hprod : ∀ u : ℂ, 0 ≤ (((MeromorphicOn.divisor
      (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) : ℝ) * ((1/(s-u)).re) := by
    intro u
    by_cases h0 : MeromorphicOn.divisor (DirichletCharacter.completedLFunction
        χ.primitiveCharacter) (Metric.closedBall 0 (|s.im| + 2)) u = 0
    · rw [h0]; norm_num
    · exact mul_nonneg (by exact_mod_cast hDnn u) (hRnn u h0)
  -- Pointwise monotonicity of the window summands in the radius.
  have hpt : ∀ u : ℂ,
      (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
          (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) : ℝ) *
        (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ' then ((1/(s-u)).re) else 0)
      ≤ (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
          (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) : ℝ) *
        (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then ((1/(s-u)).re) else 0) := by
    intro u
    by_cases hc : ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ'
    · have hcδ : ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ := le_trans hc hδ
      refine le_of_eq ?_
      rw [if_pos hc, if_pos hcδ]
    · by_cases hc2 : ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ
      · have h1 : (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ'
            then ((1/(s-u)).re) else 0) = 0 := if_neg hc
        have h2 : (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ
            then ((1/(s-u)).re) else 0) = ((1/(s-u)).re) := if_pos hc2
        rw [h1, h2, mul_zero]
        exact hprod u
      · have h1 : (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ'
            then ((1/(s-u)).re) else 0) = 0 := if_neg hc
        have h2 : (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ
            then ((1/(s-u)).re) else 0) = 0 := if_neg hc2
        rw [h1, h2]
  -- Finite supports.
  have hsupp : (Function.support (fun u : ℂ =>
      MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall 0 (|s.im| + 2)) u)).Finite :=
    MeromorphicOn.divisor_support_finite_of_subset hAn.meromorphicOn
      (isCompact_closedBall 0 (|s.im| + 2)) (fun z hz => hz)
  have hsuppR : Function.HasFiniteSupport (fun u : ℂ =>
      (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) : ℝ)) :=
    hsupp.subset (by
      intro u hu
      rw [Function.mem_support] at hu ⊢
      intro h0
      exact hu (by rw [h0]; simp))
  have hfin1 : Function.HasFiniteSupport (fun u : ℂ =>
      (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) : ℝ) *
        (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ' then ((1/(s-u)).re) else 0)) :=
    hsuppR.subset (by
      intro u hu
      rw [Function.mem_support] at hu ⊢
      intro h0
      exact hu (by rw [h0]; simp))
  have hfin2 : Function.HasFiniteSupport (fun u : ℂ =>
      (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) : ℝ) *
        (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then ((1/(s-u)).re) else 0)) :=
    hsuppR.subset (by
      intro u hu
      rw [Function.mem_support] at hu ⊢
      intro h0
      exact hu (by rw [h0]; simp))
  have hS := finsum_le_finsum' hfin1 hfin2 hpt
  have hmain := H s hs1 hs2 hs3
  calc (-logDeriv (DirichletCharacter.LFunction χ.primitiveCharacter) s).re
        + (∑ᶠ u : ℂ, (((MeromorphicOn.divisor
            (DirichletCharacter.completedLFunction χ.primitiveCharacter)
            (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) : ℝ) *
              (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ' then ((1/(s-u)).re) else 0))
      ≤ (-logDeriv (DirichletCharacter.LFunction χ.primitiveCharacter) s).re
        + (∑ᶠ u : ℂ, (((MeromorphicOn.divisor
            (DirichletCharacter.completedLFunction χ.primitiveCharacter)
            (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) : ℝ) *
              (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then ((1/(s-u)).re) else 0)) :=
        add_le_add (le_refl _) hS
    _ ≤ (c + ε/4) * Real.log (q : ℝ) := hmain

end Work.LinnikAreas.DhCapped
