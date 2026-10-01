import Mathlib
import Submission.Work.ZeroFreeTables.Table4.Engine8
import Submission.Work.ZeroFreeTables.Table4.FarNear
import Submission.Work.ZeroFreeTables.P3Pos

namespace Work.ZeroFreeTables.HB95h2

open DirichletCharacter Complex
open scoped Classical BigOperators

/-- Points within `δ` of `1 + i·Im s` lie in the closed ball of radius `δ + 1 + |Im s|`. -/
private lemma mem_closedBall_of_near_kept {s u : ℂ} {δ : ℝ}
    (hnear : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ) :
    u ∈ Metric.closedBall (0 : ℂ) (δ + 1 + |s.im|) := by
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  have h3 : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I‖ ≤ 1 + |s.im| := by
    calc ‖(1 : ℂ) + (s.im : ℂ) * Complex.I‖
        ≤ ‖(1 : ℂ)‖ + ‖(s.im : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = 1 + |s.im| := by simp
  calc ‖u‖ ≤ ‖u - ((1 : ℂ) + (s.im : ℂ) * Complex.I)‖
              + ‖(1 : ℂ) + (s.im : ℂ) * Complex.I‖ := by
        have hh := norm_add_le (u - ((1 : ℂ) + (s.im : ℂ) * Complex.I))
          ((1 : ℂ) + (s.im : ℂ) * Complex.I)
        simpa using hh
    _ = ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖
              + ‖(1 : ℂ) + (s.im : ℂ) * Complex.I‖ := by rw [norm_sub_rev]
    _ ≤ δ + (1 + |s.im|) := by linarith
    _ = δ + 1 + |s.im| := by ring

/-- The combined kept `P₃` summand is summable: its support is contained in the prescribed
finite set `S` together with the zero set of `completedLFunction χ` inside the closed ball
containing the near disk, and that zero set is finite. -/
private theorem keptP3Summand_summable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) {L a lam₁ δ : ℝ} {s : ℂ} {S : Finset ℂ} :
    Summable (fun u : ℂ => (Work.LinnikContract.zeroMult χ u : ℝ)
      * Work.ZeroFreeTables.Table4.keptInd S s δ u
      * (Work.ZeroFreeTables.P3 (((a + lam₁ : ℝ) : ℂ) / ((s - u) * (L : ℂ)))).re) := by
  classical
  have hAn : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall (0 : ℂ) (δ + 1 + |s.im|)) :=
    fun z _ => (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z
  have hfinDiv : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall (0 : ℂ) (δ + 1 + |s.im|))).support.Finite := by
    simpa [Function.HasFiniteSupport] using
      (MeromorphicOn.divisor_support_finite_of_subset
        (f := DirichletCharacter.completedLFunction χ)
        (U := Metric.closedBall (0 : ℂ) (δ + 1 + |s.im|))
        (V := Metric.closedBall (0 : ℂ) (δ + 1 + |s.im|))
        hAn.meromorphicOn (isCompact_closedBall (0 : ℂ) (δ + 1 + |s.im|)) (le_refl _))
  refine summable_of_ne_finset_zero (s := S ∪ hfinDiv.toFinset) ?_
  intro u hu
  rw [Finset.mem_union, not_or] at hu
  obtain ⟨huS, huD⟩ := hu
  by_cases hB : u ∈ Metric.closedBall (0 : ℂ) (δ + 1 + |s.im|)
  · have hdiv0 : MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall (0 : ℂ) (δ + 1 + |s.im|)) u = 0 := by
      by_contra hne
      exact huD (by rw [Set.Finite.mem_toFinset, Function.mem_support]; exact hne)
    have hzm0 : Work.LinnikContract.zeroMult χ u = 0 := by
      have hqr : MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall (0 : ℂ) (δ + 1 + |s.im|)) u
          = (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℤ) := by
        rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hAn hB]
        simp only [analyticOrderNatAt]
        cases h : analyticOrderAt (DirichletCharacter.completedLFunction χ) u with
        | top => simp
        | coe n => simp
      have hzero : analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u = 0 := by
        have : (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℤ) = 0 := by
          rw [← hqr]; exact hdiv0
        exact_mod_cast this
      rw [Work.LinnikAreas.FarRepel.zeroMult_eq_analyticOrderNatAt_of_isPrimitive χ hprim u]
      exact hzero
    rw [hzm0]; ring
  · have hnear : ¬ ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ :=
      fun hc => hB (mem_closedBall_of_near_kept hc)
    have hki : Work.ZeroFreeTables.Table4.keptInd S s δ u = 0 := by
      rw [Work.ZeroFreeTables.Table4.keptInd_eq_ite,
        if_neg (fun h => h.elim huS hnear)]
    rw [hki]; ring

theorem keptExtractW {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) {a lam₁ L δ : ℝ} {s : ℂ} {S : Finset ℂ}
    (hL : 0 < L) (ha : 0 < a) (hlam₁ : 0 ≤ lam₁) (hδ : 0 < δ) (hsre : s.re = 1 + a / L)
    (hmin : ∀ v : ℂ, Work.LinnikContract.zeroMult χ v ≠ 0 →
      (v ∈ S ∨ ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - v‖ ≤ δ) → lam₁ ≤ (1 - v.re) * L) :
    ∑ u ∈ S, (Work.LinnikContract.zeroMult χ u : ℝ)
        * (Work.ZeroFreeTables.P3 (((a + lam₁ : ℝ) : ℂ) / ((s - u) * (L : ℂ)))).re
      ≤ Work.ZeroFreeTables.Table4.keptP3Sum N L χ s a lam₁ δ S := by
  classical
  have hsumm := keptP3Summand_summable (L := L) (a := a) (lam₁ := lam₁) (δ := δ)
    (s := s) (S := S) χ hχ hprim
  have hnonneg : ∀ u : ℂ, 0 ≤ (Work.LinnikContract.zeroMult χ u : ℝ)
      * Work.ZeroFreeTables.Table4.keptInd S s δ u
      * (Work.ZeroFreeTables.P3 (((a + lam₁ : ℝ) : ℂ) / ((s - u) * (L : ℂ)))).re := by
    intro u
    by_cases hz : Work.LinnikContract.zeroMult χ u = 0
    · rw [hz]; simp
    have hzpos : 0 < (Work.LinnikContract.zeroMult χ u : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hz
    by_cases hk : Work.ZeroFreeTables.Table4.keptInd S s δ u = 0
    · rw [hk]; simp
    have hcond : u ∈ S ∨ ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ := by
      by_contra hc
      rw [Work.ZeroFreeTables.Table4.keptInd_eq_ite, if_neg hc] at hk
      exact hk rfl
    have hle : lam₁ ≤ (1 - u.re) * L := hmin u hz hcond
    have hα : 0 < a + lam₁ := by linarith
    have hLsr : L * s.re = L + a := by rw [hsre]; field_simp
    have hzre : 1 ≤ ((((s - u) * (L : ℂ)) / (((a + lam₁ : ℝ)) : ℂ))).re := by
      have h3 : ((((s - u) * (L : ℂ)) / (((a + lam₁ : ℝ)) : ℂ))).re
          = L * (s.re - u.re) / (a + lam₁) := by
        rw [show ((s - u) * (L : ℂ)) / (((a + lam₁ : ℝ)) : ℂ)
            = (((L / (a + lam₁) : ℝ)) : ℂ) * (s - u) by push_cast; ring]
        rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
          Complex.sub_re]
        ring
      rw [h3, le_div_iff₀ hα]
      nlinarith [hle, hLsr]
    have hnn' : 0 ≤ (Work.ZeroFreeTables.P3
        ((((s - u) * (L : ℂ)) / (((a + lam₁ : ℝ)) : ℂ)))⁻¹).re :=
      Work.ZeroFreeTables.P3_inv_re_nonneg _ hzre
    have harg : ((((s - u) * (L : ℂ)) / (((a + lam₁ : ℝ)) : ℂ)))⁻¹
        = (((a + lam₁ : ℝ)) : ℂ) / ((s - u) * (L : ℂ)) := by rw [inv_div]
    rw [← harg]
    exact mul_nonneg (mul_nonneg hzpos.le (Work.ZeroFreeTables.Table4.keptInd_nonneg S s δ u))
      hnn'
  have hcongr : ∑ u ∈ S, (Work.LinnikContract.zeroMult χ u : ℝ)
        * (Work.ZeroFreeTables.P3 (((a + lam₁ : ℝ) : ℂ) / ((s - u) * (L : ℂ)))).re
      = ∑ u ∈ S, (Work.LinnikContract.zeroMult χ u : ℝ)
        * Work.ZeroFreeTables.Table4.keptInd S s δ u
        * (Work.ZeroFreeTables.P3 (((a + lam₁ : ℝ) : ℂ) / ((s - u) * (L : ℂ)))).re := by
    refine Finset.sum_congr rfl (fun u hu => ?_)
    rw [Work.ZeroFreeTables.Table4.keptInd_eq_ite, if_pos (Or.inl hu)]
    ring
  rw [hcongr, Work.ZeroFreeTables.Table4.keptP3Sum]
  exact Summable.sum_le_tsum S (fun i _ => hnonneg i) hsumm

end Work.ZeroFreeTables.HB95h2
