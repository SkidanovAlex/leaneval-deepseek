import Mathlib
import Submission.Work.LinnikAreas.OtherCharRepel.LFunction_eq_primitiveCharacter_mul
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_TuranOther_lFunctionOrderAddInvGammaR

namespace Work.LinnikAreas.turanAux2

open DirichletCharacter Complex

/-- Evenness of a Dirichlet character is preserved when passing to its primitive character. -/
lemma even_primitiveCharacter_iff {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    [NeZero χ.conductor] : χ.Even ↔ χ.primitiveCharacter.Even := by
  have hkey : χ (-1) = χ.primitiveCharacter (-1) := by
    have h1 : (changeLevel χ.conductor_dvd_level) χ.primitiveCharacter (-1)
        = χ.primitiveCharacter (-1) := by
      simpa using changeLevel_eq_cast_of_dvd' χ.primitiveCharacter χ.conductor_dvd_level
        (a := -1) ((IsCoprime.neg_left_iff _ _).mpr isCoprime_one_left)
    rw [← h1]
    exact (DFunLike.congr_fun (changeLevel_primitiveCharacter (χ := χ)) (-1)).symm
  simp only [DirichletCharacter.Even]
  rw [hkey]

/-- The archimedean Gamma factor of a Dirichlet character agrees with that of its primitive
character. -/
lemma gammaFactor_primitiveCharacter {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    [NeZero χ.conductor] :
    DirichletCharacter.gammaFactor χ = DirichletCharacter.gammaFactor χ.primitiveCharacter := by
  funext s
  rcases χ.even_or_odd with h | h
  · rw [h.gammaFactor_def, (even_primitiveCharacter_iff χ).mp h |>.gammaFactor_def]
  · have h' : χ.primitiveCharacter.Odd := by
      rcases χ.primitiveCharacter.even_or_odd with h'' | h''
      · exact absurd ((even_primitiveCharacter_iff χ).mpr h'') h.not_even
      · exact h''
    rw [h.gammaFactor_def, h'.gammaFactor_def]

theorem completedLFunction_primitiveFactor {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q)
    [NeZero ψ.conductor] (hψ : ψ ≠ 1) :
    DirichletCharacter.completedLFunction ψ
      = fun s : ℂ => DirichletCharacter.completedLFunction ψ.primitiveCharacter s *
          ∏ p ∈ q.primeFactors,
            (1 - ψ.primitiveCharacter (p : ZMod ψ.conductor) * (p : ℂ) ^ (-s)) := by
  have hprim : ψ.primitiveCharacter ≠ 1 := by
    intro h
    apply hψ
    rw [← changeLevel_primitiveCharacter (χ := ψ), h]
    exact changeLevel_one _
  have hq : q ≠ 1 := fun h => hψ (level_one' ψ h)
  have hm : ψ.conductor ≠ 1 := fun h => hprim (level_one' ψ.primitiveCharacter h)
  have hP : Differentiable ℂ (fun s : ℂ => ∏ p ∈ q.primeFactors,
        (1 - ψ.primitiveCharacter (p : ZMod ψ.conductor) * (p : ℂ) ^ (-s))) := by
    refine Differentiable.fun_finsetProd fun p hp => ?_
    have : NeZero p := ⟨(Nat.pos_of_mem_primeFactors hp).ne'⟩
    fun_prop
  have hpoint : ∀ s : ℂ, 1 < s.re →
      DirichletCharacter.completedLFunction ψ s =
        DirichletCharacter.completedLFunction ψ.primitiveCharacter s *
          ∏ p ∈ q.primeFactors,
            (1 - ψ.primitiveCharacter (p : ZMod ψ.conductor) * (p : ℂ) ^ (-s)) := by
    intro s hs
    have hs0 : (s).Gammaℝ ≠ 0 := Gammaℝ_ne_zero_of_re_pos (lt_trans zero_lt_one hs)
    have hs1 : (s + 1).Gammaℝ ≠ 0 :=
      Gammaℝ_ne_zero_of_re_pos (by rw [Complex.add_re, Complex.one_re]; linarith)
    have hgψ : DirichletCharacter.gammaFactor ψ s ≠ 0 := by
      rcases ψ.even_or_odd with h | h
      · rw [h.gammaFactor_def]; exact hs0
      · rw [h.gammaFactor_def]; exact hs1
    have hgprim : DirichletCharacter.gammaFactor ψ.primitiveCharacter s ≠ 0 := by
      rw [← congr_fun (gammaFactor_primitiveCharacter ψ) s]
      exact hgψ
    have hF_eq : DirichletCharacter.gammaFactor ψ s * DirichletCharacter.LFunction ψ s
        = DirichletCharacter.completedLFunction ψ s := by
      rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor ψ s (Or.inr hq),
        mul_div_cancel₀ (DirichletCharacter.completedLFunction ψ s) hgψ]
    have hP_eq : DirichletCharacter.gammaFactor ψ.primitiveCharacter s *
          DirichletCharacter.LFunction ψ.primitiveCharacter s
        = DirichletCharacter.completedLFunction ψ.primitiveCharacter s := by
      rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor ψ.primitiveCharacter s
            (Or.inr hm),
        mul_div_cancel₀ (DirichletCharacter.completedLFunction ψ.primitiveCharacter s) hgprim]
    calc DirichletCharacter.completedLFunction ψ s
        = DirichletCharacter.gammaFactor ψ s * DirichletCharacter.LFunction ψ s := hF_eq.symm
      _ = DirichletCharacter.gammaFactor ψ.primitiveCharacter s *
            (DirichletCharacter.LFunction ψ.primitiveCharacter s *
              ∏ p ∈ q.primeFactors,
                (1 - ψ.primitiveCharacter (p : ZMod ψ.conductor) * (p : ℂ) ^ (-s))) := by
            rw [congr_fun (gammaFactor_primitiveCharacter ψ) s,
              Work.LinnikAreas.OtherCharRepel.LFunction_eq_primitiveCharacter_mul ψ hψ s]
      _ = (DirichletCharacter.gammaFactor ψ.primitiveCharacter s *
              DirichletCharacter.LFunction ψ.primitiveCharacter s) *
            ∏ p ∈ q.primeFactors,
              (1 - ψ.primitiveCharacter (p : ZMod ψ.conductor) * (p : ℂ) ^ (-s)) := by ring
      _ = DirichletCharacter.completedLFunction ψ.primitiveCharacter s *
            ∏ p ∈ q.primeFactors,
              (1 - ψ.primitiveCharacter (p : ZMod ψ.conductor) * (p : ℂ) ^ (-s)) := by
            rw [hP_eq]
  refine AnalyticOnNhd.eq_of_eventuallyEq (𝕜 := ℂ) (z₀ := 2) ?_ ?_ ?_
  · intro z _
    exact (differentiable_completedLFunction hψ).analyticAt z
  · intro z _
    exact ((differentiable_completedLFunction hprim).mul hP).analyticAt z
  · exact Filter.eventually_of_mem
      ((Complex.continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds
        (by norm_num : (1 : ℝ) < (2 : ℂ).re)) hpoint

end Work.LinnikAreas.turanAux2
