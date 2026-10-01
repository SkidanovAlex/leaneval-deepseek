import Mathlib
import Submission.Work.ZeroDensity.LogFree.ZFImports
import Submission.Work.ZeroDensity.LogFree.excZeroReal
import Submission.Work.LinnikAreas.OtherCharRepel.twoRealCharRepel

namespace Work.ZeroDensity.LogFree

open DirichletCharacter

/-- If the primitive character inducing `χ` is real (`χ*·χ* = 1`) then so is `χ` itself:
`χ` is the `changeLevel` of `χ*` to the level of `χ`, and `changeLevel` is a monoid hom. -/
lemma sq_eq_one_of_primitiveCharacter_sq_eq_one {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (h : χ.primitiveCharacter ^ 2 = 1) : χ ^ 2 = 1 := by
  have h' := congrArg (DirichletCharacter.changeLevel χ.conductor_dvd_level) h
  simpa only [map_pow, map_one, DirichletCharacter.changeLevel_primitiveCharacter] using h'

/-- Comparison of the two normalisations `λ(ρ) = (1-Re ρ)·log q` and `(1-Re ρ)·Lscale q T`:
for `q ≥ 2` and `T ≥ 1` the logarithmic parameter `Lscale q T = log(q(T+2))` dominates `log q`,
so `(1-Re ρ)·Lscale q T < c` forces `λ(ρ) < c` whenever `c > 0`. -/
private lemma lamOf_lt_of_mul_Lscale_lt {q : ℕ} (hq : 2 ≤ q) {T : ℝ} (hT : 1 ≤ T)
    {ρ : ℂ} {c : ℝ} (hc : 0 < c) (h : (1 - ρ.re) * Lscale q T < c) :
    Work.LinnikContract.lamOf q ρ < c := by
  rw [Work.LinnikContract.lamOf]
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hlogq_nonneg : 0 ≤ Real.log (q : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ q))
  have hlogq_le : Real.log (q : ℝ) ≤ Lscale q T := by
    rw [Lscale, scale]
    exact Real.log_le_log hqpos (by nlinarith [hT, hqpos.le])
  rcases le_or_gt (1 - ρ.re) 0 with h' | h'
  · have : (1 - ρ.re) * Real.log (q : ℝ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h' hlogq_nonneg
    linarith
  · have : (1 - ρ.re) * Real.log (q : ℝ) ≤ (1 - ρ.re) * Lscale q T :=
      mul_le_mul_of_nonneg_left hlogq_le h'.le
    linarith

theorem excCharUnique :
    ∃ c : ℝ, 0 < c ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (T : ℝ), 1 ≤ T →
      ∀ χ₁ χ₂ : DirichletCharacter ℂ q, χ₁ ≠ 1 → χ₂ ≠ 1 → χ₁ ≠ χ₂ →
        ¬ ((∃ ρ₁ : ℂ, Work.LinnikContract.zeroMult χ₁ ρ₁ ≠ 0 ∧ |ρ₁.im| ≤ T ∧
              (1 - ρ₁.re) * Work.ZeroDensity.LogFree.Lscale q T < c) ∧
           (∃ ρ₂ : ℂ, Work.LinnikContract.zeroMult χ₂ ρ₂ ≠ 0 ∧ |ρ₂.im| ≤ T ∧
              (1 - ρ₂.re) * Work.ZeroDensity.LogFree.Lscale q T < c)) := by
  -- the two inputs: zeros that close to the line are real zeros of real characters
  -- (uniform zero-free regions), and Landau repulsion for distinct real characters
  obtain ⟨c₀, hc₀pos, h₀⟩ := excZeroReal
  obtain ⟨c₂, hc₂pos, q₂, h₂⟩ := Work.LinnikAreas.OtherCharRepel.twoRealCharRepel
  refine ⟨min c₀ c₂, lt_min hc₀pos hc₂pos, max q₂ 2, ?_⟩
  intro q hq _ T hT χ₁ χ₂ hχ₁ hχ₂ hχ₁χ₂ h
  obtain ⟨⟨ρ₁, hzm₁, him₁, hsmall₁⟩, ⟨ρ₂, hzm₂, him₂, hsmall₂⟩⟩ := h
  have hq2 : 2 ≤ q := le_trans (le_max_right q₂ 2) hq
  have hqq₂ : q₂ ≤ q := le_trans (le_max_left q₂ 2) hq
  have hsmall₁₀ : (1 - ρ₁.re) * Lscale q T < c₀ := lt_of_lt_of_le hsmall₁ (min_le_left _ _)
  have hsmall₂₀ : (1 - ρ₂.re) * Lscale q T < c₀ := lt_of_lt_of_le hsmall₂ (min_le_left _ _)
  obtain ⟨him₁0, hpc₁⟩ := h₀ q hq2 χ₁ hχ₁ ρ₁ T hT him₁ hzm₁ hsmall₁₀
  obtain ⟨him₂0, hpc₂⟩ := h₀ q hq2 χ₂ hχ₂ ρ₂ T hT him₂ hzm₂ hsmall₂₀
  have hsq₁ : χ₁ ^ 2 = 1 := sq_eq_one_of_primitiveCharacter_sq_eq_one hpc₁
  have hsq₂ : χ₂ ^ 2 = 1 := sq_eq_one_of_primitiveCharacter_sq_eq_one hpc₂
  have hrepel : c₂ ≤ max (Work.LinnikContract.lamOf q ρ₁) (Work.LinnikContract.lamOf q ρ₂) :=
    h₂ q hqq₂ χ₁ ρ₁ χ₂ ρ₂ hχ₁ hsq₁ him₁0 hzm₁ hχ₂ hsq₂ him₂0 hzm₂ (Ne.symm hχ₁χ₂)
  have hlam₁ : Work.LinnikContract.lamOf q ρ₁ < c₂ :=
    lamOf_lt_of_mul_Lscale_lt hq2 hT hc₂pos (lt_of_lt_of_le hsmall₁ (min_le_right _ _))
  have hlam₂ : Work.LinnikContract.lamOf q ρ₂ < c₂ :=
    lamOf_lt_of_mul_Lscale_lt hq2 hT hc₂pos (lt_of_lt_of_le hsmall₂ (min_le_right _ _))
  exact absurd hrepel (not_le.mpr (max_lt hlam₁ hlam₂))

end Work.ZeroDensity.LogFree
