import Mathlib
import Submission.Work.ZeroFreeTables.lam0w.FarBound
import Submission.Work.ZeroFreeTables.HB94.Lam0GeEngine

namespace Work.ZeroFreeTables.OffAxis

open Work.ZeroFreeTables

/-! ## Helper lemmas: the `P₃` terms of the kept-zero sums in `P3AB` normal form -/

/-- **Evenness of `P3AB` in its third argument, with no hypothesis on `β`.**
`P3AB α β t = Re P₃(α/(β+it))` is unchanged under `t ↦ -t` because the map
`t ↦ α/(β+it)` becomes its complex conjugate (for real `α`, `β`) and `P₃` has real
coefficients.  (The library version `P3AB_neg` assumes `0 < β`; here `β = a + λ₀`
need not be positive, so we prove the general statement.) -/
lemma P3AB_neg_gen (α β t : ℝ) :
    Work.ZeroFreeTables.Table4.P3AB α β (-t) = Work.ZeroFreeTables.Table4.P3AB α β t := by
  unfold Work.ZeroFreeTables.Table4.P3AB
  have h : starRingEnd ℂ ((α : ℂ) / ((β : ℂ) + (t : ℂ) * Complex.I))
      = ((α : ℂ) / ((β : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)) := by
    rw [map_div₀, map_add, map_mul]
    simp only [Complex.conj_ofReal]
    rw [Complex.conj_I]
    congr 1
    push_cast
    ring
  rw [← h, Work.ZeroFreeTables.HB94.Lam0GeEngine.P3_re_conj]

/-- A kept-zero term at the test point `sPt a L t` in the `P3AB` normal form: for a zero
`ρ` with `ρ.re = 1 - lam/L`, `ρ.im = gam`,
`Re P₃((a+λ₁)/((sPt a L t - ρ)𝓛)) = P3AB (a+λ₁) (a+lam) ((t - gam)L)`. -/
lemma P3_sPt_split {a L lam1 lam gam t : ℝ} (hL : L ≠ 0) {ρ : ℂ}
    (hre : ρ.re = 1 - lam / L) (him : ρ.im = gam) :
    (Work.ZeroFreeTables.P3 (((a : ℂ) + (lam1 : ℂ)) /
        ((Work.ZeroFreeTables.HB94.Lam0GeEngine.sPt a L t - ρ) * (L : ℂ)))).re
      = Work.ZeroFreeTables.Table4.P3AB (a + lam1) (a + lam) ((t - gam) * L) := by
  have h := Work.ZeroFreeTables.HB94.Lam0GeEngine.P3_arg_eq_split (a := a) (L := L)
    (lam₁ := lam1) (lam := lam) (gam := gam) (t := t) hL hre him
  simpa only [Work.ZeroFreeTables.Table4.P3AB, Work.ZeroFreeTables.P9.PhiG] using h

/-- The pole (`u = 1`) term at the test point `sPt a L t` in the `P3AB` normal form:
`Re P₃((a+λ₁)/((sPt a L t - 1)𝓛)) = P3AB (a+λ₁) a (t𝓛)`. -/
lemma P3_sPt_pole {a L lam1 t : ℝ} (hL : L ≠ 0) :
    (Work.ZeroFreeTables.P3 (((a : ℂ) + (lam1 : ℂ)) /
        ((Work.ZeroFreeTables.HB94.Lam0GeEngine.sPt a L t - 1) * (L : ℂ)))).re
      = Work.ZeroFreeTables.Table4.P3AB (a + lam1) a (t * L) := by
  have h := Work.ZeroFreeTables.HB94.Lam0GeEngine.P3_arg_eq_pole_split (a := a) (L := L)
    (t := t) (lam := lam1) hL
  simpa only [Work.ZeroFreeTables.Table4.P3AB, Work.ZeroFreeTables.P9.PhiG] using h

theorem hb83KeptSums {L a lam1 lam0 γ : ℝ} {ρ1 ρ0 : ℂ}
    (hL : L ≠ 0) (ha : 0 < a) (hlam1 : 0 ≤ lam1) (hγ : γ = ρ0.im)
    (hr1 : ρ1.re = 1 - lam1 / L) (hr0 : ρ0.re = 1 - lam0 / L)
    (him1 : ρ1.im = 0) (hne : ρ1 ≠ ρ0) (him0 : ρ0.im ≠ 0) :
    (∑ u ∈ ({ρ1, ρ0} : Finset ℂ),
        (Work.ZeroFreeTables.P3
          (((a : ℂ) + (lam1 : ℂ)) / ((Work.ZeroFreeTables.HB94.Lam0GeEngine.sPt a L 0 - u) * (L : ℂ)))).re)
      = Work.ZeroFreeTables.P3R 1
        + Work.ZeroFreeTables.Table4.P3AB (a + lam1) (a + lam0) (γ * L) ∧
    (∑ u ∈ ({ρ1, ρ0, starRingEnd ℂ ρ0} : Finset ℂ),
        (Work.ZeroFreeTables.P3
          (((a : ℂ) + (lam1 : ℂ)) / ((Work.ZeroFreeTables.HB94.Lam0GeEngine.sPt a L γ - u) * (L : ℂ)))).re)
      = Work.ZeroFreeTables.Table4.P3AB (a + lam1) (a + lam1) (γ * L)
        + Work.ZeroFreeTables.P3R ((a + lam1) / (a + lam0))
        + Work.ZeroFreeTables.Table4.P3AB (a + lam1) (a + lam0) (2 * γ * L) ∧
    (∑ u ∈ ({ρ1, ρ0} : Finset ℂ),
        (Work.ZeroFreeTables.P3
          (((a : ℂ) + (lam1 : ℂ)) / ((Work.ZeroFreeTables.HB94.Lam0GeEngine.sPt a L (2 * γ) - u) * (L : ℂ)))).re)
      = Work.ZeroFreeTables.Table4.P3AB (a + lam1) (a + lam1) (2 * γ * L)
        + Work.ZeroFreeTables.Table4.P3AB (a + lam1) (a + lam0) (γ * L) ∧
    (Work.ZeroFreeTables.P3
        (((a : ℂ) + (lam1 : ℂ)) / ((Work.ZeroFreeTables.HB94.Lam0GeEngine.sPt a L 0 - 1) * (L : ℂ)))).re
      = Work.ZeroFreeTables.P3R ((a + lam1) / a) ∧
    (Work.ZeroFreeTables.P3
        (((a : ℂ) + (lam1 : ℂ)) / ((Work.ZeroFreeTables.HB94.Lam0GeEngine.sPt a L γ - 1) * (L : ℂ)))).re
      = Work.ZeroFreeTables.Table4.P3AB (a + lam1) a (γ * L) ∧
    (Work.ZeroFreeTables.P3
        (((a : ℂ) + (lam1 : ℂ)) / ((Work.ZeroFreeTables.HB94.Lam0GeEngine.sPt a L (2 * γ) - 1) * (L : ℂ)))).re
      = Work.ZeroFreeTables.Table4.P3AB (a + lam1) a (2 * γ * L) := by
  classical
  have him0' : ρ0.im = γ := hγ.symm
  have hβ1 : (0 : ℝ) < a + lam1 := by linarith
  have hne0c : ρ0 ≠ starRingEnd ℂ ρ0 := by
    intro h
    have h2 : ρ0.im = -ρ0.im := by
      have := congrArg Complex.im h
      simpa using this
    exact him0 (by linarith)
  have hne1c : ρ1 ≠ starRingEnd ℂ ρ0 := by
    intro h
    have h2 : ρ1.im = -ρ0.im := by
      have := congrArg Complex.im h
      simpa using this
    rw [him1] at h2
    exact him0 (by linarith)
  have hrec : (starRingEnd ℂ ρ0).re = 1 - lam0 / L := by
    rw [show (starRingEnd ℂ ρ0).re = ρ0.re by simp]
    exact hr0
  have himc : (starRingEnd ℂ ρ0).im = -γ := by
    rw [show (starRingEnd ℂ ρ0).im = -ρ0.im by simp]
    rw [← hγ]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Finset.sum_pair hne]
    have e1 : (Work.ZeroFreeTables.P3 (((a : ℂ) + (lam1 : ℂ)) /
          ((Work.ZeroFreeTables.HB94.Lam0GeEngine.sPt a L 0 - ρ1) * (L : ℂ)))).re
        = Work.ZeroFreeTables.P3R 1 := by
      rw [P3_sPt_split (a := a) (L := L) (lam := lam1) (gam := 0) (t := 0) hL hr1 him1]
      rw [show ((0 : ℝ) - 0) * L = 0 by ring]
      rw [Work.ZeroFreeTables.Table4.P3AB_zero, div_self (ne_of_gt hβ1)]
    have e2 : (Work.ZeroFreeTables.P3 (((a : ℂ) + (lam1 : ℂ)) /
          ((Work.ZeroFreeTables.HB94.Lam0GeEngine.sPt a L 0 - ρ0) * (L : ℂ)))).re
        = Work.ZeroFreeTables.Table4.P3AB (a + lam1) (a + lam0) (γ * L) := by
      rw [P3_sPt_split (a := a) (L := L) (lam := lam0) (gam := γ) (t := 0) hL hr0 him0']
      rw [show ((0 : ℝ) - γ) * L = -(γ * L) by ring]
      rw [P3AB_neg_gen]
    rw [e1, e2]
  · rw [show ({ρ1, ρ0, starRingEnd ℂ ρ0} : Finset ℂ)
        = insert ρ1 (insert ρ0 {starRingEnd ℂ ρ0}) by rfl]
    rw [Finset.sum_insert (by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hne, hne1c⟩),
      Finset.sum_insert (by simp only [Finset.mem_singleton]; exact hne0c),
      Finset.sum_singleton]
    rw [P3_sPt_split (a := a) (L := L) (lam := lam1) (gam := 0) (t := γ) hL hr1 him1]
    rw [P3_sPt_split (a := a) (L := L) (lam := lam0) (gam := γ) (t := γ) hL hr0 him0']
    rw [P3_sPt_split (a := a) (L := L) (lam := lam0) (gam := -γ) (t := γ) hL hrec himc]
    rw [show ((γ : ℝ) - 0) * L = γ * L by ring]
    rw [show ((γ : ℝ) - γ) * L = 0 by ring]
    rw [show ((γ : ℝ) - -γ) * L = 2 * γ * L by ring]
    rw [Work.ZeroFreeTables.Table4.P3AB_zero]
    ring
  · rw [Finset.sum_pair hne]
    rw [P3_sPt_split (a := a) (L := L) (lam := lam1) (gam := 0) (t := 2 * γ) hL hr1 him1]
    rw [P3_sPt_split (a := a) (L := L) (lam := lam0) (gam := γ) (t := 2 * γ) hL hr0 him0']
    rw [show (((2 : ℝ) * γ) - 0) * L = 2 * γ * L by ring]
    rw [show (((2 : ℝ) * γ) - γ) * L = γ * L by ring]
  · rw [P3_sPt_pole (a := a) (L := L) (lam1 := lam1) (t := 0) hL]
    rw [show ((0 : ℝ) * L) = 0 by ring]
    rw [Work.ZeroFreeTables.Table4.P3AB_zero]
  · rw [P3_sPt_pole (a := a) (L := L) (lam1 := lam1) (t := γ) hL]
  · rw [P3_sPt_pole (a := a) (L := L) (lam1 := lam1) (t := 2 * γ) hL]

end Work.ZeroFreeTables.OffAxis
