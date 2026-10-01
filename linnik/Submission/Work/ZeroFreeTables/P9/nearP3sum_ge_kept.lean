import Mathlib
import Submission.Work.ZeroFreeTables.P9.Defs
import Submission.Work.ZeroFreeTables.P9.NearSummandDefs
import Submission.Work.ZeroFreeTables.P9.NearSummandLemmas
import Submission.Work.ZeroFreeTables.P3.DefsL
import Submission.Work.ZeroFreeTables.P3Pos
import Submission.Work.LinnikAreas.boxMaxZero
import Submission.Work.ZeroFreeTables.P9.P3term_abs_le_of_far
import Submission.Work.ZeroFreeTables.P9.nearP3summand_mem_box

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables.P9

theorem nearP3sum_ge_kept {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    {L a lam₁ δ : ℝ} (hL : 0 < L) (ha : 0 < a) (hlam₁ : 0 ≤ lam₁) (hδ : 0 < δ) (hδ1 : δ < 1)
    (haδ : 2 * a ≤ δ * L) {s : ℂ} (hsre : s.re = 1 + a / L) (hsim : |s.im| ≤ 3)
    (hmin : ∀ u : ℂ, Work.LinnikContract.zeroMult χ u ≠ 0 → |u.im| ≤ 10 → lam₁ ≤ (1 - u.re) * L)
    (T : Finset ℂ) (hT : ∀ u ∈ T, Work.LinnikContract.zeroMult χ u ≠ 0)
    (hTim : ∀ u ∈ T, |u.im| ≤ 10) :
    ∑ u ∈ T, (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re
      ≤ Work.ZeroFreeTables.P9.nearP3sum N L χ s a lam₁ δ
        + (T.card : ℝ) * (8 * (a + lam₁) / (δ * L)) := by
  classical
  -- the box `|Im| ≤ 4` containing the support of the summand
  set S : Finset ℂ := (Work.LinnikAreas.boxMaxZeroAux.finite_zeroMult_box χ 0 4).toFinset with hS
  have hmemS : ∀ u : ℂ, u ∈ S ↔
      Work.LinnikContract.zeroMult χ u ≠ 0 ∧ 0 ≤ u.re ∧ u.re ≤ 1 ∧ |u.im| ≤ 4 := by
    intro u
    rw [hS, Set.Finite.mem_toFinset]
    rfl
  -- the summand vanishes off `S`
  have hsupp : ∀ u : ℂ, u ∉ S → nearP3summand N L χ s a lam₁ δ u = 0 := by
    intro u hu
    by_contra h
    exact hu ((hmemS u).mpr (nearP3summand_mem_box χ hχ hδ1 hsim u h))
  -- `nearP3sum` is the sum over `S ∪ T`
  have htsum : Work.ZeroFreeTables.P9.nearP3sum N L χ s a lam₁ δ
      = ∑ u ∈ S ∪ T, nearP3summand N L χ s a lam₁ δ u := by
    rw [nearP3sum_eq_tsum]
    exact tsum_eq_sum (s := S ∪ T) (fun u hu => hsupp u (fun h => hu (Finset.mem_union_left _ h)))
  -- the `δ`-window
  set p : ℂ → Prop := fun u => ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ with hp
  have hTsplit : ∑ u ∈ T, (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re
      = ∑ u ∈ T.filter p, (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re
        + ∑ u ∈ T.filter (fun u => ¬ p u),
            (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re :=
    (Finset.sum_filter_add_sum_filter_not T p _).symm
  -- the zeros of `T` inside the window are dominated term by term by `nearP3sum`
  have hnear_pt : ∀ u ∈ T.filter p,
      (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re
        ≤ nearP3summand N L χ s a lam₁ δ u := by
    intro u hu
    rw [Finset.mem_filter] at hu
    obtain ⟨huT, hpu⟩ := hu
    rw [nearP3summand_eq_P3]
    have hind : nearInd s δ u = 1 := by
      rw [nearInd_eq_ite]
      exact if_pos (by simpa [hp] using hpu)
    rw [hind, mul_one]
    have hmult : (1 : ℝ) ≤ (Work.LinnikContract.zeroMult χ u : ℝ) := by
      have := hT u huT
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
    have hP3 : 0 ≤ (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re := by
      have hnn := nearP3summand_nonneg χ hL ha hlam₁ hδ1 hsre hsim hmin u
      rw [nearP3summand_eq_P3, hind, mul_one] at hnn
      by_contra hcon
      push Not at hcon
      have hpos : 0 < (Work.LinnikContract.zeroMult χ u : ℝ) := by linarith
      have hlt := mul_lt_mul_of_pos_left hcon hpos
      rw [mul_zero] at hlt
      linarith
    calc (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re
        = 1 * (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re := by ring
      _ ≤ (Work.LinnikContract.zeroMult χ u : ℝ)
            * (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re :=
          mul_le_mul_of_nonneg_right hmult hP3
  have hnear : ∑ u ∈ T.filter p,
        (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re
      ≤ ∑ u ∈ S ∪ T, nearP3summand N L χ s a lam₁ δ u :=
    le_trans (Finset.sum_le_sum hnear_pt)
      (Finset.sum_le_sum_of_subset_of_nonneg
        (fun u hu => Finset.mem_union_right S (Finset.mem_filter.mp hu).1)
        (fun u _ _ => nearP3summand_nonneg χ hL ha hlam₁ hδ1 hsre hsim hmin u))
  -- the zeros of `T` outside the window are bounded by the far constant
  have hfar : ∑ u ∈ T.filter (fun u => ¬ p u),
        (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re
      ≤ (T.card : ℝ) * (8 * (a + lam₁) / (δ * L)) := by
    have hconst : 0 ≤ 8 * (a + lam₁) / (δ * L) := by positivity
    have hpt : ∀ u ∈ T.filter (fun u => ¬ p u),
        (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re
          ≤ 8 * (a + lam₁) / (δ * L) := by
      intro u hu
      rw [Finset.mem_filter] at hu
      obtain ⟨huT, hpu⟩ := hu
      have hminu : lam₁ ≤ (1 - u.re) * L := hmin u (hT u huT) (hTim u huT)
      have hpune : ¬ (‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ) := by simpa [hp] using hpu
      have hfar_lt : δ < ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ := lt_of_not_ge hpune
      exact le_trans (le_abs_self _) (P3term_abs_le_of_far hL ha hlam₁ hδ haδ hsre hminu hfar_lt)
    calc ∑ u ∈ T.filter (fun u => ¬ p u),
          (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re
        ≤ ∑ u ∈ T.filter (fun u => ¬ p u), 8 * (a + lam₁) / (δ * L) := Finset.sum_le_sum hpt
      _ = ((T.filter (fun u => ¬ p u)).card : ℝ) * (8 * (a + lam₁) / (δ * L)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (T.card : ℝ) * (8 * (a + lam₁) / (δ * L)) := by
          apply mul_le_mul_of_nonneg_right _ hconst
          exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
  rw [hTsplit]
  linarith [hnear, hfar, htsum]

end Work.ZeroFreeTables.P9
