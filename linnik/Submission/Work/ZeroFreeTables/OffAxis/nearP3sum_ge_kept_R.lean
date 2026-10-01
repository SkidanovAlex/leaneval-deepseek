import Mathlib
import Submission.Work.ZeroFreeTables.P9.nearP3sum_ge_kept
import Submission.Work.ZeroFreeTables.P9.NearP3summandMemBoxGen
import Submission.Work.ZeroFreeTables.P9.NearP3summandNonnegWindow
import Submission.Work.ZeroFreeTables.P9.P3term_abs_le_of_far

namespace Work.ZeroFreeTables.OffAxis

theorem nearP3sum_ge_kept_R {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    {L a lam₁ δ R : ℝ} (hL : 0 < L) (ha : 0 < a) (hlam₁ : 0 ≤ lam₁) (hδ : 0 < δ) (hδ1 : δ < 1)
    (haδ : 2 * a ≤ δ * L) {s : ℂ} (hsre : s.re = 1 + a / L) (hsim : |s.im| ≤ R)
    (hmin : ∀ u : ℂ, Work.LinnikContract.zeroMult χ u ≠ 0 → |u.im| ≤ R + 1 →
      lam₁ ≤ (1 - u.re) * L)
    (T : Finset ℂ) (hT : ∀ u ∈ T, Work.LinnikContract.zeroMult χ u ≠ 0)
    (hTim : ∀ u ∈ T, |u.im| ≤ R + 1) :
    ∑ u ∈ T, (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re
      ≤ Work.ZeroFreeTables.P9.nearP3sum N L χ s a lam₁ δ
        + (T.card : ℝ) * (8 * (a + lam₁) / (δ * L)) := by
  classical
  -- the box `|Im| ≤ R + 1` containing the support of the summand
  set S : Finset ℂ := (Work.LinnikAreas.boxMaxZeroAux.finite_zeroMult_box χ 0 (R + 1)).toFinset
    with hS
  have hmemS : ∀ u : ℂ, u ∈ S ↔
      Work.LinnikContract.zeroMult χ u ≠ 0 ∧ 0 ≤ u.re ∧ u.re ≤ 1 ∧ |u.im| ≤ R + 1 := by
    intro u
    rw [hS, Set.Finite.mem_toFinset]
    rfl
  -- the summand vanishes off `S`
  have hsupp : ∀ u : ℂ, u ∉ S →
      Work.ZeroFreeTables.P9.nearP3summand N L χ s a lam₁ δ u = 0 := by
    intro u hu
    by_contra h
    have hbox := Work.ZeroFreeTables.P9.NearP3summandMemBoxGen χ h
    obtain ⟨hzm, hre1, hre2, him⟩ := hbox
    exact hu ((hmemS u).mpr ⟨hzm, by linarith, hre2, by linarith⟩)
  -- `nearP3sum` is the sum over `S ∪ T`
  have htsum : Work.ZeroFreeTables.P9.nearP3sum N L χ s a lam₁ δ
      = ∑ u ∈ S ∪ T, Work.ZeroFreeTables.P9.nearP3summand N L χ s a lam₁ δ u := by
    rw [Work.ZeroFreeTables.P9.nearP3sum_eq_tsum]
    exact tsum_eq_sum (s := S ∪ T) (fun u hu => hsupp u (fun h => hu (Finset.mem_union_left _ h)))
  -- the `δ`-window
  set p : ℂ → Prop := fun u => ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ with hp
  have hTsplit : ∑ u ∈ T, (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re
      = ∑ u ∈ T.filter p, (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re
        + ∑ u ∈ T.filter (fun u => ¬ p u),
            (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re :=
    (Finset.sum_filter_add_sum_filter_not T p _).symm
  -- on the window, `hmin` applies through `|u.im| ≤ R + 1`
  have hwin : ∀ u : ℂ, Work.LinnikContract.zeroMult χ u ≠ 0 →
      ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ → lam₁ ≤ (1 - u.re) * L := by
    intro u hzm hw
    refine hmin u hzm ?_
    have h2 : ((1 : ℂ) + (s.im : ℂ) * Complex.I - u).im = s.im - u.im := by simp
    have h1 : |s.im - u.im| ≤ δ := by
      have h1' := Complex.abs_im_le_norm ((1 : ℂ) + (s.im : ℂ) * Complex.I - u)
      rw [h2] at h1'
      exact h1'.trans hw
    have h3 : |u.im| ≤ |s.im| + |s.im - u.im| := by
      calc |u.im| = |s.im - (s.im - u.im)| := by congr 1; ring
        _ ≤ |s.im| + |s.im - u.im| := abs_sub _ _
    linarith
  have hsummand_nonneg : ∀ u : ℂ,
      0 ≤ Work.ZeroFreeTables.P9.nearP3summand N L χ s a lam₁ δ u :=
    fun u => Work.ZeroFreeTables.P9.NearP3summandNonnegWindow χ hL (by linarith) hsre hwin u
  -- the zeros of `T` inside the window are dominated term by term by `nearP3sum`
  have hnear_pt : ∀ u ∈ T.filter p,
      (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re
        ≤ Work.ZeroFreeTables.P9.nearP3summand N L χ s a lam₁ δ u := by
    intro u hu
    rw [Finset.mem_filter] at hu
    obtain ⟨huT, hpu⟩ := hu
    rw [Work.ZeroFreeTables.P9.nearP3summand_eq_P3]
    have hind : Work.ZeroFreeTables.P9.nearInd s δ u = 1 := by
      rw [Work.ZeroFreeTables.P9.nearInd_eq_ite]
      exact if_pos (by simpa [hp] using hpu)
    rw [hind, mul_one]
    have hmult : (1 : ℝ) ≤ (Work.LinnikContract.zeroMult χ u : ℝ) := by
      have := hT u huT
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
    have hP3 : 0 ≤ (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re := by
      have hnn := hsummand_nonneg u
      rw [Work.ZeroFreeTables.P9.nearP3summand_eq_P3, hind, mul_one] at hnn
      have hpos : 0 < (Work.LinnikContract.zeroMult χ u : ℝ) := by
        have := hT u huT
        exact_mod_cast Nat.pos_of_ne_zero this
      exact (mul_nonneg_iff_of_pos_left hpos).mp hnn
    calc (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re
        = 1 * (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re := by ring
      _ ≤ (Work.LinnikContract.zeroMult χ u : ℝ)
            * (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re :=
          mul_le_mul_of_nonneg_right hmult hP3
  have hnear : ∑ u ∈ T.filter p,
        (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re
      ≤ ∑ u ∈ S ∪ T, Work.ZeroFreeTables.P9.nearP3summand N L χ s a lam₁ δ u :=
    le_trans (Finset.sum_le_sum hnear_pt)
      (Finset.sum_le_sum_of_subset_of_nonneg
        (fun u hu => Finset.mem_union_right S (Finset.mem_filter.mp hu).1)
        (fun u _ _ => hsummand_nonneg u))
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
      have hpune : ¬ (‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ) := by
        simpa [hp] using hpu
      have hfar_lt : δ < ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ := lt_of_not_ge hpune
      exact le_trans (le_abs_self _)
        (Work.ZeroFreeTables.P9.P3term_abs_le_of_far hL ha hlam₁ hδ haδ hsre hminu hfar_lt)
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

end Work.ZeroFreeTables.OffAxis
