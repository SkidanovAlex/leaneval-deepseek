import Mathlib
import Submission.Work.ZeroFreeTables.Table4.Engine8A
import Submission.Work.ZeroFreeTables.P9.Defs

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables.Table4

open Work.ZeroFreeTables

/-- **The `P₃` near sum dominates any prescribed finite set of zeros, up to one far-cost per
zero.**  This is `P9.nearP3sum_ge_kept` without the hypothesis `|Im u| ≤ 10` on the elements of
`T`: zeros outside the `δ`-window of `1 + i·Im s` are bounded by the far bound
`P3term_abs_le_of_far` (`8α/(δL)` each), which costs only the side condition `2(a+λ₁) ≤ δL`,
while zeros inside the window automatically satisfy `|u.im| < 10` (because `|s.im| ≤ 3` and
`δ < 1`) and are dominated term by term by the non-negative summands of `nearP3sum`. -/
theorem nearP3sum_ge_kept' {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) {L a lam₁ δ : ℝ} (hL : 0 < L) (ha : 0 < a) (hlam₁ : 0 ≤ lam₁)
    (hδ : 0 < δ) (hδ1 : δ < 1) (haδ : 2 * a ≤ δ * L) (hαδ : 2 * (a + lam₁) ≤ δ * L)
    {s : ℂ} (hsre : s.re = 1 + a / L) (hsim : |s.im| ≤ 3)
    (hmin : ∀ u : ℂ, Work.LinnikContract.zeroMult χ u ≠ 0 → |u.im| ≤ 10 →
      lam₁ ≤ (1 - u.re) * L)
    (T : Finset ℂ) (hT : ∀ u ∈ T, Work.LinnikContract.zeroMult χ u ≠ 0) :
    ∑ u ∈ T, (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re
      ≤ Work.ZeroFreeTables.P9.nearP3sum N L χ s a lam₁ δ
        + (T.card : ℝ) * (8 * (a + lam₁) / (δ * L)) := by
  classical
  have hδ1' : δ ≤ 1 := le_of_lt hδ1
  have hsumm := nearP3summand_summable χ hχ hprim (L := L) (a := a) (lam₁ := lam₁) hδ hδ1'
    (s := s)
  have hnn : ∀ u : ℂ, 0 ≤ Work.ZeroFreeTables.P9.nearP3summand N L χ s a lam₁ δ u :=
    fun u => Work.ZeroFreeTables.P9.nearP3summand_nonneg χ hL ha hlam₁ hδ1 hsre hsim hmin u
  -- zeros inside the window
  have hnear_pt : ∀ u ∈ T.filter (fun u => ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ),
      (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re
        ≤ Work.ZeroFreeTables.P9.nearP3summand N L χ s a lam₁ δ u := by
    intro u hu
    obtain ⟨huT, hpu⟩ := Finset.mem_filter.mp hu
    have him : |u.im| ≤ 10 := by
      have h2 : ((1 : ℂ) + (s.im : ℂ) * Complex.I - u).im = s.im - u.im := by simp
      have h1 : |s.im - u.im| ≤ δ := by
        have h1' := Complex.abs_im_le_norm ((1 : ℂ) + (s.im : ℂ) * Complex.I - u)
        rw [h2] at h1'
        exact h1'.trans hpu
      have h3 : |u.im| ≤ |s.im| + |s.im - u.im| := by
        calc |u.im| = |s.im - (s.im - u.im)| := by congr 1; ring
          _ ≤ |s.im| + |s.im - u.im| := abs_sub _ _
      linarith [hsim]
    have hlu : lam₁ ≤ (1 - u.re) * L := hmin u (hT u huT) him
    have hP3nn : 0 ≤ (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re :=
      Work.ZeroFreeTables.P9.P3term_nonneg_of_min hL ha hlam₁ hsre hlu
    have hmult : (1 : ℝ) ≤ (Work.LinnikContract.zeroMult χ u : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (hT u huT)
    rw [Work.ZeroFreeTables.P9.nearP3summand_eq_P3]
    have hind : Work.ZeroFreeTables.P9.nearInd s δ u = 1 := by
      rw [Work.ZeroFreeTables.P9.nearInd_eq_ite]
      exact if_pos hpu
    rw [hind, mul_one]
    calc (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re
        = 1 * (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re := by ring
      _ ≤ (Work.LinnikContract.zeroMult χ u : ℝ)
            * (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re :=
          mul_le_mul_of_nonneg_right hmult hP3nn
  have hnear : ∑ u ∈ T.filter (fun u => ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ),
        (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re
      ≤ Work.ZeroFreeTables.P9.nearP3sum N L χ s a lam₁ δ := by
    rw [Work.ZeroFreeTables.P9.nearP3sum_eq_tsum]
    exact le_trans (Finset.sum_le_sum hnear_pt)
      (Summable.sum_le_tsum _ (fun u _ => hnn u) hsumm)
  -- zeros outside the window
  have hconst : (0 : ℝ) ≤ 8 * (a + lam₁) / (δ * L) := by positivity
  have hfar_pt : ∀ u ∈ T.filter (fun u => ¬ (‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ)),
      (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re
        ≤ 8 * (a + lam₁) / (δ * L) := by
    intro u hu
    obtain ⟨huT, hpu⟩ := Finset.mem_filter.mp hu
    have hfar_lt : δ < ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ := lt_of_not_ge hpu
    exact (abs_le.mp (P3term_abs_le_of_far hL ha hlam₁ hδ haδ hαδ hsre hfar_lt)).2
  have hfar : ∑ u ∈ T.filter (fun u => ¬ (‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ)),
        (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re
      ≤ (T.card : ℝ) * (8 * (a + lam₁) / (δ * L)) := by
    calc ∑ u ∈ T.filter (fun u => ¬ (‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ)),
          (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re
        ≤ ∑ _u ∈ T.filter (fun u => ¬ (‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ)),
            8 * (a + lam₁) / (δ * L) := Finset.sum_le_sum hfar_pt
      _ = (((T.filter (fun u => ¬ (‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ))).card : ℝ)
            * (8 * (a + lam₁) / (δ * L))) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (T.card : ℝ) * (8 * (a + lam₁) / (δ * L)) := by
          apply mul_le_mul_of_nonneg_right _ hconst
          exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
  have hsplit : (∑ u ∈ T, (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re)
      = (∑ u ∈ T.filter (fun u => ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ),
          (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re)
        + (∑ u ∈ T.filter (fun u => ¬ (‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ)),
          (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re) :=
    (Finset.sum_filter_add_sum_filter_not T
      (fun u : ℂ => ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ)
      (fun u : ℂ => (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re)).symm
  linarith [hnear, hfar, hsplit]

theorem point_bound83 {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) {L a lam₁ δ c Cj Ct : ℝ}
    (ha : 0 < a) (hlam₁ : 0 ≤ lam₁) (hδ : 0 < δ) (hδ1 : δ < 1) (hL : 1 < L)
    (haδL : 2 * a ≤ δ * L) (hαδL : 2 * (a + lam₁) ≤ δ * L)
    {s : ℂ} (hsre : s.re = 1 + a / L) (hsim : |s.im| ≤ 3)
    (hlog : (-logDeriv (DirichletCharacter.LFunction χ) s).re
        + Work.ZeroFreeTables.P9.nearInvSum N χ s δ ≤ c * L)
    (par : ℕ) (hpar0 : χ.Even → par = 0) (hpar1 : χ.Odd → par = 1)
    (hS2 : |∑' n : ℕ, (((1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 2)).re| ≤ Ct)
    (hS3 : |∑' n : ℕ, (((1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 3)).re| ≤ Ct)
    (hJ : Work.ZeroFreeTables.P9.invSqSum N χ s ≤ Cj)
    (hmin : ∀ u : ℂ, Work.LinnikContract.zeroMult χ u ≠ 0 → |u.im| ≤ 10 → lam₁ ≤ (1 - u.re) * L)
    (T : Finset ℂ) (hT : ∀ u ∈ T, Work.LinnikContract.zeroMult χ u ≠ 0) :
    Work.ZeroFreeTables.SigmaP3L N L χ s a lam₁
      ≤ -(∑ u ∈ T, (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re)
        + (a + lam₁) * c
        + ((a + lam₁) ^ 2 / L ^ 2) * ((1 + 4 / δ ^ 2) * Cj + Ct)
        + (2 / 3) * ((a + lam₁) ^ 3 / L ^ 3) * ((2 / δ) * (1 + 4 / δ ^ 2) * Cj + Ct)
        + (T.card : ℝ) * (8 * (a + lam₁) / (δ * L)) := by
  have hLpos : 0 < L := by linarith
  have h1 := engine8 (N := N) χ hχ hprim (a := a) (lam₁ := lam₁) (δ := δ) (c := c) (L := L)
    (Ct := Ct) ha hlam₁ hδ hδ1 hL haδL (s := s) hsre (by linarith [hsim]) hlog par hpar0 hpar1
    hS2 hS3
  have h2 := nearP3sum_ge_kept' χ hχ hprim hLpos ha hlam₁ hδ hδ1 haδL hαδL hsre hsim hmin T hT
  have hw : (0 : ℝ) ≤ 1 + 4 / δ ^ 2 := by positivity
  have hinner1 : (1 + 4 / δ ^ 2) * Work.ZeroFreeTables.P9.invSqSum N χ s + Ct
      ≤ (1 + 4 / δ ^ 2) * Cj + Ct := by
    linarith [mul_le_mul_of_nonneg_left hJ hw]
  have hc1 : ((a + lam₁) ^ 2 / L ^ 2)
        * ((1 + 4 / δ ^ 2) * Work.ZeroFreeTables.P9.invSqSum N χ s + Ct)
      ≤ ((a + lam₁) ^ 2 / L ^ 2) * ((1 + 4 / δ ^ 2) * Cj + Ct) :=
    mul_le_mul_of_nonneg_left hinner1 (div_nonneg (sq_nonneg (a + lam₁)) (sq_nonneg L))
  have hw2 : (0 : ℝ) ≤ (2 / δ) * (1 + 4 / δ ^ 2) := by positivity
  have hinner2 : (2 / δ) * (1 + 4 / δ ^ 2) * Work.ZeroFreeTables.P9.invSqSum N χ s + Ct
      ≤ (2 / δ) * (1 + 4 / δ ^ 2) * Cj + Ct := by
    linarith [mul_le_mul_of_nonneg_left hJ hw2]
  have hcoe2 : (0 : ℝ) ≤ (2 / 3) * ((a + lam₁) ^ 3 / L ^ 3) := by positivity
  have hc2 : (2 / 3) * ((a + lam₁) ^ 3 / L ^ 3)
        * ((2 / δ) * (1 + 4 / δ ^ 2) * Work.ZeroFreeTables.P9.invSqSum N χ s + Ct)
      ≤ (2 / 3) * ((a + lam₁) ^ 3 / L ^ 3) * ((2 / δ) * (1 + 4 / δ ^ 2) * Cj + Ct) :=
    mul_le_mul_of_nonneg_left hinner2 hcoe2
  linarith [h1, h2, hc1, hc2]

end Work.ZeroFreeTables.Table4
