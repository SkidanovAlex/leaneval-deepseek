import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.Defs
import Submission.Work.ZeroFreeTables.OffAxis.WideDefs
import Submission.Work.ZeroFreeTables.HBProps
import Submission.Work.ZeroFreeTables.Tables
import Submission.Work.ZeroFreeTables.OffAxis.hbLemma9_2_engine_H
import Submission.Work.ZeroFreeTables.HBTable9_proof

open DirichletCharacter Complex
open scoped Classical BigOperators Real
noncomputable section

namespace Work.ZeroFreeTables.OffAxis

open Work.ZeroFreeTables Work.LinnikContract
open Work.ZeroFreeTables.P9F

/-! ## Helpers: the height-`L` numbering and the height-`H` numbering argument -/

/-- `IsRectMin L χ₁ ρ₁` is exactly the height-`W = 10L` numbering `IsMinWideAt L (10L)`. -/
theorem isMinWideAt_of_isRectMin {q : ℕ} [NeZero q] {L : ℝ} {χ₁ : DirichletCharacter ℂ q}
    {ρ₁ : ℂ} (hR : IsRectMin L χ₁ ρ₁) : IsMinWideAt L (10 * L) χ₁ ρ₁ :=
  ⟨hR.1.1, hR.1.2.1, hR.1.2.2, fun χ u hχ hzm him => hR.2 χ u ⟨hχ, hzm, him⟩⟩

/-- `λ₁ ≥ 0` for the minimal zero of the height-`W` numbering. -/
theorem lamOf_nonneg_of_minWideAt {q : ℕ} [NeZero q] {H W : ℝ}
    {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} (hmin : IsMinWideAt H W χ₁ ρ₁) :
    0 ≤ lamOf q ρ₁ := by
  have hstrip := zeroMult_re_mem_strip (χ := χ₁) (ρ := ρ₁) hmin.1 hmin.2.1
  rw [lamOf]
  have hlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by
    have := NeZero.ne q
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this)
  nlinarith [hstrip.2]

/-- **The Heath-Brown numbering argument of Lemma 9.2 at height `H`.**  From the Lemma 9.2
inequality (`hcore`, available for every admissible pair) and the numerical contradiction at
`(a, c)` (`hcontra`) we get `Lam3BoundH H χ₁ c`, for a pair `(χ₁, ρ₁)` of the height-`W`
numbering with `λ₁ ≤ a` and `χ₁² ≠ 1`. -/
theorem lam3_of_row_H {q : ℕ} [NeZero q] {H W : ℝ} {χ₁ : DirichletCharacter ℂ q}
    {ρ₁ : ℂ} {a c θ lam k slack : ℝ}
    (hmin : IsMinWideAt H W χ₁ ρ₁) (hcplx : χ₁ ^ 2 ≠ 1) (hlam1 : lamOf q ρ₁ ≤ a)
    (hcore : ∀ (χj : DirichletCharacter ℂ q) (ρj : ℂ), IsZAt H χj ρj →
      χj ≠ χ₁ → χj ≠ χ₁⁻¹ → χ₁ ^ 2 ≠ χj → χ₁ ^ 2 ≠ χj⁻¹ → lamOf q ρj ≤ c →
      0 ≤ (k ^ 2 + 1/2) * (La θ lam (lamOf q ρ₁) - La θ lam (lamOf q ρ₁ - lamOf q ρj))
          - 2 * k * La θ lam 0 + tf71f θ lam 0 * slack)
    (hcontra : ∀ {la1 laj : ℝ}, 0 ≤ la1 → la1 ≤ a → laj ≤ c →
      0 ≤ (k ^ 2 + 1/2) * (La θ lam la1 - La θ lam (la1 - laj)) - 2 * k * La θ lam 0
        + tf71f θ lam 0 * slack → False) :
    Lam3BoundH H χ₁ c := by
  have hlam0 : 0 ≤ lamOf q ρ₁ := lamOf_nonneg_of_minWideAt hmin
  by_contra hcon
  rw [Lam3BoundH] at hcon
  push_neg at hcon
  obtain ⟨χb, ρb, hZb, hb1, hb2, -, -, hblt⟩ := hcon χ₁
  have hkey : ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZAt H χ ρ → χ ≠ χ₁ → χ ≠ χ₁⁻¹ →
      χ ≠ χb → χ ≠ χb⁻¹ → c ≤ lamOf q ρ := by
    intro χ ρ hZ h1 h2 h3 h4
    by_contra hlt
    rw [not_le] at hlt
    by_cases hcase : χ₁ ^ 2 = χb ∨ χ₁ ^ 2 = χb⁻¹
    · have hne : χ₁ ^ 2 ≠ χ ∧ χ₁ ^ 2 ≠ χ⁻¹ := by
        rcases hcase with hc | hc
        · constructor
          · intro h; exact h3 (h.symm.trans hc)
          · intro h; exact h4 (by rw [← inv_inv χ, ← h, ← hc])
        · constructor
          · intro h; exact h4 (by rw [← h, ← hc])
          · intro h; exact h3 (by rw [← inv_inv χ, ← h, hc, inv_inv])
      exact hcontra hlam0 hlam1 (le_of_lt hlt)
        (hcore χ ρ hZ h1 h2 hne.1 hne.2 (le_of_lt hlt))
    · push_neg at hcase
      exact hcontra hlam0 hlam1 (le_of_lt hblt)
        (hcore χb ρb hZb hb1 hb2 hcase.1 hcase.2 (le_of_lt hblt))
  obtain ⟨χ, ρ, hZ, h1, h2, h3, h4, hlt⟩ := hcon χb
  exact absurd (hkey χ ρ hZ h1 h2 h3 h4) (not_le.mpr hlt)

/-! ## The generic row at rectangle height `L` -/

/-- **One row of HB Table 9 at rectangle height `L`.**  Given the test-function parameters
`θ, lam, k`, the tabulated point `(a, c)`, the slack and a numerical contradiction `hcontra`
valid for all `0 ≤ la1 ≤ a`, `laj ≤ c`, the Lemma 9.2 inequality drives `Lam3BoundH L χ₁ c`
for `λ₁ ≤ a`. -/
theorem rectRow (L : ℝ) (hL : 1 ≤ L) (Q : ℕ) (θ lam k a c slack : ℝ)
    (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam) (hk : 0 ≤ k)
    (ha2 : a ≤ 2) (hc2 : c ≤ 2)
    (hsl : (k ^ 2 + 4 * k + 3 / 2) * (1 / 6 + 1 / 1000000 + 1 / 1000000000000) ≤ slack)
    (hcontra : ∀ {la1 laj : ℝ}, 0 ≤ la1 → la1 ≤ a → laj ≤ c →
      0 ≤ (k ^ 2 + 1 / 2) * (La θ lam la1 - La θ lam (la1 - laj)) - 2 * k * La θ lam 0
        + tf71f θ lam 0 * slack → False)
    (hsup : L52Supply) :
    ∃ Q' : ℕ, Q ≤ Q' ∧ ∀ q : ℕ, Q' ≤ q → ∀ [NeZero q]
      (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsRectMin L χ₁ ρ₁ → χ₁ ^ 2 ≠ 1 → lamOf q ρ₁ ≤ a → Lam3BoundH L χ₁ c := by
  obtain ⟨δ, hδ0, hδ1, qA, hA⟩ := hsup
  have hH0 : 0 ≤ L := by linarith
  have hHW : 3 * L + δ ≤ 10 * L := by linarith
  obtain ⟨qE, hqE⟩ := hbLemma9_2_engine_H (tf71T θ lam hθ0 hθ1 hlam) k
    (1 / 6 + 1 / 1000000) (1 / 1000000000000) δ L (10 * L) hk (by norm_num) hδ0 hδ1 hH0 hHW
  refine ⟨max (max Q qA) (max qE (max Qsq (Nat.ceil (Real.exp L) + 1))), ?_, ?_⟩
  · exact le_trans (le_max_left _ _) (le_max_left _ _)
  intro q hq _inst χ₁ ρ₁ hR hcplx hlam1
  have hqA : qA ≤ q := by
    have h1 : qA ≤ max Q qA := le_max_right _ _
    have h2 : max Q qA ≤ max (max Q qA) (max qE (max Qsq (Nat.ceil (Real.exp L) + 1))) :=
      le_max_left _ _
    omega
  have hqE' : qE ≤ q := by
    have h1 : qE ≤ max qE (max Qsq (Nat.ceil (Real.exp L) + 1)) := le_max_left _ _
    have h2 : max qE (max Qsq (Nat.ceil (Real.exp L) + 1))
        ≤ max (max Q qA) (max qE (max Qsq (Nat.ceil (Real.exp L) + 1))) := le_max_right _ _
    omega
  have hqL : Nat.ceil (Real.exp L) + 1 ≤ q := by
    have h1 : Nat.ceil (Real.exp L) + 1 ≤ max Qsq (Nat.ceil (Real.exp L) + 1) := le_max_right _ _
    have h2 : max Qsq (Nat.ceil (Real.exp L) + 1)
        ≤ max qE (max Qsq (Nat.ceil (Real.exp L) + 1)) := le_max_right _ _
    have h3 : max qE (max Qsq (Nat.ceil (Real.exp L) + 1))
        ≤ max (max Q qA) (max qE (max Qsq (Nat.ceil (Real.exp L) + 1))) := le_max_right _ _
    omega
  have hqSq : Qsq ≤ q := by
    have h3 : Qsq ≤ max Qsq (Nat.ceil (Real.exp L) + 1) := le_max_left _ _
    have h4 : max Qsq (Nat.ceil (Real.exp L) + 1)
        ≤ max qE (max Qsq (Nat.ceil (Real.exp L) + 1)) := le_max_right _ _
    have h5 : max qE (max Qsq (Nat.ceil (Real.exp L) + 1))
        ≤ max (max Q qA) (max qE (max Qsq (Nat.ceil (Real.exp L) + 1))) := le_max_right _ _
    omega
  have hsq : 2 ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) := sqrt_loglog_ge_two hqSq
  have hHL : L ≤ Real.log (q : ℝ) := by
    have hexp : Real.exp L ≤ (q : ℝ) := by
      have h1 : Real.exp L ≤ ((Nat.ceil (Real.exp L) : ℕ) : ℝ) := Nat.le_ceil _
      have h2 : ((Nat.ceil (Real.exp L) : ℕ) : ℝ) + 1 ≤ (q : ℝ) := by exact_mod_cast hqL
      linarith
    have := Real.log_le_log (Real.exp_pos L) hexp
    rwa [Real.log_exp] at this
  have hmin : IsMinWideAt L (10 * L) χ₁ ρ₁ := isMinWideAt_of_isRectMin hR
  refine lam3_of_row_H hmin hcplx hlam1 ?_ hcontra
  intro χj ρj hZj h1 h2 h3 h4 hlaj
  have hE := hqE q hqE' χ₁ χj ρ₁ ρj
    (fun χ _ hχ => hA q hqA χ hχ (1 / 1000000000000) (by norm_num))
    hHL hmin hZj.2.1 hZj.1 hZj.2.2 h1 h2 hcplx h3 h4
    (by linarith) (by linarith) hsq
  rw [tf71T_F_eq_La θ lam hθ0 hθ1 hlam (-(lamOf q ρ₁)),
      tf71T_F_eq_La θ lam hθ0 hθ1 hlam (lamOf q ρj - lamOf q ρ₁),
      tf71T_F_eq_La θ lam hθ0 hθ1 hlam 0] at hE
  simp only [neg_neg, neg_sub, neg_zero, tf71T] at hE
  have hf0 : 0 ≤ tf71f θ lam 0 := tf71f_nonneg θ lam hθ0 hθ1 hlam 0
  linarith [hE, mul_nonneg hf0 (sub_nonneg.mpr hsl)]

/-! ## The twenty rows -/

/-- Row `λ₁ ≤ 34/100 ⟹ λ_j ≥ 1283/1000` of HB Table 9 at rectangle height `L`. -/
theorem rectRow_034_1283 (L : ℝ) (hL : 1 ≤ L) (Q : ℕ) (hsup : L52Supply) :
    ∃ Q' : ℕ, Q ≤ Q' ∧ ∀ q : ℕ, Q' ≤ q → ∀ [NeZero q]
      (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsRectMin L χ₁ ρ₁ → χ₁ ^ 2 ≠ 1 → lamOf q ρ₁ ≤ ((34/100:ℚ):ℝ) →
      Lam3BoundH L χ₁ ((1283/1000:ℚ):ℝ) := by
  obtain ⟨hlo, hhi⟩ := arctan25_bounds
  refine rectRow L hL Q (Real.arctan (25:ℝ)) (21/500) (81/100) ((34/100:ℚ):ℝ) ((1283/1000:ℚ):ℝ)
    (4496782761/5000000000) (Real.arctan_pos.mpr (by norm_num)) (Real.arctan_lt_pi_div_two _) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ hsup
  intro la1 laj h0 h1 h2 hineq
  refine rowcontra_034_1283 hlo hhi (by rw [Real.tan_arctan]; norm_num) h0 ?_ ?_ hineq
  · have h' : ((34/100:ℚ):ℝ) = (17/50:ℝ) := by norm_num
    linarith
  · have h' : ((1283/1000:ℚ):ℝ) = (1283/1000:ℝ) := by norm_num
    linarith

/-- Row `λ₁ ≤ 36/100 ⟹ λ_j ≥ 1230/1000` of HB Table 9 at rectangle height `L`. -/
theorem rectRow_036_123 (L : ℝ) (hL : 1 ≤ L) (Q : ℕ) (hsup : L52Supply) :
    ∃ Q' : ℕ, Q ≤ Q' ∧ ∀ q : ℕ, Q' ≤ q → ∀ [NeZero q]
      (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsRectMin L χ₁ ρ₁ → χ₁ ^ 2 ≠ 1 → lamOf q ρ₁ ≤ ((36/100:ℚ):ℝ) →
      Lam3BoundH L χ₁ ((1230/1000:ℚ):ℝ) := by
  obtain ⟨hlo, hhi⟩ := arctan25_bounds
  refine rectRow L hL Q (Real.arctan (25:ℝ)) (21/500) (407/500) ((36/100:ℚ):ℝ) ((1230/1000:ℚ):ℝ)
    (338664717947/375000000000) (Real.arctan_pos.mpr (by norm_num)) (Real.arctan_lt_pi_div_two _) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ hsup
  intro la1 laj h0 h1 h2 hineq
  refine rowcontra_036_123 hlo hhi (by rw [Real.tan_arctan]; norm_num) h0 ?_ ?_ hineq
  · have h' : ((36/100:ℚ):ℝ) = (9/25:ℝ) := by norm_num
    linarith
  · have h' : ((1230/1000:ℚ):ℝ) = (123/100:ℝ) := by norm_num
    linarith

/-- Row `λ₁ ≤ 38/100 ⟹ λ_j ≥ 1181/1000` of HB Table 9 at rectangle height `L`. -/
theorem rectRow_038_1181 (L : ℝ) (hL : 1 ≤ L) (Q : ℕ) (hsup : L52Supply) :
    ∃ Q' : ℕ, Q ≤ Q' ∧ ∀ q : ℕ, Q' ≤ q → ∀ [NeZero q]
      (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsRectMin L χ₁ ρ₁ → χ₁ ^ 2 ≠ 1 → lamOf q ρ₁ ≤ ((38/100:ℚ):ℝ) →
      Lam3BoundH L χ₁ ((1181/1000:ℚ):ℝ) := by
  obtain ⟨hlo, hhi⟩ := arctan24_bounds
  refine rectRow L hL Q (Real.arctan (24:ℝ)) (9/200) (817/1000) ((38/100:ℚ):ℝ) ((1181/1000:ℚ):ℝ)
    (1358882154467/1500000000000) (Real.arctan_pos.mpr (by norm_num)) (Real.arctan_lt_pi_div_two _) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ hsup
  intro la1 laj h0 h1 h2 hineq
  refine rowcontra_038_1181 hlo hhi (by rw [Real.tan_arctan]; norm_num) h0 ?_ ?_ hineq
  · have h' : ((38/100:ℚ):ℝ) = (19/50:ℝ) := by norm_num
    linarith
  · have h' : ((1181/1000:ℚ):ℝ) = (1181/1000:ℝ) := by norm_num
    linarith

/-- Row `λ₁ ≤ 40/100 ⟹ λ_j ≥ 1135/1000` of HB Table 9 at rectangle height `L`. -/
theorem rectRow_04_1135 (L : ℝ) (hL : 1 ≤ L) (Q : ℕ) (hsup : L52Supply) :
    ∃ Q' : ℕ, Q ≤ Q' ∧ ∀ q : ℕ, Q' ≤ q → ∀ [NeZero q]
      (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsRectMin L χ₁ ρ₁ → χ₁ ^ 2 ≠ 1 → lamOf q ρ₁ ≤ ((40/100:ℚ):ℝ) →
      Lam3BoundH L χ₁ ((1135/1000:ℚ):ℝ) := by
  obtain ⟨hlo, hhi⟩ := arctan25_bounds
  refine rectRow L hL Q (Real.arctan (25:ℝ)) (11/250) (41/50) ((40/100:ℚ):ℝ) ((1135/1000:ℚ):ℝ)
    (3407774843/3750000000) (Real.arctan_pos.mpr (by norm_num)) (Real.arctan_lt_pi_div_two _) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ hsup
  intro la1 laj h0 h1 h2 hineq
  refine rowcontra_04_1135 hlo hhi (by rw [Real.tan_arctan]; norm_num) h0 ?_ ?_ hineq
  · have h' : ((40/100:ℚ):ℝ) = (2/5:ℝ) := by norm_num
    linarith
  · have h' : ((1135/1000:ℚ):ℝ) = (227/200:ℝ) := by norm_num
    linarith

/-- Row `λ₁ ≤ 42/100 ⟹ λ_j ≥ 1094/1000` of HB Table 9 at rectangle height `L`. -/
theorem rectRow_042_1094 (L : ℝ) (hL : 1 ≤ L) (Q : ℕ) (hsup : L52Supply) :
    ∃ Q' : ℕ, Q ≤ Q' ∧ ∀ q : ℕ, Q' ≤ q → ∀ [NeZero q]
      (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsRectMin L χ₁ ρ₁ → χ₁ ^ 2 ≠ 1 → lamOf q ρ₁ ≤ ((42/100:ℚ):ℝ) →
      Lam3BoundH L χ₁ ((1094/1000:ℚ):ℝ) := by
  obtain ⟨hlo, hhi⟩ := arctan24_bounds
  refine rectRow L hL Q (Real.arctan (24:ℝ)) (23/500) (411/500) ((42/100:ℚ):ℝ) ((1094/1000:ℚ):ℝ)
    (113827579921/125000000000) (Real.arctan_pos.mpr (by norm_num)) (Real.arctan_lt_pi_div_two _) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ hsup
  intro la1 laj h0 h1 h2 hineq
  refine rowcontra_042_1094 hlo hhi (by rw [Real.tan_arctan]; norm_num) h0 ?_ ?_ hineq
  · have h' : ((42/100:ℚ):ℝ) = (21/50:ℝ) := by norm_num
    linarith
  · have h' : ((1094/1000:ℚ):ℝ) = (547/500:ℝ) := by norm_num
    linarith

/-- Row `λ₁ ≤ 44/100 ⟹ λ_j ≥ 1055/1000` of HB Table 9 at rectangle height `L`. -/
theorem rectRow_044_1055 (L : ℝ) (hL : 1 ≤ L) (Q : ℕ) (hsup : L52Supply) :
    ∃ Q' : ℕ, Q ≤ Q' ∧ ∀ q : ℕ, Q' ≤ q → ∀ [NeZero q]
      (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsRectMin L χ₁ ρ₁ → χ₁ ^ 2 ≠ 1 → lamOf q ρ₁ ≤ ((44/100:ℚ):ℝ) →
      Lam3BoundH L χ₁ ((1055/1000:ℚ):ℝ) := by
  obtain ⟨hlo, hhi⟩ := arctan25_bounds
  refine rectRow L hL Q (Real.arctan (25:ℝ)) (23/500) (33/40) ((44/100:ℚ):ℝ) ((1055/1000:ℚ):ℝ)
    (730755329/800000000) (Real.arctan_pos.mpr (by norm_num)) (Real.arctan_lt_pi_div_two _) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ hsup
  intro la1 laj h0 h1 h2 hineq
  refine rowcontra_044_1055 hlo hhi (by rw [Real.tan_arctan]; norm_num) h0 ?_ ?_ hineq
  · have h' : ((44/100:ℚ):ℝ) = (11/25:ℝ) := by norm_num
    linarith
  · have h' : ((1055/1000:ℚ):ℝ) = (211/200:ℝ) := by norm_num
    linarith

/-- Row `λ₁ ≤ 46/100 ⟹ λ_j ≥ 1018/1000` of HB Table 9 at rectangle height `L`. -/
theorem rectRow_046_1018 (L : ℝ) (hL : 1 ≤ L) (Q : ℕ) (hsup : L52Supply) :
    ∃ Q' : ℕ, Q ≤ Q' ∧ ∀ q : ℕ, Q' ≤ q → ∀ [NeZero q]
      (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsRectMin L χ₁ ρ₁ → χ₁ ^ 2 ≠ 1 → lamOf q ρ₁ ≤ ((46/100:ℚ):ℝ) →
      Lam3BoundH L χ₁ ((1018/1000:ℚ):ℝ) := by
  obtain ⟨hlo, hhi⟩ := arctan25_bounds
  refine rectRow L hL Q (Real.arctan (25:ℝ)) (23/500) (207/250) ((46/100:ℚ):ℝ) ((1018/1000:ℚ):ℝ)
    (28633458849/31250000000) (Real.arctan_pos.mpr (by norm_num)) (Real.arctan_lt_pi_div_two _) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ hsup
  intro la1 laj h0 h1 h2 hineq
  refine rowcontra_046_1018 hlo hhi (by rw [Real.tan_arctan]; norm_num) h0 ?_ ?_ hineq
  · have h' : ((46/100:ℚ):ℝ) = (23/50:ℝ) := by norm_num
    linarith
  · have h' : ((1018/1000:ℚ):ℝ) = (509/500:ℝ) := by norm_num
    linarith

/-- Row `λ₁ ≤ 48/100 ⟹ λ_j ≥ 984/1000` of HB Table 9 at rectangle height `L`. -/
theorem rectRow_048_0984 (L : ℝ) (hL : 1 ≤ L) (Q : ℕ) (hsup : L52Supply) :
    ∃ Q' : ℕ, Q ≤ Q' ∧ ∀ q : ℕ, Q' ≤ q → ∀ [NeZero q]
      (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsRectMin L χ₁ ρ₁ → χ₁ ^ 2 ≠ 1 → lamOf q ρ₁ ≤ ((48/100:ℚ):ℝ) →
      Lam3BoundH L χ₁ ((984/1000:ℚ):ℝ) := by
  obtain ⟨hlo, hhi⟩ := arctan25_bounds
  refine rectRow L hL Q (Real.arctan (25:ℝ)) (47/1000) (104/125) ((48/100:ℚ):ℝ) ((984/1000:ℚ):ℝ)
    (21563532323/23437500000) (Real.arctan_pos.mpr (by norm_num)) (Real.arctan_lt_pi_div_two _) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ hsup
  intro la1 laj h0 h1 h2 hineq
  refine rowcontra_048_0984 hlo hhi (by rw [Real.tan_arctan]; norm_num) h0 ?_ ?_ hineq
  · have h' : ((48/100:ℚ):ℝ) = (12/25:ℝ) := by norm_num
    linarith
  · have h' : ((984/1000:ℚ):ℝ) = (123/125:ℝ) := by norm_num
    linarith

/-- Row `λ₁ ≤ 50/100 ⟹ λ_j ≥ 952/1000` of HB Table 9 at rectangle height `L`. -/
theorem rectRow_05_0952 (L : ℝ) (hL : 1 ≤ L) (Q : ℕ) (hsup : L52Supply) :
    ∃ Q' : ℕ, Q ≤ Q' ∧ ∀ q : ℕ, Q' ≤ q → ∀ [NeZero q]
      (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsRectMin L χ₁ ρ₁ → χ₁ ^ 2 ≠ 1 → lamOf q ρ₁ ≤ ((50/100:ℚ):ℝ) →
      Lam3BoundH L χ₁ ((952/1000:ℚ):ℝ) := by
  obtain ⟨hlo, hhi⟩ := arctan25_bounds
  refine rectRow L hL Q (Real.arctan (25:ℝ)) (6/125) (417/500) ((50/100:ℚ):ℝ) ((952/1000:ℚ):ℝ)
    (115241590889/125000000000) (Real.arctan_pos.mpr (by norm_num)) (Real.arctan_lt_pi_div_two _) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ hsup
  intro la1 laj h0 h1 h2 hineq
  refine rowcontra_05_0952 hlo hhi (by rw [Real.tan_arctan]; norm_num) h0 ?_ ?_ hineq
  · have h' : ((50/100:ℚ):ℝ) = (1/2:ℝ) := by norm_num
    linarith
  · have h' : ((952/1000:ℚ):ℝ) = (119/125:ℝ) := by norm_num
    linarith

/-- Row `λ₁ ≤ 52/100 ⟹ λ_j ≥ 922/1000` of HB Table 9 at rectangle height `L`. -/
theorem rectRow_052_0922 (L : ℝ) (hL : 1 ≤ L) (Q : ℕ) (hsup : L52Supply) :
    ∃ Q' : ℕ, Q ≤ Q' ∧ ∀ q : ℕ, Q' ≤ q → ∀ [NeZero q]
      (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsRectMin L χ₁ ρ₁ → χ₁ ^ 2 ≠ 1 → lamOf q ρ₁ ≤ ((52/100:ℚ):ℝ) →
      Lam3BoundH L χ₁ ((922/1000:ℚ):ℝ) := by
  obtain ⟨hlo, hhi⟩ := arctan25_bounds
  refine rectRow L hL Q (Real.arctan (25:ℝ)) (6/125) (209/250) ((52/100:ℚ):ℝ) ((922/1000:ℚ):ℝ)
    (28869460681/31250000000) (Real.arctan_pos.mpr (by norm_num)) (Real.arctan_lt_pi_div_two _) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ hsup
  intro la1 laj h0 h1 h2 hineq
  refine rowcontra_052_0922 hlo hhi (by rw [Real.tan_arctan]; norm_num) h0 ?_ ?_ hineq
  · have h' : ((52/100:ℚ):ℝ) = (13/25:ℝ) := by norm_num
    linarith
  · have h' : ((922/1000:ℚ):ℝ) = (461/500:ℝ) := by norm_num
    linarith

/-- Row `λ₁ ≤ 54/100 ⟹ λ_j ≥ 893/1000` of HB Table 9 at rectangle height `L`. -/
theorem rectRow_054_0893 (L : ℝ) (hL : 1 ≤ L) (Q : ℕ) (hsup : L52Supply) :
    ∃ Q' : ℕ, Q ≤ Q' ∧ ∀ q : ℕ, Q' ≤ q → ∀ [NeZero q]
      (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsRectMin L χ₁ ρ₁ → χ₁ ^ 2 ≠ 1 → lamOf q ρ₁ ≤ ((54/100:ℚ):ℝ) →
      Lam3BoundH L χ₁ ((893/1000:ℚ):ℝ) := by
  obtain ⟨hlo, hhi⟩ := arctan25_bounds
  refine rectRow L hL Q (Real.arctan (25:ℝ)) (6/125) (419/500) ((54/100:ℚ):ℝ) ((893/1000:ℚ):ℝ)
    (347142783683/375000000000) (Real.arctan_pos.mpr (by norm_num)) (Real.arctan_lt_pi_div_two _) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ hsup
  intro la1 laj h0 h1 h2 hineq
  refine rowcontra_054_0893 hlo hhi (by rw [Real.tan_arctan]; norm_num) h0 ?_ ?_ hineq
  · have h' : ((54/100:ℚ):ℝ) = (27/50:ℝ) := by norm_num
    linarith
  · have h' : ((893/1000:ℚ):ℝ) = (893/1000:ℝ) := by norm_num
    linarith

/-- Row `λ₁ ≤ 56/100 ⟹ λ_j ≥ 866/1000` of HB Table 9 at rectangle height `L`. -/
theorem rectRow_056_0866 (L : ℝ) (hL : 1 ≤ L) (Q : ℕ) (hsup : L52Supply) :
    ∃ Q' : ℕ, Q ≤ Q' ∧ ∀ q : ℕ, Q' ≤ q → ∀ [NeZero q]
      (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsRectMin L χ₁ ρ₁ → χ₁ ^ 2 ≠ 1 → lamOf q ρ₁ ≤ ((56/100:ℚ):ℝ) →
      Lam3BoundH L χ₁ ((866/1000:ℚ):ℝ) := by
  obtain ⟨hlo, hhi⟩ := arctan25_bounds
  refine rectRow L hL Q (Real.arctan (25:ℝ)) (49/1000) (21/25) ((56/100:ℚ):ℝ) ((866/1000:ℚ):ℝ)
    (72469279/78125000) (Real.arctan_pos.mpr (by norm_num)) (Real.arctan_lt_pi_div_two _) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ hsup
  intro la1 laj h0 h1 h2 hineq
  refine rowcontra_056_0866 hlo hhi (by rw [Real.tan_arctan]; norm_num) h0 ?_ ?_ hineq
  · have h' : ((56/100:ℚ):ℝ) = (14/25:ℝ) := by norm_num
    linarith
  · have h' : ((866/1000:ℚ):ℝ) = (433/500:ℝ) := by norm_num
    linarith

/-- Row `λ₁ ≤ 58/100 ⟹ λ_j ≥ 840/1000` of HB Table 9 at rectangle height `L`. -/
theorem rectRow_058_084 (L : ℝ) (hL : 1 ≤ L) (Q : ℕ) (hsup : L52Supply) :
    ∃ Q' : ℕ, Q ≤ Q' ∧ ∀ q : ℕ, Q' ≤ q → ∀ [NeZero q]
      (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsRectMin L χ₁ ρ₁ → χ₁ ^ 2 ≠ 1 → lamOf q ρ₁ ≤ ((58/100:ℚ):ℝ) →
      Lam3BoundH L χ₁ ((840/1000:ℚ):ℝ) := by
  obtain ⟨hlo, hhi⟩ := arctan25_bounds
  refine rectRow L hL Q (Real.arctan (25:ℝ)) (1/20) (421/500) ((58/100:ℚ):ℝ) ((840/1000:ℚ):ℝ)
    (116187598241/125000000000) (Real.arctan_pos.mpr (by norm_num)) (Real.arctan_lt_pi_div_two _) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ hsup
  intro la1 laj h0 h1 h2 hineq
  refine rowcontra_058_084 hlo hhi (by rw [Real.tan_arctan]; norm_num) h0 ?_ ?_ hineq
  · have h' : ((58/100:ℚ):ℝ) = (29/50:ℝ) := by norm_num
    linarith
  · have h' : ((840/1000:ℚ):ℝ) = (21/25:ℝ) := by norm_num
    linarith

/-- Row `λ₁ ≤ 60/100 ⟹ λ_j ≥ 816/1000` of HB Table 9 at rectangle height `L`. -/
theorem rectRow_06_0816 (L : ℝ) (hL : 1 ≤ L) (Q : ℕ) (hsup : L52Supply) :
    ∃ Q' : ℕ, Q ≤ Q' ∧ ∀ q : ℕ, Q' ≤ q → ∀ [NeZero q]
      (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsRectMin L χ₁ ρ₁ → χ₁ ^ 2 ≠ 1 → lamOf q ρ₁ ≤ ((60/100:ℚ):ℝ) →
      Lam3BoundH L χ₁ ((816/1000:ℚ):ℝ) := by
  obtain ⟨hlo, hhi⟩ := arctan15_bounds
  refine rectRow L hL Q (Real.arctan (15:ℝ)) (41/500) (211/250) ((60/100:ℚ):ℝ) ((816/1000:ℚ):ℝ)
    (87318387563/93750000000) (Real.arctan_pos.mpr (by norm_num)) (Real.arctan_lt_pi_div_two _) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ hsup
  intro la1 laj h0 h1 h2 hineq
  refine rowcontra_06_0816 hlo hhi (by rw [Real.tan_arctan]; norm_num) h0 ?_ ?_ hineq
  · have h' : ((60/100:ℚ):ℝ) = (3/5:ℝ) := by norm_num
    linarith
  · have h' : ((816/1000:ℚ):ℝ) = (102/125:ℝ) := by norm_num
    linarith

/-- Row `λ₁ ≤ 62/100 ⟹ λ_j ≥ 792/1000` of HB Table 9 at rectangle height `L`. -/
theorem rectRow_062_0792 (L : ℝ) (hL : 1 ≤ L) (Q : ℕ) (hsup : L52Supply) :
    ∃ Q' : ℕ, Q ≤ Q' ∧ ∀ q : ℕ, Q' ≤ q → ∀ [NeZero q]
      (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsRectMin L χ₁ ρ₁ → χ₁ ^ 2 ≠ 1 → lamOf q ρ₁ ≤ ((62/100:ℚ):ℝ) →
      Lam3BoundH L χ₁ ((792/1000:ℚ):ℝ) := by
  obtain ⟨hlo, hhi⟩ := arctan25_bounds
  refine rectRow L hL Q (Real.arctan (25:ℝ)) (1/20) (847/1000) ((62/100:ℚ):ℝ) ((792/1000:ℚ):ℝ)
    (1401362484227/1500000000000) (Real.arctan_pos.mpr (by norm_num)) (Real.arctan_lt_pi_div_two _) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ hsup
  intro la1 laj h0 h1 h2 hineq
  refine rowcontra_062_0792 hlo hhi (by rw [Real.tan_arctan]; norm_num) h0 ?_ ?_ hineq
  · have h' : ((62/100:ℚ):ℝ) = (31/50:ℝ) := by norm_num
    linarith
  · have h' : ((792/1000:ℚ):ℝ) = (99/125:ℝ) := by norm_num
    linarith

/-- Row `λ₁ ≤ 64/100 ⟹ λ_j ≥ 770/1000` of HB Table 9 at rectangle height `L`. -/
theorem rectRow_064_077 (L : ℝ) (hL : 1 ≤ L) (Q : ℕ) (hsup : L52Supply) :
    ∃ Q' : ℕ, Q ≤ Q' ∧ ∀ q : ℕ, Q' ≤ q → ∀ [NeZero q]
      (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsRectMin L χ₁ ρ₁ → χ₁ ^ 2 ≠ 1 → lamOf q ρ₁ ≤ ((64/100:ℚ):ℝ) →
      Lam3BoundH L χ₁ ((770/1000:ℚ):ℝ) := by
  obtain ⟨hlo, hhi⟩ := arctan25_bounds
  refine rectRow L hL Q (Real.arctan (25:ℝ)) (51/1000) (849/1000) ((64/100:ℚ):ℝ) ((770/1000:ℚ):ℝ)
    (468070168801/500000000000) (Real.arctan_pos.mpr (by norm_num)) (Real.arctan_lt_pi_div_two _) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ hsup
  intro la1 laj h0 h1 h2 hineq
  refine rowcontra_064_077 hlo hhi (by rw [Real.tan_arctan]; norm_num) h0 ?_ ?_ hineq
  · have h' : ((64/100:ℚ):ℝ) = (16/25:ℝ) := by norm_num
    linarith
  · have h' : ((770/1000:ℚ):ℝ) = (77/100:ℝ) := by norm_num
    linarith

/-- Row `λ₁ ≤ 66/100 ⟹ λ_j ≥ 748/1000` of HB Table 9 at rectangle height `L`. -/
theorem rectRow_066_0748 (L : ℝ) (hL : 1 ≤ L) (Q : ℕ) (hsup : L52Supply) :
    ∃ Q' : ℕ, Q ≤ Q' ∧ ∀ q : ℕ, Q' ≤ q → ∀ [NeZero q]
      (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsRectMin L χ₁ ρ₁ → χ₁ ^ 2 ≠ 1 → lamOf q ρ₁ ≤ ((66/100:ℚ):ℝ) →
      Lam3BoundH L χ₁ ((748/1000:ℚ):ℝ) := by
  obtain ⟨hlo, hhi⟩ := arctan25_bounds
  refine rectRow L hL Q (Real.arctan (25:ℝ)) (13/250) (213/250) ((66/100:ℚ):ℝ) ((748/1000:ℚ):ℝ)
    (29343464369/31250000000) (Real.arctan_pos.mpr (by norm_num)) (Real.arctan_lt_pi_div_two _) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ hsup
  intro la1 laj h0 h1 h2 hineq
  refine rowcontra_066_0748 hlo hhi (by rw [Real.tan_arctan]; norm_num) h0 ?_ ?_ hineq
  · have h' : ((66/100:ℚ):ℝ) = (33/50:ℝ) := by norm_num
    linarith
  · have h' : ((748/1000:ℚ):ℝ) = (187/250:ℝ) := by norm_num
    linarith

/-- Row `λ₁ ≤ 68/100 ⟹ λ_j ≥ 728/1000` of HB Table 9 at rectangle height `L`. -/
theorem rectRow_068_0728 (L : ℝ) (hL : 1 ≤ L) (Q : ℕ) (hsup : L52Supply) :
    ∃ Q' : ℕ, Q ≤ Q' ∧ ∀ q : ℕ, Q' ≤ q → ∀ [NeZero q]
      (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsRectMin L χ₁ ρ₁ → χ₁ ^ 2 ≠ 1 → lamOf q ρ₁ ≤ ((68/100:ℚ):ℝ) →
      Lam3BoundH L χ₁ ((728/1000:ℚ):ℝ) := by
  obtain ⟨hlo, hhi⟩ := arctan25_bounds
  refine rectRow L hL Q (Real.arctan (25:ℝ)) (13/250) (427/500) ((68/100:ℚ):ℝ) ((728/1000:ℚ):ℝ)
    (117611609329/125000000000) (Real.arctan_pos.mpr (by norm_num)) (Real.arctan_lt_pi_div_two _) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ hsup
  intro la1 laj h0 h1 h2 hineq
  refine rowcontra_068_0728 hlo hhi (by rw [Real.tan_arctan]; norm_num) h0 ?_ ?_ hineq
  · have h' : ((68/100:ℚ):ℝ) = (17/25:ℝ) := by norm_num
    linarith
  · have h' : ((728/1000:ℚ):ℝ) = (91/125:ℝ) := by norm_num
    linarith

/-- Row `λ₁ ≤ 70/100 ⟹ λ_j ≥ 708/1000` of HB Table 9 at rectangle height `L`. -/
theorem rectRow_07_0708 (L : ℝ) (hL : 1 ≤ L) (Q : ℕ) (hsup : L52Supply) :
    ∃ Q' : ℕ, Q ≤ Q' ∧ ∀ q : ℕ, Q' ≤ q → ∀ [NeZero q]
      (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsRectMin L χ₁ ρ₁ → χ₁ ^ 2 ≠ 1 → lamOf q ρ₁ ≤ ((70/100:ℚ):ℝ) →
      Lam3BoundH L χ₁ ((708/1000:ℚ):ℝ) := by
  obtain ⟨hlo, hhi⟩ := arctan25_bounds
  refine rectRow L hL Q (Real.arctan (25:ℝ)) (13/250) (107/125) ((70/100:ℚ):ℝ) ((708/1000:ℚ):ℝ)
    (2762098309/2929687500) (Real.arctan_pos.mpr (by norm_num)) (Real.arctan_lt_pi_div_two _) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ hsup
  intro la1 laj h0 h1 h2 hineq
  refine rowcontra_07_0708 hlo hhi (by rw [Real.tan_arctan]; norm_num) h0 ?_ ?_ hineq
  · have h' : ((70/100:ℚ):ℝ) = (7/10:ℝ) := by norm_num
    linarith
  · have h' : ((708/1000:ℚ):ℝ) = (177/250:ℝ) := by norm_num
    linarith

/-- Row `λ₁ ≤ 704/1000 ⟹ λ_j ≥ 704/1000` of HB Table 9 at rectangle height `L`. -/
theorem rectRow_0704_0704 (L : ℝ) (hL : 1 ≤ L) (Q : ℕ) (hsup : L52Supply) :
    ∃ Q' : ℕ, Q ≤ Q' ∧ ∀ q : ℕ, Q' ≤ q → ∀ [NeZero q]
      (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsRectMin L χ₁ ρ₁ → χ₁ ^ 2 ≠ 1 → lamOf q ρ₁ ≤ ((704/1000:ℚ):ℝ) →
      Lam3BoundH L χ₁ ((704/1000:ℚ):ℝ) := by
  obtain ⟨hlo, hhi⟩ := arctan25_bounds
  refine rectRow L hL Q (Real.arctan (25:ℝ)) (13/250) (107/125) ((704/1000:ℚ):ℝ) ((704/1000:ℚ):ℝ)
    (2762098309/2929687500) (Real.arctan_pos.mpr (by norm_num)) (Real.arctan_lt_pi_div_two _) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ hsup
  intro la1 laj h0 h1 h2 hineq
  refine rowcontra_0704_0704 hlo hhi (by rw [Real.tan_arctan]; norm_num) h0 ?_ ?_ hineq
  · have h' : ((704/1000:ℚ):ℝ) = (88/125:ℝ) := by norm_num
    linarith
  · have h' : ((704/1000:ℚ):ℝ) = (88/125:ℝ) := by norm_num
    linarith

/-- **`RectT9H`**: HB Table 9 (Lemma 9.2) at rectangle height `L`. -/
theorem RectT9H : ∀ L : ℝ, 1 ≤ L → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
    Work.ZeroFreeTables.IsRectMin L χ₁ ρ₁ → 1 < |ρ₁.im| →
      (348:ℝ)/1000 ≤ Work.LinnikContract.lamOf q ρ₁ → χ₁ ^ 2 ≠ 1 →
      ∀ p ∈ Work.ZeroFreeTables.tableR Work.ZeroFreeTables.hbTable9,
        Work.LinnikContract.lamOf q ρ₁ ≤ p.1 →
        Work.ZeroFreeTables.Lam3BoundH L χ₁ p.2 := by
  intro L hL
  have hsup : L52Supply := L52Supply_of_burgess Work.LinnikAreas.LBound13_holds
  obtain ⟨Q0, hQ0, hrow0⟩ := rectRow_034_1283 L hL 0 hsup
  obtain ⟨Q1, hQ1, hrow1⟩ := rectRow_036_123 L hL Q0 hsup
  obtain ⟨Q2, hQ2, hrow2⟩ := rectRow_038_1181 L hL Q1 hsup
  obtain ⟨Q3, hQ3, hrow3⟩ := rectRow_04_1135 L hL Q2 hsup
  obtain ⟨Q4, hQ4, hrow4⟩ := rectRow_042_1094 L hL Q3 hsup
  obtain ⟨Q5, hQ5, hrow5⟩ := rectRow_044_1055 L hL Q4 hsup
  obtain ⟨Q6, hQ6, hrow6⟩ := rectRow_046_1018 L hL Q5 hsup
  obtain ⟨Q7, hQ7, hrow7⟩ := rectRow_048_0984 L hL Q6 hsup
  obtain ⟨Q8, hQ8, hrow8⟩ := rectRow_05_0952 L hL Q7 hsup
  obtain ⟨Q9, hQ9, hrow9⟩ := rectRow_052_0922 L hL Q8 hsup
  obtain ⟨Q10, hQ10, hrow10⟩ := rectRow_054_0893 L hL Q9 hsup
  obtain ⟨Q11, hQ11, hrow11⟩ := rectRow_056_0866 L hL Q10 hsup
  obtain ⟨Q12, hQ12, hrow12⟩ := rectRow_058_084 L hL Q11 hsup
  obtain ⟨Q13, hQ13, hrow13⟩ := rectRow_06_0816 L hL Q12 hsup
  obtain ⟨Q14, hQ14, hrow14⟩ := rectRow_062_0792 L hL Q13 hsup
  obtain ⟨Q15, hQ15, hrow15⟩ := rectRow_064_077 L hL Q14 hsup
  obtain ⟨Q16, hQ16, hrow16⟩ := rectRow_066_0748 L hL Q15 hsup
  obtain ⟨Q17, hQ17, hrow17⟩ := rectRow_068_0728 L hL Q16 hsup
  obtain ⟨Q18, hQ18, hrow18⟩ := rectRow_07_0708 L hL Q17 hsup
  obtain ⟨Q19, hQ19, hrow19⟩ := rectRow_0704_0704 L hL Q18 hsup
  refine ⟨Q19, ?_⟩
  intro q hq _inst χ₁ ρ₁ hR _him _h348 hcplx p hp hlep
  have hQ0s : Q0 ≤ q := by omega
  have hQ1s : Q1 ≤ q := by omega
  have hQ2s : Q2 ≤ q := by omega
  have hQ3s : Q3 ≤ q := by omega
  have hQ4s : Q4 ≤ q := by omega
  have hQ5s : Q5 ≤ q := by omega
  have hQ6s : Q6 ≤ q := by omega
  have hQ7s : Q7 ≤ q := by omega
  have hQ8s : Q8 ≤ q := by omega
  have hQ9s : Q9 ≤ q := by omega
  have hQ10s : Q10 ≤ q := by omega
  have hQ11s : Q11 ≤ q := by omega
  have hQ12s : Q12 ≤ q := by omega
  have hQ13s : Q13 ≤ q := by omega
  have hQ14s : Q14 ≤ q := by omega
  have hQ15s : Q15 ≤ q := by omega
  have hQ16s : Q16 ≤ q := by omega
  have hQ17s : Q17 ≤ q := by omega
  have hQ18s : Q18 ≤ q := by omega
  have hQ19s : Q19 ≤ q := by omega
  simp only [tableR, hbTable9, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hp
  rcases hp with hp0 | hp1 | hp2 | hp3 | hp4 | hp5 | hp6 | hp7 | hp8 | hp9 | hp10 | hp11 | hp12 | hp13 | hp14 | hp15 | hp16 | hp17 | hp18 | hp19
  · subst hp0; exact hrow0 q hQ0s χ₁ ρ₁ hR hcplx hlep
  · subst hp1; exact hrow1 q hQ1s χ₁ ρ₁ hR hcplx hlep
  · subst hp2; exact hrow2 q hQ2s χ₁ ρ₁ hR hcplx hlep
  · subst hp3; exact hrow3 q hQ3s χ₁ ρ₁ hR hcplx hlep
  · subst hp4; exact hrow4 q hQ4s χ₁ ρ₁ hR hcplx hlep
  · subst hp5; exact hrow5 q hQ5s χ₁ ρ₁ hR hcplx hlep
  · subst hp6; exact hrow6 q hQ6s χ₁ ρ₁ hR hcplx hlep
  · subst hp7; exact hrow7 q hQ7s χ₁ ρ₁ hR hcplx hlep
  · subst hp8; exact hrow8 q hQ8s χ₁ ρ₁ hR hcplx hlep
  · subst hp9; exact hrow9 q hQ9s χ₁ ρ₁ hR hcplx hlep
  · subst hp10; exact hrow10 q hQ10s χ₁ ρ₁ hR hcplx hlep
  · subst hp11; exact hrow11 q hQ11s χ₁ ρ₁ hR hcplx hlep
  · subst hp12; exact hrow12 q hQ12s χ₁ ρ₁ hR hcplx hlep
  · subst hp13; exact hrow13 q hQ13s χ₁ ρ₁ hR hcplx hlep
  · subst hp14; exact hrow14 q hQ14s χ₁ ρ₁ hR hcplx hlep
  · subst hp15; exact hrow15 q hQ15s χ₁ ρ₁ hR hcplx hlep
  · subst hp16; exact hrow16 q hQ16s χ₁ ρ₁ hR hcplx hlep
  · subst hp17; exact hrow17 q hQ17s χ₁ ρ₁ hR hcplx hlep
  · subst hp18; exact hrow18 q hQ18s χ₁ ρ₁ hR hcplx hlep
  · subst hp19; exact hrow19 q hQ19s χ₁ ρ₁ hR hcplx hlep

end Work.ZeroFreeTables.OffAxis
