import Mathlib
import Submission.Work.HP.MDEstimates.hiparts.HiCellDefs

/-!
# The cell fibre bound for the `𝔡₃`-cells of the case-`I` sum at `(4,4)`

Given a finite set `F` of items whose `𝔡₃`-value `dd p` and `λ₁`-value `ll p` satisfy
`A^{1/20} ≤ dd p` and `1 ≤ ll p`, together with a counting hypothesis saying that for every pair of
cutoffs `Δ, M` the number of items with `dd p ≤ Δ` and `ll p ≤ M` is at most `Kl * hiLZ B Δ M`,
the items lying in a fixed dyadic cell `(hiIdx A (dd p), hiJdx (ll p)) = (i, j)` number at most
`Kl * hiLZ B (2 * hiDelta A i) (2 * hiM j)`.

Indeed, `hiIdx A (dd p) = i` forces `dd p < 2 * hiDelta A i` and `hiJdx (ll p) = j` forces
`ll p < 2 * hiM j` (`hiIdx_lt`, `hiJdx_lt`), i.e. the cell fibre is contained in the set cut out by
the doubled cutoffs, to which the counting hypothesis applies.
-/

namespace Work.HP.MDEstimates.hiparts

/-- The `(k+1)`-st power of `2`, written with a real exponent, is twice the `k`-th power. -/
private lemma two_pow_succ_cast (k : ℕ) : (2 : ℝ) ^ ((k : ℝ) + 1) = 2 * (2 : ℝ) ^ k := by
  rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one, Real.rpow_natCast]
  ring

/-- An item whose `𝔡₃`-cell index is `i` has `𝔡₃`-value below the doubled `i`-th cutoff,
provided its `𝔡₃`-value is at least the threshold `A^{1/20}`. -/
private lemma hiIdx_lt {A d : ℝ} (hA : 0 < A) (hd : A ^ ((1 : ℝ) / 20) ≤ d) {i : ℕ}
    (h : hiIdx A d = i) : d < 2 * hiDelta A i := by
  have hc : 0 < A ^ ((1 : ℝ) / 20) := Real.rpow_pos_of_pos hA _
  have hx : 1 ≤ d / A ^ ((1 : ℝ) / 20) := by
    rw [le_div_iff₀ hc]; simpa using hd
  have hxpos : 0 < d / A ^ ((1 : ℝ) / 20) := lt_of_lt_of_le zero_lt_one hx
  have hy : 0 ≤ Real.logb 2 (d / A ^ ((1 : ℝ) / 20)) := Real.logb_nonneg (by norm_num) hx
  have hlt : Real.logb 2 (d / A ^ ((1 : ℝ) / 20)) < (i : ℝ) + 1 :=
    ((Nat.floor_eq_iff hy).mp h).2
  have hlt2 : d / A ^ ((1 : ℝ) / 20) < (2 : ℝ) ^ ((i : ℝ) + 1) :=
    (Real.logb_lt_iff_lt_rpow (by norm_num) hxpos).mp hlt
  rw [two_pow_succ_cast] at hlt2
  have h3 : d < (2 * (2 : ℝ) ^ i) * A ^ ((1 : ℝ) / 20) := (div_lt_iff₀ hc).mp hlt2
  unfold hiDelta
  calc d < (2 * (2 : ℝ) ^ i) * A ^ ((1 : ℝ) / 20) := h3
    _ = 2 * (A ^ ((1 : ℝ) / 20) * (2 : ℝ) ^ i) := by ring

/-- An item whose `λ₁`-cell index is `j` has `λ₁`-value below the doubled `j`-th cutoff,
provided its `λ₁`-value is at least `1`. -/
private lemma hiJdx_lt {l : ℝ} (hl : 1 ≤ l) {j : ℕ} (h : hiJdx l = j) :
    l < 2 * hiM j := by
  have hpos : 0 < l := lt_of_lt_of_le zero_lt_one hl
  have hy : 0 ≤ Real.logb 2 l := Real.logb_nonneg (by norm_num) hl
  have hlt : Real.logb 2 l < (j : ℝ) + 1 := ((Nat.floor_eq_iff hy).mp h).2
  have hlt2 : l < (2 : ℝ) ^ ((j : ℝ) + 1) :=
    (Real.logb_lt_iff_lt_rpow (by norm_num) hpos).mp hlt
  rw [two_pow_succ_cast] at hlt2
  unfold hiM
  exact hlt2

/-- The dyadic `𝔡₃`-cutoffs are at least one when `1 ≤ A`. -/
private lemma hiDelta_ge_one (A : ℝ) (hA : 1 ≤ A) (i : ℕ) : 1 ≤ hiDelta A i := by
  unfold hiDelta
  have h1 : (1 : ℝ) ≤ A ^ ((1 : ℝ) / 20) := Real.one_le_rpow hA (by norm_num)
  have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ i := one_le_pow₀ (by norm_num)
  nlinarith [h1, h2]

/-- The dyadic `λ₁`-cutoffs are at least one. -/
private lemma hiM_ge_one (j : ℕ) : 1 ≤ hiM j := by
  unfold hiM
  exact one_le_pow₀ (by norm_num)

theorem hi_fiber_card {ι : Type*} (F : Finset ι) (dd ll : ι → ℝ) (A B Kl : ℝ)
    (hA : 0 < A) (hA1 : 1 ≤ A) (hKl : 0 ≤ Kl)
    (h1 : ∀ p ∈ F, A ^ ((1 : ℝ) / 20) ≤ dd p) (h2 : ∀ p ∈ F, 1 ≤ ll p)
    (hcount : ∀ Δ M : ℝ, 1 ≤ Δ → 1 ≤ M →
      ((F.filter (fun p => dd p ≤ Δ ∧ ll p ≤ M)).card : ℝ) ≤ Kl * hiLZ B Δ M)
    (i j : ℕ) :
    ((F.filter (fun p => hiIdx A (dd p) = i ∧ hiJdx (ll p) = j)).card : ℝ)
      ≤ Kl * hiLZ B (2 * hiDelta A i) (2 * hiM j) := by
  have hsub : F.filter (fun p => hiIdx A (dd p) = i ∧ hiJdx (ll p) = j)
      ⊆ F.filter (fun p => dd p ≤ 2 * hiDelta A i ∧ ll p ≤ 2 * hiM j) := by
    intro p hp
    simp only [Finset.mem_filter] at hp ⊢
    obtain ⟨hpF, hpi, hpj⟩ := hp
    exact ⟨hpF, le_of_lt (hiIdx_lt hA (h1 p hpF) hpi), le_of_lt (hiJdx_lt (h2 p hpF) hpj)⟩
  have hcard := Finset.card_le_card hsub
  have hΔ : (1 : ℝ) ≤ 2 * hiDelta A i := by
    have := hiDelta_ge_one A hA1 i; linarith
  have hM : (1 : ℝ) ≤ 2 * hiM j := by
    have := hiM_ge_one j; linarith
  calc ((F.filter (fun p => hiIdx A (dd p) = i ∧ hiJdx (ll p) = j)).card : ℝ)
      ≤ ((F.filter (fun p => dd p ≤ 2 * hiDelta A i ∧ ll p ≤ 2 * hiM j)).card : ℝ) := by
        exact_mod_cast hcard
    _ ≤ Kl * hiLZ B (2 * hiDelta A i) (2 * hiM j) := hcount _ _ hΔ hM

end Work.HP.MDEstimates.hiparts
