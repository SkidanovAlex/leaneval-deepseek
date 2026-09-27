import Mathlib
import Submission.Work.Mostow.LinAlgMatrixIneqAux

namespace Work.Mostow

/-- If `matPhi a = matPhi b` for distinct `a, b ∈ (0,1)`, then `a*b + a + b = 1`. -/
lemma matPhi_eq_imp_add_mul {a b : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b)
    (hb1 : b < 1) (hab : a ≠ b) (h : matPhi a = matPhi b) : a * b + a + b = 1 := by
  have h1a : 1 - a ≠ 0 := by linarith
  have h1b : 1 - b ≠ 0 := by linarith
  have ha : a ≠ 0 := ne_of_gt ha0
  have hb : b ≠ 0 := ne_of_gt hb0
  have h' := h
  unfold matPhi at h'
  field_simp at h'
  have key : (b - a) * (1 - a * b - a - b) = 0 := by nlinarith [h']
  have hzero : 1 - a * b - a - b = 0 := by
    rcases mul_eq_zero.mp key with h1 | h2
    · exact absurd (by linarith : a = b) hab
    · exact h2
  linarith

/-- A function taking at most the two values `a < b` with `a*b+a+b=1` and both values
occurring cannot sum to `1` when `n ≥ 3`. -/
lemma two_val_sum_ne_one {n : ℕ} (hn : 3 ≤ n) {a b : ℝ} (hab : a < b)
    (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) (hb1 : b < 1)
    (hrel : a * b + a + b = 1) (y : Fin n → ℝ) (hmem : ∀ k, y k = a ∨ y k = b)
    (ha_occ : ∃ p, y p = a) (hb_occ : ∃ q, y q = b) (hsum : ∑ k, y k = 1) : False := by
  classical
  set S := Finset.univ.filter (fun k : Fin n => y k = b) with hS
  have hs1 : ∑ k : Fin n, (a : ℝ) = (n : ℝ) * a := by simp
  have hs2 : ∑ k : Fin n, (if y k = b then (1 : ℝ) else 0) = (S.card : ℝ) := by
    rw [hS]; exact Finset.sum_boole _ _
  have hcount : ∑ k : Fin n, y k = (n : ℝ) * a + (b - a) * (S.card : ℝ) := by
    have hcongr : ∑ k : Fin n, y k = ∑ k : Fin n, (if y k = b then b else a) := by
      apply Finset.sum_congr rfl
      intro k _
      rcases hmem k with h | h
      · rw [h]; simp [ne_of_lt hab]
      · rw [h]; simp
    rw [hcongr]
    calc ∑ k : Fin n, (if y k = b then b else a)
        = ∑ k : Fin n, (a + (b - a) * (if y k = b then (1 : ℝ) else 0)) :=
          Finset.sum_congr rfl (fun k _ => by by_cases hkb : y k = b <;> simp [hkb])
      _ = (∑ k : Fin n, (a : ℝ))
            + ∑ k : Fin n, (b - a) * (if y k = b then (1 : ℝ) else 0) :=
          Finset.sum_add_distrib
      _ = (∑ k : Fin n, (a : ℝ))
            + (b - a) * ∑ k : Fin n, (if y k = b then (1 : ℝ) else 0) := by
          rw [Finset.mul_sum]
      _ = (n : ℝ) * a + (b - a) * (S.card : ℝ) := by rw [hs1, hs2]
  rw [hcount] at hsum
  have hM1 : 1 ≤ S.card := by
    obtain ⟨q, hq⟩ := hb_occ
    exact Finset.card_pos.mpr ⟨q, by rw [hS]; simp [hq]⟩
  have hMn : S.card ≤ n - 1 := by
    have hsub : S ⊂ (Finset.univ : Finset (Fin n)) := by
      rw [hS, Finset.filter_ssubset]
      obtain ⟨p, hp⟩ := ha_occ
      exact ⟨p, Finset.mem_univ p, by rw [hp]; exact ne_of_lt hab⟩
    have hlt := Finset.card_lt_card hsub
    simp only [Finset.card_univ, Fintype.card_fin] at hlt
    omega
  have heq : ((n : ℝ) - (S.card : ℝ) - 1) * a + ((S.card : ℝ) - 1) * b = a * b := by
    nlinarith [hsum, hrel]
  rcases (by omega : S.card ≤ n - 2 ∨ S.card = n - 1) with hcase | hcase
  · have hSle : (S.card : ℝ) ≤ (n : ℝ) - 2 := by
      have h1 : (S.card : ℝ) ≤ ((n - 2 : ℕ) : ℝ) := by exact_mod_cast hcase
      rwa [Nat.cast_sub (by omega : 2 ≤ n)] at h1
    have hbge : (1 : ℝ) ≤ (n : ℝ) - (S.card : ℝ) - 1 := by linarith
    have hbneg : b - ((n : ℝ) - (S.card : ℝ) - 1) < 0 := by linarith
    have hlhs : a * (b - ((n : ℝ) - (S.card : ℝ) - 1)) < 0 :=
      mul_neg_of_pos_of_neg ha0 hbneg
    have hrhs : 0 ≤ ((S.card : ℝ) - 1) * b := by
      have : (0 : ℝ) ≤ (S.card : ℝ) - 1 := by
        have := (show (1 : ℝ) ≤ (S.card : ℝ) by exact_mod_cast hM1); linarith
      exact mul_nonneg this (le_of_lt hb0)
    have hfac : a * (b - ((n : ℝ) - (S.card : ℝ) - 1)) = ((S.card : ℝ) - 1) * b := by
      linarith [heq]
    linarith
  · have hzero : (n : ℝ) - (S.card : ℝ) - 1 = 0 := by
      have hcast : (S.card : ℝ) = ((n - 1 : ℕ) : ℝ) := by rw [hcase]
      rw [hcast, Nat.cast_sub (by omega : 1 ≤ n)]
      ring
    have hkey : ((S.card : ℝ) - 1) * b = a * b := by nlinarith [heq, hzero]
    have hbne : b ≠ 0 := ne_of_gt hb0
    have haeq : a = (n : ℝ) - 2 := by
      have h2 : ((S.card : ℝ) - 1 - a) * b = 0 := by linarith [hkey]
      have h3 : (S.card : ℝ) - 1 - a = 0 := by
        rcases mul_eq_zero.mp h2 with h | h
        · exact h
        · exact absurd h hbne
      have h4 : (S.card : ℝ) - 1 = (n : ℝ) - 2 := by linarith
      linarith
    have ha_ge : (1 : ℝ) ≤ a := by
      have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    exact absurd ha_ge (not_le.mpr ha1)

theorem matPhi_all_eq_imp {n : ℕ} (hn : 3 ≤ n) (x : Fin n → ℝ)
    (hx0 : ∀ i, 0 < x i) (hx1 : ∀ i, x i < 1) (hsum : ∑ i, x i = 1)
    (hphi : ∀ i j, matPhi (x i) = matPhi (x j)) : ∀ i, x i = 1 / (n : ℝ) := by
  classical
  by_cases hall : ∃ i j, x i ≠ x j
  · exfalso
    obtain ⟨p, q, hpq⟩ := hall
    have hrel_aux : ∀ (r s : Fin n), x r < x s → x r * x s + x r + x s = 1 :=
      fun r s hrs =>
        matPhi_eq_imp_add_mul (hx0 r) (hx1 r) (hx0 s) (hx1 s) (ne_of_lt hrs) (hphi r s)
    have hmem_aux : ∀ (r s : Fin n), x r < x s → ∀ k, x k = x r ∨ x k = x s := by
      intro r s hrs k
      by_cases hkb : x k = x s
      · exact Or.inr hkb
      · left
        have hk : x k * x s + x k + x s = 1 :=
          matPhi_eq_imp_add_mul (hx0 k) (hx1 k) (hx0 s) (hx1 s) hkb (hphi k s)
        have hr : x r * x s + x r + x s = 1 := hrel_aux r s hrs
        have : (x k - x r) * (x s + 1) = 0 := by linarith
        rcases mul_eq_zero.mp this with h1 | h2
        · linarith
        · exfalso; linarith [hx0 s]
    rcases lt_or_gt_of_ne hpq with hlt | hgt
    · exact two_val_sum_ne_one hn hlt (hx0 p) (hx1 p) (hx0 q) (hx1 q)
        (hrel_aux p q hlt) x (hmem_aux p q hlt) ⟨p, rfl⟩ ⟨q, rfl⟩ hsum
    · exact two_val_sum_ne_one hn hgt (hx0 q) (hx1 q) (hx0 p) (hx1 p)
        (hrel_aux q p hgt) x (hmem_aux q p hgt) ⟨q, rfl⟩ ⟨p, rfl⟩ hsum
  · push Not at hall
    intro i
    have hsum_const : ∑ k : Fin n, x k = (n : ℝ) * x i := by
      calc ∑ k : Fin n, x k = ∑ _k : Fin n, x i := Finset.sum_congr rfl (fun k _ => hall k i)
        _ = (n : ℝ) * x i := by simp
    have hxi : (n : ℝ) * x i = 1 := by rw [← hsum_const]; exact hsum
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    rw [eq_div_iff hn0]
    linarith

end Work.Mostow
