/-
# The continued fraction expansion of a `2 × 2` integer matrix

This file iterates the one-step Euclidean recursion `nxt` and proves the estimates for the
resulting expansion `M = ±(T^{q₀} S T^{q₁} S ⋯ S T^{q_k})`:

* the recursion terminates (`kZ`);
* the product of the quotients is bounded by `3^k · uZ M` (the telescoping estimate);
* the squared Frobenius norm grows by controlled factors;
* the length of the expansion is logarithmic in the size of `M` (`2^n ≤ 2 max(|c|,1)`).
-/
import Mathlib
import Submission.Work.Rigidity.SigmaEntryBound.Defs
import Submission.Work.Rigidity.SigmaEntryBound.nxt_estimates
import Submission.Work.Rigidity.SigmaEntryBound.StepAux

namespace Work.Rigidity.SigmaEntryBound

open Matrix

variable {M : Matrix (Fin 2) (Fin 2) ℤ}

/-! ## The sequence of states -/

theorem stateZ_zero (M : Matrix (Fin 2) (Fin 2) ℤ) : stateZ M 0 = M := rfl

theorem stateZ_succ (M : Matrix (Fin 2) (Fin 2) ℤ) (n : ℕ) :
    stateZ M (n + 1) = nxt (stateZ M n) := rfl

theorem stateZ_frozen {M : Matrix (Fin 2) (Fin 2) ℤ} {n : ℕ}
    (h : (stateZ M n) 1 0 = 0) : stateZ M (n + 1) = stateZ M n := by
  rw [stateZ_succ, nxt_frozen h]

theorem stateZ_shift (M : Matrix (Fin 2) (Fin 2) ℤ) (n : ℕ) :
    stateZ (nxt M) n = stateZ M (n + 1) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [stateZ_succ (nxt M) k, ih, ← stateZ_succ M (k + 1)]

theorem detZ_stateZ (M : Matrix (Fin 2) (Fin 2) ℤ) (n : ℕ) :
    detZ (stateZ M n) = detZ M := by
  induction n with
  | zero => rfl
  | succ k ih =>
    by_cases h : (stateZ M k) 1 0 = 0
    · rw [stateZ_frozen h, ih]
    · rw [stateZ_succ, detZ_nxt h, ih]

/-! ## Termination -/

theorem muZ_stateZ_lt {M : Matrix (Fin 2) (Fin 2) ℤ} {n : ℕ}
    (h : (stateZ M n) 1 0 ≠ 0) : muZ (stateZ M (n + 1)) < muZ (stateZ M n) := by
  rw [stateZ_succ]
  exact (nxt_estimates h).2.2.2.1

theorem exists_term (M : Matrix (Fin 2) (Fin 2) ℤ) : ∃ k, (stateZ M k) 1 0 = 0 := by
  by_contra h
  push_neg at h
  have key : ∀ n, muZ (stateZ M n) + n ≤ muZ M := by
    intro n
    induction n with
    | zero => simp only [stateZ_zero, Nat.add_zero]; exact le_refl _
    | succ k ih =>
      have hlt := muZ_stateZ_lt (M := M) (n := k) (h k)
      omega
  have := key (muZ M + 1)
  omega

/-- The number of reduction steps needed to reach a terminal state. -/
noncomputable def kZ (M : Matrix (Fin 2) (Fin 2) ℤ) : ℕ := Nat.find (exists_term M)

theorem kZ_spec (M : Matrix (Fin 2) (Fin 2) ℤ) : (stateZ M (kZ M)) 1 0 = 0 :=
  Nat.find_spec (exists_term M)

theorem kZ_min (M : Matrix (Fin 2) (Fin 2) ℤ) {j : ℕ} (hj : j < kZ M) :
    (stateZ M j) 1 0 ≠ 0 :=
  Nat.find_min (exists_term M) hj

/-! ## The list of quotients -/

/-- The list of the first `n` quotients of the recursion. -/
def LZ (M : Matrix (Fin 2) (Fin 2) ℤ) (n : ℕ) : List ℤ :=
  (List.range n).map (fun j => quo (stateZ M j))

lemma LZ_zero (M : Matrix (Fin 2) (Fin 2) ℤ) : LZ M 0 = [] := rfl

lemma LZ_succ (M : Matrix (Fin 2) (Fin 2) ℤ) (n : ℕ) :
    LZ M (n + 1) = LZ M n ++ [quo (stateZ M n)] := by
  simp only [LZ, List.range_succ, List.map_append, List.map_cons, List.map_nil]

lemma LZ_ne_nil (M : Matrix (Fin 2) (Fin 2) ℤ) (n : ℕ) : LZ M (n + 1) ≠ [] := by
  intro h
  have h2 : (LZ M (n + 1)).length = 0 := by rw [h]; rfl
  simp [LZ] at h2

lemma LZ_succ_cons (M : Matrix (Fin 2) (Fin 2) ℤ) (n : ℕ) :
    LZ M (n + 1) = quo M :: LZ (nxt M) n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    calc LZ M (k + 1 + 1) = LZ M (k + 1) ++ [quo (stateZ M (k + 1))] := LZ_succ M (k+1)
      _ = (quo M :: LZ (nxt M) k) ++ [quo (stateZ M (k + 1))] := by rw [ih]
      _ = quo M :: (LZ (nxt M) k ++ [quo (stateZ M (k + 1))]) := rfl
      _ = quo M :: LZ (nxt M) (k + 1) := by rw [LZ_succ, stateZ_shift]

lemma prod1p_nil : prod1p ([] : List ℤ) = 1 := rfl

lemma prod1p_cons (a : ℤ) (l : List ℤ) : prod1p (a :: l) = (1 + a.natAbs) * prod1p l := rfl

lemma prod1p_singleton (a : ℤ) : prod1p [a] = 1 + a.natAbs := by simp [prod1p]

lemma prod1p_append (l₁ l₂ : List ℤ) : prod1p (l₁ ++ l₂) = prod1p l₁ * prod1p l₂ := by
  induction l₁ with
  | nil => simp [prod1p]
  | cons a t ih =>
    show (1 + a.natAbs) * prod1p (t ++ l₂) = (1 + a.natAbs) * prod1p t * prod1p l₂
    rw [ih]; ring

lemma prod1p_LZ_succ (M : Matrix (Fin 2) (Fin 2) ℤ) (n : ℕ) :
    prod1p (LZ M (n + 1)) =
      prod1p (LZ M n) * (1 + (quo (stateZ M n)).natAbs) := by
  rw [LZ_succ, prod1p_append, prod1p_singleton]

/-! ## The prefix estimates -/

theorem prod_bound (M : Matrix (Fin 2) (Fin 2) ℤ) (n : ℕ)
    (h : ∀ j < n, (stateZ M j) 1 0 ≠ 0) :
    prod1p (LZ M n) * uZ (stateZ M n) ≤ 3 ^ n * uZ M := by
  induction n with
  | zero => simp [LZ_zero, prod1p_nil, stateZ_zero]
  | succ k ih =>
    have hk : (stateZ M k) 1 0 ≠ 0 := h k (Nat.lt_succ_self k)
    have ih' := ih (fun j hj => h j (Nat.lt_trans hj (Nat.lt_succ_self k)))
    rw [prod1p_LZ_succ, stateZ_succ]
    calc prod1p (LZ M k) * (1 + (quo (stateZ M k)).natAbs) * uZ (nxt (stateZ M k))
        = prod1p (LZ M k) * ((1 + (quo (stateZ M k)).natAbs) * uZ (nxt (stateZ M k))) := by
          ring
      _ ≤ prod1p (LZ M k) * (3 * uZ (stateZ M k)) :=
          Nat.mul_le_mul_left _ (nxt_estimates hk).2.2.1
      _ = 3 * (prod1p (LZ M k) * uZ (stateZ M k)) := by ring
      _ ≤ 3 * (3 ^ k * uZ M) := Nat.mul_le_mul_left _ ih'
      _ = 3 ^ (k + 1) * uZ M := by ring

theorem frob2Z_bound (M : Matrix (Fin 2) (Fin 2) ℤ) (n : ℕ)
    (h : ∀ j < n, (stateZ M j) 1 0 ≠ 0) :
    frob2Z (stateZ M n) ≤ 2 ^ n * (prod1p (LZ M n)) ^ 2 * frob2Z M := by
  induction n with
  | zero => simp [LZ_zero, prod1p_nil, stateZ_zero]
  | succ k ih =>
    have hk : (stateZ M k) 1 0 ≠ 0 := h k (Nat.lt_succ_self k)
    have ih' := ih (fun j hj => h j (Nat.lt_trans hj (Nat.lt_succ_self k)))
    rw [prod1p_LZ_succ, stateZ_succ]
    calc frob2Z (nxt (stateZ M k))
        ≤ 2 * (1 + (quo (stateZ M k)).natAbs) ^ 2 * frob2Z (stateZ M k) :=
          (nxt_estimates hk).2.2.2.2
      _ ≤ 2 * (1 + (quo (stateZ M k)).natAbs) ^ 2
            * (2 ^ k * (prod1p (LZ M k)) ^ 2 * frob2Z M) :=
          Nat.mul_le_mul_left _ ih'
      _ = 2 ^ (k + 1) * (prod1p (LZ M k) * (1 + (quo (stateZ M k)).natAbs)) ^ 2 * frob2Z M := by
          ring

theorem pow_c_bound (M : Matrix (Fin 2) (Fin 2) ℤ) (n : ℕ) :
    2 ^ n * ((stateZ M n) 1 0).natAbs ≤ (M 1 0).natAbs := by
  induction n with
  | zero => simp [stateZ_zero]
  | succ k ih =>
    have step : 2 * ((stateZ M (k + 1)) 1 0).natAbs ≤ ((stateZ M k) 1 0).natAbs := by
      by_cases h : (stateZ M k) 1 0 = 0
      · rw [stateZ_frozen h]; simp [h]
      · rw [stateZ_succ]
        have h1 : ((nxt (stateZ M k)) 1 0).natAbs = (remz (stateZ M k)).natAbs := by
          rw [(nxt_entries h).2.2.1, Int.natAbs_neg]
        rw [h1]
        exact (nxt_estimates h).1
    calc 2 ^ (k + 1) * ((stateZ M (k + 1)) 1 0).natAbs
        = 2 ^ k * (2 * ((stateZ M (k + 1)) 1 0).natAbs) := by ring
      _ ≤ 2 ^ k * ((stateZ M k) 1 0).natAbs := Nat.mul_le_mul_left _ step
      _ ≤ (M 1 0).natAbs := ih

theorem len_bound (M : Matrix (Fin 2) (Fin 2) ℤ) (n : ℕ)
    (h : ∀ j < n, (stateZ M j) 1 0 ≠ 0) :
    2 ^ n ≤ 2 * max ((M 1 0).natAbs) 1 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact le_trans (by norm_num) (Nat.mul_le_mul_left 2 (le_max_right _ _))
  · have hlt : n - 1 < n := Nat.sub_one_lt_of_lt hn
    have hne : (stateZ M (n - 1)) 1 0 ≠ 0 := h (n - 1) hlt
    have h1 : 1 ≤ ((stateZ M (n - 1)) 1 0).natAbs := Int.natAbs_pos.mpr hne
    have h2 := pow_c_bound M (n - 1)
    have h3 : 2 ^ (n - 1) ≤ (M 1 0).natAbs := by
      calc 2 ^ (n - 1) = 2 ^ (n - 1) * 1 := by ring
        _ ≤ 2 ^ (n - 1) * ((stateZ M (n - 1)) 1 0).natAbs := Nat.mul_le_mul_left _ h1
        _ ≤ (M 1 0).natAbs := h2
    have hn1 : n = (n - 1) + 1 := by omega
    calc 2 ^ n = 2 * 2 ^ (n - 1) := by
          conv_lhs => rw [hn1]
          rw [pow_succ']
      _ ≤ 2 * (M 1 0).natAbs := Nat.mul_le_mul_left _ h3
      _ ≤ 2 * max ((M 1 0).natAbs) 1 := Nat.mul_le_mul_left _ (le_max_left _ _)

/-! ## The reconstruction -/

lemma recon_singleton (q : ℤ) : recon [q] = Tpow q := rfl

lemma recon_cons (q : ℤ) (l : List ℤ) (hl : l ≠ []) :
    recon (q :: l) = Tpow q * Smat * recon l := by
  cases l with
  | nil => exact absurd rfl hl
  | cons a t => rfl

theorem recon_LZ : ∀ (n : ℕ) (M : Matrix (Fin 2) (Fin 2) ℤ),
    (∀ j < n, (stateZ M j) 1 0 ≠ 0) → (stateZ M n) 1 0 = 0 → detZ M = 1 →
    recon (LZ M (n + 1)) = M ∨ recon (LZ M (n + 1)) = -M := by
  intro n
  induction n with
  | zero =>
    intro M _ hterm hdet
    have h1 : LZ M 1 = [quo M] := by rw [LZ_succ, LZ_zero, List.nil_append]; rfl
    rw [h1, recon_singleton]
    rcases terminal_step hterm hdet with h | h
    · exact Or.inl (show Tpow (quo M) = M from h.symm)
    · exact Or.inr (by rw [← neg_inj, neg_neg]; exact h.symm)
  | succ k ih =>
    intro M hprev hterm hdet
    have h0 : M 1 0 ≠ 0 := hprev 0 (Nat.succ_pos k)
    have ih' := ih (nxt M)
      (fun j hj => by rw [stateZ_shift]; exact hprev (j + 1) (by omega))
      (by rw [stateZ_shift]; exact hterm)
      (by rw [detZ_nxt h0]; exact hdet)
    rw [LZ_succ_cons M (k + 1),
      recon_cons (quo M) (LZ (nxt M) (k + 1)) (LZ_ne_nil (nxt M) k)]
    rcases ih' with h | h
    · left; rw [h, ← step_id h0]
    · right; rw [h, mul_neg, ← step_id h0]

/-! ## The terminal state -/

theorem uZ_Tpow (q : ℤ) : uZ (Tpow q) = 1 := by
  simp [uZ, Tpow]

theorem uZ_neg_Tpow (q : ℤ) : uZ (-(Tpow q)) = 1 := by
  simp [uZ, Tpow]

theorem frob2Z_Tpow (q : ℤ) : frob2Z (Tpow q) = q.natAbs ^ 2 + 2 := by
  simp [frob2Z, Tpow]; ring

theorem frob2Z_neg_Tpow (q : ℤ) : frob2Z (-(Tpow q)) = q.natAbs ^ 2 + 2 := by
  simp [frob2Z, Tpow]; ring

theorem quo_Tpow (q : ℤ) : quo (Tpow q) = q := by
  simp [quo, Tpow]

theorem quo_neg_Tpow (q : ℤ) : quo (-(Tpow q)) = q := by
  simp [quo, Tpow]

lemma self_le_sq_add (x : ℕ) : x ≤ x ^ 2 + 2 := by
  by_cases hx : x = 0
  · omega
  · have h1 : 1 ≤ x := Nat.one_le_iff_ne_zero.mpr hx
    nlinarith [h1]

theorem terminal_data {M : Matrix (Fin 2) (Fin 2) ℤ} (h : M 1 0 = 0) (hdet : detZ M = 1) :
    uZ M = 1 ∧
    frob2Z M = (quo M).natAbs ^ 2 + 2 ∧
    (quo M).natAbs ≤ frob2Z M := by
  rcases terminal_step h hdet with hh | hh
  · rw [hh, quo_Tpow, uZ_Tpow, frob2Z_Tpow]
    exact ⟨rfl, rfl, self_le_sq_add _⟩
  · rw [hh, quo_neg_Tpow, uZ_neg_Tpow, frob2Z_neg_Tpow]
    exact ⟨rfl, rfl, self_le_sq_add _⟩

end Work.Rigidity.SigmaEntryBound
