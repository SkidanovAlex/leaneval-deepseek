import Mathlib
import Submission.Work.Higman.c4_field_core

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.Higman

/-!
# `c4_lam_ne_mu`

Let `F` be a finite field of characteristic `2` with `|F| = 2 ^ n`, `n ≥ 2`, and let
`lam` be an element of order `2 ^ n - 1` (a generator of `Fˣ`).  If `β : F → F → F` is
additive in each variable, alternating (`β a a = 0`) and satisfies the equivariance
`β (lam * a) (lam * b) = mu * β a b`, and `β` is not identically zero, then `lam ≠ mu`.

## Proof idea

Suppose `lam = mu`.  Since `β` is biadditive, the Frobenius expansion
(`Work.Higman.bilinear_frob`) writes
`β x y = ∑_{k,l<n} d k l * x ^ (2^k) * y ^ (2^l)`
with `d k l = d l k` and `d k k = 0`, and the equivariance forces, for every `k, l < n`,
`d k l * (lam ^ (2^k) * lam ^ (2^l) - mu) = 0`
(`Work.Higman.bilinear_frob_general_constraint`).  A non-zero coefficient exists because
`β ≠ 0`; for such a coefficient `(k,l)` the relation reads `lam ^ (2^k + 2^l) = lam`, hence
`2 ^ k + 2 ^ l ≡ 1 [MOD 2 ^ n - 1]`.  As `2 ≤ 2 ^ k + 2 ^ l ≤ 2 ^ n`, this forces
`2 ^ k + 2 ^ l = 2 ^ n` and therefore `k = l = n - 1`.  So every non-zero coefficient sits
on the diagonal at `(n-1, n-1)` — but the diagonal coefficients all vanish.  Contradiction.
-/

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- Auxiliary: in a field of characteristic two, the identity `β (x + y) (x + y) = 0`
(together with additivity of `β` in each variable) implies that `β` is symmetric. -/
theorem beta_symm_of_alt {β : F → F → F}
    (h1 : ∀ a b d : F, β (a + b) d = β a d + β b d)
    (h2 : ∀ a b d : F, β a (b + d) = β a b + β a d)
    (halt : ∀ a : F, β a a = 0) :
    ∀ x y : F, β x y = β y x := by
  have htwo : (2 : F) = 0 := by
    have h := (CharP.cast_eq_zero_iff F 2 2).mpr (dvd_refl 2)
    simpa using h
  have hadd2 : ∀ x : F, x + x = 0 := fun x => by rw [← two_mul, htwo, zero_mul]
  intro x y
  have h := halt (x + y)
  rw [h1 x y (x + y)] at h
  rw [h2 x x y, h2 y x y, halt x, halt y] at h
  simp only [zero_add, add_zero] at h
  have hu : β x y + β x y = 0 := hadd2 _
  calc β x y = β x y + (β x y + β y x) := by rw [h, add_zero]
    _ = (β x y + β x y) + β y x := by abel
    _ = 0 + β y x := by rw [hu]
    _ = β y x := zero_add _

/-- Auxiliary arithmetic: if `k < n`, `l < n` and `2 ^ k + 2 ^ l = 2 ^ n` then
`k = n - 1` and `l = n - 1`. -/
theorem eq_pred_of_two_pow_add {n k l : ℕ} (hsum : 2 ^ k + 2 ^ l = 2 ^ n) :
    k = n - 1 ∧ l = n - 1 := by
  have hkl : k = l := by
    rcases lt_trichotomy k l with hlt | heq | hlt
    · exact (two_pow_add_ne_two_pow hlt hsum.symm).elim
    · exact heq
    · exact (two_pow_add_ne_two_pow hlt (by rw [Nat.add_comm]; exact hsum.symm)).elim
  subst hkl
  have h1 : 2 ^ (k + 1) = 2 ^ n := by rw [pow_succ']; omega
  have hnk : k + 1 = n := by
    rcases lt_trichotomy (k + 1) n with hlt' | heq' | hgt'
    · exact absurd h1 (ne_of_lt (Nat.pow_lt_pow_right (by norm_num : 1 < 2) hlt'))
    · exact heq'
    · exact absurd h1.symm (ne_of_lt (Nat.pow_lt_pow_right (by norm_num : 1 < 2) hgt'))
  omega

theorem c4_lam_ne_mu {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
    {n : ℕ} (hn : 2 ≤ n) (hcard : Fintype.card F = 2 ^ n) (lam mu : F)
    (hlamord : orderOf lam = 2 ^ n - 1) (hmuord : orderOf mu = 2 ^ n - 1)
    (beta : F → F → F)
    (hbeta1 : ∀ a b d : F, beta (a + b) d = beta a d + beta b d)
    (hbeta2 : ∀ a b d : F, beta a (b + d) = beta a b + beta a d)
    (hbetaalt : ∀ a : F, beta a a = 0)
    (hbetaeq : ∀ a b : F, beta (lam * a) (lam * b) = mu * beta a b)
    (hbetane : ∃ a b : F, beta a b ≠ 0) :
    lam ≠ mu := by
  classical
  intro hmu
  -- `lam` is a unit
  have hNpos : 0 < 2 ^ n - 1 := by
    have h4 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  have hlam0 : lam ≠ 0 := by
    intro h0
    have h1 : lam ^ (2 ^ n - 1) = 1 := by
      rw [← hlamord]; exact pow_orderOf_eq_one lam
    rw [h0, zero_pow hNpos.ne'] at h1
    exact zero_ne_one h1
  -- `beta` is symmetric
  have hsym : ∀ x y : F, beta x y = beta y x :=
    beta_symm_of_alt hbeta1 hbeta2 hbetaalt
  -- Frobenius expansion with symmetric coefficients vanishing on the diagonal
  obtain ⟨d, _hdsym, hddiag, hdexp⟩ :=
    bilinear_frob hcard beta (fun y x x' => hbeta1 x x' y) (fun x y y' => hbeta2 x y y')
      hsym hbetaalt
  -- the coefficient constraint
  have hdc : ∀ k ∈ Finset.range n, ∀ l ∈ Finset.range n,
      d k l * (lam ^ (2 ^ k) * lam ^ (2 ^ l) - mu) = 0 :=
    bilinear_frob_general_constraint hcard beta d hdexp lam lam mu hbetaeq
  -- a non-zero coefficient exists since `beta ≠ 0`
  have hex : ∃ k l, k ∈ Finset.range n ∧ l ∈ Finset.range n ∧ d k l ≠ 0 := by
    by_contra hcon
    obtain ⟨a, b, hab⟩ := hbetane
    refine hab ?_
    rw [hdexp a b]
    refine Finset.sum_eq_zero (fun k hk => Finset.sum_eq_zero (fun l hl => ?_))
    by_contra hkl
    exact hcon ⟨k, l, hk, hl, fun h0 => hkl (by rw [h0]; ring)⟩
  obtain ⟨k0, l0, hk0, hl0, hk0ne⟩ := hex
  have hk0lt : k0 < n := Finset.mem_range.mp hk0
  have hl0lt : l0 < n := Finset.mem_range.mp hl0
  -- every non-zero coefficient sits at `(n-1, n-1)`
  have hkey : ∀ k l, k < n → l < n → d k l ≠ 0 → k = n - 1 ∧ l = n - 1 := by
    intro k l hklt hllt hne
    have hc := hdc k (Finset.mem_range.mpr hklt) l (Finset.mem_range.mpr hllt)
    rw [← hmu] at hc
    have hprod : lam ^ (2 ^ k) * lam ^ (2 ^ l) = lam := by
      rcases mul_eq_zero.mp hc with h | h
      · exact absurd h hne
      · exact sub_eq_zero.mp h
    have hpow : lam ^ (2 ^ k + 2 ^ l) = lam ^ 1 := by
      rw [pow_add, hprod, pow_one]
    have hmod : 2 ^ k + 2 ^ l ≡ 1 [MOD 2 ^ n - 1] :=
      modEq_of_pow_eq_pow hlam0 hlamord hpow
    have hA1 : 1 ≤ 2 ^ k + 2 ^ l :=
      le_trans (Nat.one_le_two_pow (n := k)) (Nat.le_add_right _ _)
    have hA2 : 2 ^ k + 2 ^ l ≤ 2 ^ n := by
      have h1 : 2 ^ k ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : 2 ^ l ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h3 : 2 ^ (n - 1) + 2 ^ (n - 1) = 2 ^ n := by
        rw [← two_mul, ← pow_succ']
        congr 1
        omega
      calc 2 ^ k + 2 ^ l ≤ 2 ^ (n - 1) + 2 ^ (n - 1) := add_le_add h1 h2
        _ = 2 ^ n := h3
    have hA2' : 2 ≤ 2 ^ k + 2 ^ l :=
      add_le_add (Nat.one_le_two_pow (n := k)) (Nat.one_le_two_pow (n := l))
    have hsum : 2 ^ k + 2 ^ l = 2 ^ n := by
      rcases eq_or_eq_one_of_modEq hA1 hA2 (le_refl 1) (Nat.one_le_two_pow (n := n)) hmod
        with h | h | h
      · exact absurd h (by omega)
      · exact absurd h.1 (by omega)
      · exact h.1
    exact eq_pred_of_two_pow_add hsum
  obtain ⟨hkn, hln⟩ := hkey k0 l0 hk0lt hl0lt hk0ne
  have hd0 : d (n - 1) (n - 1) = 0 := hddiag (n - 1)
  rw [hkn, hln] at hk0ne
  exact hk0ne hd0

end Work.Higman
