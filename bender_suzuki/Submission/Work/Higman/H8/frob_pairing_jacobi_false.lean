import Mathlib
import Submission.Work.Higman.bivariate_monomial_indep
import Submission.Work.Higman.bilinear_frob
import Submission.Work.Higman.resonance_of_equivariant_biadditive
import Submission.Work.Higman.Q3.two_pow_add_eq_pow

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman.H8

/-- On a finite field `F` with `|F| = 2 ^ n` the map `x ↦ x ^ (2 ^ (n - 1))` is injective:
squaring separates the values, and `x ^ (2 ^ n) = x` on `F`. -/
private lemma pow_two_pow_pred_injective {F : Type} [Field F] [Fintype F] {n : ℕ} (hn : 1 ≤ n)
    (hcard : Fintype.card F = 2 ^ n) : Function.Injective (fun x : F => x ^ (2 ^ (n - 1))) := by
  intro a b hab
  have hab' : a ^ (2 ^ (n - 1)) = b ^ (2 ^ (n - 1)) := hab
  have hmul : 2 ^ (n - 1) * 2 = 2 ^ n := by rw [← pow_succ]; congr 1; omega
  have h2 : (a ^ (2 ^ (n - 1))) ^ 2 = (b ^ (2 ^ (n - 1))) ^ 2 := by rw [hab']
  have ha : (a ^ (2 ^ (n - 1))) ^ 2 = a := by
    rw [← pow_mul, hmul, Work.Higman.pow_two_pow_card hcard a]
  have hb : (b ^ (2 ^ (n - 1))) ^ 2 = b := by
    rw [← pow_mul, hmul, Work.Higman.pow_two_pow_card hcard b]
  rw [ha, hb] at h2
  exact h2

/-- **The `𝔽_q`-resonance/Jacobi coefficient comparison.**  Let `F` be a field with `2 ^ n`
elements (`n ≥ 2`), `lam` a generator of `Fˣ`, and `t` with `1 ≤ t ≤ 2 ^ n - 2`.  Let
`B : F → F → F` and `P : F → F → F` be additive in each variable with
`B (lam ^ t * a) (lam * b) = lam * B a b` and `P (lam * a) (lam * b) = lam * P a b`, both
non-zero.  Then the "Jacobi" symmetry `P (B y x) z = P (B y z) x` (for all `y x z`) is
impossible. -/
theorem frob_pairing_jacobi_false {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
    {n : ℕ} (hn : 2 ≤ n) (hcard : Fintype.card F = 2 ^ n) {lam : F}
    (hlam : orderOf lam = 2 ^ n - 1) {t : ℕ} (ht1 : 1 ≤ t) (ht2 : t ≤ 2 ^ n - 2)
    {B P : F → F → F}
    (hB1 : ∀ a b d : F, B (a + b) d = B a d + B b d)
    (hB2 : ∀ a b d : F, B a (b + d) = B a b + B a d)
    (hBeq : ∀ a b : F, B (lam ^ t * a) (lam * b) = lam * B a b)
    (hBne : ∃ a b : F, B a b ≠ 0)
    (hP1 : ∀ a b d : F, P (a + b) d = P a d + P b d)
    (hP2 : ∀ a b d : F, P a (b + d) = P a b + P a d)
    (hPeq : ∀ a b : F, P (lam * a) (lam * b) = lam * P a b)
    (hPne : ∃ a b : F, P a b ≠ 0)
    (hjac : ∀ y x z : F, P (B y x) z = P (B y z) x) : False := by
  classical
  -- ## Step 1: Frobenius expansion of `P` and its resonance support.
  --
  -- `P` is `lam`-equivariant on both variables, so `resonance_support_of_generators`
  -- (with `ν = lam`, `t = 1`, `r = 1`) expands `P` in the Frobenius basis
  -- `(x,y) ↦ x ^ (2 ^ k) * y ^ (2 ^ l)` and forces every non-zero coefficient to lie on the
  -- resonance locus `2 ^ k + 2 ^ l ≡ 1 (mod 2 ^ n - 1)`.
  obtain ⟨p, hpexp, hpres⟩ :=
    Work.Higman.resonance_support_of_generators hn hcard lam hlam 1 1 P hP1 hP2
      (fun a b => by simpa using hPeq a b)
  -- ## Step 2: the resonance locus is the single point `(n - 1, n - 1)`.
  have hp_supp : ∀ i j : ℕ, i < n → j < n → p i j ≠ 0 → i = n - 1 ∧ j = n - 1 := by
    intro i j hi hj hpij
    have hmod : 2 ^ i + 2 ^ j ≡ 1 [MOD 2 ^ n - 1] := by
      simpa using hpres i j hi hj hpij
    -- `1 = 2 ^ 0`, so this is `2 ^ i + 2 ^ j ≡ 2 ^ 0`.
    have hdvd : (2 ^ n - 1 : ℤ) ∣ (2 ^ i : ℤ) + 2 ^ j - 2 ^ 0 := by
      have h1 := Nat.ModEq.dvd hmod
      rw [Nat.cast_sub (Nat.one_le_two_pow)] at h1
      push_cast at h1
      have h2 : (2 ^ n - 1 : ℤ) ∣ -(((2 ^ i : ℤ) + 2 ^ j) - 2 ^ 0) := by
        convert h1 using 1; ring
      simpa using dvd_neg.mp h2
    have hkey := Work.Higman.Q3.two_pow_add_eq_pow (n := n) (A := i) (B := j) (C := 0)
      (by omega) hi hj (by omega) hdvd
    obtain ⟨hij, hc⟩ := hkey
    refine ⟨?_, ?_⟩ <;> (rcases hc with h | ⟨h, _⟩ <;> omega)
  -- ## Step 3: consequently `P` is the single monomial `p (n-1) (n-1) * x ^ (2^(n-1)) * y ^ (2^(n-1))`.
  have hP_eq : ∀ u v : F,
      P u v = p (n - 1) (n - 1) * u ^ (2 ^ (n - 1)) * v ^ (2 ^ (n - 1)) := by
    intro u v
    rw [hpexp u v]
    have hnm : n - 1 < n := by omega
    have houter : (∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
          p k l * u ^ (2 ^ k) * v ^ (2 ^ l))
        = (∑ l ∈ Finset.range n, p (n - 1) l * u ^ (2 ^ (n - 1)) * v ^ (2 ^ l)) :=
      Finset.sum_eq_single (n - 1) (fun k hk hkne => by
        apply Finset.sum_eq_zero
        intro l hl
        have hk' : k < n := Finset.mem_range.mp hk
        have hl' : l < n := Finset.mem_range.mp hl
        have : p k l = 0 := by
          by_contra hp; exact hkne (hp_supp k l hk' hl' hp).1
        rw [this, zero_mul, zero_mul]) (fun hmem => absurd (Finset.mem_range.mpr hnm) hmem)
    have hinner : (∑ l ∈ Finset.range n, p (n - 1) l * u ^ (2 ^ (n - 1)) * v ^ (2 ^ l))
        = p (n - 1) (n - 1) * u ^ (2 ^ (n - 1)) * v ^ (2 ^ (n - 1)) :=
      Finset.sum_eq_single (n - 1) (fun l hl hlne => by
        have hl' : l < n := Finset.mem_range.mp hl
        have : p (n - 1) l = 0 := by
          by_contra hp; exact hlne (hp_supp (n - 1) l hnm hl' hp).2
        rw [this, zero_mul, zero_mul]) (fun hmem => absurd (Finset.mem_range.mpr hnm) hmem)
    rw [houter, hinner]
  have hdne : p (n - 1) (n - 1) ≠ 0 := by
    obtain ⟨a, b, hab⟩ := hPne
    intro hp0
    exact hab (by rw [hP_eq a b, hp0, zero_mul, zero_mul])
  -- ## Step 4: Jacobi reduces to `B y x * z = B y z * x`.
  --
  -- Since `x ↦ x ^ (2^(n-1))` is multiplicative and injective, the Jacobi identity
  -- `P (B y x) z = P (B y z) x` becomes `B y x * z = B y z * x` for all `y x z`.
  have hjac' : ∀ y x z : F, B y x * z = B y z * x := by
    intro y x z
    have h := hjac y x z
    rw [hP_eq (B y x) z, hP_eq (B y z) x] at h
    have h3 : p (n - 1) (n - 1) * ((B y x) ^ (2 ^ (n - 1)) * z ^ (2 ^ (n - 1)))
        = p (n - 1) (n - 1) * ((B y z) ^ (2 ^ (n - 1)) * x ^ (2 ^ (n - 1))) := by
      rw [← mul_assoc, ← mul_assoc]; exact h
    have h4 := mul_left_cancel₀ hdne h3
    have h5 : (B y x * z) ^ (2 ^ (n - 1)) = (B y z * x) ^ (2 ^ (n - 1)) := by
      rw [mul_pow, mul_pow]; exact h4
    exact pow_two_pow_pred_injective (by omega) hcard h5
  have hBform : ∀ y x : F, B y x = B y 1 * x := by
    intro y x
    have := hjac' y x 1
    simpa using this
  -- ## Step 5: `g a := B a 1` is additive and invariant under `a ↦ lam ^ t * a`, hence zero.
  let g : F →+ F :=
    { toFun := fun y => B y 1
      map_zero' := by
        have h := hB1 0 0 1
        rw [add_zero] at h
        have h' : B 0 1 + 0 = B 0 1 + B 0 1 := by rw [add_zero]; exact h
        exact (add_left_cancel h').symm
      map_add' := fun a b => hB1 a b 1 }
  have hlam0 : lam ≠ 0 := by
    intro h0
    have h := pow_orderOf_eq_one lam
    rw [hlam, h0] at h
    have hne : 2 ^ n - 1 ≠ 0 := by
      have h2 : 2 ≤ 2 ^ n := by
        calc (2 : ℕ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rw [zero_pow hne] at h
    exact zero_ne_one h
  have hg_shift : ∀ a : F, g (lam ^ t * a) = g a := by
    intro a
    have h := hBeq a 1
    rw [mul_one] at h
    rw [hBform (lam ^ t * a) lam] at h
    rw [mul_comm lam (B a 1)] at h
    exact mul_right_cancel₀ hlam0 h
  have hlamt_ne_one : lam ^ t ≠ 1 := by
    intro h
    have hdvd : orderOf lam ∣ t := orderOf_dvd_iff_pow_eq_one.mpr h
    rw [hlam] at hdvd
    have hlt : t < 2 ^ n - 1 := by omega
    have hle : 2 ^ n - 1 ≤ t := Nat.le_of_dvd (by omega) hdvd
    omega
  have hgz : ∀ y : F, g y = 0 := by
    intro y
    have hc : lam ^ t - 1 ≠ 0 := sub_ne_zero.mpr hlamt_ne_one
    -- `lam ^ t - 1` is a non-zero scalar, so every `y` is of the form `(lam ^ t - 1) * c`.
    obtain ⟨c, hc'⟩ : ∃ c, (lam ^ t - 1) * c = y :=
      ⟨(lam ^ t - 1)⁻¹ * y, by rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]⟩
    rw [← hc']
    have hsubst : (lam ^ t - 1) * c = lam ^ t * c - c := by ring
    rw [hsubst, map_sub, hg_shift c, sub_self]
  -- ## Step 6: this forces `B = 0`, contradicting `hBne`.
  obtain ⟨a, b, hab⟩ := hBne
  rw [hBform a b] at hab
  have hga : B a 1 = 0 := hgz a
  rw [hga, zero_mul] at hab
  exact hab rfl

end Work.Higman.H8
