/-
# The Frobenius-resonance endgame of the `C₄` gap

`Work.Higman.H8.c4_resonance_false`: over a field `F` with `2^n` elements (`n ≥ 2`) and
`mu : F` of order `2^n - 1`, there are no biadditive `b φ : F → F → F` with

* `b` symmetric, non-zero, `b (mu * a) (mu * c) = mu^2 * b a c`,
* `φ` non-zero, `φ (mu^2 * a) (mu * c) = mu^2 * φ a c`,
* `φ (b x y) z = φ (b y z) x` for all `x y z`.

This is the eigenvalue-bookkeeping endgame of the `C₄` gap `⁅C,C⁆ = A² = Ω₁(P)`: in the
"two-cover" configuration `P = C·E`, `C ∩ E = A` the eigenvalues of `ξ` on `C/A`, `E/A`,
`A/A²` and `A²` are all forced to `mu` (for the first two) and `mu^2` (for the latter two) —
see `H8/NOTES_c4_gap_session11.md` §§1–2 — and `b`, `φ` are the pairings
`B : C/A × E/A → A/A²`, `φ : A/A² × C/A → A²`, whose Jacobi relation is
`H8.c4_jacobi_pairing` in `H8/c4_card_le.lean`.

Proof: `resonance_support_of_generators` (with `ν = mu`, `t = 1`, `r = 2`) puts the Frobenius
support of `b` on `2^i + 2^j ≡ 2 (mod 2^n-1)`, which by `Q3.two_pow_add_eq_pow` is `{(0,0)}`;
so `b a c = d 0 0 * a * c` with `d 0 0 ≠ 0`.  Likewise `resonance_support_of_generators`
(with `ν = mu^2`, `t = 2^(n-1)`, `r = 1`) puts the support of `φ` on
`2^i + 2^(n-1) * 2^j ≡ 1`; multiplying by `2` and applying `two_pow_add_eq_pow` (splitting off
the case `i + 1 = n` where `2^n ≡ 1`) gives the single point `(n-1, 0)`, so
`φ u v = e (n-1) 0 * u ^ (2^(n-1)) * v` with `e (n-1) 0 ≠ 0`.  The Jacobi relation then reads
`(x y) ^ (2^(n-1)) * z = (y z) ^ (2^(n-1)) * x`, which with `y = z = 1` is
`x ^ (2^(n-1)) = x` for all `x` — false for `x = mu` because `n ≥ 2` and hence
`0 < 2^(n-1) - 1 < 2^n - 1`. -/
import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.resonance_of_equivariant_biadditive
import Submission.Work.Higman.Q3.two_pow_add_eq_pow
import Submission.Work.Higman.H8.frob_pairing_jacobi_false

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace Work.Higman.H8

/-- `x ↦ x ^ (2^(n-1))` is injective on a field with `2^n` elements. -/
private lemma pow_pred_injective {F : Type} [Field F] [Fintype F] {n : ℕ} (hn : 1 ≤ n)
    (hcard : Fintype.card F = 2 ^ n) :
    Function.Injective (fun x : F => x ^ (2 ^ (n - 1))) := by
  intro a c hac
  have hac' : a ^ (2 ^ (n - 1)) = c ^ (2 ^ (n - 1)) := hac
  have hmul : 2 ^ (n - 1) * 2 = 2 ^ n := by rw [← pow_succ]; congr 1; omega
  have ha : (a ^ (2 ^ (n - 1))) ^ 2 = a := by
    rw [← pow_mul, hmul, Work.Higman.pow_two_pow_card hcard a]
  have hc : (c ^ (2 ^ (n - 1))) ^ 2 = c := by
    rw [← pow_mul, hmul, Work.Higman.pow_two_pow_card hcard c]
  rw [← ha, hac', hc]

/-- A `ℕ`-congruence `2^A + 2^B ≡ 2^C (mod 2^n-1)` as a `ℤ`-divisibility. -/
private lemma int_dvd_of_modeq {n A B C : ℕ} (h : 2 ^ A + 2 ^ B ≡ 2 ^ C [MOD 2 ^ n - 1]) :
    (2 ^ n - 1 : ℤ) ∣ (2 ^ A : ℤ) + 2 ^ B - 2 ^ C := by
  have h1 := Nat.ModEq.dvd h
  rw [Nat.cast_sub (Nat.one_le_two_pow)] at h1
  push_cast at h1
  have h2 : (2 ^ n - 1 : ℤ) ∣ -(((2 ^ A : ℤ) + 2 ^ B) - 2 ^ C) := by
    convert h1 using 1; ring
  simpa using dvd_neg.mp h2

theorem c4_resonance_false {n : ℕ} (hn : 2 ≤ n) {F : Type} [Field F] [Fintype F]
    [DecidableEq F] [CharP F 2] (hcard : Fintype.card F = 2 ^ n)
    (mu : F) (hmu : orderOf mu = 2 ^ n - 1)
    (b φ : F → F → F)
    (hb1 : ∀ a a' c : F, b (a + a') c = b a c + b a' c)
    (hb2 : ∀ a c c' : F, b a (c + c') = b a c + b a c')
    (hbsym : ∀ a c : F, b a c = b c a)
    (hbm : ∀ a c : F, b (mu * a) (mu * c) = mu ^ 2 * b a c)
    (hbne : ∃ a c : F, b a c ≠ 0)
    (hf1 : ∀ a a' c : F, φ (a + a') c = φ a c + φ a' c)
    (hf2 : ∀ a c c' : F, φ a (c + c') = φ a c + φ a c')
    (hfm : ∀ a c : F, φ (mu ^ 2 * a) (mu * c) = mu ^ 2 * φ a c)
    (hfne : ∃ a c : F, φ a c ≠ 0)
    (hJac : ∀ x y z : F, φ (b x y) z = φ (b y z) x) :
    False := by
  classical
  have hn1 : 1 ≤ n := by omega
  have hn0 : 0 < n := by omega
  -- ## `b = d 0 0 * x * y`
  obtain ⟨d, hdexp, hdres⟩ :=
    Work.Higman.resonance_support_of_generators hn hcard mu hmu 1 2 b hb1 hb2
      (by intro a c; simpa using hbm a c)
  have hbsupp : ∀ i j : ℕ, i < n → j < n → d i j ≠ 0 → i = 0 ∧ j = 0 := by
    intro i j hi hj hd
    have hmod : 2 ^ i + 2 ^ j ≡ 2 ^ 1 [MOD 2 ^ n - 1] := by simpa using hdres i j hi hj hd
    have hdvd := int_dvd_of_modeq (n := n) hmod
    obtain ⟨hij, hc⟩ := Work.Higman.Q3.two_pow_add_eq_pow (n := n) (A := i) (B := j) (C := 1)
      hn1 hi hj (by omega) hdvd
    rcases hc with h | ⟨h, h0⟩
    · exact ⟨by omega, by omega⟩
    · exact absurd h0 (by norm_num)
  have hbeq : ∀ x y : F, b x y = d 0 0 * x * y := by
    intro x y
    rw [hdexp x y]
    have houter : (∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
        d k l * x ^ (2 ^ k) * y ^ (2 ^ l))
        = (∑ l ∈ Finset.range n, d 0 l * x ^ (2 ^ 0) * y ^ (2 ^ l)) :=
      Finset.sum_eq_single 0 (fun k hk hkne => by
        apply Finset.sum_eq_zero
        intro l hl
        have hk' : k < n := Finset.mem_range.mp hk
        have hl' : l < n := Finset.mem_range.mp hl
        have hz : d k l = 0 := by
          by_contra hz
          exact hkne (hbsupp k l hk' hl' hz).1
        rw [hz, zero_mul, zero_mul]) (fun hmem => absurd (Finset.mem_range.mpr hn0) hmem)
    have hinner : (∑ l ∈ Finset.range n, d 0 l * x ^ (2 ^ 0) * y ^ (2 ^ l))
        = d 0 0 * x ^ (2 ^ 0) * y ^ (2 ^ 0) :=
      Finset.sum_eq_single 0 (fun l hl hlne => by
        have hl' : l < n := Finset.mem_range.mp hl
        have hz : d 0 l = 0 := by
          by_contra hz
          exact hlne (hbsupp 0 l hn0 hl' hz).2
        rw [hz, zero_mul, zero_mul]) (fun hmem => absurd (Finset.mem_range.mpr hn0) hmem)
    rw [houter, hinner]
    simp only [pow_zero, pow_one]
  have hd00 : d 0 0 ≠ 0 := by
    obtain ⟨x, y, hxy⟩ := hbne
    intro h0
    exact hxy (by rw [hbeq x y, h0, zero_mul, zero_mul])
  -- ## `φ u v = e (n-1) 0 * u ^ (2^(n-1)) * v`
  have hodd : Odd (2 ^ n - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact ⟨2 ^ m - 1, by
      have h : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      rw [pow_succ]; omega⟩
  have hmu2order : orderOf (mu ^ 2) = 2 ^ n - 1 := by
    refine Nat.dvd_antisymm ?_ ?_
    · rw [orderOf_dvd_iff_pow_eq_one]
      have h1 : (mu ^ 2) ^ (2 ^ n - 1) = mu ^ (2 * (2 ^ n - 1)) := by rw [pow_mul]
      rw [h1, show 2 * (2 ^ n - 1) = (2 ^ n - 1) * 2 by ring, pow_mul,
        show mu ^ (2 ^ n - 1) = 1 from by rw [← hmu]; exact pow_orderOf_eq_one mu, one_pow]
    · have hcop : Nat.Coprime (2 ^ n - 1) 2 := Nat.coprime_two_right.mpr hodd
      refine hcop.dvd_of_dvd_mul_right ?_
      rw [← hmu]
      refine orderOf_dvd_iff_pow_eq_one.mpr ?_
      have h2 : mu ^ (orderOf (mu ^ 2) * 2) = (mu ^ 2) ^ orderOf (mu ^ 2) := by
        rw [← pow_mul]
        congr 1
        exact Nat.mul_comm _ _
      rw [h2]
      exact pow_orderOf_eq_one (mu ^ 2)
  have hmun : (mu ^ 2) ^ (2 ^ (n - 1)) = mu := by
    rw [← pow_mul, show 2 * 2 ^ (n - 1) = 2 ^ n by rw [← pow_succ']; congr 1; omega]
    exact Work.Higman.pow_two_pow_card hcard mu
  obtain ⟨e, heexp, heres⟩ :=
    Work.Higman.resonance_support_of_generators hn hcard (mu ^ 2) hmu2order (2 ^ (n - 1)) 1 φ
      hf1 hf2 (by intro a c; rw [hmun]; simpa using hfm a c)
  have hpow4 : 2 < 2 ^ n := by
    have h : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  have h1lt : 1 < 2 ^ n - 1 := by omega
  have h2n0 : 2 ^ n ≡ 2 ^ 0 [MOD 2 ^ n - 1] := by
    have h1 : 2 ^ n % (2 ^ n - 1) = 1 := by
      rw [show 2 ^ n % (2 ^ n - 1) = (1 + (2 ^ n - 1) * 1) % (2 ^ n - 1) by
        congr 1
        have h : 1 ≤ 2 ^ n := Nat.one_le_two_pow
        omega]
      rw [Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt h1lt
    have h2 : 2 ^ 0 % (2 ^ n - 1) = 1 := by
      rw [pow_zero]
      exact Nat.mod_eq_of_lt h1lt
    rw [Nat.ModEq, h1, h2]
  have hesupp : ∀ i j : ℕ, i < n → j < n → e i j ≠ 0 → i = n - 1 ∧ j = 0 := by
    intro i j hi hj he
    have hmod : 2 ^ i + 2 ^ (n - 1) * 2 ^ j ≡ 2 ^ 0 [MOD 2 ^ n - 1] := by
      simpa using heres i j hi hj he
    have h1a : 2 ^ i * 2 = 2 ^ (i + 1) := by rw [pow_succ]
    have h1b : 2 ^ (n - 1) * 2 ^ j * 2 = 2 ^ n * 2 ^ j := by
      rw [show 2 ^ (n - 1) * 2 ^ j * 2 = 2 ^ (n + j) by
            rw [← pow_add, ← pow_succ]
            congr 1
            omega,
          show 2 ^ n * 2 ^ j = 2 ^ (n + j) by rw [← pow_add]]
    have h1 : (2 ^ i + 2 ^ (n - 1) * 2 ^ j) * 2 = 2 ^ (i + 1) + 2 ^ n * 2 ^ j := by
      rw [add_mul, h1a, h1b]
    have hnew : 2 ^ (i + 1) + 2 ^ j ≡ 2 ^ 1 [MOD 2 ^ n - 1] := by
      have h3 : 2 ^ (i + 1) + 2 ^ n * 2 ^ j ≡ 2 ^ (i + 1) + 2 ^ j [MOD 2 ^ n - 1] := by
        simpa using (Nat.ModEq.refl (2 ^ (i + 1))).add
          (h2n0.mul (Nat.ModEq.refl (2 ^ j)))
      have h4 : (2 ^ i + 2 ^ (n - 1) * 2 ^ j) * 2 ≡ 1 * 2 [MOD 2 ^ n - 1] :=
        hmod.mul (Nat.ModEq.refl 2)
      rw [h1] at h4
      exact h3.symm.trans (by simpa using h4)
    rcases Nat.lt_or_ge (i + 1) n with hlt | hge
    · have hdvd := int_dvd_of_modeq (n := n) hnew
      obtain ⟨hij, hc⟩ := Work.Higman.Q3.two_pow_add_eq_pow (n := n) (A := i + 1) (B := j)
        (C := 1) hn1 hlt hj (by omega) hdvd
      rcases hc with h | ⟨h, h0⟩ <;> omega
    · have hi1 : i + 1 = n := by omega
      have hnew' : 2 ^ 0 + 2 ^ j ≡ 2 ^ 1 [MOD 2 ^ n - 1] := by
        have h6 : 2 ^ n + 2 ^ j ≡ 2 ^ 0 + 2 ^ j [MOD 2 ^ n - 1] :=
          h2n0.add (Nat.ModEq.refl (2 ^ j))
        have hnew0 : 2 ^ n + 2 ^ j ≡ 2 ^ 1 [MOD 2 ^ n - 1] := by
          have hh : (2 : ℕ) ^ n + 2 ^ j = 2 ^ (i + 1) + 2 ^ j := by rw [hi1]
          rw [hh]; exact hnew
        exact h6.symm.trans hnew0
      have hdvd := int_dvd_of_modeq (n := n) hnew'
      obtain ⟨h0j, hc⟩ := Work.Higman.Q3.two_pow_add_eq_pow (n := n) (A := 0) (B := j) (C := 1)
        hn1 hn0 hj (by omega) hdvd
      rcases hc with h | ⟨h, h0⟩ <;> omega
  have heeq : ∀ u v : F, φ u v = e (n - 1) 0 * u ^ (2 ^ (n - 1)) * v := by
    intro u v
    rw [heexp u v]
    have hnm : n - 1 < n := by omega
    have houter : (∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
        e k l * u ^ (2 ^ k) * v ^ (2 ^ l))
        = (∑ l ∈ Finset.range n, e (n - 1) l * u ^ (2 ^ (n - 1)) * v ^ (2 ^ l)) :=
      Finset.sum_eq_single (n - 1) (fun k hk hkne => by
        apply Finset.sum_eq_zero
        intro l hl
        have hk' : k < n := Finset.mem_range.mp hk
        have hl' : l < n := Finset.mem_range.mp hl
        have hz : e k l = 0 := by
          by_contra hz
          exact hkne (hesupp k l hk' hl' hz).1
        rw [hz, zero_mul, zero_mul]) (fun hmem => absurd (Finset.mem_range.mpr hnm) hmem)
    have hinner : (∑ l ∈ Finset.range n, e (n - 1) l * u ^ (2 ^ (n - 1)) * v ^ (2 ^ l))
        = e (n - 1) 0 * u ^ (2 ^ (n - 1)) * v ^ (2 ^ 0) :=
      Finset.sum_eq_single 0 (fun l hl hlne => by
        have hl' : l < n := Finset.mem_range.mp hl
        have hz : e (n - 1) l = 0 := by
          by_contra hz
          exact hlne (hesupp (n - 1) l hnm hl' hz).2
        rw [hz, zero_mul, zero_mul]) (fun hmem => absurd (Finset.mem_range.mpr hn0) hmem)
    rw [houter, hinner]
    simp only [pow_zero, pow_one]
  have he_ne : e (n - 1) 0 ≠ 0 := by
    obtain ⟨u, v, huv⟩ := hfne
    intro h0
    exact huv (by rw [heeq u v, h0, zero_mul, zero_mul])
  -- ## the Jacobi identity is contradictory
  have hkey : ∀ x z : F, x ^ (2 ^ (n - 1)) * z = z ^ (2 ^ (n - 1)) * x := by
    intro x z
    have h := hJac x 1 z
    rw [hbeq x 1, hbeq 1 z, heeq (d 0 0 * x * 1) z, heeq (d 0 0 * 1 * z) x] at h
    have hL : (d 0 0 * x * 1) ^ (2 ^ (n - 1))
        = d 0 0 ^ (2 ^ (n - 1)) * x ^ (2 ^ (n - 1)) := by
      rw [mul_pow, mul_pow, one_pow, mul_one]
    have hR : (d 0 0 * 1 * z) ^ (2 ^ (n - 1))
        = d 0 0 ^ (2 ^ (n - 1)) * z ^ (2 ^ (n - 1)) := by
      rw [mul_pow, mul_pow, one_pow, mul_one]
    rw [hL, hR] at h
    have hd : d 0 0 ^ (2 ^ (n - 1)) ≠ 0 := pow_ne_zero _ hd00
    have h1 : e (n - 1) 0 * (d 0 0 ^ (2 ^ (n - 1)) * (x ^ (2 ^ (n - 1)) * z))
        = e (n - 1) 0 * (d 0 0 ^ (2 ^ (n - 1)) * (z ^ (2 ^ (n - 1)) * x)) := by
      simpa only [mul_assoc] using h
    have h2 := mul_left_cancel₀ he_ne h1
    exact mul_left_cancel₀ hd h2
  have hzall : ∀ z : F, z ^ (2 ^ (n - 1)) = z := by
    intro z
    have h := hkey 1 z
    simpa using h.symm
  have hmu0 : mu ≠ 0 := by
    intro h0
    have h1 := pow_orderOf_eq_one mu
    rw [hmu, h0] at h1
    rw [zero_pow (by omega : 2 ^ n - 1 ≠ 0)] at h1
    exact zero_ne_one h1
  have hres : mu ^ (2 ^ (n - 1) - 1) = 1 := by
    have h1 : mu ^ (2 ^ (n - 1) - 1) * mu = mu := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_two_pow)]
      exact hzall mu
    have h1' : mu ^ (2 ^ (n - 1) - 1) * mu = 1 * mu := by rw [one_mul]; exact h1
    exact mul_right_cancel₀ hmu0 h1'
  have hdvd : (2 ^ n - 1) ∣ (2 ^ (n - 1) - 1) := by
    rw [← hmu]
    exact orderOf_dvd_iff_pow_eq_one.mpr hres
  have h4 : 2 ≤ 2 ^ (n - 1) := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpos : 0 < 2 ^ (n - 1) - 1 := by omega
  have hlt : 2 ^ (n - 1) - 1 < 2 ^ n - 1 := by
    have h5 : 2 ^ n = 2 * 2 ^ (n - 1) := by rw [← pow_succ']; congr 1; omega
    omega
  have := Nat.le_of_dvd hpos hdvd
  omega

end Work.Higman.H8
