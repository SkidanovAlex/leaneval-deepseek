import Mathlib
import Submission.Work.Higman.c4_field_core
import Submission.Work.Higman.bivariate_monomial_indep

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.Higman

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- **Resonance (support condition) for a `ξ`-equivariant biadditive pairing.**

Let `|F| = 2 ^ n` (`n ≥ 2`), let `ν` generate `Fˣ` (so `orderOf ν = 2 ^ n - 1`), and let
`B : F → F → F` be additive in each variable with
`B (ν * a) (ν ^ t * b) = ν * B a b`.  Then in the Frobenius expansion
`B x y = ∑_{i,j < n} d i j * x ^ (2^i) * y ^ (2 ^ j)`, every non-zero coefficient satisfies the
resonance `ν ^ (2 ^ i + t * 2 ^ j) = ν`, i.e. `2 ^ i + t * 2 ^ j ≡ 1 (mod 2 ^ n - 1)`.

This is the eigenvalue bookkeeping of Higman §4 Lemma 6 in the form needed for the case `D/A`
of the `C₄` configuration: the equivariance of the pairing forces its support to lie on the
resonance locus, whose arithmetic is what excludes the exotic pairs of Singer actions. -/
theorem resonance_of_equivariant_biadditive {n : ℕ} (hn : 2 ≤ n)
    (hcard : Fintype.card F = 2 ^ n) (ν : F) (hν : orderOf ν = 2 ^ n - 1) (t : ℕ)
    (B : F → F → F)
    (hB1 : ∀ a b d : F, B (a + b) d = B a d + B b d)
    (hB2 : ∀ a b d : F, B a (b + d) = B a b + B a d)
    (heq : ∀ a b : F, B (ν * a) (ν ^ t * b) = ν * B a b) :
    ∃ d : ℕ → ℕ → F,
      (∀ x y : F, B x y =
        ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
          d k l * x ^ (2 ^ k) * y ^ (2 ^ l)) ∧
      ∀ i j : ℕ, i < n → j < n → d i j ≠ 0 →
        2 ^ i + t * 2 ^ j ≡ 1 [MOD 2 ^ n - 1] := by
  classical
  obtain ⟨d, hdexp⟩ := bilinear_frob_general hcard B
    (fun y x x' => hB1 x x' y) (fun x y y' => hB2 x y y')
  refine ⟨d, hdexp, ?_⟩
  -- `ν ≠ 0`
  have hνpow : ν ^ (2 ^ n - 1) = 1 := by
    rw [← hν]; exact pow_orderOf_eq_one ν
  have hpow2 : 2 ≤ 2 ^ n := by
    calc (2:ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hν0 : ν ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega : 2 ^ n - 1 ≠ 0)] at hνpow
    exact zero_ne_one hνpow
  -- the equivariance, expanded: only resonant coefficients can survive
  have hkey : ∀ x y : F,
      ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
        ((ν ^ (2 ^ k + t * 2 ^ l) - ν) * d k l) * x ^ (2 ^ k) * y ^ (2 ^ l) = 0 := by
    intro x y
    have hsum : (∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
          d k l * (ν * x) ^ (2 ^ k) * (ν ^ t * y) ^ (2 ^ l))
        = B (ν * x) (ν ^ t * y) := (hdexp (ν * x) (ν ^ t * y)).symm
    have hsum' : (∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
          ν * (d k l * x ^ (2 ^ k) * y ^ (2 ^ l))) = ν * B x y := by
      rw [hdexp x y, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum]
    have hdiff : (∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
          ((ν ^ (2 ^ k + t * 2 ^ l) - ν) * d k l) * x ^ (2 ^ k) * y ^ (2 ^ l))
        = (∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
            (d k l * (ν * x) ^ (2 ^ k) * (ν ^ t * y) ^ (2 ^ l)
              - ν * (d k l * x ^ (2 ^ k) * y ^ (2 ^ l)))) := by
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      have hp : ν ^ (2 ^ k + t * 2 ^ l) = ν ^ (2 ^ k) * ν ^ (t * 2 ^ l) := by rw [pow_add]
      rw [mul_pow, mul_pow, ← pow_mul, hp]
      ring
    rw [hdiff]
    simp only [Finset.sum_sub_distrib]
    rw [hsum, hsum', heq x y, sub_self]
  have hvan := bivariate_monomial_indep hcard
    (fun k l => (ν ^ (2 ^ k + t * 2 ^ l) - ν) * d k l) hkey
  intro i j hi hj hdij
  have h0 : (ν ^ (2 ^ i + t * 2 ^ j) - ν) * d i j = 0 :=
    hvan i (Finset.mem_range.mpr hi) j (Finset.mem_range.mpr hj)
  have h1 : ν ^ (2 ^ i + t * 2 ^ j) = ν := by
    rcases mul_eq_zero.mp h0 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hdij
  -- pass to the unit group to convert the power relation into a congruence
  set u : Fˣ := Units.mk0 ν hν0 with hu
  have huval : (u : F) = ν := by rw [hu]; exact Units.val_mk0 hν0
  have huord : orderOf u = 2 ^ n - 1 := by
    rw [← orderOf_units, huval]; exact hν
  have h1u : u ^ (2 ^ i + t * 2 ^ j) = u ^ 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, huval, pow_one]
    exact h1
  have h2 : (2 ^ i + t * 2 ^ j) ≡ 1 [MOD orderOf u] := pow_eq_pow_iff_modEq.mp h1u
  rwa [huord] at h2

/-! ## The `t = 1` (isomorphic) case, and the limits of the counting route -/

/-- **`t = 1` support concentration.**  When the two Singer actions agree (`t = 1`), the resonance
locus `2 ^ i + 2 ^ j ≡ 1 (mod 2 ^ n - 1)` is the single point `(n-1, n-1)`: the pairing is then
concentrated at the top Frobenius exponents. -/
theorem two_pow_eq_two_pow_of_sum {n i j : ℕ} (hi : i < n) (hj : j < n)
    (h : 2 ^ i + 2 ^ j = 2 ^ n) : i = n - 1 ∧ j = n - 1 := by
  have h1 : 2 ^ i ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ j ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : 2 ^ (n - 1) * 2 = 2 ^ n := by
    rw [← pow_succ]
    congr 1
    omega
  have hi' : 2 ^ i = 2 ^ (n - 1) := by omega
  have hj' : 2 ^ j = 2 ^ (n - 1) := by omega
  exact ⟨Nat.pow_right_injective (by norm_num) hi', Nat.pow_right_injective (by norm_num) hj'⟩

/-- **The resonance condition alone does not exclude `s ≠ 1`.**

With `t = 2 ^ s - 1` the resonance `2 ^ i + t * 2 ^ j ≡ 1 (mod 2 ^ n - 1)` is *satisfiable* for
`s ≠ 1`: for `n = 3`, `s = 2` (`t = 3`) and `i = j = 1` one has `2 + 3 * 2 = 8 ≡ 1 (mod 7)`.

Consequently the counting/eigenvalue argument (`coprime_orderOf_div_card_sub_one`) cannot by
itself close the residual `C₄` case: the exclusion of the exotic (`s ≠ 1`) pairs needs the
alternating pairing and the anisotropy of the squaring form as well, i.e. the full Higman
§4/§6 (Lemma 12-type) analysis.  This lemma records that obstruction as a no-go statement. -/
theorem resonance_satisfiable_of_s_ne_one :
    2 ^ 1 + (2 ^ 2 - 1) * 2 ^ 1 ≡ 1 [MOD 2 ^ 3 - 1] := by
  decide

/-! ## The exotic (two-generator) resonance interface -/

/-- **Resonance for the exotic Singer twist** (the pinned-form interface used by
`Work.Higman.isom_crux_exotic`).

Let `|F| = 2 ^ n` (`n ≥ 2`), let `ν` generate `Fˣ`, and let `B : F → F → F` be biadditive with
`B (ν * a) (ν ^ t * b) = ν ^ r * B a b`.  Then the Frobenius support of `B` lies on the
resonance locus `2 ^ k + t * 2 ^ l ≡ r (mod 2 ^ n - 1)`.

Writing `ν' = ν ^ t`, `λ = ν ^ r`, this is exactly Higman's resonance
`ν ^ (2 ^ k) * ν' ^ (2 ^ l) = λ` on the non-zero coefficients of the pinned normal form of `Q`,
which is the input to the exotic case of the isometry crux. -/
theorem resonance_support_of_generators {n : ℕ} (hn : 2 ≤ n)
    (hcard : Fintype.card F = 2 ^ n) (ν : F) (hν : orderOf ν = 2 ^ n - 1) (t r : ℕ)
    (B : F → F → F)
    (hB1 : ∀ a b d : F, B (a + b) d = B a d + B b d)
    (hB2 : ∀ a b d : F, B a (b + d) = B a b + B a d)
    (heq : ∀ a b : F, B (ν * a) (ν ^ t * b) = ν ^ r * B a b) :
    ∃ d : ℕ → ℕ → F,
      (∀ x y : F, B x y =
        ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
          d k l * x ^ (2 ^ k) * y ^ (2 ^ l)) ∧
      ∀ i j : ℕ, i < n → j < n → d i j ≠ 0 →
        2 ^ i + t * 2 ^ j ≡ r [MOD 2 ^ n - 1] := by
  classical
  obtain ⟨d, hdexp⟩ := bilinear_frob_general hcard B
    (fun y x x' => hB1 x x' y) (fun x y y' => hB2 x y y')
  refine ⟨d, hdexp, ?_⟩
  have hkey : ∀ x y : F,
      ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
        ((ν ^ (2 ^ k + t * 2 ^ l) - ν ^ r) * d k l) * x ^ (2 ^ k) * y ^ (2 ^ l) = 0 := by
    intro x y
    have hsum : (∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
          d k l * (ν * x) ^ (2 ^ k) * (ν ^ t * y) ^ (2 ^ l))
        = B (ν * x) (ν ^ t * y) := (hdexp (ν * x) (ν ^ t * y)).symm
    have hsum' : (∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
          ν ^ r * (d k l * x ^ (2 ^ k) * y ^ (2 ^ l))) = ν ^ r * B x y := by
      rw [hdexp x y, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum]
    have hdiff : (∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
          ((ν ^ (2 ^ k + t * 2 ^ l) - ν ^ r) * d k l) * x ^ (2 ^ k) * y ^ (2 ^ l))
        = (∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
            (d k l * (ν * x) ^ (2 ^ k) * (ν ^ t * y) ^ (2 ^ l)
              - ν ^ r * (d k l * x ^ (2 ^ k) * y ^ (2 ^ l)))) := by
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      have hp : ν ^ (2 ^ k + t * 2 ^ l) = ν ^ (2 ^ k) * ν ^ (t * 2 ^ l) := by rw [pow_add]
      rw [mul_pow, mul_pow, ← pow_mul, hp]
      ring
    rw [hdiff]
    simp only [Finset.sum_sub_distrib]
    rw [hsum, hsum', heq x y, sub_self]
  have hvan := bivariate_monomial_indep hcard
    (fun k l => (ν ^ (2 ^ k + t * 2 ^ l) - ν ^ r) * d k l) hkey
  intro i j hi hj hdij
  have h0 : (ν ^ (2 ^ i + t * 2 ^ j) - ν ^ r) * d i j = 0 :=
    hvan i (Finset.mem_range.mpr hi) j (Finset.mem_range.mpr hj)
  have h1 : ν ^ (2 ^ i + t * 2 ^ j) = ν ^ r := by
    rcases mul_eq_zero.mp h0 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hdij
  set u : Fˣ := Units.mk0 ν (by
    intro h0
    rw [h0] at hν
    simp at hν
    have : 2 ≤ 2 ^ n := by
      calc (2:ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega) with hu
  have huval : (u : F) = ν := by rw [hu]; exact Units.val_mk0 _
  have huord : orderOf u = 2 ^ n - 1 := by
    rw [← orderOf_units, huval]; exact hν
  have h1u : u ^ (2 ^ i + t * 2 ^ j) = u ^ r := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, huval]
    exact h1
  have h2 : (2 ^ i + t * 2 ^ j) ≡ r [MOD orderOf u] := pow_eq_pow_iff_modEq.mp h1u
  rwa [huord] at h2

end Work.Higman
