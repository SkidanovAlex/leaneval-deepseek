import Submission.ZagierHoffmanProof.GenEvalEntire
import Submission.Commons.RingTheory.PowerSeries.coeff_mul_X

/-!
# Gauss norms on power series and the Schwarz–Jensen inequality (ABP, analytic part)

This file develops the *coefficient* (Gauss) norm formalism used in the
Anderson–Brownawell–Papanikolas criterion.

For a nonarchimedean valued field `K` and a radius `r : Γ₀` we say that `A` is a **Gauss norm of
`f` at radius `r`** if

  `v (fₙ) · rⁿ ≤ A` for all `n`, with equality for some `n`   (`IsGaussNormAt r f A`).

Main results.

* `IsGaussNormAt.mul` — multiplicativity: the Gauss norm of a product is the product
  (the weighted form of `Commons.RingTheory.PowerSeries.gaussNorm_mul`).
* `IsGaussNormAt.prod` — the Gauss norm at radius `r` of a product `∏ (X - C ωᵢ)` of linear
  factors with `v ωᵢ ≤ r` is `r` to the number of factors.
* ★★★ `v_coeff_le_of_gaussNorm` — **the Schwarz–Jensen inequality in coefficient form**: if
  `E = (∏ᵢ (X - C ωᵢ)) · G` with `1 ≤ v ωᵢ ≤ r`, then for every `m`

    `v (E_m) ≤ (∏ᵢ v ωᵢ) · |E|_r · r^{-M}`,

  where `|E|_r` is the Gauss norm of `E` at radius `r`.  No maximum-modulus principle is needed:
  the statement is coefficientwise.
-/

set_option autoImplicit false
open Filter Polynomial
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

section algebra

variable {r a b c d : Γ₀}

/-- `(r^p)⁻¹ * (r^q)⁻¹ = (r^(p+q))⁻¹`. -/
lemma gauss_inv_pow_mul_inv_pow (r : Γ₀) (p q : ℕ) : (r ^ p)⁻¹ * (r ^ q)⁻¹ = (r ^ (p + q))⁻¹ := by
  rw [← mul_inv_rev, mul_comm (r ^ q) (r ^ p), ← pow_add]

/-- `(a * (r^p)⁻¹) * (b * (r^q)⁻¹) = a * b * (r^(p+q))⁻¹`. -/
lemma gauss_mul_inv_pow_mul_inv_pow (a b : Γ₀) (r : Γ₀) (p q : ℕ) :
    (a * (r ^ p)⁻¹) * (b * (r ^ q)⁻¹) = a * b * (r ^ (p + q))⁻¹ := by
  rw [mul_mul_mul_comm, gauss_inv_pow_mul_inv_pow]

/-- For `r ≠ 0`, `a ≤ b * r⁻ⁿ ↔ a * rⁿ ≤ b`. -/
lemma gauss_le_mul_inv_pow_iff {r : Γ₀} (hr : r ≠ 0) (n : ℕ) {a b : Γ₀} :
    a ≤ b * (r ^ n)⁻¹ ↔ a * r ^ n ≤ b := by
  constructor
  · intro h
    calc a * r ^ n ≤ b * (r ^ n)⁻¹ * r ^ n := mul_le_mul_left h (r ^ n)
      _ = b := by rw [mul_assoc, inv_mul_cancel₀ (pow_ne_zero n hr), mul_one]
  · intro h
    calc a = a * r ^ n * (r ^ n)⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ (pow_ne_zero n hr), mul_one]
      _ ≤ b * (r ^ n)⁻¹ := mul_le_mul_left h _

/-- Strict version, with the strictness on the left factor. -/
lemma mul_lt_mul_of_lt_of_le' {a b c d : Γ₀} (h1 : a < b) (h2 : c ≤ d) (hb : 0 < b)
    (hd : 0 < d) : a * c < b * d := by
  rcases eq_or_lt_of_le (zero_le : (0 : Γ₀) ≤ c) with hc | hc
  · rw [← hc, mul_zero]; exact mul_pos hb hd
  · calc a * c < b * c := mul_lt_mul_of_pos_right h1 hc
      _ ≤ b * d := mul_le_mul_of_nonneg_left h2 hb.le

/-- Strict version, with the strictness on the right factor. -/
lemma mul_lt_mul_of_le_of_lt' {a b c d : Γ₀} (h1 : a ≤ b) (h2 : c < d) (hb : 0 < b)
    (hd : 0 < d) : a * c < b * d := by
  rcases eq_or_lt_of_le (zero_le : (0 : Γ₀) ≤ a) with ha0 | ha0
  · rw [← ha0, zero_mul]; exact mul_pos hb hd
  · calc a * c < a * d := mul_lt_mul_of_pos_left h2 ha0
      _ ≤ b * d := mul_le_mul_of_nonneg_right h1 zero_le

end algebra

/-- `A` is a **Gauss norm** of the power series `f` at the radius `r`: `v (fₙ) · rⁿ ≤ A` for
every `n`, with equality for at least one `n`. -/
def IsGaussNormAt (r : Γ₀) (f : PowerSeries K) (A : Γ₀) : Prop :=
  (∀ n : ℕ, Valued.v (PowerSeries.coeff n f) * r ^ n ≤ A) ∧
    ∃ n : ℕ, Valued.v (PowerSeries.coeff n f) * r ^ n = A

lemma IsGaussNormAt.bound {r A : Γ₀} {f : PowerSeries K} (h : IsGaussNormAt r f A) (n : ℕ) :
    Valued.v (PowerSeries.coeff n f) * r ^ n ≤ A := h.1 n

lemma IsGaussNormAt.attained {r A : Γ₀} {f : PowerSeries K} (h : IsGaussNormAt r f A) :
    ∃ n : ℕ, Valued.v (PowerSeries.coeff n f) * r ^ n = A := h.2

/-- The Gauss norm at radius `r` is unique. -/
lemma IsGaussNormAt.unique {r A A' : Γ₀} {f : PowerSeries K}
    (h : IsGaussNormAt r f A) (h' : IsGaussNormAt r f A') : A = A' := by
  refine le_antisymm ?_ ?_
  · obtain ⟨n, hn⟩ := h.2
    rw [← hn]
    exact h'.1 n
  · obtain ⟨n, hn⟩ := h'.2
    rw [← hn]
    exact h.1 n

lemma isGaussNormAt_zero (r : Γ₀) : IsGaussNormAt r (0 : PowerSeries K) 0 := by
  refine ⟨fun n => ?_, ⟨0, ?_⟩⟩
  · rw [map_zero (PowerSeries.coeff n), map_zero (Valued.v), zero_mul]
  · rw [map_zero (PowerSeries.coeff 0), map_zero (Valued.v), zero_mul]

lemma isGaussNormAt_one (r : Γ₀) : IsGaussNormAt r (1 : PowerSeries K) 1 := by
  refine ⟨fun n => ?_, ⟨0, ?_⟩⟩
  · rcases eq_or_ne n 0 with rfl | hn
    · rw [PowerSeries.coeff_one, if_pos rfl, map_one, pow_zero, mul_one]
    · rw [PowerSeries.coeff_one, if_neg hn, map_zero, zero_mul]
      exact zero_le
  · rw [PowerSeries.coeff_one, if_pos rfl, map_one, pow_zero, mul_one]

lemma isGaussNormAt_neg {r A : Γ₀} {f : PowerSeries K} (h : IsGaussNormAt r f A) :
    IsGaussNormAt r (-f) A := by
  refine ⟨fun n => ?_, ?_⟩
  · rw [map_neg (PowerSeries.coeff n), Valuation.map_neg]
    exact h.1 n
  · obtain ⟨n, hn⟩ := h.2
    exact ⟨n, by rw [map_neg (PowerSeries.coeff n), Valuation.map_neg, hn]⟩

section mul

variable {r A B : Γ₀} {f g : PowerSeries K}

/-- **Gauss-norm multiplicativity**, weighted form: the Gauss norm at radius `r` of a product is
the product of the Gauss norms. -/
theorem IsGaussNormAt.mul (hr : r ≠ 0) (hf : IsGaussNormAt r f A) (hg : IsGaussNormAt r g B) :
    IsGaussNormAt r (f * g) (A * B) := by
  rcases eq_or_ne A 0 with hA | hA
  · have hf0 : f = 0 := by
      ext n
      have h := hf.1 n
      rw [hA] at h
      have hz : Valued.v (PowerSeries.coeff n f) * r ^ n = 0 := le_antisymm h zero_le
      rcases mul_eq_zero.mp hz with h' | h'
      · exact (Valuation.zero_iff Valued.v).mp h'
      · exact absurd h' (pow_ne_zero n hr)
    rw [hf0, zero_mul, hA, zero_mul]
    exact isGaussNormAt_zero r
  rcases eq_or_ne B 0 with hB | hB
  · have hg0 : g = 0 := by
      ext n
      have h := hg.1 n
      rw [hB] at h
      have hz : Valued.v (PowerSeries.coeff n g) * r ^ n = 0 := le_antisymm h zero_le
      rcases mul_eq_zero.mp hz with h' | h'
      · exact (Valuation.zero_iff Valued.v).mp h'
      · exact absurd h' (pow_ne_zero n hr)
    rw [hg0, mul_zero, hB, mul_zero]
    exact isGaussNormAt_zero r
  have hApos : 0 < A := lt_of_le_of_ne zero_le (Ne.symm hA)
  have hBpos : 0 < B := lt_of_le_of_ne zero_le (Ne.symm hB)
  obtain ⟨kA, hkA⟩ := hf.2
  obtain ⟨kB, hkB⟩ := hg.2
  have hexA : ∃ n : ℕ, Valued.v (PowerSeries.coeff n f) * r ^ n = A := ⟨kA, hkA⟩
  have hexB : ∃ n : ℕ, Valued.v (PowerSeries.coeff n g) * r ^ n = B := ⟨kB, hkB⟩
  set p := Nat.find hexA with hpdef
  set q := Nat.find hexB with hqdef
  have hp : Valued.v (PowerSeries.coeff p f) * r ^ p = A := Nat.find_spec hexA
  have hq : Valued.v (PowerSeries.coeff q g) * r ^ q = B := Nat.find_spec hexB
  have hpmin : ∀ m, Valued.v (PowerSeries.coeff m f) * r ^ m = A → p ≤ m :=
    fun m hm => Nat.find_min' hexA hm
  have hqmin : ∀ m, Valued.v (PowerSeries.coeff m g) * r ^ m = B → q ≤ m :=
    fun m hm => Nat.find_min' hexB hm
  have hdom : ∀ i ∈ Finset.antidiagonal (p + q) \ {(p, q)},
      Valued.v (PowerSeries.coeff i.1 f * PowerSeries.coeff i.2 g)
        < Valued.v (PowerSeries.coeff p f * PowerSeries.coeff q g) := by
    intro i hi
    rw [Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_antidiagonal] at hi
    obtain ⟨hsum, hne⟩ := hi
    have hkey : Valued.v (PowerSeries.coeff i.1 f) * r ^ i.1
        * (Valued.v (PowerSeries.coeff i.2 g) * r ^ i.2) < A * B := by
      rcases lt_trichotomy i.1 p with hlt | heq | hgt
      · have h1 : Valued.v (PowerSeries.coeff i.1 f) * r ^ i.1 < A := by
          rcases lt_or_eq_of_le (hf.1 i.1) with h | h
          · exact h
          · exact absurd (hpmin i.1 h) (by omega)
        exact mul_lt_mul_of_lt_of_le' h1 (hg.1 i.2) hApos hBpos
      · exact absurd (Prod.ext heq (by omega)) hne
      · have h2 : Valued.v (PowerSeries.coeff i.2 g) * r ^ i.2 < B := by
          rcases lt_or_eq_of_le (hg.1 i.2) with h | h
          · exact h
          · exact absurd (hqmin i.2 h) (by omega)
        exact mul_lt_mul_of_le_of_lt' (hf.1 i.1) h2 hApos hBpos
    rw [Valuation.map_mul, Valuation.map_mul]
    refine lt_of_mul_lt_mul_right ?_ (zero_le : (0 : Γ₀) ≤ r ^ (p + q))
    calc Valued.v (PowerSeries.coeff i.1 f) * Valued.v (PowerSeries.coeff i.2 g) * r ^ (p + q)
        = Valued.v (PowerSeries.coeff i.1 f) * r ^ i.1
          * (Valued.v (PowerSeries.coeff i.2 g) * r ^ i.2) := by
          rw [← hsum, pow_add, mul_mul_mul_comm]
      _ < A * B := hkey
      _ = Valued.v (PowerSeries.coeff p f) * Valued.v (PowerSeries.coeff q g) * r ^ (p + q) := by
          rw [pow_add, mul_mul_mul_comm, hp, hq]
  refine ⟨fun n => ?_, ⟨p + q, ?_⟩⟩
  · have hsum : Valued.v (∑ i ∈ Finset.antidiagonal n,
        PowerSeries.coeff i.1 f * PowerSeries.coeff i.2 g) ≤ A * B * (r ^ n)⁻¹ := by
      refine Valuation.map_sum_le Valued.v (fun i hi => ?_)
      rw [← Finset.mem_antidiagonal.mp hi, Valuation.map_mul]
      have h1 : Valued.v (PowerSeries.coeff i.1 f) ≤ A * (r ^ i.1)⁻¹ :=
        (gauss_le_mul_inv_pow_iff hr i.1).mpr (hf.1 i.1)
      have h2 : Valued.v (PowerSeries.coeff i.2 g) ≤ B * (r ^ i.2)⁻¹ :=
        (gauss_le_mul_inv_pow_iff hr i.2).mpr (hg.1 i.2)
      calc Valued.v (PowerSeries.coeff i.1 f) * Valued.v (PowerSeries.coeff i.2 g)
          ≤ (A * (r ^ i.1)⁻¹) * (B * (r ^ i.2)⁻¹) := mul_le_mul h1 h2 zero_le zero_le
        _ = A * B * (r ^ (i.1 + i.2))⁻¹ := gauss_mul_inv_pow_mul_inv_pow A B r i.1 i.2
    rw [PowerSeries.coeff_mul]
    calc Valued.v (∑ i ∈ Finset.antidiagonal n,
          PowerSeries.coeff i.1 f * PowerSeries.coeff i.2 g) * r ^ n
        ≤ (A * B * (r ^ n)⁻¹) * r ^ n := mul_le_mul_left hsum (r ^ n)
      _ = A * B := by rw [mul_assoc (A * B), inv_mul_cancel₀ (pow_ne_zero n hr), mul_one]
  · rw [PowerSeries.coeff_mul]
    rw [Valuation.map_sum_eq_of_lt (Valued.v)
      (Finset.mem_antidiagonal.mpr rfl) hdom, Valuation.map_mul]
    rw [pow_add, mul_mul_mul_comm, hp, hq]

end mul

section linear

/-- The Gauss norm at radius `r` of the linear factor `X - C ω` (`1 ≤ r`, `v ω ≤ r`). -/
lemma isGaussNormAt_X_sub_C {r : Γ₀} (hr1 : 1 ≤ r) {ω : K} (hω : Valued.v ω ≤ r) :
    IsGaussNormAt r (PowerSeries.X - PowerSeries.C ω) r := by
  have hrne : r ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hr1)
  have hcoe : ∀ n : ℕ, PowerSeries.coeff n (PowerSeries.X - PowerSeries.C ω)
      = PowerSeries.coeff n (PowerSeries.X : PowerSeries K)
        - PowerSeries.coeff n (PowerSeries.C ω) :=
    fun n => map_sub (PowerSeries.coeff n) _ _
  have hX : ∀ n : ℕ,
      Valued.v (PowerSeries.coeff n (PowerSeries.X : PowerSeries K)) * r ^ n ≤ r := by
    intro n
    rw [PowerSeries.coeff_X]
    split_ifs with h
    · rw [h, Valued.v.map_one, pow_one, one_mul]
    · rw [map_zero (Valued.v), zero_mul]
      exact zero_le
  have hC : ∀ n : ℕ, Valued.v (PowerSeries.coeff n (PowerSeries.C ω)) * r ^ n ≤ r := by
    intro n
    rw [PowerSeries.coeff_C]
    split_ifs with h
    · rw [h, pow_zero, mul_one]
      exact hω
    · rw [map_zero (Valued.v), zero_mul]
      exact zero_le
  refine ⟨fun n => ?_, ⟨1, ?_⟩⟩
  · rw [hcoe n, ← gauss_le_mul_inv_pow_iff hrne n]
    refine le_trans (Valuation.map_sub Valued.v _ _) (max_le ?_ ?_)
    · exact (gauss_le_mul_inv_pow_iff hrne n).mpr (hX n)
    · exact (gauss_le_mul_inv_pow_iff hrne n).mpr (hC n)
  · rw [hcoe 1, PowerSeries.coeff_X, PowerSeries.coeff_C, if_pos rfl,
      if_neg (by omega : ¬ ((1 : ℕ) = 0)), sub_zero, Valued.v.map_one, pow_one, one_mul]

/-- The Gauss norm at radius `r` of a product of linear factors `∏ᵢ (X - C ωᵢ)`. -/
lemma isGaussNormAt_prod {ι : Type*} (s : Finset ι) (ω : ι → K) {r : Γ₀} (hr1 : 1 ≤ r)
    (hω : ∀ i ∈ s, Valued.v (ω i) ≤ r) :
    IsGaussNormAt r (∏ i ∈ s, (PowerSeries.X - PowerSeries.C (ω i))) (r ^ s.card) := by
  classical
  have hrne : r ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hr1)
  induction s using Finset.induction with
  | empty => simpa using isGaussNormAt_one r
  | insert a s ha ih =>
    have h1 : IsGaussNormAt r (PowerSeries.X - PowerSeries.C (ω a)) r :=
      isGaussNormAt_X_sub_C hr1 (hω a (Finset.mem_insert_self a s))
    have h2 : IsGaussNormAt r (∏ i ∈ s, (PowerSeries.X - PowerSeries.C (ω i))) (r ^ s.card) :=
      ih (fun i hi => hω i (Finset.mem_insert_of_mem hi))
    have hm := h1.mul hrne h2
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ, mul_comm (r ^ s.card) r]
    exact hm

/-- The coefficients of `∏ᵢ (X - C ωᵢ)` are bounded by `∏ᵢ v ωᵢ` whenever `v ωᵢ ≥ 1`. -/
lemma v_coeff_prod_X_sub_C_le_aux {ι : Type*} (s : Finset ι) (ω : ι → K) :
    (∀ i ∈ s, 1 ≤ Valued.v (ω i)) →
      ∀ k : ℕ, Valued.v (PowerSeries.coeff k (∏ i ∈ s, (PowerSeries.X - PowerSeries.C (ω i))))
        ≤ ∏ i ∈ s, Valued.v (ω i) := by
  classical
  induction s using Finset.induction with
  | empty =>
    intro _ k
    rw [Finset.prod_empty, PowerSeries.coeff_one]
    split_ifs with h
    · exact le_of_eq (map_one (Valued.v))
    · exact le_trans (le_of_eq (map_zero (Valued.v))) zero_le
  | insert a s ha ih =>
    intro hω k
    have hωa : 1 ≤ Valued.v (ω a) := hω a (Finset.mem_insert_self a s)
    have hs : ∀ i ∈ s, 1 ≤ Valued.v (ω i) := fun i hi => hω i (Finset.mem_insert_of_mem hi)
    have hcoeff : PowerSeries.coeff k ((PowerSeries.X - PowerSeries.C (ω a))
        * (∏ i ∈ s, (PowerSeries.X - PowerSeries.C (ω i))))
        = PowerSeries.coeff k (PowerSeries.X * (∏ i ∈ s, (PowerSeries.X - PowerSeries.C (ω i))))
          - PowerSeries.coeff k (PowerSeries.C (ω a)
            * (∏ i ∈ s, (PowerSeries.X - PowerSeries.C (ω i)))) := by
      rw [sub_mul]
      exact map_sub (PowerSeries.coeff k) _ _
    have hRs : ∏ i ∈ insert a s, Valued.v (ω i)
        = Valued.v (ω a) * ∏ i ∈ s, Valued.v (ω i) := Finset.prod_insert ha
    have hL : PowerSeries.coeff k (∏ i ∈ insert a s, (PowerSeries.X - PowerSeries.C (ω i)))
        = PowerSeries.coeff k ((PowerSeries.X - PowerSeries.C (ω a))
          * (∏ i ∈ s, (PowerSeries.X - PowerSeries.C (ω i)))) := by
      rw [Finset.prod_insert ha]
    rw [hRs, hL, hcoeff]
    refine le_trans (Valuation.map_sub Valued.v _ _) (max_le ?_ ?_)
    · rw [mul_comm, Commons.RingTheory.PowerSeries.coeff_mul_X]
      rcases eq_or_ne k 0 with rfl | hk
      · rw [if_neg (by omega : ¬ (1 ≤ 0)), map_zero (Valued.v)]
        exact zero_le
      · rw [if_pos (by omega : 1 ≤ k)]
        exact le_trans (ih hs (k - 1)) (le_mul_of_one_le_left zero_le hωa)
    · rw [PowerSeries.coeff_C_mul, Valuation.map_mul]
      exact mul_le_mul_right (ih hs k) (Valued.v (ω a))

/-- The coefficients of `∏ᵢ (X - C ωᵢ)` are bounded by `∏ᵢ v ωᵢ` whenever `v ωᵢ ≥ 1`. -/
lemma v_coeff_prod_X_sub_C_le {ι : Type*} (s : Finset ι) (ω : ι → K)
    (hω : ∀ i ∈ s, 1 ≤ Valued.v (ω i)) (k : ℕ) :
    Valued.v (PowerSeries.coeff k (∏ i ∈ s, (PowerSeries.X - PowerSeries.C (ω i))))
      ≤ ∏ i ∈ s, Valued.v (ω i) :=
  v_coeff_prod_X_sub_C_le_aux s ω hω k

end linear

section polynomial

/-- A nonzero polynomial, viewed as a power series, has a Gauss norm at every radius. -/
lemma exists_isGaussNormAt_polynomial {r : Γ₀} {p : Polynomial K} (hp : p ≠ 0) :
    ∃ A : Γ₀, IsGaussNormAt r (p : PowerSeries K) A := by
  classical
  have hne : p.support.Nonempty := Polynomial.support_nonempty.mpr hp
  refine ⟨p.support.sup (fun i => Valued.v (p.coeff i) * r ^ i), fun n => ?_, ?_⟩
  · by_cases hn : n ∈ p.support
    · rw [Polynomial.coeff_coe]
      exact Finset.le_sup (f := fun i => Valued.v (p.coeff i) * r ^ i) hn
    · rw [Polynomial.coeff_coe]
      rw [Polynomial.mem_support_iff, not_not] at hn
      rw [hn, map_zero (Valued.v), zero_mul]
      obtain ⟨i, hi⟩ := hne
      exact le_trans zero_le (Finset.le_sup (f := fun i => Valued.v (p.coeff i) * r ^ i) hi)
  · obtain ⟨i, hi, hsup⟩ :=
      Finset.exists_mem_eq_sup p.support hne (fun i => Valued.v (p.coeff i) * r ^ i)
    exact ⟨i, by rw [Polynomial.coeff_coe, hsup]⟩

/-- The coefficients of a polynomial of degree `≤ d` with coefficient bound `H` have
`v (pₙ) rⁿ ≤ H r^d`. -/
lemma coeff_coe_mul_pow_le {r H : Γ₀} {d : ℕ} {p : Polynomial K} (hr1 : 1 ≤ r)
    (hdeg : p.natDegree ≤ d) (hH : ∀ i, Valued.v (p.coeff i) ≤ H) (n : ℕ) :
    Valued.v (PowerSeries.coeff n (p : PowerSeries K)) * r ^ n ≤ H * r ^ d := by
  rw [Polynomial.coeff_coe]
  rcases lt_or_ge d n with hnd | hnd
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg hnd),
      map_zero (Valued.v), zero_mul]
    exact zero_le
  · calc Valued.v (p.coeff n) * r ^ n ≤ H * r ^ n := mul_le_mul_left (hH n) _
      _ ≤ H * r ^ d := mul_le_mul_right (pow_le_pow_right₀ hr1 hnd) H

end polynomial

section schwarz


/-- ★★★ **The Schwarz–Jensen inequality in coefficient form.**  If `E` factors as
`(∏ᵢ (X - C ωᵢ)) · G` with `G` having Gauss norm `B` at radius `r` and `1 ≤ v ωᵢ ≤ r`, then every
coefficient of `E` is bounded by `(∏ᵢ v ωᵢ) · B`. -/
theorem v_coeff_le_of_prod {r B : Γ₀} (hr1 : 1 ≤ r) {ι : Type*} {s : Finset ι} {ω : ι → K}
    (hω1 : ∀ i ∈ s, 1 ≤ Valued.v (ω i)) (_hω2 : ∀ i ∈ s, Valued.v (ω i) ≤ r)
    {E G : PowerSeries K}
    (hE : E = (∏ i ∈ s, (PowerSeries.X - PowerSeries.C (ω i))) * G)
    (hG : IsGaussNormAt r G B) (m : ℕ) :
    Valued.v (PowerSeries.coeff m E) ≤ (∏ i ∈ s, Valued.v (ω i)) * B := by
  classical
  rw [hE, PowerSeries.coeff_mul]
  refine Valuation.map_sum_le Valued.v (fun p hp => ?_)
  rw [Valuation.map_mul]
  refine mul_le_mul (v_coeff_prod_X_sub_C_le s ω hω1 p.1) ?_ zero_le zero_le
  calc Valued.v (PowerSeries.coeff p.2 G)
      ≤ Valued.v (PowerSeries.coeff p.2 G) * r ^ p.2 :=
        le_mul_of_one_le_right zero_le (one_le_pow₀ hr1)
    _ ≤ B := hG.1 p.2

/-- ★★★ **Schwarz–Jensen, Gauss-norm form.**  If `E = (∏ᵢ (X - C ωᵢ)) · G` with
`1 ≤ v ωᵢ ≤ r`, `G` having Gauss norm `B` and `A` the Gauss norm of `E` at radius `r`, then
`B = A · r^{-M}` and every coefficient of `E` is bounded by `(∏ᵢ v ωᵢ) · A · r^{-M}`. -/
theorem v_coeff_le_of_gaussNorm {r A B : Γ₀} (hr1 : 1 ≤ r) {ι : Type*} {s : Finset ι} {ω : ι → K}
    (hω1 : ∀ i ∈ s, 1 ≤ Valued.v (ω i)) (hω2 : ∀ i ∈ s, Valued.v (ω i) ≤ r)
    {E G : PowerSeries K} (hE : E = (∏ i ∈ s, (PowerSeries.X - PowerSeries.C (ω i))) * G)
    (hA : IsGaussNormAt r E A) (hG : IsGaussNormAt r G B) (m : ℕ) :
    Valued.v (PowerSeries.coeff m E) ≤ (∏ i ∈ s, Valued.v (ω i)) * A * (r ^ s.card)⁻¹ := by
  have hrne : r ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hr1)
  have hP : IsGaussNormAt r (∏ i ∈ s, (PowerSeries.X - PowerSeries.C (ω i))) (r ^ s.card) :=
    isGaussNormAt_prod s ω hr1 hω2
  have hPG : IsGaussNormAt r E (r ^ s.card * B) := by
    rw [hE]; exact hP.mul hrne hG
  have huniq : r ^ s.card * B = A := hPG.unique hA
  have hBsimp : r ^ s.card * B * (r ^ s.card)⁻¹ = B := by
    rw [mul_assoc, mul_comm B ((r ^ s.card)⁻¹), ← mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero _ hrne), one_mul]
  refine le_trans (v_coeff_le_of_prod hr1 hω1 hω2 hE hG m) ?_
  rw [← huniq, mul_assoc (∏ i ∈ s, Valued.v (ω i)) (r ^ s.card * B) (r ^ s.card)⁻¹, hBsimp]

end schwarz

end ZagierHoffmanPositiveChar
