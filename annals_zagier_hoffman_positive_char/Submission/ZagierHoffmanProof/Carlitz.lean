import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.FieldTheory.RatFunc.Basic

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Polynomial
open scoped BigOperators

/-!
# The Carlitz module over `A = F[X]`: factorials, brackets, exponential, logarithm

Let `F` be a finite field, `q = Nat.card F`, `A = F[X]` (the paper's `F_q[θ]`, with `θ = X`) and
`K = RatFunc F` (the paper's `F_q(θ)`).  This file starts the formalisation of the *Carlitz module*
machinery which underlies §4–§6 of Ngo Dac's paper (dual `t`-motives, Anderson–Thakur polynomials,
the Carlitz period).

Objects introduced here:

* `carlitzBracket k = X ^ (q ^ k) - X` — the paper's `[k]`;
* `carlitzFact k = ∏_{i < k} (X ^ (q ^ k) - X ^ (q ^ i))` — the Carlitz factorial `D_k`
  (also equal to `∏_{ℓ=1}^{k} [ℓ] ^ (q ^ (k - ℓ))`, the paper's definition);
* the recursion `D_{k+1} = [k+1] * D_k ^ q`, non-vanishing, monicity and the degree `k * q ^ k`;
* `carlitzExp` — the Carlitz exponential `∑_{n ≥ 0} z ^ (q ^ n) / D_n` (as a power series over `K`)
  together with its functional equation `e_C (θ z) = θ * e_C z + (e_C z) ^ q`;
* `carlitzLog` — the Carlitz logarithm `∑_{n ≥ 0} z ^ (q ^ n) / L_n`,
  `L_n = ∏_{i=1}^{n} (θ - θ ^ (q ^ i))`, with the functional equation `log_C (θ z + z ^ q) = θ * log_C z`.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

section CharP

/-- The cardinality of a finite field is a power of its characteristic. -/
lemma card_eq_ringChar_pow : ∃ n : ℕ, (ringChar F).Prime ∧ Nat.card F = (ringChar F) ^ n := by
  letI : Fintype F := Fintype.ofFinite F
  obtain ⟨n, hprime, hcard⟩ := FiniteField.card (K := F) (p := ringChar F)
  exact ⟨n, hprime, by rw [← Fintype.card_eq_nat_card, hcard]⟩

/-- The Freshman's dream for a finite field `F` acting on a ring of characteristic `ringChar F`:
`(x + y) ^ q = x ^ q + y ^ q`. -/
lemma carlitz_add_pow_card {S : Type*} [CommRing S] [CharP S (ringChar F)] (x y : S) :
    (x + y) ^ (Nat.card F) = x ^ (Nat.card F) + y ^ (Nat.card F) := by
  obtain ⟨n, hprime, hn⟩ := card_eq_ringChar_pow F
  haveI : Fact (Nat.Prime (ringChar F)) := ⟨hprime⟩
  rw [hn]
  exact add_pow_char_pow x y (ringChar F) n

/-- The subtraction form of the Freshman's dream. -/
lemma sub_pow_card {S : Type*} [CommRing S] [CharP S (ringChar F)] (x y : S) :
    (x - y) ^ (Nat.card F) = x ^ (Nat.card F) - y ^ (Nat.card F) := by
  obtain ⟨n, hprime, hn⟩ := card_eq_ringChar_pow F
  haveI : Fact (Nat.Prime (ringChar F)) := ⟨hprime⟩
  rw [hn]
  exact sub_pow_char_pow x y n

/-- A finite sum of `q`-th powers: `(∑ x) ^ q = ∑ x ^ q`. -/
lemma carlitz_sum_pow_card {S : Type*} [CommRing S] [CharP S (ringChar F)] {ι : Type*}
    (s : Finset ι) (f : ι → S) :
    (∑ i ∈ s, f i) ^ (Nat.card F) = ∑ i ∈ s, (f i) ^ (Nat.card F) := by
  classical
  induction s using Finset.induction with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty]
      exact zero_pow (Nat.card_pos (α := F)).ne'
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, carlitz_add_pow_card F, ih]

end CharP

end ZagierHoffmanPositiveChar
namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

section Factorial

/-- The paper's `[k] = θ ^ (q ^ k) - θ`, as a polynomial in `X = θ`.  Note `[0] = 0`. -/
noncomputable def carlitzBracket (k : ℕ) : F[X] := X ^ (Nat.card F ^ k) - X

/-- The Carlitz factorial `D_k = ∏_{i < k} (θ ^ (q ^ k) - θ ^ (q ^ i))` (`D_0 = 1`). -/
noncomputable def carlitzFact (k : ℕ) : F[X] :=
  ∏ i ∈ Finset.range k, (X ^ (Nat.card F ^ k) - X ^ (Nat.card F ^ i))

lemma one_lt_card : 1 < Nat.card F := by
  haveI : Fintype F := Fintype.ofFinite F
  rw [← Fintype.card_eq_nat_card]
  exact Fintype.one_lt_card

lemma carlitz_card_ge_two : 2 ≤ Nat.card F := by have h := one_lt_card F; omega

lemma pow_lt_pow_of_lt {i k : ℕ} (h : i < k) : Nat.card F ^ i < Nat.card F ^ k :=
  Nat.pow_lt_pow_right (one_lt_card F) h

lemma monic_X_pow_sub_X_pow {i k : ℕ} (h : i < k) :
    (X ^ (Nat.card F ^ k) - X ^ (Nat.card F ^ i) : F[X]).Monic := by
  refine Monic.sub_of_left (monic_X_pow _) ?_
  rw [degree_X_pow, degree_X_pow]
  exact_mod_cast pow_lt_pow_of_lt F h

lemma monic_carlitzBracket {k : ℕ} (hk : 1 ≤ k) : (carlitzBracket F k).Monic := by
  have h : 0 < k := hk
  have : (X ^ (Nat.card F ^ k) - X ^ 1 : F[X]).Monic :=
    monic_X_pow_sub_X_pow F (i := 0) (k := k) h
  simpa [carlitzBracket, pow_one] using this

lemma carlitzBracket_ne_zero {k : ℕ} (hk : 1 ≤ k) : carlitzBracket F k ≠ 0 :=
  (monic_carlitzBracket F hk).ne_zero

@[simp]
lemma carlitzFact_zero : carlitzFact F 0 = 1 := by simp [carlitzFact]

lemma carlitzFact_monic (k : ℕ) : (carlitzFact F k).Monic := by
  refine monic_prod_of_monic _ _ ?_
  intro i hi
  rw [Finset.mem_range] at hi
  exact monic_X_pow_sub_X_pow F hi

lemma carlitzFact_ne_zero (k : ℕ) : carlitzFact F k ≠ 0 :=
  (carlitzFact_monic F k).ne_zero

lemma natDegree_carlitzFact (k : ℕ) :
    (carlitzFact F k).natDegree = k * Nat.card F ^ k := by
  rw [carlitzFact,
    natDegree_prod _ _ (fun i hi => (monic_X_pow_sub_X_pow F (Finset.mem_range.mp hi)).ne_zero)]
  rw [Finset.sum_congr rfl (fun i hi => ?_), Finset.sum_const, Finset.card_range,
    smul_eq_mul]
  rw [natDegree_sub_eq_left_of_natDegree_lt (p := X ^ (Nat.card F ^ k))
        (q := X ^ (Nat.card F ^ i)) ?_, natDegree_X_pow]
  rw [natDegree_X_pow, natDegree_X_pow]
  exact pow_lt_pow_of_lt F (Finset.mem_range.mp hi)

/-- The recursion `D_{k+1} = D_k ^ q * [k+1]`. -/
lemma carlitzFact_succ (k : ℕ) :
    carlitzFact F (k + 1) = (carlitzFact F k) ^ (Nat.card F) * carlitzBracket F (k + 1) := by
  have hpow : ∀ i : ℕ, (X ^ (Nat.card F ^ k) - X ^ (Nat.card F ^ i) : F[X]) ^ (Nat.card F)
      = X ^ (Nat.card F ^ (k + 1)) - X ^ (Nat.card F ^ (i + 1)) := by
    intro i
    rw [sub_pow_card F]
    congr 1 <;> rw [← pow_mul, ← pow_succ]
  simp only [carlitzFact, carlitzBracket]
  rw [Finset.prod_range_succ', ← Finset.prod_pow]
  congr 1
  · refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [hpow i]
  · rw [pow_zero, pow_one]

/-- `D_k = ∏_{ℓ=1}^{k} [ℓ] ^ (q ^ (k - ℓ))` (the paper's definition of the Carlitz factorial). -/
lemma carlitzFact_eq_prod_bracket (k : ℕ) :
    carlitzFact F k
      = ∏ l ∈ Finset.Icc 1 k, (carlitzBracket F l) ^ (Nat.card F ^ (k - l)) := by
  induction k with
  | zero => simp [Finset.Icc_eq_empty_of_lt (by omega : 0 < 1)]
  | succ k ih =>
      rw [carlitzFact_succ, ih, ← Finset.prod_pow]
      rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ k + 1)]
      congr 1
      · refine Finset.prod_congr rfl (fun l hl => ?_)
        rw [Finset.mem_Icc] at hl
        have hexp : Nat.card F ^ (k - l) * Nat.card F = Nat.card F ^ (k + 1 - l) := by
          rw [← pow_succ]
          congr 1
          omega
        rw [← pow_mul, hexp]
      · rw [Nat.sub_self, pow_zero, pow_one]

end Factorial

end ZagierHoffmanPositiveChar
namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

section Gamma

/-- The arithmetic `Γ`-function of Carlitz: `Γ n = ∏_j D_j ^ (n_j)` where
`n - 1 = ∑_j n_j q ^ j` is the base-`q` expansion of `n - 1`.  (Indexing as in the paper:
`Γ_1 = 1`.) -/
noncomputable def carlitzGamma (n : ℕ) : F[X] :=
  ∏ j ∈ Finset.range n, (carlitzFact F j) ^ ((n - 1) / (Nat.card F ^ j) % Nat.card F)

@[simp]
lemma carlitzGamma_one : carlitzGamma F 1 = 1 := by
  simp [carlitzGamma]

lemma carlitzGamma_ne_zero (n : ℕ) : carlitzGamma F n ≠ 0 := by
  rw [carlitzGamma]
  exact Finset.prod_ne_zero_iff.mpr (fun j _ => pow_ne_zero _ (carlitzFact_ne_zero F j))

lemma carlitzGamma_monic (n : ℕ) : (carlitzGamma F n).Monic := by
  rw [carlitzGamma]
  exact monic_prod_of_monic _ _ (fun j _ => (carlitzFact_monic F j).pow _)

end Gamma

section Log

/-- The denominators `L_i = ∏_{j=1}^{i} (θ - θ ^ (q ^ j))` of the coefficients `1 / L_i` of the
*Carlitz logarithm* `log_C(z) = ∑_{i ≥ 0} z ^ (q ^ i) / L_i`. -/
noncomputable def carlitzL (i : ℕ) : F[X] :=
  ∏ j ∈ Finset.range i, (X - X ^ (Nat.card F ^ (j + 1)))

@[simp]
lemma carlitzL_zero : carlitzL F 0 = 1 := by simp [carlitzL]

lemma carlitzL_succ (i : ℕ) :
    carlitzL F (i + 1) = carlitzL F i * (X - X ^ (Nat.card F ^ (i + 1))) := by
  rw [carlitzL, Finset.prod_range_succ, carlitzL]

lemma carlitzL_eq_prod_neg (i : ℕ) :
    carlitzL F i = ∏ j ∈ Finset.range i, (-(carlitzBracket F (j + 1))) := by
  rw [carlitzL]
  exact Finset.prod_congr rfl (fun j _ => by rw [carlitzBracket, neg_sub])

lemma carlitzL_ne_zero (i : ℕ) : carlitzL F i ≠ 0 := by
  rw [carlitzL_eq_prod_neg]
  exact Finset.prod_ne_zero_iff.mpr
    (fun j _ => neg_ne_zero.mpr (carlitzBracket_ne_zero F (by omega : 1 ≤ j + 1)))

/-- `L_d = (-1) ^ d * ∏_{j=1}^{d} [j]`.  Since the depth-one power sum of the paper satisfies
`P_d(1) = ∏_{j=1}^{d} [j] ^ (-1)`, this exhibits the Carlitz logarithm's coefficients as
(up to sign) the inverse power sums. -/
lemma carlitzL_eq_neg_pow_mul (d : ℕ) :
    carlitzL F d = (-1) ^ d * ∏ j ∈ Finset.range d, carlitzBracket F (j + 1) := by
  rw [carlitzL_eq_prod_neg, Finset.prod_neg, Finset.card_range]

end Log

end ZagierHoffmanPositiveChar
namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

section Exp

/-! ### The Carlitz exponential

`e_C(z) = ∑_{n ≥ 0} z ^ (q ^ n) / D_n ∈ K⟦z⟧`, `K = RatFunc F`, with the functional equation
`e_C(θ z) = θ e_C(z) + e_C(z) ^ q` defining the Carlitz module `C_θ(z) = θ z + z ^ q`. -/

/-- The `θ` of the Carlitz module: the variable of `K = RatFunc F`. -/
noncomputable def carlitzTheta : RatFunc F := (X : F[X])

lemma carlitz_coe_mul (p q : F[X]) :
    ((p * q : F[X]) : RatFunc F) = (p : RatFunc F) * (q : RatFunc F) :=
  map_mul (algebraMap F[X] (RatFunc F)) p q

lemma carlitz_coe_pow (p : F[X]) (n : ℕ) :
    ((p ^ n : F[X]) : RatFunc F) = (p : RatFunc F) ^ n :=
  map_pow (algebraMap F[X] (RatFunc F)) p n

lemma carlitz_coe_sub (p q : F[X]) :
    ((p - q : F[X]) : RatFunc F) = (p : RatFunc F) - (q : RatFunc F) :=
  map_sub (algebraMap F[X] (RatFunc F)) p q

lemma carlitz_coe_X : ((X : F[X]) : RatFunc F) = carlitzTheta F := rfl

/-- The coefficient sequence of the Carlitz exponential: `1 / D_i` at `q ^ i` and `0` elsewhere. -/
noncomputable def carlitzECoeff (n : ℕ) : RatFunc F := by
  classical
  exact if h : ∃ i, n = Nat.card F ^ i then
    (((carlitzFact F h.choose : F[X]) : RatFunc F))⁻¹ else 0

lemma carlitzECoeff_pow (i : ℕ) :
    carlitzECoeff F (Nat.card F ^ i) = (((carlitzFact F i : F[X]) : RatFunc F))⁻¹ := by
  classical
  have hex : ∃ j, Nat.card F ^ i = Nat.card F ^ j := ⟨i, rfl⟩
  unfold carlitzECoeff
  rw [dif_pos hex]
  rw [show hex.choose = i from
    Nat.pow_right_injective (carlitz_card_ge_two F) (Classical.choose_spec hex).symm]

lemma carlitzECoeff_eq_zero {n : ℕ} (h : ∀ i, n ≠ Nat.card F ^ i) : carlitzECoeff F n = 0 := by
  unfold carlitzECoeff
  rw [dif_neg (fun hh => h hh.choose hh.choose_spec)]

lemma carlitzFact_coe_ne_zero (i : ℕ) : (((carlitzFact F i : F[X]) : RatFunc F)) ≠ 0 :=
  (map_ne_zero_iff (algebraMap F[X] (RatFunc F)) (RatFunc.algebraMap_injective F)).mpr
    (carlitzFact_ne_zero F i)

lemma carlitzFact_rec_coe (i : ℕ) :
    (((carlitzFact F (i + 1) : F[X]) : RatFunc F))
      = (((carlitzFact F i : F[X]) : RatFunc F)) ^ (Nat.card F)
        * (((carlitzBracket F (i + 1) : F[X]) : RatFunc F)) := by
  rw [carlitzFact_succ, carlitz_coe_mul, carlitz_coe_pow]

lemma carlitzTheta_pow {i : ℕ} (hi : 1 ≤ i) :
    (carlitzTheta F) ^ (Nat.card F ^ i)
      = carlitzTheta F + (((carlitzBracket F i : F[X]) : RatFunc F)) := by
  have h1 : carlitzTheta F = ((X : F[X]) : RatFunc F) := rfl
  have h2 : (((carlitzBracket F i : F[X]) : RatFunc F))
      = (((X : F[X]) ^ (Nat.card F ^ i) : F[X]) : RatFunc F) - ((X : F[X]) : RatFunc F) := by
    rw [carlitzBracket]
    exact map_sub (algebraMap F[X] (RatFunc F)) (X ^ (Nat.card F ^ i)) X
  have h3 : ((X : F[X]) : RatFunc F) ^ (Nat.card F ^ i)
      = (((X : F[X]) ^ (Nat.card F ^ i) : F[X]) : RatFunc F) :=
    (map_pow (algebraMap F[X] (RatFunc F)) (X : F[X]) (Nat.card F ^ i)).symm
  rw [h1, h3, h2]
  ring

/-- The coefficient identity behind the functional equation of the Carlitz exponential:
`θ ^ (q ^ i) / D_i = θ / D_i + 1 / D_{i-1} ^ q`. -/
lemma carlitzECoeff_rec {i : ℕ} (hi : 1 ≤ i) :
    (carlitzTheta F) ^ (Nat.card F ^ i) * ((((carlitzFact F i : F[X]) : RatFunc F)))⁻¹
      = carlitzTheta F * ((((carlitzFact F i : F[X]) : RatFunc F)))⁻¹
        + ((((carlitzFact F (i - 1) : F[X]) : RatFunc F)) ^ (Nat.card F))⁻¹ := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  rw [show j + 1 - 1 = j from rfl, carlitzFact_rec_coe F j, mul_inv, ← inv_pow]
  have hA : (((carlitzFact F j : F[X]) : RatFunc F)) ≠ 0 := carlitzFact_coe_ne_zero F j
  have hB : (((carlitzBracket F (j + 1) : F[X]) : RatFunc F)) ≠ 0 :=
    (map_ne_zero_iff (algebraMap F[X] (RatFunc F)) (RatFunc.algebraMap_injective F)).mpr
      (carlitzBracket_ne_zero F (by omega : 1 ≤ j + 1))
  have hAq : (((carlitzFact F j : F[X]) : RatFunc F)) ^ (Nat.card F) ≠ 0 := pow_ne_zero _ hA
  rw [carlitzTheta_pow F (by omega : 1 ≤ j + 1)]
  field_simp

/-- The Carlitz exponential `e_C(z) = ∑_{n ≥ 0} z ^ (q ^ n) / D_n`, as a power series over `K`. -/
noncomputable def carlitzExp : PowerSeries (RatFunc F) := PowerSeries.mk (carlitzECoeff F)

end Exp

end ZagierHoffmanPositiveChar
namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

section ExpFrob

/-- The `q`-th power of a power series over a field of characteristic `p` (with `q = p ^ e`):
the Frobenius map raises the coefficients to the `q`-th power and multiplies the exponents. -/
lemma mk_pow_card_general {R : Type*} [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]
    (e : ℕ) (c : ℕ → R) :
    (PowerSeries.mk c) ^ p ^ e
      = PowerSeries.mk (fun n => if p ^ e ∣ n then (c (n / p ^ e)) ^ (p ^ e) else 0) := by
  rw [show (PowerSeries.mk c) ^ p ^ e
      = PowerSeries.map (iterateFrobenius R p e)
          ((PowerSeries.expand (p ^ e) (pow_ne_zero e (Fact.out : p.Prime).pos.ne')) (PowerSeries.mk c))
      from (MvPowerSeries.map_iterateFrobenius_expand (σ := Unit) p (Fact.out : p.Prime).pos.ne'
        (PowerSeries.mk c) e).symm]
  congr 1
  rw [show (PowerSeries.expand (p ^ e) (pow_ne_zero e (Fact.out : p.Prime).pos.ne'))
        (PowerSeries.mk c)
      = PowerSeries.mk (fun n => if p ^ e ∣ n then c (n / p ^ e) else 0) from by
    ext n
    rw [PowerSeries.coeff_expand, PowerSeries.coeff_mk, PowerSeries.coeff_mk]]
  ext n
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  split_ifs with h
  · rw [iterateFrobenius_def]
  · rw [map_zero]

/-- The `q`-th power of a power series over `RatFunc F`. -/
lemma mk_pow_card (c : ℕ → RatFunc F) :
    (PowerSeries.mk c) ^ (Nat.card F)
      = PowerSeries.mk (fun n =>
          if Nat.card F ∣ n then (c (n / Nat.card F)) ^ (Nat.card F) else 0) := by
  obtain ⟨e, hprime, hcard⟩ := card_eq_ringChar_pow F
  haveI : Fact (Nat.Prime (ringChar F)) := ⟨hprime⟩
  rw [hcard]
  exact mk_pow_card_general (ringChar F) e c

end ExpFrob

section ExpFunctional

open PowerSeries

/-- **The functional equation of the Carlitz exponential**: `e_C(θ z) = θ · e_C(z) + e_C(z) ^ q`. -/
theorem carlitzExp_functional :
    PowerSeries.rescale (carlitzTheta F) (carlitzExp F)
      = PowerSeries.C (carlitzTheta F) * carlitzExp F + (carlitzExp F) ^ (Nat.card F) := by
  rw [carlitzExp, mk_pow_card F (carlitzECoeff F)]
  ext n
  rw [PowerSeries.coeff_rescale, map_add, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  by_cases hn : ∃ i, n = Nat.card F ^ i
  · obtain ⟨i, rfl⟩ := hn
    rw [carlitzECoeff_pow F i]
    rcases Nat.eq_zero_or_pos i with hi | hi
    · subst hi
      rw [pow_zero, pow_one]
      have hnot : ¬ Nat.card F ∣ 1 := by
        intro hd
        have h1 := Nat.le_of_dvd (by omega) hd
        have h2 := carlitz_card_ge_two F
        omega
      rw [show (1 : ℕ) / Nat.card F = 0 from Nat.div_eq_of_lt (one_lt_card F), if_neg hnot]
      ring
    · have hdiv : Nat.card F ∣ Nat.card F ^ i := ⟨Nat.card F ^ (i - 1), by
        rw [mul_comm, ← pow_succ]
        congr 1
        omega⟩
      have hdiv' : Nat.card F ^ i / Nat.card F = Nat.card F ^ (i - 1) := by
        obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
        rw [show j + 1 - 1 = j from rfl, pow_succ]
        exact Nat.mul_div_cancel _ (by have := carlitz_card_ge_two F; omega : 0 < Nat.card F)
      rw [if_pos hdiv, hdiv', carlitzECoeff_pow F (i - 1), inv_pow]
      exact carlitzECoeff_rec F hi
  · rw [not_exists] at hn
    rw [carlitzECoeff_eq_zero F hn]
    have hz : (if Nat.card F ∣ n then (carlitzECoeff F (n / Nat.card F)) ^ (Nat.card F) else 0)
        = 0 := by
      by_cases hd : Nat.card F ∣ n
      · rw [if_pos hd]
        obtain ⟨m, hm⟩ := hd
        have h1 : n / Nat.card F = m := by
          rw [hm, Nat.mul_div_cancel_left _ (by have := carlitz_card_ge_two F; omega)]
        have h2 : carlitzECoeff F m = 0 := carlitzECoeff_eq_zero F (fun j hj => hn (j + 1) (by
          rw [hm, hj, mul_comm, ← pow_succ]))
        rw [h1, h2]
        exact zero_pow (by have := carlitz_card_ge_two F; omega : Nat.card F ≠ 0)
      · rw [if_neg hd]
    rw [hz]
    ring

end ExpFunctional

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

section Twisted

open PowerSeries

/-- The Carlitz functional equation holds for every *scaled* Carlitz exponential `e_C(a z)`:
`e_C(θ a z) = θ e_C(a z) + e_C(a z) ^ q` for every `a ∈ K`.  (The general form of
`carlitzExp_functional`, which is the case `a = 1`.) -/
theorem carlitzExp_rescale_functional (a : RatFunc F) :
    PowerSeries.rescale (carlitzTheta F) (PowerSeries.rescale a (carlitzExp F))
      = PowerSeries.C (carlitzTheta F) * PowerSeries.rescale a (carlitzExp F)
        + (PowerSeries.rescale a (carlitzExp F)) ^ (Nat.card F) := by
  rw [carlitzExp, PowerSeries.rescale_mk,
    mk_pow_card F (fun n => a ^ n * carlitzECoeff F n)]
  ext n
  rw [PowerSeries.coeff_rescale, map_add, PowerSeries.coeff_C_mul]
  simp only [PowerSeries.coeff_mk]
  by_cases hn : ∃ i, n = Nat.card F ^ i
  · obtain ⟨i, rfl⟩ := hn
    rw [carlitzECoeff_pow F i]
    rcases Nat.eq_zero_or_pos i with hi | hi
    · subst hi
      rw [pow_zero, pow_one]
      have hnot : ¬ Nat.card F ∣ 1 := by
        intro hd
        have h1 := Nat.le_of_dvd (by omega) hd
        have h2 := carlitz_card_ge_two F
        omega
      rw [show (1 : ℕ) / Nat.card F = 0 from Nat.div_eq_of_lt (one_lt_card F), if_neg hnot]
      ring
    · have hdiv : Nat.card F ∣ Nat.card F ^ i := ⟨Nat.card F ^ (i - 1), by
        rw [mul_comm, ← pow_succ]
        congr 1
        omega⟩
      have hdiv' : Nat.card F ^ i / Nat.card F = Nat.card F ^ (i - 1) := by
        obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
        rw [show j + 1 - 1 = j from rfl, pow_succ]
        exact Nat.mul_div_cancel _ (by have := carlitz_card_ge_two F; omega : 0 < Nat.card F)
      rw [if_pos hdiv, hdiv', carlitzECoeff_pow F (i - 1), mul_pow, ← pow_mul]
      rw [show Nat.card F ^ (i - 1) * Nat.card F = Nat.card F ^ i from by
        rw [← pow_succ]; congr 1; omega]
      rw [inv_pow]
      have hkey := congrArg (fun x => x * a ^ (Nat.card F ^ i)) (carlitzECoeff_rec F hi)
      ring_nf at hkey ⊢
      exact hkey
  · rw [not_exists] at hn
    rw [carlitzECoeff_eq_zero F hn]
    have hz : (if Nat.card F ∣ n
        then (a ^ (n / Nat.card F) * carlitzECoeff F (n / Nat.card F)) ^ (Nat.card F)
        else 0) = 0 := by
      by_cases hd : Nat.card F ∣ n
      · rw [if_pos hd]
        obtain ⟨m, hm⟩ := hd
        have h1 : n / Nat.card F = m := by
          rw [hm, Nat.mul_div_cancel_left _ (by have := carlitz_card_ge_two F; omega)]
        have h2 : carlitzECoeff F m = 0 := carlitzECoeff_eq_zero F (fun j hj => hn (j + 1) (by
          rw [hm, hj, mul_comm, ← pow_succ]))
        rw [h1, h2, mul_zero]
        exact zero_pow (by have := carlitz_card_ge_two F; omega : Nat.card F ≠ 0)
      · rw [if_neg hd]
    rw [hz]
    ring

end Twisted

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

section Action

open PowerSeries

/-- The `n`-fold iterate of the Carlitz module `C_θ(z) = θ z + z ^ q` applied to a power series:
`carlitzAction 0 f = f` and `carlitzAction (n+1) f = θ * carlitzAction n f + (carlitzAction n f) ^ q`.
This is the Carlitz module action of `θ ^ n ∈ A` on `f`. -/
noncomputable def carlitzAction : ℕ → PowerSeries (RatFunc F) → PowerSeries (RatFunc F)
  | 0, f => f
  | n + 1, f => PowerSeries.C (carlitzTheta F) * carlitzAction n f
      + (carlitzAction n f) ^ (Nat.card F)

lemma carlitzAction_zero (f : PowerSeries (RatFunc F)) : carlitzAction F 0 f = f := rfl

lemma carlitzAction_succ (n : ℕ) (f : PowerSeries (RatFunc F)) :
    carlitzAction F (n + 1) f
      = PowerSeries.C (carlitzTheta F) * carlitzAction F n f
        + (carlitzAction F n f) ^ (Nat.card F) := rfl

/-- ★★ **The Carlitz exponential uniformizes the Carlitz module**:
`C_{θ ^ n}(e_C(z)) = e_C(θ ^ n · z)` for every `n`. -/
theorem carlitzAction_exp (n : ℕ) :
    carlitzAction F n (carlitzExp F)
      = PowerSeries.rescale ((carlitzTheta F) ^ n) (carlitzExp F) := by
  induction n with
  | zero => rw [carlitzAction_zero, pow_zero, PowerSeries.rescale_one]; rfl
  | succ n ih =>
      rw [carlitzAction_succ, ih, pow_succ, ← PowerSeries.rescale_rescale]
      exact (carlitzExp_rescale_functional F ((carlitzTheta F) ^ n)).symm

/-- The same statement, in the form `e_C(θ ^ n z) = C_{θ ^ n}(e_C(z))`. -/
theorem carlitzExp_theta_pow (n : ℕ) :
    PowerSeries.rescale ((carlitzTheta F) ^ n) (carlitzExp F)
      = carlitzAction F n (carlitzExp F) :=
  (carlitzAction_exp F n).symm

end Action

end ZagierHoffmanPositiveChar
