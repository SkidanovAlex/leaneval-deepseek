import Submission.ZagierHoffmanProof.Entire
import Submission.ZagierHoffmanProof.Valuation
import Submission.ZagierHoffmanProof.EntireTwist
import Submission.ZagierHoffmanProof.Carlitz
import Submission.ZagierHoffmanProof.CarlitzLog

/-!
# The Carlitz exponential and logarithm as entire functions

The coefficient field of the paper's analytic chapter is `K∞ = F((1/t))`
(`RatFunc.CompletionAtInfty F`), in which `F(t)` sits via the natural map.  Pushing the
power series `e_C` and `log_C` (built in `Carlitz.lean`/`CarlitzLog.lean` over `F(t)`)
through this map yields power series over `K∞`, and we prove that they are *entire* in the
sense of `Entire.lean`:

* `entire_carlitzExp : Entire (seriesToK F (carlitzExp F))`
* `entire_carlitzLog : Entire (seriesToK F (carlitzLog F))`

Both are the convergence-everywhere statements for the Carlitz exponential/logarithm, i.e.
the first examples of elements of the ring `E` of the Anderson–Brownawell–Papanikolas
criterion, which is the analytic substrate of §4 of Ngo Dac's paper.

## Main definitions

* `seriesToK F` — the ring hom `F(t)⟦z⟧ → K∞⟦z⟧` induced by `F(t) → K∞`.

## Main results

* `v_algebraMap_inv_poly` — valuation of `1/p` inside `K∞` for a nonzero polynomial `p`.
* `natDegree_carlitzL` — `deg L_i = ∑_{j<i} q^{j+1}`.
* `entire_carlitzExp`, `entire_carlitzLog`.
-/

set_option autoImplicit false

open Filter Polynomial RatFunc
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- A power series over `F(t)`, viewed over the completion `K∞ = F((1/t))`. -/
noncomputable def seriesToK : PowerSeries (RatFunc F) →+* PowerSeries (RatFunc.CompletionAtInfty F) :=
  PowerSeries.map (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F))

lemma seriesToK_coeff (f : PowerSeries (RatFunc F)) (n : ℕ) :
    PowerSeries.coeff n (seriesToK F f)
      = algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F) (PowerSeries.coeff n f) :=
  PowerSeries.coeff_map _ _ _

section vals

/-- The cardinality of a finite field is at least two. -/
lemma two_le_card : 2 ≤ Nat.card F := by
  haveI : Fintype F := Fintype.ofFinite F
  have h := Fintype.one_lt_card (α := F)
  rw [Nat.card_eq_fintype_card]
  omega

/-- The degree of the bracket `[k] = θ^{q^k} - θ`. -/
lemma natDegree_carlitzBracket {k : ℕ} (hk : 1 ≤ k) :
    (carlitzBracket F k).natDegree = Nat.card F ^ k := by
  rw [carlitzBracket, natDegree_sub_eq_left_of_natDegree_lt
    (p := Polynomial.X ^ (Nat.card F ^ k)) (q := Polynomial.X) ?_]
  · rw [natDegree_X_pow]
  · rw [natDegree_X_pow, natDegree_X]
    exact one_lt_pow₀ (by have := two_le_card F; omega) (by omega : k ≠ 0)

/-- The polynomial `θ - θ^{q^{j+1}}` is nonzero. -/
lemma carlitzBracketPoly_ne_zero (j : ℕ) :
    (Polynomial.X - Polynomial.X ^ (Nat.card F ^ (j + 1)) : F[X]) ≠ 0 := by
  have h : (Polynomial.X - Polynomial.X ^ (Nat.card F ^ (j + 1)) : F[X])
      = -(carlitzBracket F (j + 1)) := by
    rw [carlitzBracket]; ring
  rw [h]
  exact neg_ne_zero.mpr (carlitzBracket_ne_zero F (by omega))

/-- The degree of `θ - θ^{q^{j+1}}`. -/
lemma natDegree_carlitzBracketPoly (j : ℕ) :
    (Polynomial.X - Polynomial.X ^ (Nat.card F ^ (j + 1)) : F[X]).natDegree
      = Nat.card F ^ (j + 1) := by
  have h : (Polynomial.X - Polynomial.X ^ (Nat.card F ^ (j + 1)) : F[X])
      = -(carlitzBracket F (j + 1)) := by
    rw [carlitzBracket]; ring
  rw [h, Polynomial.natDegree_neg, natDegree_carlitzBracket F (by omega)]

/-- The valuation of the inverse of (the image of) a nonzero polynomial inside `K∞`. -/
lemma v_algebraMap_inv_poly (p : F[X]) (hp : p ≠ 0) :
    Valued.v (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F) ((p : RatFunc F))⁻¹)
      = WithZero.exp (-(p.natDegree : ℤ)) := by
  have hcoe : algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F) ((p : RatFunc F))
      = ((p : RatFunc F) : RatFunc.CompletionAtInfty F) := rfl
  rw [map_inv₀, Valuation.map_inv, hcoe, inftyValued_v_polynomial F p hp,
    ← WithZero.exp_neg]

/-- The valuation of the coefficient `1/D_i` of the Carlitz exponential. -/
lemma v_algebraMap_carlitzFact_inv (i : ℕ) :
    Valued.v (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F)
        (((carlitzFact F i : F[X]) : RatFunc F))⁻¹)
      = WithZero.exp (-(((i * Nat.card F ^ i : ℕ)) : ℤ)) := by
  rw [v_algebraMap_inv_poly F _ (carlitzFact_ne_zero F i), natDegree_carlitzFact]

/-- The degree of `L_i = ∏_{j=1}^{i}(θ - θ^{q^j})`. -/
lemma natDegree_carlitzL (i : ℕ) :
    (carlitzL F i).natDegree = ∑ j ∈ Finset.range i, Nat.card F ^ (j + 1) := by
  rw [carlitzL, natDegree_prod _ _ (fun j _ => carlitzBracketPoly_ne_zero F j)]
  exact Finset.sum_congr rfl (fun j _ => natDegree_carlitzBracketPoly F j)

end vals



/-- The Carlitz exponential, viewed as a power series over `K∞`, is entire. -/
theorem entire_carlitzExp : Entire (seriesToK F (carlitzExp F)) := by
  have hq : 1 < Nat.card F := by have := two_le_card F; omega
  refine Entire.of_nat (fun N => ?_)
  refine Filter.eventually_atTop.mpr ⟨Nat.card F ^ (N + 1), fun n hn => ?_⟩
  rw [seriesToK_coeff]
  by_cases h : ∃ i, n = Nat.card F ^ i
  · obtain ⟨i, hi⟩ := h
    subst hi
    have hi1 : N + 1 ≤ i := by
      by_contra hlt
      rw [Nat.not_le] at hlt
      exact absurd hn (not_le.mpr (Nat.pow_lt_pow_right hq hlt))
    rw [show PowerSeries.coeff (Nat.card F ^ i) (carlitzExp F)
        = carlitzECoeff F (Nat.card F ^ i) from PowerSeries.coeff_mk _ _,
      carlitzECoeff_pow F i, v_algebraMap_carlitzFact_inv F i, WithZero.exp_lt_exp]
    have hqi1 : 1 ≤ Nat.card F ^ i := Nat.one_le_pow i (Nat.card F) (by omega)
    have hnat : N < i * Nat.card F ^ i := by nlinarith [hi1, hqi1]
    have : (N : ℤ) < ((i * Nat.card F ^ i : ℕ) : ℤ) := by exact_mod_cast hnat
    omega
  · rw [show PowerSeries.coeff n (carlitzExp F) = carlitzECoeff F n from
        PowerSeries.coeff_mk _ _,
      carlitzECoeff_eq_zero F (fun i hi => h ⟨i, hi⟩),
      map_zero (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F)), Valuation.map_zero]
    exact lt_of_le_of_ne bot_le (fun hh => WithZero.exp_ne_zero hh.symm)

/-- The Carlitz logarithm, viewed as a power series over `K∞`, is entire. -/
theorem entire_carlitzLog : Entire (seriesToK F (carlitzLog F)) := by
  have hq : 1 < Nat.card F := by have := two_le_card F; omega
  refine Entire.of_nat (fun N => ?_)
  refine Filter.eventually_atTop.mpr ⟨Nat.card F ^ (N + 1), fun n hn => ?_⟩
  rw [seriesToK_coeff]
  by_cases h : ∃ i, n = Nat.card F ^ i
  · obtain ⟨i, hi⟩ := h
    subst hi
    have hi1 : N + 1 ≤ i := by
      by_contra hlt
      rw [Nat.not_le] at hlt
      exact absurd hn (not_le.mpr (Nat.pow_lt_pow_right hq hlt))
    rw [show PowerSeries.coeff (Nat.card F ^ i) (carlitzLog F)
        = carlitzLCoeff F (Nat.card F ^ i) from carlitzLog_coeff F _,
      carlitzLCoeff_pow F i,
      v_algebraMap_inv_poly F _ (carlitzL_ne_zero F i), natDegree_carlitzL F i,
      WithZero.exp_lt_exp]
    have hsum : Nat.card F ^ i ≤ ∑ j ∈ Finset.range i, Nat.card F ^ (j + 1) := by
      rcases Nat.eq_zero_or_pos i with h0 | h0
      · subst h0; exfalso; omega
      · have hmem : i - 1 ∈ Finset.range i := Finset.mem_range.mpr (by omega)
        have hterm : Nat.card F ^ i = Nat.card F ^ (i - 1 + 1) := by rw [Nat.sub_add_cancel h0]
        rw [hterm]
        exact Finset.single_le_sum (f := fun j => Nat.card F ^ (j + 1))
          (fun j _ => Nat.zero_le _) hmem
    have hself : i < Nat.card F ^ i := Nat.lt_pow_self hq
    have hnat : N < ∑ j ∈ Finset.range i, Nat.card F ^ (j + 1) := by omega
    have : (N : ℤ) < ((∑ j ∈ Finset.range i, Nat.card F ^ (j + 1) : ℕ) : ℤ) := by
      exact_mod_cast hnat
    omega
  · rw [show PowerSeries.coeff n (carlitzLog F) = carlitzLCoeff F n from carlitzLog_coeff F _,
      carlitzLCoeff_eq_zero F (fun i hi => h ⟨i, hi⟩),
      map_zero (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F)), Valuation.map_zero]
    exact lt_of_le_of_ne bot_le (fun hh => WithZero.exp_ne_zero hh.symm)

end ZagierHoffmanPositiveChar
