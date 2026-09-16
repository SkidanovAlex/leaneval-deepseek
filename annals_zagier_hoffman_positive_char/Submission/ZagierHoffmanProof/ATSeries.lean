import Submission.ZagierHoffmanProof.CarlitzAT
import Mathlib.RingTheory.PowerSeries.Inverse
import Submission.Commons.RingTheory.PowerSeries.qpow_rec_mul_inv
import Submission.Commons.Combinatorics.QPowerRec.seq_rec_expand
import Submission.Commons.Combinatorics.QPowerRec.sum_seq_eq_multinomial
import Submission.Commons.Combinatorics.Multinomial.lucas_no_carry

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Polynomial
open scoped BigOperators

/-!
# The Anderson–Thakur coefficients as power-series coefficients

`CarlitzAT.lean` defines the Anderson–Thakur coefficient sequence `c_n = atCoeff F n` by the
recursion
```
c_0 = 1,   c_n = ∑_{j : q^j ≤ n} (γ_j/D_j) c_{n-q^j}   (n ≥ 1),
```
so that `α_n = Γ_n c_{n-1}`.  This file identifies the sequence with the coefficients of the
inverse of the power series
```
1 - S(x),   S(x) = ∑_j (γ_j/D_j) x^(q^j).
```
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

/-- The power series `S(x) = ∑_j (γ_j / D_j) x ^ (q ^ j)` (only the `q`-power exponents are
non-zero, so the coefficient of `x ^ n` is `γ_j/D_j` if `n = q ^ j`, and `0` otherwise). -/
noncomputable def atS : PowerSeries (atQ F) :=
  PowerSeries.mk fun n => ∑ j ∈ (Finset.range (n + 1)).filter (fun j => Nat.card F ^ j = n),
    (atGamma F j) * (atD F j)⁻¹

lemma atS_coeff (n : ℕ) :
    PowerSeries.coeff n (atS F)
      = ∑ j ∈ (Finset.range (n + 1)).filter (fun j => Nat.card F ^ j = n),
          (atGamma F j) * (atD F j)⁻¹ :=
  PowerSeries.coeff_mk n _

lemma atS_coeff_zero : PowerSeries.coeff 0 (atS F) = 0 := by
  rw [atS_coeff]
  refine Finset.sum_eq_zero fun j hj => ?_
  rw [Finset.mem_filter] at hj
  exact absurd hj.2 (pow_ne_zero j (by have := carlitz_card_ge_two F; omega))

lemma atS_coeff_pow (j : ℕ) :
    PowerSeries.coeff (Nat.card F ^ j) (atS F) = (atGamma F j) * (atD F j)⁻¹ := by
  rw [atS_coeff]
  refine Finset.sum_eq_single j ?_ ?_
  · intro i hi hne
    rw [Finset.mem_filter] at hi
    exact absurd (Nat.pow_right_injective (carlitz_card_ge_two F) hi.2) hne
  · intro h
    refine absurd ?_ h
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_lt (Nat.lt_pow_self (by have := carlitz_card_ge_two F; omega)), rfl⟩

lemma constantCoeff_atS : PowerSeries.constantCoeff (atS F) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact atS_coeff_zero F

lemma constantCoeff_one_sub_atS :
    PowerSeries.constantCoeff (1 - atS F) = 1 := by
  rw [map_sub, map_one, constantCoeff_atS F, sub_zero]

lemma one_sub_atS_ne_zero : (1 - atS F) ≠ 0 := by
  intro h
  have := congrArg PowerSeries.constantCoeff h
  rw [constantCoeff_one_sub_atS F, map_zero] at this
  exact one_ne_zero this

section Bridge

open PowerSeries

/-- The recursion hypothesis of the generic `q`-power lemmas, specialised to the
Anderson–Thakur coefficients: this is `atCoeff_succ`. -/
lemma atCoeff_hrec :
    ∀ n, 1 ≤ n → atCoeff F n =
      ∑ j ∈ (Finset.range (n + 1)).filter (fun j => Nat.card F ^ j ≤ n),
        (atGamma F j * (atD F j)⁻¹) * atCoeff F (n - Nat.card F ^ j) :=
  fun n hn => atCoeff_succ F (by omega)

/-- ★ **The Anderson–Thakur coefficients are the coefficients of the inverse of
`1 - ∑_j (γ_j/D_j) x ^ (q ^ j)`.** -/
theorem atCoeff_eq_coeff_inv (N : ℕ) :
    atCoeff F N = PowerSeries.coeff N ((1 - atS F)⁻¹) := by
  have h := Commons.RingTheory.PowerSeries.qpow_rec_mul_inv
    (Nat.card F) (carlitz_card_ge_two F) (fun j => atGamma F j * (atD F j)⁻¹) (atCoeff F)
    (atCoeff_zero F) (atCoeff_hrec F)
  have hne : PowerSeries.constantCoeff (1 - atS F) ≠ 0 := by
    rw [constantCoeff_one_sub_atS F]
    exact one_ne_zero
  have hinv : (1 - atS F)⁻¹ = PowerSeries.mk (atCoeff F) :=
    (PowerSeries.inv_eq_iff_mul_eq_one (φ := PowerSeries.mk (atCoeff F)) hne).mpr h
  rw [hinv, PowerSeries.coeff_mk]

/-- ★ **Chen's explicit expansion of `c_N` as an ordered-partition sum** (Lemma 2.6(a) of
arXiv:1506.06463, before regrouping by multiplicities). -/
theorem atCoeff_eq_sum_seq (N B : ℕ) (hB : N + 1 ≤ B) :
    atCoeff F N = ∑ m ∈ Finset.range (N + 1), ∑ a : Fin m → Fin B,
      (if (∑ i, Nat.card F ^ ((a i : ℕ))) = N then
        ∏ i, (atGamma F ((a i : ℕ))) * (atD F ((a i : ℕ)))⁻¹ else 0) :=
  Commons.Combinatorics.QPowerRec.seq_rec_expand (Nat.card F) (carlitz_card_ge_two F)
    (fun j => atGamma F j * (atD F j)⁻¹) (atCoeff F) (atCoeff_zero F) (atCoeff_hrec F) N B hB

/-- ★ **Chen's explicit expansion of `c_N`, regrouped by multiplicities** (the multinomial form of
Lemma 2.6(a) of arXiv:1506.06463): the ordered partitions of `N` into `q`-powers are grouped into
multiplicity vectors `b : Fin B → Fin (N+1)` (`b i` = the number of times `q ^ i` occurs), each
counted with its multinomial coefficient. -/
theorem atCoeff_eq_sum_multinomial (N B : ℕ) (hB : N + 1 ≤ B) :
    atCoeff F N =
      ∑ b : {b : Fin B → Fin (N + 1) //
          (∑ i, ((b i : ℕ)) * Nat.card F ^ ((i : ℕ))) = N},
        ((Nat.multinomial Finset.univ (fun i => ((b.1 i : ℕ))) : ℕ) : atQ F) *
          ∏ i : Fin B, (atGamma F ((i : ℕ)) * (atD F ((i : ℕ)))⁻¹) ^ ((b.1 i : ℕ)) := by
  rw [atCoeff_eq_sum_seq F N B hB]
  exact Commons.Combinatorics.QPowerRec.sum_seq_eq_multinomial (Nat.card F)
    (by have := carlitz_card_ge_two F; omega) (fun j => atGamma F j * (atD F j)⁻¹) N B hB

end Bridge

section NoCarry

/-- In characteristic `p`, a sum of terms whose coefficients are divisible by `p` may be
restricted to the indices satisfying any predicate. -/
lemma sum_filter_eq_of_dvd_cast {R : Type*} [CommRing R] {p : ℕ} [CharP R p] {ι : Type*}
    (s : Finset ι) (m : ι → ℕ) (g : ι → R) (P : ι → Prop) [DecidablePred P]
    (h : ∀ i ∈ s, ¬ P i → (m i : R) = 0) :
    ∑ i ∈ s, (m i : R) * g i = ∑ i ∈ s.filter P, (m i : R) * g i := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  by_cases hP : P i
  · rw [if_pos hP]
  · rw [if_neg hP, h i hi hP, zero_mul]


/-- A vector of multiplicities has **no carries** in base `p = ringChar F`: at every position the
base-`p` digits of the entries sum to a value `< p`. -/
def NoCarryVec {B : ℕ} (v : Fin B → ℕ) : Prop :=
  ∀ j : ℕ, (∑ i : Fin B, v i / (ringChar F) ^ j % (ringChar F)) < ringChar F

open Classical in
/-- ★★ **Chen's Lemma 2.6(a) in its no-carry form**: in `atCoeff`, only the multiplicity vectors
whose base-`p` column sums are all `< p` (equivalently, whose multinomial coefficient is prime to
`p`) contribute — all other terms have a coefficient divisible by `p` and vanish in characteristic
`p`.  This is the form in which the recursive structure of the `c_n` is visible. -/
theorem atCoeff_eq_sum_multinomial_noCarry (N B : ℕ) (hB : N + 1 ≤ B) :
    atCoeff F N =
      ∑ b ∈ (Finset.univ : Finset {b : Fin B → Fin (N + 1) //
            (∑ i, ((b i : ℕ)) * Nat.card F ^ ((i : ℕ))) = N}).filter
          (fun b => NoCarryVec F (fun i => ((b.1 i : ℕ)))),
        ((Nat.multinomial Finset.univ (fun i => ((b.1 i : ℕ))) : ℕ) : atQ F) *
          ∏ i : Fin B, (atGamma F ((i : ℕ)) * (atD F ((i : ℕ)))⁻¹) ^ ((b.1 i : ℕ)) := by
  rw [atCoeff_eq_sum_multinomial F N B hB]
  refine sum_filter_eq_of_dvd_cast (R := atQ F) (p := ringChar F)
    (Finset.univ : Finset {b : Fin B → Fin (N + 1) //
      (∑ i, ((b i : ℕ)) * Nat.card F ^ ((i : ℕ))) = N})
    (fun b => Nat.multinomial Finset.univ (fun i => ((b.1 i : ℕ))))
    (fun b => ∏ i : Fin B, (atGamma F ((i : ℕ)) * (atD F ((i : ℕ)))⁻¹) ^ ((b.1 i : ℕ)))
    (fun b => NoCarryVec F (fun i => ((b.1 i : ℕ)))) ?_
  intro b _ hb
  rw [CharP.cast_eq_zero_iff (atQ F) (ringChar F)]
  by_contra hdvd
  exact hb ((Commons.Combinatorics.Multinomial.lucas_no_carry
    (CharP.prime_ringChar F) (fun i : Fin B => ((b.1 i : ℕ)))).mp hdvd)

open Classical in
/-- ★★ **Chen's Lemma 2.6(a) in the `ℕ`-valued form.**  The multiplicity vectors are now
functions `Fin B → ℕ` (bounded by `N`, `N + 1 ≤ B`), which is the form in which the Frobenius
descent `S_{q^M-1} ≅ S_{q^{M-1}-1}` on *no-carry* partition vectors operates (the `Fin (N+1)`-valued
form is `atCoeff_eq_sum_multinomial_noCarry`). -/
theorem atCoeff_eq_sum_multi (N B : ℕ) (hB : N + 1 ≤ B) :
    atCoeff F N =
      ∑ b ∈ ((Fintype.piFinset fun _ : Fin B => Finset.range (N + 1)).filter
          (fun b : Fin B → ℕ =>
            (∑ i, b i * Nat.card F ^ (i : ℕ)) = N ∧ NoCarryVec F b)),
        ((Nat.multinomial Finset.univ b : ℕ) : atQ F) *
          ∏ i : Fin B, (atGamma F ((i : ℕ)) * (atD F ((i : ℕ)))⁻¹) ^ (b i) := by
  rw [atCoeff_eq_sum_multinomial_noCarry F N B hB]
  refine Finset.sum_bij (fun b _ => fun k => ((b.1 k : ℕ))) ?_ ?_ ?_ ?_
  · intro b hb
    rw [Finset.mem_filter] at hb ⊢
    obtain ⟨-, hnc⟩ := hb
    refine ⟨?_, b.2, hnc⟩
    rw [Fintype.mem_piFinset]
    intro k
    exact Finset.mem_range.mpr (b.1 k).isLt
  · intro b₁ hb₁ b₂ hb₂ heq
    refine Subtype.ext (funext (fun k => Fin.ext ?_))
    simpa using congrFun heq k
  · intro b hb
    rw [Finset.mem_filter, Fintype.mem_piFinset] at hb
    obtain ⟨hbound, hsum, hnc⟩ := hb
    refine ⟨⟨fun k => ⟨b k, Nat.lt_succ_iff.mpr (by
      have := hbound k; rw [Finset.mem_range] at this; omega)⟩, by simpa using hsum⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · simpa using hnc
    · rfl
  · intro b hb
    rfl

end NoCarry

end ZagierHoffmanPositiveChar
