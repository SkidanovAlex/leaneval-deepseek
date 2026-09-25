import Mathlib
import Submission.Work.BourgainPlan.Oscillation.lacunary_defs
import Submission.Work.BourgainPlan.Oscillation.polyActIdxN_card_le_one_pow4

/-!
# At most one active arc at a lacunary scale `N ≥ 2^{4m+4}`

`polyActIdxN_card_le_one_pow4` proves "at most one active arc" for an arbitrary scale `N`,
but only under the two hypotheses `m ≥ 3` and `4^m ≤ N`.  The consumers of the oscillation
area need the statement for **all** `m` at the scale threshold `2^{4m+4} ≤ N` (this is the
hypothesis shape of `polyErrMultCutN_tsum_sq_le`).

The present file removes the hypothesis `m ≥ 3` by using the stronger scale threshold
`N ≥ 2^{4m+4}` instead of `N ≥ 4^m`: since `4m + 4 ≥ 2m`, the new threshold implies the old
one, but the numerical separation estimate obtained from it,

`2 · polyArcRadN P N ≤ 2^{1-7m-7} < (2^{2m+2})^{-1}`,

holds for every `m` (with `N ≥ 4^m` one only gets `m ≥ 3`).  The argument is then literally the
proof of `polyActIdxN_card_le_one_pow4`.
-/

namespace Work.BourgainPlan.Oscillation

open Finset MeasureTheory
open scoped BigOperators ENNReal
open Work.BourgainPlan.Maximal
open Commons.Analysis.ExponentialSums

noncomputable section

/-! ## Numerical bounds at the threshold `N ≥ 2^{4m+4}` -/

/-- **The arc radius at scale `N ≥ 2^{4m+4}` is at most `2^{-(7m+7)}`.**  Since `P.natDegree ≥ 2`
the exponent `-(d - 1/4) ≤ -7/4` and `N ≥ 2^{4m+4} = (2^{4m+4})`. -/
lemma polyArcRadN_le_two_pow_gen (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) {m N : ℕ}
    (hN : 2 ^ (4 * m + 4) ≤ N) :
    polyArcRadN P N ≤ (2:ℝ)^(-(7*(m:ℝ)+7)) := by
  have hNr : (2:ℝ)^(4*m+4) ≤ (N:ℝ) := by
    have h := (Nat.cast_le (α := ℝ)).mpr hN
    push_cast at h
    exact h
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by
    have h1 : (1:ℝ) ≤ (2:ℝ)^(4*m+4) := one_le_pow₀ (by norm_num)
    linarith
  have he : -((P.natDegree:ℝ) - 1/4) ≤ -(7/4:ℝ) := by
    have hd' : (2:ℝ) ≤ (P.natDegree:ℝ) := by exact_mod_cast hd
    linarith
  calc polyArcRadN P N
      = (N:ℝ) ^ (-((P.natDegree:ℝ) - 1/4)) := rfl
    _ ≤ (N:ℝ) ^ (-(7/4:ℝ)) := Real.rpow_le_rpow_of_exponent_le hN1 he
    _ ≤ ((2:ℝ)^(4*m+4)) ^ (-(7/4:ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hNr (by norm_num)
    _ = (2:ℝ)^(-(7*(m:ℝ)+7)) := by
        rw [← Real.rpow_natCast (2:ℝ) (4*m+4), ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
        congr 1
        push_cast
        ring

/-- A packaged form of `polyArcRadN_le_two_pow_gen`: `2 · polyArcRadN P N ≤ 2^{1-7m-7}`. -/
lemma two_mul_polyArcRadN_le_gen (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) {m N : ℕ}
    (hN : 2 ^ (4 * m + 4) ≤ N) :
    2 * polyArcRadN P N ≤ (2:ℝ)^((1:ℝ) - (7*(m:ℝ)+7)) := by
  have h := polyArcRadN_le_two_pow_gen P hd hN
  calc 2 * polyArcRadN P N ≤ 2 * (2:ℝ)^(-(7*(m:ℝ)+7)) := by linarith
    _ = (2:ℝ)^(1:ℝ) * (2:ℝ)^(-(7*(m:ℝ)+7)) := by rw [Real.rpow_one]
    _ = (2:ℝ)^((1:ℝ) + -(7*(m:ℝ)+7)) := (Real.rpow_add (by norm_num) _ _).symm
    _ = (2:ℝ)^((1:ℝ) - (7*(m:ℝ)+7)) := by ring_nf

/-- **The separation estimate at scale `N ≥ 2^{4m+4}`, for every `m`**:
`2 · polyArcRadN P N < (2^{2m+2})^{-1}`, the latter being an upper bound for `((q q')^{-1})`
with `q, q' < 2^{m+1}`. -/
lemma two_mul_polyArcRadN_lt_inv_gen (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) {m N : ℕ}
    (hN : 2 ^ (4 * m + 4) ≤ N) :
    2 * polyArcRadN P N < ((2:ℝ)^(2*m+2))⁻¹ := by
  have h2 := two_mul_polyArcRadN_le_gen P hd hN
  have hexp : (1:ℝ) - (7*(m:ℝ)+7) < -(((2*m+2 : ℕ)):ℝ) := by
    push_cast
    linarith
  calc 2 * polyArcRadN P N ≤ (2:ℝ)^((1:ℝ) - (7*(m:ℝ)+7)) := h2
    _ < (2:ℝ)^(-(((2*m+2 : ℕ)):ℝ)) := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hexp
    _ = ((2:ℝ)^(2*m+2))⁻¹ := by
          rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast]

/-- **The arc radius is smaller than `1/2`** at the scale `N ≥ 2^{4m+4}`, for every `m`. -/
lemma two_mul_polyArcRadN_lt_one_gen (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) {m N : ℕ}
    (hN : 2 ^ (4 * m + 4) ≤ N) : 2 * polyArcRadN P N < 1 := by
  have h := two_mul_polyArcRadN_lt_inv_gen P hd hN
  have hge : (1:ℝ) ≤ (2:ℝ)^(2*m+2) := one_le_pow₀ (by norm_num)
  have hle : ((2:ℝ)^(2*m+2))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hge
  linarith

/-! ## The main statement -/

/-- **At most one arc of a lacunary block is active.**  For `N ≥ 2^{4m+4}` and any `m`, at any
frequency `θ` at most one index triple `(q,a,l)` of the `m`-th block satisfies the arc condition
`|c θ − a/q − l| ≤ N^{−(d−1/4)}`.

Proof (as in `polyActIdxN_card_le_one_pow4`): two active arcs both contain `c θ`, so the two
frequencies `a/q + l`, `a'/q' + l'` lie within `2 · polyArcRadN P N` of each other.  Since
`q, q' < 2^{m+1}` their product is `≤ 2^{2m+2}`, while `2 · polyArcRadN P N < (2^{2m+2})⁻¹`;
hence `2 · polyArcRadN P N < ((q q')^{-1})` and `majorArc_term_unique` identifies the triples.
When `q = q'` the same estimate (here `2 · polyArcRadN P N < 1`) forces `l = l'`. -/
theorem polyActIdxN_card_le_one_pow (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) :
    ∀ (m N : ℕ) (θ : ℝ), 2 ^ (4 * m + 4) ≤ N →
      (Work.BourgainPlan.Oscillation.polyActIdxN P m N θ).card ≤ 1 := by
  intro m N θ hN
  rw [Finset.card_le_one]
  intro p hp q hq
  rw [polyActIdxN, Finset.mem_filter] at hp hq
  obtain ⟨hp1, hparc⟩ := hp
  obtain ⟨hq1, hqarc⟩ := hq
  rw [mem_polyAllIdx] at hp1 hq1
  obtain ⟨hmemP, _⟩ := hp1
  obtain ⟨hmemQ, _⟩ := hq1
  have hmemP' := mem_blockPair.mp hmemP
  have hmemQ' := mem_blockPair.mp hmemQ
  have hppos : 0 < p.1.1 := by
    have : 1 ≤ 2^m := Nat.one_le_two_pow
    omega
  have hqpos : 0 < q.1.1 := by
    have : 1 ≤ 2^m := Nat.one_le_two_pow
    omega
  by_cases hqa : p.1 = q.1
  · have hqarc' : |(P.leadingCoeff : ℝ) * θ - (p.1.2 : ℝ)/(p.1.1 : ℝ) - (q.2 : ℝ)|
        ≤ polyArcRadN P N := by
      have h := hqarc
      rw [← hqa] at h
      exact h
    have hl : p.2 = q.2 := by
      by_contra hne
      have h2r : 2 * polyArcRadN P N < 1 := two_mul_polyArcRadN_lt_one_gen P hd hN
      have hkey : |(p.2:ℝ) - (q.2:ℝ)| ≤ 2 * polyArcRadN P N := by
        have h := abs_sub_zero
          ((P.leadingCoeff : ℝ) * θ - (p.1.2:ℝ)/(p.1.1:ℝ) - (p.2:ℝ))
          ((P.leadingCoeff : ℝ) * θ - (p.1.2:ℝ)/(p.1.1:ℝ) - (q.2:ℝ))
        rw [show ((P.leadingCoeff : ℝ) * θ - (p.1.2:ℝ)/(p.1.1:ℝ) - (p.2:ℝ))
              - ((P.leadingCoeff : ℝ) * θ - (p.1.2:ℝ)/(p.1.1:ℝ) - (q.2:ℝ))
              = (q.2:ℝ) - (p.2:ℝ) by ring,
          abs_sub_comm] at h
        linarith
      have hcast : (((p.2 - q.2 : ℤ)) : ℝ) = (p.2:ℝ) - (q.2:ℝ) := by push_cast; ring
      have hlt : |((p.2 - q.2 : ℤ) : ℝ)| < 1 := by rw [hcast]; linarith
      rw [← Int.cast_abs] at hlt
      have h2 : |p.2 - q.2| < (1:ℤ) := by exact_mod_cast hlt
      rw [abs_lt] at h2
      exact hne (by omega)
    exact Prod.ext hqa hl
  · have hp_lt : (p.1.1:ℝ) < (2:ℝ)^(m+1) := by
      have := hmemP'.2.1
      exact_mod_cast this
    have hq_lt : (q.1.1:ℝ) < (2:ℝ)^(m+1) := by
      have := hmemQ'.2.1
      exact_mod_cast this
    have hppos' : (0:ℝ) < (p.1.1:ℝ) := by exact_mod_cast hppos
    have hqpos' : (0:ℝ) < (q.1.1:ℝ) := by exact_mod_cast hqpos
    have hpow : (2:ℝ)^(m+1) * (2:ℝ)^(m+1) = (2:ℝ)^(2*m+2) := by
      rw [← pow_add]
      congr 1
      ring
    have hprod : ((p.1.1:ℝ) * (q.1.1:ℝ)) ≤ (2:ℝ)^(2*m+2) := by
      have hpq : (p.1.1:ℝ) * (q.1.1:ℝ) < (2:ℝ)^(m+1) * (2:ℝ)^(m+1) :=
        mul_lt_mul hp_lt (le_of_lt hq_lt) hqpos' (by positivity)
      rw [hpow] at hpq
      exact le_of_lt hpq
    have hsep : 2 * polyArcRadN P N < ((p.1.1:ℝ) * (q.1.1:ℝ))⁻¹ := by
      refine lt_of_lt_of_le (two_mul_polyArcRadN_lt_inv_gen P hd hN)
        ((inv_le_inv₀ (by positivity) (by positivity)).mpr hprod)
    have huniq := majorArc_term_unique hppos hqpos hmemP'.2.2.1 hmemQ'.2.2.1
      (Nat.coprime_iff_gcd_eq_one.mp hmemP'.2.2.2) (Nat.coprime_iff_gcd_eq_one.mp hmemQ'.2.2.2)
      hparc hqarc hsep
    obtain ⟨h1, h2, h3⟩ := huniq
    exact absurd (Prod.ext (Prod.ext h1 h2) h3) (fun h' => hqa (congrArg Prod.fst h'))

end

end Work.BourgainPlan.Oscillation
