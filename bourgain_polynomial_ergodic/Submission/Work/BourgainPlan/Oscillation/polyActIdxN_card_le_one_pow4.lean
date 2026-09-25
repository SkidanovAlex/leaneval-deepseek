import Mathlib
import Submission.Work.BourgainPlan.Oscillation.lacunary_defs

/-!
# At most one active arc at an arbitrary lacunary scale `N ≥ 4^m`

The circle-method development uses the **dyadic** scales `N = 2^k` and the corresponding
separation estimate `Work.BourgainPlan.Maximal.polyActIdx_card_le_one`.  Bourgain's oscillation
inequality, however, is stated along the **lacunary** scales `N_i = ⌊ρ^i⌋`, which are not dyadic,
so the "at most one active arc" statement must be re-proved at an arbitrary scale `N`.

The present file does exactly that: for `N ≥ 4^m` and `m ≥ 3`, at most one index triple of the
`m`-th denominator block can satisfy the arc condition

`|c·θ − a/q − l| ≤ polyArcRadN P N = N^{−(d−1/4)}`,  where `c = P.leadingCoeff`, `d = P.natDegree`.

The separation input is `Commons.Analysis.ExponentialSums.majorArc_term_unique`; the only new
content is the numerical estimate

`2 · polyArcRadN P N ≤ 2^{1 − 7m/2} < (2^{2m+2})^{-1} ≤ ((q·q')^{-1})`,

which replaces the dyadic estimate `2 · polyArcRad P k < ((q q')^{-1})` of the maximal area.
-/

namespace Work.BourgainPlan.Oscillation

open Finset MeasureTheory
open scoped BigOperators ENNReal
open Work.BourgainPlan.Maximal
open Commons.Analysis.ExponentialSums

noncomputable section

/-! ## Numerical bounds on the arbitrary-scale arc radius -/

/-- **The arc radius at scale `N ≥ 4^m` is at most `2^{-7m/2}`.**  This is the estimate that
replaces the dyadic `powArcRad` bound: since `P.natDegree ≥ 2` the exponent `−(d−1/4) ≤ −7/4`
and `N ≥ 4^m = 2^{2m}`. -/
lemma polyArcRadN_le_two_pow (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) {m N : ℕ}
    (hN : 4 ^ m ≤ N) : polyArcRadN P N ≤ (2:ℝ)^(-(7*(m:ℝ)/2)) := by
  have hNr : (4:ℝ)^m ≤ (N:ℝ) := by
    have h := (Nat.cast_le (α := ℝ)).mpr hN
    push_cast at h
    exact h
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by
    have h1 : (1:ℝ) ≤ (4:ℝ)^m := one_le_pow₀ (by norm_num)
    linarith
  have h2mN : (2:ℝ)^(2*m) ≤ (N:ℝ) := by
    have hpow : (2:ℝ)^(2*m) = (4:ℝ)^m := by rw [pow_mul]; norm_num
    rw [hpow]; exact hNr
  have he : -((P.natDegree:ℝ) - 1/4) ≤ -(7/4:ℝ) := by
    have hd' : (2:ℝ) ≤ (P.natDegree:ℝ) := by exact_mod_cast hd
    linarith
  calc polyArcRadN P N
      = (N:ℝ) ^ (-((P.natDegree:ℝ) - 1/4)) := rfl
    _ ≤ (N:ℝ) ^ (-(7/4:ℝ)) := Real.rpow_le_rpow_of_exponent_le hN1 he
    _ ≤ ((2:ℝ)^(2*m)) ^ (-(7/4:ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) h2mN (by norm_num)
    _ = (2:ℝ)^(-(7*(m:ℝ)/2)) := by
        rw [← Real.rpow_natCast (2:ℝ) (2*m), ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
        congr 1
        push_cast
        ring

/-- A packaged form of `polyArcRadN_le_two_pow`: `2 · polyArcRadN P N ≤ 2^{1−7m/2}`. -/
lemma two_mul_polyArcRadN_le (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) {m N : ℕ}
    (hN : 4 ^ m ≤ N) : 2 * polyArcRadN P N ≤ (2:ℝ)^((1:ℝ) - 7*(m:ℝ)/2) := by
  have h := polyArcRadN_le_two_pow P hd hN
  calc 2 * polyArcRadN P N ≤ 2 * (2:ℝ)^(-(7*(m:ℝ)/2)) := by linarith
    _ = (2:ℝ)^(1:ℝ) * (2:ℝ)^(-(7*(m:ℝ)/2)) := by rw [Real.rpow_one]
    _ = (2:ℝ)^((1:ℝ) + -(7*(m:ℝ)/2)) := (Real.rpow_add (by norm_num) _ _).symm
    _ = (2:ℝ)^((1:ℝ) - 7*(m:ℝ)/2) := by ring_nf

/-- **The arc radius is smaller than `1/2`** once `N ≥ 4^m` and `m ≥ 3`. -/
lemma two_mul_polyArcRadN_lt_one (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) {m N : ℕ}
    (hm : 3 ≤ m) (hN : 4 ^ m ≤ N) : 2 * polyArcRadN P N < 1 := by
  have h2 := two_mul_polyArcRadN_le P hd hN
  have hexp : (1:ℝ) - 7*(m:ℝ)/2 < 0 := by
    have hm' : (3:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
    linarith
  calc 2 * polyArcRadN P N ≤ (2:ℝ)^((1:ℝ) - 7*(m:ℝ)/2) := h2
    _ < (2:ℝ)^(0:ℝ) := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hexp
    _ = 1 := Real.rpow_zero 2

/-- **The separation estimate at an arbitrary scale**: for `N ≥ 4^m` and `m ≥ 3`,
`2 · polyArcRadN P N < (2^{2m+2})^{-1}`, the latter being an upper bound for `((q q')^{-1})`
with `q, q' < 2^{m+1}`. -/
lemma two_mul_polyArcRadN_lt_inv (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) {m N : ℕ}
    (hm : 3 ≤ m) (hN : 4 ^ m ≤ N) :
    2 * polyArcRadN P N < ((2:ℝ)^(2*m+2))⁻¹ := by
  have h2 := two_mul_polyArcRadN_le P hd hN
  have hexp : (1:ℝ) - 7*(m:ℝ)/2 < -(((2*m+2 : ℕ)):ℝ) := by
    have hm' : (3:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
    push_cast
    linarith
  calc 2 * polyArcRadN P N ≤ (2:ℝ)^((1:ℝ) - 7*(m:ℝ)/2) := h2
    _ < (2:ℝ)^(-(((2*m+2 : ℕ)):ℝ)) := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hexp
    _ = ((2:ℝ)^(2*m+2))⁻¹ := by
          rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast]

/-! ## The main statement -/

/-- **At most one arc of an arbitrary-scale block is active.**  For `N ≥ 4^m` and `m ≥ 3`, at any
frequency `θ` at most one index triple `(q,a,l)` of the `m`-th block satisfies the arc condition
`|c θ − a/q − l| ≤ N^{−(d−1/4)}`.

Proof: the two arcs both contain `c θ`, so the two frequencies `a/q + l`, `a'/q' + l'` are within
`2 · polyArcRadN P N` of each other.  Since `q, q' < 2^{m+1}`, their product is `< 2^{2m+2}`, while
`2 · polyArcRadN P N < (2^{2m+2})⁻¹` (previous lemma); hence
`2 · polyArcRadN P N < ((q q')^{-1})` and `majorArc_term_unique` identifies the two triples. -/
theorem polyActIdxN_card_le_one_pow4 (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    {m N : ℕ} (hm : 3 ≤ m) (hN : 4 ^ m ≤ N) (θ : ℝ) :
    (Work.BourgainPlan.Oscillation.polyActIdxN P m N θ).card ≤ 1 := by
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
      have h2r : 2 * polyArcRadN P N < 1 := two_mul_polyArcRadN_lt_one P hd hm hN
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
      refine lt_of_lt_of_le (two_mul_polyArcRadN_lt_inv P hd hm hN)
        ((inv_le_inv₀ (by positivity) (by positivity)).mpr hprod)
    have huniq := majorArc_term_unique hppos hqpos hmemP'.2.2.1 hmemQ'.2.2.1
      (Nat.coprime_iff_gcd_eq_one.mp hmemP'.2.2.2) (Nat.coprime_iff_gcd_eq_one.mp hmemQ'.2.2.2)
      hparc hqarc hsep
    obtain ⟨h1, h2, h3⟩ := huniq
    exact absurd (Prod.ext (Prod.ext h1 h2) h3) (fun h' => hqa (congrArg Prod.fst h'))

end

end Work.BourgainPlan.Oscillation
