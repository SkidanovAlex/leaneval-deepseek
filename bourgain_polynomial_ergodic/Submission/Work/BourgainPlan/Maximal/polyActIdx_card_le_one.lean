import Mathlib
import Submission.Work.BourgainPlan.Maximal.poly_block_core_defs

namespace Work.BourgainPlan.Maximal

open Commons.Analysis.ExponentialSums

/-- **At most one arc of a dyadic block is active.**  For `N = 2^k` with `k ≥ 2m+3`, at any frequency `θ` at most one index triple `(q,a,l)` of the `m`-th dyadic block satisfies the arc condition `|c θ − a/q − l| ≤ N^{−(d−1/4)}`.

Proof: port `Commons.Analysis.ExponentialSums.powActIdx_card_le_one`
(`pure_power_kernel_maximal_l2.lean` ~line 1698) verbatim, where `powActIdx` has the same arc
condition on `a/q + l`.  The core estimate is `2 * polyArcRad P k < ((q:ℝ) * (q':ℝ))⁻¹` from
`q, q' < 2^{m+1}` and `k ≥ 2m+3`, followed by
`Commons.Analysis.ExponentialSums.majorArc_term_unique`.  Note: `Work.BourgainPlan.Maximal.poly_arc_witness_unique`
needs the stronger hypothesis `q ≤ N^{1/4}`; do not use it, supply the separation `hsep` by hand. -/
theorem polyActIdx_card_le_one (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) {m k : ℕ}
    (hk : 2*m+3 ≤ k) (θ : ℝ) : (polyActIdx P m k θ).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro p hp q hq
  rw [mem_polyActIdx] at hp hq
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
  have hk1 : 1 ≤ k := by omega
  by_cases hqa : p.1 = q.1
  · have hqarc' : |(P.leadingCoeff : ℝ) * θ - (p.1.2:ℝ)/(p.1.1:ℝ) - (q.2:ℝ)|
        ≤ polyArcRad P k := by
      have h := hqarc
      rw [← hqa] at h
      exact h
    have hl : p.2 = q.2 := by
      by_contra hne
      have h2r : 2 * polyArcRad P k < 1 := by
        have h1 := powArcRad_lt_half P.natDegree hd hk1
        have h1' : polyArcRad P k < 1/2 := h1
        linarith
      have hkey : |(p.2:ℝ) - (q.2:ℝ)| ≤ 2 * polyArcRad P k := by
        have h := abs_sub_zero ((P.leadingCoeff : ℝ) * θ - (p.1.2:ℝ)/(p.1.1:ℝ) - (p.2:ℝ))
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
    have hsep : 2 * polyArcRad P k < ((p.1.1:ℝ) * (q.1.1:ℝ))⁻¹ := by
      refine lt_of_lt_of_le ?_ ((inv_le_inv₀ (by positivity) (by positivity)).mpr hprod)
      have hk' : (2 * (m:ℝ) + 3) ≤ (k:ℝ) := by exact_mod_cast hk
      have hd' : (2:ℝ) ≤ (P.natDegree:ℝ) := by exact_mod_cast hd
      have hexp : (1:ℝ) - (k:ℝ) * ((P.natDegree:ℝ) - 1/4) < -(((2*m+2 : ℕ)) : ℝ) := by
        have h4 : (7/4:ℝ) ≤ (P.natDegree:ℝ) - 1/4 := by linarith
        have h5 : (7/4:ℝ) * (k:ℝ) ≤ ((P.natDegree:ℝ) - 1/4) * (k:ℝ) :=
          mul_le_mul_of_nonneg_right h4 (Nat.cast_nonneg k)
        push_cast
        nlinarith
      have hA : polyArcRad P k = (2:ℝ)^(-((k:ℝ) * ((P.natDegree:ℝ) - 1/4))) := by
        rw [polyArcRad, powArcRad_two_pow, ← Real.rpow_natCast (2:ℝ) k,
          ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
        congr 1
        ring
      have h2 : 2 * polyArcRad P k
          = (2:ℝ)^((1:ℝ) - (k:ℝ) * ((P.natDegree:ℝ) - 1/4)) := by
        calc 2 * polyArcRad P k
            = (2:ℝ)^(1:ℝ) * (2:ℝ)^(-((k:ℝ) * ((P.natDegree:ℝ) - 1/4))) := by
                rw [Real.rpow_one, hA]
          _ = (2:ℝ)^((1:ℝ) + -((k:ℝ) * ((P.natDegree:ℝ) - 1/4))) :=
                (Real.rpow_add (by norm_num : (0:ℝ) < 2) _ _).symm
          _ = (2:ℝ)^((1:ℝ) - (k:ℝ) * ((P.natDegree:ℝ) - 1/4)) := by ring_nf
      rw [h2, ← Real.rpow_natCast (2:ℝ) (2*m+2), ← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
      exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hexp
    have huniq := majorArc_term_unique hppos hqpos hmemP'.2.2.1 hmemQ'.2.2.1
      (Nat.coprime_iff_gcd_eq_one.mp hmemP'.2.2.2) (Nat.coprime_iff_gcd_eq_one.mp hmemQ'.2.2.2)
      hparc hqarc hsep
    obtain ⟨h1, h2, h3⟩ := huniq
    exact absurd (Prod.ext (Prod.ext h1 h2) h3) (fun h' => hqa (congrArg Prod.fst h'))

end Work.BourgainPlan.Maximal
