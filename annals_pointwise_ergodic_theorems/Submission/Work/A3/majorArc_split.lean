import Mathlib
import Submission.Work.A3.majorArcKernel
import Submission.Work.A3.weyl_poly
import Submission.Work.A3.polyEnergyOn_one_le

/-!
# The "large-denominator" part of the major arcs (Area A3)

For `θ` lying in an arc of radius `1/(q N^{d/2})` around a reduced fraction `a/q` with
`N^γ ≤ q ≤ N^η` (`η ≤ 1`), the rational approximation `a/q` *validates Weyl's inequality*
(`|θ - a/q| ≤ 1/q²` because `q ≤ N^η ≤ N ≤ N^{d/2}`), and the Weyl bracket is
`(1/q + 1/N + q/N^d)^{1/2^{d-1}} ≤ (3/q)^{1/2^{d-1}} ≤ 3^{1/2^{d-1}} N^{-γ/2^{d-1}}`.

Hence `‖expSum Q N θ‖ ≤ C_ε N^{1+ε-γ/2^{d-1}}` on that set, a **fixed power of N** saving,
and since `∫₀¹‖expSum Q N‖² = E₁(N) ≤ deg Q · N` (the sharp second moment), the `L²` trick
  `∫_A ‖S‖^{2s} ≤ (sup_A ‖S‖)^{2s-2} ∫_A ‖S‖²`
gives `∫_{A} ‖expSum Q N‖^{2s} ≤ C^{2s} N^{2s-d}` as soon as
`(2s-2)(γ/2^{d-1} - ε) ≥ d-1`.

This is the "case `q ≥ N^γ`" of the major-arc analysis (see
`NOTES_A3_deepShoulder_SESSION.md`); the cases `q < N^γ` (coherent + transition + deep shoulder)
are handled by `A3/coherentArc_bound`, `A3/transitionArc_bound` and the (open) deep-shoulder
input.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.A3

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators

noncomputable section

/-- The union of the arcs of radius `1/(q N^{d/2})` around the reduced fractions `a/q` with
`N^γ ≤ q ≤ N^η`.  (The "large denominator" part of the major arcs.) -/
def largeArcSet (Q : Polynomial ℤ) (N : ℕ) (η γ : ℝ) : Set ℝ :=
  {θ : ℝ | ∃ (q : ℕ) (a : ℤ), 1 ≤ q ∧ IsCoprime a (q : ℤ) ∧
    (N : ℝ) ^ γ ≤ (q : ℝ) ∧ (q : ℝ) ≤ (N : ℝ) ^ η ∧
    |θ - (a : ℝ) / (q : ℝ)| ≤ 1 / ((q : ℝ) * (N : ℝ) ^ ((Q.natDegree : ℝ) / 2))}

theorem largeArcSet_subset_majorArcSet (Q : Polynomial ℤ) (N : ℕ) {η γ : ℝ} (hγη : γ ≤ η) :
    largeArcSet Q N η γ ⊆ majorArcSet Q N η := by
  rintro θ ⟨q, a, hq1, hcop, -, hqη, hθ⟩
  exact ⟨q, a, hq1, hcop, hqη, hθ⟩

/-- The "coherent + transition" part of the major arcs around the `a/q` with `q ≤ N^γ`: the
points with `|β| N^d = |θ - a/q| N^d ≤ (N/q)^{d/(d+1)}/100`, i.e. exactly the range covered by
`A3/transitionArc_bound`.  (For `q ≤ N^γ` these are the arcs where the block sums of the residue
split are dominated by their integrals.) -/
def transitionArcSet (Q : Polynomial ℤ) (N : ℕ) (γ : ℝ) : Set ℝ :=
  {θ : ℝ | ∃ (q : ℕ) (a : ℤ), 1 ≤ q ∧ IsCoprime a (q : ℤ) ∧ (q : ℝ) ≤ (N : ℝ) ^ γ ∧
    |θ - (a : ℝ) / (q : ℝ)| ≤ 1 / ((q : ℝ) * (N : ℝ) ^ ((Q.natDegree : ℝ) / 2)) ∧
    |θ - (a : ℝ) / (q : ℝ)| * (N : ℝ) ^ Q.natDegree ≤
      ((N : ℝ) / (q : ℝ)) ^ ((Q.natDegree : ℝ) / (Q.natDegree + 1)) / 100}

/-- The "deep shoulder" of the major arcs: the points of the arcs around reduced `a/q` with
`q ≤ N^γ` whose `β = θ - a/q` is *beyond* the transition threshold
`|β| N^d = (N/q)^{d/(d+1)}/100` (the range that the elementary block/Riemann-sum comparison plus
the singular-integral bound cannot reach).  Its complement (inside the `q ≤ N^γ` arcs) is the
coherent + transition region handled by `A3/coherentArc_bound` and `A3/transitionArc_bound`. -/
def deepArcSet (Q : Polynomial ℤ) (N : ℕ) (γ : ℝ) : Set ℝ :=
  {θ : ℝ | ∃ (q : ℕ) (a : ℤ), 1 ≤ q ∧ IsCoprime a (q : ℤ) ∧ (q : ℝ) ≤ (N : ℝ) ^ γ ∧
    |θ - (a : ℝ) / (q : ℝ)| ≤ 1 / ((q : ℝ) * (N : ℝ) ^ ((Q.natDegree : ℝ) / 2)) ∧
    ((N : ℝ) / (q : ℝ)) ^ ((Q.natDegree : ℝ) / (Q.natDegree + 1)) / 100 ≤
      |θ - (a : ℝ) / (q : ℝ)| * (N : ℝ) ^ Q.natDegree}

/-- **Weyl on the large-denominator arcs**: a fixed power saving. -/
theorem expSum_le_of_largeArc (Q : Polynomial ℤ) (hd : 2 ≤ Polynomial.natDegree Q)
    {ε γ η : ℝ} (hε : 0 < ε) (hη : η ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (θ : ℝ), 1 ≤ N → θ ∈ largeArcSet Q N η γ →
      ‖expSum Q N θ‖ ≤
        C * (N : ℝ) ^ (1 + ε - γ / (2 : ℝ) ^ (Polynomial.natDegree Q - 1)) := by
  obtain ⟨CW, hCW, hweyl⟩ := weyl_poly Q hd hε
  refine ⟨CW * (3 : ℝ) ^ ((1 : ℝ) / (2 : ℝ) ^ (Polynomial.natDegree Q - 1)), by positivity, ?_⟩
  intro N θ hN hθ
  obtain ⟨q, a, hq1, hcop, hqγ, hqη, happrox⟩ := hθ
  have hq1' : (1 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq1
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le zero_lt_one hN1
  have hd1 : 1 ≤ Polynomial.natDegree Q := le_trans (by norm_num) hd
  set d := Polynomial.natDegree Q with hddef
  set t : ℝ := (1 : ℝ) / (2 : ℝ) ^ (d - 1) with ht
  have htpos : 0 < t := by rw [ht]; positivity
  have hqNη : (q : ℝ) ≤ (N : ℝ) ^ η := hqη
  have hNηN : (N : ℝ) ^ η ≤ (N : ℝ) ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN1 hη
  have hN1' : (N : ℝ) ^ (1 : ℝ) = (N : ℝ) := Real.rpow_one _
  have hNd : (N : ℝ) ≤ (N : ℝ) ^ ((d : ℝ) / 2) := by
    have h2 : (1 : ℝ) ≤ (d : ℝ) / 2 := by
      have h3 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      linarith
    calc (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (N : ℝ) ^ ((d : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le hN1 h2
  have hqNd : (q : ℝ) ≤ (N : ℝ) ^ ((d : ℝ) / 2) := by
    calc (q : ℝ) ≤ (N : ℝ) ^ η := hqNη
      _ ≤ (N : ℝ) ^ (1 : ℝ) := hNηN
      _ = (N : ℝ) := hN1'
      _ ≤ (N : ℝ) ^ ((d : ℝ) / 2) := hNd
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
  have hweylhyp : |θ - (a : ℝ) / (q : ℝ)| ≤ 1 / ((q : ℝ) ^ 2) := by
    have h2 : 1 / ((q : ℝ) * (N : ℝ) ^ ((d : ℝ) / 2)) ≤ 1 / ((q : ℝ) ^ 2) := by
      apply one_div_le_one_div_of_le (by positivity)
      calc (q : ℝ) ^ 2 = (q : ℝ) * (q : ℝ) := by ring
        _ ≤ (q : ℝ) * (N : ℝ) ^ ((d : ℝ) / 2) :=
            mul_le_mul_of_nonneg_left hqNd hqpos.le
    exact le_trans happrox h2
  have hmain : ‖expSum Q N θ‖ ≤ CW * (N : ℝ) ^ (1 + ε) *
      (((q : ℝ)⁻¹ + (N : ℝ)⁻¹ + (q : ℝ) * (N : ℝ) ^ (-((d : ℤ)))) ^ t) := by
    have h := hweyl N a (q : ℤ) θ hN hq1' hcop hweylhyp
    simpa only [Int.cast_natCast, mul_assoc] using h
  have hqN : (q : ℝ) ≤ (N : ℝ) := by
    calc (q : ℝ) ≤ (N : ℝ) ^ η := hqNη
      _ ≤ (N : ℝ) ^ (1 : ℝ) := hNηN
      _ = (N : ℝ) := hN1'
  have hbr : ((q : ℝ)⁻¹ + (N : ℝ)⁻¹ + (q : ℝ) * (N : ℝ) ^ (-((d : ℤ)))) ≤
      3 * (q : ℝ)⁻¹ := by
    have h2 : (N : ℝ)⁻¹ ≤ (q : ℝ)⁻¹ := by
      rw [inv_le_inv₀ hNpos hqpos]; exact hqN
    have h3 : (q : ℝ) * (N : ℝ) ^ (-((d : ℤ))) ≤ (q : ℝ)⁻¹ := by
      have h4 : (N : ℝ) ^ (-((d : ℤ))) = (((N : ℝ) ^ d))⁻¹ := by
        rw [zpow_neg, zpow_natCast]
      have h6 : ((N : ℝ) ^ ((d : ℝ) / 2)) ^ 2 = (N : ℝ) ^ d := by
        rw [sq, ← Real.rpow_add hNpos, ← Real.rpow_natCast (N : ℝ) d]
        congr 1
        ring
      have h5 : (q : ℝ) ^ 2 ≤ (N : ℝ) ^ d :=
        calc (q : ℝ) ^ 2 ≤ ((N : ℝ) ^ ((d : ℝ) / 2)) ^ 2 :=
              pow_le_pow_left₀ hqpos.le hqNd 2
          _ = (N : ℝ) ^ d := h6
      rw [h4]
      have hNdpos : (0 : ℝ) < ((N : ℝ) ^ d) := by positivity
      have hstep : (↑q) ^ 2 * (((N : ℝ) ^ d))⁻¹ * ((↑q))⁻¹ ≤
          ((N : ℝ) ^ d) * (((N : ℝ) ^ d))⁻¹ * ((↑q))⁻¹ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right h5 (inv_nonneg.mpr hNdpos.le))
          (inv_nonneg.mpr hqpos.le)
      calc (↑q) * (((N : ℝ) ^ d))⁻¹
          = (↑q) ^ 2 * (((N : ℝ) ^ d))⁻¹ * ((↑q))⁻¹ := by field_simp <;> ring
        _ ≤ ((N : ℝ) ^ d) * (((N : ℝ) ^ d))⁻¹ * (((↑q)))⁻¹ := hstep
        _ = ((↑q))⁻¹ := by field_simp <;> ring
    linarith
  have hbrnn : (0 : ℝ) ≤ (q : ℝ)⁻¹ + (N : ℝ)⁻¹ + (q : ℝ) * (N : ℝ) ^ (-((d : ℤ))) := by
    positivity
  have hpow : (((q : ℝ)⁻¹ + (N : ℝ)⁻¹ + (q : ℝ) * (N : ℝ) ^ (-((d : ℤ)))) ^ t) ≤
      (3 * (q : ℝ)⁻¹) ^ t := Real.rpow_le_rpow hbrnn hbr htpos.le
  have hsplit : (3 * (q : ℝ)⁻¹) ^ t = (3 : ℝ) ^ t * (q : ℝ) ^ (-t) := by
    rw [Real.mul_rpow (by norm_num) (by positivity), Real.inv_rpow hqpos.le,
      ← Real.rpow_neg hqpos.le]
  have hqγpos : (0 : ℝ) < (N : ℝ) ^ γ := Real.rpow_pos_of_pos hNpos γ
  have hqinv : (q : ℝ) ^ (-t) ≤ ((N : ℝ) ^ γ) ^ (-t) :=
    Real.rpow_le_rpow_of_nonpos hqγpos hqγ (by linarith)
  have hqinv' : ((N : ℝ) ^ γ) ^ (-t) = (N : ℝ) ^ (-(γ * t)) :=
    (Real.rpow_mul hNpos.le γ (-t)).symm.trans (by congr 1; ring)
  have hNpow : (N : ℝ) ^ (1 + ε) * (N : ℝ) ^ (-(γ * t)) =
      (N : ℝ) ^ (1 + ε - γ * t) := by
    rw [← Real.rpow_add hNpos]
    rw [show (1 + ε) + (-(γ * t)) = 1 + ε - γ * t by ring]
  calc ‖expSum Q N θ‖
      ≤ CW * (N : ℝ) ^ (1 + ε) *
          (((q : ℝ)⁻¹ + (N : ℝ)⁻¹ + (q : ℝ) * (N : ℝ) ^ (-((d : ℤ)))) ^ t) := by
        exact hmain
    _ ≤ CW * (N : ℝ) ^ (1 + ε) * ((3 : ℝ) ^ t * (q : ℝ) ^ (-t)) := by
        rw [← hsplit]
        exact mul_le_mul_of_nonneg_left hpow (by positivity)
    _ ≤ CW * (N : ℝ) ^ (1 + ε) * ((3 : ℝ) ^ t * ((N : ℝ) ^ (-(γ * t)))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left (hqinv.trans_eq hqinv') (by positivity)
    _ = (CW * (3 : ℝ) ^ t) * (N : ℝ) ^ (1 + ε - γ * t) := by
        rw [← hNpow]; ring
    _ = (CW * (3 : ℝ) ^ ((1 : ℝ) / (2 : ℝ) ^ (Polynomial.natDegree Q - 1))) *
          (N : ℝ) ^ (1 + ε - γ / (2 : ℝ) ^ (Polynomial.natDegree Q - 1)) := by
        have hexp : γ * t = γ / (2 : ℝ) ^ (d - 1) := by rw [ht]; ring
        have h3t : (3 : ℝ) ^ t = (3 : ℝ) ^ ((1 : ℝ) / (2 : ℝ) ^ (d - 1)) := by rw [ht]
        rw [h3t, hexp, hddef]

/-- **The major arcs split into the three regions of the analysis.**  A point of `majorArcSet`
has a witness `a/q` with `q ≤ N^η`; either `q ≥ N^γ` (large-denominator region) or `q ≤ N^γ`,
and in the second case the size of `β = θ - a/q` either stays below the transition threshold
(`transitionArcSet`) or exceeds it (`deepArcSet`).  This is the set-theoretic input of the final
assembly. -/
theorem majorArcSet_subset_split (Q : Polynomial ℤ) (N : ℕ) {η γ : ℝ} (hγη : γ ≤ η) :
    majorArcSet Q N η ⊆
      largeArcSet Q N η γ ∪ (transitionArcSet Q N γ ∪ deepArcSet Q N γ) := by
  rintro θ ⟨q, a, hq1, hcop, hqη, hθ⟩
  by_cases hq : (N : ℝ) ^ γ ≤ (q : ℝ)
  · exact Or.inl ⟨q, a, hq1, hcop, hq, hqη, hθ⟩
  · push_neg at hq
    have hqγ : (q : ℝ) ≤ (N : ℝ) ^ γ := le_of_lt hq
    by_cases htr : |θ - (a : ℝ) / (q : ℝ)| * (N : ℝ) ^ Q.natDegree ≤
        ((N : ℝ) / (q : ℝ)) ^ ((Q.natDegree : ℝ) / (Q.natDegree + 1)) / 100
    · exact Or.inr (Or.inl ⟨q, a, hq1, hcop, hqγ, hθ, htr⟩)
    · push_neg at htr
      exact Or.inr (Or.inr ⟨q, a, hq1, hcop, hqγ, hθ, le_of_lt htr⟩)

end

end Work.A3
