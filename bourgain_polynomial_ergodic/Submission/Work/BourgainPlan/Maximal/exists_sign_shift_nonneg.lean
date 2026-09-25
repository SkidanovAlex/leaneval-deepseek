import Mathlib

namespace Work.BourgainPlan.Maximal

open Filter Polynomial

/-- A real polynomial that is eventually nonnegative at `+∞` can be shifted upwards by a
nonnegative constant so as to become nonnegative on the whole of `[0, ∞)`.

Indeed, the polynomial is continuous, hence bounded below on the compact interval
`[0, max R 0]` where `R` is a threshold beyond which it is nonnegative; taking `M` to be the
maximum of `0` and the negative of the minimum on that interval does the job, and beyond the
threshold the shift is harmless because it is nonnegative. -/
lemma exists_shift_nonneg_of_eventually_nonneg (p : Polynomial ℝ)
    (hp : ∀ᶠ x in atTop, 0 ≤ p.eval x) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, 0 ≤ x → 0 ≤ (p + Polynomial.C M).eval x := by
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.mp hp
  have hR0 : (0 : ℝ) ≤ max R₀ 0 := le_max_right _ _
  obtain ⟨x₀, _hx₀, hx₀min⟩ := isCompact_Icc.exists_isMinOn (s := Set.Icc (0 : ℝ) (max R₀ 0))
      ⟨0, le_refl 0, hR0⟩ p.continuous.continuousOn
  refine ⟨max 0 (-(p.eval x₀)), le_max_left _ _, ?_⟩
  intro x hx
  rw [Polynomial.eval_add, Polynomial.eval_C]
  rcases le_total x (max R₀ 0) with hxR | hxR
  · have h1 : p.eval x₀ ≤ p.eval x := (isMinOn_iff.mp hx₀min) x ⟨hx, hxR⟩
    have h2 : -(p.eval x₀) ≤ max 0 (-(p.eval x₀)) := le_max_right _ _
    linarith
  · have h1 : 0 ≤ p.eval x := hR₀ x ((le_max_left R₀ 0).trans hxR)
    have h2 : 0 ≤ max 0 (-(p.eval x₀)) := le_max_left _ _
    linarith

/-- Every real polynomial of degree at least one can be given a sign `ε = ±1` and shifted by a
nonnegative constant `M` so that `ε q + M` is nonnegative on `[0, ∞)` without losing degree.

The sign is chosen so that the leading coefficient of `ε q` is positive; then `ε q` tends to
`+∞` at `+∞`, so it is eventually nonnegative, and the upward shift of the previous lemma
finishes. Since `q.natDegree ≥ 1`, adding a constant does not change the degree. -/
lemma exists_sign_shift_nonneg (q : Polynomial ℝ) (hdeg : 1 ≤ q.natDegree) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∃ M : ℝ, 0 ≤ M ∧
      (∀ x : ℝ, 0 ≤ x → 0 ≤ (Polynomial.C ε * q + Polynomial.C M).eval x) ∧
      1 ≤ (Polynomial.C ε * q + Polynomial.C M).natDegree := by
  have hq : q ≠ 0 := by
    intro h; rw [h] at hdeg; simp at hdeg
  have hpos : 0 < q.natDegree := hdeg
  rcases lt_trichotomy q.leadingCoeff 0 with hlt | heq | hgt
  · -- the leading coefficient is negative: flip the sign
    have hCq : (Polynomial.C (-1 : ℝ) * q) = -q := by simp
    have hlead : 0 ≤ (Polynomial.C (-1 : ℝ) * q).leadingCoeff := by
      rw [hCq, Polynomial.leadingCoeff_neg]; linarith
    have hdeg' : 0 < (Polynomial.C (-1 : ℝ) * q).degree := by
      rw [← Polynomial.natDegree_pos_iff_degree_pos,
        Polynomial.natDegree_C_mul (by norm_num : (-1 : ℝ) ≠ 0)]
      exact hpos
    obtain ⟨M, hM0, hMnn⟩ := exists_shift_nonneg_of_eventually_nonneg (Polynomial.C (-1 : ℝ) * q)
      ((Polynomial.tendsto_atTop_of_leadingCoeff_nonneg _ hdeg' hlead).eventually
        (eventually_ge_atTop 0))
    refine ⟨-1, Or.inr rfl, M, hM0, hMnn, ?_⟩
    have hnlt : (Polynomial.C M).natDegree < (Polynomial.C (-1 : ℝ) * q).natDegree := by
      rw [Polynomial.natDegree_C, Polynomial.natDegree_C_mul (by norm_num : (-1 : ℝ) ≠ 0)]
      exact hpos
    have hnd : (Polynomial.C (-1 : ℝ) * q + Polynomial.C M).natDegree = q.natDegree := by
      rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt hnlt,
        Polynomial.natDegree_C_mul (by norm_num : (-1 : ℝ) ≠ 0)]
    rw [hnd]; exact hdeg
  · exact absurd heq (Polynomial.leadingCoeff_ne_zero.mpr hq)
  · -- the leading coefficient is positive: keep `q`
    have hCq : (Polynomial.C (1 : ℝ) * q) = q := by simp
    have hlead : 0 ≤ (Polynomial.C (1 : ℝ) * q).leadingCoeff := by
      rw [hCq]; exact le_of_lt hgt
    have hdeg' : 0 < (Polynomial.C (1 : ℝ) * q).degree := by
      rw [← Polynomial.natDegree_pos_iff_degree_pos,
        Polynomial.natDegree_C_mul (by norm_num : (1 : ℝ) ≠ 0)]
      exact hpos
    obtain ⟨M, hM0, hMnn⟩ := exists_shift_nonneg_of_eventually_nonneg (Polynomial.C (1 : ℝ) * q)
      ((Polynomial.tendsto_atTop_of_leadingCoeff_nonneg _ hdeg' hlead).eventually
        (eventually_ge_atTop 0))
    refine ⟨1, Or.inl rfl, M, hM0, hMnn, ?_⟩
    have hnlt : (Polynomial.C M).natDegree < (Polynomial.C (1 : ℝ) * q).natDegree := by
      rw [Polynomial.natDegree_C, Polynomial.natDegree_C_mul (by norm_num : (1 : ℝ) ≠ 0)]
      exact hpos
    have hnd : (Polynomial.C (1 : ℝ) * q + Polynomial.C M).natDegree = q.natDegree := by
      rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt hnlt,
        Polynomial.natDegree_C_mul (by norm_num : (1 : ℝ) ≠ 0)]
    rw [hnd]; exact hdeg

end Work.BourgainPlan.Maximal
