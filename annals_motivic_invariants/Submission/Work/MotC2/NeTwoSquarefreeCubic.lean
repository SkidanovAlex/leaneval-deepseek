import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC2

/-- A cubic over a field with no double root is squarefree.  (`Squarefree p` is Mathlib's
`∀ a, a * a ∣ p → IsUnit a`.)  Proof route: suppose `a * a ∣ p`, `a` not a unit.  Then `a ≠ 0`
(as `p ≠ 0`), and `2 * a.natDegree = (a * a).natDegree ≤ p.natDegree = 3`, so `a.natDegree = 1`;
`deg = 1` gives `a = c * (X - α)` with `c ≠ 0`, hence `(X - α) ^ 2 ∣ p`, so `p.eval α = 0` and
`p.derivative.eval α = 0`, contradiction. -/
lemma NeTwoSquarefreeCubic {K : Type*} [Field K] (p : Polynomial K) (hp : p.natDegree = 3)
    (h : ∀ α : K, ¬ (p.eval α = 0 ∧ p.derivative.eval α = 0)) : Squarefree p := by
  intro a ha
  by_contra hnu
  -- `p ≠ 0` since it has degree `3`.
  have hp0 : p ≠ 0 := by
    intro h0
    rw [h0, Polynomial.natDegree_zero] at hp
    exact absurd hp (by norm_num)
  -- `a ≠ 0` since `a * a` is a nonzero divisor of `p`.
  have haa0 : a * a ≠ 0 := ne_zero_of_dvd_ne_zero hp0 ha
  have ha0 : a ≠ 0 := by intro h0; exact haa0 (by rw [h0, mul_zero])
  -- Degree count: `2 * a.natDegree = (a * a).natDegree ≤ p.natDegree = 3`.
  have hdeg : 2 * a.natDegree ≤ 3 := by
    have h1 : (a * a).natDegree = a.natDegree + a.natDegree := Polynomial.natDegree_mul ha0 ha0
    have h2 : (a * a).natDegree ≤ p.natDegree := Polynomial.natDegree_le_of_dvd ha hp0
    rw [hp] at h2
    omega
  -- `a` is not a unit, so `a.natDegree ≠ 0`; hence `a.natDegree = 1`.
  have ha1 : a.natDegree = 1 := by
    have hle : a.natDegree ≤ 1 := by omega
    have hne : a.natDegree ≠ 0 := by
      intro h0
      have hd : a.degree = 0 := by
        rw [Polynomial.degree_eq_natDegree ha0, h0]
        simp
      exact hnu ((Polynomial.isUnit_iff_degree_eq_zero).mpr hd)
    omega
  -- So `a` is linear, hence has a root `α` and `X - C α` divides `a`.
  have hda : a.degree = 1 := by
    rw [Polynomial.degree_eq_natDegree ha0, ha1]
    norm_num
  obtain ⟨α, hα⟩ := Polynomial.exists_root_of_degree_eq_one hda
  have hdvd : Polynomial.X - Polynomial.C α ∣ a := Polynomial.dvd_iff_isRoot.mpr hα
  -- Hence `(X - C α) ^ 2 ∣ a * a ∣ p`, so `α` is a double root of `p`.
  have hsq : (Polynomial.X - Polynomial.C α) ^ 2 ∣ p := by
    have h1 : (Polynomial.X - Polynomial.C α) ^ 2 ∣ a * a := by
      rw [sq]
      exact mul_dvd_mul hdvd hdvd
    exact h1.trans ha
  have hlt : 1 < p.rootMultiplicity α := by
    have := (Polynomial.le_rootMultiplicity_iff hp0).mpr hsq
    omega
  obtain ⟨hr, hdr⟩ := (Polynomial.one_lt_rootMultiplicity_iff_isRoot hp0).mp hlt
  exact h α ⟨hr, hdr⟩

end Work.MotC2
