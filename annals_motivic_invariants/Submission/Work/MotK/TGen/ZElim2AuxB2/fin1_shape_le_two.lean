import Mathlib
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotK.TGen.ZElim2AuxB2

open MvPolynomial

/-- A finitely supported function on `Fin 1` is determined by its value at `0`. -/
lemma fin1_eq_single_iff (m : Fin 1 →₀ ℕ) (n : ℕ) :
    m = Finsupp.single (0 : Fin 1) n ↔ m 0 = n := by
  constructor
  · intro h
    rw [h, Finsupp.single_eq_same]
  · intro h
    apply Finsupp.ext
    intro i
    rw [Subsingleton.elim i (0 : Fin 1), Finsupp.single_eq_same]
    exact h

/-- A finitely supported function on `Fin 1` vanishes iff it vanishes at `0`. -/
lemma fin1_eq_zero_iff (m : Fin 1 →₀ ℕ) : m = 0 ↔ m 0 = 0 := by
  constructor
  · intro h; rw [h]; rfl
  · intro h
    have := (fin1_eq_single_iff m 0).mpr h
    rwa [Finsupp.single_zero] at this

/-- Every polynomial of total degree at most two in a single variable is of the form
`a X² + b X + c`. -/
theorem fin1_shape_le_two {L : Type*} [Field L] (p : MvPolynomial (Fin 1) L) (h : p.totalDegree ≤ 2) :
    ∃ a b c : L, p = MvPolynomial.C a * (MvPolynomial.X 0) ^ 2 + MvPolynomial.C b * MvPolynomial.X 0 + MvPolynomial.C c := by
  classical
  have hsupp : ∀ m ∈ p.support, m 0 ≤ 2 :=
    MvPolynomial.degreeOf_le_iff.mp
      ((MvPolynomial.degreeOf_le_totalDegree p 0).trans h)
  refine ⟨p.coeff (Finsupp.single (0 : Fin 1) 2),
          p.coeff (Finsupp.single (0 : Fin 1) 1), p.coeff 0, ?_⟩
  rw [MvPolynomial.C_mul_X_pow_eq_monomial, MvPolynomial.C_mul_X_eq_monomial]
  apply MvPolynomial.ext
  intro m
  have hc : ∀ n : ℕ, (Finsupp.single (0 : Fin 1) n = m) ↔ (m 0 = n) := by
    intro n
    exact ⟨fun hh => (fin1_eq_single_iff m n).mp hh.symm,
           fun hh => ((fin1_eq_single_iff m n).mpr hh).symm⟩
  have h0c : ((0 : Fin 1 →₀ ℕ) = m) ↔ (m 0 = 0) := by
    constructor
    · intro hh; rw [← hh]; simp
    · intro hh
      have h1 : m = Finsupp.single (0 : Fin 1) 0 := (fin1_eq_single_iff m 0).mpr hh
      rw [h1, Finsupp.single_zero]
  simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_monomial, MvPolynomial.coeff_C,
    hc 2, hc 1, h0c]
  rcases Nat.lt_or_ge (m 0) 3 with hlt | hge
  · rcases (by omega : m 0 = 0 ∨ m 0 = 1 ∨ m 0 = 2) with h0 | h1 | h2
    · rw [if_neg (show ¬ (m 0 = 2) by omega), if_neg (show ¬ (m 0 = 1) by omega),
        if_pos h0]
      have hm : m = 0 := (fin1_eq_zero_iff m).mpr h0
      rw [hm]
      first | refl_ring1 | ring
    · rw [if_neg (show ¬ (m 0 = 2) by omega), if_pos h1,
        if_neg (show ¬ (m 0 = 0) by omega)]
      have hm : m = Finsupp.single (0 : Fin 1) 1 := (fin1_eq_single_iff m 1).mpr h1
      rw [hm]
      first | refl_ring1 | ring
    · rw [if_pos h2, if_neg (show ¬ (m 0 = 1) by omega),
        if_neg (show ¬ (m 0 = 0) by omega)]
      have hm : m = Finsupp.single (0 : Fin 1) 2 := (fin1_eq_single_iff m 2).mpr h2
      rw [hm]
      first | refl_ring1 | ring
  · rw [if_neg (show ¬ (m 0 = 2) by omega), if_neg (show ¬ (m 0 = 1) by omega),
      if_neg (show ¬ (m 0 = 0) by omega)]
    have hnot : m ∉ p.support := fun hmem => by
      have := hsupp m hmem
      omega
    rw [MvPolynomial.notMem_support_iff.mp hnot]
    first | refl_ring1 | ring

end Work.MotK.TGen.ZElim2AuxB2
