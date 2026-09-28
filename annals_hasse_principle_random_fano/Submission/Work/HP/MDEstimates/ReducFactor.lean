import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.Q44Geom.ReducDefs
import Submission.Work.Q44Geom.isUnit_of_isHomogeneous_zero

/-!
# Reducible quartics over `ℚ` factor into homogeneous factors of degrees `1 + 3` or `2 + 2`

If `P = formOf 4 4 c` is reducible over `ℚ`, we extract two non-unit factors `A * B = P`.  Over an
integral domain a factor of a homogeneous polynomial is again homogeneous: if `A * B` is
homogeneous of degree `n` and `A, B ≠ 0`, then the lowest-degree parts and the highest-degree
parts of `A` and `B` multiply to nonzero homogeneous parts of `A * B`, both of which must sit in
degree `n`; squeezing forces `A` and `B` themselves to be homogeneous, with degrees summing to
`n` (`isHomogeneous_of_mul_eq`).

Since `formOf 4 4 c` has degree `4` and is neither zero nor a unit, the two degrees are positive
and add up to `4`: they are `1 + 3` or `2 + 2`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MvPolynomial Finset

namespace Work.HP.MDEstimates

open Work.HP

namespace ReducFactor

/-! ## Highest degrees -/

/-- `IsMaxDeg r P`: `r` is the largest degree of a monomial occurring in `P`. -/
def IsMaxDeg {R : Type*} [CommSemiring R] (r : ℕ) (P : MvPolynomial (Fin 5) R) : Prop :=
  (∃ t ∈ P.support, t.degree = r) ∧ (∀ t ∈ P.support, t.degree ≤ r)

lemma exists_isMaxDeg {R : Type*} [CommSemiring R] (P : MvPolynomial (Fin 5) R) (hP : P ≠ 0) :
    ∃ r, IsMaxDeg r P := by
  have hne : P.support.Nonempty := Finset.nonempty_iff_ne_empty.mpr fun h => hP (by
    rw [MvPolynomial.as_sum P, h]; simp)
  let F : Finset ℕ := P.support.image (fun t : Fin 5 →₀ ℕ => t.degree)
  have hFne : F.Nonempty := hne.image _
  refine ⟨F.max' hFne, ?_, ?_⟩
  · obtain ⟨t, ht, hts⟩ := Finset.mem_image.mp (Finset.max'_mem F hFne)
    exact ⟨t, ht, hts⟩
  · intro t ht
    exact Finset.le_max' F t.degree (Finset.mem_image.mpr ⟨t, ht, rfl⟩)

lemma IsMaxDeg.coeff_ne_zero {R : Type*} [CommSemiring R] {r : ℕ} {P : MvPolynomial (Fin 5) R}
    (h : IsMaxDeg r P) : (MvPolynomial.homogeneousComponent r P) ≠ 0 := by
  obtain ⟨t, ht, htr⟩ := h.1
  intro h0
  have h1 : (MvPolynomial.homogeneousComponent r P).coeff t = 0 := by rw [h0]; simp
  rw [MvPolynomial.coeff_homogeneousComponent, if_pos htr] at h1
  exact (MvPolynomial.mem_support_iff.mp ht) h1

/-- The highest-degree part of a product is the product of the highest-degree parts. -/
lemma homogeneousComponent_mul_of_maxDeg {R : Type*} [CommSemiring R]
    {a b : MvPolynomial (Fin 5) R} {r s : ℕ} (ha : IsMaxDeg r a) (hb : IsMaxDeg s b) :
    MvPolynomial.homogeneousComponent (r + s) (a * b)
      = MvPolynomial.homogeneousComponent r a * MvPolynomial.homogeneousComponent s b := by
  refine MvPolynomial.ext _ _ fun T => ?_
  rw [MvPolynomial.coeff_homogeneousComponent, MvPolynomial.coeff_mul, MvPolynomial.coeff_mul]
  by_cases hT : T.degree = r + s
  · rw [if_pos hT]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx' : x.1 + x.2 = T := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    have hdeg : x.1.degree + x.2.degree = r + s := by
      rw [← hT, ← hx', map_add]
    rw [MvPolynomial.coeff_homogeneousComponent, MvPolynomial.coeff_homogeneousComponent]
    by_cases h1 : a.coeff x.1 = 0
    · simp [h1]
    · by_cases h2 : b.coeff x.2 = 0
      · simp [h2]
      · have hx1 : x.1 ∈ a.support := MvPolynomial.mem_support_iff.mpr h1
        have hle1 : x.1.degree ≤ r := ha.2 x.1 hx1
        have hx2 : x.2 ∈ b.support := MvPolynomial.mem_support_iff.mpr h2
        have hle2 : x.2.degree ≤ s := hb.2 x.2 hx2
        have e1 : x.1.degree = r := by omega
        have e2 : x.2.degree = s := by omega
        rw [if_pos e1, if_pos e2]
  · rw [if_neg hT]
    have hzero : (∑ x ∈ Finset.HasAntidiagonal.antidiagonal T,
        (MvPolynomial.homogeneousComponent r a).coeff x.1
          * (MvPolynomial.homogeneousComponent s b).coeff x.2) = 0 := by
      rw [Finset.sum_eq_zero]
      intro x hx
      have hx' : x.1 + x.2 = T := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
      have hdeg : x.1.degree + x.2.degree = T.degree := by rw [← hx', map_add]
      rw [MvPolynomial.coeff_homogeneousComponent, MvPolynomial.coeff_homogeneousComponent]
      by_cases h1 : x.1.degree = r
      · have h2 : x.2.degree ≠ s := by omega
        rw [if_pos h1, if_neg h2, mul_zero]
      · rw [if_neg h1, zero_mul]
    rw [hzero]

/-! ## Factors of a homogeneous polynomial are homogeneous -/

/-- Over an integral domain, both factors of a nonzero homogeneous product are homogeneous,
with degrees adding up to the degree of the product. -/
theorem isHomogeneous_of_mul_eq {n : ℕ} {P A B : MvPolynomial (Fin 5) ℚ}
    (hP : P.IsHomogeneous n) (hAB : P = A * B) (hA : A ≠ 0) (hB : B ≠ 0) :
    ∃ i j : ℕ, i + j = n ∧ A.IsHomogeneous i ∧ B.IsHomogeneous j := by
  -- lowest degrees
  obtain ⟨i, hi⟩ := Work.Q44Geom.exists_isMinDeg A hA
  obtain ⟨j, hj⟩ := Work.Q44Geom.exists_isMinDeg B hB
  have hmem : P ∈ MvPolynomial.homogeneousSubmodule (Fin 5) ℚ n :=
    (MvPolynomial.mem_homogeneousSubmodule n P).mpr hP
  have hmin : i + j = n := by
    by_contra h
    have hne : MvPolynomial.homogeneousComponent (i + j) (A * B) ≠ 0 := by
      rw [Work.Q44Geom.homogeneousComponent_mul_of_minDeg hi hj]
      exact mul_ne_zero (Work.Q44Geom.IsMinDeg.coeff_ne_zero hi)
        (Work.Q44Geom.IsMinDeg.coeff_ne_zero hj)
    rw [← hAB, MvPolynomial.homogeneousComponent_of_mem hmem, if_neg h] at hne
    exact hne rfl
  -- highest degrees
  obtain ⟨a, ha⟩ := exists_isMaxDeg A hA
  obtain ⟨b, hb⟩ := exists_isMaxDeg B hB
  have hmax : a + b = n := by
    by_contra h
    have hne : MvPolynomial.homogeneousComponent (a + b) (A * B) ≠ 0 := by
      rw [homogeneousComponent_mul_of_maxDeg ha hb]
      exact mul_ne_zero ha.coeff_ne_zero hb.coeff_ne_zero
    rw [← hAB, MvPolynomial.homogeneousComponent_of_mem hmem, if_neg h] at hne
    exact hne rfl
  -- squeeze: the extreme degrees coincide
  have hia : i ≤ a := by
    obtain ⟨t, ht, htr⟩ := hi.1
    rw [← htr]
    exact ha.2 t ht
  have hjb : j ≤ b := by
    obtain ⟨t, ht, htr⟩ := hj.1
    rw [← htr]
    exact hb.2 t ht
  have hia' : i = a := by omega
  have hjb' : j = b := by omega
  -- both factors are squeezed into a single degree
  have homA : A.IsHomogeneous i := by
    have heq : A = MvPolynomial.homogeneousComponent i A := by
      ext d
      rw [MvPolynomial.coeff_homogeneousComponent]
      by_cases hd : A.coeff d = 0
      · simp [hd]
      · have h1 : i ≤ d.degree := hi.2 d (MvPolynomial.mem_support_iff.mpr hd)
        have h2 : d.degree ≤ i := by
          have h3 := ha.2 d (MvPolynomial.mem_support_iff.mpr hd)
          omega
        rw [if_pos (le_antisymm h2 h1)]
    rw [heq]
    exact MvPolynomial.homogeneousComponent_isHomogeneous i A
  have homB : B.IsHomogeneous j := by
    have heq : B = MvPolynomial.homogeneousComponent j B := by
      ext d
      rw [MvPolynomial.coeff_homogeneousComponent]
      by_cases hd : B.coeff d = 0
      · simp [hd]
      · have h1 : j ≤ d.degree := hj.2 d (MvPolynomial.mem_support_iff.mpr hd)
        have h2 : d.degree ≤ j := by
          have h3 := hb.2 d (MvPolynomial.mem_support_iff.mpr hd)
          omega
        rw [if_pos (le_antisymm h2 h1)]
    rw [heq]
    exact MvPolynomial.homogeneousComponent_isHomogeneous j B
  exact ⟨i, j, hmin, homA, homB⟩

/-! ## The degree split of a reducible quartic -/

/-- A reducible quartic form in `5` variables is a product of two homogeneous forms, of degrees
`1` and `3`, or of degrees `2` and `2`. -/
theorem exists_homogeneous_factor (c : Mon 4 4 → ℤ) (hc : c ≠ 0)
    (hred : ¬ Irreducible (formOf 4 4 c)) :
    (∃ A B : MvPolynomial (Fin 5) ℚ, A.IsHomogeneous 1 ∧ B.IsHomogeneous 3 ∧ A ≠ 0 ∧ B ≠ 0 ∧
        formOf 4 4 c = A * B)
    ∨ (∃ A B : MvPolynomial (Fin 5) ℚ, A.IsHomogeneous 2 ∧ B.IsHomogeneous 2 ∧ A ≠ 0 ∧ B ≠ 0 ∧
        formOf 4 4 c = A * B) := by
  have hne : formOf 4 4 c ≠ 0 := fun h => hc ((formOf_eq_zero_iff (d := 4) (n := 4) c).mp h)
  have hP : (formOf 4 4 c).IsHomogeneous 4 := by
    rw [Work.Q44Geom.formOf_eq_polyOfR]
    exact Work.Q44Geom.isHomogeneous_polyOfR _
  have hnotunit : ¬ IsUnit (formOf 4 4 c) := by
    intro h
    rw [MvPolynomial.isUnit_iff_totalDegree_of_isReduced] at h
    have h4 := hP.totalDegree hne
    have h0 := h.2
    omega
  obtain ⟨A, B, hAnu, hBnu, hAB⟩ := (irreducible_or_factor hnotunit).resolve_left hred
  have hABne : A * B ≠ 0 := by rw [← hAB]; exact hne
  have hA : A ≠ 0 := (mul_ne_zero_iff.mp hABne).1
  have hB : B ≠ 0 := (mul_ne_zero_iff.mp hABne).2
  obtain ⟨i, j, hij, hAi, hBj⟩ := isHomogeneous_of_mul_eq hP hAB hA hB
  have hi1 : 1 ≤ i := by
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · refine absurd ?_ hAnu
      rw [h0] at hAi
      exact Work.Q44Geom.isUnit_of_isHomogeneous_zero hAi hA
    · exact hpos
  have hj1 : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · refine absurd ?_ hBnu
      rw [h0] at hBj
      exact Work.Q44Geom.isUnit_of_isHomogeneous_zero hBj hB
    · exact hpos
  have hi3 : i ≤ 3 := by omega
  interval_cases i
  · -- degrees `1` and `3`
    have hj : j = 3 := by omega
    exact Or.inl ⟨A, B, hAi, hj ▸ hBj, hA, hB, hAB⟩
  · -- degrees `2` and `2`
    have hj : j = 2 := by omega
    exact Or.inr ⟨A, B, hAi, hj ▸ hBj, hA, hB, hAB⟩
  · -- degrees `3` and `1`; swap the factors
    have hj : j = 1 := by omega
    exact Or.inl ⟨B, A, hj ▸ hBj, hAi, hB, hA, by rw [hAB, mul_comm]⟩

end ReducFactor

end Work.HP.MDEstimates
