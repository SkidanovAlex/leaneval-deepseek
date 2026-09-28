import Mathlib
import Submission.Work.Q44Geom.ReducDefs

/-!
# Maximal degrees of multivariate polynomials

Companion to `Work.Q44Geom.IsMinDeg` (in `Q44Geom/ReducDefs`): `IsMaxDeg a P` says that `a` is
the largest degree of a monomial occurring in `P` (and that such a monomial exists).

Also contains the elementary "squeeze" fact: a polynomial all of whose monomials have degree `i`
is homogeneous of degree `i`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MvPolynomial Finset

namespace Work.Q44Geom

/-- `IsMaxDeg a P` says that `a` is the largest degree of a monomial occurring in `P`
(and that such a monomial exists). -/
def IsMaxDeg {R : Type*} [CommSemiring R] (a : ℕ) (P : MvPolynomial (Fin 5) R) : Prop :=
  (∃ t ∈ P.support, t.degree = a) ∧ (∀ t ∈ P.support, t.degree ≤ a)

lemma exists_isMaxDeg {R : Type*} [CommSemiring R] (P : MvPolynomial (Fin 5) R) (hP : P ≠ 0) :
    ∃ a, IsMaxDeg a P := by
  have hne : P.support.Nonempty := Finset.nonempty_iff_ne_empty.mpr fun h => hP (by
    rw [MvPolynomial.as_sum P, h]; simp)
  let F : Finset ℕ := P.support.image (fun t : Fin 5 →₀ ℕ => t.degree)
  have hFne : F.Nonempty := hne.image _
  refine ⟨F.max' hFne, ?_, ?_⟩
  · obtain ⟨t, ht, hts⟩ := Finset.mem_image.mp (Finset.max'_mem F hFne)
    exact ⟨t, ht, hts⟩
  · intro t ht
    exact Finset.le_max' F t.degree (Finset.mem_image.mpr ⟨t, ht, rfl⟩)

lemma IsMaxDeg.ne_zero {R : Type*} [CommSemiring R] {a : ℕ} {P : MvPolynomial (Fin 5) R}
    (h : IsMaxDeg a P) : P ≠ 0 := by
  intro h0
  rw [h0] at h
  obtain ⟨t, ht, _⟩ := h.1
  simpa using ht

lemma IsMaxDeg.coeff_ne_zero {R : Type*} [CommSemiring R] {a : ℕ} {P : MvPolynomial (Fin 5) R}
    (h : IsMaxDeg a P) : (MvPolynomial.homogeneousComponent a P) ≠ 0 := by
  obtain ⟨t, ht, hta⟩ := h.1
  intro h0
  have h1 : (MvPolynomial.homogeneousComponent a P).coeff t = 0 := by rw [h0]; simp
  rw [MvPolynomial.coeff_homogeneousComponent, if_pos hta] at h1
  exact (MvPolynomial.mem_support_iff.mp ht) h1

/-- The minimal degree is at most the maximal degree. -/
lemma IsMinDeg.le_maxDeg {R : Type*} [CommSemiring R] {i a : ℕ} {P : MvPolynomial (Fin 5) R}
    (hi : IsMinDeg i P) (ha : IsMaxDeg a P) : i ≤ a := by
  obtain ⟨t, ht, htr⟩ := hi.1
  rw [← htr]
  exact ha.2 t ht

/-- If every monomial of `P` has degree at most `i` and `i` is the minimal degree of `P`, then
`P` is homogeneous of degree `i`. -/
lemma IsMinDeg.isHomogeneous_of_forall_le {R : Type*} [CommSemiring R] {i : ℕ}
    {P : MvPolynomial (Fin 5) R} (hi : IsMinDeg i P)
    (hle : ∀ t ∈ P.support, t.degree ≤ i) : P.IsHomogeneous i := by
  have heq : P = MvPolynomial.homogeneousComponent i P := by
    ext d
    rw [MvPolynomial.coeff_homogeneousComponent]
    by_cases hd : P.coeff d = 0
    · simp [hd]
    · have h1 : i ≤ d.degree := hi.2 d (MvPolynomial.mem_support_iff.mpr hd)
      have h2 : d.degree ≤ i := hle d (MvPolynomial.mem_support_iff.mpr hd)
      rw [if_pos (le_antisymm h2 h1)]
  rw [heq]
  exact MvPolynomial.homogeneousComponent_isHomogeneous i P

end Work.Q44Geom
