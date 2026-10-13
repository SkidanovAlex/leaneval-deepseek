import Mathlib
import Submission.Work.WilE2.atomSetDefs

set_option autoImplicit false

namespace Work.WilE2

open Classical
open WilkiesDesign WilkiesDesign.E

noncomputable section

/-!
  ## Degree bookkeeping for the single-atom set

  `atomSet c B` is the positive set of the product atom `G = ∏ B.pos` over the equation family
  `B.eqs`.  Here we show that the degree datum of that object — the sum of the atom degrees of the
  equation family together with those of `G` and of any level atom `G - δ` — never exceeds
  `B.deg + 1`, which is what makes the polynomial accounting in the final assembly possible.
-/

/-- The atom degree of a list product is bounded by the sum of the atom degrees, as soon as the
list is non-empty (the `+1`'s are what pay for the `+1` of the product). -/
theorem atomDeg_list_prod_le {k r : ℕ} (l : List (EAPoly k r)) (hne : l ≠ []) :
    atomDeg l.prod ≤ (l.map atomDeg).sum := by
  have h1 : (l.prod).totalDegree ≤ (l.map (fun g => g.totalDegree)).sum :=
    MvPolynomial.totalDegree_list_prod l
  have h2 : ∀ l : List (EAPoly k r),
      (l.map (fun g => atomDeg g)).sum = (l.map (fun g => g.totalDegree)).sum + l.length := by
    intro l
    induction l with
    | nil => simp
    | cons a t ih =>
      have hatom : atomDeg a = a.totalDegree + 1 := rfl
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [hatom, ih]
      ring
  have h3 : 1 ≤ l.length := by
    cases l with
    | nil => exact absurd rfl hne
    | cons a t => simp
  have hatom : atomDeg l.prod = l.prod.totalDegree + 1 := rfl
  rw [h2 l, hatom]
  omega

/-- Subtracting a constant does not raise the atom degree. -/
theorem atomDeg_sub_C_le {k r : ℕ} (P : EAPoly k r) (a : ℝ) :
    atomDeg (P - MvPolynomial.C a) ≤ atomDeg P := by
  have h : (P - MvPolynomial.C a).totalDegree ≤ P.totalDegree := by
    refine (MvPolynomial.totalDegree_sub _ _).trans ?_
    rw [MvPolynomial.totalDegree_C]
    exact max_le le_rfl (Nat.zero_le _)
  exact Nat.add_le_add_right h 1

/-- The sum over the `Finset` underlying a list is at most the sum over the list (each element of
the `Finset` occurs at least once in the list). -/
theorem list_toFinset_sum_le {α : Type*} [DecidableEq α] (l : List α) (f : α → ℕ) :
    l.toFinset.sum f ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.toFinset_cons, List.map_cons, List.sum_cons]
    by_cases ha : a ∈ t.toFinset
    · rw [Finset.insert_eq_of_mem ha]
      exact le_trans ih (Nat.le_add_left _ _)
    · rw [Finset.sum_insert ha]
      exact Nat.add_le_add_left ih (f a)

/-- The degree datum of the single-atom set of a basic set, never exceeding `B.deg + 1`. -/
theorem atomSet_degree_le {k r : ℕ} (B : Basic k r) :
    (∑ h ∈ B.eqs.toFinset, atomDeg h) + atomDeg (posProd B) ≤ Basic.deg B + 1 := by
  have h1 : (∑ h ∈ B.eqs.toFinset, atomDeg h) ≤ (B.eqs.map atomDeg).sum :=
    list_toFinset_sum_le B.eqs atomDeg
  have hdegeq : Basic.deg B = (B.eqs.map atomDeg).sum + (B.pos.map atomDeg).sum := by
    rw [show Basic.deg B = ((B.eqs ++ B.pos).map atomDeg).sum from rfl, List.map_append,
      List.sum_append]
  rw [hdegeq]
  by_cases hpos : B.pos = []
  · have h4 : atomDeg (posProd B) = 1 := by
      have hpt : posProd B = 1 := by simp [posProd, hpos]
      rw [hpt, atomDeg, MvPolynomial.totalDegree_one]
    have h6 : (B.pos.map atomDeg).sum = 0 := by rw [hpos]; simp
    omega
  · have h5 : atomDeg (posProd B) ≤ (B.pos.map atomDeg).sum := atomDeg_list_prod_le B.pos hpos
    omega

/-- The single-atom set of a basic set is the positive set of the product atom over the equation
family. -/
theorem atomSet_eq_posVarietySet {k r : ℕ} (c : EAChain k r) (B : Basic k r) :
    atomSet c B = cubeC k ∩ Zset c B.eqs.toFinset ∩ {x | 0 < eaEval c (posProd B) x} := by
  ext x
  simp only [atomSet, Set.mem_setOf_eq, Set.mem_inter_iff, Zset, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, fun f hf => h2 f (List.mem_toFinset.mp hf)⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, fun f hf => h2 f (List.mem_toFinset.mpr hf), h3⟩

end

end Work.WilE2
