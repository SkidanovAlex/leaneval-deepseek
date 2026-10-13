/-
Area DSCOH — `d² = 0` for the *geometric* alternating Čech differential `altCechDiff`.

The `q`-th term of the alternating Čech complex of a finite family of opens `U : ι → Opens X` with
coefficients in a presheaf `P` of `A`-modules is the product, over the `(q+1)`-element subsets `S`
of `ι`, of the sections `P (⋂_{i∈S} U i)`; `altCechDiff P U q` sends a `q`-cochain to the
`(q+1)`-cochain whose `T`-component is the alternating sum, over `i ∈ T`, of the restriction
`⋂_{i∈T∖{i}} U → ⋂_{i∈T} U` applied to the `(T∖{i})`-component, with the sign
`(-1)^{#{j ∈ T : j < i}}`.

This file proves `Work.DSCOH.altCechDiff_comp`, that two consecutive such differentials compose to
zero, so that `altCech` (the geometric alternating Čech complex) is a cochain complex.

The argument is the classical simplicial one, and is the exact transcription of the proof of
`Work.DSCOH.cechDiff_comp` for the chart Čech complex: expanding the two sums produces a double
sum over ordered pairs `(i,j)` of *distinct* elements of `T`; the map `(i,j) ↦ (j,i)` pairs the
terms, the two composites of restriction maps agree by functoriality of the presheaf `P`, and the
two signs are opposite because the position of `i` in `T` and the position of `j` in `T \ {i}`
differ from the swapped pair of positions by exactly one.  The only difference from the chart case
is that the structure maps `resAt` of the chart localizations are replaced by the restriction maps
of the presheaf `P`; since morphisms in the category of opens form a subsingleton, the inclusions
from which those restriction maps are built are irrelevant, which is what makes the functoriality
`resP_comp` below hold on the nose.
-/
import Mathlib
import Submission.Work.DSCOH.AltCech
import Submission.Work.DSCOH.negOne_pow_card_filter_erase_gen
import Submission.Work.DSCOH.sum_attach_erase_eq_sum_product
import Submission.Work.DSCOH.sum_product_swap_eq_zero

open CategoryTheory

namespace Work.DSCOH

section Restrictions

variable {X : Type*} [TopologicalSpace X]
variable {A : Type*} [CommRing A] {ι : Type*}

/-- The restriction map of the presheaf `P` along `S ⊆ T`: from the sections over
`⋂_{i∈S} U i` to the sections over `⋂_{i∈T} U i`.  This is the map that appears in the `T`-th
component of `altCechDiff P U q` for `S = T.erase i`. -/
private noncomputable def resP (P : (TopologicalSpace.Opens X)ᵒᵖ ⥤ ModuleCat A)
    (U : ι → TopologicalSpace.Opens X) {S T : Finset ι} (h : S ⊆ T) :
    P.obj (Opposite.op (S.inf U)) →ₗ[A] P.obj (Opposite.op (T.inf U)) :=
  (P.map (CategoryTheory.homOfLE (Finset.le_inf fun _ hk => Finset.inf_le (h hk))).op).hom

/-- `resP` does not depend on the proof of the inclusion (morphisms of the category of opens are
a subsingleton). -/
private lemma resP_congr (P : (TopologicalSpace.Opens X)ᵒᵖ ⥤ ModuleCat A)
    (U : ι → TopologicalSpace.Opens X) {S T : Finset ι} (h h' : S ⊆ T) :
    resP P U h = resP P U h' := by
  unfold resP
  congr 1

/-- Functoriality of the restriction maps of `P`: this is `P.map_comp` transported through the
(subsingleton) category of opens. -/
private lemma resP_comp (P : (TopologicalSpace.Opens X)ᵒᵖ ⥤ ModuleCat A)
    (U : ι → TopologicalSpace.Opens X) {S T V : Finset ι} (h₁ : S ⊆ T) (h₂ : T ⊆ V) :
    resP P U (h₁.trans h₂) = (resP P U h₂).comp (resP P U h₁) := by
  unfold resP
  rw [← ModuleCat.hom_comp, ← P.map_comp]
  congr 1

/-- Functoriality of `resP` in the form used to collapse the two composites occurring in `d²`:
`resP h₂ (resP h₁ y) = resP (h₁.trans h₂) y`. -/
private lemma resP_comp_apply (P : (TopologicalSpace.Opens X)ᵒᵖ ⥤ ModuleCat A)
    (U : ι → TopologicalSpace.Opens X) {S T V : Finset ι} (h₁ : S ⊆ T) (h₂ : T ⊆ V)
    (y : P.obj (Opposite.op (S.inf U))) :
    resP P U h₂ (resP P U h₁ y) = resP P U (h₁.trans h₂) y := by
  have h : resP P U h₂ (resP P U h₁ y) = ((resP P U h₂).comp (resP P U h₁)) y := rfl
  rw [h, ← resP_comp]

/-- `resP` is insensitive to replacing the source finset by an equal one (the two erased finsets
of an ordered pair of distinct elements agree by `Finset.erase_right_comm`). -/
private lemma resP_eq_of_eq (P : (TopologicalSpace.Opens X)ᵒᵖ ⥤ ModuleCat A)
    (U : ι → TopologicalSpace.Opens X) {S S' T : Finset ι} (hS : S = S') (h : S ⊆ T)
    (h' : S' ⊆ T) {y : P.obj (Opposite.op (S.inf U))} {y' : P.obj (Opposite.op (S'.inf U))}
    (hy : HEq y y') : resP P U h y = resP P U h' y' := by
  subst hS
  rw [eq_of_heq hy, resP_congr P U h h']

/-- Heterogeneous equality of the values of a dependent function at equal arguments. -/
private lemma heq_apply_of_eq {α : Type*} {β : α → Type*} {a b : α} (h : a = b)
    (f : (i : α) → β i) : HEq (f a) (f b) := by
  subst h
  rfl

end Restrictions

section Differential

variable {X : Type*} [TopologicalSpace X]
variable {A : Type*} [CommRing A] {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]

/-- The `T`-component of the alternating Čech differential, written with the restriction maps
`resP` of the presheaf (this is just the definition of `altCechDiff`, using
`CategoryTheory.homOfLE` in place of the map of `P`). -/
private noncomputable def altCechDiffComp (P : (TopologicalSpace.Opens X)ᵒᵖ ⥤ ModuleCat A)
    (U : ι → TopologicalSpace.Opens X) (q : ℕ)
    (T : {S : Finset ι // S.card = q + 1 + 1}) :
    AltCechTerm P U q →ₗ[A] P.obj (Opposite.op (T.1.inf U)) :=
  ∑ i ∈ T.1.attach,
    (-1 : ℤ) ^ ((T.1.filter fun j => j < i.1)).card •
      ((resP P U (Finset.erase_subset i.1 T.1)).comp
        (LinearMap.proj (R := A)
          (φ := fun S : {S : Finset ι // S.card = q + 1} => P.obj (Opposite.op (S.1.inf U)))
          ⟨T.1.erase i.1, by rw [Finset.card_erase_of_mem i.2]; omega⟩))

omit [Fintype ι] in
/-- `altCechDiff` is the product of its components `altCechDiffComp`. -/
private lemma altCechDiff_eq_pi (P : (TopologicalSpace.Opens X)ᵒᵖ ⥤ ModuleCat A)
    (U : ι → TopologicalSpace.Opens X) (q : ℕ) :
    altCechDiff P U q = LinearMap.pi (R := A) (altCechDiffComp P U q) := rfl

/-- **The alternating Čech differential squares to zero**, so that the geometric alternating Čech
complex is a cochain complex. -/
theorem altCechDiff_comp (X : Type*) [TopologicalSpace X] (A : Type*) [CommRing A]
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (P : CategoryTheory.Functor (Opposite (TopologicalSpace.Opens X)) (ModuleCat A))
    (U : ι → TopologicalSpace.Opens X) (q : ℕ) :
    (altCechDiff P U (q + 1)).comp (altCechDiff P U q) = 0 := by
  apply LinearMap.ext; intro x
  funext T
  -- Expand the outer differential, then the inner one, and push the linear maps through the
  -- sums: this produces the double sum over ordered pairs `(i,j)`, `i ∈ T`, `j ∈ T \ {i}`.
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  rw [altCechDiff_eq_pi, LinearMap.pi_apply]
  simp only [altCechDiffComp]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]
  simp only [Pi.zero_apply]
  simp only [LinearMap.proj_apply, LinearMap.pi_apply, altCechDiff_eq_pi, altCechDiffComp]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, map_sum, map_zsmul,
    LinearMap.proj_apply, resP_comp_apply]
  -- Combine the two integer coefficients acting on each summand, and the two nested sums into a
  -- single sum over the product `T × T` (the diagonal contributing zero).
  simp only [Finset.smul_sum, smul_smul]
  let pairCoeff : ι → ι → ℤ := fun i j =>
    (-1 : ℤ) ^ ((T.1.filter (fun k => k < i)).card) *
      (-1 : ℤ) ^ (((T.1.erase i).filter (fun k => k < j)).card)
  let G : (i : ι) → i ∈ T.1 → (j : ι) → j ∈ T.1.erase i → P.obj (Opposite.op (T.1.inf U)) :=
    fun i hi j hj => pairCoeff i j •
      resP P U
        ((Finset.erase_subset j (T.1.erase i)).trans (Finset.erase_subset i T.1))
        (x ⟨(T.1.erase i).erase j,
          by rw [Finset.card_erase_of_mem hj, Finset.card_erase_of_mem hi]; omega⟩)
  let f : ι × ι → P.obj (Opposite.op (T.1.inf U)) := fun p =>
    if h : p.1 ∈ T.1 ∧ p.2 ∈ T.1.erase p.1 then G p.1 h.1 p.2 h.2 else 0
  rw [sum_attach_erase_eq_sum_product (G := G)]
  show ∑ p ∈ T.1 ×ˢ T.1, f p = 0
  -- The diagonal vanishes, and the two terms of an off-diagonal pair are opposites.
  have hdiag : ∀ i ∈ T.1, f (i, i) = 0 := by
    intro i _
    show (if h : i ∈ T.1 ∧ i ∈ T.1.erase i then G i h.1 i h.2 else 0) = 0
    rw [dite_eq_right]
    rintro ⟨-, h2⟩
    exact (Finset.mem_erase.mp h2).1 rfl
  have hswap : ∀ p ∈ T.1 ×ˢ T.1, f p.swap = - f p := by
    rintro ⟨i, j⟩ hp
    have hi : i ∈ T.1 := (Finset.mem_product.mp hp).1
    have hj : j ∈ T.1 := (Finset.mem_product.mp hp).2
    show f (j, i) = - f (i, j)
    by_cases hij : i = j
    · subst hij
      rw [hdiag i hi, neg_zero]
    · have hgi : i ∈ T.1 ∧ j ∈ T.1.erase i := ⟨hi, Finset.mem_erase.mpr ⟨Ne.symm hij, hj⟩⟩
      have hgj : j ∈ T.1 ∧ i ∈ T.1.erase j := ⟨hj, Finset.mem_erase.mpr ⟨hij, hi⟩⟩
      show (if h : j ∈ T.1 ∧ i ∈ T.1.erase j then G j h.1 i h.2 else 0) =
        - (if h : i ∈ T.1 ∧ j ∈ T.1.erase i then G i h.1 j h.2 else 0)
      rw [dite_eq_left hgj, dite_eq_left hgi]
      -- The two erased finsets agree, and so do the two restriction maps applied to `x`.
      have hsub1 : (T.1.erase j).erase i ⊆ T.1 :=
        (Finset.erase_subset i (T.1.erase j)).trans (Finset.erase_subset j T.1)
      have hsub2 : (T.1.erase i).erase j ⊆ T.1 :=
        (Finset.erase_subset j (T.1.erase i)).trans (Finset.erase_subset i T.1)
      have hc1 : ((T.1.erase j).erase i).card = q + 1 := by
        rw [Finset.card_erase_of_mem hgj.2, Finset.card_erase_of_mem hgj.1]; omega
      have hc2 : ((T.1.erase i).erase j).card = q + 1 := by
        rw [Finset.card_erase_of_mem hgi.2, Finset.card_erase_of_mem hgi.1]; omega
      have hval : resP P U (S := (T.1.erase j).erase i) (T := T.1) hsub1
            (x ⟨(T.1.erase j).erase i, hc1⟩)
          = resP P U (S := (T.1.erase i).erase j) (T := T.1) hsub2
            (x ⟨(T.1.erase i).erase j, hc2⟩) := by
        have hset : (T.1.erase j).erase i = (T.1.erase i).erase j :=
          (Finset.erase_right_comm (a := i) (b := j)).symm
        have hupair : (⟨(T.1.erase j).erase i, hc1⟩ : {S : Finset ι // S.card = q + 1})
            = ⟨(T.1.erase i).erase j, hc2⟩ := Subtype.ext hset
        exact resP_eq_of_eq P U hset hsub1 hsub2 (heq_apply_of_eq hupair x)
      -- The two integer coefficients sum to zero.
      have hcoe : pairCoeff j i + pairCoeff i j = 0 :=
        negOne_pow_card_filter_erase_gen T.1 hj hi (Ne.symm hij)
      rw [show G j hgj.1 i hgj.2 = pairCoeff j i •
            resP P U (S := (T.1.erase j).erase i) (T := T.1) hsub1
              (x ⟨(T.1.erase j).erase i, hc1⟩) from rfl,
          show G i hgi.1 j hgi.2 = pairCoeff i j •
            resP P U (S := (T.1.erase i).erase j) (T := T.1) hsub2
              (x ⟨(T.1.erase i).erase j, hc2⟩) from rfl,
          hval, eq_neg_of_add_eq_zero_right hcoe, neg_smul, neg_neg]
  exact sum_product_swap_eq_zero T.1 f hswap hdiag

end Differential

end Work.DSCOH
