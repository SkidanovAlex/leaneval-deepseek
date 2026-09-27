import Mathlib
import Submission.Work.EKLC6Core.growth_le_HcondSig
import Submission.Work.EKLContract.All
import Submission.Work.EKLC6Core.shape_comap_conj
import Submission.Work.EKLC6Core.conjBy_neg_inter_U
import Submission.Work.EKLC6Core.conjBox_nhds

/-!
# Pulling a plaque algebra back along the diagonal flow

`IsPlaqueAlgebra U Z m` says that `m` is a countably generated sub-σ-algebra of the Borel one
with `Z ∈ m`, whose atoms on `Z` are bounded open `U`-plaques contained in `Z`
(Pisa Def. 6.2 / Thm 6.3(iv), frozen in `EKLContract/Defs.lean`).

Since `aDiag t` normalises `U` (`IsHoro U`), the map `φ y = aDiag t • y` carries a plaque
algebra for `U` on `Z` to a plaque algebra for `U` on `φ ⁻¹' Z`, with σ-algebra
`comap φ m`.  Concretely (`Work.EKLContract.aDiag` and `Work.EKLC6Core.conjBy`):

* `m ≤ borel` pulls back because `φ` is continuous (hence Borel measurable);
* a countable generating family pulls back to a countable generating family
  (`MeasurableSpace.comap_generateFrom`);
* `MeasurableSet[comap φ m] (φ ⁻¹' Z)` holds by definition of `comap`;
* `atom (comap φ m) x = φ ⁻¹' atom m (φ x)` (`Work.EKLComp.atom_comap`) — no hypothesis on `φ`;
* the shape transports by conjugation
  (`Work.EKLC6Core.shape_comap_conj`, Pisa 7.17):
  `shape (comap φ m) U x = conjBy (-t) (shape m U (φ x))`,
  so a shape which is `O ∩ U` with `O` open becomes `conjBy (-t) O ∩ U`
  (`Work.EKLC6Core.conjBy_neg_inter_U`), again open since conjugation is continuous, and an
  entrywise bounded shape stays entrywise bounded (`conjBy_neg_entries_le`, using the scalar
  action of the diagonal flow on matrix entries, `Work.EKLC6Core.aDiag_conj_entry`);
* the atom clause `atom ⊆ Z` transports by preimage, and the orbit clause
  `atom ⊆ (u ↦ u • ·) '' U` transports because `φ` is injective and equivariant for the
  normalisation `aDiag t · U · (aDiag t)⁻¹ = U` (the `A`-normalisation field of `IsHoro`).

This is the `descending` step of Pisa 7.17 used to build the *descending* plaque algebra
`A = ⨆_n comap ((aDiag t)·)^[n] M` (`EKLC6Core/exists_gen_partition.lean`,
`EKLC6Core/exists_desc_plaque_algebra.lean`).
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-! ## Auxiliary facts about conjugation by the diagonal flow -/

/-- Borel measurability of the diagonal action on `X₃`.  Stated at the top level so that the
`MeasurableSpace X₃` instances are the Borel ones: inside a proof that binds a local hypothesis
`A : MeasurableSpace X₃`, typeclass search would otherwise capture `A`. -/
theorem measurable_const_smul_aDiag (t : Fin 3 → ℝ) :
    Measurable (fun y : X3 => aDiag t • y) :=
  (continuous_const_smul (aDiag t)).measurable

/-- Membership in the `aDiag (-t)`-conjugate of a set. -/
theorem mem_conjBy_neg {t : Fin 3 → ℝ} {S : Set SL3} {g : SL3} :
    g ∈ conjBy (-t) S ↔ aDiag t * g * (aDiag t)⁻¹ ∈ S := by
  rw [conjBy, Set.mem_image]
  constructor
  · rintro ⟨w, hw, rfl⟩
    have h : aDiag t * (aDiag (-t) * w * (aDiag (-t))⁻¹) * (aDiag t)⁻¹ = w := by
      rw [aDiag_neg_eq_inv]; group
    rw [h]; exact hw
  · intro hg
    refine ⟨aDiag t * g * (aDiag t)⁻¹, hg, ?_⟩
    show aDiag (-t) * (aDiag t * g * (aDiag t)⁻¹) * (aDiag (-t))⁻¹ = g
    rw [aDiag_neg_eq_inv]; group

/-- `conjBy (-t) S` described by the membership predicate of conjugation by `aDiag t`. -/
theorem conjBy_neg_eq_setOf (t : Fin 3 → ℝ) (S : Set SL3) :
    conjBy (-t) S = {g : SL3 | aDiag t * g * (aDiag t)⁻¹ ∈ S} := by
  ext g
  rw [Set.mem_ofPred_eq]
  exact mem_conjBy_neg

/-- **Boundedness of a conjugated set**: conjugation by `aDiag (-t)` multiplies the entries of a
matrix by the exponential factors `e^{tⱼ - tᵢ}`, so it keeps entrywise bounds. -/
theorem conjBy_neg_entries_le {t : Fin 3 → ℝ} {S : Set SL3} {C : ℝ}
    (h : ∀ g ∈ S, ∀ i j, |g i j| ≤ C) :
    ∃ C' : ℝ, ∀ g ∈ conjBy (-t) S, ∀ i j, |g i j| ≤ C' := by
  refine ⟨|C| * (∑ i : Fin 3, ∑ j : Fin 3, Real.exp (t j - t i)), ?_⟩
  intro g hg i j
  rw [conjBy, Set.mem_image] at hg
  obtain ⟨w, hw, hw2⟩ := hg
  subst hw2
  have hentry : (aDiag (-t) * w * (aDiag (-t))⁻¹) i j = Real.exp (t j - t i) * w i j := by
    rw [← aDiag_neg_eq_inv (-t), neg_neg]
    exact aDiag_conj_entry t w i j
  rw [hentry, abs_mul, Real.abs_exp]
  have hb : |w i j| ≤ |C| := le_trans (h w hw i j) (le_abs_self C)
  have hsum : Real.exp (t j - t i) ≤ ∑ i' : Fin 3, ∑ j' : Fin 3, Real.exp (t j' - t i') := by
    refine le_trans ?_ (Finset.single_le_sum
      (f := fun i' : Fin 3 => ∑ j' : Fin 3, Real.exp (t j' - t i'))
      (fun i' _ => Finset.sum_nonneg (fun j' _ => (Real.exp_pos _).le)) (Finset.mem_univ i))
    exact Finset.single_le_sum (f := fun j' : Fin 3 => Real.exp (t j' - t i))
      (fun j' _ => (Real.exp_pos _).le) (Finset.mem_univ j)
  calc Real.exp (t j - t i) * |w i j|
      ≤ Real.exp (t j - t i) * |C| :=
        mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ = |C| * Real.exp (t j - t i) := by ring
    _ ≤ |C| * (∑ i' : Fin 3, ∑ j' : Fin 3, Real.exp (t j' - t i')) :=
        mul_le_mul_of_nonneg_left hsum (abs_nonneg C)

/-! ## The transport of plaque algebras -/

theorem isPlaqueAlgebra_comap {U : Subgroup Work.EKLContract.SL3} {Z : Set Work.EKLContract.X3}
    {A : MeasurableSpace Work.EKLContract.X3} (hU : Work.EKLContract.IsHoro U) (t : Fin 3 → ℝ)
    (h : Work.EKLContract.IsPlaqueAlgebra U Z A) :
    Work.EKLContract.IsPlaqueAlgebra U
      ((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y) ⁻¹' Z)
      (MeasurableSpace.comap (fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y) A) := by
  obtain ⟨hAle, ⟨b, hbc, hbm⟩, hZ, hcl⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `comap φ A ≤ borel`: `A ≤ borel` and `φ` is Borel measurable
    exact (MeasurableSpace.comap_mono hAle).trans (measurable_const_smul_aDiag t).comap_le
  · -- countable generation pulls back
    refine ⟨Set.preimage (fun y : X3 => aDiag t • y) '' b, hbc.image _, ?_⟩
    rw [hbm, MeasurableSpace.comap_generateFrom]
  · -- `φ ⁻¹' Z` is comap-measurable by definition of `comap`
    exact (MeasurableSpace.measurableSet_comap).mpr ⟨Z, hZ, rfl⟩
  · -- the atom of a point of `φ ⁻¹' Z`
    intro x hx
    have hpxZ : aDiag t • x ∈ Z := hx
    obtain ⟨hatomZ, hatomU, ⟨O, hOopen, hOshape⟩, ⟨C, hCbound⟩⟩ := hcl (aDiag t • x) hpxZ
    have hatom : atom (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) x
        = (fun y : X3 => aDiag t • y) ⁻¹' atom A (aDiag t • x) :=
      Work.EKLComp.atom_comap _ _ _
    have hshape : shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x
        = conjBy (-t) (shape A U (aDiag t • x)) := shape_comap_conj (A := A) (U := U) hU t x
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- `atom ⊆ φ ⁻¹' Z`
      rw [hatom]; exact Set.preimage_mono hatomZ
    · -- `atom ⊆ (u ↦ u • x) '' U`
      rw [hatom]
      rintro y hy
      obtain ⟨v, hvU, hv⟩ := hatomU hy
      refine ⟨aDiag (-t) * v * aDiag t, ?_, ?_⟩
      · have hh := hU.2.1 (-t) v hvU
        simpa [aDiag_neg_eq_inv, neg_neg] using hh
      · have hv' : v • (aDiag t • x) = aDiag t • y := hv
        show (aDiag (-t) * v * aDiag t) • x = y
        rw [mul_smul, mul_smul, hv', aDiag_neg_smul]
    · -- the shape is `O' ∩ U` with `O'` open
      refine ⟨{g : SL3 | aDiag t * g * (aDiag t)⁻¹ ∈ O}, ?_, ?_⟩
      · exact hOopen.preimage ((continuous_const.mul continuous_id).mul continuous_const)
      · rw [hshape, hOshape, conjBy_neg_inter_U hU t O, conjBy_neg_eq_setOf]
    · -- the shape is entrywise bounded
      obtain ⟨C', hC'⟩ := conjBy_neg_entries_le (t := t) hCbound
      refine ⟨C', fun u hu i j => ?_⟩
      rw [hshape] at hu
      exact hC' u hu i j

end Work.EKLC6Core
