import Mathlib
import Submission.Vdw.ImprimitiveBlock
import Submission.Vdw.BlockPoly

open Polynomial
open scoped Pointwise

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# The *naive* Galois action on the roots, and its relation to Mathlib's

Mathlib's `Polynomial.Gal.galAction p E` on `rootSet p E` is, for
`E = p.SplittingField`, the naive action `σ • x = σ x` *conjugated* by the
bijection of the root set induced by the (opaque) splitting-field lift `φ`:
`σ • x = φ (σ (φ⁻¹ x))`.  Consequently the identity
`↑(galActionHom p p.SplittingField σ x) = σ ↑x` is *not* provable, and the
`hbridge` hypotheses of `BlockPolyGalois` cannot be discharged.

This module repairs the situation by introducing the naive action
(`galRootPermN`, using Mathlib's `galActionAux` instance, whose `smul` is
definitionally `σ x`), its `Fin`-indexed version `galFinHomN`, and the
conjugacy with the project's `galRootPerm` / `galFinHom`.

Consequences: the equivariance `σ (rootOf i) = rootOf (galFinHomN σ i)`, the
Galois action on block polynomials, the identification of the coefficientwise
stabilizer with the setwise block stabilizer, and the identification of the
setwise stabilizer with the fixing subgroup of the block field — all with no
extra hypotheses.

Axioms: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw

noncomputable section

/-! ## The naive action -/

noncomputable def galRootPermN (p : ℚ[X]) :
    p.Gal →* Equiv.Perm (p.rootSet p.SplittingField) :=
  letI : MulAction p.Gal (p.rootSet p.SplittingField) := Polynomial.Gal.galActionAux p
  MulAction.toPermHom p.Gal (p.rootSet p.SplittingField)

lemma galRootPermN_apply (p : ℚ[X]) (σ : p.Gal) (x : p.rootSet p.SplittingField) :
    ((galRootPermN p σ x : p.rootSet p.SplittingField) : p.SplittingField) =
      σ (x : p.SplittingField) := rfl

lemma galRootPermN_mul_apply (p : ℚ[X]) (σ τ : p.Gal) (x : p.rootSet p.SplittingField) :
    galRootPermN p σ (galRootPermN p τ x) = galRootPermN p (σ * τ) x := by
  have h : galRootPermN p σ * galRootPermN p τ = galRootPermN p (σ * τ) :=
    (map_mul (galRootPermN p) σ τ).symm
  rw [show galRootPermN p σ (galRootPermN p τ x)
      = (galRootPermN p σ * galRootPermN p τ) x from rfl, h]

lemma galRootPermN_one_apply (p : ℚ[X]) (x : p.rootSet p.SplittingField) :
    galRootPermN p 1 x = x := by
  have h : (galRootPermN p) 1 = 1 := map_one _
  rw [show galRootPermN p 1 x = ((galRootPermN p) 1 : Equiv.Perm _) x from rfl, h]
  rfl

noncomputable def galFinHomN (p : ℚ[X]) (hsep : p.Separable) :
    p.Gal →* Equiv.Perm (Fin p.natDegree) :=
  (permCongrHom (rootFinEquiv p hsep)).comp (galRootPermN p)

lemma galFinHomN_apply (p : ℚ[X]) (hsep : p.Separable) (σ : p.Gal) (i : Fin p.natDegree) :
    galFinHomN p hsep σ i
      = (rootFinEquiv p hsep) (galRootPermN p σ ((rootFinEquiv p hsep).symm i)) :=
  Equiv.permCongr_apply _ _ _

lemma galFinHomN_rootFinEquiv (p : ℚ[X]) (hsep : p.Separable) (σ : p.Gal)
    (i : Fin p.natDegree) :
    ((rootFinEquiv p hsep).symm (galFinHomN p hsep σ i) : p.rootSet p.SplittingField) =
      galRootPermN p σ ((rootFinEquiv p hsep).symm i) := by
  have h := galFinHomN_apply p hsep σ i
  rw [h]
  exact Equiv.symm_apply_apply _ _

lemma gal_apply_rootOfN (p : ℚ[X]) (hsep : p.Separable) (σ : p.Gal)
    (i : Fin p.natDegree) :
    σ (rootOf p hsep i) = rootOf p hsep (galFinHomN p hsep σ i) := by
  have h := galRootPermN_apply p σ ((rootFinEquiv p hsep).symm i)
  have h2 := galFinHomN_rootFinEquiv p hsep σ i
  change σ (((rootFinEquiv p hsep).symm i : p.rootSet p.SplittingField) : p.SplittingField) =
    (((rootFinEquiv p hsep).symm (galFinHomN p hsep σ i) : p.rootSet p.SplittingField) :
      p.SplittingField)
  rw [h2]
  exact h.symm

lemma galRootPerm_conj_apply (p : ℚ[X])
    [Fact ((p.map (algebraMap ℚ p.SplittingField)).Splits)] (σ : p.Gal)
    (x : p.rootSet p.SplittingField) :
    ((galRootPerm p σ x : p.rootSet p.SplittingField) : p.SplittingField) =
      ((Polynomial.Gal.rootsEquivRoots p p.SplittingField)
        (galRootPermN p σ
          ((Polynomial.Gal.rootsEquivRoots p p.SplittingField).symm x)) :
        p.rootSet p.SplittingField) := by
  show ((σ • x : p.rootSet p.SplittingField) : p.SplittingField) = _
  rw [Polynomial.Gal.smul_def]
  rfl

lemma galRootPerm_conj_apply' (p : ℚ[X])
    [Fact ((p.map (algebraMap ℚ p.SplittingField)).Splits)] (σ : p.Gal)
    (x : p.rootSet p.SplittingField) :
    galRootPerm p σ x =
      (Polynomial.Gal.rootsEquivRoots p p.SplittingField)
        (galRootPermN p σ
          ((Polynomial.Gal.rootsEquivRoots p p.SplittingField).symm x)) :=
  Subtype.ext (galRootPerm_conj_apply p σ x)

noncomputable def conjPerm (p : ℚ[X]) (hsep : p.Separable)
    [Fact ((p.map (algebraMap ℚ p.SplittingField)).Splits)] : Equiv.Perm (Fin p.natDegree) where
  toFun i := (rootFinEquiv p hsep)
    ((Polynomial.Gal.rootsEquivRoots p p.SplittingField) ((rootFinEquiv p hsep).symm i))
  invFun i := (rootFinEquiv p hsep)
    ((Polynomial.Gal.rootsEquivRoots p p.SplittingField).symm ((rootFinEquiv p hsep).symm i))
  left_inv := by
    intro i
    simp only
    have h1 : (rootFinEquiv p hsep).symm ((rootFinEquiv p hsep)
        ((Polynomial.Gal.rootsEquivRoots p p.SplittingField) ((rootFinEquiv p hsep).symm i))) =
        (Polynomial.Gal.rootsEquivRoots p p.SplittingField) ((rootFinEquiv p hsep).symm i) :=
      Equiv.symm_apply_apply _ _
    rw [h1]
    have h2 : (Polynomial.Gal.rootsEquivRoots p p.SplittingField).symm
        ((Polynomial.Gal.rootsEquivRoots p p.SplittingField) ((rootFinEquiv p hsep).symm i)) =
        (rootFinEquiv p hsep).symm i :=
      Equiv.symm_apply_apply _ _
    rw [h2]
    exact Equiv.apply_symm_apply _ _
  right_inv := by
    intro i
    simp only
    have h1 : (rootFinEquiv p hsep).symm ((rootFinEquiv p hsep)
        ((Polynomial.Gal.rootsEquivRoots p p.SplittingField).symm ((rootFinEquiv p hsep).symm i))) =
        (Polynomial.Gal.rootsEquivRoots p p.SplittingField).symm ((rootFinEquiv p hsep).symm i) :=
      Equiv.symm_apply_apply _ _
    rw [h1]
    have h2 : (Polynomial.Gal.rootsEquivRoots p p.SplittingField)
        ((Polynomial.Gal.rootsEquivRoots p p.SplittingField).symm ((rootFinEquiv p hsep).symm i)) =
        (rootFinEquiv p hsep).symm i :=
      Equiv.apply_symm_apply _ _
    rw [h2]
    exact Equiv.apply_symm_apply _ _

lemma conjPerm_apply (p : ℚ[X]) (hsep : p.Separable)
    [Fact ((p.map (algebraMap ℚ p.SplittingField)).Splits)] (i : Fin p.natDegree) :
    conjPerm p hsep i = (rootFinEquiv p hsep)
      ((Polynomial.Gal.rootsEquivRoots p p.SplittingField) ((rootFinEquiv p hsep).symm i)) :=
  rfl

lemma conjPerm_symm_apply (p : ℚ[X]) (hsep : p.Separable)
    [Fact ((p.map (algebraMap ℚ p.SplittingField)).Splits)] (i : Fin p.natDegree) :
    (conjPerm p hsep)⁻¹ i = (rootFinEquiv p hsep)
      ((Polynomial.Gal.rootsEquivRoots p p.SplittingField).symm ((rootFinEquiv p hsep).symm i)) :=
  rfl

lemma galFinHom_conj (p : ℚ[X]) (hsep : p.Separable)
    [Fact ((p.map (algebraMap ℚ p.SplittingField)).Splits)] (σ : p.Gal) :
    galFinHom p hsep σ = conjPerm p hsep * galFinHomN p hsep σ * (conjPerm p hsep)⁻¹ := by
  refine Equiv.ext (fun i => ?_)
  have hΦ : ∀ j, conjPerm p hsep j = (rootFinEquiv p hsep)
      ((Polynomial.Gal.rootsEquivRoots p p.SplittingField) ((rootFinEquiv p hsep).symm j)) :=
    fun j => rfl
  have hN : ∀ j, galFinHomN p hsep σ j = (rootFinEquiv p hsep)
      (galRootPermN p σ ((rootFinEquiv p hsep).symm j)) :=
    fun j => galFinHomN_apply p hsep σ j
  have hR : ∀ y : p.rootSet p.SplittingField, (rootFinEquiv p hsep).symm
      ((rootFinEquiv p hsep) y) = y := fun y => Equiv.symm_apply_apply _ _
  have hkey : (rootFinEquiv p hsep).symm ((conjPerm p hsep)⁻¹ i)
      = (Polynomial.Gal.rootsEquivRoots p p.SplittingField).symm
        ((rootFinEquiv p hsep).symm i) := by
    rw [show (conjPerm p hsep)⁻¹ i = (rootFinEquiv p hsep)
      ((Polynomial.Gal.rootsEquivRoots p p.SplittingField).symm
        ((rootFinEquiv p hsep).symm i)) from rfl]
    exact hR _
  have hstep : (rootFinEquiv p hsep).symm
      (galFinHomN p hsep σ ((conjPerm p hsep)⁻¹ i))
      = galRootPermN p σ ((rootFinEquiv p hsep).symm ((conjPerm p hsep)⁻¹ i)) := by
    rw [hN, hR]
  calc galFinHom p hsep σ i
      = (rootFinEquiv p hsep) (galRootPerm p σ ((rootFinEquiv p hsep).symm i)) :=
        galFinHom_apply p hsep σ i
    _ = (rootFinEquiv p hsep) ((Polynomial.Gal.rootsEquivRoots p p.SplittingField)
          (galRootPermN p σ ((Polynomial.Gal.rootsEquivRoots p p.SplittingField).symm
            ((rootFinEquiv p hsep).symm i)))) :=
        congrArg _ (galRootPerm_conj_apply' p σ _)
    _ = (rootFinEquiv p hsep) ((Polynomial.Gal.rootsEquivRoots p p.SplittingField)
          (galRootPermN p σ ((rootFinEquiv p hsep).symm ((conjPerm p hsep)⁻¹ i)))) :=
        congrArg (fun y => (rootFinEquiv p hsep)
          ((Polynomial.Gal.rootsEquivRoots p p.SplittingField) (galRootPermN p σ y)))
          hkey.symm
    _ = (rootFinEquiv p hsep) ((Polynomial.Gal.rootsEquivRoots p p.SplittingField)
          ((rootFinEquiv p hsep).symm (galFinHomN p hsep σ ((conjPerm p hsep)⁻¹ i)))) :=
        congrArg (fun y => (rootFinEquiv p hsep)
          ((Polynomial.Gal.rootsEquivRoots p p.SplittingField) y)) hstep.symm
    _ = conjPerm p hsep (galFinHomN p hsep σ ((conjPerm p hsep)⁻¹ i)) := (hΦ _).symm
    _ = (conjPerm p hsep * galFinHomN p hsep σ * (conjPerm p hsep)⁻¹) i := rfl

lemma conjPerm_mul_apply (p : ℚ[X]) (hsep : p.Separable)
    [Fact ((p.map (algebraMap ℚ p.SplittingField)).Splits)] (σ : p.Gal) (i : Fin p.natDegree) :
    (conjPerm p hsep * galFinHomN p hsep σ * (conjPerm p hsep)⁻¹) i
      = conjPerm p hsep (galFinHomN p hsep σ ((conjPerm p hsep)⁻¹ i)) := rfl

lemma galFinHom_range_eq (p : ℚ[X]) (hsep : p.Separable)
    [Fact ((p.map (algebraMap ℚ p.SplittingField)).Splits)] :
    (galFinHom p hsep).range
      = ((galFinHomN p hsep).range).map (MulAut.conj (conjPerm p hsep)).toMonoidHom := by
  ext x
  constructor
  · rintro ⟨σ, rfl⟩
    exact ⟨galFinHomN p hsep σ, ⟨σ, rfl⟩,
      (MulAut.conj_apply _ _).trans (galFinHom_conj p hsep σ).symm⟩
  · rintro ⟨y, ⟨σ, rfl⟩, hy⟩
    refine ⟨σ, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom] at hy
    rw [MulAut.conj_apply] at hy
    rw [galFinHom_conj p hsep σ, hy]


/-! ## Block transfer under conjugation -/

lemma inv_smul_image_self {α : Type*} (Φ : Equiv.Perm α) (B : Set α) :
    Φ⁻¹ • (Φ '' B) = B := by
  have h : (Φ '' B : Set α) = Φ • B := rfl
  rw [h, smul_smul, inv_mul_cancel, one_smul]

lemma subgroup_map_conj_inv {α : Type*} (Φ : Equiv.Perm α) (H : Subgroup (Equiv.Perm α)) :
    (H.map (MulAut.conj Φ).toMonoidHom).map (MulAut.conj Φ⁻¹).toMonoidHom = H := by
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, ⟨z, hz, hzy⟩, hyx⟩
    have hx : x = z := by rw [← hyx, ← hzy]; group
    rw [hx]; exact hz
  · intro hx
    exact ⟨Φ * x * Φ⁻¹, ⟨x, hx, rfl⟩, by group⟩

/-- **Blocks transfer through conjugation** (Mathlib's
`IsBlock.of_subgroup_of_conjugate`, both directions). -/
lemma isBlock_map_conj_iff {α : Type*} (Φ : Equiv.Perm α) (H : Subgroup (Equiv.Perm α))
    (B : Set α) :
    MulAction.IsBlock (H.map (MulAut.conj Φ).toMonoidHom) (Φ '' B) ↔
      MulAction.IsBlock H B := by
  constructor
  · intro hB
    have h2 := hB.of_subgroup_of_conjugate (Φ⁻¹)
    rw [subgroup_map_conj_inv Φ H, inv_smul_image_self Φ B] at h2
    exact h2
  · intro hB
    exact hB.of_subgroup_of_conjugate Φ

/-! ## The naive block condition -/

/-- The naive analogue of `irrGalFinHom`. -/
noncomputable def irrGalFinHomN (f : ℤ[X]) [Fact (Irreducible (f.map φℚ))] :
    (f.map φℚ).Gal →* Equiv.Perm (Fin ((f.map φℚ).natDegree)) :=
  galFinHomN (f.map φℚ) (separable_of_irreducible_rat Fact.out)

/-- **`f` admits a block of size `k`** for the *naive* action of
`Gal (f.map φℚ)` on the `n` roots. -/
def HasBlockSizeN (f : ℤ[X]) (h : Irreducible (f.map φℚ)) (k : ℕ) : Prop :=
  letI : Fact (Irreducible (f.map φℚ)) := ⟨h⟩
  ∃ B : Set (Fin ((f.map φℚ).natDegree)),
    MulAction.IsBlock (irrGalFinHomN f).range B ∧ B.ncard = k

/-- The project's `HasBlockSize` (Mathlib's action) agrees with the naive
version. -/
lemma image_symm_image {α : Type*} (Φ : Equiv.Perm α) (B : Set α) :
    Φ '' (Φ.symm '' B) = B := by
  rw [Set.image_image]
  ext x
  simp

theorem hasBlockSize_iff (f : ℤ[X]) (h : Irreducible (f.map φℚ)) (k : ℕ) :
    HasBlockSize f h k ↔ HasBlockSizeN f h k := by
  letI : Fact (Irreducible (f.map φℚ)) := ⟨h⟩
  letI : Fact (((f.map φℚ).map (algebraMap ℚ (f.map φℚ).SplittingField)).Splits) :=
    ⟨Polynomial.SplittingField.splits (f.map φℚ)⟩
  set Φ : Equiv.Perm (Fin ((f.map φℚ).natDegree)) :=
    conjPerm (f.map φℚ) (separable_of_irreducible_rat Fact.out) with hΦdef
  have hΦ : (irrGalFinHom f).range
      = ((irrGalFinHomN f).range).map (MulAut.conj Φ).toMonoidHom :=
    galFinHom_range_eq (f.map φℚ) (separable_of_irreducible_rat Fact.out)
  constructor
  · rintro ⟨B, hB, hk⟩
    refine ⟨Φ.symm '' B, ?_, ?_⟩
    · have hB' : MulAction.IsBlock
          (↥(((irrGalFinHomN f).range).map (MulAut.conj Φ).toMonoidHom)) B :=
        (congrArg (fun H : Subgroup (Equiv.Perm (Fin ((f.map φℚ).natDegree))) =>
          MulAction.IsBlock (↥H) B) hΦ).mp hB
      have hB'' : MulAction.IsBlock
          (↥(((irrGalFinHomN f).range).map (MulAut.conj Φ).toMonoidHom))
          (Φ '' (Φ.symm '' B)) := by
        rwa [image_symm_image]
      exact (isBlock_map_conj_iff Φ ((irrGalFinHomN f).range) (Φ.symm '' B)).mp hB''
    · rw [Set.ncard_image_of_injective _ Φ.symm.injective]
      exact hk
  · rintro ⟨B, hB, hk⟩
    refine ⟨Φ '' B, ?_, ?_⟩
    · have hkey := (isBlock_map_conj_iff Φ ((irrGalFinHomN f).range) B).mpr hB
      exact (congrArg (fun H : Subgroup (Equiv.Perm (Fin ((f.map φℚ).natDegree))) =>
          MulAction.IsBlock (↥H) (Φ '' B)) hΦ).mpr hkey
    · rw [Set.ncard_image_of_injective _ Φ.injective]
      exact hk

end

end Submission.Vdw
