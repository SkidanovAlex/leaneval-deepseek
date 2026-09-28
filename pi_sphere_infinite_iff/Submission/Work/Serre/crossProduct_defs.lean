import Mathlib
import Submission.Work.Kunneth.HomValue
import Submission.Work.Kunneth.CrossGen
import Submission.Work.Serre.tpC_homologyMap_cokernel_subsingleton

/-!
# The complex `ℤ[r+1]` and the map `ℤ[r+1] ⟶ D` with `1 ↦ z`

For a chain complex `D` of `ℤ`-modules and a cycle `z ∈ Z_{r+1}(D)`, this file provides

* `Work.Serre.dzComplex r` — the coefficient complex `ℤ[r+1]`: the complex which is `ℤ` in degree
  `r+1` and `0` elsewhere, with zero differentials;
* `Work.Serre.dzMap r D z` — the chain map `ℤ[r+1] ⟶ D` carrying the generator of degree `r+1` to
  the cycle `z`;  it is a monomorphism as soon as `z` is not a torsion element
  (`Work.Serre.mono_dzMap`).

The cokernel of `dzMap r D z` is the quotient complex `D ⧸ ℤz`, and the map
`tpMap C C (ℤ[r+1]) D (𝟙 C) (dzMap r D z)` is "the cross product with `z`".  These are the two
objects in terms of which `Work.Serre.crossProduct_coker_rat` is proved.

## Main definitions and results

* `Work.Serre.dzX`, `Work.Serre.dzComplex`, `Work.Serre.dzComplex_X`, `Work.Serre.dzComplex_d_succ`;
* `Work.Serre.dzIso` — the identification `(ℤ[r+1])_{r+1} ≅ ℤ`;
* `Work.Serre.dzGen` — the component of `dzMap` at degree `r+1`;
* `Work.Serre.dzMap`, `Work.Serre.dzMap_f_self`, `Work.Serre.dzMap_f_self_apply`;
* `Work.Serre.dzGen_comp_d_eq_zero`, `Work.Serre.mono_dzMap`;
* `Work.Serre.subsingleton_tpSummand_dz` — the summands of `tpC C ℤ[r+1]` away from the
  `(r+1)`-column are trivial.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct ZeroObject

namespace Work.Serre

noncomputable section

/-! ## Elementary linear algebra -/

/-- **Tensoring with a subsingleton is a subsingleton.** -/
theorem subsingleton_tensor_of_subsingleton_right {M : Type*} [AddCommGroup M] [Module ℤ M]
    {N : Type*} [AddCommGroup N] [Module ℤ N] [Subsingleton N] :
    Subsingleton (M ⊗[ℤ] N) := by
  rw [subsingleton_iff]
  intro x y
  have hzero : ∀ z : M ⊗[ℤ] N, z = 0 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | tmul m n => rw [Subsingleton.elim n (0 : N), TensorProduct.tmul_zero]
    | add a b ha hb => rw [ha, hb, add_zero]
  rw [hzero x, hzero y]

/-- **A linear map out of `ℤ` is determined by its value at `1`.** -/
theorem toSpanSingleton_injective_of {M : Type*} [AddCommGroup M] [Module ℤ M] {m : M}
    (h : ∀ k : ℤ, (LinearMap.toSpanSingleton ℤ M m) k = 0 → k = 0) :
    Function.Injective (LinearMap.toSpanSingleton ℤ M m) := by
  intro a b hab
  have h2 : (LinearMap.toSpanSingleton ℤ M m) (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  have h3 := h (a - b) h2
  omega

/-! ## The complex `ℤ[r+1]` -/

/-- The degree-`j` part of `ℤ[r+1]`: `ℤ` in degree `r+1`, the zero module elsewhere. -/
def dzX (r j : ℕ) : ModuleCat ℤ :=
  if j = r + 1 then ModuleCat.of ℤ ℤ else ModuleCat.of ℤ PUnit

theorem dzX_self (r : ℕ) : dzX r (r + 1) = ModuleCat.of ℤ ℤ := by simp [dzX]

theorem dzX_of_ne (r j : ℕ) (h : j ≠ r + 1) : dzX r j = ModuleCat.of ℤ PUnit := by
  simp [dzX, h]

/-- Away from degree `r+1` the complex `ℤ[r+1]` is trivial. -/
theorem subsingleton_dzX (r j : ℕ) (h : j ≠ r + 1) : Subsingleton ↥(dzX r j) := by
  rw [dzX_of_ne r j h]
  infer_instance

/-- **The complex `ℤ[r+1]`** concentrated in degree `r+1`, with zero differentials. -/
def dzComplex (r : ℕ) : ChainComplex (ModuleCat ℤ) ℕ :=
  ChainComplex.of (dzX r) (fun j => (0 : dzX r (j + 1) ⟶ dzX r j)) (fun j => by simp)

@[simp]
theorem dzComplex_X (r j : ℕ) : (dzComplex r).X j = dzX r j := rfl

theorem dzComplex_d_succ (r j : ℕ) : (dzComplex r).d (j + 1) j = 0 := by
  simp only [dzComplex, ChainComplex.of_d]
  rfl

theorem dzComplex_d (r i j : ℕ) (h : ¬ (ComplexShape.down ℕ).Rel i j) :
    (dzComplex r).d i j = 0 := HomologicalComplex.shape (dzComplex r) i j h

/-- The identification `(ℤ[r+1])_{r+1} ≅ ℤ`. -/
def dzIso (r : ℕ) : (dzComplex r).X (r + 1) ≅ ModuleCat.of ℤ ℤ :=
  eqToIso (by rw [dzComplex]; exact dzX_self r)

/-- The degree-`j` module of `ℤ[r+1]` is a subsingleton away from `r+1`. -/
theorem subsingleton_dzComplex_X (r j : ℕ) (h : j ≠ r + 1) :
    Subsingleton ↥((dzComplex r).X j) := by
  have h1 : (dzComplex r).X j = dzX r j := rfl
  rw [h1]
  exact subsingleton_dzX r j h

/-! ## The map `ℤ[r+1] ⟶ D` with `1 ↦ z` -/

/-- The component at degree `r+1`: the map `ℤ ⟶ D_{r+1}` carrying the generator to `z`. -/
def dzGen (r : ℕ) (D : ChainComplex (ModuleCat ℤ) ℕ) (z : ↥(D.cycles (r + 1))) :
    (dzComplex r).X (r + 1) ⟶ D.X (r + 1) :=
  (dzIso r).hom ≫
    ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ ↥(D.X (r + 1)) ((D.iCycles (r + 1)) z))

/-- The value of the component at degree `r+1`. -/
theorem dzGen_apply (r : ℕ) (D : ChainComplex (ModuleCat ℤ) ℕ) (z : ↥(D.cycles (r + 1)))
    (y : ↥((dzComplex r).X (r + 1))) :
    (dzGen r D z).hom y
      = (LinearMap.toSpanSingleton ℤ ↥(D.X (r + 1)) ((D.iCycles (r + 1)) z))
          ((dzIso r).hom.hom y) := by
  rw [dzGen, ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom]

/-- The component at degree `r+1` is injective as soon as `z` is not a torsion element. -/
theorem injective_dzGen (r : ℕ) (D : ChainComplex (ModuleCat ℤ) ℕ) (z : ↥(D.cycles (r + 1)))
    (hznt : ∀ k : ℤ, (LinearMap.toSpanSingleton ℤ ↥(D.X (r + 1))
      ((D.iCycles (r + 1)) z)) k = 0 → k = 0) :
    Function.Injective (dzGen r D z).hom := by
  have h1 : Function.Injective
      (LinearMap.toSpanSingleton ℤ ↥(D.X (r + 1)) ((D.iCycles (r + 1)) z)) :=
    toSpanSingleton_injective_of hznt
  have h2 : Function.Injective ((dzIso r).hom.hom) := by
    rw [← ModuleCat.mono_iff_injective]
    infer_instance
  have h3 : (dzGen r D z).hom = (LinearMap.toSpanSingleton ℤ ↥(D.X (r + 1))
      ((D.iCycles (r + 1)) z)).comp ((dzIso r).hom.hom) := by
    rw [dzGen, ModuleCat.hom_comp, ModuleCat.hom_ofHom]
  rw [h3]
  exact h1.comp h2

/-- The composite `ℤ[r+1]_{r+1} ⟶ D_{r+1} ⟶ D_r` vanishes. -/
theorem dzGen_comp_d_eq_zero (r : ℕ) (D : ChainComplex (ModuleCat ℤ) ℕ)
    (z : ↥(D.cycles (r + 1))) : dzGen r D z ≫ D.d (r + 1) r = 0 := by
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_comp, ModuleCat.hom_zero]
  apply LinearMap.ext
  intro x
  show (D.d (r + 1) r).hom ((dzGen r D z).hom x) = 0
  rw [dzGen, ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    LinearMap.toSpanSingleton_apply]
  rw [LinearMap.map_smul]
  have hz : (D.d (r + 1) r) ((D.iCycles (r + 1)) z) = 0 := Work.Kunneth.d_iCycles D (r + 1) z
  rw [hz, smul_zero]

/-- The degree-`j` component of `dzMap`. -/
def dzMapF (r : ℕ) (D : ChainComplex (ModuleCat ℤ) ℕ) (z : ↥(D.cycles (r + 1))) (j : ℕ) :
    (dzComplex r).X j ⟶ D.X j :=
  if h : j = r + 1 then
    (eqToHom (by rw [h]) : (dzComplex r).X j ⟶ (dzComplex r).X (r + 1)) ≫
      dzGen r D z ≫ (eqToHom (by rw [h]) : D.X (r + 1) ⟶ D.X j)
  else 0

theorem dzMapF_self (r : ℕ) (D : ChainComplex (ModuleCat ℤ) ℕ) (z : ↥(D.cycles (r + 1))) :
    dzMapF r D z (r + 1) = dzGen r D z := by
  rw [dzMapF]
  rw [dif_pos rfl]
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]

/-- **The chain map `ℤ[r+1] ⟶ D`** carrying the generator of degree `r+1` to the cycle `z`. -/
def dzMap (r : ℕ) (D : ChainComplex (ModuleCat ℤ) ℕ) (z : ↥(D.cycles (r + 1))) :
    dzComplex r ⟶ D where
  f := dzMapF r D z
  comm' i j hij := by
    have hji : j + 1 = i := hij
    subst hji
    rw [dzComplex_d_succ, zero_comp]
    by_cases h : j + 1 = r + 1
    · have hj : j = r := by omega
      rw [hj, dzMapF_self]
      exact dzGen_comp_d_eq_zero r D z
    · rw [dzMapF, dif_neg h, zero_comp]

theorem dzMap_f_self (r : ℕ) (D : ChainComplex (ModuleCat ℤ) ℕ) (z : ↥(D.cycles (r + 1))) :
    (dzMap r D z).f (r + 1) = dzGen r D z := dzMapF_self r D z

/-- The value of the `(r+1)`-component of `dzMap`. -/
theorem dzMap_f_self_apply (r : ℕ) (D : ChainComplex (ModuleCat ℤ) ℕ) (z : ↥(D.cycles (r + 1)))
    (y : ↥((dzComplex r).X (r + 1))) :
    ((dzMap r D z).f (r + 1)).hom y
      = (LinearMap.toSpanSingleton ℤ ↥(D.X (r + 1)) ((D.iCycles (r + 1)) z))
          ((dzIso r).hom.hom y) := by
  rw [dzMap_f_self]
  exact dzGen_apply r D z y

theorem dzMap_f_of_ne (r : ℕ) (D : ChainComplex (ModuleCat ℤ) ℕ) (z : ↥(D.cycles (r + 1)))
    (j : ℕ) (h : j ≠ r + 1) : (dzMap r D z).f j = 0 := by
  change dzMapF r D z j = 0
  rw [dzMapF, dif_neg h]

/-- **`dzMap` is a monomorphism** when the cycle `z` is not a torsion element. -/
theorem mono_dzMap (r : ℕ) (D : ChainComplex (ModuleCat ℤ) ℕ) (z : ↥(D.cycles (r + 1)))
    (hznt : ∀ k : ℤ, (LinearMap.toSpanSingleton ℤ ↥(D.X (r + 1))
      ((D.iCycles (r + 1)) z)) k = 0 → k = 0) :
    Mono (dzMap r D z) := by
  have hinj : ∀ j, Function.Injective ((dzMap r D z).f j).hom := by
    intro j
    by_cases h : j = r + 1
    · subst h
      rw [dzMap_f_self]
      exact injective_dzGen r D z hznt
    · haveI : Subsingleton ↥((dzComplex r).X j) := subsingleton_dzComplex_X r j h
      rw [dzMap_f_of_ne r D z j h]
      exact fun a b _ => Subsingleton.elim a b
  refine ⟨fun {Z} f g hfg => ?_⟩
  apply HomologicalComplex.Hom.ext
  funext j
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have h := congrArg (fun (φ : Z ⟶ D) => (φ.f j).hom x) hfg
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact hinj j h

/-! ## The summands of `tpC C ℤ[r+1]` -/

/-- Away from the `r+1`-column, the summands of `tpC C ℤ[r+1]` are trivial. -/
theorem subsingleton_tpSummand_dz (C : ChainComplex (ModuleCat ℤ) ℕ) (r p q : ℕ)
    (hq : q ≠ r + 1) :
    Subsingleton (Work.Kunneth.tpSummand C (dzComplex r) p q) := by
  haveI : Subsingleton ↥((dzComplex r).X q) := subsingleton_dzComplex_X r q hq
  exact subsingleton_tensor_of_subsingleton_right

end

end Work.Serre
