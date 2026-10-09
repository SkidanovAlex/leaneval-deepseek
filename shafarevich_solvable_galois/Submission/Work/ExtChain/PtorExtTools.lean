import Mathlib
import Submission.Work.ExtChain.PtorsionDecompDefs
import Submission.Work.SSGRoute.ExtChain.subsingleton_ext_fpRegular
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Ext`-tools for the dévissage of `Ext²` in the first variable

This file contains the homological half of `Work.ExtChain.ext2_fn_ptorsion_of_trivial`.  Given a
representation `X` that carries a family of "coordinate" maps
`incl i : F i ⟶ X`, `proj i : X ⟶ F i` summing to the identity
(`∑ i, proj i ≫ incl i = 𝟙 X`, the usual coordinate system of a finite direct sum), the first
variable `Ext` functor is detected by the coordinates:

* the reconstruction identity `z = ∑ i, (mk₀ (proj i)).comp ((mk₀ (incl i)).comp z)`;
* hence `Ext X A 2` is a subsingleton as soon as each `Ext (F i) A 2` is;
* and injectivity of `(·).comp (mk₀ φ)` transfers from the coordinates to `X`.

These are applied to the two model modules `trivPow p H a = 𝔽_p^a` (with coordinates indexed by
`Fin a` and `F = 𝔽_p`) and `regPow p H b = 𝔽_p[H]^b` (coordinates indexed by `Fin b` and
`F = 𝔽_p[H]`), giving respectively the transfer of injectivity from the trivial coefficient and the
vanishing of `Ext²` of the regular coefficient
(`Work.SSGRoute.ExtChain.subsingleton_ext_fpRegular`).
-/

namespace Work.ExtChain

open CategoryTheory
open scoped BigOperators

noncomputable section

/-! ## General coordinate manipulations -/

/-- **Reconstruction from coordinates.**  If `incl : ι → (F ⟶ X)`, `proj : ι → (X ⟶ F)` satisfy
`∑ i, proj i ≫ incl i = 𝟙 X`, then every `z : Ext X A n` is the sum of its coordinates
`(mk₀ (incl i)).comp z`, pushed back by `mk₀ (proj i)`. -/
theorem ext_reconstruct_of_coords {C : Type*} [Category C] [Abelian C] [HasExt C]
    {X F A : C} {ι : Type} [Fintype ι]
    (incl : ι → (F ⟶ X)) (proj : ι → (X ⟶ F))
    (h : (∑ i, proj i ≫ incl i) = 𝟙 X) (z : CategoryTheory.Abelian.Ext X A 2) :
    z = ∑ i, (CategoryTheory.Abelian.Ext.mk₀ (proj i)).comp
        ((CategoryTheory.Abelian.Ext.mk₀ (incl i)).comp z
          (show 0 + 2 = 2 by norm_num))
        (show 0 + 2 = 2 by norm_num) := by
  symm
  simp only [← CategoryTheory.Abelian.Ext.comp_assoc_of_second_deg_zero,
    CategoryTheory.Abelian.Ext.mk₀_comp_mk₀]
  rw [← CategoryTheory.Abelian.Ext.sum_comp, ← CategoryTheory.Abelian.Ext.mk₀_sum, h,
    CategoryTheory.Abelian.Ext.mk₀_id_comp]

/-- **Vanishing from coordinates.**  If `Ext (F i) A n` vanishes for every coordinate then
`Ext X A n` vanishes. -/
theorem ext_subsingleton_of_coords {C : Type*} [Category C] [Abelian C] [HasExt C]
    {X F A : C} {ι : Type} [Fintype ι]
    (incl : ι → (F ⟶ X)) (proj : ι → (X ⟶ F))
    (h : (∑ i, proj i ≫ incl i) = 𝟙 X)
    (hzero : Subsingleton (CategoryTheory.Abelian.Ext F A 2)) :
    Subsingleton (CategoryTheory.Abelian.Ext X A 2) := by
  have key := ext_reconstruct_of_coords (A := A) incl proj h
  refine ⟨fun z w => ?_⟩
  rw [key z, key w]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  congr 1
  exact Subsingleton.elim _ _

/-- **Injectivity from coordinates.**  If `(·).comp (mk₀ φ)` is injective on every
`Ext (F i) A n`, it is injective on `Ext X A n`. -/
theorem ext_injective_of_coords {C : Type*} [Category C] [Abelian C] [HasExt C]
    {X F A B : C} (φ : A ⟶ B) {ι : Type} [Fintype ι]
    (incl : ι → (F ⟶ X)) (proj : ι → (X ⟶ F))
    (h : (∑ i, proj i ≫ incl i) = 𝟙 X)
    (htriv : Function.Injective (fun z : CategoryTheory.Abelian.Ext F A 2 =>
      z.comp (CategoryTheory.Abelian.Ext.mk₀ φ) (add_zero 2))) :
    Function.Injective (fun z : CategoryTheory.Abelian.Ext X A 2 =>
      z.comp (CategoryTheory.Abelian.Ext.mk₀ φ) (add_zero 2)) := by
  have key := ext_reconstruct_of_coords (A := A) incl proj h
  intro z w hzw
  have hzw' : z.comp (CategoryTheory.Abelian.Ext.mk₀ φ) (add_zero 2) =
      w.comp (CategoryTheory.Abelian.Ext.mk₀ φ) (add_zero 2) := hzw
  rw [key z, key w]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  congr 1
  apply htriv
  simp only [CategoryTheory.Abelian.Ext.comp_assoc_of_third_deg_zero]
  rw [hzw']

/-- **Transfer along a retract.**  If `s : N ⟶ M`, `r : M ⟶ N` satisfy `s ≫ r = 𝟙 N` and
`(·).comp (mk₀ φ)` is injective on `Ext M A n`, then it is injective on `Ext N A n`. -/
theorem ext_injective_of_retract {C : Type*} [Category C] [Abelian C] [HasExt C]
    {N M A B : C} (s : N ⟶ M) (r : M ⟶ N) (hrs : s ≫ r = 𝟙 N) (φ : A ⟶ B)
    (hM : Function.Injective (fun z : CategoryTheory.Abelian.Ext M A 2 =>
      z.comp (CategoryTheory.Abelian.Ext.mk₀ φ) (add_zero 2))) :
    Function.Injective (fun z : CategoryTheory.Abelian.Ext N A 2 =>
      z.comp (CategoryTheory.Abelian.Ext.mk₀ φ) (add_zero 2)) := by
  intro z w hzw
  have hzw' : z.comp (CategoryTheory.Abelian.Ext.mk₀ φ) (add_zero 2) =
      w.comp (CategoryTheory.Abelian.Ext.mk₀ φ) (add_zero 2) := hzw
  have hq : (CategoryTheory.Abelian.Ext.mk₀ r).comp
        (z.comp (CategoryTheory.Abelian.Ext.mk₀ φ) (add_zero 2)) (zero_add 2) =
      (CategoryTheory.Abelian.Ext.mk₀ r).comp
        (w.comp (CategoryTheory.Abelian.Ext.mk₀ φ) (add_zero 2)) (zero_add 2) := by rw [hzw']
  simp only [← CategoryTheory.Abelian.Ext.comp_assoc_of_third_deg_zero] at hq
  have heq : (CategoryTheory.Abelian.Ext.mk₀ r).comp z (zero_add 2) =
      (CategoryTheory.Abelian.Ext.mk₀ r).comp w (zero_add 2) := hM hq
  have hz : z = (CategoryTheory.Abelian.Ext.mk₀ s).comp
      ((CategoryTheory.Abelian.Ext.mk₀ r).comp z (zero_add 2)) (zero_add 2) := by
    rw [← CategoryTheory.Abelian.Ext.comp_assoc_of_second_deg_zero]
    rw [CategoryTheory.Abelian.Ext.mk₀_comp_mk₀, hrs,
      CategoryTheory.Abelian.Ext.mk₀_id_comp]
  rw [hz, heq]
  rw [← CategoryTheory.Abelian.Ext.comp_assoc_of_second_deg_zero]
  rw [CategoryTheory.Abelian.Ext.mk₀_comp_mk₀, hrs,
    CategoryTheory.Abelian.Ext.mk₀_id_comp]

/-- A subsingleton `Ext X A n` makes `(·).comp (mk₀ φ)` injective. -/
theorem ext_injective_of_subsingleton {C : Type*} [Category C] [Abelian C] [HasExt C]
    {X A B : C} (φ : A ⟶ B) (h : Subsingleton (CategoryTheory.Abelian.Ext X A 2)) :
    Function.Injective (fun z : CategoryTheory.Abelian.Ext X A 2 =>
      z.comp (CategoryTheory.Abelian.Ext.mk₀ φ) (add_zero 2)) :=
  fun z w _ => h.elim z w

/-- **Injectivity on a binary biproduct.**  If `(·).comp (mk₀ φ)` is injective on both factors it
is injective on the biproduct. -/
theorem ext_injective_biprod {C : Type*} [Category C] [Abelian C] [HasExt C]
    {X₁ X₂ A B : C} (φ : A ⟶ B)
    (h₁ : Function.Injective (fun z : CategoryTheory.Abelian.Ext X₁ A 2 =>
      z.comp (CategoryTheory.Abelian.Ext.mk₀ φ) (add_zero 2)))
    (h₂ : Function.Injective (fun z : CategoryTheory.Abelian.Ext X₂ A 2 =>
      z.comp (CategoryTheory.Abelian.Ext.mk₀ φ) (add_zero 2))) :
    Function.Injective (fun z : CategoryTheory.Abelian.Ext (X₁ ⊞ X₂) A 2 =>
      z.comp (CategoryTheory.Abelian.Ext.mk₀ φ) (add_zero 2)) := by
  intro z w hzw
  have hzw' : z.comp (CategoryTheory.Abelian.Ext.mk₀ φ) (add_zero 2) =
      w.comp (CategoryTheory.Abelian.Ext.mk₀ φ) (add_zero 2) := hzw
  have h1' : (CategoryTheory.Abelian.Ext.biprodAddEquiv (Y := A) (n := 2) z).1 =
      (CategoryTheory.Abelian.Ext.biprodAddEquiv (Y := A) (n := 2) w).1 := by
    apply h₁
    simp only [CategoryTheory.Abelian.Ext.biprodAddEquiv_apply_fst]
    rw [CategoryTheory.Abelian.Ext.comp_assoc_of_third_deg_zero,
      CategoryTheory.Abelian.Ext.comp_assoc_of_third_deg_zero, hzw']
  have h2' : (CategoryTheory.Abelian.Ext.biprodAddEquiv (Y := A) (n := 2) z).2 =
      (CategoryTheory.Abelian.Ext.biprodAddEquiv (Y := A) (n := 2) w).2 := by
    apply h₂
    simp only [CategoryTheory.Abelian.Ext.biprodAddEquiv_apply_snd]
    rw [CategoryTheory.Abelian.Ext.comp_assoc_of_third_deg_zero,
      CategoryTheory.Abelian.Ext.comp_assoc_of_third_deg_zero, hzw']
  exact (CategoryTheory.Abelian.Ext.biprodAddEquiv (X₁ := X₁) (X₂ := X₂) (Y := A)
    (n := 2)).injective (Prod.ext h1' h2')

/-! ## Coordinates on `trivPow` and `regPow` -/

section Coords

variable (p : ℕ) (H : Type) [Group H]

/-- The `i`-th coordinate inclusion `𝔽_p → 𝔽_p^a`. -/
def inclT (a : ℕ) (i : Fin a) : trivOne p H ⟶ trivPow p H a :=
  Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap _ _ (Finsupp.lsingle i)
    (fun _ _ => rfl))

/-- The `i`-th coordinate projection `𝔽_p^a → 𝔽_p`. -/
def projT (a : ℕ) (i : Fin a) : trivPow p H a ⟶ trivOne p H :=
  Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap _ _ (Finsupp.lapply i)
    (fun _ _ => rfl))

/-- The coordinate system of `𝔽_p^a` sums to the identity. -/
theorem projT_inclT_sum (a : ℕ) :
    (∑ i : Fin a, projT p H a i ≫ inclT p H a i) = 𝟙 (trivPow p H a) := by
  ext y
  rw [Rep.sum_hom]
  rw [Representation.IntertwiningMap.toLinearMap_sum]
  rw [LinearMap.sum_apply]
  simp only [Rep.hom_comp_toLinearMap, Rep.hom_ofHom, Rep.hom_id, LinearMap.comp_apply,
    Finsupp.lapply_apply, Finsupp.lsingle_apply]
  exact (Finsupp.sum_fintype y Finsupp.single (fun i => by simp)).symm.trans
    (Finsupp.sum_single y)

/-- The `j`-th coordinate inclusion `𝔽_p[H] → 𝔽_p[H]^b`. -/
def inclR (b : ℕ) (j : Fin b) : regOne p H ⟶ regPow p H b :=
  Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap _ _ (Finsupp.lsingle j)
    (fun g y => by
      rw [Representation.ofDistribMulAction_apply_apply,
        Representation.ofDistribMulAction_apply_apply]
      simp only [Finsupp.lsingle_apply, Finsupp.smul_single]))

/-- The `j`-th coordinate projection `𝔽_p[H]^b → 𝔽_p[H]`. -/
def projR (b : ℕ) (j : Fin b) : regPow p H b ⟶ regOne p H :=
  Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap _ _ (Finsupp.lapply j)
    (fun g y => by
      rw [Representation.ofDistribMulAction_apply_apply,
        Representation.ofDistribMulAction_apply_apply, Finsupp.lapply_apply,
        Finsupp.lapply_apply, Finsupp.smul_apply]))

/-- The coordinate system of `𝔽_p[H]^b` sums to the identity. -/
theorem projR_inclR_sum (b : ℕ) :
    (∑ j : Fin b, projR p H b j ≫ inclR p H b j) = 𝟙 (regPow p H b) := by
  ext y
  rw [Rep.sum_hom]
  rw [Representation.IntertwiningMap.toLinearMap_sum]
  rw [LinearMap.sum_apply]
  simp only [Rep.hom_comp_toLinearMap, Rep.hom_ofHom, Rep.hom_id, LinearMap.comp_apply,
    Finsupp.lapply_apply, Finsupp.lsingle_apply]
  exact (Finsupp.sum_fintype y Finsupp.single (fun i => by simp)).symm.trans
    (Finsupp.sum_single y)

end Coords

/-! ## The two coefficient transfers -/

/-- **Injectivity transfers from the trivial coefficient to `𝔽_p^a`.** -/
theorem ext_injective_trivPow {p : ℕ} [Fact p.Prime] {H : Type} [Group H] (a : ℕ)
    (A B : Rep.{0} SSGRoute.PTExt.Coeff H) (φ : A ⟶ B)
    (htriv : Function.Injective (fun z : CategoryTheory.Abelian.Ext.{0}
        (trivOne p H) A 2 =>
      z.comp (CategoryTheory.Abelian.Ext.mk₀ φ) (add_zero 2))) :
    Function.Injective (fun z : CategoryTheory.Abelian.Ext.{0}
        (trivPow p H a) A 2 =>
      z.comp (CategoryTheory.Abelian.Ext.mk₀ φ) (add_zero 2)) :=
  ext_injective_of_coords (X := trivPow p H a) (F := trivOne p H) (A := A) (B := B) φ
    (inclT p H a) (projT p H a) (projT_inclT_sum p H a) htriv

/-- **`Ext²` of the free (regular) coefficient vanishes.** -/
theorem subsingleton_ext_regPow {p : ℕ} [Fact p.Prime] {H : Type} [Group H] (b : ℕ)
    (A : Rep.{0} SSGRoute.PTExt.Coeff H) :
    Subsingleton (CategoryTheory.Abelian.Ext.{0} (regPow p H b) A 2) :=
  ext_subsingleton_of_coords (X := regPow p H b) (F := regOne p H) (A := A) (ι := Fin b)
    (inclR p H b) (projR p H b) (projR_inclR_sum p H b)
    (SSGRoute.ExtChain.subsingleton_ext_fpRegular p H A 2 (by norm_num))

/-- **Injectivity on `Ext²(regPow p H b, ·)` is automatic.** -/
theorem ext_injective_regPow {p : ℕ} [Fact p.Prime] {H : Type} [Group H] (b : ℕ)
    (A B : Rep.{0} SSGRoute.PTExt.Coeff H) (φ : A ⟶ B) :
    Function.Injective (fun z : CategoryTheory.Abelian.Ext.{0} (regPow p H b) A 2 =>
      z.comp (CategoryTheory.Abelian.Ext.mk₀ φ) (add_zero 2)) :=
  ext_injective_of_subsingleton φ (subsingleton_ext_regPow b A)

end

end Work.ExtChain
