import Mathlib
import Submission.Work.ANALYTIC.RealSide
import Submission.Work.ANALYTIC.NullFamily
import Submission.Work.FLAT.SheafifyTensor
import Submission.Work.ANALYTIC.exists_realNullSeq
import Submission.Work.ANALYTIC.preSolid_all

/-!
# `∏^bnd ℝ` is solid-null (AN2, REFS/03 §3)

The light condensed abelian group `∏^bnd ℝ` (`Work.ANALYTIC.boundedReal`, the uniformly bounded
families of continuous real-valued functions on a light profinite set) is solid-null: every
morphism `(∏^bnd ℝ)[0] ⟶ ι N` in `D(LightCondAb)` is zero.

Route (RC Thm 3.2.4(4), REFS/03 §3).  `∏^bnd ℝ` carries an action of the condensed ring
`realCond = ℝ` (coordinatewise multiplication), which is unital for the "constant `1`" section
`realCondUnit`; the null-sequence machinery `Work.ANALYTIC.solidNull_of_unit_action` then applies,
with the parametrised null sequence `Work.ANALYTIC.exists_realNullSeq` and the input
`Work.ANALYTIC.preSolid_all` (which needs `tensorLeft P` to preserve finite limits, i.e. the
flatness of `P`).

The construction of the action: at the level of the underlying presheaves of ℤ-modules one has the
sectionwise product `C(T,ℝ) ⊗ ∏^bndℝ(T) ⟶ ∏^bndℝ(T)`, `r ⊗ x ↦ (n ↦ r·x n)`
(`Work.ANALYTIC.BoundedRealAction.multPresheaf`, well defined because `T` is compact), the
unit section `1` (`Work.ANALYTIC.BoundedRealAction.unitPresheaf`), and the identity "multiplying by
`1` is the identity" (`Work.ANALYTIC.BoundedRealAction.mult_unitPresheaf`, proved sectionwise).
Transporting these across the canonical isomorphisms `Z ≅ L(S Z)` (sheafify the underlying
presheaf) and the monoidal structure of the localization gives the unital action
`Work.ANALYTIC.BoundedRealAction.realCondAct`, whose unitality
(`Work.ANALYTIC.BoundedRealAction.realCondAct_unital`) is the (weak) monoidal coherence
`Functor.LaxMonoidal.left_unitality` of sheafification together with the presheaf-level identities.
-/


open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid
open Opposite

noncomputable section

namespace Work.ANALYTIC

/-! ### The action of the condensed ring `ℝ` on `∏^bnd ℝ` -/
namespace BoundedRealAction

/-- Pointwise multiplication of a uniformly bounded family `x` of continuous real-valued functions
on the light profinite set `T` by a continuous function `r`.  The result is uniformly bounded
because `T` is compact, so that `r` is bounded. -/
noncomputable def boundedRealMul (T : LightProfinite) (r : C(T,ℝ)) (x : boundedRealSet T) :
    boundedRealSet T :=
  ⟨fun n => ⟨fun t => r t * x.1 n t, r.continuous.mul (x.1 n).continuous⟩, by
    obtain ⟨N, hN⟩ := x.2
    obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn r.continuous.continuousOn
    refine ⟨|M| * |N|, fun n t => ?_⟩
    calc |r t * x.1 n t| = |r t| * |x.1 n t| := abs_mul _ _
      _ ≤ |M| * |N| := mul_le_mul ((by simpa using hM t trivial : |r t| ≤ M).trans (le_abs_self M))
          ((hN n t).trans (le_abs_self N)) (abs_nonneg _) (abs_nonneg _)⟩

theorem boundedRealMul_add_left (T : LightProfinite) (r r' : C(T,ℝ)) (x : boundedRealSet T) :
    boundedRealMul T (r + r') x = boundedRealMul T r x + boundedRealMul T r' x := by
  refine Subtype.ext (funext fun n => ContinuousMap.ext fun t => ?_)
  simp only [boundedRealMul]
  simp [add_mul]

theorem boundedRealMul_add_right (T : LightProfinite) (r : C(T,ℝ)) (x y : boundedRealSet T) :
    boundedRealMul T r (x + y) = boundedRealMul T r x + boundedRealMul T r y := by
  refine Subtype.ext (funext fun n => ContinuousMap.ext fun t => ?_)
  simp only [boundedRealMul]
  simp [mul_add]

theorem boundedRealMul_smul_left (T : LightProfinite) (c : ℤ) (r : C(T,ℝ)) (x : boundedRealSet T) :
    boundedRealMul T (c • r) x = c • boundedRealMul T r x := by
  refine Subtype.ext (funext fun n => ContinuousMap.ext fun t => ?_)
  simp only [boundedRealMul, ContinuousMap.coe_mk, ContinuousMap.smul_apply, Submodule.coe_smul,
    Pi.smul_apply]
  ring

theorem boundedRealMul_smul_right (T : LightProfinite) (c : ℤ) (r : C(T,ℝ)) (x : boundedRealSet T) :
    boundedRealMul T r (c • x) = c • boundedRealMul T r x := by
  refine Subtype.ext (funext fun n => ContinuousMap.ext fun t => ?_)
  simp only [boundedRealMul, ContinuousMap.coe_mk, ContinuousMap.smul_apply, Submodule.coe_smul,
    Pi.smul_apply]
  ring

/-- The underlying presheaf of `boundedReal`. -/
noncomputable abbrev preB : Work.FLAT.PreMod := Work.FLAT.presheafOf.obj boundedReal

/-- The underlying presheaf of `realCond`. -/
noncomputable abbrev preR : Work.FLAT.PreMod := Work.FLAT.presheafOf.obj realCond

noncomputable def multPresheafApp (S : (LightProfinite.{0})ᵒᵖ) :
    preR.obj S ⊗ preB.obj S ⟶ preB.obj S :=
  ModuleCat.MonoidalCategory.tensorLift (fun r x => boundedRealMul S.unop r x)
    (boundedRealMul_add_left S.unop) (boundedRealMul_smul_left S.unop) (boundedRealMul_add_right S.unop)
    (boundedRealMul_smul_right S.unop)

theorem multPresheafApp_tmul (S : (LightProfinite.{0})ᵒᵖ) (r : C(S.unop,ℝ))
    (x : boundedRealSet S.unop) :
    multPresheafApp S (r ⊗ₜ x) = boundedRealMul S.unop r x := rfl

theorem multPresheaf_naturality (S S' : (LightProfinite.{0})ᵒᵖ) (f : S ⟶ S') :
    (preR ⊗ preB).map f ≫ multPresheafApp S' = multPresheafApp S ≫ preB.map f := by
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro r x
  rfl

noncomputable def multPresheaf : preR ⊗ preB ⟶ preB where
  app S := multPresheafApp S
  naturality := multPresheaf_naturality

noncomputable def unitPresheafApp (S : (LightProfinite.{0})ᵒᵖ) :
    (𝟙_ Work.FLAT.PreMod).obj S ⟶ preR.obj S :=
  ModuleCat.ofHom
    { toFun := fun z => ⟨fun _ => (z : ℝ), continuous_const⟩
      map_add' := by
        intro a b
        ext t
        simp only [ContinuousMap.add_apply, ContinuousMap.coe_mk]
        push_cast
        ring
      map_smul' := by
        intro c a
        ext t
        simp only [ContinuousMap.coe_mk, zsmul_eq_mul, Int.cast_mul, Int.cast_id]
        rw [ContinuousMap.mul_apply, ContinuousMap.intCast_apply, ContinuousMap.coe_mk]
        simp }

theorem unitPresheafApp_apply (S : (LightProfinite.{0})ᵒᵖ) (z : ℤ) :
    unitPresheafApp S z = ⟨fun _ => (z : ℝ), continuous_const⟩ := rfl

theorem unitPresheaf_naturality (S S' : (LightProfinite.{0})ᵒᵖ) (f : S ⟶ S') :
    (𝟙_ Work.FLAT.PreMod).map f ≫ unitPresheafApp S' = unitPresheafApp S ≫ preR.map f := by
  rw [CategoryTheory.Monoidal.tensorUnit_map]
  exact Category.id_comp _

noncomputable def unitPresheaf : 𝟙_ Work.FLAT.PreMod ⟶ preR where
  app S := unitPresheafApp S
  naturality := unitPresheaf_naturality

/-- Multiplying by an integer constant is the scalar action. -/
theorem boundedRealMul_intCast (T : LightProfinite) (z : ℤ) (x : boundedRealSet T) :
    boundedRealMul T ((z : ℤ) : C(T,ℝ)) x = z • x := by
  refine Subtype.ext (funext fun n => ContinuousMap.ext fun t => ?_)
  simp only [boundedRealMul, ContinuousMap.coe_mk, Submodule.coe_smul, Pi.smul_apply,
    ContinuousMap.smul_apply, ContinuousMap.mul_apply, ContinuousMap.intCast_apply,
    zsmul_eq_mul]

/-- Multiplication by the unit is the identity, sectionwise. -/
theorem mult_unitPresheaf_app (S : (LightProfinite.{0})ᵒᵖ) :
    (unitPresheafApp S ▷ preB.obj S) ≫ multPresheafApp S = (λ_ (preB.obj S)).hom := by
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro z x
  rw [ModuleCat.comp_apply, ModuleCat.MonoidalCategory.whiskerRight_apply]
  erw [multPresheafApp_tmul]
  rw [unitPresheafApp_apply]
  erw [ModuleCat.MonoidalCategory.leftUnitor_hom_apply]
  exact boundedRealMul_intCast S.unop z x

theorem mult_unitPresheaf : (unitPresheaf ▷ preB) ≫ multPresheaf = (λ_ preB).hom := by
  apply NatTrans.ext
  funext T
  exact mult_unitPresheaf_app T

noncomputable def realCondUnit : 𝟙_ LightCondAb ⟶ realCond :=
  Functor.LaxMonoidal.ε Work.FLAT.sheafify ≫ Work.FLAT.sheafify.map unitPresheaf ≫
    (Work.FLAT.sheafifyCounitIso realCond).inv

theorem realCondUnit_spec :
    realCondUnit ≫ (Work.FLAT.sheafifyCounitIso realCond).hom =
      Functor.LaxMonoidal.ε Work.FLAT.sheafify ≫ Work.FLAT.sheafify.map unitPresheaf := by
  simp only [realCondUnit, Category.assoc, Iso.inv_hom_id, Category.comp_id]

noncomputable def realCondAct : realCond ⊗ boundedReal ⟶ boundedReal :=
  (Work.FLAT.sheafifyCounitIso realCond).hom ▷ boundedReal ≫
    (Work.FLAT.sheafify.obj preR ◁ (Work.FLAT.sheafifyCounitIso boundedReal).hom) ≫
    Functor.LaxMonoidal.μ Work.FLAT.sheafify preR preB ≫
    Work.FLAT.sheafify.map multPresheaf ≫
    (Work.FLAT.sheafifyCounitIso boundedReal).inv

theorem realCondAct_unital : (realCondUnit ▷ boundedReal) ≫ realCondAct = (λ_ boundedReal).hom := by
  have hstepB : ∀ {Z : LightCondAb} (h : Work.FLAT.sheafify.obj preR ⊗ boundedReal ⟶ Z),
      (realCondUnit ▷ boundedReal) ≫ ((Work.FLAT.sheafifyCounitIso realCond).hom ▷ boundedReal) ≫ h =
        (Functor.LaxMonoidal.ε Work.FLAT.sheafify ▷ boundedReal) ≫
          (Work.FLAT.sheafify.map unitPresheaf ▷ boundedReal) ≫ h := by
    intro Z h
    rw [← Category.assoc, ← comp_whiskerRight, realCondUnit_spec, comp_whiskerRight, Category.assoc]
  have hstepC : ∀ {Z : LightCondAb}
      (h : Work.FLAT.sheafify.obj preR ⊗ Work.FLAT.sheafify.obj preB ⟶ Z),
      (Work.FLAT.sheafify.map unitPresheaf ▷ boundedReal) ≫
          (Work.FLAT.sheafify.obj preR ◁ (Work.FLAT.sheafifyCounitIso boundedReal).hom) ≫ h =
        (Work.FLAT.sheafify.obj (𝟙_ Work.FLAT.PreMod) ◁
            (Work.FLAT.sheafifyCounitIso boundedReal).hom) ≫
          (Work.FLAT.sheafify.map unitPresheaf ▷ Work.FLAT.sheafify.obj preB) ≫ h := by
    intro Z h
    rw [← Category.assoc, ← CategoryTheory.MonoidalCategory.whisker_exchange, Category.assoc]
  have hstepD : ∀ {Z : LightCondAb}
      (h : Work.FLAT.sheafify.obj (𝟙_ Work.FLAT.PreMod) ⊗
        Work.FLAT.sheafify.obj preB ⟶ Z),
      (Functor.LaxMonoidal.ε Work.FLAT.sheafify ▷ boundedReal) ≫
          (Work.FLAT.sheafify.obj (𝟙_ Work.FLAT.PreMod) ◁
            (Work.FLAT.sheafifyCounitIso boundedReal).hom) ≫ h =
        (𝟙_ LightCondAb ◁ (Work.FLAT.sheafifyCounitIso boundedReal).hom) ≫
          (Functor.LaxMonoidal.ε Work.FLAT.sheafify ▷ Work.FLAT.sheafify.obj preB) ≫ h := by
    intro Z h
    rw [← Category.assoc, ← CategoryTheory.MonoidalCategory.whisker_exchange, Category.assoc]
  have hstepE : ∀ {Z : LightCondAb} (h : Work.FLAT.sheafify.obj (preR ⊗ preB) ⟶ Z),
      (Work.FLAT.sheafify.map unitPresheaf ▷ Work.FLAT.sheafify.obj preB) ≫
          Functor.LaxMonoidal.μ Work.FLAT.sheafify preR preB ≫ h =
        Functor.LaxMonoidal.μ Work.FLAT.sheafify (𝟙_ Work.FLAT.PreMod) preB ≫
          Work.FLAT.sheafify.map (unitPresheaf ▷ preB) ≫ h := by
    intro Z h
    rw [← Category.assoc (f := Work.FLAT.sheafify.map unitPresheaf ▷ Work.FLAT.sheafify.obj preB)
        (g := Functor.LaxMonoidal.μ Work.FLAT.sheafify preR preB) (h := h)]
    rw [show (Work.FLAT.sheafify.map unitPresheaf ▷ Work.FLAT.sheafify.obj preB) ≫
          Functor.LaxMonoidal.μ Work.FLAT.sheafify preR preB =
        Functor.LaxMonoidal.μ Work.FLAT.sheafify (𝟙_ Work.FLAT.PreMod) preB ≫
          Work.FLAT.sheafify.map (unitPresheaf ▷ preB) from
        Functor.LaxMonoidal.μ_natural_left Work.FLAT.sheafify unitPresheaf preB]
    rw [Category.assoc]
  have hstepF : Work.FLAT.sheafify.map (unitPresheaf ▷ preB) ≫
      Work.FLAT.sheafify.map multPresheaf =
        Work.FLAT.sheafify.map ((unitPresheaf ▷ preB) ≫ multPresheaf) :=
    (Work.FLAT.sheafify.map_comp _ _).symm
  have hstepG : Work.FLAT.sheafify.map ((unitPresheaf ▷ preB) ≫ multPresheaf) =
      Work.FLAT.sheafify.map (λ_ preB).hom := by rw [mult_unitPresheaf]
  have hstepH : (Functor.LaxMonoidal.ε Work.FLAT.sheafify ▷ Work.FLAT.sheafify.obj preB) ≫
      Functor.LaxMonoidal.μ Work.FLAT.sheafify (𝟙_ Work.FLAT.PreMod) preB ≫
      Work.FLAT.sheafify.map (λ_ preB).hom = (λ_ (Work.FLAT.sheafify.obj preB)).hom :=
    (Functor.LaxMonoidal.left_unitality Work.FLAT.sheafify preB).symm
  have hstepI : (𝟙_ LightCondAb ◁ (Work.FLAT.sheafifyCounitIso boundedReal).hom) ≫
      (λ_ (Work.FLAT.sheafify.obj preB)).hom =
        (λ_ boundedReal).hom ≫ (Work.FLAT.sheafifyCounitIso boundedReal).hom :=
    MonoidalCategory.leftUnitor_naturality (Work.FLAT.sheafifyCounitIso boundedReal).hom
  have hkey : (realCondUnit ▷ boundedReal) ≫ realCondAct ≫
      (Work.FLAT.sheafifyCounitIso boundedReal).hom = (λ_ boundedReal).hom ≫
        (Work.FLAT.sheafifyCounitIso boundedReal).hom := by
    calc (realCondUnit ▷ boundedReal) ≫ realCondAct ≫
            (Work.FLAT.sheafifyCounitIso boundedReal).hom
        = (realCondUnit ▷ boundedReal) ≫ ((Work.FLAT.sheafifyCounitIso realCond).hom ▷ boundedReal) ≫
            (Work.FLAT.sheafify.obj preR ◁ (Work.FLAT.sheafifyCounitIso boundedReal).hom) ≫
            Functor.LaxMonoidal.μ Work.FLAT.sheafify preR preB ≫
            Work.FLAT.sheafify.map multPresheaf := by
          simp only [realCondAct, Category.assoc, Iso.inv_hom_id, Category.comp_id]
      _ = (Functor.LaxMonoidal.ε Work.FLAT.sheafify ▷ boundedReal) ≫
            (Work.FLAT.sheafify.map unitPresheaf ▷ boundedReal) ≫
            (Work.FLAT.sheafify.obj preR ◁ (Work.FLAT.sheafifyCounitIso boundedReal).hom) ≫
            Functor.LaxMonoidal.μ Work.FLAT.sheafify preR preB ≫
            Work.FLAT.sheafify.map multPresheaf := by
          rw [hstepB]
      _ = (Functor.LaxMonoidal.ε Work.FLAT.sheafify ▷ boundedReal) ≫
            (Work.FLAT.sheafify.obj (𝟙_ Work.FLAT.PreMod) ◁
              (Work.FLAT.sheafifyCounitIso boundedReal).hom) ≫
            (Work.FLAT.sheafify.map unitPresheaf ▷ Work.FLAT.sheafify.obj preB) ≫
            Functor.LaxMonoidal.μ Work.FLAT.sheafify preR preB ≫
            Work.FLAT.sheafify.map multPresheaf := by
          rw [hstepC]
      _ = (𝟙_ LightCondAb ◁ (Work.FLAT.sheafifyCounitIso boundedReal).hom) ≫
            (Functor.LaxMonoidal.ε Work.FLAT.sheafify ▷ Work.FLAT.sheafify.obj preB) ≫
            (Work.FLAT.sheafify.map unitPresheaf ▷ Work.FLAT.sheafify.obj preB) ≫
            Functor.LaxMonoidal.μ Work.FLAT.sheafify preR preB ≫
            Work.FLAT.sheafify.map multPresheaf := by
          rw [hstepD]
      _ = (𝟙_ LightCondAb ◁ (Work.FLAT.sheafifyCounitIso boundedReal).hom) ≫
            (Functor.LaxMonoidal.ε Work.FLAT.sheafify ▷ Work.FLAT.sheafify.obj preB) ≫
            Functor.LaxMonoidal.μ Work.FLAT.sheafify (𝟙_ Work.FLAT.PreMod) preB ≫
            Work.FLAT.sheafify.map (unitPresheaf ▷ preB) ≫ Work.FLAT.sheafify.map multPresheaf := by
          rw [hstepE]
      _ = (𝟙_ LightCondAb ◁ (Work.FLAT.sheafifyCounitIso boundedReal).hom) ≫
            (Functor.LaxMonoidal.ε Work.FLAT.sheafify ▷ Work.FLAT.sheafify.obj preB) ≫
            Functor.LaxMonoidal.μ Work.FLAT.sheafify (𝟙_ Work.FLAT.PreMod) preB ≫
            Work.FLAT.sheafify.map ((unitPresheaf ▷ preB) ≫ multPresheaf) := by
          rw [hstepF]
      _ = (𝟙_ LightCondAb ◁ (Work.FLAT.sheafifyCounitIso boundedReal).hom) ≫
            (Functor.LaxMonoidal.ε Work.FLAT.sheafify ▷ Work.FLAT.sheafify.obj preB) ≫
            Functor.LaxMonoidal.μ Work.FLAT.sheafify (𝟙_ Work.FLAT.PreMod) preB ≫
            Work.FLAT.sheafify.map (λ_ preB).hom := by
          rw [hstepG]
      _ = (𝟙_ LightCondAb ◁ (Work.FLAT.sheafifyCounitIso boundedReal).hom) ≫
            (λ_ (Work.FLAT.sheafify.obj preB)).hom := by
          rw [hstepH]
      _ = (λ_ boundedReal).hom ≫ (Work.FLAT.sheafifyCounitIso boundedReal).hom := hstepI
  calc (realCondUnit ▷ boundedReal) ≫ realCondAct
      = ((realCondUnit ▷ boundedReal) ≫ realCondAct ≫ (Work.FLAT.sheafifyCounitIso boundedReal).hom) ≫
          (Work.FLAT.sheafifyCounitIso boundedReal).inv := by
        simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    _ = ((λ_ boundedReal).hom ≫ (Work.FLAT.sheafifyCounitIso boundedReal).hom) ≫
          (Work.FLAT.sheafifyCounitIso boundedReal).inv := by rw [hkey]
    _ = (λ_ boundedReal).hom := by
        simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end BoundedRealAction

open BoundedRealAction

/-- **`∏^bnd ℝ` is solid-null** (AN2, REFS/03 §3, RC Thm 3.2.4(4)): every morphism from `∏^bnd ℝ`
in degree `0` into the derived inclusion of a complex of solid objects is zero. -/
theorem solidNull_boundedReal [CategoryTheory.Limits.PreservesFiniteLimits (CategoryTheory.MonoidalCategory.tensorLeft LightCondensed.P)] : Work.ANALYTIC.SolidNull ((DerivedCategory.singleFunctor LightCondAb 0).obj Work.ANALYTIC.boundedReal) := by
  obtain ⟨f, F, G, e₀, e₁, h₁, h₂, h₃, h₄, h₅⟩ := exists_realNullSeq realCondUnit
  refine solidNull_of_unit_action realCond boundedReal realCondAct f F G e₀ e₁ h₁ h₂ h₃ h₄ ?_
    (preSolid_all boundedReal)
  rw [← Category.assoc, ← comp_whiskerRight, h₅, realCondAct_unital]

end Work.ANALYTIC
