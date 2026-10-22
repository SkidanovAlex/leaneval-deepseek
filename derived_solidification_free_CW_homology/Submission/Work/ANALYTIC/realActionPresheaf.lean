import Mathlib
import Submission.Work.ANALYTIC.RealSide
import Submission.Work.FLAT.Main

/-!
# The sectionwise action of `ℝ` on `∏_ℕ ℝ` at the level of presheaves

The light condensed abelian groups `realCond = ℝ` (`S ↦ C(S,ℝ)`) and `prodReal = ∏_ℕ ℝ`
(`S ↦ ℕ → C(S,ℝ)`) of `Submission/Work/ANALYTIC/RealSide.lean` are sheafifications of presheaves
of `ℤ`-modules on light profinite sets, and the coordinatewise multiplication
`C(S,ℝ) ⊗ (ℕ → C(S,ℝ)) → (ℕ → C(S,ℝ))`, `r ⊗ x ↦ (n ↦ r · x n)` is a *sectionwise* natural
transformation

`mulPre : realPresheaf ⊗ prodRealPresheaf ⟶ prodRealPresheaf`

of presheaves (here the tensor product of presheaves is the pointwise one).  Its unit law
`(unitPre ▷ prodRealPresheaf) ≫ mulPre = (λ_ _).hom`, together with the fact that sheafification
is a strong monoidal functor, is what turns `prodReal` into a module object over `realCond`
(see `Submission/Work/ANALYTIC/solidNull_prodReal.lean`).

Because the tensor product of presheaves is computed sectionwise, all the work happens on the
`ℤ`-modules `C(S,ℝ)` and `ℕ → C(S,ℝ)` of sections over a light profinite set `S`.  We keep the
sections in their "raw" form (`C(S,ℝ)`, `ℕ → C(S,ℝ)`) throughout, since the coercion
`↥(F.obj S)` of a section module is not unfolded by type class search; the `set_option` below
makes the definitional equalities between `↥(F.obj S)` and `C(S,ℝ)` usable by tactics.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Work.ANALYTIC

/-- The underlying presheaf of `realCond`: `S ↦ C(S,ℝ)`.  This is `presheafOf.obj realCond` by
definition, recorded here so that the sectionwise statements below stay readable. -/
abbrev realPresheaf' : Work.FLAT.PreMod := Work.FLAT.presheafOf.obj realCond

/-- The underlying presheaf of `prodReal`: `S ↦ ℕ → C(S,ℝ)`. -/
abbrev prodRealPresheaf' : Work.FLAT.PreMod := Work.FLAT.presheafOf.obj prodReal

theorem realPresheaf'_eq : realPresheaf' = realPresheaf := rfl

theorem prodRealPresheaf'_eq : prodRealPresheaf' = prodRealPresheaf := rfl

/-! ## The sectionwise multiplication -/

/-- **The sectionwise multiplication** `C(S,ℝ) ⊗ (ℕ → C(S,ℝ)) → (ℕ → C(S,ℝ))`, as a morphism of
`ℤ`-modules over a light profinite set `S`. -/
def realMulS (S : (LightProfinite.{0})ᵒᵖ) :
    ModuleCat.of ℤ C(S.unop,ℝ) ⊗ ModuleCat.of ℤ (ℕ → C(S.unop,ℝ)) ⟶
      ModuleCat.of ℤ (ℕ → C(S.unop,ℝ)) :=
  ModuleCat.ofHom (TensorProduct.lift
    (LinearMap.mk₂ ℤ (fun (r : C(S.unop,ℝ)) (x : ℕ → C(S.unop,ℝ)) => r • x)
      (fun r r' x => add_smul r r' x)
      (fun a r x => smul_assoc a r x)
      (fun r x x' => smul_add r x x')
      (fun r a x => (smul_comm r a x).symm)))

/-- The value of `realMulS` on a pure tensor. -/
theorem realMulS_tmul (S : (LightProfinite.{0})ᵒᵖ) (r : C(S.unop,ℝ))
    (x : ℕ → C(S.unop,ℝ)) : realMulS S (r ⊗ₜ[ℤ] x) = r • x := by
  show (TensorProduct.lift (LinearMap.mk₂ ℤ (fun r x => r • x) _ _ _ _)
      (r ⊗ₜ[ℤ] x)) = r • x
  rw [TensorProduct.lift.tmul]
  rfl

/-- The action of the presheaf map `realPresheaf.map f` on sections. -/
theorem realPresheaf_map_apply {S T : (LightProfinite.{0})ᵒᵖ} (f : S ⟶ T) (g : C(S.unop,ℝ)) :
    ((realPresheaf.map f) g : C(T.unop,ℝ)) =
      g.comp (LightProfinite.toTopCat.map f.unop).hom := rfl

/-- The action of the presheaf map `prodRealPresheaf.map f` on sections. -/
theorem prodRealPresheaf_map_apply {S T : (LightProfinite.{0})ᵒᵖ} (f : S ⟶ T)
    (x : ℕ → C(S.unop,ℝ)) :
    ((prodRealPresheaf.map f) x : ℕ → C(T.unop,ℝ)) =
      fun n => (x n).comp (LightProfinite.toTopCat.map f.unop).hom := rfl

/-- The component at `S` of the sectionwise multiplication, with the domain written in the
"unfolded" form `F.obj S ⊗ G.obj S` so that componentwise arguments apply without unfolding. -/
def realMulComp (S : (LightProfinite.{0})ᵒᵖ) :
    (realPresheaf'.obj S ⊗ prodRealPresheaf'.obj S) ⟶ prodRealPresheaf'.obj S := realMulS S

/-- **The sectionwise multiplication is a natural transformation of presheaves.** -/
def realMulPre : realPresheaf' ⊗ prodRealPresheaf' ⟶ prodRealPresheaf' where
  app S := realMulComp S
  naturality {S T} f := by
    apply ModuleCat.hom_ext
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp]
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul r x =>
        show realMulS T (((realPresheaf.map f) r : C(T.unop,ℝ)) ⊗ₜ[ℤ]
            ((prodRealPresheaf.map f) x : ℕ → C(T.unop,ℝ))) =
          ((prodRealPresheaf.map f) (realMulS S (r ⊗ₜ[ℤ] x)) : ℕ → C(T.unop,ℝ))
        rw [realMulS_tmul, realMulS_tmul]
        funext n
        rw [realPresheaf_map_apply, prodRealPresheaf_map_apply, prodRealPresheaf_map_apply]
        ext s
        simp only [ContinuousMap.mul_apply, ContinuousMap.comp_apply, Pi.smul_apply,
          smul_eq_mul]
    | add u v hu hv => rw [map_add, map_add, hu, hv]

/-! ## The unit -/

/-- **The sectionwise unit** `ℤ → C(S,ℝ)`, the constant function `1` (as a `ℤ`-linear map). -/
def realUnitS (S : (LightProfinite.{0})ᵒᵖ) :
    ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ C(S.unop,ℝ) :=
  ModuleCat.ofHom
    { toFun := fun z => z • (1 : C(S.unop,ℝ))
      map_add' := by intro a b; rw [add_smul]
      map_smul' := by intro a b; simp }

/-- The value of `realUnitS`: it is the constant function `z`. -/
theorem realUnitS_eq (S : (LightProfinite.{0})ᵒᵖ) (z : ℤ) :
    (ModuleCat.Hom.hom (realUnitS S) z : C(S.unop,ℝ)) = z • (1 : C(S.unop,ℝ)) := rfl

/-- The component at `S` of the unit, in the "unfolded" form. -/
def realUnitComp (S : (LightProfinite.{0})ᵒᵖ) :
    (𝟙_ (ModuleCat ℤ)) ⟶ realPresheaf'.obj S := realUnitS S

/-- **The sectionwise unit is a natural transformation of presheaves.** -/
def realUnitPre : 𝟙_ Work.FLAT.PreMod ⟶ realPresheaf' where
  app S := realUnitComp S
  naturality {S T} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    show ((realPresheaf.map f) ((realUnitS S) z) : C(T.unop,ℝ)) = (realUnitS T) z
    rw [realUnitS_eq, realUnitS_eq, realPresheaf_map_apply]
    rfl

/-- **The unit law, on sections.** -/
theorem realUnitS_mulS (S : (LightProfinite.{0})ᵒᵖ) (z : ℤ) (m : ℕ → C(S.unop,ℝ)) :
    (ModuleCat.Hom.hom (realMulS S))
      ((ModuleCat.Hom.hom (realUnitS S) z : C(S.unop,ℝ)) ⊗ₜ[ℤ] m) = z • m := by
  show (TensorProduct.lift (LinearMap.mk₂ ℤ
      (fun (r : C(S.unop,ℝ)) (x : ℕ → C(S.unop,ℝ)) => r • x) _ _ _ _))
      (((ModuleCat.Hom.hom (realUnitS S) z : C(S.unop,ℝ))) ⊗ₜ[ℤ] m) = z • m
  rw [TensorProduct.lift.tmul, realUnitS_eq]
  show (z • (1 : C(S.unop,ℝ))) • m = z • m
  rw [smul_assoc, one_smul]

/-- **The unit law at a single light profinite set.**  The sectionwise multiplication is unital
for the sectionwise unit, and the presheaf unitor is computed sectionwise. -/
theorem realUnitComp_mulComp (S : (LightProfinite.{0})ᵒᵖ) :
    (realUnitComp S ▷ prodRealPresheaf'.obj S) ≫ realMulComp S =
      (λ_ (prodRealPresheaf'.obj S)).hom := by
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_comp]
  apply LinearMap.ext
  intro z
  rw [LinearMap.comp_apply]
  induction z using TensorProduct.inductionOn with
  | tmul r m =>
      rw [ModuleCat.MonoidalCategory.whiskerRight_apply,
        ModuleCat.MonoidalCategory.leftUnitor_hom_apply]
      exact realUnitS_mulS S r m
  | add u v hu hv => simp only [map_add, hu, hv]

/-- **The presheaf version of the unit law**: `(unitPre ▷ prodRealPresheaf) ≫ mulPre` is the left
unitor of the presheaf category. -/
theorem realUnitPre_mulPre :
    (realUnitPre ▷ prodRealPresheaf') ≫ realMulPre = (λ_ prodRealPresheaf').hom := by
  apply NatTrans.ext
  funext S
  show (realUnitComp S ▷ prodRealPresheaf'.obj S) ≫ realMulComp S =
    (λ_ (prodRealPresheaf'.obj S)).hom
  exact realUnitComp_mulComp S

end Work.ANALYTIC
