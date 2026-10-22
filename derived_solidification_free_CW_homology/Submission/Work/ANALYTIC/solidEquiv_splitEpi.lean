import Mathlib
import Submission.Work.ANALYTIC.Basic

/-!
# `SolidEquiv` of a split epimorphism vs. `SolidNull` of its kernel

Let `f : A ⟶ B` be a split epimorphism of light condensed abelian groups, with section
`s : B ⟶ A` (`s ≫ f = 𝟙 B`).  Then, writing `F := singleFunctor LightCondAb 0` for the
"complex concentrated in degree `0`" functor `LightCondAb ⥤ D(LightCondAb)`, the following
are equivalent:

* `F f` is a solid-equivalence, i.e. precomposition with `F f` is a bijection on morphisms
  into `ι N` for every complex `N` of solid objects;
* `F (ker f)` is solid-null, i.e. every morphism `F (ker f) ⟶ ι N` is zero.

The splitting makes `ker f ⟶ A` a complemented subobject: with `k := kernel.ι f` the kernel
inclusion and `p' : A ⟶ ker f` the lift of `𝟙 A - f ≫ s`, one has `k ≫ p' = 𝟙 (ker f)`,
`k ≫ f = 0` and `p' ≫ k + f ≫ s = 𝟙 A`.  Transported by the additive functor `F`, these are the
"biproduct" identities that make the equivalence formal:

* (`⟸`) every `ψ : F A ⟶ M` decomposes as
  `ψ = F f ≫ (F s ≫ ψ) + F p' ≫ (F k ≫ ψ)`, and the second summand vanishes because
  `F k ≫ ψ = 0` by solid-nullity of `F (ker f)`;
* (`⟹`) applying surjectivity to `F p' ≫ φ`, for `φ : F (ker f) ⟶ M`, exhibits `F p' ≫ φ` as a
  composite `F k ≫ (F f ≫ h)`, hence `φ = F k ≫ F p' ≫ φ = F k ≫ F f ≫ h = 0` because
  `F k ≫ F f = F (k ≫ f) = 0`.

The abstract form of the argument is isolated as `Work.ANALYTIC.splitEpi_solidEquiv_iff`; the
requested theorem is its instantiation.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

namespace Work.ANALYTIC

/-- **Abstract form.**  Let `C` be an abelian category, `D` a preadditive category and
`F : C ⥤ D` an additive functor.  For a split epimorphism `f : A ⟶ B` with section `s`, and any
family `M : ι → D` of test objects, precomposition with `F f` is a bijection on morphisms into
each `M i` if and only if there are no nonzero morphisms `F (ker f) ⟶ M i`.

The splitting enters only through the additive relations
`k ≫ p' = 𝟙`, `k ≫ f = 0`, `p' ≫ k + f ≫ s = 𝟙` on kernels, transported by `F`. -/
theorem splitEpi_solidEquiv_iff {C : Type*} [Category C] [Abelian C]
    {D : Type*} [Category D] [Preadditive D]
    (F : C ⥤ D) [F.Additive]
    {A B : C} (f : A ⟶ B) (s : B ⟶ A) (hs : s ≫ f = 𝟙 B)
    {ι : Type*} (M : ι → D) :
    (∀ i, Function.Bijective (fun g : F.obj B ⟶ M i => F.map f ≫ g)) ↔
      ∀ i, Subsingleton (F.obj (Limits.kernel f) ⟶ M i) := by
  have hp : (𝟙 A - f ≫ s) ≫ f = 0 := by
    rw [Preadditive.sub_comp, Category.id_comp, Category.assoc, hs, Category.comp_id, sub_self]
  let p' : A ⟶ Limits.kernel f := Limits.kernel.lift f (𝟙 A - f ≫ s) hp
  have hp' : p' ≫ Limits.kernel.ι f = 𝟙 A - f ≫ s := Limits.kernel.lift_ι f (𝟙 A - f ≫ s) hp
  have hkf : Limits.kernel.ι f ≫ f = 0 := Limits.kernel.condition f
  -- `k ≫ p' = 𝟙`, by cancelling the monomorphism `k`
  have hkp : Limits.kernel.ι f ≫ p' = 𝟙 (Limits.kernel f) := by
    apply (cancel_mono (Limits.kernel.ι f)).mp
    calc (Limits.kernel.ι f ≫ p') ≫ Limits.kernel.ι f
        = Limits.kernel.ι f ≫ (p' ≫ Limits.kernel.ι f) := Category.assoc _ _ _
      _ = Limits.kernel.ι f ≫ (𝟙 A - f ≫ s) := by rw [hp']
      _ = Limits.kernel.ι f - Limits.kernel.ι f ≫ (f ≫ s) := by
            rw [Preadditive.comp_sub, Category.comp_id]
      _ = Limits.kernel.ι f - (Limits.kernel.ι f ≫ f) ≫ s := by rw [Category.assoc]
      _ = Limits.kernel.ι f - 0 := by rw [hkf, Limits.zero_comp]
      _ = Limits.kernel.ι f := sub_zero _
      _ = 𝟙 (Limits.kernel f) ≫ Limits.kernel.ι f := (Category.id_comp _).symm
  -- the complement of `k` splits the identity
  have hsplit : p' ≫ Limits.kernel.ι f + f ≫ s = 𝟙 A := by
    rw [hp', sub_add_cancel]
  have hfs : f ≫ s = 𝟙 A - p' ≫ Limits.kernel.ι f := by
    rw [← hsplit]
    abel
  -- transport by the additive functor `F`
  have h1 : F.map (Limits.kernel.ι f) ≫ F.map f = 0 := by rw [← F.map_comp, hkf, F.map_zero]
  have h2 : F.map (Limits.kernel.ι f) ≫ F.map p' = 𝟙 (F.obj (Limits.kernel f)) := by
    rw [← F.map_comp, hkp, F.map_id]
  have h3 : F.map f ≫ F.map s = 𝟙 (F.obj A) - F.map p' ≫ F.map (Limits.kernel.ι f) := by
    rw [← F.map_comp, hfs, F.map_sub, F.map_comp, F.map_id]
  have h4 : F.map s ≫ F.map f = 𝟙 (F.obj B) := by rw [← F.map_comp, hs, F.map_id]
  constructor
  · -- surjectivity kills the kernel: `φ = F k ≫ F p' ≫ φ = F k ≫ F f ≫ h = 0`
    intro hb i
    have hbij := hb i
    refine ⟨fun φ η => ?_⟩
    have hzero : ∀ φ : F.obj (Limits.kernel f) ⟶ M i, φ = 0 := by
      intro φ
      obtain ⟨h, hh⟩ := hbij.2 (F.map p' ≫ φ)
      calc φ = 𝟙 (F.obj (Limits.kernel f)) ≫ φ := (Category.id_comp _).symm
        _ = (F.map (Limits.kernel.ι f) ≫ F.map p') ≫ φ := by rw [h2]
        _ = F.map (Limits.kernel.ι f) ≫ (F.map p' ≫ φ) := Category.assoc _ _ _
        _ = F.map (Limits.kernel.ι f) ≫ (F.map f ≫ h) := by rw [← hh]
        _ = (F.map (Limits.kernel.ι f) ≫ F.map f) ≫ h := (Category.assoc _ _ _).symm
        _ = 0 ≫ h := by rw [h1]
        _ = 0 := Limits.zero_comp
    rw [hzero φ, hzero η]
  · -- solid-nullity of the kernel gives surjectivity, via `𝟙 = F f ≫ F s + F p' ≫ F k`
    intro hsub i
    refine ⟨fun a b hab => ?_, fun ψ => ⟨F.map s ≫ ψ, ?_⟩⟩
    · have hab' : F.map f ≫ a = F.map f ≫ b := hab
      calc a = 𝟙 (F.obj B) ≫ a := (Category.id_comp _).symm
        _ = (F.map s ≫ F.map f) ≫ a := by rw [h4]
        _ = F.map s ≫ (F.map f ≫ a) := Category.assoc _ _ _
        _ = F.map s ≫ (F.map f ≫ b) := by rw [hab']
        _ = (F.map s ≫ F.map f) ≫ b := (Category.assoc _ _ _).symm
        _ = 𝟙 (F.obj B) ≫ b := by rw [h4]
        _ = b := Category.id_comp _
    · have hzero : F.map (Limits.kernel.ι f) ≫ ψ = 0 := @Subsingleton.elim _ (hsub i) _ _
      calc F.map f ≫ (F.map s ≫ ψ) = (F.map f ≫ F.map s) ≫ ψ := (Category.assoc _ _ _).symm
        _ = (𝟙 (F.obj A) - F.map p' ≫ F.map (Limits.kernel.ι f)) ≫ ψ := by rw [h3]
        _ = 𝟙 (F.obj A) ≫ ψ - (F.map p' ≫ F.map (Limits.kernel.ι f)) ≫ ψ :=
              Preadditive.sub_comp _ _ _
        _ = ψ - F.map p' ≫ (F.map (Limits.kernel.ι f) ≫ ψ) := by
              rw [Category.id_comp, Category.assoc]
        _ = ψ - 0 := by rw [hzero, Limits.comp_zero]
        _ = ψ := sub_zero _

/-- **Derived solidification of a split epimorphism.**  If `f : A ⟶ B` is a split epimorphism of
light condensed abelian groups (`s ≫ f = 𝟙 B`), then `f` becomes a solid-equivalence after
derived solidification if and only if the (light condensed abelian group) kernel of `f` is
solid-null. -/
theorem solidEquiv_splitEpi {A B : LightCondAb} (f : A ⟶ B) (s : B ⟶ A)
    (hs : CategoryTheory.CategoryStruct.comp s f = CategoryTheory.CategoryStruct.id B) :
    Submission.Blueprint.SolidEquiv
        (CategoryTheory.Functor.map (DerivedCategory.singleFunctor LightCondAb 0) f) ↔
      Work.ANALYTIC.SolidNull
        (CategoryTheory.Functor.obj (DerivedCategory.singleFunctor LightCondAb 0)
          (CategoryTheory.Limits.kernel f)) :=
  splitEpi_solidEquiv_iff (DerivedCategory.singleFunctor LightCondAb 0) f s hs
    (fun N : DSolid => derivedInclusion.obj N)

end Work.ANALYTIC
