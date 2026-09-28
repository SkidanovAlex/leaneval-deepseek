import Mathlib
import Submission.Work.Serre.Defs
import Submission.Work.Stems.HurewiczNeutral
import Submission.Work.RatHurewicz.isZero_ratH_one_of_torsion
import Submission.Work.Stems.HurewiczFirstDegree
import Submission.Work.RatHurewicz.intRat_mono_of_torsion_ker
import Submission.Work.RatHurewicz.freeTorsionModel
import Submission.Work.StemsB.WangCohRat
import Submission.Work.Rat.RankOneC1.fg_ratModule_structure_of_ratEmbedding

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Rat.RankOneC1

open CategoryTheory CategoryTheory.Limits

noncomputable section

set_option linter.style.haveILetI false

theorem fgSubgroup_rank_le_one_of
    (h3 : ∀ {X : Type} [TopologicalSpace X] [PathConnectedSpace X] (x₀ : X),
      (∀ a b : HomotopyGroup (Fin 1) X x₀, a * b = b * a) →
      letI hGr : Group (HomotopyGroup (Fin 1) X x₀) := HomotopyGroup.group (Fin 1)
      ∀ a : HomotopyGroup (Fin 1) X x₀,
        Work.Stems.hurewiczMapN 1 (le_refl 1) x₀ a = 0 → ∃ N : ℕ, 0 < N ∧ a ^ N = 1)
    {X : Type} [TopologicalSpace X] [PathConnectedSpace X] (x₀ : X)
    (hcomm : ∀ a b : HomotopyGroup (Fin 1) X x₀, a * b = b * a)
    (h1 : Nonempty (Work.Serre.ratH (TopCat.of X) 1 ≅ ModuleCat.of ℚ ℚ))
    (H : Subgroup (HomotopyGroup (Fin 1) X x₀)) [Group.FG H] :
    ∃ (r : ℕ) (F : Type) (_ : AddCommGroup F) (_ : Finite F), r ≤ 1 ∧
      Nonempty (Additive H ≃+ (Fin r → ℤ) × F) := by
  classical
  haveI : Nonempty (Fin 1) := ⟨⟨0, by norm_num⟩⟩
  have hHfg : Group.FG H := ‹Group.FG H›
  -- The subgroup `H` is abelian, and we work with it additively.
  letI hcommH : CommGroup ↥H :=
    { (inferInstance : Group ↥H) with mul_comm := fun a b => Subtype.ext (hcomm a.1 b.1) }
  -- `H₁(X;ℤ)`, presented in two ways: the singular-chain homology `A0`, and the same object with
  -- the canonical `ℤ`-module structure `A1` (they are propositionally equal).
  let A0 : ModuleCat ℤ := (Work.Stems.chains (TopCat.of X)).homology 1
  let A1 : ModuleCat ℤ := @ModuleCat.of ℤ _ ↥A0 _ (AddCommGroup.toIntModule ↥A0)
  have hAgen : ∀ (A : ModuleCat ℤ),
      A = @ModuleCat.of ℤ _ ↥A _ (AddCommGroup.toIntModule ↥A) := by
    intro A; cases A; congr 1; exact Subsingleton.elim _ _
  have hA : A0 = A1 := hAgen A0
  -- The Hurewicz map kills the unit.
  have hone : Work.Stems.hurewiczMapN 1 (le_refl 1) x₀
      (1 : HomotopyGroup (Fin 1) X x₀) = 0 := by
    have h := Work.Stems.hurewiczMapN_mul 0 x₀
      (1 : HomotopyGroup (Fin 1) X x₀) (1 : HomotopyGroup (Fin 1) X x₀)
    rw [mul_one] at h
    refine add_left_cancel (a := Work.Stems.hurewiczMapN 1 (le_refl 1) x₀
      (1 : HomotopyGroup (Fin 1) X x₀)) ?_
    rw [add_zero]
    exact h.symm
  -- The Hurewicz map restricted to `H`, as an additive homomorphism.
  let φH : Additive ↥H →+ ↥A0 :=
    { toFun := fun a => Work.Stems.hurewiczMapN 1 (le_refl 1) x₀
        ((Additive.toMul a : ↥H) : HomotopyGroup (Fin 1) X x₀)
      map_zero' := by
        show Work.Stems.hurewiczMapN 1 (le_refl 1) x₀
          (((Additive.toMul (0 : Additive ↥H)) : ↥H) : HomotopyGroup (Fin 1) X x₀) = 0
        have h1 : ((Additive.toMul (0 : Additive ↥H) : ↥H) : HomotopyGroup (Fin 1) X x₀)
            = 1 := rfl
        rw [h1]
        exact hone
      map_add' := fun a b =>
        Work.Stems.hurewiczMapN_mul 0 x₀
          ((Additive.toMul a : ↥H) : HomotopyGroup (Fin 1) X x₀)
          ((Additive.toMul b : ↥H) : HomotopyGroup (Fin 1) X x₀) }
  haveI hfinH : Module.Finite ℤ (Additive ↥H) := AddMonoid.FG.to_moduleFinite_int
  -- Package the Hurewicz map as a morphism of `ℤ`-modules into `A1`.
  letI hAm : Module ℤ ↥A0 := AddCommGroup.toIntModule ↥A0
  let hlin := φH.toIntLinearMap
  let φ : ModuleCat.of ℤ (Additive ↥H) ⟶ A1 :=
    @ModuleCat.ofHom ℤ _ (Additive ↥H) ↥A0 _ _ _ (AddCommGroup.toIntModule ↥A0) hlin
  have hφa : ∀ a : Additive ↥H, (ModuleCat.Hom.hom φ) a = φH a := fun a => rfl
  -- The kernel of the Hurewicz map is torsion, by `h3`.
  have hker : ∀ a : Additive ↥H,
      (ModuleCat.Hom.hom φ) a = 0 → ∃ N : ℕ, 0 < N ∧ N • a = 0 := by
    intro a ha
    have ha' : Work.Stems.hurewiczMapN 1 (le_refl 1) x₀
        ((Additive.toMul a : ↥H) : HomotopyGroup (Fin 1) X x₀) = 0 := by
      have hφ' : (ModuleCat.Hom.hom φ) a = φH a := rfl
      rw [hφ'] at ha
      exact ha
    obtain ⟨N, hNpos, hN⟩ := h3 x₀ hcomm
      ((Additive.toMul a : ↥H) : HomotopyGroup (Fin 1) X x₀) ha'
    refine ⟨N, hNpos, ?_⟩
    have hpoweq : (Additive.toMul a : ↥H) ^ N = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hN
    rw [show a = Additive.ofMul (Additive.toMul a) from (ofMul_toMul a).symm,
      ← ofMul_pow N (Additive.toMul a), hpoweq]
    rfl
  -- Rationalising a map with torsion kernel is injective.
  have hmono : CategoryTheory.Mono ((Work.StemsB.RatBC.IntRat).map φ) :=
    Work.RatHurewicz.intRat_mono_of_torsion_ker φ hker
  have hinj : Function.Injective
      (ConcreteCategory.hom ((Work.StemsB.RatBC.IntRat).map φ)) :=
    (ModuleCat.mono_iff_injective _).mp hmono
  -- `H₁(X;ℚ) ≅ ℚ`, and it is the rationalisation of `H₁(X;ℤ)`.
  obtain ⟨eQ⟩ := h1
  let e2 : (Work.StemsB.RatBC.IntRat).obj A1 ≅ ModuleCat.of ℚ ℚ :=
    (Work.StemsB.RatBC.IntRat.mapIso (eqToIso hA)).symm ≪≫
      (Work.StemsB.homologyBaseChangeRat (TopCat.of X) 1).symm ≪≫ eQ
  have hE2inj : Function.Injective (ConcreteCategory.hom e2.hom) :=
    (ModuleCat.mono_iff_injective e2.hom).mp (inferInstance : CategoryTheory.Mono e2.hom)
  let f : (↥((Work.StemsB.RatBC.IntRat).obj
        (ModuleCat.of ℤ (Additive ↥H)))) →ₗ[ℚ] ℚ :=
    (ConcreteCategory.hom e2.hom).comp
      (ConcreteCategory.hom ((Work.StemsB.RatBC.IntRat).map φ))
  have hf : Function.Injective f := hE2inj.comp hinj
  obtain ⟨r, F, hFadd, hFfin, hr, ⟨e⟩⟩ :=
    fg_ratModule_structure_of_ratEmbedding (M := Additive ↥H) (f := f) hf
  exact ⟨r, F, hFadd, hFfin, hr, ⟨e⟩⟩

end

end Work.Rat.RankOneC1
