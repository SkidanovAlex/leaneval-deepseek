import Mathlib
import Submission.Work.Cohomology.SmallChains
import Submission.Work.Cohomology.SmallChainsIsoAux

namespace Work.Cohomology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial
-- `Work.Cohomology.smallProj U V n` is the projection of the singular chains of `X` onto the
-- small chains of the cover, defined in `SmallChainsIsoAux.lean` by the coproduct universal
-- property (`SSet.isColimitChainComplexXCofan`) as: `gen X n σ ↦ genSSet (smallSSet U V) n ⟨σ,h⟩`
-- for a small `σ` and `gen X n σ ↦ 0` otherwise.  The proof of `smallToSing_f_injective` in that
-- file establishes both `hcomp` (the first conjunct) and `hfac` (which gives the other two
-- conjuncts by applying to `1 : ℤ`, cf. `genSSet`/`smallToSing_gen`), but neither is exported.
theorem smallProj_spec {X : TopCat} (U V : Set X) :
    (∀ n, (Work.Cohomology.smallToSing U V).f n ≫ Work.Cohomology.smallProj U V n
        = 𝟙 ((Work.Cohomology.smallChains U V).X n)) ∧
    (∀ n (σ : Work.Cohomology.Simplex X n) (h : Work.Cohomology.IsSmall U V σ),
      (Work.Cohomology.smallProj U V n) (Work.Cohomology.gen X n σ)
        = Work.Cohomology.genSSet (Work.Cohomology.smallSSet U V) n ⟨σ, h⟩) ∧
    (∀ n (σ : Work.Cohomology.Simplex X n), ¬ Work.Cohomology.IsSmall U V σ →
      (Work.Cohomology.smallProj U V n) (Work.Cohomology.gen X n σ) = 0) := by
  classical
  -- The defining universal property of `smallProj`: it maps each generator `σ` to the generator
  -- of the small chains when `σ` is small, and to `0` otherwise.
  have hfac : ∀ (n : ℕ) (σ : (TopCat.toSSet.obj X) _⦋n⦌),
      (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ ≫ smallProj U V n
        = if h : IsSmall U V σ then (smallSSet U V).ιChainComplex ⟨σ, h⟩ else 0 :=
    fun n σ => Cofan.IsColimit.fac _ _ _
  refine ⟨?_, ?_, ?_⟩
  · intro n
    apply SSet.chainComplex_hom_ext (X := smallSSet U V) (R := ModuleCat.of ℤ ℤ) (n := n)
    intro x
    have h1 : (smallSSet U V).ιChainComplex (R := ModuleCat.of ℤ ℤ) x ≫ (smallToSing U V).f n
        = (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) x.1 := by
      have h := SSet.ι_chainComplexMap_f (f := (smallSubcomplex U V).ι) (R := ModuleCat.of ℤ ℤ)
        (X := smallSSet U V) (Y := TopCat.toSSet.obj X) (n := n) x
      simpa using h
    rw [← Category.assoc, h1, hfac]
    split_ifs with h
    · simp
    · exact absurd x.2 h
  · intro n σ h
    have key := congrArg (fun (g : ModuleCat.of ℤ ℤ ⟶ (smallChains U V).X n) =>
        (ModuleCat.Hom.hom g) (1 : ℤ)) (hfac n σ)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at key
    rw [dif_pos h] at key
    simp only [gen, genSSet] at key ⊢
    exact key
  · intro n σ h
    have key := congrArg (fun (g : ModuleCat.of ℤ ℤ ⟶ (smallChains U V).X n) =>
        (ModuleCat.Hom.hom g) (1 : ℤ)) (hfac n σ)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at key
    rw [dif_neg h] at key
    simp only [gen, ModuleCat.hom_zero, LinearMap.zero_apply] at key ⊢
    exact key

end Work.Cohomology
