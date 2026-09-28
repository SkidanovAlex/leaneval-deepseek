import Mathlib
import Submission.Work.Cohomology.mvCochainDefs

/-!
# Injectivity of the first map of the cochain Mayer–Vietoris sequence

`Work.Cohomology.mvCochainF U V` is the dual of the chain-level map `(smallOfU, -smallOfV)`,
which is the (surjective) second map of the Mayer–Vietoris short exact sequence of chain
complexes.  Dually, `mvCochainF` is injective.  This file proves the degreewise statement
`Work.Cohomology.mvCochainF_injective`.

The proof is elementwise.  The generators of `(smallChains U V).X n` are the `n`-simplices of the
small simplicial set, and each of them is the image of a simplex of `U` or of a simplex of `V`
(`Work.Cohomology.smallLift_cov`).  Hence a linear functional on the small `n`-chains that kills
the images of `smallOfU` and `smallOfV` is zero; the two components of `mvCochainF` are exactly
the transposes of these two maps.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-- The chain-level identity `chainComplexMap_ι_apply` in the form of generators, for an arbitrary
map of simplicial sets. -/
lemma dualMV_genSSet_chainComplexMap {X Y : SSet} (f : X ⟶ Y) (n : ℕ) (x : X _⦋n⦌) :
    genSSet Y n ((f.app (Opposite.op ⦋n⦌)) x)
      = ModuleCat.Hom.hom ((SSet.chainComplexMap f (ModuleCat.of ℤ ℤ)).f n) (genSSet X n x) := by
  have h := congrArg (fun g => ModuleCat.Hom.hom g (1 : ℤ))
    (SSet.ι_chainComplexMap_f X Y f (ModuleCat.of ℤ ℤ) x)
  rw [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  simpa [genSSet] using h.symm

/-- A `ℤ`-linear functional on the `n`-chains of a simplicial set which vanishes on all the
generators `genSSet Y n s` is zero. -/
lemma dualMV_eq_zero_of_forall_genSSet {Y : SSet} {n : ℕ}
    (φ : ↑((Y.chainComplex (ModuleCat.of ℤ ℤ)).X n) →ₗ[ℤ] ℤ)
    (h : ∀ s : Y _⦋n⦌, φ (genSSet Y n s) = 0) : φ = 0 := by
  have hhom : ModuleCat.ofHom φ = 0 := by
    apply SSet.chainComplex_hom_ext (X := Y) (R := ModuleCat.of ℤ ℤ) (n := n)
    intro s
    apply ModuleCat.hom_ext
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, comp_zero, ModuleCat.hom_zero]
    apply LinearMap.ext_ring
    rw [LinearMap.comp_apply, LinearMap.zero_apply]
    simpa [genSSet] using h s
  simpa [ModuleCat.hom_ofHom, ModuleCat.hom_zero] using congrArg ModuleCat.Hom.hom hhom

variable {X : TopCat} (U V : Set X) (n : ℕ)

/-- On the generators, `smallOfU` sends a simplex of `U` to the corresponding generator of the
small chains. -/
lemma dualMV_genSSet_smallOfU (a : (TopCat.toSSet.obj (TopCat.of U)) _⦋n⦌) :
    genSSet (smallSSet U V) n ((smallLiftU U V).app (Opposite.op ⦋n⦌) a)
      = ModuleCat.Hom.hom ((smallOfU U V).f n)
          (genSSet (TopCat.toSSet.obj (TopCat.of U)) n a) :=
  dualMV_genSSet_chainComplexMap (smallLiftU U V) n a

/-- On the generators, `smallOfV` sends a simplex of `V` to the corresponding generator of the
small chains. -/
lemma dualMV_genSSet_smallOfV (b : (TopCat.toSSet.obj (TopCat.of V)) _⦋n⦌) :
    genSSet (smallSSet U V) n ((smallLiftV U V).app (Opposite.op ⦋n⦌) b)
      = ModuleCat.Hom.hom ((smallOfV U V).f n)
          (genSSet (TopCat.toSSet.obj (TopCat.of V)) n b) :=
  dualMV_genSSet_chainComplexMap (smallLiftV U V) n b

/-- The first component of `mvCochainF` at degree `n`, evaluated on a cochain: it is the transpose
of `smallOfU`, i.e. precomposition with `smallOfU`. -/
lemma dualMV_mvCochainF_fst_apply (x : (smallChains U V).X n →ₗ[ℤ] ℤ) :
    ModuleCat.Hom.hom ((biprod.fst : cochainU U V ⊞ cochainV U V ⟶ cochainU U V).f n)
        (ModuleCat.Hom.hom ((mvCochainF U V).f n) (x : ↑((dualComplex ℤ (smallChains U V)).X n)))
      = x.comp ((smallOfU U V).f n).hom := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, mvCochainF_fst, dualComplexMap_f]
  exact dualComplexMapComp_apply' ℤ (singularChains ℤ (TopCat.of U)) (smallChains U V)
    (smallOfU U V) n x

/-- The second component of `mvCochainF` at degree `n`, evaluated on a cochain: it is minus the
transpose of `smallOfV`. -/
lemma dualMV_mvCochainF_snd_apply (x : (smallChains U V).X n →ₗ[ℤ] ℤ) :
    ModuleCat.Hom.hom ((biprod.snd : cochainU U V ⊞ cochainV U V ⟶ cochainV U V).f n)
        (ModuleCat.Hom.hom ((mvCochainF U V).f n) (x : ↑((dualComplex ℤ (smallChains U V)).X n)))
      = -(x.comp ((smallOfV U V).f n).hom) := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, mvCochainF_snd, HomologicalComplex.neg_f_apply,
    ModuleCat.hom_neg, LinearMap.neg_apply]
  congr 1

/-- Two degree-`n` cochains of `C^{U,V}_*(X)` with the same image under `mvCochainF` are equal. -/
lemma dualMV_mvCochainF_apply_injective (x y : (smallChains U V).X n →ₗ[ℤ] ℤ)
    (hxy : ModuleCat.Hom.hom ((mvCochainF U V).f n)
        (x : ↑((dualComplex ℤ (smallChains U V)).X n)) =
      ModuleCat.Hom.hom ((mvCochainF U V).f n)
        (y : ↑((dualComplex ℤ (smallChains U V)).X n))) : x = y := by
  -- the two cochains agree after precomposition with `smallOfU` ...
  have hU : ∀ a : ↑((singularChains ℤ (TopCat.of U)).X n),
      x (ModuleCat.Hom.hom ((smallOfU U V).f n) a)
        = y (ModuleCat.Hom.hom ((smallOfU U V).f n) a) := by
    intro a
    have h := congrArg (fun (w : ↑((cochainU U V ⊞ cochainV U V).X n)) => ModuleCat.Hom.hom
      ((biprod.fst : cochainU U V ⊞ cochainV U V ⟶ cochainU U V).f n) w) hxy
    rw [dualMV_mvCochainF_fst_apply U V n, dualMV_mvCochainF_fst_apply U V n] at h
    simpa [LinearMap.comp_apply] using LinearMap.congr_fun h a
  -- ... and after precomposition with `smallOfV`
  have hV : ∀ b : ↑((singularChains ℤ (TopCat.of V)).X n),
      x (ModuleCat.Hom.hom ((smallOfV U V).f n) b)
        = y (ModuleCat.Hom.hom ((smallOfV U V).f n) b) := by
    intro b
    have h := congrArg (fun (w : ↑((cochainU U V ⊞ cochainV U V).X n)) => ModuleCat.Hom.hom
      ((biprod.snd : cochainU U V ⊞ cochainV U V ⟶ cochainV U V).f n) w) hxy
    rw [dualMV_mvCochainF_snd_apply U V n, dualMV_mvCochainF_snd_apply U V n] at h
    have h' : x.comp ((smallOfV U V).f n).hom = y.comp ((smallOfV U V).f n).hom :=
      neg_injective h
    simpa [LinearMap.comp_apply] using LinearMap.congr_fun h' b
  -- hence they agree on every generator of the small chains
  have hgen : ∀ s : (smallSSet U V) _⦋n⦌,
      x (genSSet (smallSSet U V) n s) = y (genSSet (smallSSet U V) n s) := by
    intro s
    rcases smallLift_cov U V (Opposite.op ⦋n⦌) s with ⟨a, ha⟩ | ⟨b, hb⟩
    · have key : genSSet (smallSSet U V) n s
          = ModuleCat.Hom.hom ((smallOfU U V).f n)
              (genSSet (TopCat.toSSet.obj (TopCat.of U)) n a) := by
        rw [← ha]; exact dualMV_genSSet_smallOfU U V n a
      rw [key]
      exact hU (genSSet (TopCat.toSSet.obj (TopCat.of U)) n a)
    · have key : genSSet (smallSSet U V) n s
          = ModuleCat.Hom.hom ((smallOfV U V).f n)
              (genSSet (TopCat.toSSet.obj (TopCat.of V)) n b) := by
        rw [← hb]; exact dualMV_genSSet_smallOfV U V n b
      rw [key]
      exact hV (genSSet (TopCat.toSSet.obj (TopCat.of V)) n b)
  -- and a functional that vanishes on all generators is zero
  suffices hsub : x - y = 0 by exact sub_eq_zero.mp hsub
  refine dualMV_eq_zero_of_forall_genSSet (x - y) (fun s => ?_)
  rw [LinearMap.sub_apply, sub_eq_zero]
  exact hgen s

theorem mvCochainF_injective {X : TopCat} (U V : Set X) (n : ℕ) :
    Function.Injective (ModuleCat.Hom.hom ((Work.Cohomology.mvCochainF U V).f n)) := by
  intro x y hxy
  exact dualMV_mvCochainF_apply_injective U V n (x : (smallChains U V).X n →ₗ[ℤ] ℤ)
    (y : (smallChains U V).X n →ₗ[ℤ] ℤ) hxy

end

end Work.Cohomology
