import Mathlib
import Submission.Work.Cohomology.Pullback

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Homotopy invariance of singular cohomology

Two homotopic continuous maps `f g : X ⟶ Y` induce the same map on singular cohomology with
coefficients in a commutative ring `R`.

The proof transposes the chain homotopy supplied by Mathlib
(`TopCat.Homotopy.singularChainComplexFunctorObjMap`, which provides a chain homotopy between the
induced maps on singular chains, thanks to homotopy invariance of the homology of simplicial sets)
into a cochain homotopy between the induced maps on the dual cochain complexes.  Concretely, if
`s : C_*(X) ⟶ C_*(Y)` is the homotopy with components `s_n : C_n(X) ⟶ C_{n+1}(Y)`, then the
transposes `s_n^T : C^{n+1}(Y) ⟶ C^n(X)` assemble into a cochain homotopy, where the component at
`(i, i-1)` is the transpose of `s_{i-1}`.  Homotopic cochain maps induce equal maps on homology.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology Limits

namespace Work.Cohomology

noncomputable section

theorem homotopyInvariance (R : Type) [CommRing R] (X Y : TopCat) {f g : X ⟶ Y}
    (H : TopCat.Homotopy f g) (n : ℕ) :
    Work.Cohomology.singularCohomologyMap R X Y f n =
      Work.Cohomology.singularCohomologyMap R X Y g n := by
  -- the chain homotopy induced by `H`
  let S : Homotopy (Work.Cohomology.chainMap R X Y f) (Work.Cohomology.chainMap R X Y g) :=
    H.singularChainComplexFunctorObjMap (ModuleCat.of R R)
  -- the transposed cochain homotopy: the component at `(i, i-1)` is the transpose of `S i (i-1)`
  let h : ∀ i j, Work.Cohomology.dualChains R Y i ⟶ Work.Cohomology.dualChains R X j :=
    fun i j => if hij : j + 1 = i then ModuleCat.ofHom ((S.hom j i).hom.dualMap) else 0
  have hzero : ∀ i j, ¬ (ComplexShape.up ℕ).Rel j i → h i j = 0 := by
    intro i j hij
    rw [ComplexShape.up_Rel] at hij
    dsimp only [h]
    rw [dif_neg hij]
  have hL : ∀ (i : ℕ) (φ : Work.Cohomology.dualChains R Y i)
      (x : (Work.Cohomology.singularChains R X).X i),
      (show (Work.Cohomology.singularChains R X).X i →ₗ[R] R from
        ((Work.Cohomology.dualChainMap R X Y f).f i).hom φ) x
        = φ (((Work.Cohomology.chainMap R X Y f).f i).hom x) := by
    intro i φ x
    exact Work.Cohomology.cochainPullbackHom_apply (R := R) X Y f i φ x
  have hR : ∀ (i : ℕ) (φ : Work.Cohomology.dualChains R Y i)
      (x : (Work.Cohomology.singularChains R X).X i),
      (show (Work.Cohomology.singularChains R X).X i →ₗ[R] R from
        ((Work.Cohomology.dualChainMap R X Y g).f i).hom φ) x
        = φ (((Work.Cohomology.chainMap R X Y g).f i).hom x) := by
    intro i φ x
    exact Work.Cohomology.cochainPullbackHom_apply (R := R) X Y g i φ x
  -- evaluation of the "`dNext`" part of the transposed homotopy
  have hdNext : ∀ (i : ℕ) (φ : Work.Cohomology.dualChains R Y i)
      (x : (Work.Cohomology.singularChains R X).X i),
      (show (Work.Cohomology.singularChains R X).X i →ₗ[R] R from
        (dNext (C := Work.Cohomology.singularCochainComplex R Y)
          (D := Work.Cohomology.singularCochainComplex R X) i h).hom φ) x
        = φ (((Work.Cohomology.singularChains R Y).d (i+1) i).hom ((S.hom i (i+1)).hom x)) := by
    intro i φ x
    rw [Homotopy.dNext_cochainComplex (P := Work.Cohomology.singularCochainComplex R Y)
      (Q := Work.Cohomology.singularCochainComplex R X) h i]
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, h, dif_pos rfl, ModuleCat.hom_ofHom]
    erw [LinearMap.dualMap_apply]
    simp only [Work.Cohomology.singularCochainComplex, CochainComplex.of_d,
      Work.Cohomology.dualDifferential, ModuleCat.hom_ofHom]
    rfl
  -- evaluation of the "`prevD`" part of the transposed homotopy
  have hprevD : ∀ (i : ℕ) (φ : Work.Cohomology.dualChains R Y i)
      (x : (Work.Cohomology.singularChains R X).X i),
      (show (Work.Cohomology.singularChains R X).X i →ₗ[R] R from
        (prevD (C := Work.Cohomology.singularCochainComplex R Y)
          (D := Work.Cohomology.singularCochainComplex R X) i h).hom φ) x
        = φ ((S.hom (i-1) i).hom (((Work.Cohomology.singularChains R X).d i (i-1)).hom x)) := by
    intro i φ x
    rcases i with _ | k
    · rw [Homotopy.prevD_zero_cochainComplex (P := Work.Cohomology.singularCochainComplex R Y)
        (Q := Work.Cohomology.singularCochainComplex R X) h]
      simp only [ModuleCat.hom_zero, LinearMap.zero_apply]
      rw [show (0:ℕ) - 1 = 0 from rfl]
      have hz : (Work.Cohomology.singularChains R X).d 0 0 = 0 :=
        (Work.Cohomology.singularChains R X).shape 0 0 (by rw [ComplexShape.down_Rel]; decide)
      rw [hz]
      simp only [ModuleCat.hom_zero, LinearMap.zero_apply, map_zero]
    · rw [Homotopy.prevD_succ_cochainComplex (P := Work.Cohomology.singularCochainComplex R Y)
        (Q := Work.Cohomology.singularCochainComplex R X) h k]
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, h, dif_pos rfl, ModuleCat.hom_ofHom]
      erw [LinearMap.dualMap_apply']
      simp only [Work.Cohomology.singularCochainComplex, CochainComplex.of_d,
        Work.Cohomology.dualDifferential, ModuleCat.hom_ofHom]
      rfl
  -- the chain homotopy relation, evaluated
  have hS : ∀ (i : ℕ) (x : (Work.Cohomology.singularChains R X).X i),
      ((Work.Cohomology.chainMap R X Y f).f i).hom x
        = (S.hom (i-1) i).hom (((Work.Cohomology.singularChains R X).d i (i-1)).hom x)
          + ((Work.Cohomology.singularChains R Y).d (i+1) i).hom ((S.hom i (i+1)).hom x)
          + ((Work.Cohomology.chainMap R X Y g).f i).hom x := by
    intro i x
    rw [S.comm i]
    simp only [ModuleCat.hom_add, LinearMap.add_apply]
    rw [dNext_nat (Work.Cohomology.singularChains R X) (Work.Cohomology.singularChains R Y) i S.hom,
      prevD_eq S.hom (j := i) (j' := i+1) (by rw [ComplexShape.down_Rel])]
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  -- the transposed maps form a cochain homotopy
  have hcomm : ∀ i, (Work.Cohomology.dualChainMap R X Y f).f i
      = dNext (C := Work.Cohomology.singularCochainComplex R Y)
          (D := Work.Cohomology.singularCochainComplex R X) i h
        + prevD (C := Work.Cohomology.singularCochainComplex R Y)
          (D := Work.Cohomology.singularCochainComplex R X) i h
        + (Work.Cohomology.dualChainMap R X Y g).f i := by
    intro i
    apply ModuleCat.hom_ext
    show (ModuleCat.Hom.hom ((Work.Cohomology.dualChainMap R X Y f).f i) :
        Work.Cohomology.dualChains R Y i →ₗ[R] Work.Cohomology.dualChains R X i)
      = (ModuleCat.Hom.hom (dNext (C := Work.Cohomology.singularCochainComplex R Y)
          (D := Work.Cohomology.singularCochainComplex R X) i h
        + prevD (C := Work.Cohomology.singularCochainComplex R Y)
          (D := Work.Cohomology.singularCochainComplex R X) i h
        + (Work.Cohomology.dualChainMap R X Y g).f i) :
        Work.Cohomology.dualChains R Y i →ₗ[R] Work.Cohomology.dualChains R X i)
    apply LinearMap.ext; intro φ
    apply LinearMap.ext; intro x
    simp only [ModuleCat.hom_add, LinearMap.add_apply]
    change (show (Work.Cohomology.singularChains R X).X i →ₗ[R] R from
        (ModuleCat.Hom.hom ((Work.Cohomology.dualChainMap R X Y f).f i)) φ) x
      = (show (Work.Cohomology.singularChains R X).X i →ₗ[R] R from
          (ModuleCat.Hom.hom (dNext (C := Work.Cohomology.singularCochainComplex R Y)
            (D := Work.Cohomology.singularCochainComplex R X) i h)) φ) x
        + (show (Work.Cohomology.singularChains R X).X i →ₗ[R] R from
            (ModuleCat.Hom.hom (prevD (C := Work.Cohomology.singularCochainComplex R Y)
              (D := Work.Cohomology.singularCochainComplex R X) i h)) φ) x
        + (show (Work.Cohomology.singularChains R X).X i →ₗ[R] R from
            (ModuleCat.Hom.hom ((Work.Cohomology.dualChainMap R X Y g).f i)) φ) x
    rw [hL i φ x, hdNext i φ x, hprevD i φ x, hR i φ x, hS i x]
    simp only [map_add]
    abel
  let T : Homotopy (Work.Cohomology.dualChainMap R X Y f) (Work.Cohomology.dualChainMap R X Y g) :=
    { hom := h, zero := hzero, comm := hcomm }
  exact T.homologyMap_eq n

end

end Work.Cohomology
