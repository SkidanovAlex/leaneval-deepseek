import Mathlib
import Submission.Work.ThomBordism.chartModelClassDefs
import Submission.Work.Tubular.relKronH_natural
import Submission.Work.Tubular.ThomRepOfLocalDegree

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000

namespace Work.ThomBordism

/-!
# The pairing of the ambient standard class is the pairing of the chart model class

`Work.ThomBordism.value_eq_chartModelClass` is a formal consequence of the naturality of the
relative Kronecker pairing `Work.Tubular.relKronH_natural` under the *map of pairs*
`(C.U, tubeInvPunct) → (ν, ν∖0)` induced by the tube inverse `C.inv`:

* the pullback of `chartModelClass` along that map is `ambientStandardClass`
  (`Work.ThomBordism.ambientStandardClass_eq_chartModelClass`), and
* the pushforward of `δ` along that map is `collapseRelK8` (the hypothesis `hδ`), and
  `tubeInvHomology` *is* that pushforward by definition.

The only bookkeeping is the degree: the target statement pairs at degree `k + 8`, while the class
`chartModelClass` (and the naturality statement) live at degree `8 + k`.  The transfer between the
two degrees is isolated in `chainsHomologyCast` and `relKronH_cast_snd` below.
-/

/-- **Degree cast for the homology of a chain complex**: the only reason for this definition (rather
than a plain `▸` at the point of use) is that the degree cast of a *homology class of a concrete
complex* is awkward to elaborate when the expected type is still a metavariable; with `X`, `A`, `a`
and `b` as variables the substitution elaborates smoothly. -/
def chainsHomologyCast {K : ChainComplex (ModuleCat ℤ) ℕ} {a b : ℕ} (h : a = b)
    (x : K.homology a) : K.homology b := h ▸ x

/-- **The relative Kronecker pairing across a change of degree**: pairing at degree `b` a class cast
down from degree `a` is the same as pairing at degree `a` after casting the homology class up to
degree `a`.  This is `Work.Tubular.relKronH_cast` with the cast on the homology side transported
into `chainsHomologyCast`. -/
lemma relKronH_cast_right {X : TopCat} {A : Set X} {a b : ℕ} (h : a = b)
    (β : (Work.Cohomology.relComplex ℤ X A).homology a)
    (c : (Work.Cohomology.relChains X A).homology b) :
    Work.Tubular.relKronH X A b (h ▸ β) c
      = Work.Tubular.relKronH X A a β (h.symm ▸ c) := by
  have hc : h ▸ (h.symm ▸ c) = c := by cases h; rfl
  calc Work.Tubular.relKronH X A b (h ▸ β) c
      = Work.Tubular.relKronH X A b (h ▸ β) (h ▸ (h.symm ▸ c)) := by rw [hc]
      _ = Work.Tubular.relKronH X A a β (h.symm ▸ c) :=
        Work.Tubular.relKronH_cast h β (h.symm ▸ c)

/-- **The relative Kronecker pairing across a change of degree**, in the form in which it is used
below: the cast on the homology argument is written through `chainsHomologyCast`. -/
lemma relKronH_cast_snd {X : TopCat} {A : Set X} {a b : ℕ} (h : a = b)
    (β : (Work.Cohomology.relComplex ℤ X A).homology a)
    (c : (Work.Cohomology.relChains X A).homology b) :
    Work.Tubular.relKronH X A b (h ▸ β) c
      = Work.Tubular.relKronH X A a β (chainsHomologyCast h.symm c) :=
  relKronH_cast_right h β c

/-- **A degree cast commutes with `homologyMap`**, in the `chainsHomologyCast` form. -/
lemma homologyMap_chainsCast {K L : ChainComplex (ModuleCat ℤ) ℕ} (φ : K ⟶ L) {a b : ℕ}
    (h : a = b) (x : K.homology a) :
    (HomologicalComplex.homologyMap φ b).hom (chainsHomologyCast h x)
      = chainsHomologyCast h ((HomologicalComplex.homologyMap φ a).hom x) :=
  Work.Tubular.homologyMap_cast_nat φ h x

theorem value_eq_chartModelClass {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    {R : ℝ} (hR : 0 ≤ R) (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R) (x : V.pt)
    (hcont : Continuous fun p : Work.Tubular.NormalTotal E =>
      Work.ThomBordism.chartAffine E x (Work.ThomBordism.cap E ε p))
    (δ : (Work.Cohomology.relChains (TopCat.of ↥C.U)
        (Work.ThomBordism.tubeInvPunct E C)).homology (k + 8))
    (hδ : Work.ThomBordism.tubeInvHomology E C δ
      = Work.Tubular.collapseRelK8 C g hg hR hbox) :
    Work.Tubular.relKronH (TopCat.of ↥C.U) (Work.ThomBordism.tubeInvPunct E C) (k + 8)
        ((Nat.add_comm 8 k) ▸ Work.ThomBordism.ambientStandardClass E C x) δ
      = Work.Tubular.relKronH (TopCat.of (Work.Tubular.NormalTotal E))
          (Work.Tubular.normalNonzero E) (k + 8)
          ((Nat.add_comm 8 k) ▸ Work.ThomBordism.chartModelClass E C x hcont)
          (Work.Tubular.collapseRelK8 C g hg hR hbox) := by
  -- the induced map on the punctured parts, copied from the definition of `tubeInvHomology`
  let G : TopCat.of (Work.ThomBordism.tubeInvPunct E C) ⟶
      TopCat.of (Work.Tubular.normalNonzero E) :=
    TopCat.ofHom ⟨fun y : ↥(Work.ThomBordism.tubeInvPunct E C) =>
        ⟨C.inv y.1.1, y.2⟩,
      Continuous.subtype_mk
        (((Work.ThomBordism.tubeInvMap E C).continuous).comp continuous_subtype_val)
        (fun y => (show C.inv (↑(y : ↥C.U) : Work.Tubular.Euc (8 + k)) ∈
          Work.Tubular.normalNonzero E from y.2))⟩
  -- the compatibility of the two maps with the inclusions
  let W : CategoryTheory.CategoryStruct.comp
        (Work.Cohomology.subtypeIncl (TopCat.of ↥C.U) (Work.ThomBordism.tubeInvPunct E C))
        (TopCat.ofHom (Work.ThomBordism.tubeInvMap E C))
      = CategoryTheory.CategoryStruct.comp G
        (Work.Cohomology.subtypeIncl (TopCat.of (Work.Tubular.NormalTotal E))
          (Work.Tubular.normalNonzero E)) := by
    apply TopCat.ext; intro a; rfl
  -- the induced map of relative chain complexes
  let φh : Work.Cohomology.relChains (TopCat.of ↥C.U) (Work.ThomBordism.tubeInvPunct E C) ⟶
      Work.Cohomology.relChains (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E) :=
    Work.Cohomology.relChainsMapOf (TopCat.of ↥C.U) (TopCat.of (Work.Tubular.NormalTotal E))
      (Work.ThomBordism.tubeInvPunct E C) (Work.Tubular.normalNonzero E)
      (TopCat.ofHom (Work.ThomBordism.tubeInvMap E C)) G W
  -- `φh` is the map whose induced map on homology is `tubeInvHomology`
  have hkey : (HomologicalComplex.homologyMap φh (k + 8)).hom δ
      = Work.Tubular.collapseRelK8 C g hg hR hbox := by
    rw [show (HomologicalComplex.homologyMap φh (k + 8)).hom δ
        = Work.ThomBordism.tubeInvHomology E C δ from rfl]
    exact hδ
  -- naturality of the relative Kronecker pairing under the tube inverse
  have hnat := Work.Tubular.relKronH_natural
    (X := TopCat.of ↥C.U) (Y := TopCat.of (Work.Tubular.NormalTotal E))
    (A := Work.ThomBordism.tubeInvPunct E C) (B := Work.Tubular.normalNonzero E)
    (TopCat.ofHom (Work.ThomBordism.tubeInvMap E C)) G (fun y hy => hy) W
    (8 + k) (Work.ThomBordism.chartModelClass E C x hcont)
    (chainsHomologyCast (K := Work.Cohomology.relChains (TopCat.of ↥C.U)
      (Work.ThomBordism.tubeInvPunct E C)) (Nat.add_comm 8 k).symm δ)
  rw [relKronH_cast_snd (Nat.add_comm 8 k) (Work.ThomBordism.ambientStandardClass E C x) δ]
  rw [← Work.ThomBordism.ambientStandardClass_eq_chartModelClass E C x hcont]
  rw [hnat]
  rw [homologyMap_chainsCast φh (Nat.add_comm 8 k).symm δ]
  rw [hkey]
  rw [← relKronH_cast_snd (Nat.add_comm 8 k) (Work.ThomBordism.chartModelClass E C x hcont)
    (Work.Tubular.collapseRelK8 C g hg hR hbox)]

end Work.ThomBordism
