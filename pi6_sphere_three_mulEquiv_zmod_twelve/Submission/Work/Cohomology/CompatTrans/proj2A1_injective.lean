import Mathlib
import Submission.Work.Cohomology.CompatTrans.prodSphereDefs
import Submission.Work.Cohomology.CompatTrans.homotopyEquiv_A1set
import Submission.Work.Cohomology.sphereHomologyTop
import Submission.Work.Cohomology.sphereVanishing
import Submission.Work.Cohomology.homologyContractible
import Submission.Work.Cohomology.localHomology

/-!
# The projection `(Sᵖ ∖ {Nₚ}) × Sᵍ ⟶ Sᵍ` is injective on homology

`A1set p q = (Sᵖ ∖ {Nₚ}) × Sᵍ` is the first piece of the cover of the punctured product
`Sᵖ × Sᵍ ∖ {pt}` used in the Mayer–Vietoris computation of `Hₙ(Sᵖ × Sᵍ)`.  The first factor is
contractible, so the projection `proj₂A1 p q : A1set p q ⟶ Sᵍ` onto the second factor is a homotopy
equivalence: it has the section `secA1` sending `y` to `(pt0, y)` (where `pt0` is a point of the
punctured sphere `Sᵖ ∖ {Nₚ}`), and `secA1 ∘ proj₂A1` is homotopic to the identity of `A1set p q`
because `Sᵖ ∖ {Nₚ}` is contractible.  Hence the induced map on singular homology is an isomorphism
(homotopy invariance of singular homology, `Work.Cohomology.homologyEquiv`), in particular
injective.

The homotopy is produced without any explicit formula: `id_nullhomotopic` supplies a homotopy on
the punctured sphere from the identity to the constant map at `pt0`, one applies `Homotopy.prodMap`
to add the identity on the second factor, and one conjugates by the homeomorphism
`PhiA1 : A1set p q ≃ₜ (Sᵖ ∖ {Nₚ}) × Sᵍ`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology Limits
open scoped Topology

namespace Work.Cohomology

noncomputable section

/-! ## The section of `proj₂A1` -/

/-- A point of the punctured sphere `Sᵖ ∖ {Nₚ}` at which the identity is null-homotopic: the
witness provided by contractibility. -/
noncomputable def pt0 (p : ℕ) : ↥(PunctP p) := by
  haveI : ContractibleSpace ↥(PunctP p) := contractible_compl_sphN p
  exact (id_nullhomotopic ↥(PunctP p)).choose

/-- The defining property of `pt0`: the identity of `Sᵖ ∖ {Nₚ}` is homotopic to the constant map
at `pt0`. -/
lemma pt0_homotopic (p : ℕ) :
    ContinuousMap.Homotopic (ContinuousMap.id ↥(PunctP p))
      (ContinuousMap.const _ (pt0 p)) := by
  haveI : ContractibleSpace ↥(PunctP p) := contractible_compl_sphN p
  exact (id_nullhomotopic ↥(PunctP p)).choose_spec

/-- The homeomorphism `A1set p q ≅ (Sᵖ ∖ {Nₚ}) × Sᵍ`. -/
def PhiA1 (p q : ℕ) : ↥(A1set p q) ≃ₜ ↥(PunctP p) × ↥(sphSet (q+1)) :=
  (homeo_A1_A2 p q).trans (homeo_A2_prod p q)

/-- Through `PhiA1`, the second factor is exactly `proj₂A1`. -/
lemma PhiA1_snd (p q : ℕ) (z : ↥(A1set p q)) :
    (PhiA1 p q z).2 = proj₂A1 p q z := rfl

/-- The section `y ↦ (pt0, y)` of the projection `proj₂A1`. -/
def secA1 (p q : ℕ) : sphTop (q+1) ⟶ TopCat.of ↥(A1set p q) :=
  TopCat.ofHom (((PhiA1 p q).symm : C(↥(PunctP p) × ↥(sphSet (q+1)), ↥(A1set p q))).comp
    (ContinuousMap.prodMk (ContinuousMap.const _ (pt0 p)) (ContinuousMap.id _)))

/-- The section `secA1`, evaluated. -/
lemma secA1_hom_apply (p q : ℕ) (y : ↥(sphSet (q+1))) :
    (secA1 p q).hom y
      = ((PhiA1 p q).symm : C(↥(PunctP p) × ↥(sphSet (q+1)), ↥(A1set p q))) (pt0 p, y) := rfl

/-- `secA1` is a section of `proj₂A1`. -/
lemma secA1_comp_proj₂A1 (p q : ℕ) : secA1 p q ≫ proj₂A1 p q = 𝟙 (sphTop (q+1)) := by
  apply TopCat.hom_ext
  rw [TopCat.hom_comp, TopCat.hom_id]
  apply ContinuousMap.ext
  intro y
  rw [ContinuousMap.comp_apply, ContinuousMap.id_apply, secA1_hom_apply]
  show (PhiA1 p q ((PhiA1 p q).symm (pt0 p, y))).2 = y
  rw [Homeomorph.apply_symm_apply]

/-! ## A general homotopy-conjugation lemma -/

/-- Conjugating a homotopy of endomorphisms of `Y` by a homeomorphism `e : X ≃ₜ Y`. -/
def homotopy_conj_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) {f₀ f₁ : C(Y, Y)} (F : f₀.Homotopy f₁) :
    (((e.symm : C(Y, X)).comp (f₀.comp (e : C(X, Y))))).Homotopy
      (((e.symm : C(Y, X)).comp (f₁.comp (e : C(X, Y))))) :=
  (ContinuousMap.Homotopy.refl (e.symm : C(Y, X))).comp (F.compContinuousMap (e : C(X, Y)))

/-! ## The projection is injective on homology -/

/-- The projection `proj₂A1 : A1set p q ⟶ Sᵍ` induces an injective map on homology in positive
degrees.  (`A1set p q = (Sᵖ \ {N_p}) × Sᵍ` inside `Yset p q`; the first factor is contractible, so
this projection is a homotopy equivalence onto `Sᵍ`.) -/
lemma proj2A1_injective (p q n : ℕ) (hq : 1 ≤ q) (hn : 1 ≤ n) :
    Function.Injective (HomologicalComplex.homologyMap
      (chainMap ℤ (TopCat.of ↥(A1set p q)) (sphTop (q + 1)) (proj₂A1 p q)) n).hom := by
  haveI : ContractibleSpace ↥(PunctP p) := contractible_compl_sphN p
  -- the product homotopy, from `(pt0, ·)` to the identity on `(Sᵖ ∖ {Nₚ}) × Sᵍ`
  have h2 : (ContinuousMap.id ↥(PunctP p)).prodMap (ContinuousMap.id ↥(sphSet (q+1)))
      = ContinuousMap.id (↥(PunctP p) × ↥(sphSet (q+1))) := by
    apply ContinuousMap.ext
    intro z
    rw [ContinuousMap.prodMap_apply]
    rfl
  have hF : ((ContinuousMap.const ↥(PunctP p) (pt0 p)).prodMap
        (ContinuousMap.id ↥(sphSet (q+1)))).Homotopy
      (ContinuousMap.id (↥(PunctP p) × ↥(sphSet (q+1)))) :=
    ((pt0_homotopic p).some.symm.prodMap (ContinuousMap.Homotopy.refl (ContinuousMap.id _))).cast
      rfl h2
  -- conjugate it along the homeomorphism `PhiA1`
  have hconj := homotopy_conj_homeomorph (PhiA1 p q) hF
  have hpair : ∀ w : ↥(PunctP p) × ↥(sphSet (q+1)),
      Prod.map (⇑(ContinuousMap.const (↥(PunctP p)) (pt0 p)))
        (⇑(ContinuousMap.id ↥(sphSet (q+1)))) w = (pt0 p, w.2) := by
    rintro ⟨a, b⟩
    rfl
  have hA : ((PhiA1 p q).symm : C(↥(PunctP p) × ↥(sphSet (q+1)), ↥(A1set p q))).comp
      (((ContinuousMap.const ↥(PunctP p) (pt0 p)).prodMap
        (ContinuousMap.id ↥(sphSet (q+1)))).comp
        ((PhiA1 p q) : C(↥(A1set p q), ↥(PunctP p) × ↥(sphSet (q+1)))))
      = (secA1 p q).hom.comp (proj₂A1 p q).hom := by
    apply ContinuousMap.ext
    intro z
    simp only [ContinuousMap.comp_apply]
    rw [ContinuousMap.prodMap_apply, hpair, secA1_hom_apply]
    rfl
  have hB : ((PhiA1 p q).symm : C(↥(PunctP p) × ↥(sphSet (q+1)), ↥(A1set p q))).comp
      ((ContinuousMap.id _).comp
        ((PhiA1 p q) : C(↥(A1set p q), ↥(PunctP p) × ↥(sphSet (q+1)))))
      = ContinuousMap.id ↥(A1set p q) := by
    apply ContinuousMap.ext
    intro z
    simp only [ContinuousMap.comp_apply, ContinuousMap.id_apply]
    exact Homeomorph.symm_apply_apply (PhiA1 p q) z
  -- so `proj₂A1 ∘ secA1` is homotopic to the identity of `A1set p q`
  have h1 : TopCat.Homotopy (proj₂A1 p q ≫ secA1 p q) (𝟙 (TopCat.of ↥(A1set p q))) :=
    hconj.cast hA hB
  have hsec : TopCat.Homotopy (secA1 p q ≫ proj₂A1 p q) (𝟙 (sphTop (q+1))) := by
    rw [secA1_comp_proj₂A1]
    exact TopCat.Homotopy.refl _
  -- homotopy invariance of singular homology upgrades this to an isomorphism on homology
  haveI : IsIso (HomologicalComplex.homologyMap
      (chainMap ℤ (TopCat.of ↥(A1set p q)) (sphTop (q+1)) (proj₂A1 p q)) n) :=
    homologyEquiv ℤ (TopCat.of ↥(A1set p q)) (sphTop (q+1)) (proj₂A1 p q) (secA1 p q) h1 hsec n
  exact (ModuleCat.mono_iff_injective _).1 inferInstance

end

end Work.Cohomology
