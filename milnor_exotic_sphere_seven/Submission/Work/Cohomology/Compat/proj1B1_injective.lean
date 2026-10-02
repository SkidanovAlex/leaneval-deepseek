import Mathlib
import Submission.Work.Cohomology.Compat.prodSphereDefs
import Submission.Work.Cohomology.Compat.homotopyEquiv_B1set
import Submission.Work.Cohomology.sphereHomologyTop
import Submission.Work.Cohomology.sphereVanishing
import Submission.Work.Cohomology.homologyContractible
import Submission.Work.Cohomology.localHomology

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The projection `B1set p q ⟶ Sᵖ` is injective on homology

`B1set p q = Sᵖ × (Sᵍ ∖ {N_q})` (inside `Yset p q`), and the second factor is contractible
(`Work.Cohomology.contractible_compl_sphN`).  Consequently the first projection
`proj₁B1 p q : ↥(B1set p q) ⟶ Sᵖ` is a homotopy equivalence, hence induces an isomorphism — in
particular an injection — on singular homology in every degree.

The homotopy equivalence is exhibited explicitly:

* `prodFstHomotopyEquiv X q` : the projection `X × (Sᵍ ∖ {N_q}) ⟶ X` is a homotopy equivalence,
  with explicit section `x ↦ (x, y₀)` where `y₀` is a point at which the identity of the
  punctured sphere is nullhomotopic;
* `proj₁B1HomotopyEquiv p q` : conjugating by the homeomorphism `B1Homeo p q` gives a homotopy
  equivalence `↥(B1set p q) ≃ₕ Sᵖ` whose forward map is (definitionally) `proj₁B1 p q`.

Composing with `Work.Cohomology.homologyEquiv` and using that an isomorphism in `ModuleCat ℤ` is a
monomorphism gives the result.
-/

namespace Work.Cohomology.Compat

noncomputable section

open CategoryTheory

set_option linter.style.haveILetI false

/-- The punctured sphere `Sᵍ ∖ {N_q}`. -/
abbrev PunctSph (q : ℕ) : Type := {y : ↥(sphSet (q+1)) // y ≠ sphN q}

/-- The punctured sphere is contractible (`Work.Cohomology.contractible_compl_sphN`). -/
local instance punctSphContractible (q : ℕ) : ContractibleSpace (PunctSph q) :=
  contractible_compl_sphN q

/-- A point of the punctured sphere, namely the value of the identity at the end of a
nullhomotopy of the identity. -/
noncomputable def punctSphPt (q : ℕ) : PunctSph q :=
  Classical.choose (id_nullhomotopic (PunctSph q))

/-- The identity of the punctured sphere is homotopic to the constant map at `punctSphPt q`. -/
lemma punctSphPt_spec (q : ℕ) : (ContinuousMap.id (PunctSph q)).Homotopic
    (ContinuousMap.const (PunctSph q) (punctSphPt q)) :=
  Classical.choose_spec (id_nullhomotopic (PunctSph q))

/-- If `Y` is contractible, the first projection `X × Y ⟶ X` is a homotopy equivalence.  Here we
record the homotopy equivalence with its *explicit* forward map `ContinuousMap.fst` and the
explicit section `x ↦ (x, y₀)`, where `y₀ := punctSphPt q` is the point provided by a
nullhomotopy of `id_Y`. -/
noncomputable def prodFstHomotopyEquiv (X : Type*) [TopologicalSpace X] (q : ℕ) :
    ContinuousMap.HomotopyEquiv (X × PunctSph q) X where
  toFun := ContinuousMap.fst
  invFun := ContinuousMap.prodMk (ContinuousMap.id X) (ContinuousMap.const X (punctSphPt q))
  left_inv := by
    have h1 : (ContinuousMap.prodMk (ContinuousMap.id X)
          (ContinuousMap.const X (punctSphPt q))).comp ContinuousMap.fst
        = (ContinuousMap.id X).prodMap (ContinuousMap.const (PunctSph q) (punctSphPt q)) := by
      ext p <;> rfl
    have h2 : (ContinuousMap.id X).prodMap (ContinuousMap.id (PunctSph q))
        = ContinuousMap.id (X × PunctSph q) := by
      ext p <;> rfl
    have hmain : ((ContinuousMap.id X).prodMap
          (ContinuousMap.const (PunctSph q) (punctSphPt q))).Homotopic
        ((ContinuousMap.id X).prodMap (ContinuousMap.id (PunctSph q))) :=
      (ContinuousMap.Homotopic.refl (ContinuousMap.id X)).prodMap (punctSphPt_spec q).symm
    simpa [h1, h2] using hmain
  right_inv := by
    have h1 : ContinuousMap.fst.comp (ContinuousMap.prodMk (ContinuousMap.id X)
          (ContinuousMap.const X (punctSphPt q))) = ContinuousMap.id X := by
      ext x; rfl
    rw [h1]

/-- The first projection `↥(B1set p q) = Sᵖ × (Sᵍ ∖ {N_q}) ⟶ Sᵖ` is a homotopy equivalence: it is
`fst` after the homeomorphism `B1Homeo p q`. -/
noncomputable def proj₁B1HomotopyEquiv (p q : ℕ) :
    ContinuousMap.HomotopyEquiv ↥(B1set p q) ↥(sphSet (p+1)) :=
  (B1Homeo p q).toHomotopyEquiv.trans (prodFstHomotopyEquiv ↥(sphSet (p+1)) q)

/-- The forward map of `proj₁B1HomotopyEquiv p q` is the continuous map underlying `proj₁B1 p q`. -/
lemma ofHom_proj₁B1HomotopyEquiv (p q : ℕ) :
    TopCat.ofHom (proj₁B1HomotopyEquiv p q).toFun = proj₁B1 p q := by
  apply TopCat.hom_ext
  ext z
  rfl

/-- The projection `proj₁B1 : B1set p q ⟶ Sᵖ` induces an injective map on homology in positive
degrees.  (`B1set p q = Sᵖ × (Sᵍ \ {N_q})` inside `Yset p q`; the second factor is contractible,
so this projection is a homotopy equivalence onto `Sᵖ`.) -/
lemma proj1B1_injective (p q n : ℕ) (hp : 1 ≤ p) (hn : 1 ≤ n) :
    Function.Injective (HomologicalComplex.homologyMap
      (chainMap ℤ (TopCat.of ↥(B1set p q)) (sphTop (p + 1)) (proj₁B1 p q)) n).hom := by
  let e := proj₁B1HomotopyEquiv p q
  have hf : TopCat.ofHom e.toFun = proj₁B1 p q := ofHom_proj₁B1HomotopyEquiv p q
  -- `proj₁B1` is (the forward map of) a homotopy equivalence, hence an isomorphism on homology
  haveI : IsIso (HomologicalComplex.homologyMap
      (chainMap ℤ (TopCat.of ↥(B1set p q)) (sphTop (p+1)) (TopCat.ofHom e.toFun)) n) :=
    homologyEquiv ℤ (TopCat.of ↥(B1set p q)) (sphTop (p+1))
      (TopCat.ofHom e.toFun) (TopCat.ofHom e.invFun) e.left_inv.some e.right_inv.some n
  rw [← hf]
  exact (ModuleCat.mono_iff_injective _).mp inferInstance

end

end Work.Cohomology.Compat
