import Submission.Work.DSMX0U.Engine
import Submission.Work.DSMX0U.isZero_cechZ_X_of_neg
import Submission.Work.DSMX0U.coaugZ_isCycle
import Submission.Work.DSMap.Mix2

/-!
# DSMX0U — the area theorem: `MX0U` from the coherence input

This file proves `DSMap.Mix2.IsFinFreeModelU` for every finite affine cover of a projective
scheme over a Noetherian ring, *given* the coherence input (`F1` + `COH`):

    `∃ N, ∀ i, H^i(Čech) is a finitely generated A-module and vanishes for i > N`.

The coherence input is the (unproved-in-this-workspace) content of the areas `F1` and `COH` of
the proof map; it is supplied unconditionally by `Work.DSMX0U.cechZ_homology_finite`.

Everything else — the finite free model of a complex with finitely generated bounded cohomology
(`Work.DSMX0U.exists_finFreeModel_of_fgCoh`), the comparison with the Čech coaugmentation, and the
transport of the boundedness — is proved here, sorry-free and axiom-clean.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.DSMX0U

open CategoryTheory AlgebraicGeometry Limits

set_option linter.unusedVariables false

universe a

/-- **`MX0U` from the coherence input.** -/
theorem area_MX0U_of_coherence (A : Type a) [CommRing A] [IsNoetherianRing A]
    (X : Scheme.{a}) (f : X ⟶ Spec (.of A)) [IsProper f] (hp : DSMap.IsProjOver A f)
    {ι : Type a} [Finite ι] (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hcov : ⨆ i, U i = ⊤)
    (hcoh : ∃ N : ℤ, ∀ i : ℤ, Module.Finite A ((DSMap.cechZ A X f U).homology i) ∧
      (N < i → CategoryTheory.Limits.IsZero ((DSMap.cechZ A X f U).homology i))) :
    ∃ (P : CochainComplex (ModuleCat.{a} A) ℤ) (ε : ModuleCat.of A A ⟶ P.X 0),
      DSMap.Mix2.IsFinFreeModelU A X f U P ε := by
  obtain ⟨N, hN⟩ := hcoh
  obtain ⟨P, ε, φ, h1, h2, h3, h4⟩ :=
    exists_finFreeModel_of_fgCoh (C := DSMap.cechZ A X f U) (N := N)
      (fun i hi => (hN i).2 hi) (fun i => (hN i).1)
      (DSMap.coaug0 A X f U ≫
        ((DSMap.cech A X f U).extendXIso ComplexShape.embeddingUpNat (i := 0) rfl).inv)
      (coaugZ_isCycle (A := A) f U)
  refine ⟨P, ε, h1, h2, φ, h3, ?_⟩
  conv_lhs => rw [← Category.assoc]
  rw [h4]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end Work.DSMX0U
