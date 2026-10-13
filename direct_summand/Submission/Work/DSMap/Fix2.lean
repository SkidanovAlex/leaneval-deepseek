import Submission.Work.DSMap.Map

/-! # DSMap.Fix2 — lead contract repair (curric-46, 10-13)

* **G4aU** replaces `DSMap.area_G4a_localGlobal.{a,b,c,d,e}`. Its hypothesis
  `DSplit.{a,d,e} A' _` with `d, e` arbitrary is unusable: no derived-category instance exists at
  arbitrary universe levels, so for such levels the hypothesis is vacuous and gives nothing
  (DSG4a report, `Obstruction.lean`). This is the same defect as G1 (`Fix.area_G1_pullbackU`).
  `main_dsplit` uses `d = e = a + 1`, where `HasDerivedCategory.standard` provides the instances. -/

open CategoryTheory AlgebraicGeometry IsLocalRing Limits

namespace DSMap.Fix2

theorem area_G4a_localGlobalU.{a, b, c} (A : Type a) [CommRing A] [IsNoetherianRing A]
    (X : Scheme.{a}) (f : X ⟶ Spec (.of A)) [IsProper f] (hp : IsProjOver A f)
    (h : ∀ m : Ideal A, m.IsMaximal → ∃ (A' : Type a) (_ : CommRing A') (_ : IsLocalRing A')
      (ψ : A →+* A'), ψ.Flat ∧ (maximalIdeal A').comap ψ = m ∧
      DSplit.{a, a + 1, a + 1} A' (pullback f (Spec.map (CommRingCat.ofHom ψ)))
        (pullback.snd f (Spec.map (CommRingCat.ofHom ψ)))) :
    DSplit.{a, b, c} A X f := sorry

end DSMap.Fix2
