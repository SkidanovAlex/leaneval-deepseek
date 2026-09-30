import Mathlib
import Submission.Work.Pi6.BOCK.CoeffIso
import Submission.Work.Pi6.BOCK.coeffSESShortExact
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

/-!
# AREA BOCK — the maps of the Bockstein sequence and their naturality

The reduction `red` and the Bockstein connecting map `del` of

`Hₙ₊₁(X;ℤ) --·p--> Hₙ₊₁(X;ℤ) --red--> Hₙ₊₁(X;ℤ/p) --del--> Hₙ(X;ℤ) --·p--> Hₙ(X;ℤ)`

are the conjugates of the maps of the homology long exact sequence of the Bockstein short complex of
singular chains (`Work.Pi6.EMZ.bockSES`) by the identifications `H_n(C_*(X;ℤ)) ≅ H_n(X;ℤ)`
(`Work.Pi6.EMZ.expTensUnitHomologyIso`) and `H_n(C_*(X;ℤ) ⊗ ℤ/p) ≅ H_n(X;ℤ/p)`
(`Work.Pi6.BOCK.eCIso`).

This file defines them and proves that they are natural in the space.
-/

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory

namespace Work.Pi6.BOCK

noncomputable section

variable (p : ℕ)

/-- The Bockstein short complex of singular chains at `X`. -/
abbrev bSES (X : Type) [TopologicalSpace X] :
    ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
  Work.Pi6.EMZ.bockSES p X

/-- Short exactness of the Bockstein short complex of singular chains. -/
theorem bSES_shortExact (hp : p.Prime) (X : Type) [TopologicalSpace X] :
    (bSES p X).ShortExact :=
  Work.Pi6.EMZ.bockSES_shortExact p hp X (coeffSESShortExact p hp)

/-- The connecting map `H_{n+1}(C_*(X;ℤ) ⊗ ℤ/p) → H_n(C_*(X;ℤ))`. -/
def delta (hp : p.Prime) (X : Type) [TopologicalSpace X] (n : ℕ) :
    (Work.SSS.expTens (Work.Pi6.EMZ.chZ X) (Mp p)).homology (n + 1) ⟶
      (Work.SSS.expTens (Work.Pi6.EMZ.chZ X) zZ).homology n :=
  (bSES_shortExact p hp X).δ (n + 1) n (by rw [ComplexShape.down_Rel])

/-- The reduction `H_n(X;ℤ) → H_n(X;ℤ/p)`. -/
def redMor (hp : p.Prime) (X : Type) [TopologicalSpace X] (n : ℕ) :
    Work.Pi6.HR ℤ X n ⟶ (Fp p).obj (Work.Pi6.HR (ZMod p) X n) :=
  (Work.Pi6.EMZ.expTensUnitHomologyIso X n).inv ≫
    HomologicalComplex.homologyMap
      (Work.SSS.expTensHom (Work.Pi6.EMZ.chZ X) (Work.Pi6.EMZ.redP p)) n ≫
    (eCIso' p hp X n).hom

/-- The reduction as an additive homomorphism `H_n(X;ℤ) →+ H_n(X;ℤ/p)`. -/
def redHom (hp : p.Prime) (X : Type) [TopologicalSpace X] (n : ℕ) :
    Work.Pi6.HR ℤ X n →+ Work.Pi6.HR (ZMod p) X n :=
  (ModuleCat.Hom.hom (redMor p hp X n)).toAddMonoidHom

/-- The Bockstein connecting map `H_{n+1}(X;ℤ/p) → H_n(X;ℤ)`. -/
def delMor (hp : p.Prime) (X : Type) [TopologicalSpace X] (n : ℕ) :
    (Fp p).obj (Work.Pi6.HR (ZMod p) X (n + 1)) ⟶ Work.Pi6.HR ℤ X n :=
  (eCIso' p hp X (n + 1)).inv ≫ delta p hp X n ≫
    (Work.Pi6.EMZ.expTensUnitHomologyIso X n).hom

/-- The Bockstein connecting map as an additive homomorphism
`H_{n+1}(X;ℤ/p) →+ H_n(X;ℤ)`. -/
def delHom (hp : p.Prime) (X : Type) [TopologicalSpace X] (n : ℕ) :
    Work.Pi6.HR (ZMod p) X (n + 1) →+ Work.Pi6.HR ℤ X n :=
  (ModuleCat.Hom.hom (delMor p hp X n)).toAddMonoidHom

/-! ## Naturality of the two identifications -/

/-- Naturality of the identification `H_n(C_*(X;ℤ) ⊗ ℤ) ≅ H_n(X;ℤ)`. -/
theorem expTensUnitHomologyIso_natural {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (n : ℕ) :
    HomologicalComplex.homologyMap
        (expTensMapHom (Work.Pi6.EMZ.chZ X) (Work.Pi6.EMZ.chZ Y) (chMapZ f)
          (𝟙_ (ModuleCat ℤ))) n ≫
      (Work.Pi6.EMZ.expTensUnitHomologyIso Y n).hom =
    (Work.Pi6.EMZ.expTensUnitHomologyIso X n).hom ≫ Work.Pi6.hmap ℤ f n := by
  have h := expTensUnitIso_natural (Work.Pi6.EMZ.chZ X) (Work.Pi6.EMZ.chZ Y) (chMapZ f)
  have h2 := congrArg (fun t => HomologicalComplex.homologyMap t n) h
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at h2
  simp only [chMapZ, Work.Pi6.hmap]
  exact h2

/-- The inverse form of the preceding naturality. -/
theorem expTensUnitHomologyIso_natural_inv {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (n : ℕ) :
    Work.Pi6.hmap ℤ f n ≫ (Work.Pi6.EMZ.expTensUnitHomologyIso Y n).inv =
      (Work.Pi6.EMZ.expTensUnitHomologyIso X n).inv ≫
        HomologicalComplex.homologyMap
          (expTensMapHom (Work.Pi6.EMZ.chZ X) (Work.Pi6.EMZ.chZ Y) (chMapZ f)
            (𝟙_ (ModuleCat ℤ))) n :=
  inv_naturality_of_square _ _ _ _ (expTensUnitHomologyIso_natural f n)

end

end Work.Pi6.BOCK
