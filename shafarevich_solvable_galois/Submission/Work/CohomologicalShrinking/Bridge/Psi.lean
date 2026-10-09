import Submission.Work.CohomologicalShrinking.Bridge.Core
import Submission.Work.CohomologicalShrinking.SemidirectData
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped BigOperators
open CategoryTheory

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Work.Bridge

open Work.CohomologicalShrinking

variable {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Fintype G] {i j : ℕ}
variable {T : Type} [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
  [SMulCommClass G (ZMod p) T]

/-- The representation morphism `E(m,τ)⊗T ⟶ E(n,τ)⊗T` induced by an operator map. -/
noncomputable def flowRepGMap {m n : ℕ} (Φ : OperatorMap G m n) :
    flowRepG p G m i j T ⟶ flowRepG p G n i j T :=
  repMor (k := ZMod p) (G := G)
    ((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T)
    (fun g z => rTensor_equiv p (G := G) (f := gradedMapLin p Φ.toHom Φ.surjective i j)
      (fun g x => gradedMapLin_smul p Φ.toHom Φ.surjective Φ.equivariant i j g x) g z)

/-- The induced map on `H₁(G, E(-,τ)⊗T)`. -/
noncomputable def indH1 {m n : ℕ} (Φ : OperatorMap G m n) :
    (↑(groupHomology.H1 (flowRepG p G m i j T)) : Type) →+
      (↑(groupHomology.H1 (flowRepG p G n i j T)) : Type) :=
  (groupHomology.map (MonoidHom.id G) (flowRepGMap (T:=T) Φ) 1).hom.toAddMonoidHom

/-- The canonical coinflation `H₁(F(m)/ν ⋊ G, E(m,τ)⊗T) →+ H₁(G, E(m,τ)⊗T)`. -/
noncomputable def Psi (m : ℕ) :
    (↑(groupHomology.H1 (flowRep p G m i j T)) : Type) →+
      (↑(groupHomology.H1 (flowRepG p G m i j T)) : Type) :=
  (groupHomology.map (flowQuot p G m i j) (𝟙 (flowRep p G m i j T)) 1).hom.toAddMonoidHom

/-- The corestriction `H₁(F(m)/ν, E(m,τ)⊗T) →+ H₁(F(m)/ν ⋊ G, E(m,τ)⊗T)`. -/
noncomputable def corest (m : ℕ) :
    (↑(groupHomology.H1 (Rep.res (flowNormal p G m i j).subtype (flowRep p G m i j T))) : Type) →+
      (↑(groupHomology.H1 (flowRep p G m i j T)) : Type) :=
  ((groupHomology.H1CoresCoinfOfTrivial (flowRep p G m i j T) (flowNormal p G m i j)).f).hom.toAddMonoidHom

theorem corest_eq_flowHSα (m : ℕ) : corest (T:=T) m = flowHSα p G i j T m :=
  AddMonoidHom.ext (fun x => ((flowHS_spec p G i j T m).1 x).symm)

/-- The rep-morphism equality underlying the naturality of the coinflation. -/
theorem flowRepMap_eq {m n : ℕ} (Φ : OperatorMap G m n) :
    flowRepMap (p:=p) G i j Φ T
      = (CategoryTheory.Functor.map (Rep.resFunctor (flowQuot p G m i j))
          (flowRepGMap (i:=i) (j:=j) (T:=T) Φ)) := by
  apply Rep.hom_ext
  ext x
  rfl

theorem Psi_natural_mor {m n : ℕ} (Φ : OperatorMap G m n) :
    groupHomology.map (flowGroupMap p G i j Φ) (flowRepMap (p:=p) G i j Φ T) 1
      ≫ groupHomology.map (flowQuot p G n i j) (𝟙 (flowRep p G n i j T)) 1
    = groupHomology.map (flowQuot p G m i j) (𝟙 (flowRep p G m i j T)) 1
      ≫ groupHomology.map (MonoidHom.id G) (flowRepGMap (i:=i) (j:=j) (T:=T) Φ) 1 := by
  rw [← groupHomology.map_comp (f := flowGroupMap p G i j Φ) (g := flowQuot p G n i j)
        (A := flowRep p G m i j T) (B := flowRep p G n i j T)
        (flowRepMap (p:=p) G i j Φ T) (𝟙 (flowRep p G n i j T)) 1,
      ← groupHomology.map_comp (f := flowQuot p G m i j) (g := MonoidHom.id G)
        (A := flowRep p G m i j T) (B := flowRepG p G m i j T) (C := flowRepG p G n i j T)
        (𝟙 (flowRep p G m i j T)) (flowRepGMap (i:=i) (j:=j) (T:=T) Φ) 1]
  refine groupHomology.map_congr rfl ?_ 1
  ext x
  rfl

/-- **Naturality of the canonical coinflation.** -/
theorem Psi_natural {m n : ℕ} (Φ : OperatorMap G m n) :
    (Psi (T:=T) n).comp (flowZMap (p := p) G i j Φ T)
      = (indH1 (T:=T) Φ).comp (Psi (T:=T) m) := by
  apply AddMonoidHom.ext
  intro y
  exact congrArg (fun (f : groupHomology (flowRep p G m i j T) 1 ⟶
      groupHomology (flowRepG p G n i j T) 1) => (ConcreteCategory.hom f) y)
    (Psi_natural_mor (T:=T) Φ)

end Work.Bridge
