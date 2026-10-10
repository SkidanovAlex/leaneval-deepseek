import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
import Submission.Work.CohomologicalShrinking.Bridge.Psi
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped TensorProduct
open CategoryTheory

set_option backward.isDefEq.respectTransparency false

namespace Work.CohomologicalShrinking.bridge

open Work.CohomologicalShrinking

/-- The intertwining condition exhibiting `E(m,τ) ⊗ T` as a representation of `Γ ⧸ N ≃* G`
through the `G`-action, i.e. the identification of the `G ⧸ N`-representation with `flowRepG`. -/
theorem flowHS_he (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Fintype G] (m i j : ℕ)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T] :
    ∀ q : flowGroup p G m i j ⧸ flowNormal p G m i j,
      (LinearEquiv.refl (ZMod p) (E p G m i j ⊗[ZMod p] T)) ∘ₗ
        ((Rep.ofQuotient (flowRep p G m i j T) (flowNormal p G m i j)).ρ q) =
      (flowRepG p G m i j T).ρ (flowQuotEquiv p G m i j q) ∘ₗ
        (LinearEquiv.refl (ZMod p) (E p G m i j ⊗[ZMod p] T)) := by
  intro q
  rw [LinearEquiv.refl_toLinearMap, LinearMap.id_comp, LinearMap.comp_id]
  induction q using QuotientGroup.induction_on with
  | H γ =>
    rw [hochschildSerre.flowQuotEquiv_mk]
    rfl

/-- The isomorphism `H₁(Γ ⧸ N, E(m,τ) ⊗ T) ≅ H₁(G, E(m,τ) ⊗ T)`. -/
noncomputable abbrev flowH1QuotIso (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Fintype G]
    (m i j : ℕ) (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T] :
    groupHomology.H1 (Rep.ofQuotient (flowRep p G m i j T) (flowNormal p G m i j)) ≅
      groupHomology.H1 (flowRepG p G m i j T) :=
  groupHomology.mapIso (A := Rep.ofQuotient (flowRep p G m i j T) (flowNormal p G m i j))
    (B := flowRepG p G m i j T) (flowQuotEquiv p G m i j)
    (LinearEquiv.refl (ZMod p) (E p G m i j ⊗[ZMod p] T)) (flowHS_he p G m i j T) 1

/-- **The canonical coinflation is the corestriction–coinflation sequence's `g`, transported
along `Γ ⧸ N ≃* G`.**  Concretely,
`Psi m = g ≫ e` where `g` is Mathlib's coinflation map
`H₁(Γ, E⊗T) → H₁(Γ⧸N, E⊗T)` and `e` is the isomorphism `H₁(Γ⧸N, E⊗T) ≅ H₁(G, E⊗T)`. -/
theorem Psi_eq_g_iso (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Fintype G] (m i j : ℕ)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T] :
    Work.Bridge.Psi (p := p) (G := G) (i := i) (j := j) (T := T) m
      = ((groupHomology.H1CoresCoinfOfTrivial (flowRep p G m i j T) (flowNormal p G m i j)).g
          ≫ (flowH1QuotIso p G m i j T).hom).hom.toAddMonoidHom := by
  change (groupHomology.map (flowQuot p G m i j) (𝟙 (flowRep p G m i j T)) 1).hom.toAddMonoidHom
    = ((groupHomology.H1CoresCoinfOfTrivial (flowRep p G m i j T)
        (flowNormal p G m i j)).g ≫ (groupHomology.mapIso
          (A := Rep.ofQuotient (flowRep p G m i j T) (flowNormal p G m i j))
          (B := flowRepG p G m i j T) (flowQuotEquiv p G m i j)
          (LinearEquiv.refl (ZMod p) (E p G m i j ⊗[ZMod p] T)) (flowHS_he p G m i j T) 1).hom).hom.toAddMonoidHom
  have hid : groupHomology.map (flowQuot p G m i j) (𝟙 (flowRep p G m i j T)) 1
      = (groupHomology.H1CoresCoinfOfTrivial (flowRep p G m i j T) (flowNormal p G m i j)).g
        ≫ (groupHomology.mapIso
            (A := Rep.ofQuotient (flowRep p G m i j T) (flowNormal p G m i j))
            (B := flowRepG p G m i j T) (flowQuotEquiv p G m i j)
            (LinearEquiv.refl (ZMod p) (E p G m i j ⊗[ZMod p] T)) (flowHS_he p G m i j T) 1).hom := by
    rw [groupHomology.H1CoresCoinfOfTrivial_g]
    let ψ : Rep.ofQuotient (flowRep p G m i j T) (flowNormal p G m i j) ⟶
        Rep.res ((flowQuotEquiv p G m i j).toMonoidHom) (flowRepG p G m i j T) :=
      Rep.ofHom { toLinearMap := (LinearEquiv.refl (ZMod p) (E p G m i j ⊗[ZMod p] T)).toLinearMap, isIntertwining' := flowHS_he p G m i j T }
    show groupHomology.map (flowQuot p G m i j) (𝟙 (flowRep p G m i j T)) 1
        = groupHomology.map (QuotientGroup.mk' (flowNormal p G m i j)) (𝟙 (flowRep p G m i j T)) 1
          ≫ groupHomology.map ((flowQuotEquiv p G m i j).toMonoidHom) ψ 1
    refine Eq.trans ?_ (groupHomology.map_comp
        (A := flowRep p G m i j T)
        (B := Rep.ofQuotient (flowRep p G m i j T) (flowNormal p G m i j))
        (C := flowRepG p G m i j T)
        (f := QuotientGroup.mk' (flowNormal p G m i j))
        (g := (flowQuotEquiv p G m i j).toMonoidHom)
        (φ := (𝟙 (flowRep p G m i j T)))
        (ψ := ψ) 1)
    exact groupHomology.map_congr (A := flowRep p G m i j T) (B := flowRepG p G m i j T) (n := 1)
        (hfg := (MonoidHom.ext (fun γ => hochschildSerre.flowQuotEquiv_mk p G m i j γ)).symm)
        (by ext; rfl)
  rw [hid]

/-- **The kernel of the canonical coinflation.**  It is the kernel of Mathlib's coinflation map
`H₁(Γ, E⊗T) → H₁(Γ⧸N, E⊗T)` of the corestriction–coinflation sequence. -/
theorem Psi_ker_eq_g_ker (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Fintype G] (m i j : ℕ)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T] :
    (Work.Bridge.Psi (p := p) (G := G) (i := i) (j := j) (T := T) m).ker
      = ((groupHomology.H1CoresCoinfOfTrivial (flowRep p G m i j T)
          (flowNormal p G m i j)).g.hom).ker.toAddSubgroup := by
  rw [Psi_eq_g_iso p G m i j T]
  rw [ModuleCat.hom_comp]
  rw [show ((groupHomology.mapIso
        (A := Rep.ofQuotient (flowRep p G m i j T) (flowNormal p G m i j))
        (B := flowRepG p G m i j T) (flowQuotEquiv p G m i j)
        (LinearEquiv.refl (ZMod p) (E p G m i j ⊗[ZMod p] T))
        (flowHS_he p G m i j T) 1).hom.hom ∘ₗ
      (groupHomology.H1CoresCoinfOfTrivial (flowRep p G m i j T)
        (flowNormal p G m i j)).g.hom).toAddMonoidHom
    = ((groupHomology.mapIso
        (A := Rep.ofQuotient (flowRep p G m i j T) (flowNormal p G m i j))
        (B := flowRepG p G m i j T) (flowQuotEquiv p G m i j)
        (LinearEquiv.refl (ZMod p) (E p G m i j ⊗[ZMod p] T))
        (flowHS_he p G m i j T) 1).hom.hom.toAddMonoidHom).comp
      ((groupHomology.H1CoresCoinfOfTrivial (flowRep p G m i j T)
        (flowNormal p G m i j)).g.hom.toAddMonoidHom) from rfl]
  rw [AddMonoidHom.ker_comp_of_injective _ _ (by
    show Function.Injective ⇑((groupHomology.mapIso
        (A := Rep.ofQuotient (flowRep p G m i j T) (flowNormal p G m i j))
        (B := flowRepG p G m i j T) (flowQuotEquiv p G m i j)
        (LinearEquiv.refl (ZMod p) (E p G m i j ⊗[ZMod p] T))
        (flowHS_he p G m i j T) 1).toLinearEquiv)
    exact (groupHomology.mapIso
        (A := Rep.ofQuotient (flowRep p G m i j T) (flowNormal p G m i j))
        (B := flowRepG p G m i j T) (flowQuotEquiv p G m i j)
        (LinearEquiv.refl (ZMod p) (E p G m i j ⊗[ZMod p] T))
        (flowHS_he p G m i j T) 1).toLinearEquiv.injective)]
  exact (LinearMap.ker_toAddSubgroup _).symm

/-- **The kernel of the canonical coinflation is the range of the corestriction**
(the exactness of the corestriction–coinflation sequence in degree `1`). -/
theorem Psi_ker (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Fintype G] (i j : ℕ)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T] (m : ℕ) :
    (Work.Bridge.Psi (p := p) (G := G) (i := i) (j := j) (T := T) m).ker
      = (Work.Bridge.corest (p := p) (G := G) (i := i) (j := j) (T := T) m).range := by
  rw [Psi_ker_eq_g_ker p G m i j T, Work.Bridge.corest_eq_flowHSα]
  have hα : flowHSα p G i j T m
      = ((groupHomology.H1CoresCoinfOfTrivial (flowRep p G m i j T)
          (flowNormal p G m i j)).f.hom).toAddMonoidHom :=
    AddMonoidHom.ext (flowHS_spec p G i j T m).1
  rw [hα, ← LinearMap.range_toAddSubgroup, ShortComplex.Exact.moduleCat_range_eq_ker
    (groupHomology.H1CoresCoinfOfTrivial_exact (flowRep p G m i j T) (flowNormal p G m i j))]

end Work.CohomologicalShrinking.bridge
