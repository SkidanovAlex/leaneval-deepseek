/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The concrete model of `H₁(F(m)/F(m)^{(ν)} ⋊ G, E(m,τ) ⊗ T)`

This file instantiates the abstract Hochschild–Serre data
`Work.CohomologicalShrinking.SemidirectShrinkingData` of Schmidt–Wingberg's Proposition 7 (i) at
the paper's *own* group and coefficients:

* `Z m := groupHomology.H1 (flowRep p G m i j T)`, the group homology of the semidirect product
  `Γ_m = F(m)/F(m)^{(i,j)} ⋊ G` (`Semidirect.lean`) with coefficients in `E(m,τ) ⊗ T`;
* `zMap Φ := flowZMap Φ T`, the map induced by an operator map (functorial by
  `flow.flowZMap_comp`);
* `β m := γ m ∘ β₀ m`, where `β₀ m` is the second map of the homological Hochschild–Serre
  sequence `H₁(Γ_m, E⊗T) → H₁(Γ_m/N_m, E⊗T) = H₁(G, E⊗T)` (Mathlib's coinflation, transported
  along `Γ_m ⧸ N_m ≃* G` by `hochschildSerre.flowQuotH1Equiv`), and `γ` is the paper's recalled
  identification `H₁ = Ĥ^{-2}`, `Ĥ^{-2}(G, E⊗T) = Ĥ^{-1}(G, E⊗T ⊗ I_G) = Work.Tate.Hm1 …`;
* `α m`, a map `F(m)/F(m)² ⊗ E(m,τ) ⊗ T →+ H₁(Γ_m, E⊗T)` whose image is the image of the
  corestriction `H₁(F(m)/ν, E⊗T) → H₁(Γ_m, E⊗T)` — the paper's `α`.

**Proved outright here:** the exactness `range α = ker β` and the surjectivity of `β` (both
transported from Mathlib's `groupHomology.H1CoresCoinfOfTrivial_exact` and `…_g_epi`, see
`hochschildSerre.flowHSExact`), and the functoriality `zMap (Ψ ∘ Φ) = zMap Ψ ∘ zMap Φ`
(`flow.flowZMap_comp`).

**Taken as input** (explicit hypotheses of `semidirectShrinkingData_of`, never `sorry`s): the
identification of the image of the paper's `α` with the image of the corestriction, the
naturality in the rank of `α` and of `β`, and the identification `H₁(G, ·) = Ĥ^{-2}(G, ·)` (the
paper's "recall that `H^{-2} = H_1`", written as an isomorphism `γ` with its injectivity and
surjectivity).
-/

import Mathlib
import Submission.Work.CohomologicalShrinking.FlowGroupMap
import Submission.Work.CohomologicalShrinking.OperatorMap
import Submission.Work.CohomologicalShrinking.flow.flowNormalSquareEquiv
import Submission.Work.CohomologicalShrinking.Prop7i
import Submission.Work.CohomologicalShrinking.flow.flowZMap_comp
import Submission.Work.CohomologicalShrinking.flow.flowGroupMap_comp
import Submission.Work.CohomologicalShrinking.hochschildSerre.flowQuotH1Equiv
import Submission.Work.CohomologicalShrinking.hochschildSerre.flowHSExact
import Submission.Work.CohomologicalShrinking.universalCoefficient.h1AddEquivPQuotientSub
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

attribute [local instance] Classical.decEq

namespace Work.CohomologicalShrinking

open scoped TensorProduct
open CategoryTheory

universe u

variable {p : ℕ}

/-! ## The two maps of the Hochschild–Serre sequence, at the paper's own group -/

/-- The corestriction `H₁(F(m)/F(m)^{(ν)}, E⊗T) →+ H₁(F(m)/F(m)^{(ν)} ⋊ G, E⊗T)`, the first map
of the homological Hochschild–Serre sequence.  It is `α₀` of `semidirectShrinkingData_of`. -/
noncomputable def flowHSα (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Fintype G]
    (i j : ℕ) (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T] (m : ℕ) :
    (↑(groupHomology.H1 (Rep.res (flowNormal p G m i j).subtype (flowRep p G m i j T))) : Type) →+
      (↑(groupHomology.H1 (flowRep p G m i j T)) : Type) :=
  Classical.choose (hochschildSerre.flowHSExact p G m i j T)

/-- The coinflation `H₁(Γ, E⊗T) →+ H₁(G, E⊗T)`, the second map of the homological
Hochschild–Serre sequence (transported along `Γ ⧸ N ≃* G`). -/
noncomputable def flowHSβ (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Fintype G]
    (i j : ℕ) (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T] (m : ℕ) :
    (↑(groupHomology.H1 (flowRep p G m i j T)) : Type) →+
      (↑(groupHomology.H1 (flowRepG p G m i j T)) : Type) :=
  Classical.choose (Classical.choose_spec (hochschildSerre.flowHSExact p G m i j T))

theorem flowHS_spec (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Fintype G]
    (i j : ℕ) (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T] (m : ℕ) :
    (∀ x, flowHSα p G i j T m x = (groupHomology.H1CoresCoinfOfTrivial (flowRep p G m i j T)
        (flowNormal p G m i j)).f.hom x) ∧
      Function.Surjective (flowHSβ p G i j T m) ∧
      (flowHSα p G i j T m).range = (flowHSβ p G i j T m).ker :=
  Classical.choose_spec (Classical.choose_spec (hochschildSerre.flowHSExact p G m i j T))

/-! ## Assembling the Hochschild–Serre data -/

/-- **The concrete Hochschild–Serre data of Proposition 7 (i)** for the paper's own group and
coefficients.  The exactness, the surjectivity of `β` and the functoriality of `zMap` are proved;
the remaining inputs are the identification of the image of the paper's `α` with the image of the
corestriction, the naturality in the rank of `α` and `β`, and the paper's recalled
`H^{-2} = H₁`. -/
noncomputable def semidirectShrinkingData_of (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Fintype G]
    {i j : ℕ} (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T]
    (α : ∀ m : ℕ, (squareQuotient p G m ⊗[ZMod p] (E p G m i j ⊗[ZMod p] T)) →+
      (↑(groupHomology.H1 (flowRep p G m i j T)) : Type))
    (hαrange : ∀ m : ℕ, (α m).range = (flowHSα p G i j T m).range)
    (hαnat : ∀ ⦃m n : ℕ⦄ (Φ : OperatorMap G m n)
      (x : squareQuotient p G m ⊗[ZMod p] (E p G m i j ⊗[ZMod p] T)),
      α n (Φ.h1Map p G T x) = flowZMap (p := p) G i j Φ T (α m x))
    (γ : ∀ m : ℕ, (↑(groupHomology.H1 (flowRepG p G m i j T)) : Type) →+
      Work.Tate.Hm1 G (E p G m i j ⊗[ZMod p] (T ⊗[ZMod p] augIdeal p G)))
    (hγinj : ∀ m, Function.Injective (γ m))
    (hγsurj : ∀ m, Function.Surjective (γ m))
    (hβnat : ∀ ⦃m n : ℕ⦄ (Φ : OperatorMap G m n)
      (y : (↑(groupHomology.H1 (flowRep p G m i j T)) : Type)),
      (Φ.hm1Map p G (T ⊗[ZMod p] augIdeal p G))
          (γ m (flowHSβ p G i j T m y))
        = γ n (flowHSβ p G i j T n (flowZMap (p := p) G i j Φ T y))) :
    SemidirectShrinkingData p G i j T (fun m => groupHomology.H1 (flowRep p G m i j T)) := by
  classical
  refine
    { α := fun m => α m
      β := fun m => (γ m).comp (flowHSβ p G i j T m)
      zMap := fun m n Φ => flowZMap (p := p) G i j Φ T
      exact_αβ := ?_
      β_surjective := ?_
      zMap_comp := ?_
      α_natural := ?_
      β_natural := ?_ }
  · intro m
    have hker : ((γ m).comp (flowHSβ p G i j T m)).ker = (flowHSβ p G i j T m).ker :=
      AddMonoidHom.ker_comp_of_injective _ _ (hγinj m)
    rw [hker, ← (flowHS_spec p G i j T m).2.2, ← hαrange m]
  · intro m
    rw [AddMonoidHom.range_eq_top]
    intro y
    obtain ⟨y', rfl⟩ := hγsurj m y
    obtain ⟨z, hz⟩ := (flowHS_spec p G i j T m).2.1 y'
    exact ⟨z, by change (γ m) (flowHSβ p G i j T m z) = γ m y'; rw [hz]⟩
  · intro m n l Φ Ψ
    exact flow.flowZMap_comp p G i j Φ Ψ T
  · intro m n Φ
    ext x
    exact (hαnat Φ x).symm
  · intro m n Φ
    ext y
    exact hβnat Φ y

/-- The first part of `flowAlpha`: the identification
`F(m)/F(m)² ⊗ E⊗T ≅ (F(m)/ν)/(F(m)/ν)² ⊗ E⊗T`. -/
noncomputable def flowAlphaAux (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Fintype G] (i j : ℕ)
    (hi : 2 ≤ i) (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T] (m : ℕ) :
    (squareQuotient p G m ⊗[ZMod p] (E p G m i j ⊗[ZMod p] T)) →+
      ((↑(groupHomology.H1 (Rep.res (flowNormal p G m i j).subtype
        (flowRep p G m i j T))) : Type)) :=
  ((Classical.choice (universalCoefficient.h1AddEquivPQuotientSub p (flowNormal p G m i j)
      (flowRep p G m i j T))).symm.toAddMonoidHom).comp
    (((TensorProduct.congr (Classical.choice (flow.flowNormalSquareEquiv p G i j m hi))
      (LinearEquiv.refl (ZMod p) (E p G m i j ⊗[ZMod p] T))).toLinearMap).toAddMonoidHom)


/-! ## The paper's `α`, built from the universal coefficient formula -/

/-- **The map `α` of Proposition 7 (i)**, built exactly as in the paper: the universal
coefficient formula `H₁(F(m)/ν, E⊗T) ≅ F(m)/F(m)² ⊗ E⊗T` (`h1AddEquivPQuotientSub`) together
with the identification `(F(m)/ν)/(F(m)/ν)² ≅ F(m)/F(m)²` (`flowNormalSquareEquiv`, which needs
`ν = (i,j) ≥ (2,1)`), followed by the corestriction `H₁(F(m)/ν, E⊗T) → H₁(Γ, E⊗T)`. -/
noncomputable def flowAlpha (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Fintype G] (i j : ℕ)
    (hi : 2 ≤ i) (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T] (m : ℕ) :
    (squareQuotient p G m ⊗[ZMod p] (E p G m i j ⊗[ZMod p] T)) →+
      (↑(groupHomology.H1 (flowRep p G m i j T)) : Type) :=
  (flowHSα p G i j T m).comp (flowAlphaAux p G i j hi T m)

/-- The first part of `flowAlpha` is surjective: it is the composite of the identification
`(F(m)/ν)/(F(m)/ν)² ≅ F(m)/F(m)²` with the inverse of the universal coefficient formula. -/
theorem flowAlphaAux_surjective (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Fintype G]
    (i j : ℕ) (hi : 2 ≤ i) (T : Type) [AddCommGroup T] [Module (ZMod p) T]
    [DistribMulAction G T] [SMulCommClass G (ZMod p) T] (m : ℕ) :
    Function.Surjective (flowAlphaAux p G i j hi T m) := by
  intro y
  refine ⟨(TensorProduct.congr (Classical.choice (flow.flowNormalSquareEquiv p G i j m hi))
      (LinearEquiv.refl (ZMod p) (E p G m i j ⊗[ZMod p] T))).symm
      ((Classical.choice (universalCoefficient.h1AddEquivPQuotientSub p (flowNormal p G m i j)
        (flowRep p G m i j T))) y), ?_⟩
  change (Classical.choice (universalCoefficient.h1AddEquivPQuotientSub p (flowNormal p G m i j)
      (flowRep p G m i j T))).symm
      ((TensorProduct.congr (Classical.choice (flow.flowNormalSquareEquiv p G i j m hi))
        (LinearEquiv.refl (ZMod p) (E p G m i j ⊗[ZMod p] T)))
        ((TensorProduct.congr (Classical.choice (flow.flowNormalSquareEquiv p G i j m hi))
          (LinearEquiv.refl (ZMod p) (E p G m i j ⊗[ZMod p] T))).symm
          ((Classical.choice (universalCoefficient.h1AddEquivPQuotientSub p (flowNormal p G m i j)
            (flowRep p G m i j T))) y))) = y
  rw [LinearEquiv.apply_symm_apply, AddEquiv.symm_apply_apply]

/-- The image of the paper's `α` is the image of the corestriction (this is the content of the
universal coefficient formula together with `(F(m)/ν)/(F(m)/ν)² ≅ F(m)/F(m)²`). -/
theorem flowAlpha_range (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Fintype G] (i j : ℕ)
    (hi : 2 ≤ i) (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T] (m : ℕ) :
    (flowAlpha p G i j hi T m).range = (flowHSα p G i j T m).range := by
  rw [flowAlpha]
  refine le_antisymm ?_ ?_
  · rintro y ⟨x, rfl⟩
    exact ⟨flowAlphaAux p G i j hi T m x, rfl⟩
  · rintro y ⟨z, rfl⟩
    obtain ⟨x, hx⟩ := flowAlphaAux_surjective p G i j hi T m z
    exact ⟨x, by rw [AddMonoidHom.comp_apply, hx]⟩

end Work.CohomologicalShrinking
