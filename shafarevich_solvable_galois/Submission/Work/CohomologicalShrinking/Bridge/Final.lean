import Submission.Work.CohomologicalShrinking.Bridge.Psi
import Submission.Work.CohomologicalShrinking.coindUpAddEquivTensor
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped BigOperators
open scoped TensorProduct
open CategoryTheory

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

namespace Work.Bridge

open Work.CohomologicalShrinking

variable {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Fintype G] {i j : ℕ}
variable {T : Type} [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
  [SMulCommClass G (ZMod p) T]

/-- The chosen natural equivalence `A^♯ ≃+ A ⊗ I_G`. -/
noncomputable def cEq (A : Type) [AddCommGroup A] [Module (ZMod p) A] [DistribMulAction G A]
    [SMulCommClass G (ZMod p) A] : Work.Tate.coindUp G A ≃+ (A ⊗[ZMod p] augIdeal p G) :=
  Classical.choose (coindUpAddEquivTensor p G) A

theorem cEq_equiv : ∀ (A : Type) [AddCommGroup A] [Module (ZMod p) A] [DistribMulAction G A]
    [SMulCommClass G (ZMod p) A] (γ : G) (x : Work.Tate.coindUp G A),
    cEq (p:=p) (G:=G) A (γ • x) = γ • cEq (p:=p) (G:=G) A x :=
  (Classical.choose_spec (coindUpAddEquivTensor p G)).1

theorem cEq_natural : ∀ (A : Type) [AddCommGroup A] [Module (ZMod p) A] [DistribMulAction G A]
    [SMulCommClass G (ZMod p) A] (B : Type) [AddCommGroup B] [Module (ZMod p) B]
    [DistribMulAction G B] [SMulCommClass G (ZMod p) B]
    (φ : A →ₗ[ZMod p] B) (hφ : ∀ (γ : G) (a : A), φ (γ • a) = γ • φ a),
    (cEq (p:=p) (G:=G) B).toAddMonoidHom.comp (Work.Tate.coindUpMap (φ.toAddMonoidHom) hφ)
      = ((LinearMap.rTensor (augIdeal p G) φ).toAddMonoidHom).comp
          (cEq (p:=p) (G:=G) A).toAddMonoidHom :=
  (Classical.choose_spec (coindUpAddEquivTensor p G)).2

/-- Transport `Ĥ⁻¹` along the `I_G`-twist identification. -/
noncomputable def tr1 (A : Type) [AddCommGroup A] [Module (ZMod p) A] [DistribMulAction G A]
    [SMulCommClass G (ZMod p) A] : Work.Tate.Hm1 G (Work.Tate.coindUp G A) ≃+
      Work.Tate.Hm1 G (A ⊗[ZMod p] augIdeal p G) :=
  Work.Tate.Hm1Equiv (cEq (p:=p) (G:=G) A).toAddMonoidHom (cEq_equiv (p:=p) (G:=G) A)
    (cEq (p:=p) (G:=G) A).bijective

/-- Transport `Ĥ⁻¹` along associativity of the tensor product. -/
noncomputable def assocEq (A B C : Type) [AddCommGroup A] [Module (ZMod p) A]
    [AddCommGroup B] [Module (ZMod p) B] [AddCommGroup C] [Module (ZMod p) C]
    [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]
    [SMulCommClass G (ZMod p) A] [SMulCommClass G (ZMod p) B] [SMulCommClass G (ZMod p) C] :
    (A ⊗[ZMod p] B) ⊗[ZMod p] C ≃ₗ[ZMod p] A ⊗[ZMod p] (B ⊗[ZMod p] C) :=
  TensorProduct.assoc (ZMod p) A B C


/-- **The final assembly.**  Given a natural isomorphism `GAMMA` from `H₁(G, E(m,τ)⊗T)` to
`Ĥ⁻¹(G, E(m,τ)⊗(T⊗I_G))` and an automorphism family `eps m` with `eps m ∘ Ψ_m = β_m`
(existing because the coinflation `Ψ_m` and `flowHSβ m` are surjective with the same kernel),
the family `γ_m = GAMMA_m ∘ (eps m)⁻¹` is a natural family of isomorphisms. -/
theorem exists_bridge_of_data
    (GAMMA : ∀ m : ℕ, (↑(groupHomology.H1 (flowRepG p G m i j T)) : Type) ≃+
      Work.Tate.Hm1 G (E p G m i j ⊗[ZMod p] (T ⊗[ZMod p] augIdeal p G)))
    (hGAMMA : ∀ ⦃m n : ℕ⦄ (Φ : OperatorMap G m n)
      (z : (↑(groupHomology.H1 (flowRepG p G m i j T)) : Type)),
      GAMMA n (indH1 (i:=i) (j:=j) (T:=T) Φ z)
        = (Φ.hm1Map p G (T ⊗[ZMod p] augIdeal p G)) (GAMMA m z))
    (eps : ∀ m : ℕ, (↑(groupHomology.H1 (flowRepG p G m i j T)) : Type) ≃+
      (↑(groupHomology.H1 (flowRepG p G m i j T)) : Type))
    (heps : ∀ m x, eps m (Psi (i:=i) (j:=j) (T:=T) m x) = flowHSβ p G i j T m x) :
    ∃ γ : ∀ m : ℕ, (↑(groupHomology.H1 (flowRepG p G m i j T)) : Type) →+
      Work.Tate.Hm1 G (E p G m i j ⊗[ZMod p] (T ⊗[ZMod p] augIdeal p G)),
      (∀ m, Function.Injective (γ m)) ∧ (∀ m, Function.Surjective (γ m)) ∧
      (∀ ⦃m n : ℕ⦄ (Φ : OperatorMap G m n)
        (y : (↑(groupHomology.H1 (flowRep p G m i j T)) : Type)),
        (Φ.hm1Map p G (T ⊗[ZMod p] augIdeal p G))
            (γ m (flowHSβ p G i j T m y))
          = γ n (flowHSβ p G i j T n (flowZMap (p := p) G i j Φ T y))) := by
  refine ⟨fun m => (GAMMA m).toAddMonoidHom.comp (eps m).symm.toAddMonoidHom,
    fun m => (GAMMA m).injective.comp (eps m).symm.injective,
    fun m => (GAMMA m).surjective.comp (eps m).symm.surjective, ?_⟩
  intro m n Φ y
  have h1 : (eps m).symm (flowHSβ p G i j T m y) = Psi (i:=i) (j:=j) (T:=T) m y := by
    rw [← heps m y, AddEquiv.symm_apply_apply]
  have h2 : (eps n).symm (flowHSβ p G i j T n (flowZMap (p := p) G i j Φ T y))
      = Psi (i:=i) (j:=j) (T:=T) n (flowZMap (p := p) G i j Φ T y) := by
    rw [← heps n (flowZMap (p := p) G i j Φ T y), AddEquiv.symm_apply_apply]
  change (Φ.hm1Map p G (T ⊗[ZMod p] augIdeal p G))
      (GAMMA m ((eps m).symm (flowHSβ p G i j T m y)))
    = (GAMMA n) ((eps n).symm (flowHSβ p G i j T n (flowZMap (p := p) G i j Φ T y)))
  rw [h1, h2, ← hGAMMA (m:=m) (n:=n) Φ (Psi (i:=i) (j:=j) (T:=T) m y)]
  congr 1
  exact (congrArg (fun f : (↑(groupHomology.H1 (flowRep p G m i j T)) : Type) →+
      (↑(groupHomology.H1 (flowRepG p G n i j T)) : Type) => f y)
    (Psi_natural (i:=i) (j:=j) (T:=T) Φ)).symm

end Work.Bridge
