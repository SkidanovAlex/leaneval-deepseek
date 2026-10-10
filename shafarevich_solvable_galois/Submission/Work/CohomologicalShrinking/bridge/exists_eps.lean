import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Algebra.Field.ZMod
import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
import Submission.Work.CohomologicalShrinking.bridge.Psi_ker
import Submission.Work.CohomologicalShrinking.bridge.Psi_surjective
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.CohomologicalShrinking.bridge

open Work.CohomologicalShrinking

/-- The canonical coinflation `Ψ` and the second map `β` of the homological Hochschild–Serre
sequence have the *same* kernel (`range corest = range flowHSα = ker flowHSβ`) and the *same*
(surjective) target.  Hence there is a unique additive automorphism `ε` of `H₁(G, E(m,τ)⊗T)` with
`ε ∘ Ψ = flowHSβ` — equivalently, the two maps `Ψ` and `flowHSβ` differ by an automorphism of
their common target. -/
theorem exists_eps (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Fintype G] (i j : ℕ)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T] (m : ℕ) :
    ∃ ε : (↑(groupHomology.H1 (Work.CohomologicalShrinking.flowRepG p G m i j T)) : Type) ≃+
      (↑(groupHomology.H1 (Work.CohomologicalShrinking.flowRepG p G m i j T)) : Type),
      ∀ x, ε (Work.Bridge.Psi (p := p) (G := G) (i := i) (j := j) (T := T) m x)
        = Work.CohomologicalShrinking.flowHSβ p G i j T m x := by
  classical
  have hsurj : Function.Surjective
      (Work.Bridge.Psi (p := p) (G := G) (i := i) (j := j) (T := T) m) :=
    Psi_surjective p G i j T m
  -- `ker Ψ = ker β`: `ker Ψ = range corest = range flowHSα = ker flowHSβ`
  have hker : (Work.Bridge.Psi (p := p) (G := G) (i := i) (j := j) (T := T) m).ker
      = (flowHSβ p G i j T m).ker := by
    rw [Psi_ker p G i j T m,
      Work.Bridge.corest_eq_flowHSα (p := p) (G := G) (i := i) (j := j) (T := T) m]
    exact (flowHS_spec p G i j T m).2.2
  -- the additive map `ε₀` induced by `Ψ` and `β`
  obtain ⟨ε₀, hε₀⟩ :
      ∃ ε₀ : (↑(groupHomology.H1 (flowRepG p G m i j T)) : Type) →+
        (↑(groupHomology.H1 (flowRepG p G m i j T)) : Type),
        ε₀.comp (Work.Bridge.Psi (p := p) (G := G) (i := i) (j := j) (T := T) m)
          = flowHSβ p G i j T m :=
    ⟨(AddMonoidHom.liftOfSurjective (Work.Bridge.Psi (p := p) (G := G) (i := i) (j := j)
          (T := T) m) hsurj) ⟨flowHSβ p G i j T m, le_of_eq hker⟩,
      AddMonoidHom.liftOfRightInverse_comp
        (Work.Bridge.Psi (p := p) (G := G) (i := i) (j := j) (T := T) m)
        (Function.surjInv hsurj) (Function.rightInverse_surjInv hsurj)
        ⟨flowHSβ p G i j T m, le_of_eq hker⟩⟩
  have happ : ∀ x : (↑(groupHomology.H1 (flowRep p G m i j T)) : Type),
      ε₀ (Work.Bridge.Psi (p := p) (G := G) (i := i) (j := j) (T := T) m x)
        = flowHSβ p G i j T m x := by
    intro x
    change (ε₀.comp (Work.Bridge.Psi (p := p) (G := G) (i := i) (j := j) (T := T) m)) x
      = (flowHSβ p G i j T m) x
    rw [hε₀]
  -- `ε₀` is injective, because `ker Ψ = ker β`
  have hinj : Function.Injective ε₀ := by
    intro a b hab
    obtain ⟨x, rfl⟩ := hsurj a
    obtain ⟨y, rfl⟩ := hsurj b
    rw [happ x, happ y] at hab
    have h1 : x - y ∈ (flowHSβ p G i j T m).ker := by
      rw [AddMonoidHom.mem_ker, map_sub, hab, sub_self]
    have h2 : x - y ∈ (Work.Bridge.Psi (p := p) (G := G) (i := i) (j := j) (T := T) m).ker :=
      hker.symm ▸ h1
    have h3 : (Work.Bridge.Psi (p := p) (G := G) (i := i) (j := j) (T := T) m) (x - y) = 0 :=
      (AddMonoidHom.mem_ker).1 h2
    rw [map_sub, sub_eq_zero] at h3
    exact h3
  -- `ε₀` is surjective, because `β` is surjective
  have hsurj₀ : Function.Surjective ε₀ := by
    intro y
    obtain ⟨x, hx⟩ := (flowHS_spec p G i j T m).2.1 y
    exact ⟨Work.Bridge.Psi (p := p) (G := G) (i := i) (j := j) (T := T) m x, by
      rw [happ, hx]⟩
  have hbij : Function.Bijective ε₀ := ⟨hinj, hsurj₀⟩
  refine ⟨AddEquiv.ofBijective ε₀ hbij, ?_⟩
  intro x
  exact (AddEquiv.ofBijective_apply ε₀ hbij
      (Work.Bridge.Psi (p := p) (G := G) (i := i) (j := j) (T := T) m x)).trans (happ x)

end Work.CohomologicalShrinking.bridge
