import Mathlib.GroupTheory.Index
import Submission.Commons.GroupTheory.Hopfian.finite_homs_of_fg

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Commons.GroupTheory.Hopfian

noncomputable section

/-- A bijection between the cosets of a finite-index subgroup `H` and `Fin n`, given
that `H.index = n`. -/
private def finEquiv_of_index {G : Type*} [Group G] (n : ℕ) {H : Subgroup G}
    (hF : H.FiniteIndex) (hidx : H.index = n) : (G ⧸ H) ≃ Fin n := by
  letI : H.FiniteIndex := hF
  letI : Fintype (G ⧸ H) := Subgroup.fintypeQuotientOfFiniteIndex (G := G) (H := H)
  have hcard : Fintype.card (G ⧸ H) = n := by
    have h1 : Nat.card (G ⧸ H) = n := by
      rw [← Subgroup.index_eq_card H]
      exact hidx
    exact (Nat.card_eq_fintype_card (α := G ⧸ H)).symm.trans h1
  exact Fintype.equivFinOfCardEq hcard

/-- The permutation representation of `G` on the cosets of `H`, transported along `e`
to a permutation representation on `Fin n`. -/
private def permRep {G : Type*} [Group G] {H : Subgroup G} {n : ℕ}
    (e : (G ⧸ H) ≃ Fin n) : G →* Equiv.Perm (Fin n) :=
  (e.permCongrHom.toMonoidHom).comp (MulAction.toPermHom G (G ⧸ H))

/-- `g` fixes the transported trivial coset iff `g ∈ H`: the fixed coset is exactly the
stabilizer of the trivial coset, which is `H`. -/
private lemma permRep_fixed_iff {G : Type*} [Group G] {H : Subgroup G} {n : ℕ}
    (e : (G ⧸ H) ≃ Fin n) (g : G) :
    permRep e g (e ((1 : G) : G ⧸ H)) = e ((1 : G) : G ⧸ H) ↔ g ∈ H := by
  have hred : permRep e g (e ((1 : G) : G ⧸ H)) =
      e (g • ((1 : G) : G ⧸ H)) := by
    simp [permRep]
  calc
    permRep e g (e ((1 : G) : G ⧸ H)) = e ((1 : G) : G ⧸ H)
        ↔ g • ((1 : G) : G ⧸ H) = ((1 : G) : G ⧸ H) := by
      constructor
      · intro h
        apply e.injective
        rw [← hred]
        exact h
      · intro hg
        rw [hred, hg]
    _ ↔ g ∈ H := by
      rw [← MulAction.mem_stabilizer_iff, MulAction.stabilizer_quotient]

/-- There are only finitely many subgroups of a given finite index `n` in a finitely
generated group.  Proof sketch: for each such subgroup `H` choose (Classical.choice) an
identification `e : G ⧸ H ≃ Fin n` and form `(φ, p)` with `φ : G →* Equiv.Perm (Fin n)`
the transported coset-permutation representation and `p := e (1 : G ⧸ H)`.  The map
`H ↦ (φ, p)` is injective (`g ∈ H` iff `φ g` fixes `p`), and the codomain is finite via
`finite_homs_of_fg`.  Non-normal strengthening of `finite_normalSubgroups_of_index`. -/
theorem finite_subgroups_of_index {G : Type*} [Group G] [Group.FG G] (n : ℕ) :
    Finite {H : Subgroup G // H.FiniteIndex ∧ H.index = n} := by
  classical
  let S := {H : Subgroup G // H.FiniteIndex ∧ H.index = n}
  let e : (H : S) → (G ⧸ H.1) ≃ Fin n := fun H => finEquiv_of_index n H.2.1 H.2.2
  let φ : (H : S) → G →* Equiv.Perm (Fin n) := fun H => permRep (e H)
  let p : (H : S) → Fin n := fun H => e H ((1 : G) : G ⧸ H.1)
  have hfin : Finite (G →* Equiv.Perm (Fin n)) :=
    finite_homs_of_fg (G := G) (Equiv.Perm (Fin n))
  letI : Finite (G →* Equiv.Perm (Fin n)) := hfin
  refine Finite.of_injective (fun H : S => (φ H, p H)) ?_
  intro H₁ H₂ h
  have hφ : φ H₁ = φ H₂ := congrArg Prod.fst h
  have hp : p H₁ = p H₂ := congrArg Prod.snd h
  apply Subtype.ext
  ext g
  constructor
  · intro hg₁
    apply (permRep_fixed_iff (e H₂) g).1
    have hfix₁ : φ H₁ g (p H₁) = p H₁ := (permRep_fixed_iff (e H₁) g).2 hg₁
    calc
      φ H₂ g (p H₂) = φ H₁ g (p H₂) := by
        have hg : φ H₂ g = φ H₁ g :=
          congrArg (fun ψ : G →* Equiv.Perm (Fin n) => ψ g) hφ.symm
        exact congrArg (fun π : Equiv.Perm (Fin n) => π (p H₂)) hg
      _ = φ H₁ g (p H₁) := by rw [hp]
      _ = p H₁ := hfix₁
      _ = p H₂ := hp
  · intro hg₂
    apply (permRep_fixed_iff (e H₁) g).1
    have hfix₂ : φ H₂ g (p H₂) = p H₂ := (permRep_fixed_iff (e H₂) g).2 hg₂
    calc
      φ H₁ g (p H₁) = φ H₂ g (p H₁) := by
        have hg : φ H₁ g = φ H₂ g :=
          congrArg (fun ψ : G →* Equiv.Perm (Fin n) => ψ g) hφ
        exact congrArg (fun π : Equiv.Perm (Fin n) => π (p H₁)) hg
      _ = φ H₂ g (p H₂) := by rw [hp]
      _ = p H₂ := hfix₂
      _ = p H₁ := hp.symm

end

end Commons.GroupTheory.Hopfian