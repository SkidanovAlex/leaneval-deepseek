import Mathlib
import Submission.Work.BG.HatInjDefs
import Submission.Work.BG.hatInjParity
import Submission.OddOrder.FeitThompson
import Submission.OddOrder.GroupTheory.RepresentationTheory.BrauerPermutationUnconditional
import Submission.OddOrder.Isaacs.Ch04_Commutators.ForwardFromCh03

/-!
# Area BG: the Glauberman count (`hatInjCount`)

Backup route for `Work.BG.hatInjCount`: for a finite group `U` of odd order with an involutive
automorphism `σ`, `#{σ-invariant irreducibles of U} = |Irr(C_U(σ))|`.

The proof is the standard one:
`#σ-invariant irreducibles = #σ-invariant classes` (Brauer's permutation lemma for the two
permutations induced by `σ` on `Irr U` and `ConjClasses U`),
`#σ-invariant classes = #classes of C_U(σ)` (Isaacs Theorem 3.26,
`OddOrder.Isaacs.Ch04.aInvariantConjClassesEquiv`), and
`#classes of C_U(σ) = |Irr(C_U(σ))|` (`card_irreducibleCharacter_eq`).
-/

namespace Work.BG

open OddOrder.RepresentationTheory

variable {U : Type} [Group U]

theorem mulAut_mul_self_apply (σ : MulAut U) (hσ : σ * σ = 1) (u : U) : σ (σ u) = u := by
  have h := congrArg (fun e : MulAut U => e u) hσ
  simpa using h

/-- Composition rule for the induced class map. -/
theorem conjClasses_map_comp (f g : U →* U) (C : ConjClasses U) :
    ConjClasses.map (f.comp g) C = ConjClasses.map f (ConjClasses.map g C) := by
  obtain ⟨a, rfl⟩ := ConjClasses.exists_rep C
  rfl

/-- The class map induced by an involutive automorphism is an involution. -/
theorem conjClassesMap_involutive (σ : MulAut U) (hσ : σ * σ = 1) :
    Function.Involutive (fun C : ConjClasses U => ConjClasses.map (σ : U →* U) C) := by
  intro C
  obtain ⟨a, rfl⟩ := ConjClasses.exists_rep C
  show ConjClasses.map (σ : U →* U) (ConjClasses.map (σ : U →* U) (ConjClasses.mk a)) =
    ConjClasses.mk a
  rw [show ConjClasses.map (σ : U →* U) (ConjClasses.mk a) = ConjClasses.mk (σ a) from rfl,
    show ConjClasses.map (σ : U →* U) (ConjClasses.mk (σ a)) =
      ConjClasses.mk (σ (σ a)) from rfl,
    mulAut_mul_self_apply σ hσ a]

/-- The permutation of `Irr U` given by `α ↦ α ∘ σ`. -/
noncomputable def irrPerm (σ : MulAut U) (hσ : σ * σ = 1) :
    Equiv.Perm (IrreducibleCharacter U) :=
  Function.Involutive.toPerm (twist σ) (fun α => twist_involutive σ hσ α)

@[simp] theorem irrPerm_apply (σ : MulAut U) (hσ : σ * σ = 1) (α : IrreducibleCharacter U) :
    irrPerm σ hσ α = twist σ α := rfl

/-- The permutation of `ConjClasses U` given by the class map of `σ`. -/
noncomputable def classPerm (σ : MulAut U) (hσ : σ * σ = 1) : Equiv.Perm (ConjClasses U) :=
  Function.Involutive.toPerm _ (conjClassesMap_involutive σ hσ)

@[simp] theorem classPerm_apply (σ : MulAut U) (hσ : σ * σ = 1) (C : ConjClasses U) :
    classPerm σ hσ C = ConjClasses.map (σ : U →* U) C := rfl

/-- The character table is compatible with the two permutations induced by `σ`. -/
theorem characterTableEntry_perm (σ : MulAut U) (hσ : σ * σ = 1)
    (χ : IrreducibleCharacter U) (C : ConjClasses U) :
    characterTableEntry (irrPerm σ hσ χ) C = characterTableEntry χ (classPerm σ hσ C) := by
  rw [characterTableEntry, characterTableEntry, irrPerm_apply, twist_apply]
  have h1 : ConjClasses.mk (conjugacyClassRepresentative (classPerm σ hσ C)) =
      classPerm σ hσ C := conjugacyClassRepresentative_mk_eq _
  have h2 : classPerm σ hσ C = ConjClasses.mk (σ (conjugacyClassRepresentative C)) := by
    rw [classPerm_apply]
    conv_lhs => rw [← conjugacyClassRepresentative_mk_eq C]
    rfl
  refine (χ : ClassFunction U ℂ).of_isConj ?_
  rw [← ConjClasses.mk_eq_mk_iff_isConj, h1, h2]

/-- `#σ-invariant irreducibles = #σ-fixed points of the twist permutation`. -/
theorem card_sigmaInvIrr_eq_fixedPoints_irrPerm (σ : MulAut U) (hσ : σ * σ = 1) :
    Nat.card (SigmaInvIrr U σ) = Nat.card (Function.fixedPoints (irrPerm σ hσ)) :=
  Nat.card_congr (Equiv.subtypeEquivRight (fun α => (twist_eq_self_iff σ α).symm))

/-- Iterating the class map of a fixed class. -/
theorem conjClasses_map_pow {σ : MulAut U} {C : ConjClasses U}
    (hfix : ConjClasses.map (σ : U →* U) C = C) :
    ∀ n : ℕ, ConjClasses.map (((σ ^ n : MulAut U)) : U →* U) C = C := by
  intro n
  induction n with
  | zero =>
    have h0 : (((1 : MulAut U)) : U →* U) = MonoidHom.id U := rfl
    rw [pow_zero, h0, ConjClasses.map_id]
  | succ n ih =>
    have hcast : (((σ ^ (n + 1) : MulAut U)) : U →* U)
        = (((σ ^ n : MulAut U)) : U →* U).comp (σ : U →* U) := by
      ext x
      rw [pow_succ]
      rfl
    rw [hcast, conjClasses_map_comp, hfix, ih]

section ClassSide

variable [Finite U]

/-- The set of automorphisms that fix the conjugacy class `C`. -/
def classFix (C : ConjClasses U) : Subgroup (MulAut U) where
  carrier := {l : MulAut U | ConjClasses.map (l : U →* U) C = C}
  one_mem' := by
    show ConjClasses.map (((1 : MulAut U)) : U →* U) C = C
    rw [show (((1 : MulAut U)) : U →* U) = MonoidHom.id U from rfl, ConjClasses.map_id]
  mul_mem' := by
    intro f g hf hg
    show ConjClasses.map ((f * g : MulAut U) : U →* U) C = C
    have hcast : ((f * g : MulAut U) : U →* U) = (f : U →* U).comp (g : U →* U) := by
      ext x
      rfl
    rw [hcast, conjClasses_map_comp, hg, hf]
  inv_mem' := by
    intro f hf
    show ConjClasses.map ((f⁻¹ : MulAut U) : U →* U) C = C
    have hcast : (((f⁻¹ * f : MulAut U)) : U →* U) =
        ((f⁻¹ : MulAut U) : U →* U).comp ((f : MulAut U) : U →* U) := by
      ext x
      rfl
    calc ConjClasses.map ((f⁻¹ : MulAut U) : U →* U) C
        = ConjClasses.map ((f⁻¹ : MulAut U) : U →* U)
            (ConjClasses.map (f : U →* U) C) := by rw [hf]
      _ = ConjClasses.map ((((f⁻¹ : MulAut U)) : U →* U).comp (((f : MulAut U)) : U →* U)) C :=
            (conjClasses_map_comp _ _ C).symm
      _ = ConjClasses.map (((f⁻¹ * f : MulAut U)) : U →* U) C := by rw [← hcast]
      _ = ConjClasses.map (((1 : MulAut U)) : U →* U) C := by rw [inv_mul_cancel]
      _ = ConjClasses.map (MonoidHom.id U) C := by
            rw [show (((1 : MulAut U)) : U →* U) = MonoidHom.id U from rfl]
      _ = C := ConjClasses.map_id C

/-- `C_U(σ)` is the fixed subgroup of the action of the cyclic group `⟨σ⟩`. -/
theorem fixedSubgroup_zpowers_eq (σ : MulAut U) (hσ : σ * σ = 1) :
    OddOrder.GroupTheory.fixedSubgroup (Subgroup.zpowers σ).subtype ⊤ = fixedSubgroup σ := by
  ext u
  rw [OddOrder.GroupTheory.mem_fixedSubgroup]
  constructor
  · intro h
    exact h ⟨σ, Subgroup.mem_zpowers σ⟩ (Subgroup.mem_top _)
  · intro h a _
    have hs : σ ∈ MulAction.stabilizer (MulAut U) u := by
      rw [MulAction.mem_stabilizer_iff]
      exact h
    have hle := (Subgroup.zpowers_le (H := MulAction.stabilizer (MulAut U) u)).mpr hs
    have hmem := hle a.2
    rwa [MulAction.mem_stabilizer_iff] at hmem

/-- A class is fixed by the action of `⟨σ⟩` iff it is fixed by `σ`. -/
theorem conjClasses_map_subtype_eq (σ : MulAut U) (hσ : σ * σ = 1) (C : ConjClasses U) :
    (∀ a : ↥(Subgroup.zpowers σ),
        ConjClasses.map ((Subgroup.zpowers σ).subtype a).toMonoidHom C = C) ↔
      ConjClasses.map (σ : U →* U) C = C := by
  constructor
  · intro h
    simpa using h ⟨σ, Subgroup.mem_zpowers σ⟩
  · intro h a
    have hle := (Subgroup.zpowers_le (H := classFix C)).mpr (show σ ∈ classFix C from h)
    exact hle a.2

/-- **The Glauberman count**, backup proof (Brauer's permutation lemma for the automorphism `σ`,
Isaacs 3.26 on `A`-invariant classes, and `#Irr = #ConjClasses`). -/
theorem hatInjCountAlt {U : Type} [Group U] [Finite U]
    (hU : Odd (Nat.card U)) (σ : MulAut U) (hσ : σ * σ = 1) :
    Nat.card (SigmaInvIrr U σ) = Nat.card (IrreducibleCharacter ↥(fixedSubgroup σ)) := by
  classical
  haveI : Fintype U := Fintype.ofFinite U
  -- coprimality of `|⟨σ⟩|` with `|U|`, and solvability
  have hdiv : Nat.card ↥(Subgroup.zpowers σ) ∣ 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hσ)
  have hcop : Nat.Coprime (Nat.card ↥(Subgroup.zpowers σ)) (Nat.card U) := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with h | h
    · rw [h]
      exact Nat.coprime_one_left _
    · rw [h]
      exact Nat.coprime_comm.mpr (Nat.coprime_two_right.mpr hU)
  have hSolv : Group.IsSolvable ↥(Subgroup.zpowers σ) ∨ Group.IsSolvable U :=
    Or.inr (OddOrder.feitThompson hU)
  -- Isaacs 3.26 for the action of `⟨σ⟩` on `U`
  have heq := OddOrder.Isaacs.Ch04.aInvariantConjClassesEquiv
    (G := U) (A := ↥(Subgroup.zpowers σ)) (φ := (Subgroup.zpowers σ).subtype) hcop hSolv
  have h1 : Nat.card (ConjClasses ↥(OddOrder.GroupTheory.fixedSubgroup
        (Subgroup.zpowers σ).subtype ⊤))
      = Nat.card (ConjClasses ↥(fixedSubgroup σ)) :=
    Nat.card_congr (Equiv.cast (congrArg (fun H : Subgroup U => ConjClasses ↥H)
      (fixedSubgroup_zpowers_eq σ hσ)))
  have h2 : Nat.card (ConjClasses ↥(OddOrder.GroupTheory.fixedSubgroup
        (Subgroup.zpowers σ).subtype ⊤))
      = Nat.card {C : ConjClasses U // classPerm σ hσ C = C} :=
    (Nat.card_congr heq).trans (Nat.card_congr (Equiv.subtypeEquivRight
      (fun C => (conjClasses_map_subtype_eq σ hσ C).trans (by rw [classPerm_apply]))))
  have h3 : Nat.card (Function.fixedPoints (classPerm σ hσ))
      = Nat.card {C : ConjClasses U // classPerm σ hσ C = C} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun C => Function.mem_fixedPoints))
  calc Nat.card (SigmaInvIrr U σ)
      = Nat.card (Function.fixedPoints (irrPerm σ hσ)) :=
        card_sigmaInvIrr_eq_fixedPoints_irrPerm σ hσ
    _ = Nat.card (Function.fixedPoints (classPerm σ hσ)) :=
        brauer_permutation_lemma_general' (irrPerm σ hσ) (classPerm σ hσ)
          (characterTableEntry_perm σ hσ)
    _ = Nat.card {C : ConjClasses U // classPerm σ hσ C = C} := h3
    _ = Nat.card (ConjClasses ↥(OddOrder.GroupTheory.fixedSubgroup
          (Subgroup.zpowers σ).subtype ⊤)) := h2.symm
    _ = Nat.card (ConjClasses ↥(fixedSubgroup σ)) := h1
    _ = Nat.card (IrreducibleCharacter ↥(fixedSubgroup σ)) :=
        (card_irreducibleCharacter_eq (G := ↥(fixedSubgroup σ))).symm

end ClassSide

end Work.BG
