/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# The no-zero-exponent-sum case, via Magnus's embedding

This module sets up the vocabulary of the *embedding* route to the "no letter of the relator has
exponent sum zero" case of the Magnus--Moldavanskii step (lead design, `MM_NOZERO_LEAD.md`).

The substitution `ψ = subst t x p q` of `Submission.Work.OROneRel.HNNStep`
(`t ↦ t^p`, `x ↦ x * t^(-q)`, all other letters fixed) induces a homomorphism

  `substHom r t x p q : ⟨α | r⟩ →* ⟨α | ψ r⟩`,   `mk w ↦ mk (ψ w)`  (`substHom_mk`),

which for `p = eps x r`, `q = eps t r` kills the exponent sum of `t` (`eps_subst_t`) and is an
embedding (`Work.OROneRel.SubstEmbedding.substHom_injective`, delegated separately).

The second half of the file provides the amalgam
`⟨α | r⟩ ∗_(t^n = s^(p n)) ⟨s⟩ ≅ ⟨α | ψ r⟩` (`Work.OROneRel.SubstPushout.subst_pushout_equiv`):
`AmFactor r : Bool → Type u` is the family of factors, `amPhi r t p` the two maps out of the common
edge group `ULift (Multiplicative ℤ)`.

Everything here is sorry-free and depends only on `propext`, `Classical.choice`, `Quot.sound`.
-/
import Mathlib
import Submission.Work.OROneRel.HNNStep
import Submission.Work.OROneRel.case2_substitution
import Submission.Work.OROneRel.eps_eq_toAdd_sigma

set_option autoImplicit false

namespace Work.OROneRel

universe u v

/-! ## 1. The homomorphism induced by a Case-2 substitution -/

/-- The substitution `ψ = subst t x p q` (`t ↦ t^p`, `x ↦ x * t^(-q)`) induces a homomorphism of
one-relator groups `⟨α | r⟩ →* ⟨α | ψ r⟩`. -/
noncomputable def substHom {α : Type u} (r : FreeGroup α) (t x : α) (p q : ℤ) :
    PresentedGroup ({r} : Set (FreeGroup α)) →*
      PresentedGroup ({subst t x p q r} : Set (FreeGroup α)) :=
  PresentedGroup.map (subst t x p q)
    (by intro y hy; rw [Set.mem_singleton_iff] at hy ⊢; rw [hy])

/-- `substHom` carries the class of `w` to the class of `ψ w`. -/
theorem substHom_mk {α : Type u} (r : FreeGroup α) (t x : α) (p q : ℤ) (w : FreeGroup α) :
    substHom r t x p q (PresentedGroup.mk ({r} : Set (FreeGroup α)) w) =
      PresentedGroup.mk ({subst t x p q r} : Set (FreeGroup α)) (subst t x p q w) := by
  unfold substHom
  change (QuotientGroup.map _ _ (subst t x p q) _) (QuotientGroup.mk' _ w) = _
  rw [QuotientGroup.map_mk']
  rfl

/-- `substHom` on the canonical generators. -/
theorem substHom_of {α : Type u} (r : FreeGroup α) (t x : α) (p q : ℤ) (a : α) :
    substHom r t x p q (PresentedGroup.of a) =
      PresentedGroup.mk ({subst t x p q r} : Set (FreeGroup α))
        (subst t x p q (FreeGroup.of a)) := by
  rw [PresentedGroup.of, substHom_mk]

/-- `substHom` commutes with powers of the image of a word. -/
theorem substHom_mk_pow {α : Type u} (r : FreeGroup α) (t x : α) (p q : ℤ) (w : FreeGroup α)
    (l : ℕ) :
    substHom r t x p q ((PresentedGroup.mk ({r} : Set (FreeGroup α)) w) ^ l) =
      (PresentedGroup.mk ({subst t x p q r} : Set (FreeGroup α)) (subst t x p q w)) ^ l := by
  rw [← map_pow, substHom_mk, map_pow, map_pow]

/-- **The exponent sum of `t` after the substitution.**  `σ_t (ψ w) = p σ_t w - q σ_x w`; with
`p = σ_x w` and `q = σ_t w` this is `0`. -/
theorem eps_subst_t {α : Type u} {t x : α} (hxt : x ≠ t) (p q : ℤ) (w : FreeGroup α) :
    eps t (subst t x p q w) = p * eps t w - q * eps x w := by
  have h := congrArg Multiplicative.toAdd (c2s_sigma_t_subst (α := α) hxt p q w)
  simp only [toAdd_mul, toAdd_zpow] at h
  simp only [eps_eq_toAdd_sigma]
  rw [h]
  ring

/-! ## 2. The amalgam `⟨α | r⟩ ∗_(t^n = s^(p n)) ⟨s⟩` -/

/-- The two factors of the amalgam: the one-relator group `⟨α | r⟩` and the infinite cyclic group
that carries the new generator `s`. -/
noncomputable abbrev AmFactor {α : Type u} (r : FreeGroup α) : Bool → Type u
  | true => PresentedGroup ({r} : Set (FreeGroup α))
  | false => ULift.{u} (Multiplicative ℤ)

noncomputable instance instGroupAmFactor {α : Type u} (r : FreeGroup α) :
    ∀ i : Bool, Group (AmFactor r i)
  | true => inferInstanceAs (Group (PresentedGroup ({r} : Set (FreeGroup α))))
  | false => ULift.group

/-- The two amalgamation maps `n ↦ (mk t)^n` into `⟨α | r⟩` and `n ↦ s^(p n)` into `⟨s⟩`, out of
the common edge group `ULift (Multiplicative ℤ)`. -/
noncomputable def amPhi {α : Type u} (r : FreeGroup α) (t : α) (p : ℤ) :
    ∀ i : Bool, ULift.{u} (Multiplicative ℤ) →* AmFactor r i
  | true => MonoidHom.mk'
      (fun n : ULift.{u} (Multiplicative ℤ) =>
        (PresentedGroup.mk ({r} : Set (FreeGroup α)) (FreeGroup.of t)) ^
          (Multiplicative.toAdd n.down))
      (fun a b => by
        rw [show Multiplicative.toAdd (a * b).down =
              Multiplicative.toAdd a.down + Multiplicative.toAdd b.down from rfl,
          zpow_add])
  | false => MonoidHom.mk'
      (fun n : ULift.{u} (Multiplicative ℤ) => ULift.up (n.down ^ p))
      (fun a b => by
        rw [show (a * b).down ^ p = a.down ^ p * b.down ^ p from by
          rw [show (a * b).down = a.down * b.down from rfl, mul_zpow]]
        rfl)

@[simp]
theorem amPhi_true_apply {α : Type u} (r : FreeGroup α) (t : α) (p : ℤ)
    (n : ULift.{u} (Multiplicative ℤ)) :
    amPhi r t p true n =
      (PresentedGroup.mk ({r} : Set (FreeGroup α)) (FreeGroup.of t)) ^
        (Multiplicative.toAdd n.down) :=
  rfl

@[simp]
theorem amPhi_false_apply {α : Type u} (r : FreeGroup α) (t : α) (p : ℤ)
    (n : ULift.{u} (Multiplicative ℤ)) :
    amPhi r t p false n = ULift.up (n.down ^ p) :=
  rfl

end Work.OROneRel
