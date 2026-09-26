import Mathlib
import Submission.Work.PTCert.GlueDefs
import Submission.Work.PTCert.twistedFourierCriterion

/-!
# Shared helpers for the Fourier transport lemma `FourierTransport` (GL4)

Small facts about the sign character `chiS` under a coordinate permutation, and about a
`(ℤ/2)^m`-action satisfying `act (a + b) = act a ∘ act b` (so that every `act a` is an
involution, since `a + a = 0`).  Used both in the key scalar identity
`fourierW (S.map p) (rep (τ u)) (rep (τ v)) = χ(ν_u) χ(ν_v) · fourierW S u v`
and in the representative-transport argument.
-/

namespace Work.PTCert

open Submission.PTCert
open scoped BigOperators

set_option autoImplicit false

/-- `2 = 0` in `ZMod 2`. -/
lemma zmod2_two : (2 : ZMod 2) = 0 := by decide

/-- Every element of `ZMod 2` is its own additive inverse. -/
lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by revert x; decide

/-- `chiS` of the image of `S` under a permutation is `chiS S` composed with the permutation. -/
lemma chiS_map {m : ℕ} (S : Finset (Fin m)) (p : Equiv.Perm (Fin m)) (a : Fin m → ZMod 2) :
    chiS (S.map p.toEmbedding) a = chiS S (fun i => a (p i)) := by
  simp only [chiS]
  rw [Finset.prod_map]
  rfl

/-- The inverse form of `chiS_map`. -/
lemma chiS_map_symm {m : ℕ} (S : Finset (Fin m)) (p : Equiv.Perm (Fin m))
    (b : Fin m → ZMod 2) :
    chiS (S.map p.toEmbedding) (fun i => b (p.symm i)) = chiS S b := by
  rw [chiS_map]
  congr 1
  ext i
  simp

/-- Every `act a` is an involution: `act a (act a x) = x`. -/
lemma act_neg {m : ℕ} {ι : Type} (act : (Fin m → ZMod 2) → ι → ι)
    (hact_add : ∀ a b x, act (a + b) x = act a (act b x)) (hact_zero : ∀ x, act 0 x = x)
    (a : Fin m → ZMod 2) (x : ι) : act a (act a x) = x := by
  have h : a + a = 0 := by funext i; exact zmod2_add_self (a i)
  rw [← hact_add a a x, h, hact_zero]

/-- The normalising relation of `τ`, in the direction used to push `act` past `τ`. -/
lemma tau_act {m : ℕ} {ι : Type} (act : (Fin m → ZMod 2) → ι → ι) (τ : ι ≃ ι)
    (p : Equiv.Perm (Fin m))
    (hτ : ∀ a x, τ (act a x) = act (fun i => a (p.symm i)) (τ x)) :
    ∀ a x, act a (τ x) = τ (act (fun i => a (p i)) x) := by
  intro a x
  have h := hτ (fun i => a (p i)) x
  have h2 : (fun i => (fun j => a (p j)) (p.symm i)) = a := by funext i; simp
  rw [h2] at h
  exact h.symm

/-- `τ.symm` also normalises the action, with the inverse coordinate permutation. -/
lemma tau_symm_act {m : ℕ} {ι : Type} (act : (Fin m → ZMod 2) → ι → ι) (τ : ι ≃ ι)
    (p : Equiv.Perm (Fin m))
    (hτ : ∀ a x, τ (act a x) = act (fun i => a (p.symm i)) (τ x)) :
    ∀ a x, τ.symm (act a x) = act (fun i => a (p i)) (τ.symm x) := by
  intro a x
  apply τ.injective
  rw [Equiv.apply_symm_apply, hτ (fun i => a (p i)) (τ.symm x), Equiv.apply_symm_apply]
  congr 1
  funext i
  simp

end Work.PTCert
