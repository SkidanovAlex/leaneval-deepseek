/-
Copyright: subproject `ORLocInd` -- the Cohen--Lyndon basis theorem (node N4).

# Definitions for the substitution step (Case 2) of the Cohen--Lyndon induction

This module contains the free-group infrastructure used by
`Submission/Work/ORLocInd/CohenLyndon/cohenLyndonNC_subst.lean`: the free group `P = F(α₁)`
obtained from `F(α)` by adjoining one extra letter `z`, the copy `rootHom : F(α) →* P` of `F(α)`
inside `P` (with `t ↦ z ^ p`), the isomorphism `theta : F(α) ≃* P` of the Magnus change of
generators (`t ↦ z`, `x ↦ x * z ^ q`), and the key identity `theta ∘ ψ = rootHom` relating the
Magnus substitution `ψ` to the embedding.

See the header of `cohenLyndonNC_subst.lean` for the mathematics (Karrass--Solitar 1972, §4).
-/
import Mathlib
import Submission.Work.OROneRel.HNNStep
import Submission.Work.OROneRel.wcp_subst_injective

set_option autoImplicit false
set_option linter.dupNamespace false

universe u

namespace Work.ORLocInd.CohenLyndon

section Setup

variable {α : Type u} [DecidableEq α]

/-! ## The free group with an extra letter `z` -/

/-- Index type of the free group `P` obtained from `F(α)` by adjoining one new letter `z`: the
letters of `α` different from `t`, together with one extra generator. -/
abbrev RootIdx (α : Type u) (t : α) := {a : α // a ≠ t} ⊕ Unit

/-- The extra letter `z` of `P = F(RootIdx α t)`. -/
noncomputable def rootLetter (t : α) : FreeGroup (RootIdx α t) := FreeGroup.of (Sum.inr ())

/-- The embedding `rootHom t p : F(α) →* F(RootIdx α t)` with `t ↦ z ^ p` and every other letter
fixed.  This is the copy of `F(α)` inside the amalgam `⟨F(α), z | z ^ p = t⟩`. -/
noncomputable def rootHom (t : α) (p : ℤ) : FreeGroup α →* FreeGroup (RootIdx α t) :=
  FreeGroup.lift fun a => if h : a = t then rootLetter t ^ p else FreeGroup.of (Sum.inl ⟨a, h⟩)

@[simp] theorem rootHom_of_eq (t : α) (p : ℤ) :
    rootHom t p (FreeGroup.of t) = rootLetter t ^ p := by
  rw [rootHom, FreeGroup.lift_apply_of]
  simp

theorem rootHom_of_ne {t a : α} (h : a ≠ t) (p : ℤ) :
    rootHom t p (FreeGroup.of a) = FreeGroup.of (Sum.inl ⟨a, h⟩) := by
  rw [rootHom, FreeGroup.lift_apply_of, dif_neg h]

/-! ## The isomorphism `theta : F(α) ≃* P` -/

/-- The forward map `F(α) →* P` of the Magnus change of generators: `t ↦ z`,
`x ↦ x * z ^ q`, every other letter fixed. -/
noncomputable def thetaHom (t x : α) (hxt : x ≠ t) (q : ℤ) :
    FreeGroup α →* FreeGroup (RootIdx α t) :=
  FreeGroup.lift fun a =>
    if ha : a = t then rootLetter t
    else if _ : a = x then FreeGroup.of (Sum.inl ⟨x, hxt⟩) * rootLetter t ^ q
    else FreeGroup.of (Sum.inl ⟨a, ha⟩)

/-- The inverse map `P →* F(α)`: `z ↦ t`, `x ↦ x * t ^ (-q)`, every other letter fixed. -/
noncomputable def thetaInv (t x : α) (hxt : x ≠ t) (q : ℤ) :
    FreeGroup (RootIdx α t) →* FreeGroup α :=
  FreeGroup.lift (Sum.elim
    (fun a : {a : α // a ≠ t} =>
      if _ : (a : α) = x then FreeGroup.of x * (FreeGroup.of t) ^ (-q) else FreeGroup.of (a : α))
    (fun _ : Unit => FreeGroup.of t))

theorem thetaHom_of_eq (t x : α) (hxt : x ≠ t) (q : ℤ) :
    thetaHom t x hxt q (FreeGroup.of t) = rootLetter t := by
  rw [thetaHom, FreeGroup.lift_apply_of, dif_pos rfl]

theorem thetaHom_of_x (t x : α) (hxt : x ≠ t) (q : ℤ) :
    thetaHom t x hxt q (FreeGroup.of x) = FreeGroup.of (Sum.inl ⟨x, hxt⟩) * rootLetter t ^ q := by
  rw [thetaHom, FreeGroup.lift_apply_of, dif_neg hxt, dif_pos rfl]

theorem thetaHom_of_ne (t x a : α) (hxt : x ≠ t) (q : ℤ) (hat : a ≠ t) (hax : a ≠ x) :
    thetaHom t x hxt q (FreeGroup.of a) = FreeGroup.of (Sum.inl ⟨a, hat⟩) := by
  rw [thetaHom, FreeGroup.lift_apply_of, dif_neg hat, dif_neg hax]

theorem thetaInv_of_inr (t x : α) (hxt : x ≠ t) (q : ℤ) :
    thetaInv t x hxt q (rootLetter t) = FreeGroup.of t := by
  rw [thetaInv, rootLetter, FreeGroup.lift_apply_of, Sum.elim_inr]

theorem thetaInv_of_inl_eq (t x : α) (hxt : x ≠ t) (q : ℤ) :
    thetaInv t x hxt q (FreeGroup.of (Sum.inl ⟨x, hxt⟩))
      = FreeGroup.of x * (FreeGroup.of t) ^ (-q) := by
  rw [thetaInv, FreeGroup.lift_apply_of, Sum.elim_inl, dif_pos rfl]

theorem thetaInv_of_inl_ne (t x : α) (hxt : x ≠ t) (q : ℤ) {a : {a : α // a ≠ t}}
    (ha : (a : α) ≠ x) :
    thetaInv t x hxt q (FreeGroup.of (Sum.inl a)) = FreeGroup.of (a : α) := by
  rw [thetaInv, FreeGroup.lift_apply_of, Sum.elim_inl, dif_neg ha]

theorem thetaInv_comp_thetaHom (t x : α) (hxt : x ≠ t) (q : ℤ) :
    (thetaInv t x hxt q).comp (thetaHom t x hxt q) = MonoidHom.id (FreeGroup α) := by
  apply FreeGroup.ext_hom
  intro a
  show thetaInv t x hxt q (thetaHom t x hxt q (FreeGroup.of a)) = FreeGroup.of a
  by_cases hat : a = t
  · rw [hat, thetaHom_of_eq, thetaInv_of_inr]
  · by_cases hax : a = x
    · rw [hax, thetaHom_of_x, map_mul, map_zpow, thetaInv_of_inl_eq, thetaInv_of_inr]
      group
    · rw [thetaHom_of_ne t x a hxt q hat hax, thetaInv_of_inl_ne t x hxt q hax]

theorem thetaHom_comp_thetaInv (t x : α) (hxt : x ≠ t) (q : ℤ) :
    (thetaHom t x hxt q).comp (thetaInv t x hxt q)
      = MonoidHom.id (FreeGroup (RootIdx α t)) := by
  apply FreeGroup.ext_hom
  intro s
  match s with
  | Sum.inl a =>
    by_cases ha : (a : α) = x
    · have haz : a = ⟨x, hxt⟩ := Subtype.ext ha
      rw [MonoidHom.comp_apply, MonoidHom.id_apply, haz, thetaInv_of_inl_eq, map_mul, map_zpow,
        thetaHom_of_x, thetaHom_of_eq]
      group
    · rw [MonoidHom.comp_apply, MonoidHom.id_apply, thetaInv_of_inl_ne t x hxt q ha,
          thetaHom_of_ne t x (a : α) hxt q a.2 ha]
  | Sum.inr u =>
    cases u
    show (thetaHom t x hxt q) ((thetaInv t x hxt q) (rootLetter t)) = rootLetter t
    rw [thetaInv_of_inr, thetaHom_of_eq]

/-- **The isomorphism `theta : F(α) ≃* P`** of the Magnus change of generators: `t ↦ z`,
`x ↦ x * z ^ q`, every other letter fixed. -/
noncomputable def theta (t x : α) (hxt : x ≠ t) (q : ℤ) :
    FreeGroup α ≃* FreeGroup (RootIdx α t) :=
  MonoidHom.toMulEquiv (thetaHom t x hxt q) (thetaInv t x hxt q)
    (thetaInv_comp_thetaHom t x hxt q) (thetaHom_comp_thetaInv t x hxt q)

theorem theta_of_eq (t x : α) (hxt : x ≠ t) (q : ℤ) :
    (theta t x hxt q).toMonoidHom (FreeGroup.of t) = rootLetter t :=
  thetaHom_of_eq t x hxt q

theorem theta_of_x (t x : α) (hxt : x ≠ t) (q : ℤ) :
    (theta t x hxt q).toMonoidHom (FreeGroup.of x)
      = FreeGroup.of (Sum.inl ⟨x, hxt⟩) * rootLetter t ^ q :=
  thetaHom_of_x t x hxt q

theorem theta_of_ne (t x a : α) (hxt : x ≠ t) (q : ℤ) (hat : a ≠ t) (hax : a ≠ x) :
    (theta t x hxt q).toMonoidHom (FreeGroup.of a) = FreeGroup.of (Sum.inl ⟨a, hat⟩) :=
  thetaHom_of_ne t x a hxt q hat hax

/-! ## `theta` composed with the Magnus substitution is `rootHom` -/

theorem subst_of_eq (t x : α) (p q : ℤ) :
    Work.OROneRel.subst t x p q (FreeGroup.of t) = (FreeGroup.of t) ^ p := by
  rw [Work.OROneRel.subst, FreeGroup.lift_apply_of]
  simp [Work.OROneRel.substFun]

theorem subst_of_x {t x : α} (hxt : x ≠ t) (p q : ℤ) :
    Work.OROneRel.subst t x p q (FreeGroup.of x) = FreeGroup.of x * (FreeGroup.of t) ^ (-q) := by
  rw [Work.OROneRel.subst, FreeGroup.lift_apply_of]
  simp [Work.OROneRel.substFun, hxt]

theorem subst_of_ne {t x a : α} (hat : a ≠ t) (hax : a ≠ x) (p q : ℤ) :
    Work.OROneRel.subst t x p q (FreeGroup.of a) = FreeGroup.of a := by
  rw [Work.OROneRel.subst, FreeGroup.lift_apply_of]
  simp [Work.OROneRel.substFun, hat, hax]

/-- **The key identity of the Magnus substitution**: composing the isomorphism
`theta : F(α) ≃* P` with the substitution `ψ` gives the embedding `rootHom : F(α) →* P`.  In other
words `ψ r` and `r` are the same element of `P`, i.e. `theta (ψ r) = rootHom r`. -/
theorem theta_comp_subst {t x : α} (hxt : x ≠ t) (p q : ℤ) :
    (theta t x hxt q).toMonoidHom.comp (Work.OROneRel.subst t x p q) = rootHom t p := by
  apply FreeGroup.ext_hom
  intro a
  rw [MonoidHom.comp_apply]
  by_cases hat : a = t
  · rw [hat, subst_of_eq, map_zpow, theta_of_eq, rootHom_of_eq]
  · by_cases hax : a = x
    · rw [hax, subst_of_x hxt, map_mul, map_zpow, theta_of_x, theta_of_eq]
      rw [rootHom_of_ne hxt]
      group
    · rw [subst_of_ne hat hax, theta_of_ne t x a hxt q hat hax, rootHom_of_ne hat]

/-- **Injectivity of the embedding `rootHom`**: the copy of `F(α)` inside `P` is a free subgroup of
rank `α`, generated by `{z ^ p} ∪ {a : a ≠ t}`. -/
theorem rootHom_injective {t x : α} (hxt : x ≠ t) {p : ℤ} (hp : p ≠ 0) :
    Function.Injective (rootHom (α := α) t p) := by
  have h : rootHom (α := α) t p
      = (theta t x hxt 0).toMonoidHom.comp (Work.OROneRel.subst t x p 0) := by
    rw [theta_comp_subst hxt p 0]
  rw [h]
  exact (theta t x hxt 0).injective.comp (Work.OROneRel.wcp_subst_injective t x p 0 hxt hp)

end Setup

end Work.ORLocInd.CohenLyndon
