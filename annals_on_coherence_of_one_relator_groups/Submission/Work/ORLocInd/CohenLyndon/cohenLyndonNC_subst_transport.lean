/-
Copyright: subproject `ORLocInd` -- the Cohen--Lyndon basis theorem (node N4).

# Case 2 of the Cohen--Lyndon induction: the substitution step

Let `F = F(α)`, `r ∈ F` cyclically reduced and not a proper power, and let `t ≠ x` be letters of `r`
with `p := σ_x r ≠ 0` and `q := σ_t r ≠ 0`.  The Magnus substitution `ψ` is
`ψ(t) = t ^ p`, `ψ(x) = x * t ^ (-q)`, all other letters fixed; it is injective
(`Work.OROneRel.wcp_subst_injective`) and turns `r` into a relator with vanishing `t`-exponent sum:
`σ_t (ψ r) = p * q - q * p = 0`.

Karrass--Solitar's *substitution step* (Putnam, *One-relator groups*, Case 2 of Theorem 6.1) says
that the Cohen--Lyndon property of `ψ r` in `F(α)` implies that of `r`.  The proof is the one
carried out in `Submission/Work/ORLocInd/CohenLyndon/cohenLyndonNC_subst.lean`: it adjoins a `p`-th
root `z` of `t`, so that `F(α)` sits in the free group `P = ⟨F(α), z | z^p = t⟩` (which is free, by
`theta`, on `{z, x z^q} ∪ (α \ {t,x})`), and there `ψ r` and `r` become the same element
(`theta ∘ ψ = rootHom`).  Concretely the proof transports the hypothesis along the isomorphism
`theta`, applies Karrass--Solitar's descent (`CLDescent`, its hypothesis `hmal` supplied by
`Work.ORLocInd.CohenLyndon.rootHom_conj_mem_range`) to the malnormal copy `rootHom(F(α)) ≤ P` of
`F(α)`, and transports back.

This file is the same statement as `cohenLyndonNC_subst`, proved here from `CLDescent` so that the
induction depends on a single, self-contained module.
-/
import Mathlib
import Submission.Work.ORLocInd.CohenLyndon.NCForm
import Submission.Work.ORLocInd.CohenLyndon.CLDescent
import Submission.Work.ORLocInd.CohenLyndon.substDefs
import Submission.Work.ORLocInd.CohenLyndon.cohenLyndonNC_mulEquiv
import Submission.Work.ORLocInd.CohenLyndon.normalClosure_inf_zpowers_eq_bot
import Submission.Work.ORLocInd.CohenLyndon.rootHom_conj_mem_range

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedVariables false

universe u

namespace Work.ORLocInd.CohenLyndon

/-- **Case 2 of the Cohen--Lyndon induction: the substitution step.**  Let `r ∈ F(α)` be cyclically
reduced, not a proper power, with two distinct letters `t ≠ x` occurring in it whose exponent sums
are nonzero.  Then the Cohen--Lyndon property for the substituted relator
`ψ r = subst t x (σ_x r) (σ_t r) r` in `F(α)` implies the Cohen--Lyndon property for `r`. -/
theorem cohenLyndonNC_subst_transport {α : Type u} [DecidableEq α] {r : FreeGroup α} {t x : α}
    (htx : t ≠ x)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator r)
    (hpp : ¬ Work.OROneRel.IsProperPower r) (hr1 : r ≠ 1)
    (htl : t ∈ Work.OROneRel.relatorLetters r) (hxl : x ∈ Work.OROneRel.relatorLetters r)
    (hσt : Work.OROneRel.sigma t r ≠ 1) (hσx : Work.OROneRel.sigma x r ≠ 1)
    (h : Work.CohenLyndon.CohenLyndonNC
      (Work.OROneRel.subst t x (Work.OROneRel.sigma x r) (Work.OROneRel.sigma t r) r)) :
    Work.CohenLyndon.CohenLyndonNC r := by
  classical
  have hxt : x ≠ t := fun h' => htx h'.symm
  have hsigx : Work.OROneRel.sigma x r =
      Multiplicative.ofAdd (Multiplicative.toAdd (Work.OROneRel.sigma x r)) := by simp
  have hp : Multiplicative.toAdd (Work.OROneRel.sigma x r) ≠ 0 := by
    intro h0
    exact hσx (by rw [hsigx, h0]; rfl)
  -- **Step 1.**  Transport the hypothesis along the isomorphism `theta : F(α) ≃* P`.
  have h1 : Work.CohenLyndon.CohenLyndonNC
      (theta t x hxt (Multiplicative.toAdd (Work.OROneRel.sigma t r))
        (Work.OROneRel.subst t x (Work.OROneRel.sigma x r) (Work.OROneRel.sigma t r) r)) :=
    (cohenLyndonNC_mulEquiv (theta t x hxt (Multiplicative.toAdd (Work.OROneRel.sigma t r)))
      (Work.OROneRel.subst t x (Work.OROneRel.sigma x r) (Work.OROneRel.sigma t r) r)).mp h
  -- **Step 2.**  `theta (ψ r) = rootHom r`.
  have hkey : theta t x hxt (Multiplicative.toAdd (Work.OROneRel.sigma t r))
        (Work.OROneRel.subst t x (Work.OROneRel.sigma x r) (Work.OROneRel.sigma t r) r)
      = rootHom t (Multiplicative.toAdd (Work.OROneRel.sigma x r)) r :=
    DFunLike.congr_fun (theta_comp_subst hxt (Multiplicative.toAdd (Work.OROneRel.sigma x r))
      (Multiplicative.toAdd (Work.OROneRel.sigma t r))) r
  rw [hkey] at h1
  -- **Step 3.**  `rootHom r ≠ 1`.
  have hrne : rootHom (α := α) t (Multiplicative.toAdd (Work.OROneRel.sigma x r)) r ≠ 1 := by
    intro h0
    exact hr1 ((rootHom_injective (α := α) hxt hp) (by rw [h0, map_one]))
  -- **Step 4.**  The Freiheitssatz condition `⟪r⟫ ∩ ⟨t⟩ = 1` and the malnormality input.
  have hnd : Subgroup.normalClosure ({r} : Set (FreeGroup α)) ⊓
      Subgroup.zpowers (FreeGroup.of t) = ⊥ :=
    normalClosure_inf_zpowers_eq_bot htx hσx
  have hmal : ∀ g : FreeGroup (RootIdx α t),
      (∃ j : ℤ, j ≠ 0 ∧ (g * rootHom t (Multiplicative.toAdd (Work.OROneRel.sigma x r)) r
          * g⁻¹) ^ j ∈ (rootHom t (Multiplicative.toAdd (Work.OROneRel.sigma x r))).range) →
      g ∈ (rootHom t (Multiplicative.toAdd (Work.OROneRel.sigma x r))).range :=
    rootHom_conj_mem_range t x hxt (Multiplicative.toAdd (Work.OROneRel.sigma x r)) hp hr1 hnd
  -- **Step 5.**  Karrass--Solitar descent inside `P`.
  have hrne' : (⟨rootHom (α := α) t (Multiplicative.toAdd (Work.OROneRel.sigma x r)) r,
      ⟨r, rfl⟩⟩ : (rootHom (α := α) t
        (Multiplicative.toAdd (Work.OROneRel.sigma x r))).range) ≠ 1 := by
    intro h0
    exact hrne (Subtype.ext_iff.mp h0)
  have h5 : Work.CohenLyndon.CohenLyndonNC
      (⟨rootHom (α := α) t (Multiplicative.toAdd (Work.OROneRel.sigma x r)) r, ⟨r, rfl⟩⟩ :
        (rootHom (α := α) t (Multiplicative.toAdd (Work.OROneRel.sigma x r))).range) :=
    CLDescent hrne' h1 hmal
  -- **Step 6.**  Transport back along the isomorphism `F(α) ≃* (rootHom t p).range`.
  have h6 : Work.CohenLyndon.CohenLyndonNC
      ((MonoidHom.ofInjective (rootHom_injective (α := α) hxt hp)) r) := by
    rw [show (MonoidHom.ofInjective (rootHom_injective (α := α) hxt hp)) r
        = ⟨rootHom (α := α) t (Multiplicative.toAdd (Work.OROneRel.sigma x r)) r, ⟨r, rfl⟩⟩ from
      Subtype.ext (MonoidHom.ofInjective_apply _)]
    exact h5
  exact (cohenLyndonNC_mulEquiv (MonoidHom.ofInjective (rootHom_injective (α := α) hxt hp))
    r).mpr h6

end Work.ORLocInd.CohenLyndon
