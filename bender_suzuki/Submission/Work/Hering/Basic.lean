import Mathlib
import ChallengeDeps

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Area `Hering`: groups acting doubly transitively on their involutions

This is the basic vocabulary layer of the area `Hering` for the Bender–Suzuki project
(Peterfalvi I, Chapter IV, Théorème E; C. Hering, *On finite groups operating doubly transitively
on their involutions*, Arch. Math. 22 (1971) 456–458).

The area's goal (`Submission.Blueprint.HeringProp`) is:

> a finite group `G` of even order acting doubly transitively by conjugation on its involutions
> has 2-rank one (contains no four-group).

The local copy of the definitions keeps this module's import footprint small
(`Mathlib` + `ChallengeDeps`); `Work.Hering.Main` imports the blueprint and converts.

## Conventions

* `involutions G` is the *set* of elements of order `2`.
* `DTInv G` is the double transitivity hypothesis, stated elementwise with the conjugation
  convention `x ↦ g * x * g⁻¹` used throughout the Bender–Suzuki blueprint.
* `HasFourGroup G` is `Submission.Blueprint.HasFourGroup` (2-rank `≥ 2`); `TwoRankOne` is its
  negation.
-/

set_option autoImplicit false

namespace Work.Hering

open LeanEval.GroupTheory.Defs

section Defs

variable {G : Type*} [Group G]

/-- The set of involutions of `G`. -/
def involutions (G : Type*) [Group G] : Set G := {x | orderOf x = 2}

/-- `G` acts **doubly transitively by conjugation on its involutions**: any two ordered pairs of
distinct involutions are conjugate. This is the hypothesis of Hering's theorem
(Peterfalvi I, Théorème E, p. 188). -/
def DTInv (G : Type*) [Group G] : Prop :=
  ∀ a b c d : G, orderOf a = 2 → orderOf b = 2 → orderOf c = 2 → orderOf d = 2 →
    a ≠ b → c ≠ d → ∃ g : G, g * a * g⁻¹ = c ∧ g * b * g⁻¹ = d

/-- `G` has 2-rank at least two, i.e. contains a four-group. This is
`Submission.Blueprint.HasFourGroup`, repeated here to keep this module's imports light. -/
def HasFourGroup (G : Type*) [Group G] : Prop :=
  ∃ a b : G, orderOf a = 2 ∧ orderOf b = 2 ∧ a ≠ b ∧ a * b = b * a

/-- Hering's conclusion: 2-rank one. -/
def TwoRankOne (G : Type*) [Group G] : Prop := ¬ HasFourGroup G

end Defs

section Involutions

variable {G : Type*} [Group G]

@[simp] theorem mem_involutions {x : G} : x ∈ involutions G ↔ orderOf x = 2 := Iff.rfl

theorem sq_eq_one_of_orderOf_eq_two {x : G} (hx : orderOf x = 2) : x * x = 1 := by
  have h : x ^ 2 = 1 := by rw [← orderOf_dvd_iff_pow_eq_one, hx]
  simpa [pow_two] using h

theorem orderOf_eq_two_of_sq_eq_one {x : G} (h : x * x = 1) (h1 : x ≠ 1) : orderOf x = 2 := by
  refine orderOf_eq_prime ?_ h1
  simpa [pow_two] using h

theorem ne_one_of_mem_involutions {x : G} (hx : x ∈ involutions G) : x ≠ 1 := by
  intro h; rw [mem_involutions, h] at hx; simp at hx

theorem involutions_inv_mem {x : G} (hx : x ∈ involutions G) : x⁻¹ ∈ involutions G := by
  rw [mem_involutions] at hx ⊢; rw [orderOf_inv, hx]

theorem eq_inv_of_mem_involutions {x : G} (hx : x ∈ involutions G) : x⁻¹ = x :=
  inv_eq_of_mul_eq_one_right (sq_eq_one_of_orderOf_eq_two hx)

theorem orderOf_conj (g x : G) : orderOf (g * x * g⁻¹) = orderOf x := by
  rw [← MulAut.conj_apply g x]
  exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x

theorem involutions_conj_mem {x : G} (hx : x ∈ involutions G) (g : G) :
    g * x * g⁻¹ ∈ involutions G := by
  rw [mem_involutions, orderOf_conj, hx]

theorem sq_comm_of_mem_involutions {x y : G} (hx : x ∈ involutions G) (hy : y ∈ involutions G)
    (hcomm : x * y = y * x) (hxy : x ≠ y) : x * y ∈ involutions G := by
  have hx2 : x * x = 1 := sq_eq_one_of_orderOf_eq_two hx
  have hy2 : y * y = 1 := sq_eq_one_of_orderOf_eq_two hy
  have hxy1 : x * y ≠ 1 := by
    intro h
    have hyinv : y⁻¹ = y := eq_inv_of_mem_involutions hy
    rw [← hyinv] at h
    exact hxy (mul_inv_eq_one.mp h)
  rw [mem_involutions]
  refine orderOf_eq_two_of_sq_eq_one ?_ hxy1
  calc x * y * (x * y) = x * (y * x) * y := by group
    _ = x * (x * y) * y := by rw [hcomm]
    _ = 1 := by simp [mul_assoc, hx2, hy2]

end Involutions

section DTInv

variable {G : Type*} [Group G]

/-- **Step 1 of Peterfalvi I §2** (p. 191): if `G` of 2-rank `≥ 2` acts doubly transitively on its
involutions, then its involutions commute pairwise. -/
theorem comm_of_dtinv (hDT : DTInv G) (h4 : HasFourGroup G) :
    ∀ a b : G, orderOf a = 2 → orderOf b = 2 → a * b = b * a := by
  intro a b ha hb
  by_cases hab : a = b
  · subst hab; rfl
  obtain ⟨x, y, hx, hy, hxy, hxymul⟩ := h4
  obtain ⟨g, hg1, hg2⟩ := hDT x y a b hx hy ha hb hxy hab
  rw [← hg1, ← hg2]
  calc g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by group
    _ = g * (y * x) * g⁻¹ := by rw [hxymul]
    _ = g * y * g⁻¹ * (g * x * g⁻¹) := by group

/-- Product of two distinct involutions is again an involution (Step 1, continued). -/
theorem mul_mem_involutions_of_dtinv (hDT : DTInv G) (h4 : HasFourGroup G) {x y : G}
    (hx : x ∈ involutions G) (hy : y ∈ involutions G) (hxy : x ≠ y) :
    x * y ∈ involutions G :=
  sq_comm_of_mem_involutions hx hy (comm_of_dtinv hDT h4 x y hx hy) hxy

/-- For a group with `DTInv` and 2-rank `≥ 2`, the product of two distinct involutions is a third
distinct involution. -/
theorem mul_ne_left_of_dtinv (hDT : DTInv G) (h4 : HasFourGroup G) {x y : G}
    (hx : x ∈ involutions G) (hy : y ∈ involutions G) (hxy : x ≠ y) : x * y ≠ x := by
  intro h
  have hy1 : y = 1 := by
    have h2 := congrArg (fun t => x⁻¹ * t) h
    simpa [← mul_assoc] using h2
  exact ne_one_of_mem_involutions hy hy1

end DTInv

end Work.Hering
