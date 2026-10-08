import Mathlib
import Submission.Work.Higman.typeB

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV12.W_semireg_defs`

The few elementary definitions shared by the proof of `W_semireg` (Peterfalvi II, Ch. V §2):
the conjugation action of `N_G(Q)` on `Q`, and its basic properties.  This module is kept
minimal and stable so that the pieces of the `W_semireg` proof can be stated against it.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ThmF.ChV12

/-- Conjugation by an element of `N_G(Q)`, as an automorphism of `↥Q`. -/
noncomputable def conjAut {G : Type} [Group G] {Q : Subgroup G} (g : G)
    (hg : g ∈ Subgroup.normalizer (Q : Set G)) : MulAut ↥Q where
  toFun x := ⟨g * (x : G) * g⁻¹,
    (Subgroup.mem_normalizer_iff (H := Q) (g := g)).mp hg (x : G) |>.mp x.2⟩
  invFun x := ⟨g⁻¹ * (x : G) * g, by
    have h := (Subgroup.mem_normalizer_iff (H := Q) (g := g⁻¹)).mp
      ((Subgroup.normalizer (Q : Set G)).inv_mem hg) (x : G) |>.mp x.2
    simpa using h⟩
  left_inv x := by ext; group
  right_inv x := by ext; group
  map_mul' x y := by
    apply Subtype.ext
    show g * ((x : G) * (y : G)) * g⁻¹ = (g * (x : G) * g⁻¹) * (g * (y : G) * g⁻¹)
    group

theorem conjAut_coe {G : Type} [Group G] {Q : Subgroup G} (g : G)
    (hg : g ∈ Subgroup.normalizer (Q : Set G)) (x : ↥Q) :
    ((conjAut g hg x : ↥Q) : G) = g * (x : G) * g⁻¹ := rfl

theorem conjAut_pow_coe {G : Type} [Group G] {Q : Subgroup G} (g : G)
    (hg : g ∈ Subgroup.normalizer (Q : Set G)) (k : ℕ) (x : ↥Q) :
    (((conjAut g hg) ^ k) x : G) = g ^ k * (x : G) * (g ^ k)⁻¹ := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', MulAut.mul_apply, conjAut_coe, ih, pow_succ]
      group

theorem conjAut_eq_one_iff {G : Type} [Group G] {Q : Subgroup G} (g : G)
    (hg : g ∈ Subgroup.normalizer (Q : Set G)) :
    conjAut g hg = 1 ↔ ∀ x ∈ Q, g * x * g⁻¹ = x := by
  constructor
  · intro h x hx
    have h1 : (conjAut g hg) ⟨x, hx⟩ = ⟨x, hx⟩ := by
      have := congrArg (fun f : MulAut ↥Q => f ⟨x, hx⟩) h
      simpa using this
    have h2 := congrArg Subtype.val h1
    rw [conjAut_coe] at h2
    simpa using h2
  · intro h
    apply MulEquiv.ext
    intro x
    have hx : (conjAut g hg) x = x := Subtype.ext (by rw [conjAut_coe]; exact h x x.2)
    simpa using hx

end Work.ThmF.ChV12
