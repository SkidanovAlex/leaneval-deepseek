/-
Area A9, sub-area `Fpf`: fixed-point-free automorphisms of prime order.

`Fpf` provides the elementary proof that a finite **solvable** group with a fixed-point-free
automorphism of prime order is nilpotent (`isNilpotent_of_fpf_prime`, lemma F9), which is what area
A8b needs for the kernel of a Frobenius group (see `Submission/Work/NOTES_LEAD_ft_npc.md` §2).

The definitions and the restriction API live here; the lemmas F1–F8 are in the sibling files
`isFpf_mulInv_injective`, ..., and F9 is in `isNilpotent_of_fpf_prime`.
-/
import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NPC.Fpf

variable {K : Type*} [Group K]

/-- `α` is **fixed-point-free**: its only fixed point is `1`. -/
def IsFpf (α : MulAut K) : Prop := ∀ x : K, α x = x → x = 1

/-- The subgroup `H` is **`α`-invariant**. -/
def IsInv (α : MulAut K) (H : Subgroup K) : Prop := ∀ x : K, α x ∈ H ↔ x ∈ H

namespace IsInv

variable {α : MulAut K} {H : Subgroup K}

/-- An `α`-invariant subgroup is fixed by `Subgroup.map α`. -/
theorem map_eq (h : IsInv α H) : H.map α.toMonoidHom = H := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (h y).mpr hy
  · intro hx
    exact ⟨α.symm x, (h (α.symm x)).mp (by simpa using hx), by simp⟩

/-- Powers of an `α`-invariant subgroup are `α`-invariant. -/
theorem pow (h : IsInv α H) (i : ℕ) : IsInv (α ^ i) H := by
  induction i with
  | zero => intro x; simp
  | succ i ih =>
    intro x
    rw [pow_succ', MulAut.mul_apply]
    have h1 : α ((α ^ i) x) ∈ H ↔ (α ^ i) x ∈ H := h _
    have h2 : (α ^ i) x ∈ H ↔ x ∈ H := ih x
    exact h1.trans h2

/-- The restriction of an automorphism to an invariant subgroup, as an automorphism of `↥H`. -/
noncomputable def restrictEquiv (h : IsInv α H) : ↥H ≃* ↥H where
  toFun x := ⟨α x, (h x).mpr x.2⟩
  invFun x := ⟨α.symm x, (h (α.symm x)).mp (by simpa using x.2)⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp
  map_mul' x y := by ext; simp

@[simp]
theorem restrictEquiv_apply (h : IsInv α H) (x : ↥H) :
    ((h.restrictEquiv x : ↥H) : K) = α x := rfl

theorem restrictEquiv_pow_apply (h : IsInv α H) (i : ℕ) (x : ↥H) :
    (((h.restrictEquiv ^ i) x : ↥H) : K) = (α ^ i) x := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have h1 : ((h.restrictEquiv ^ (i + 1)) x : ↥H) =
        h.restrictEquiv ((h.restrictEquiv ^ i) x) := by
      rw [pow_succ', MulAut.mul_apply]
    rw [h1, IsInv.restrictEquiv_apply, ih, pow_succ', MulAut.mul_apply]

end IsInv

end Work.NPC.Fpf
