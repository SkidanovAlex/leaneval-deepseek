import Submission.Work.ZassenhausSuzuki.twoPoint_inverted

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The two-point stabiliser is abelian (Zassenhaus case)

`t` inverts the two-point stabiliser `D = twoPoint H t` (`twoPoint_inverted`, Suzuki Prop. 3).
Since `D` is `t`-invariant and `t² = 1`, inversion is an automorphism of `D`; a group whose
inversion map is an endomorphism is abelian.

This is the first step of the cyclicity of `D` (L2 of the lead's design note
`NOTES_LEAD_probe1630.md`): an *abelian* group acting fixed-point-freely on a group is cyclic
(`Work.Frobenius.Complement.isPGroup_abelian_fpf_isCyclic`,
`Work.Frobenius.Complement.abelian_fpf_representation_isCyclic`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausSuzuki

/-- **`D = twoPoint H t` is abelian.**  `t` inverts every element of `D`, and `t² = 1`, so
`t (x y) t = (t x t)(t y t)`, i.e. `(x y)⁻¹ = x⁻¹ y⁻¹`, i.e. `y x = x y`. -/
theorem twoPoint_comm {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : IsSplitRankOne H Q t) (hZ : IsZassenhaus H) (hQ : Q ≠ ⊥) (h2 : IsPGroup 2 Q) :
    ∀ x ∈ twoPoint H t, ∀ y ∈ twoPoint H t, x * y = y * x := by
  have ht2 : t * t = 1 := by
    rw [← pow_two]
    exact pow_orderOf_eq_one t ▸ (by rw [h.invol])
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  intro x hx y hy
  have hinvx := twoPoint_inverted h hZ hQ h2 x hx
  have hinvy := twoPoint_inverted h hZ hQ h2 y hy
  have hinvxy := twoPoint_inverted h hZ hQ h2 (x * y) ((twoPoint H t).mul_mem hx hy)
  rw [htinv] at hinvx hinvy hinvxy
  have key : (t * x * t) * (t * y * t) = t * (x * y) * t := by
    rw [show (t * x * t) * (t * y * t) = t * x * (t * t) * y * t from by group, ht2]
    group
  have h1 : x⁻¹ * y⁻¹ = (x * y)⁻¹ := by
    rw [← hinvxy, ← key, hinvx, hinvy]
  calc x * y = ((x * y)⁻¹)⁻¹ := (inv_inv _).symm
    _ = (x⁻¹ * y⁻¹)⁻¹ := by rw [h1.symm]
    _ = y * x := by rw [mul_inv_rev, inv_inv, inv_inv]

end Work.ZassenhausSuzuki
