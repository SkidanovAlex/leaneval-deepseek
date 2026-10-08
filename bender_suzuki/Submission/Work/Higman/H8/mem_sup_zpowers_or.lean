/-
Copyright (c) 2024. All rights reserved.

# Element description of `D ⊔ ⟨x⟩` when `D` is normal and `x * x ∈ D`

Used by `Work.Higman.H8.false_of_sq_mem_and_comm_le`: with `D` normal and `x² ∈ D`, the
subgroup `D ⊔ ⟨x⟩ = ⟨D, x⟩` is the union `D ∪ D·x` (because `(D·x)² ⊆ D`, since
`(d x)(e x) = d·(x e x⁻¹)·x²`), so every element is in `D` or of the form `d * x`.
-/

import Mathlib
import Submission.Work.Higman.PowSub

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.style.longLine false

namespace Work.Higman.H8

variable {P : Type} [Group P] [Finite P]

/-- **Element description of `D ⊔ ⟨x⟩`.**  If `D` is normal and `x * x ∈ D`, then every element
of `D ⊔ ⟨x⟩` lies in `D` or equals `d * x` with `d ∈ D`. -/
theorem mem_sup_zpowers_or {D : Subgroup P} (hDn : D.Normal) {x : P} (hx2 : x * x ∈ D) :
    ∀ m ∈ (D ⊔ Subgroup.zpowers x : Subgroup P), m ∈ D ∨ ∃ d ∈ D, m = d * x := by
  classical
  haveI : D.Normal := hDn
  have hxx : x ^ 2 ∈ D := by rw [pow_two]; exact hx2
  -- the auxiliary subgroup `T = D ∪ D·x`
  let T : Subgroup P :=
    { carrier := {p : P | p ∈ D ∨ ∃ d ∈ D, p = d * x}
      mul_mem' := by
        rintro p q (hp | ⟨d, hd, rfl⟩) (hq | ⟨e, he, rfl⟩)
        · exact Or.inl (D.mul_mem hp hq)
        · exact Or.inr ⟨p * e, D.mul_mem hp he, by group⟩
        · refine Or.inr ⟨d * (x * q * x⁻¹), D.mul_mem hd (hDn.conj_mem q hq x), ?_⟩
          group
        · refine Or.inl ?_
          have hconj : x * e * x⁻¹ ∈ D := hDn.conj_mem e he x
          have hkey : (d * x) * (e * x) = d * (x * e * x⁻¹) * x ^ 2 := by group
          rw [hkey]
          exact D.mul_mem (D.mul_mem hd hconj) hxx
      one_mem' := Or.inl D.one_mem
      inv_mem' := by
        rintro p (hp | ⟨d, hd, rfl⟩)
        · exact Or.inl (D.inv_mem hp)
        · refine Or.inr ⟨(x ^ 2)⁻¹ * (x * d⁻¹ * x⁻¹), D.mul_mem (D.inv_mem hxx) ?_, ?_⟩
          · exact hDn.conj_mem d⁻¹ (D.inv_mem hd) x
          · have hxinv : x⁻¹ = (x ^ 2)⁻¹ * x := by
              calc x⁻¹ = ((x ^ 2)⁻¹ * (x ^ 2)) * x⁻¹ := by rw [inv_mul_cancel, one_mul]
                _ = (x ^ 2)⁻¹ * x := by group
            rw [show (d * x)⁻¹ = x⁻¹ * d⁻¹ by group, hxinv]
            group }
  have hle : (D ⊔ Subgroup.zpowers x : Subgroup P) ≤ T := by
    refine sup_le ?_ ?_
    · intro p hp; exact Or.inl hp
    · refine Subgroup.zpowers_le.mpr ?_
      exact Or.inr ⟨1, D.one_mem, by group⟩
  intro m hm
  exact hle hm

end Work.Higman.H8
