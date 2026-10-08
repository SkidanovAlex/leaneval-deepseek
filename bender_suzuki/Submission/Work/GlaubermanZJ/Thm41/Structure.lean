import Mathlib
import Submission.Work.GlaubermanZJ.Basic
import Submission.Work.PGroup.All
import Submission.Work.GlaubermanZJ.Thm41.PComm
import Submission.Work.GlaubermanZJ.Thm41.IterComm

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Glauberman (4.1) and elementary commutator facts for Theorem 4.1

This file contains

* `centerIn_le_centralizer`: `Z(S)` centralizes `S`;
* `commutator_inf_commutator_eq_bot`: Glauberman's (4.1) — `A ∩ B` centralizes `[B,A]` when
  `A ≤ S` is abelian, `B ≤ S` and `[B,B]` is central in `S`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped commutatorElement
open Subgroup

namespace Work.GlaubermanZJ

variable {G : Type*} [Group G]

/-- The centre `Z(H)` (as a subgroup of the ambient group) centralizes `H`. -/
theorem centerIn_le_centralizer (H : Subgroup G) :
    Work.PGroup.centerIn H ≤ Subgroup.centralizer (H : Set G) := by
  intro x hx
  rw [Work.PGroup.centerIn, Subgroup.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy ⟨z, hz⟩)

/-- The centralizer of a join is the intersection of the centralizers. -/
theorem centralizer_sup (H K : Subgroup G) :
    Subgroup.centralizer ((H ⊔ K : Subgroup G) : Set G) =
      Subgroup.centralizer (H : Set G) ⊓ Subgroup.centralizer (K : Set G) := by
  rw [Subgroup.sup_eq_closure, Subgroup.centralizer_closure]
  ext x
  constructor
  · intro hx
    exact ⟨fun y hy => hx y (Or.inl hy), fun y hy => hx y (Or.inr hy)⟩
  · rintro ⟨h1, h2⟩ y (hy | hy)
    · exact h1 y hy
    · exact h2 y hy

/-- **Glauberman (1968), (4.1).**  If `A ≤ S` is abelian, `B ≤ S` and `[B,B]` is central in `S`,
then `A ∩ B` centralizes `[B,A]`.

(Glauberman's hypothesis is `[B,B] ⊆ Z(J(S))` with `A ≤ J(S)`; `[B,B] ⊆ Z(S)` is the form
available after reducing to `S = A·B`.) -/
theorem commutator_inf_commutator_eq_bot {S A B : Subgroup G} (hAS : A ≤ S) (hBS : B ≤ S)
    (hAab : IsMulCommutative A) (hZ : ⁅B, B⁆ ≤ Work.PGroup.centerIn S) :
    ⁅A ⊓ B, ⁅B, A⁆⁆ = ⊥ := by
  have hcent : ⁅B, B⁆ ≤ Subgroup.centralizer (A : Set G) :=
    (hZ.trans (centerIn_le_centralizer S)).trans (Subgroup.centralizer_le hAS)
  -- `[B, A∩B, A] = 1`
  have h1 : ⁅⁅B, A ⊓ B⁆, A⁆ = ⊥ := by
    have hle : ⁅B, A ⊓ B⁆ ≤ ⁅B, B⁆ := Subgroup.commutator_mono le_rfl inf_le_right
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hle.trans hcent
  -- `[A∩B, A, B] = 1`
  have h2 : ⁅⁅A ⊓ B, A⁆, B⁆ = ⊥ := by
    have hb : ⁅A ⊓ B, A⁆ = ⊥ :=
      le_bot_iff.mp ((Subgroup.commutator_mono inf_le_left le_rfl).trans
        (le_of_eq (Subgroup.commutator_self_eq_bot_iff.mpr hAab)))
    rw [hb, Subgroup.commutator_bot_left]
  -- Three subgroups lemma
  have h3 : ⁅⁅A, B⁆, A ⊓ B⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := A) (H₂ := B) h1 h2
  rw [Subgroup.commutator_comm A B] at h3
  exact le_bot_iff.mp ((Subgroup.commutator_comm_le (A ⊓ B) ⁅B, A⁆).trans (le_of_eq h3))

end Work.GlaubermanZJ
