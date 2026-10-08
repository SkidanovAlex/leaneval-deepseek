/-
Copyright (c) 2024. All rights reserved.

# Higman (1963), Lemma 9, first part: `exp A | 4`

For a maximal `ξ`-invariant abelian normal subgroup `A` of a Suzuki 2-group, `powSub A 4 = ⊥`.

The argument (Higman §5, see `Submission/Work/Higman/MSA_NOTES.md` §3) uses a minimal covering
`C > A`: `Φ(C) ≤ A` and `A² ≤ Φ(C)`, so `Φ(C) ∈ {A², A}`, and:

* `Φ(C) = A²`: Higman's Lemma 3 gives `exp A | 4`;
* `Φ(C) = A`, `C' = A`: Higman's Lemma 8 gives `exp A | 2`;
* `Φ(C) = A`, `C' ⊆ A²`: Higman's Lemma 7 makes `C` abelian, contradicting maximality of `A`.
-/

import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.homogeneous_structure
import Submission.Work.Higman.A_quot_irreducible
import Submission.Work.Higman.equivariant_bihom_trivial
import Submission.Work.Higman.MSA.basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.Higman.MSA

open scoped commutatorElement

variable {P : Type} [Group P] [Finite P]

/-- `∀ a ∈ A, a ^ 4 = 1` for an abelian `A` is the same as `powSub A 4 = ⊥`. -/
theorem powSub_four_bot_of_pow_four_eq_one {A : Subgroup P}
    (hAb : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (h : ∀ a ∈ A, a ^ 4 = 1) :
    powSub A 4 = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro y hy
  obtain ⟨a, ha, rfl⟩ := (Work.Higman.mem_powSub_iff hAb).mp hy
  simpa using h a ha

/-- **Higman (1963), Lemma 9, first part.**  A maximal `ξ`-invariant abelian normal subgroup of a
Suzuki 2-group has exponent dividing `4`. -/
theorem powSub_four_bot_of_maximal (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hA : IsXiAbelNormal h A) (hmax : ∀ B : Subgroup P, IsXiAbelNormal h B → A ≤ B → B = A)
    (h3 : ∀ {A C : Subgroup P}, IsXiAbelNormal h A → C.Normal →
      C.map (h.xi : MulAut P).toMonoidHom = C → A ≤ C → A ≠ C →
      (∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
        A ≤ D → D ≤ C → D = A ∨ D = C) →
      powSub C 2 ⊔ ⁅C, C⁆ = powSub A 2 → ∀ a ∈ A, a ^ 4 = 1)
    (h7 : ∀ {A C : Subgroup P}, IsXiAbelNormal h A → C.Normal →
      C.map (h.xi : MulAut P).toMonoidHom = C → A ≤ C → A ≠ C →
      (∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
        A ≤ D → D ≤ C → D = A ∨ D = C) →
      powSub C 2 ⊔ ⁅C, C⁆ = A → ⁅C, C⁆ ≤ powSub A 2 →
      ∀ x ∈ C, ∀ y ∈ C, x * y = y * x)
    (h8 : ∀ {A C : Subgroup P}, IsXiAbelNormal h A → C.Normal →
      C.map (h.xi : MulAut P).toMonoidHom = C → A ≤ C → A ≠ C →
      (∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
        A ≤ D → D ≤ C → D = A ∨ D = C) →
      powSub C 2 ≤ A → ⁅C, C⁆ = A → ∀ a ∈ A, a * a = 1) :
    powSub A 4 = ⊥ := by
  -- `A ≠ ⊤` as `P` is non-abelian and `A` abelian
  have hAne : A ≠ ⊤ := by
    intro htop
    obtain ⟨x, y, hxy⟩ := h.noncomm
    exact hxy (hA.abelian x (htop ▸ Subgroup.mem_top x) y (htop ▸ Subgroup.mem_top y))
  obtain ⟨C, hCn, hCinv, hAC, -, hCA, hcover⟩ :=
    exists_minimal_covering h (A := A) (M := ⊤) Subgroup.normal_top
      (by rw [Subgroup.map_top_of_surjective _ (h.xi : MulAut P).surjective]) le_top hAne.symm
  have hACne : A ≠ C := hCA.symm
  have hPhi_le : powSub C 2 ⊔ ⁅C, C⁆ ≤ A :=
    phi_le_of_minimal_covering h hA.normal hA.map_eq hCn hCinv hAC hACne hcover
  have hPhi_inv : (powSub C 2 ⊔ ⁅C, C⁆).map (h.xi : MulAut P).toMonoidHom
      = powSub C 2 ⊔ ⁅C, C⁆ := by
    rw [Subgroup.map_sup, Work.Higman.map_powSub (h.xi : MulAut P) hCinv 2,
      Subgroup.map_commutator, hCinv]
  have hDich := xi_invariant_eq_powSub_two_or_self h hA hPhi_le
    ((powSub_mono hAC).trans le_sup_left) hPhi_inv
  rcases hDich with hPhi | hPhi
  · -- `Φ(C) = A²`: Higman's Lemma 3
    exact powSub_four_bot_of_pow_four_eq_one hA.abelian
      (h3 hA hCn hCinv hAC hACne hcover hPhi)
  · -- `Φ(C) = A`: `C'` is a `ξ`-invariant subgroup of `A`
    have hC2_le : powSub C 2 ≤ A := by rw [← hPhi]; exact le_sup_left
    have hCd_le : ⁅C, C⁆ ≤ A := by rw [← hPhi]; exact le_sup_right
    have hCd_inv : (⁅C, C⁆ : Subgroup P).map (h.xi : MulAut P).toMonoidHom = ⁅C, C⁆ := by
      rw [Subgroup.map_commutator, hCinv]
    obtain ⟨e, -, -, -, hstruct⟩ := homogeneous_structure h hA.abelian hA.map_eq
    obtain ⟨j, hj⟩ := hstruct ⁅C, C⁆ hCd_le hCd_inv
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · -- `C' = A`: Higman's Lemma 8 gives exponent `≤ 2`
      have hCd : ⁅C, C⁆ = A := by rw [hj, h0, pow_zero, powSub_one_eq]
      refine powSub_four_bot_of_pow_four_eq_one hA.abelian (fun a ha => ?_)
      have h2 : a * a = 1 := h8 hA hCn hCinv hAC hACne hcover hC2_le hCd a ha
      have h4 : a ^ 4 = (a * a) * (a * a) := by
        rw [show (4 : ℕ) = 2 + 2 from by norm_num, pow_add, pow_two]
      rw [h4, h2, one_mul]
    · -- `C' ⊆ A²`: Higman's Lemma 7 makes `C` abelian, contradicting maximality
      have hCd2 : ⁅C, C⁆ ≤ powSub A 2 := by
        rw [hj]
        exact powSub_le_of_dvd hA.abelian (Nat.pow_dvd_pow 2 hpos)
      have hcomm : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x :=
        h7 hA hCn hCinv hAC hACne hcover hPhi hCd2
      exact absurd (hmax C ⟨hCn, hCinv, hcomm⟩ hAC) hCA

end Work.Higman.MSA
