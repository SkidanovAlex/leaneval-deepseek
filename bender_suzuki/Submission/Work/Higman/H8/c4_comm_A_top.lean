/-
Copyright (c) 2024. All rights reserved.

# The `C₄` setting: `⁅A,⊤⁆ = A²` (session 9)

In the `C₄` setting (`P` a Suzuki 2-group, `A ⊴ P` abelian `ξ`-invariant with `Ω₁(P) ≤ A`,
`⁅⊤,⊤⁆ = A`, every square of `P` in `A`, `A⁴ = 1`, `A² = Ω₁(P)`, `|A| = |Ω₁(P)|²`) the subgroup
`⁅A,⊤⁆` is `ξ`-invariant normal and `≤ A`, hence one of `⊥`, `A²`, `A`.

This file proves that the value is **never `A`**:

* `Work.Higman.not_isNilpotent_of_commutator_self` — if `A ⊴ G`, `⁅A,⊤⁆ = A` and `A ≠ ⊥`, then
  `G` is not nilpotent.  (The lower central series of `G` then satisfies `A ≤ γ_{n+1}(G)` for all
  `n`; nilpotency would force `γ_m(G) = ⊥` for some `m`.)
* Consequently, since a finite `2`-group is nilpotent and in the `C₄` setting
  `A ⊇ Ω₁(P) ≠ ⊥`, we get `⁅A,⊤⁆ ≠ A`, and the dichotomy leaves `⁅A,⊤⁆ = A²`.

The value `⁅A,⊤⁆ = A²` is what makes the squaring and commutator maps of `P/A` well defined:
`(xa)² = x²·a²·⁅a,x⁆` with `a² ∈ A²` and `⁅a,x⁆ ∈ ⁅A,⊤⁆ = A²`, and `⁅xa,y⁆ = ⁅x,y⁆·⁅a,y⁆` with
`⁅a,y⁆ ∈ A²`; and it makes `Erad := {x : ⁅x,⊤⁆ ≤ A²}` contain `A`.
-/

import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.OmegaAux
import Submission.Work.Higman.MSA.basic
import Submission.Work.Higman.HS.c4_hs_aux

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped commutatorElement

namespace Work.Higman

/-- **Nilpotency obstruction.**  If `A ⊴ G` satisfies `⁅A,⊤⁆ = A` and `A ≠ ⊥`, then `G` is not
nilpotent: otherwise `⊥ = γ_m(G) ≥ A` for some `m`.

This is the elementary fact that rules out the `C₄` value `⁅A,⊤⁆ = A`. -/
theorem not_isNilpotent_of_commutator_self {G : Type*} [Group G] {A : Subgroup G} [A.Normal]
    (h : ⁅A, (⊤ : Subgroup G)⁆ = A) (hne : A ≠ ⊥) : ¬ Group.IsNilpotent G := by
  intro hnil
  have hγ1 : A ≤ (⊤ : Subgroup G).lowerCentralSeries 1 := by
    rw [Subgroup.top_lowerCentralSeries_one, ← h]
    exact Subgroup.commutator_mono le_top le_top
  have hγ : ∀ n : ℕ, A ≤ (⊤ : Subgroup G).lowerCentralSeries (n + 1) := by
    intro n
    induction n with
    | zero => exact hγ1
    | succ n ih =>
        have h1 : A ≤ ⁅(⊤ : Subgroup G).lowerCentralSeries (n + 1), (⊤ : Subgroup G)⁆ := by
          rw [← h]
          exact Subgroup.commutator_mono ih le_rfl
        simpa [Subgroup.lowerCentralSeries_succ] using h1
  obtain ⟨n, hn⟩ := (Subgroup.nilpotent_iff_lowerCentralSeries).mp hnil
  have h0 : A ≤ (⊥ : Subgroup G) := by
    have h1 := hγ n
    rw [Subgroup.lowerCentralSeries_succ, hn, Subgroup.commutator_bot_left] at h1
    exact h1
  exact hne (le_bot_iff.mp h0)

/-- **The `C₄` setting: `⁅A,⊤⁆ = A²`.**

`P` a Suzuki 2-group, `A ⊴ P` abelian `ξ`-invariant with `Ω₁(P) ≤ A`, `⁅⊤,⊤⁆ = A`,
`A⁴ = 1`, `A² = Ω₁(P)`, and `A² ≤ ⁅A,⊤⁆` (e.g. because `⁅D,A⁆ = A²` for some `D`).  Then
`⁅A,⊤⁆ = A²`: it is `ξ`-invariant `≤ A`, hence `⊥`, `A²` or `A`; `⊥` is excluded by the
containment `A² ≤ ⁅A,⊤⁆` and `A` by the nilpotency obstruction
`Work.Higman.not_isNilpotent_of_commutator_self` (a finite `2`-group is nilpotent). -/
theorem comm_A_top_eq_powSub_two {P : Type} [Group P] [Finite P] (h : IsSuzuki2Grp P)
    {A : Subgroup P} (hAn : A.Normal)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hNA : omega1 P ≤ A)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hA4 : powSub A 4 = ⊥)
    (htop : powSub A 2 = omega1 P)
    (hA2le : powSub A 2 ≤ ⁅A, (⊤ : Subgroup P)⁆) :
    ⁅A, (⊤ : Subgroup P)⁆ = powSub A 2 := by
  haveI : A.Normal := hAn
  have hle : ⁅A, (⊤ : Subgroup P)⁆ ≤ A :=
    (Subgroup.commutator_mono le_top le_top).trans (le_of_eq hGs)
  have hinv : (⁅A, (⊤ : Subgroup P)⁆).map (h.xi : MulAut P).toMonoidHom
      = ⁅A, (⊤ : Subgroup P)⁆ := by
    rw [Subgroup.map_commutator, hAxi,
      Subgroup.map_top_of_surjective _ (h.xi : MulAut P).surjective]
  have hA2ne : powSub A 2 ≠ ⊥ := by
    intro hb
    have h1 : Nat.card ↥(omega1 P) = 1 := by rw [← htop, hb]; simp
    have h4 := h.omega1_card_ge_four
    omega
  rcases HS.xi_inv_sub_dichotomy h hAab hAxi htop hA4 hle hinv with hb | h2 | h3
  · exact absurd (le_bot_iff.mp (hb ▸ hA2le)) hA2ne
  · exact h2
  · exfalso
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine not_isNilpotent_of_commutator_self h3 ?_ (h.isPGroup.isNilpotent)
    intro hb
    exact hA2ne (le_bot_iff.mp ((hA2le.trans (le_of_eq h3)).trans (le_of_eq hb)))

end Work.Higman
