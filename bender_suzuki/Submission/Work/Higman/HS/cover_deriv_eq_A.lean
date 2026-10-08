/-
Copyright (c) 2024. All rights reserved.

# The two-step cover has derived subgroup `A` (`Work.Higman.HS.cover_deriv_eq_A`)

Let `P` be a Suzuki 2-group and suppose `A ≤ C ≤ M` are subgroups such that

* `A` is `ξ`-invariant abelian normal, `[P,P] = A`, `Ω₁(P) ≤ A`, all squares of `P` lie in `A`,
  `A⁴ = ⊥`, `A² = Ω₁(P)`, `|A| = |Ω₁(P)|²`, and `A` is maximal among the `ξ`-invariant abelian
  normal subgroups;
* `C` is a minimal `ξ`-invariant normal cover of `A`, with `C² ≤ A`, `[C,A] = A²` and
  `[C,C] = A²`;
* `M ≥ C` is any further `ξ`-invariant normal subgroup with `M ≠ C`.

Then `[M,M] = A`.

The proof.  `[M,M]` is normal and `ξ`-invariant with `A² = [C,C] ≤ [M,M] ≤ [P,P] = A`, so the
dichotomy `xi_inv_sub_dichotomy` gives `[M,M] = ⊥`, `[M,M] = A²` or `[M,M] = A`.  The first is
impossible because `A² = Ω₁(P) ≠ ⊥`.  If `[M,M] = A²` then also `[M,A] = A²` (squeezed between
`[C,A] = A²` and `[M,M] = A²`), so `powSub_eq_of_deriv_eq` gives `M² = A² = Ω₁(P)`; then
`M` satisfies the Chevalley–Warning hypotheses (`M² ≤ Ω₁(P)`, `[M,M] ≤ Ω₁(P)`), giving
`|M| ≤ |Ω₁(P)|³`, while the "`m = n` count" `card_quot_C_A_eq` gives `|C| = |Ω₁(P)|³`.  As
`C ≤ M` we get `|C| = |M|`, hence `M = C`, contradiction.  Therefore `[M,M] = A`.

The cardinality of `C` is the delegated fact `card_C_eq_omega1_cube` (from
`xi_pow_triv_quot_C_A` and `card_quot_C_A_eq`).
-/

import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.MSA.basic
import Submission.Work.Higman.H8.cw_cube_bound
import Submission.Work.Higman.HS.c4_hs_aux
import Submission.Work.Higman.HS.centralizer_eq_A_of_comm_C_A
import Submission.Work.Higman.HS.card_quot_C_A_eq
import Submission.Work.Higman.HS.powSub_eq_of_deriv_eq
import Submission.Work.Higman.HS.card_C_eq_omega1_cube

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.Higman.HS

open scoped commutatorElement

theorem cover_deriv_eq_A {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P)
    {A C M : Subgroup P} [hAn : A.Normal]
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hmax : ∀ B : Subgroup P, Work.Higman.IsXiAbelNormal h B → A ≤ B → B = A)
    (hNA : Work.Higman.omega1 P ≤ A) (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A) (hA4 : Work.Higman.powSub A 4 = ⊥)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    (hCn : C.Normal) (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hAC : A ≤ C) (hCA : A ≠ C)
    (hcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ C → D = A ∨ D = C)
    (hC2 : Work.Higman.powSub C 2 ≤ A) (hCAd : ⁅C, A⁆ = Work.Higman.powSub A 2)
    (hCd : ⁅C, C⁆ = Work.Higman.powSub A 2)
    (hMn : M.Normal) (hMinv : M.map (h.xi : MulAut P).toMonoidHom = M)
    (hCM : C ≤ M) (hCMne : C ≠ M)
    (hMcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      C ≤ D → D ≤ M → D = C ∨ D = M) :
    ⁅M, M⁆ = A := by
  classical
  -- `A² = Ω₁(P) ≠ ⊥`
  have hA2ne : Work.Higman.powSub A 2 ≠ ⊥ := by
    intro hb
    have h1 : Nat.card ↥(Work.Higman.omega1 P) = 1 := by rw [← htop, hb]; simp
    have h4 := h.omega1_card_ge_four
    omega
  -- `[M,M]` is normal `ξ`-invariant with `A² ≤ [M,M] ≤ A`
  have hMMleA : ⁅M, M⁆ ≤ A := (Subgroup.commutator_mono le_top le_top).trans (le_of_eq hGs)
  have hMMinv : (⁅M, M⁆).map (h.xi : MulAut P).toMonoidHom = ⁅M, M⁆ := by
    rw [Subgroup.map_commutator, hMinv]
  have hA2leMM : Work.Higman.powSub A 2 ≤ ⁅M, M⁆ := by
    calc Work.Higman.powSub A 2 = ⁅C, C⁆ := hCd.symm
      _ ≤ ⁅M, M⁆ := Subgroup.commutator_mono hCM hCM
  -- the dichotomy
  rcases Work.Higman.HS.xi_inv_sub_dichotomy h hAab hAxi htop hA4 hMMleA hMMinv with hb | hb | hb
  · -- `[M,M] = ⊥` is impossible
    exact absurd (le_bot_iff.mp (hA2leMM.trans (le_of_eq hb))) hA2ne
  · -- `[M,M] = A²` would force `M = C`
    exfalso
    -- `[M,A] = A²`
    have hMAd : ⁅M, A⁆ = Work.Higman.powSub A 2 := by
      apply le_antisymm
      · calc ⁅M, A⁆ ≤ ⁅M, M⁆ := Subgroup.commutator_mono le_rfl (hAC.trans hCM)
          _ = Work.Higman.powSub A 2 := hb
      · calc Work.Higman.powSub A 2 = ⁅C, A⁆ := hCAd.symm
          _ ≤ ⁅M, A⁆ := Subgroup.commutator_mono hCM le_rfl
    -- `M² ≤ A`
    have hM2leA : Work.Higman.powSub M 2 ≤ A := by
      rw [Work.Higman.powSub, Subgroup.closure_le]
      rintro y ⟨x, -, rfl⟩
      exact hsq x
    -- `M² = A² = Ω₁(P)`
    have hM2eq : Work.Higman.powSub M 2 = Work.Higman.powSub A 2 :=
      powSub_eq_of_deriv_eq h hAab hAxi htop hA4 hM2leA hMinv hb hMAd
    -- Chevalley–Warning upper bound `|M| ≤ |Ω₁(P)|³`
    have hω_le_M : Work.Higman.omega1 P ≤ M :=
      htop ▸ ((Work.Higman.powSub_le (by norm_num)).trans (hAC.trans hCM))
    have hM2leω : Work.Higman.powSub M 2 ≤ Work.Higman.omega1 P := by rw [hM2eq, htop]
    have hMd_leω : ⁅M, M⁆ ≤ Work.Higman.omega1 P := by rw [hb, ← htop]
    have hMcard : Nat.card ↥M ≤ (Nat.card ↥(Work.Higman.omega1 P)) ^ 3 :=
      Work.Higman.H8.card_le_cube_of_sq_le_omega1 h hω_le_M hM2leω hMd_leω
    -- and the exact count `|C| = |Ω₁(P)|³`
    have hCcard : Nat.card ↥C = (Nat.card ↥(Work.Higman.omega1 P)) ^ 3 :=
      card_C_eq_omega1_cube h hAxi hAab hNA hGs hsq hA4 htop hcard hCn hCinv hAC hCA hcover hC2 hCAd
    -- `C ≤ M` and `|C| = |M|` force `C = M`
    exact hCMne (Subgroup.eq_of_le_of_card_ge hCM (hMcard.trans (le_of_eq hCcard.symm)))
  · -- `[M,M] = A`
    exact hb

end Work.Higman.HS
