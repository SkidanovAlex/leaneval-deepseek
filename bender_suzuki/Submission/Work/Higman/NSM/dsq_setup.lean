/-
Copyright (c) 2024. All rights reserved.

# The `C₄` deep configuration (`deepSquareCase`): setup and elementary facts

This module bundles the hypotheses of `Work.Higman.NSM.deepSquareCase_v2` (Higman's `C₄`
exclusion in the maximal setting, the last open obligation of the `Higman` area) into the
structure `Work.Higman.NSM.C4`, records the elementary consequences that are *already proved*
elsewhere in the workspace, and proves the new elementary fact

* `Work.Higman.NSM.C4.powSub_top_two_eq` — `P² = A` (the square subgroup of `P` is all of `A`),

together with the cardinality facts `|D| = |Ω₁(P)|³`, `D ≠ ⊤`, etc.

It is deliberately placed in its own module so that the two branch lemmas
(`Work.Higman.NSM.dsq_caseA`, `Work.Higman.NSM.dsq_caseB`) — which are the two halves of the
case split `[P,D] ≤ A²` / `¬[P,D] ≤ A²` of the main theorem — can import it without creating a
cycle.
-/

import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.OmegaAux
import Submission.Work.Higman.homogeneous_structure
import Submission.Work.Higman.higman_lemma8
import Submission.Work.Higman.MSA.lemma8_clean
import Submission.Work.Higman.MSA.basic
import Submission.Work.Higman.center_eq_omega1_new
import Submission.Work.Higman.higman9_exists_new
import Submission.Work.Higman.H8.cw_cube_bound
import Submission.Work.Higman.H8.false_of_sq_mem_and_comm_le
import Submission.Work.Higman.H8.c4_hard_core
import Submission.Work.Higman.H8.Erad_le_D
import Submission.Work.Higman.H8.c4_sq_a2_card_quot
import Submission.Work.Higman.H8.card_sub_one_dvd_xi
import Submission.Work.Higman.MSA.centralizer_eq_self
import Submission.Work.Higman.reducible_aux
import Submission.Work.Higman.RedAux.two_cover_stage
import Submission.Work.Higman.RedAux.c4_pairing
import Submission.Work.Higman.omega1_iso_field

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Higman.NSM

open scoped commutatorElement

variable {P : Type} [Group P] [Finite P]

/-- **The `C₄` deep configuration.**  This is exactly the hypothesis list of
`Work.Higman.NSM.deepSquareCase_v2`: `P` a Suzuki 2-group, `A` a maximal `ξ`-invariant abelian
normal subgroup with `[P,P] = A`, `A² = Ω₁(P)`, `A⁴ = 1`, `|A| = |Ω₁(P)|²`, and `D` a minimal
`ξ`-invariant normal subgroup with `A < D ≤ P`, `[D,D] = A²`. -/
structure C4 (h : Work.Higman.IsSuzuki2Grp P) (A D : Subgroup P) : Prop where
  ab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x
  inv : A.map (h.xi : MulAut P).toMonoidHom = A
  max : ∀ B : Subgroup P, B.Normal → B.map (h.xi : MulAut P).toMonoidHom = B →
      (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → A ≤ B → B = A
  NA : Work.Higman.omega1 P ≤ A
  Gs : ⁅(⊤ : Subgroup P), ⊤⁆ = A
  sq : ∀ x : P, x ^ 2 ∈ A
  A4 : Work.Higman.powSub A 4 = ⊥
  top : Work.Higman.powSub A 2 = Work.Higman.omega1 P
  card : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2
  An : A.Normal
  Dn : D.Normal
  Dinv : D.map (h.xi : MulAut P).toMonoidHom = D
  AD : A ≤ D
  ADne : D ≠ A
  Dd : ⁅D, D⁆ = Work.Higman.powSub A 2
  cover : ∀ E : Subgroup P, E.Normal → E.map (h.xi : MulAut P).toMonoidHom = E →
      A ≤ E → E ≤ D → E = A ∨ E = D

namespace C4

variable {h : Work.Higman.IsSuzuki2Grp P} {A D : Subgroup P}

theorem isXiAbelNormal (H : C4 h A D) : Work.Higman.IsXiAbelNormal h A :=
  ⟨H.An, H.inv, H.ab⟩

/-- In the `C₄` configuration the centralizer of `A` is `A`. -/
theorem centralizer_eq (H : C4 h A D) : Subgroup.centralizer (A : Set P) = A :=
  Work.Higman.RedAux.c4_centralizer h H.isXiAbelNormal H.NA H.Gs H.sq H.A4 H.top H.card

/-- In the `C₄` configuration, `⁅A,D⁆ = A²`. -/
theorem comm_A_D (H : C4 h A D) : ⁅A, D⁆ = Work.Higman.powSub A 2 :=
  Work.Higman.RedAux.c4_comm_A_D h H.isXiAbelNormal H.Dinv H.A4 H.AD (Ne.symm H.ADne) H.Dd
    H.top H.card H.centralizer_eq

/-- In the `C₄` configuration, `D² = A²`. -/
theorem powSub_D_two_eq (H : C4 h A D) : Work.Higman.powSub D 2 = Work.Higman.powSub A 2 :=
  Work.Higman.RedAux.c4_D_sq h H.isXiAbelNormal H.Dinv H.top H.A4 H.sq H.AD H.Dd
    H.centralizer_eq (Ne.symm H.ADne) H.card

/-- In the `C₄` configuration, `|D/A| = |Ω₁(P)|`. -/
theorem card_quot_eq (H : C4 h A D) :
    Nat.card (↥D ⧸ A.subgroupOf D) = Nat.card ↥(Work.Higman.omega1 P) :=
  Work.Higman.RedAux.c4_card_quot h H.isXiAbelNormal H.NA H.Gs H.sq H.A4 H.top H.card
    H.centralizer_eq H.Dn H.Dinv H.AD (Ne.symm H.ADne) H.Dd H.cover

/-- In the `C₄` configuration, `|D| = |Ω₁(P)|³`. -/
theorem card_D (H : C4 h A D) :
    Nat.card ↥D = (Nat.card ↥(Work.Higman.omega1 P)) ^ 3 := by
  have hsub : Nat.card ↥(A.subgroupOf D) = Nat.card ↥A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe H.AD)
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (A.subgroupOf D)
  rw [H.card_quot_eq, hsub, H.card] at h1
  rw [h1]; ring

/-- `A ≠ A²` in the `C₄` configuration. -/
theorem A_ne_powSub_two (H : C4 h A D) : A ≠ Work.Higman.powSub A 2 := by
  intro hEq
  have hcardeq : Nat.card ↥(Work.Higman.omega1 P) ^ 2
      = Nat.card ↥(Work.Higman.omega1 P) := by
    rw [← H.card, hEq, H.top]
  have h4 := h.omega1_card_ge_four
  have hpos : 0 < Nat.card ↥(Work.Higman.omega1 P) := Nat.card_pos
  nlinarith [hcardeq, h4, hpos]

/-- `D < ⊤` in the `C₄` configuration: `[D,D] = A² ≠ A = [P,P]`. -/
theorem D_ne_top (H : C4 h A D) : D ≠ ⊤ := by
  intro htop
  have h1 : ⁅(⊤ : Subgroup P), ⊤⁆ = Work.Higman.powSub A 2 := by
    rw [← htop]; exact H.Dd
  rw [H.Gs] at h1
  exact H.A_ne_powSub_two h1

/-- There is an element of `P` outside `D`. -/
theorem exists_notMem_D (H : C4 h A D) : ∃ x : P, x ∉ D := by
  by_contra hcon
  push_neg at hcon
  exact H.D_ne_top (le_antisymm le_top (fun x _ => hcon x))

/-- **`P² = A`** in the `C₄` configuration: the square subgroup of `P` is exactly `A`.

`P² ∈ {⊥, A², A}` (a `ξ`-invariant subgroup of `A`, using `homogeneous_structure` and `A⁴ = ⊥`).
`P² = ⊥` forces `P` to have exponent `2`, hence to be abelian; `P² = A²` forces `[P,P] ⊆ A²`
(the identity `(xy)² = ⁅y,x⁆ˣ · x² · y²` and normality of `A²`), and then `A = [P,P] = A²`. -/
theorem powSub_top_two_eq (H : C4 h A D) : Work.Higman.powSub (⊤ : Subgroup P) 2 = A := by
  have hSA : Work.Higman.powSub (⊤ : Subgroup P) 2 ≤ A := by
    rw [Work.Higman.powSub, Subgroup.closure_le]
    rintro y ⟨x, -, rfl⟩
    exact H.sq x
  have hSinv : (Work.Higman.powSub (⊤ : Subgroup P) 2).map (h.xi : MulAut P).toMonoidHom
      = Work.Higman.powSub (⊤ : Subgroup P) 2 := by
    have htop : (⊤ : Subgroup P).map (h.xi : MulAut P).toMonoidHom = ⊤ := by
      rw [Subgroup.map_top]
      exact MonoidHom.range_eq_top.mpr (h.xi : MulAut P).surjective
    exact Work.Higman.map_powSub (h.xi : MulAut P) htop 2
  obtain ⟨e, -, -, -, hsub⟩ := Work.Higman.homogeneous_structure h H.ab H.inv
  obtain ⟨i, hi⟩ := hsub _ hSA hSinv
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · rw [hi, h0, pow_zero, Work.Higman.powSub_one_eq]
  rcases lt_or_ge i 2 with hlt | hge
  · -- `S = A²`: then `[P,P] ⊆ A²` and `A = A²`
    exfalso
    have hi1 : i = 1 := by omega
    have hS : Work.Higman.powSub (⊤ : Subgroup P) 2 = Work.Higman.powSub A 2 := by
      rw [hi, hi1]; norm_num
    have hcomm_le : ⁅(⊤ : Subgroup P), ⊤⁆ ≤ Work.Higman.powSub A 2 := by
      rw [Subgroup.commutator_le]
      intro x _ y _
      have hA2z : Work.Higman.powSub A 2 ≤ Subgroup.center P := by
        rw [H.top]; exact h.omega1_le_center
      have hnorm : (Work.Higman.powSub A 2).Normal := Subgroup.normal_of_le_center hA2z
      have hmem : ∀ z : P, z ^ 2 ∈ Work.Higman.powSub A 2 := fun z => by
        rw [← hS]; exact Work.Higman.pow_mem_powSub (Subgroup.mem_top z)
      have hc : x⁻¹ * x⁻¹ ∈ Work.Higman.powSub A 2 := by
        have h2 : x⁻¹ * x⁻¹ = (x ^ 2)⁻¹ := by group
        rw [h2]; exact Subgroup.inv_mem _ (hmem x)
      have hyx : ⁅y, x⁆ ∈ Work.Higman.powSub A 2 := by
        have h1 : ⁅y, x⁆ = x⁻¹ * (x * y) ^ 2 * (y ^ 2)⁻¹ * x⁻¹ := by
          rw [commutatorElement_def]; simp only [pow_two]; group
        have hkey : x⁻¹ * (x * y) ^ 2 * (y ^ 2)⁻¹ * x⁻¹
            = (x⁻¹ * (x*y)^2 * x) * (x⁻¹ * (y^2)⁻¹ * x) * (x⁻¹ * x⁻¹) := by group
        rw [h1, hkey]
        refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) hc
        · simpa [inv_inv] using hnorm.conj_mem _ (hmem (x*y)) x⁻¹
        · simpa [inv_inv] using hnorm.conj_mem _ (Subgroup.inv_mem _ (hmem y)) x⁻¹
      rw [← commutatorElement_inv y x]
      exact Subgroup.inv_mem _ hyx
    have hAle : A ≤ Work.Higman.powSub A 2 := by
      calc A = ⁅(⊤ : Subgroup P), ⊤⁆ := H.Gs.symm
        _ ≤ Work.Higman.powSub A 2 := hcomm_le
    exact H.A_ne_powSub_two
      (le_antisymm hAle (Work.Higman.powSub_le (n := 2) (by norm_num)))
  · -- `S ≤ A⁴ = ⊥`: `P` has exponent `2`, hence is abelian
    exfalso
    have hbot : Work.Higman.powSub (⊤ : Subgroup P) 2 = ⊥ := by
      rw [hi]
      refine le_bot_iff.mp ?_
      have hdvd : 4 ∣ 2 ^ i := ⟨2 ^ (i - 2), by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega⟩
      exact le_trans (Work.Higman.powSub_le_of_dvd H.ab hdvd) (le_of_eq H.A4)
    obtain ⟨x, y, hxy⟩ := h.noncomm
    have hxA : x ∈ A := H.NA (h.mem_omega1.mpr (by
      have hh := Work.Higman.pow_mem_powSub (n := 2) (Subgroup.mem_top x)
      rw [hbot] at hh; simpa using Subgroup.mem_bot.mp hh))
    have hyA : y ∈ A := H.NA (h.mem_omega1.mpr (by
      have hh := Work.Higman.pow_mem_powSub (n := 2) (Subgroup.mem_top y)
      rw [hbot] at hh; simpa using Subgroup.mem_bot.mp hh))
    exact hxy (H.ab x hxA y hyA)

end C4

/-- **The `⁅P,D⁆ ≤ A²` branch of `deepSquareCase`.**  In this branch the configuration is
impossible: if `D` does not centralise `A`, `H8.false_of_comm_le_powSub_two` applies; if it does,
Gorenstein–Thompson (`H8.alt_pairing_false`) applied to the cover `D` of `A` applies. -/
theorem C4.caseA {h : Work.Higman.IsSuzuki2Grp P} {A D : Subgroup P}
    (H : C4 h A D) (hPD : ⁅(⊤ : Subgroup P), D⁆ ≤ Work.Higman.powSub A 2) : False := by
  have hC2 : Work.Higman.powSub D 2 ≤ A := by
    rw [H.powSub_D_two_eq]; exact Work.Higman.powSub_le (n := 2) (by norm_num)
  by_cases hnZ : ∀ e ∈ D, ∀ a ∈ A, e * a = a * e
  · refine Work.Higman.H8.alt_pairing_false h H.isXiAbelNormal H.Dn H.Dinv H.AD H.ADne
      H.cover hnZ hC2 H.Dd H.top.symm ?_ ?_
    · intro hbot
      rw [H.top] at hbot
      have h4 := h.omega1_card_ge_four
      rw [hbot] at h4
      simp at h4
    · intro a ha
      have hmem : a ^ 4 ∈ Work.Higman.powSub A 4 :=
        Work.Higman.pow_mem_powSub (n := 4) ha
      rw [H.A4] at hmem
      exact Subgroup.mem_bot.mp hmem
  · exact Work.Higman.H8.false_of_comm_le_powSub_two h H.isXiAbelNormal H.Gs H.sq H.A4 H.top
      H.Dd H.AD H.Dinv hnZ hPD

end Work.Higman.NSM
