/-
Copyright (c) 2024. All rights reserved.

# Bender–Suzuki: the derived subgroup of a Suzuki 2-group lies in `Ω₁`

Higman, *Suzuki 2-groups*, Illinois J. Math. **7** (1963), 79--96, Theorem 1:
for a Suzuki 2-group `P` one has `P' = Z(P) = Φ(P) = Ω₁(P)`.

This file proves the `≤` direction `[P,P] ≤ Ω₁(P)`.

The route is Higman's:

* a maximal `ξ`-invariant abelian normal subgroup `A` is provided by
  `exists_maximal_isXiAbelNormal`; Higman's Lemma 9 gives `Ω₁(P) ≤ A`, `Φ(P) ≤ A` and
  `exp A ≤ 4` (the exponent bound via `higman9_exp_four_max`, i.e. Higman's Lemmas 3, 7, 8,
  and `Φ(P) ≤ A` via `MSA.phi_le_of_maximal`);
* Higman's Lemma 1 (`homogeneous_structure`) writes the exponent of `A` as `2 ^ e`, gives
  `|A ^ (2 ^ i)| = |A ⊓ Ω₁| ^ (e - i)`, `A ^ (2 ^ (e - 1)) = A ⊓ Ω₁ = Ω₁`, and shows that every
  `ξ`-invariant subgroup of `A` is a power subgroup `A ^ (2 ^ i)`;
* from `powSub A 4 = ⊥` we get `e ≤ 2`; from `Ω₁ ≤ [P,P] = A ^ (2 ^ s)` we get `s ≤ e - 1`;
* `e = 1` gives `A = Ω₁` and hence `[P,P] ≤ A = Ω₁`;
* `e = 2` gives `A² = Ω₁` and `s ∈ {0,1}`; `s = 1` gives `[P,P] = A² = Ω₁` while `s = 0`
  (i.e. `[P,P] = A` of exponent `4`) is excluded by Higman's Lemma 8 (`no_square_of_maximal`).
-/

import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.higman_lemma1
import Submission.Work.Higman.homogeneous_structure
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.A_quot_irreducible
import Submission.Work.Higman.suzuki_unipotence
import Submission.Work.Higman.MSA.basic
import Submission.Work.Higman.MSA.phi_le_of_maximal
import Submission.Work.Higman.higman_lemma3_aux
import Submission.Work.Higman.clo_lemma7
import Submission.Work.Higman.higman_lemma8
import Submission.Work.Higman.no_square_of_maximal

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.Higman

open scoped commutatorElement

/-! ## A minimal `ξ`-invariant normal subgroup over a maximal abelian `ξ`-subgroup -/

/-- **A minimal `ξ`-invariant normal subgroup over `A`.**  Given a `ξ`-invariant normal subgroup
`M ⊋ A`, there is a `ξ`-invariant normal subgroup `C` with `A < C ≤ M`, minimal with these
properties; in particular `C/A` is a minimal normal `ξ`-section. -/
theorem exists_minimal_xiNormal_cover {P : Type} [Group P] [Finite P]
    (h : IsSuzuki2Grp P) {A M : Subgroup P}
    (hMn : M.Normal) (hMinv : M.map (h.xi : MulAut P).toMonoidHom = M)
    (hAM : A ≤ M) (hMA : M ≠ A) :
    ∃ C : Subgroup P, C.Normal ∧ C.map (h.xi : MulAut P).toMonoidHom = C ∧
      A ≤ C ∧ C ≤ M ∧ C ≠ A ∧
      (∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
        A ≤ D → D ≤ C → D = A ∨ D = C) := by
  classical
  set S : Set (Subgroup P) := {D | D.Normal ∧ D.map (h.xi : MulAut P).toMonoidHom = D ∧
    A ≤ D ∧ D ≤ M ∧ D ≠ A} with hS
  have hSne : S.Nonempty := ⟨M, hMn, hMinv, hAM, le_rfl, hMA⟩
  have hSfin : S.Finite := Set.finite_univ.subset (fun _ _ => trivial)
  obtain ⟨C, hCs, hCmin⟩ := hSfin.exists_minimal hSne
  obtain ⟨hCn, hCinv, hAC, hCM, hCA⟩ := hCs
  refine ⟨C, hCn, hCinv, hAC, hCM, hCA, ?_⟩
  intro D hDn hDinv hAD hDC
  rcases eq_or_ne D A with rfl | hDA
  · exact Or.inl rfl
  · right
    have hDS : D ∈ S := ⟨hDn, hDinv, hAD, hDC.trans hCM, hDA⟩
    exact le_antisymm hDC (hCmin hDS hDC)

/-! ## Higman's Lemma 9, first part: the exponent of a maximal `ξ`-abelian normal subgroup -/

/-- **Higman 1963, Lemma 9, first part.**  A maximal `ξ`-invariant abelian normal subgroup `A` of
a Suzuki 2-group `P` has exponent at most `4`.

Proof (Higman, p. 87).  Choose a normal `ξ`-invariant `C > A` minimal with these properties;
then `C/A` is a minimal normal `ξ`-section and `Φ(C) = C ^ (2) · [C,C] ≤ A`, while
`A ^ (2) = Φ(A) ≤ Φ(C)`, so `Φ(C) ∈ {A ^ (2), A}`.  If `Φ(C) = A ^ (2)`, Higman's Lemma 3
(`higman_lemma3_aux`) gives `exp A ∣ 4`.  If `Φ(C) = A`, then `C'` is a `ξ`-invariant subgroup of
`A`, hence `C' = A ^ (2 ^ j)`: `j = 0` means `C' = A` and Higman's Lemma 8 (`higman_lemma8`)
gives `exp A ∣ 2`, while `j ≥ 1` means `C' ≤ A²` and Higman's Lemma 7 (`clo_lemma7`) makes `C`
abelian, contradicting the maximality of `A`. -/
theorem exp_le_four_of_maximal_aux {P : Type} [Group P] [Finite P]
    (h : IsSuzuki2Grp P) {A : Subgroup P} (hA : IsXiAbelNormal h A)
    (hmax : ∀ B : Subgroup P, IsXiAbelNormal h B → A ≤ B → B = A) :
    ∀ a ∈ A, a ^ 4 = 1 := by
  classical
  -- `A` is a proper subgroup: if `A = ⊤` then `P` would be abelian, contradicting `h.noncomm`.
  have hAne : A ≠ ⊤ := by
    intro htop
    obtain ⟨x, y, hxy⟩ := h.noncomm
    exact hxy (hA.abelian x (htop ▸ Subgroup.mem_top x) y (htop ▸ Subgroup.mem_top y))
  -- a normal `ξ`-invariant subgroup `C > A`, minimal with these properties.
  obtain ⟨C, hCn, hCinv, hAC, -, hCA, hcover⟩ :=
    MSA.exists_minimal_covering h (M := ⊤) Subgroup.normal_top
      (by rw [Subgroup.map_top_of_surjective _ (h.xi : MulAut P).surjective]) le_top hAne.symm
  -- the Frattini subgroup of the cover lies in `A`
  have hPhi_le : powSub C 2 ⊔ ⁅C, C⁆ ≤ A :=
    MSA.phi_le_of_minimal_covering h hA.normal hA.map_eq hCn hCinv hAC (Ne.symm hCA) hcover
  -- `A ^ (2) = Φ(A) ≤ Φ(C)`
  have hA2le : powSub A 2 ≤ powSub C 2 ⊔ ⁅C, C⁆ :=
    (powSub_mono (n := 2) hAC).trans le_sup_left
  -- `Φ(C)` is `ξ`-invariant
  have hPhi_inv : (powSub C 2 ⊔ ⁅C, C⁆).map (h.xi : MulAut P).toMonoidHom
      = powSub C 2 ⊔ ⁅C, C⁆ := by
    rw [Subgroup.map_sup, map_powSub (h.xi : MulAut P) hCinv 2, Subgroup.map_commutator, hCinv]
  rcases xi_invariant_eq_powSub_two_or_self h hA hPhi_le hA2le hPhi_inv with hPhi | hPhi
  · -- `Φ(C) = A ^ (2)`: Higman's Lemma 3
    exact higman_lemma3_aux h hA hCn hCinv hAC (Ne.symm hCA) hcover hPhi
  · -- `Φ(C) = A`
    have hC2 : powSub C 2 ≤ A := le_sup_left.trans (le_of_eq hPhi)
    have hCd_le : ⁅C, C⁆ ≤ A := le_sup_right.trans (le_of_eq hPhi)
    have hCd_inv : (⁅C, C⁆ : Subgroup P).map (h.xi : MulAut P).toMonoidHom = ⁅C, C⁆ := by
      rw [Subgroup.map_commutator, hCinv]
    obtain ⟨e, -, -, -, hsub⟩ := homogeneous_structure h hA.abelian hA.map_eq
    obtain ⟨j, hj⟩ := hsub ⁅C, C⁆ hCd_le hCd_inv
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · -- `C' = A`: Higman's Lemma 8 gives `exp A ∣ 2`
      have hCd_eq : ⁅C, C⁆ = A := by
        rw [hj, h0, pow_zero, powSub_one_eq]
      intro a ha
      have h2 : a * a = 1 :=
        higman_lemma8 h hA hCn hCinv hAC (Ne.symm hCA) hcover hC2 hCd_eq a ha
      have h2' : a ^ 2 = 1 := by rw [pow_two]; exact h2
      show a ^ 4 = 1
      rw [show (4 : ℕ) = 2 * 2 from by norm_num, pow_mul, h2', one_pow]
    · -- `C' ≤ A ^ (2)`: Higman's Lemma 7 makes `C` abelian, contradicting maximality
      have hCd2 : ⁅C, C⁆ ≤ powSub A 2 := by
        rw [hj]
        exact powSub_le_of_dvd hA.abelian (Nat.pow_dvd_pow 2 hpos)
      have hcomm : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x :=
        clo_lemma7 h hA hCn hCinv hAC (Ne.symm hCA) hcover hPhi hCd2
      exact absurd (hmax C ⟨hCn, hCinv, hcomm⟩ hAC) hCA

/-! ## The main theorem -/

/-- In a Suzuki 2-group `P` the commutator subgroup lies in `Ω₁(P)`: `[P,P] ≤ Ω₁(P)`
(Higman 1963, Theorem 1: `G' = Z(G) = Ω₁(G)`). -/
theorem commutator_le_omega1_aux {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P) : commutator P ≤ Work.Higman.omega1 P := by
  -- a maximal `ξ`-invariant abelian normal subgroup
  obtain ⟨A, hA, hAmax⟩ := exists_maximal_isXiAbelNormal h
  have hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := hA.abelian
  have hAxi : A.map (h.xi : MulAut P).toMonoidHom = A := hA.map_eq
  have hAn : A.Normal := hA.normal
  have hNA : omega1 P ≤ A := omega1_le_of_maximal h hA hAmax
  -- Higman's Lemma 9 (first part): `exp A ≤ 4`, hence `A ^ 4 = 1`
  have hexp4 : ∀ a ∈ A, a ^ 4 = 1 := exp_le_four_of_maximal_aux h hA hAmax
  have hA4 : powSub A 4 = ⊥ := by
    rw [eq_bot_iff, powSub, Subgroup.closure_le]
    rintro y ⟨x, hx, rfl⟩
    exact Subgroup.mem_bot.mpr (hexp4 x hx)
  -- Higman's Lemma 9 (second part): `Φ(P) ≤ A`, i.e. `P ^ 2 ≤ A` and `[P,P] ≤ A`
  have hPhi : powSub (⊤ : Subgroup P) 2 ⊔ ⁅(⊤ : Subgroup P), ⊤⁆ ≤ A :=
    MSA.phi_le_of_maximal h hA hAmax hA4
  have hDA : ⁅(⊤ : Subgroup P), ⊤⁆ ≤ A := le_trans le_sup_right hPhi
  have hsq : ∀ x : P, x ^ 2 ∈ A := fun x =>
    hPhi (Subgroup.mem_sup_left (pow_mem_powSub (n := 2) (Subgroup.mem_top x)))
  obtain ⟨e, hexp, hcard, htop, hsub⟩ := homogeneous_structure h hAab hAxi
  -- `Ω₁(P) = A ^ (2 ^ (e - 1))`
  have hOmeq : powSub A (2 ^ (e - 1)) = omega1 P := by
    rw [htop, inf_eq_right.mpr hNA]
  -- `e ≥ 1`
  have he1 : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h0 | hpos
    · exfalso
      have hA0 : A = ⊥ := by
        rw [Subgroup.eq_bot_iff_forall]
        intro x hx
        have h1 := hexp x hx
        rw [h0] at h1
        simpa using h1
      have hsub0 : omega1 P ≤ (⊥ : Subgroup P) := hA0 ▸ hNA
      have hcard1 : Nat.card ↥(omega1 P) = 1 := by
        rw [le_bot_iff.mp hsub0]
        simp
      have := h.omega1_card_ge_four
      omega
    · exact hpos
  -- `e ≤ 2`, because `A ^ 4 = 1` while `|A ^ 4| = |Ω₁| ^ (e - 2)` when `e ≥ 2`
  have he2 : e ≤ 2 := by
    rcases Nat.lt_or_ge e 2 with hlt | hge
    · omega
    · have hc := hcard 2 hge
      rw [show (2 : ℕ) ^ 2 = 4 by norm_num, hA4, inf_eq_right.mpr hNA,
        Subgroup.card_bot] at hc
      have hq1 : Nat.card ↥(omega1 P) ≠ 1 := by
        have := h.omega1_card_ge_four
        omega
      have hz : e - 2 = 0 := (Nat.pow_eq_one.mp hc.symm).resolve_left hq1
      omega
  -- `[P,P]` is a `ξ`-invariant subgroup of `A`, hence a power subgroup `A ^ (2 ^ s)`
  have hDxi : (⁅(⊤ : Subgroup P), ⊤⁆ : Subgroup P).map (h.xi : MulAut P).toMonoidHom
      = ⁅(⊤ : Subgroup P), ⊤⁆ := by
    rw [Subgroup.map_commutator,
      Subgroup.map_top_of_surjective ((h.xi : MulAut P).toMonoidHom)
        (h.xi : MulAut P).surjective]
  obtain ⟨s, hs⟩ := hsub ⁅(⊤ : Subgroup P), ⊤⁆ hDA hDxi
  -- `Ω₁(P) ≤ [P,P] = A ^ (2 ^ s)` forces `s ≤ e - 1`
  have hsle : s ≤ e - 1 := by
    by_contra hcon
    -- then `e ≤ s`, and `A ^ (2 ^ s) ≤ A ^ (2 ^ e) = 1`, so `Ω₁(P) ≤ [P,P] = 1`
    have hge : e ≤ s := by omega
    have hOmega_bot : omega1 P ≤ (⊥ : Subgroup P) := by
      refine (omega1_le_commutator h).trans ?_
      rw [hs]
      exact (powSub_le_of_dvd hAab (Nat.pow_dvd_pow 2 hge)).trans
        (le_of_eq (powSub_eq_bot_of_exp hAab le_rfl hexp))
    have hcard1 : Nat.card ↥(omega1 P) = 1 := by
      rw [le_bot_iff.mp hOmega_bot]
      simp
    have := h.omega1_card_ge_four
    omega
  rcases (show e = 1 ∨ e = 2 by omega) with he | he
  · -- `e = 1`: `A = Ω₁` and `[P,P] ≤ A`
    have hAeq : A = omega1 P := by
      rw [he] at hOmeq
      rw [show (2 : ℕ) ^ (1 - 1) = 1 by norm_num, powSub_one_eq] at hOmeq
      exact hOmeq
    rw [commutator_def, hs, ← hAeq]
    exact powSub_le (pow_pos (by norm_num) s)
  · -- `e = 2`: `A² = Ω₁`, and `s ∈ {0,1}`
    have htop2 : powSub A 2 = omega1 P := by
      rw [he] at hOmeq
      simpa using hOmeq
    rcases Nat.eq_zero_or_pos s with hs0 | hspos
    · -- `s = 0`, so `[P,P] = A` has exponent `4`: excluded by Higman's Lemma 8
      exfalso
      have hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A := by
        rw [hs, hs0, show (2 : ℕ) ^ 0 = 1 by norm_num, powSub_one_eq]
      have hcardA : Nat.card ↥A = (Nat.card ↥(omega1 P)) ^ 2 := by
        have hc0 := hcard 0 (Nat.zero_le e)
        rw [show (2 : ℕ) ^ 0 = 1 by norm_num, powSub_one_eq, inf_eq_right.mpr hNA] at hc0
        rw [he] at hc0
        simpa using hc0
      exact no_square_of_maximal h hA hAmax hNA hGs hsq hA4 htop2 hcardA
    · -- `s = 1`, so `[P,P] = A² = Ω₁`
      have hs1 : s = 1 := by omega
      rw [commutator_def, hs, hs1, show (2 : ℕ) ^ 1 = 2 by norm_num, htop2]

end Work.Higman
