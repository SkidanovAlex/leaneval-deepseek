/-
Copyright (c) 2024. All rights reserved.

# Squares are central in a Suzuki 2-group of order `q ^ 3`

Higman, *Suzuki 2-groups*, Illinois J. Math. **7** (1963), 79--96, Theorem 1: in a Suzuki
2-group `P` one has `Ω₁(P) = Z(P) = Φ(P) = P'` and `P` has exponent `4`.  Consequently
`x ^ 2 ∈ Z(P)` for every `x : P`.

This file proves the *squaring is central* statement in the case that is needed by
`Work.Higman.type_B_C_D_classification` (Higman's Lemma 12, types `B`, `C`, `D`), namely when
the order of `P` equals `q ^ 3`, `q = |Z(P)|`.  Nothing in the file depends on Higman's
Lemma 8 in the `C₄` shape `[P,P] = A` with `A ^ 2 = Ω₁(P)` beyond the *axiom-clean*
`Work.Higman.H8.c4_exclusion`; in particular it does **not** use
`Work.Higman.no_square_derived` / `Work.Higman.NSM.redcase` (the workspace's open hard case),
and its import cone carries no `sorryAx`.

## The argument

Write `q = |Ω₁(P)|`.  By `Work.Higman.center_eq_omega1_new` (axiom-clean) `Z(P) = Ω₁(P)`, so
the hypothesis reads `|P| = q ^ 3`.  Higman's Lemma 9 (existential form
`Work.Higman.higman9_exists_new`, axiom-clean) produces a `ξ`-invariant abelian normal `A`
which is maximal with these properties, contains `Ω₁(P)` and `[P,P]` and the squares of all
elements, and satisfies `A ^ 4 = 1`.

Higman's Lemma 1 (`Work.Higman.homogeneous_structure`) writes `|A| = q ^ e` with `e ≤ 2`, and
the dichotomy of `Work.Higman.core` reduces everything to the case

`[P,P] = A`,  `A ^ 2 = Ω₁(P)`,  `|A| = q ^ 2`   (the `C₄` shape).

`Work.Higman.no_square_q3` below shows that this case is *impossible* under `|P| = q ^ 3`:

* `A ≠ A ^ 2` (they have `q ^ 2` and `q` elements) and `A ≠ ⊤` (`P` is not abelian), so there is
  a normal `ξ`-invariant `D` minimal with `A < D ≤ ⊤` (`Work.Higman.MSA.exists_minimal_covering`);
* `[D,D] ≤ [P,P] = A` is `ξ`-invariant, hence of the form `A ^ (2 ^ i)`
  (`Work.Higman.homogeneous_structure`);
* `i = 0`: `[D,D] = A`, and Higman's Lemma 8 in the `C₄` shape
  (`Work.Higman.H8.c4_exclusion`, axiom-clean) gives a contradiction;
* `i = 1`: `[D,D] = A ^ 2 = Ω₁(P)`.  Orbit counting for the `ξ`-invariant subgroup `D`
  (`Work.Higman.H8.xi_invariant_card_sub_one_dvd`) gives `2 ^ n - 1 ∣ |D| - 1`, where
  `q = 2 ^ n`; since `2 ^ (2n) = |A| < |D| ≤ |P| = 2 ^ (3n)` this forces `|D| = |P|`, i.e.
  `D = ⊤`, and then `A = [⊤,⊤] = [D,D] = A ^ 2` — a contradiction;
* `i ≥ 2`: `[D,D] ≤ A ^ 4 = ⊥`, so `D` is `ξ`-invariant abelian and normal, contradicting the
  maximality of `A`.

The hypothesis `|P| = q ^ 3` is used only in the case `i = 1`; this is exactly why the present
argument avoids the open case of the general `[P,P] ≤ Ω₁(P)` statement, where the bound
`|P| ≤ q ^ 3` is itself Higman's theorem.
-/

import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.homogeneous_structure
import Submission.Work.Higman.OmegaAux
import Submission.Work.Higman.higman9_exists_new
import Submission.Work.Higman.center_eq_omega1_new
import Submission.Work.Higman.H8.c4_exclusion
import Submission.Work.Higman.H8.c4_sq_a2_orbit
import Submission.Work.Higman.MSA.basic
import Submission.Work.Higman.Q3.pow_sub_one_dvd_pow_sub_one_iff

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped commutatorElement

namespace Work.Higman

variable {P : Type} [Group P] [Finite P]

/-! ## Class-two calculus -/

/-- If `[P,P] ≤ Ω₁(P)` in a Suzuki 2-group then every square is central: every commutator is a
central involution, so in class `2` we have `⁅x ^ 2, y⁆ = ⁅x, y⁆ ^ 2 = 1`. -/
theorem sq_mem_center_of_comm_le_omega1_q3 (h : IsSuzuki2Grp P)
    (hcomm : ⁅(⊤ : Subgroup P), ⊤⁆ ≤ omega1 P) (x : P) :
    x ^ 2 ∈ Subgroup.center P := by
  rw [Subgroup.mem_center_iff]
  intro y
  have hmem : ⁅x, y⁆ ∈ omega1 P :=
    hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y))
  have hcen : ⁅x, y⁆ ∈ Subgroup.center P := h.omega1_le_center hmem
  have hsq : ⁅x, y⁆ ^ 2 = 1 := h.mem_omega1.mp hmem
  have hc : Commute x ⁅x, y⁆ := Subgroup.mem_center_iff.mp hcen x
  have key : ⁅x ^ 2, y⁆ = 1 := by
    rw [← Commute.commutatorElement_pow_left hc 2, hsq]
  exact (commutatorElement_eq_one_iff_mul_comm (g₁ := x ^ 2) (g₂ := y)).mp key |>.symm

/-! ## The `C₄` shape is impossible when `|P| = |Z(P)| ^ 3` -/

/-- **The `C₄` shape cannot occur in a Suzuki 2-group of order `q ^ 3`.**

Let `A` be a `ξ`-invariant abelian normal subgroup of a Suzuki 2-group `P`, maximal with these
properties, with `Ω₁(P) ≤ A`, `[P,P] = A`, every square of `P` in `A`, `A ^ 4 = 1`,
`A ^ 2 = Ω₁(P)` and `|A| = |Ω₁(P)| ^ 2`.  If additionally `|P| = |Z(P)| ^ 3` (so that, by
`Work.Higman.center_eq_omega1_new`, `|P| = |Ω₁(P)| ^ 3`), then we reach a contradiction.

The extra cardinality hypothesis is what rules out the middle case `[D,D] = A ^ 2` of the
minimal cover `D` of `A` (see the discussion in the file header). -/
theorem no_square_q3 (h : IsSuzuki2Grp P)
    (hcardP : Nat.card P = Nat.card ↥(Subgroup.center P) ^ 3)
    {A : Subgroup P} (hA : IsXiAbelNormal h A)
    (hmax : ∀ B : Subgroup P, IsXiAbelNormal h B → A ≤ B → B = A)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (hA4 : powSub A 4 = ⊥)
    (htop : powSub A 2 = omega1 P)
    (hcardA : Nat.card ↥A = (Nat.card ↥(omega1 P)) ^ 2) :
    False := by
  classical
  have hZ : Subgroup.center P = omega1 P := center_eq_omega1_new h
  have hq4 : 4 ≤ Nat.card ↥(omega1 P) := h.omega1_card_ge_four
  -- `A ^ 2 ≠ ⊥` and `A ≠ A ^ 2`
  have hA2ne : powSub A 2 ≠ ⊥ := by
    intro hb
    have h1 : Nat.card ↥(omega1 P) = 1 := by rw [← htop, hb]; simp
    omega
  have hAne2 : A ≠ powSub A 2 := by
    intro heq
    have h1 : Nat.card ↥(powSub A 2) = Nat.card ↥A := by rw [← heq]
    rw [htop, hcardA] at h1
    nlinarith [hq4, h1]
  -- `A ≠ ⊤`
  have hAneTop : A ≠ ⊤ := by
    intro htop'
    obtain ⟨x, y, hxy⟩ := h.noncomm
    exact hxy (hA.abelian x (htop' ▸ Subgroup.mem_top x) y (htop' ▸ Subgroup.mem_top y))
  -- a normal `ξ`-invariant `D` minimal with `A < D`
  obtain ⟨D, hDn, hDinv, hAD, -, hDneA, hcover⟩ :=
    MSA.exists_minimal_covering h (M := ⊤) Subgroup.normal_top
      (Subgroup.map_top_of_surjective _ (h.xi : MulAut P).surjective) le_top hAneTop.symm
  -- `[D,D] ≤ A` and is `ξ`-invariant, hence of the form `A ^ (2 ^ i)`
  have hDdle : ⁅D, D⁆ ≤ A := by
    rw [← hGs]
    exact Subgroup.commutator_mono le_top le_top
  have hDdinv : (⁅D, D⁆ : Subgroup P).map (h.xi : MulAut P).toMonoidHom = ⁅D, D⁆ := by
    rw [Subgroup.map_commutator, hDinv]
  obtain ⟨e', -, -, -, hsub⟩ := homogeneous_structure h hA.abelian hA.map_eq
  obtain ⟨i, hi⟩ := hsub ⁅D, D⁆ hDdle hDdinv
  rcases Nat.eq_zero_or_pos i with hi0 | hipos
  · -- `i = 0`: `[D,D] = A`, Higman's Lemma 8 in the `C₄` shape
    have hDd : ⁅D, D⁆ = A := by rw [hi, hi0, pow_zero, powSub_one_eq]
    exact H8.c4_exclusion h hA hGs hsq hDn hDinv hAD hDneA hDd hcover htop hA2ne hAne2
  · rcases Nat.eq_or_lt_of_le hipos with hi1 | hi2
    · -- `i = 1`: `[D,D] = A ^ 2 = Ω₁(P)`, and orbit counting forces `D = ⊤`
      have hDd : ⁅D, D⁆ = omega1 P := by
        rw [hi, ← hi1, pow_one, htop]
      obtain ⟨m, hm⟩ := (h.isPGroup.to_subgroup D).exists_card_eq
      obtain ⟨n, hn⟩ := h.exists_card_omega1_eq_two_pow
      have hnpos : 0 < n := by
        have h4 : 4 ≤ 2 ^ n := by rw [← hn]; exact h.omega1_card_ge_four
        by_contra hcon
        have hn0 : n = 0 := Nat.eq_zero_of_not_pos hcon
        rw [hn0] at h4
        norm_num at h4
      have hdvd : 2 ^ n - 1 ∣ 2 ^ m - 1 := by
        have h1 := H8.xi_invariant_card_sub_one_dvd h hDinv
        rwa [hn, hm] at h1
      have hnm : n ∣ m :=
        (Q3.pow_sub_one_dvd_pow_sub_one_iff (x := 2) (m := n) (k := m)
          (by norm_num) hnpos).mp hdvd
      have hPcard : Nat.card P = 2 ^ (3 * n) := by
        rw [hcardP, hZ, hn, ← pow_mul]
        congr 1
        ring
      have hmle : m ≤ 3 * n := by
        have h3 : Nat.card ↥D ≤ Nat.card ↥(⊤ : Subgroup P) := Subgroup.card_le_of_le le_top
        rw [Subgroup.card_top] at h3
        rw [hm, hPcard] at h3
        exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h3
      have hmgt : 2 * n < m := by
        have h1 : Nat.card ↥A < Nat.card ↥D :=
          Subgroup.card_lt_of_lt (lt_of_le_of_ne hAD (Ne.symm hDneA))
        rw [hcardA, hn, hm] at h1
        have h2 : (2 : ℕ) ^ (n * 2) < 2 ^ m := by
          calc (2 : ℕ) ^ (n * 2) = (2 ^ n) ^ 2 := pow_mul 2 n 2
            _ < 2 ^ m := h1
        have h3 : (2 : ℕ) ^ (2 * n) < 2 ^ m := by rwa [Nat.mul_comm n 2] at h2
        exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h3
      have heq : m = 3 * n := by
        obtain ⟨c, hc⟩ := hnm
        have hle : c ≤ 3 := by
          have h' : n * c ≤ n * 3 := by
            calc n * c = m := hc.symm
              _ ≤ 3 * n := hmle
              _ = n * 3 := Nat.mul_comm 3 n
          exact Nat.le_of_mul_le_mul_left h' hnpos
        have hgt : 2 < c := by
          have h' : n * 2 < n * c := by
            calc n * 2 = 2 * n := Nat.mul_comm n 2
              _ < m := hmgt
              _ = n * c := hc
          exact Nat.lt_of_mul_lt_mul_left h'
        have hc3 : c = 3 := by omega
        rw [hc, hc3]
        exact Nat.mul_comm n 3
      have hDtop : D = ⊤ := by
        refine Subgroup.eq_top_of_card_eq (H := D) ?_
        rw [hm, heq, hPcard]
      have hAeq : A = omega1 P := by
        have h1 : ⁅(⊤ : Subgroup P), ⊤⁆ = omega1 P := by rw [← hDtop]; exact hDd
        rw [hGs] at h1
        exact h1
      exact hAne2 (by rw [htop, hAeq])
    · -- `i ≥ 2`: `[D,D] ≤ A ^ 4 = ⊥`, so `D` is abelian, against maximality of `A`
      have hdvd : 4 ∣ 2 ^ i := ⟨2 ^ (i - 2), by
        rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_add]
        congr 1
        omega⟩
      have hbot : ⁅D, D⁆ = ⊥ := by
        rw [hi]
        exact le_bot_iff.mp ((powSub_le_of_dvd hA.abelian hdvd).trans (le_of_eq hA4))
      have hDab : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := by
        intro x hx y hy
        exact commutatorElement_eq_one_iff_mul_comm.mp (by
          have hmem : ⁅x, y⁆ ∈ ⁅D, D⁆ := Subgroup.commutator_mem_commutator hx hy
          rw [hbot] at hmem
          simpa using hmem)
      exact hDneA (hmax D ⟨hDn, hDinv, hDab⟩ hAD)

/-! ## Assembly -/

/-- **Higman 1963.**  In a Suzuki 2-group `P` whose order equals `q ^ 3` with `q = |Z(P)|`,
the commutator subgroup lies in `Ω₁(P)`. -/
theorem comm_le_omega1_q3 (h : IsSuzuki2Grp P)
    (hcardP : Nat.card P = Nat.card ↥(Subgroup.center P) ^ 3) :
    ⁅(⊤ : Subgroup P), ⊤⁆ ≤ omega1 P := by
  obtain ⟨A, hA, hmax, hNA, hDA, hsq, hexp4⟩ := higman9_exists_new h
  have hA4 : powSub A 4 = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (mem_powSub_iff hA.abelian).mp hy
    simpa using hexp4 x hx
  obtain ⟨e, hexp, hcard, htop, hsub⟩ := homogeneous_structure h hA.abelian hA.map_eq
  exact core h hA.map_eq hA.abelian hNA hDA hsq hA4 hexp hcard htop hsub
    (fun hGs htop2 hcardA => no_square_q3 h hcardP hA hmax hGs hsq hA4 htop2 hcardA)

/-- **Higman 1963, Theorem 1, `|P| = q ^ 3` case.**  In a Suzuki 2-group `P` whose order equals
`q ^ 3`, `q = |Z(P)|`, every square is central: `x ^ 2 ∈ Z(P)`. -/
theorem sq_mem_center_of_card_eq_center_cube (h : IsSuzuki2Grp P)
    (hcardP : Nat.card P = Nat.card ↥(Subgroup.center P) ^ 3) :
    ∀ x : P, x ^ 2 ∈ Subgroup.center P :=
  fun x => sq_mem_center_of_comm_le_omega1_q3 h (comm_le_omega1_q3 h hcardP) x

end Work.Higman
