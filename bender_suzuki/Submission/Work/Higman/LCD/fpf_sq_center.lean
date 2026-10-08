/-
# Squares are central in a Suzuki 2-group with a fixed-point-free `ξ`

The `FpfXi` setting (`|P| = q ^ 3`, `q = |Z(P)|`, `ξ` of order `q - 1` acting fixed-point-freely
on `P ∖ {1}`) makes Higman's Theorem 1 (`x ^ 2 ∈ Z(P)` for all `x`) *much* cheaper than in the
general setting, and this is the point of the present file.

The reason is that in this setting every `ξ`-invariant subgroup `H ≤ P` has `q - 1 ∣ |H| - 1`
(`Work.Higman.card_sub_one_dvd_of_xi_invariant`), so with `q = 2 ^ n` its order is a power `2 ^ m`
with `n ∣ m`; combined with `|P| = q ^ 3` this pins every intermediate subgroup down to
`1, q, q ^ 2, q ^ 3`.  In particular, with

* `A` a maximal `ξ`-invariant abelian normal subgroup (`exists_maximal_isXiAbelNormal`),
* `homogeneous_structure` writing `|A| = |A ⊓ Ω₁(P)| ^ e = q ^ e` with `exp A = 2 ^ e`,

the case analysis collapses: `e ≤ 2` (as `A ≠ ⊤`), `Φ(P) ≤ A` (`MSA.phi_le_of_maximal`), and
then

* if `e = 1` (so `A = Ω₁(P) = Z(P)`) or if `P' = A² = Ω₁(P) = Z(P)`, the commutator subgroup is
  central *and* of exponent two, so `[x², y] = [x,y]² = 1`;
* if `P' = A` — the `C₄` shape — then `A` is covered by `C = ⊤` with `C' = A` and `C² ≤ A`, and
  the *covering hypothesis* of Higman's Lemma 8 is automatic here: any normal `ξ`-invariant `D`
  with `A ≤ D` has `|D| ∈ {q ^ 2, q ^ 3}` (orders are `2 ^ m` with `n ∣ m` and
  `q ^ 2 ≤ |D| ≤ q ^ 3`), so `D = A` or `D = ⊤`.  Higman's Lemma 8 (`higman_lemma8`) then gives
  `exp A ≤ 2`, contradicting `A² = Ω₁(P) ≠ 1`.

So `Work.Higman.higman_lemma8` is the *only* substantial input, and no `C₄` machinery beyond it is
needed: the second `C₄` sub-case (`C' = A²`) never arises because we use `C = ⊤` rather than the
minimal cover.
-/
import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.homogeneous_structure
import Submission.Work.Higman.card_sub_one_dvd_of_xi_invariant
import Submission.Work.Higman.MSA.phi_le_of_maximal
import Submission.Work.Higman.higman_lemma8
import Submission.Work.Higman.Q3.pow_sub_one_dvd_pow_sub_one_iff
import Submission.Work.Higman.LayersAlt.GroupSide

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open scoped commutatorElement

namespace Work.Higman.LCD

variable {P : Type} [Group P] [Finite P]

/-- In a group of class two, `⁅x ^ 2, y⁆ = ⁅x, y⁆ ^ 2`. -/
theorem commutator_sq_of_le_center
    (hZ : ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ ≤ Subgroup.center P) (x y : P) :
    ⁅x ^ 2, y⁆ = ⁅x, y⁆ * ⁅x, y⁆ := by
  have hc : x * ⁅x, y⁆ = ⁅x, y⁆ * x :=
    (Subgroup.mem_center_iff.mp
      (hZ (Subgroup.commutator_mem_commutator (Subgroup.mem_top x)
        (Subgroup.mem_top y)))) x
  have h1 : x * y * x⁻¹ = ⁅x, y⁆ * y := by rw [commutatorElement_def]; group
  rw [commutatorElement_def, pow_two (a := x)]
  rw [show (x * x) * y * (x * x)⁻¹ * y⁻¹ = x * (x * y * x⁻¹) * x⁻¹ * y⁻¹ by group]
  rw [h1]
  rw [show x * (⁅x, y⁆ * y) * x⁻¹ * y⁻¹ = x * ⁅x, y⁆ * (y * x⁻¹) * y⁻¹ by group]
  rw [hc]
  rw [show ⁅x, y⁆ * x * (y * x⁻¹) * y⁻¹ = ⁅x, y⁆ * (x * y * x⁻¹) * y⁻¹ by group]
  rw [h1]
  rw [show ⁅x, y⁆ * (⁅x, y⁆ * y) * y⁻¹ = ⁅x, y⁆ * ⁅x, y⁆ by group]

/-- If the commutator subgroup is central and of exponent two (i.e. contained in `Ω₁(P)`), then
every square is central. -/
theorem sq_mem_center_of_commutator_le (h : IsSuzuki2Grp P)
    (hZ : ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ ≤ Subgroup.center P)
    (hO : ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ ≤ omega1 P) :
    ∀ x : P, x ^ 2 ∈ Subgroup.center P := by
  intro x
  rw [Subgroup.mem_center_iff]
  intro y
  refine ((commutatorElement_eq_one_iff_mul_comm (g₁ := x ^ 2) (g₂ := y)).mp ?_).symm
  rw [commutator_sq_of_le_center hZ x y]
  have hmem : ⁅x, y⁆ ∈ omega1 P :=
    hO (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y))
  have h1 := h.mem_omega1.mp hmem
  rwa [pow_two] at h1

/-- **Higman 1963, Theorem 1, in the `FpfXi` setting**: every square of a Suzuki 2-group admitting
a fixed-point-free automorphism `ξ` of order `|Z(P)| - 1` is central. -/
theorem sq_mem_center_of_fpf (h : IsSuzuki2Grp P) {ξ : MulAut P} (hξ : FpfXi ξ) :
    ∀ x : P, x ^ 2 ∈ Subgroup.center P := by
  classical
  -- ## `Z(P) = Ω₁(P)`, of order `q = 2 ^ n`, and `|P| = q ^ 3`
  have hZeq : Subgroup.center P = omega1 P := LayersAlt.center_eq_omega1_of_fpf h hξ
  obtain ⟨n, hZn⟩ : ∃ n : ℕ, Nat.card ↥(Subgroup.center P) = 2 ^ n :=
    (h.isPGroup.to_subgroup (Subgroup.center P)).exists_card_eq
  have hn1 : 1 ≤ n := by
    have h4 : 4 ≤ 2 ^ n := by rw [← hZn, hZeq]; exact h.omega1_card_ge_four
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [h0, pow_zero] at h4; omega
    · exact hpos
  have hnpos : 0 < n := by omega
  have h2n : 1 < 2 ^ n := by
    calc (1 : ℕ) < 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn1
  have hPcard : Nat.card P = (2 ^ n) ^ 3 := by rw [← hZn]; exact hξ.card_cube
  have hPcard2 : Nat.card P = 2 ^ (3 * n) := by rw [hPcard, ← pow_mul, Nat.mul_comm]
  -- ## a maximal `ξ`-invariant abelian normal subgroup
  obtain ⟨A, hA, hmax⟩ := exists_maximal_isXiAbelNormal h
  have hNA : omega1 P ≤ A := omega1_le_of_maximal h hA hmax
  have hAne_top : A ≠ ⊤ := by
    intro htop
    obtain ⟨x, y, hxy⟩ := h.noncomm
    exact hxy (hA.abelian x (htop ▸ Subgroup.mem_top x) y (htop ▸ Subgroup.mem_top y))
  -- ## the homogeneous structure of `A`
  obtain ⟨e, hexp, hcard, htop, hsub⟩ := homogeneous_structure h hA.abelian hA.map_eq
  have hinf : A ⊓ omega1 P = omega1 P := inf_eq_right.mpr hNA
  have hAcard : Nat.card ↥A = (2 ^ n) ^ e := by
    have h0 := hcard 0 (Nat.zero_le e)
    rw [show (2 : ℕ) ^ 0 = 1 from by norm_num, powSub_one_eq, hinf, ← hZeq, hZn,
      Nat.sub_zero] at h0
    exact h0
  -- ## `1 ≤ e ≤ 2`
  have hAnlt : Nat.card ↥A < Nat.card P := by
    have hidx : 1 < A.index := Subgroup.one_lt_index_of_ne_top hAne_top
    have hmul : Nat.card ↥A * A.index = Nat.card P := Subgroup.card_mul_index A
    calc Nat.card ↥A = Nat.card ↥A * 1 := (mul_one _).symm
      _ < Nat.card ↥A * A.index := Nat.mul_lt_mul_of_pos_left hidx Nat.card_pos
      _ = Nat.card P := hmul
  have he_le : e ≤ 2 := by
    have hlt : e < 3 := by
      rw [hAcard, hPcard] at hAnlt
      exact (Nat.pow_lt_pow_iff_right h2n).mp hAnlt
    omega
  have hAne_bot : A ≠ ⊥ := by
    intro hbot
    have h1 : (omega1 P : Subgroup P) ≤ ⊥ := hbot ▸ hNA
    have h2 : Nat.card ↥(omega1 P) = 1 := by rw [le_bot_iff.mp h1]; simp
    have h3 : 4 ≤ Nat.card ↥(omega1 P) := h.omega1_card_ge_four
    omega
  have hepos : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h0 | hpos
    · exfalso
      have hA1 : Nat.card ↥A = 1 := by rw [hAcard, h0, pow_zero]
      exact hAne_bot (Subgroup.eq_bot_of_card_eq (H := A) hA1)
    · exact hpos
  -- ## `Φ(P) ≤ A`
  have hA4 : powSub A 4 = ⊥ := by
    rw [eq_bot_iff, powSub, Subgroup.closure_le]
    rintro y ⟨x, hx, rfl⟩
    refine Subgroup.mem_bot.mpr ?_
    have h2 : x ^ 2 ^ e = 1 := hexp x hx
    have hdvd : 2 ^ e ∣ 4 := by
      rcases (show e = 1 ∨ e = 2 by omega) with h1 | h1 <;> rw [h1] <;> norm_num
    obtain ⟨k, hk⟩ := hdvd
    rw [hk, pow_mul, h2, one_pow]
  have hPhi : powSub (⊤ : Subgroup P) 2 ⊔ ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ ≤ A :=
    MSA.phi_le_of_maximal h hA hmax hA4
  have hP2A : powSub (⊤ : Subgroup P) 2 ≤ A := le_sup_left.trans hPhi
  have hDA : ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ ≤ A := le_sup_right.trans hPhi
  rcases (show e = 1 ∨ e = 2 by omega) with he | he
  · -- ## `e = 1`: `A = Ω₁(P) = Z(P)` and `[P,P] ≤ A`
    have hAeq : A = omega1 P := by
      have hcard' : Nat.card ↥A ≤ Nat.card ↥(omega1 P) := by
        rw [hAcard, he, pow_one, ← hZeq, ← hZn]
      exact (Subgroup.eq_of_le_of_card_ge hNA hcard').symm
    refine sq_mem_center_of_commutator_le h ?_ ?_
    · exact hDA.trans (le_of_eq (hAeq.trans hZeq.symm))
    · exact hDA.trans (le_of_eq hAeq)
  · -- ## `e = 2`: `A² = A ⊓ Ω₁(P) = Ω₁(P) = Z(P)`
    have hA2 : powSub A 2 = omega1 P := by
      have h1 := htop
      rw [he, show (2 : ℕ) ^ (2 - 1) = 2 from by norm_num, hinf] at h1
      exact h1
    have hDinv : (⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆).map (h.xi : MulAut P).toMonoidHom
        = ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ := by
      rw [Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ (h.xi : MulAut P).surjective]
    obtain ⟨i, hi⟩ := hsub ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ hDA hDinv
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · -- ### `P' = A`: the `C₄` shape, excluded by Higman's Lemma 8
      exfalso
      have hGs : ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ = A := by
        rw [hi, hi0, pow_zero, powSub_one_eq]
      have hAcard2 : Nat.card ↥A = 2 ^ (2 * n) := by
        rw [hAcard, he, ← pow_mul, Nat.mul_comm]
      -- the covering hypothesis for `C = ⊤` is automatic
      have hcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
          A ≤ D → D ≤ ⊤ → D = A ∨ D = ⊤ := by
        intro D _ hDinv' hAD _
        obtain ⟨m, hm⟩ : ∃ m : ℕ, Nat.card ↥D = 2 ^ m :=
          (h.isPGroup.to_subgroup D).exists_card_eq
        have hnm : n ∣ m := by
          have h1 := card_sub_one_dvd_of_xi_invariant h hDinv'
          rw [← hZeq, hZn, hm] at h1
          exact (Q3.pow_sub_one_dvd_pow_sub_one_iff (x := 2) (m := n) (k := m)
            (by norm_num) hn1).mp h1
        have hmA : 2 * n ≤ m := by
          have h1 : Nat.card ↥A ≤ Nat.card ↥D := Subgroup.card_le_of_le hAD
          rw [hAcard2, hm] at h1
          exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h1
        have hmP : m ≤ 3 * n := by
          have h1 : Nat.card ↥D ≤ Nat.card P := Subgroup.card_le_card_group D
          rw [hm, hPcard2] at h1
          exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h1
        obtain ⟨k, hk⟩ := hnm
        have hk23 : k = 2 ∨ k = 3 := by
          have hA' : 2 * n ≤ n * k := hk ▸ hmA
          have hP' : n * k ≤ 3 * n := hk ▸ hmP
          have h1 : n * 2 ≤ n * k := by rwa [Nat.mul_comm 2 n] at hA'
          have h2 : n * k ≤ n * 3 := by rwa [Nat.mul_comm 3 n] at hP'
          have h3 : 2 ≤ k := Nat.le_of_mul_le_mul_left h1 hnpos
          have h4 : k ≤ 3 := Nat.le_of_mul_le_mul_left h2 hnpos
          omega
        rcases hk23 with hk2 | hk3
        · left
          refine (Subgroup.eq_of_le_of_card_ge hAD ?_).symm
          rw [hAcard2, hm, hk, hk2, Nat.mul_comm n 2]
        · right
          refine Subgroup.eq_top_of_card_eq (H := D) ?_
          rw [hm, hk, hk3, Nat.mul_comm n 3]
          exact hPcard2.symm
      have hconcl : ∀ a ∈ A, a * a = 1 :=
        higman_lemma8 h hA Subgroup.normal_top
          (Subgroup.map_top_of_surjective _ (h.xi : MulAut P).surjective)
          le_top hAne_top hcover hP2A hGs
      have hAle : A ≤ omega1 P := fun a ha =>
        Subgroup.subset_closure (mem_sqOne.mpr (by rw [pow_two]; exact hconcl a ha))
      have hle : Nat.card ↥A ≤ 2 ^ n := by
        have h1 : Nat.card ↥A ≤ Nat.card ↥(omega1 P) := Subgroup.card_le_of_le hAle
        rw [← hZeq, hZn] at h1
        exact h1
      rw [hAcard2] at hle
      have hcontra : 2 * n ≤ n := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
      omega
    · -- ### `P' = A ^ (2 ^ i)` with `i ≥ 1`
      rcases Nat.lt_or_ge i 2 with hi1 | hi2
      · -- `P' = A² = Ω₁(P) = Z(P)`
        have hi1' : i = 1 := by omega
        have hPeq : ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ = omega1 P := by
          rw [hi, hi1', show (2 : ℕ) ^ 1 = 2 from by norm_num, hA2]
        exact sq_mem_center_of_commutator_le h (le_of_eq (hPeq.trans hZeq.symm)) (le_of_eq hPeq)
      · -- `P' ≤ A ^ (2 ^ i) ≤ A ^ 4 = ⊥`
        have hPbot : ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ = ⊥ := by
          have hdvd : 4 ∣ 2 ^ i := ⟨2 ^ (i - 2), by
            rw [show (4 : ℕ) = 2 ^ 2 from by norm_num, ← pow_add]
            congr 1
            omega⟩
          have hle : powSub A (2 ^ i) ≤ powSub A 4 := powSub_le_of_dvd hA.abelian hdvd
          rw [hi]
          exact le_bot_iff.mp (hle.trans (le_of_eq hA4))
        exact sq_mem_center_of_commutator_le h (by rw [hPbot]; exact bot_le)
          (by rw [hPbot]; exact bot_le)

end Work.Higman.LCD
