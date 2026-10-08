import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.typeB
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.homogeneous_structure
import Submission.Work.Higman.higman9_exists_new
import Submission.Work.Higman.LayersAlt.fpf_defs
import Submission.Work.Higman.LayersAlt.GroupSide
import Submission.Work.Higman.LayersAlt.card_derivTop_trichotomy
import Submission.Work.Higman.Layers.card_dvd_card_sub_one_of_map_xi_eq
import Submission.Work.Higman.Q3.pow_sub_one_dvd_pow_sub_one_iff

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped commutatorElement

namespace Work.Higman.LayersAlt

/-- **The non-class-two case of a Suzuki 2-group with a fixed-point-free `ξ` is controlled by a
maximal `ξ`-invariant abelian normal subgroup.**

Let `P` be a Suzuki 2-group and `ξ` a fixed-point-free automorphism of order `|Z(P)| - 1`
(`FpfXi ξ`).  If `P' ⊄ Z(P)` (`hcl2`), then `P² = P'` and `(P')² = Z(P)`.

The proof only uses Higman's Lemma 9 (`Work.Higman.higman9_exists_new`: existence of a maximal
`ξ`-invariant abelian normal `A ⊇ Ω₁(P)` with `[P,P] ≤ A`, all squares of `P` in `A` and
`exp A ≤ 4`) and Higman's Lemma 1 in the structural form `Work.Higman.homogeneous_structure`
(the `ξ`-invariant subgroups of `A` are the power subgroups `A^(2^i)`).

Write `q = |Z(P)|`.  Since `Z(P) = Ω₁(P)` (`center_eq_omega1_of_fpf`), we have `A ⊇ Ω₁(P)`, so
`A ⊓ Ω₁(P) = Ω₁(P)`.  Put `|A| = q ^ e`.

* `2 ≤ e`: if `e ≤ 1` then `2 ^ (e - 1) = 1`, so `homogeneous_structure`'s identification
  `A ^ (2 ^ (e - 1)) = A ⊓ Ω₁(P)` gives `A = Ω₁(P) = Z(P)`, hence `P' ≤ A ≤ Z(P)`, contrary to
  `hcl2`.
* `e ≤ 2`: `A ^ 2 ≤ Ω₁(P)` (because `a ^ 4 = 1` for `a ∈ A`), while the chain identity gives
  `|A ^ 2| = q ^ (e - 1)`; as `1 < q` this forces `e - 1 ≤ 1`.
* Hence `e = 2`, and `|A ^ 2| = q = |Ω₁(P)|` with `A ^ 2 ≤ Ω₁(P)` gives `A ^ 2 = Ω₁(P)`.
* Finally `P'` is `ξ`-invariant and `P' ≤ A`, so `P' = A ^ (2 ^ i)` for some `i`; `P' ≠ 1`
  forces `i ≤ 1` (as `A ^ 4 = 1`), and `i = 1` would give `P' = A ^ 2 = Ω₁(P) = Z(P)`,
  contradicting `hcl2`.  So `i = 0`, i.e. `P' = A`; and then `P' ≤ P² ≤ A` gives `P² = P'`,
  while `(P')² = A² = Ω₁(P) = Z(P)`. -/
theorem bad_case_structure {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P) {ξ : MulAut P} (hξ : Work.Higman.FpfXi ξ)
    (hbad : ∃ x : P, x ^ 2 ∉ Subgroup.center P)
    (hcl2 : ¬ Work.Higman.LayersAlt.derivTop P ≤ Subgroup.center P) :
    Work.Higman.LayersAlt.sqSub P = Work.Higman.LayersAlt.derivTop P ∧
      Work.Higman.powSub (Work.Higman.LayersAlt.derivTop P) 2 = Subgroup.center P := by
  classical
  -- ## `Z(P) = Ω₁(P)` in the fixed-point-free case
  have hZ : Subgroup.center P = Work.Higman.omega1 P := center_eq_omega1_of_fpf h hξ
  -- ## a maximal `ξ`-invariant abelian normal subgroup
  obtain ⟨A, hA, hmax, hNA, hDA, hsq, hA4⟩ := Work.Higman.higman9_exists_new h
  -- `Z(P) ≤ A`
  have hZA : Subgroup.center P ≤ A := hZ ▸ hNA
  -- `hcl2` forbids `A ≤ Z(P)` (as `P' ≤ A`)
  have hAz : ¬ A ≤ Subgroup.center P := fun hAZ => hcl2 (hDA.trans hAZ)
  -- ## Higman's Lemma 1 (structural form)
  obtain ⟨e, hexp, hcard, htop, hsub⟩ :=
    Work.Higman.homogeneous_structure h hA.abelian hA.map_eq
  have hinf : A ⊓ Work.Higman.omega1 P = Work.Higman.omega1 P := inf_eq_right.mpr hNA
  -- ## `2 ≤ e`
  have he_ge : 2 ≤ e := by
    by_contra hlt
    have hlt' : e < 2 := not_le.mp hlt
    have h2 : (2 : ℕ) ^ (e - 1) = 1 := by
      have : e - 1 = 0 := by omega
      rw [this, pow_zero]
    have hAeq : A = Work.Higman.omega1 P := by
      have hh := htop
      rwa [h2, Work.Higman.powSub_one_eq, hinf] at hh
    exact hAz (by rw [hAeq]; exact le_of_eq hZ.symm)
  -- the chain cardinality at `i = 1`, i.e. `|A²| = q ^ (e - 1)`
  have hcardA2 : Nat.card ↥(Work.Higman.powSub A 2)
      = (Nat.card ↥(Work.Higman.omega1 P)) ^ (e - 1) := by
    simpa [hinf] using hcard 1 (by omega)
  -- ## `A² ≤ Ω₁(P)`
  have hA2le : Work.Higman.powSub A 2 ≤ Work.Higman.omega1 P := by
    rw [Work.Higman.powSub, Subgroup.closure_le]
    rintro y ⟨x, hx, rfl⟩
    refine h.mem_omega1.mpr ?_
    have h4 : x ^ 4 = 1 := hA4 x hx
    rw [show (x ^ 2) ^ 2 = x ^ 4 from by rw [← pow_mul]]
    exact h4
  -- ## `e ≤ 2`
  have he_le : e ≤ 2 := by
    have hle : (Nat.card ↥(Work.Higman.omega1 P)) ^ (e - 1)
        ≤ Nat.card ↥(Work.Higman.omega1 P) := by
      rw [← hcardA2]
      exact Nat.card_le_card_of_injective (Subgroup.inclusion hA2le)
        (Subgroup.inclusion_injective hA2le)
    have hq : 1 < Nat.card ↥(Work.Higman.omega1 P) := by
      have h4 := h.omega1_card_ge_four
      omega
    have hpow : (Nat.card ↥(Work.Higman.omega1 P)) ^ (e - 1)
        ≤ (Nat.card ↥(Work.Higman.omega1 P)) ^ 1 := by simpa using hle
    have := (Nat.pow_le_pow_iff_right hq).mp hpow
    omega
  have heq : e = 2 := le_antisymm he_le he_ge
  -- ## `A² = Ω₁(P)`
  have hA2ome : Work.Higman.powSub A 2 = Work.Higman.omega1 P := by
    have hc : Nat.card ↥(Work.Higman.powSub A 2) = Nat.card ↥(Work.Higman.omega1 P) := by
      rw [hcardA2, heq]
      norm_num
    exact Subgroup.eq_of_le_of_card_ge hA2le (le_of_eq hc.symm)
  -- ## `P' ≠ ⊥`
  have hDne : derivTop P ≠ ⊥ := by
    intro hbot
    obtain ⟨x, y, hxy⟩ := h.noncomm
    have hmem : ⁅x, y⁆ ∈ derivTop P :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
    rw [hbot] at hmem
    exact hxy (commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp hmem))
  -- ## `P' = A ^ (2 ^ i)` with `i ≤ 1`
  obtain ⟨i, hi⟩ := hsub (derivTop P) hDA (map_derivTop h.xi)
  have hbotA4 : Work.Higman.powSub A 4 = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    rw [Work.Higman.mem_powSub_iff hA.abelian] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact Subgroup.mem_bot.mpr (hA4 x hx)
  have hi1 : i ≤ 1 := by
    by_contra hcon
    have hcon' : 2 ≤ i := by omega
    have hdvd : 2 ^ 2 ∣ 2 ^ i := Nat.pow_dvd_pow 2 hcon'
    have hle : Work.Higman.powSub A (2 ^ i) ≤ Work.Higman.powSub A (2 ^ 2) :=
      Work.Higman.powSub_le_of_dvd hA.abelian hdvd
    have hbot2 : Work.Higman.powSub A (2 ^ 2) = ⊥ := by
      rw [show (2 : ℕ) ^ 2 = 4 from by norm_num]
      exact hbotA4
    rw [← hi] at hle
    exact hDne (le_bot_iff.mp (hbot2 ▸ hle))
  -- ## `i = 0`
  have hi0 : i = 0 := by
    rcases (show i = 0 ∨ i = 1 by omega) with h0 | h1
    · exact h0
    · exfalso
      have hP' : derivTop P = Work.Higman.omega1 P := by
        have h2i : (2 : ℕ) ^ i = 2 := by rw [h1]; norm_num
        rw [hi, h2i, hA2ome]
      exact hcl2 (by rw [hP', ← hZ])
  have hDeq : derivTop P = A := by
    have h2i : (2 : ℕ) ^ i = 1 := by rw [hi0]; norm_num
    rw [hi, h2i, Work.Higman.powSub_one_eq]
  -- ## conclusion
  refine ⟨?_, ?_⟩
  · refine le_antisymm ?_ derivTop_le_sqSub
    rw [sqSub, hDeq, Work.Higman.powSub, Subgroup.closure_le]
    rintro y ⟨x, -, rfl⟩
    exact hsq x
  · rw [hDeq, hA2ome]
    exact hZ.symm

end Work.Higman.LayersAlt
