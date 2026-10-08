/-
The Sylow `2`-subgroup of `SU(3,2^n)` and its normalizer.

The unipotent radical `U` has order `q^3 = 2^(3n)`, which is exactly the `2`-part of
`|SU(3,2^n)| = q^3 (q^2-1) (q^3+1)`, so `U` is a Sylow `2`-subgroup.  Its normalizer is the
Borel subgroup `B`: any `g` normalizing `U` fixes the unique `U`-fixed isotropic point `[e_0]`,
hence lies in `B = Stab([e_0])`.  Consequently the number of Sylow `2`-subgroups is
`[SU(3,2^n) : B] = q^3 + 1`.
-/
import Mathlib
import ChallengeDeps
import Submission.Work.Models.Port.PSU3.StronglyEmbedded
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.normalizer_subgroupOf

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 3200000
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
set_option linter.unnecessarySeqFocus false

open Matrix LeanEval.GroupTheory.Defs
open scoped Pointwise LinearAlgebra.Projectivization

namespace Submission.PSU3

/-- `U` as a subgroup of `SU(3,2^n)`. -/
noncomputable abbrev suUS (n : ℕ) : Subgroup (↥(SU3 n)) := (suU n).subgroupOf (SU3 n)

/-- `B` as a subgroup of `SU(3,2^n)`. -/
noncomputable abbrev suBS (n : ℕ) : Subgroup (↥(SU3 n)) := (suB n).subgroupOf (SU3 n)

lemma exists_ne_pE0_and_ne (n : ℕ) (hn : 1 ≤ n) (p : suIsoPt n) (hp : p ≠ pE0' n) :
    ∃ q : suIsoPt n, q ≠ pE0' n ∧ q ≠ p := by
  classical
  by_contra h
  simp only [not_exists, not_and_or, Classical.not_not] at h
  haveI : Fintype (suIsoPt n) := Fintype.ofFinite _
  have hinj : Function.Injective
      (fun x : suIsoPt n => if x = pE0' n then (0 : Fin 2) else 1) := by
    intro x y hxy
    rcases h x with hx | hx <;> rcases h y with hy | hy
    · rw [hx, hy]
    · rw [hx] at hxy; rw [hy] at hxy
      simp only [if_true, if_neg hp] at hxy
      exact absurd hxy (by decide)
    · rw [hx] at hxy; rw [hy] at hxy
      simp only [if_true, if_neg hp] at hxy
      exact absurd hxy.symm (by decide)
    · rw [hx, hy]
  have hle := Fintype.card_le_of_injective _ hinj
  rw [Fintype.card_fin] at hle
  have hcard : 2 < Fintype.card (suIsoPt n) := by
    rw [← Nat.card_eq_fintype_card, card_suIsoPt n hn]
    have h2 : 2 ≤ 2 ^ (3 * n) := by
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (3 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact (not_le.mpr hcard) hle

/-- The only isotropic point fixed by every element of `U` is `[e_0]`. -/
lemma eq_pE0_of_forall_suUS_fixed (n : ℕ) (hn : 1 ≤ n) {p : suIsoPt n}
    (h : ∀ u : ↥(suUS n), u • p = p) : p = pE0' n := by
  classical
  by_contra hp
  obtain ⟨q, hq1, hq2⟩ := exists_ne_pE0_and_ne n hn p hp
  obtain ⟨g, hgmem, hg⟩ := suU_transitive_ne n hp hq1
  have hfix : (⟨g, hgmem⟩ : ↥(suUS n)) • p = p := h ⟨g, hgmem⟩
  rw [Subgroup.smul_def] at hfix
  rw [hfix] at hg
  exact hq2 hg.symm

theorem normalizer_suU_inf_SU3 (n : ℕ) (hn : 1 ≤ n) :
    Subgroup.normalizer (suU n : Set (GL (Fin 3) (F n))) ⊓ SU3 n = suB n := by
  apply le_antisymm
  · intro g hg
    obtain ⟨hgN, hgU3⟩ := hg
    have hconj : ∀ u ∈ suU n, g⁻¹ * u * g ∈ suU n :=
      fun u hu => (((Subgroup.mem_normalizer_iff'').mp hgN) u).mp hu
    have hstab : (⟨g, hgU3⟩ : ↥(SU3 n)) ∈ MulAction.stabilizer ↥(SU3 n) (pE0' n) := by
      rw [MulAction.mem_stabilizer_iff]
      have hfix : ∀ u : ↥(suUS n), u • ((⟨g, hgU3⟩ : ↥(SU3 n)) • pE0' n) =
          (⟨g, hgU3⟩ : ↥(SU3 n)) • pE0' n := by
        intro u
        set u' : ↥(SU3 n) := (u : ↥(SU3 n)) with hu'
        have hug : (u' : GL (Fin 3) (F n)) ∈ suU n := u.2
        rw [Subgroup.smul_def, ← mul_smul]
        have h1 : u' * (⟨g, hgU3⟩ : ↥(SU3 n)) =
            (⟨g, hgU3⟩ : ↥(SU3 n)) *
              (⟨g⁻¹ * (u' : GL (Fin 3) (F n)) * g,
                suU_le_SU3 n (hconj (u' : GL (Fin 3) (F n)) hug)⟩ : ↥(SU3 n)) := by
          ext
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          group
        rw [h1, mul_smul, suU_fixes_pE0 n _ (hconj (u' : GL (Fin 3) (F n)) hug)]
      exact eq_pE0_of_forall_suUS_fixed n hn hfix
    rw [stabilizer_pE0 n] at hstab
    exact hstab
  · intro g hg
    exact ⟨suB_le_normalizer_suU n hg, suB_le_SU3 n hg⟩

theorem normalizer_suUS (n : ℕ) (hn : 1 ≤ n) :
    Subgroup.normalizer (suUS n : Set (↥(SU3 n))) = suBS n := by
  rw [suUS, suBS, Commons.GroupTheory.Subgroup.normalizer_subgroupOf (suU n) (SU3 n) (suU_le_SU3 n),
    normalizer_suU_inf_SU3 n hn]

lemma suUS_isPGroup (n : ℕ) (hn : 1 ≤ n) : IsPGroup 2 ↥(suUS n) :=
  (isPGroup_suU n hn).of_equiv (Subgroup.subgroupOfEquivOfLe (suU_le_SU3 n)).symm

lemma odd_two_pow_add_one (k : ℕ) (hk : 1 ≤ k) : Odd (2 ^ k + 1) := by
  refine ⟨2 ^ (k - 1), ?_⟩
  rw [show 2 ^ k = 2 * 2 ^ (k - 1) by
    rw [← pow_succ', Nat.sub_add_cancel hk]]

lemma not_dvd_index_suUS (n : ℕ) (hn : 1 ≤ n) : ¬ 2 ∣ (suUS n).index := by
  have h1 := Subgroup.card_mul_index (suUS n)
  rw [suUS, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (suU_le_SU3 n)).toEquiv,
    card_suU n hn, card_SU3 n hn] at h1
  have h2 : (suUS n).index = (2 ^ (2 * n) - 1) * (2 ^ (3 * n) + 1) := by
    have hpos : 0 < 2 ^ (3 * n) := pow_pos (by norm_num) _
    refine Nat.mul_left_cancel hpos ?_
    rw [h1]
    ring
  rw [h2]
  intro hdvd
  exact (Nat.not_even_iff_odd.mpr
    (Odd.mul (odd_two_pow_sub_one (2 * n) (by omega))
      (odd_two_pow_add_one (3 * n) (by omega)))) (even_iff_two_dvd.mpr hdvd)

/-- A Sylow `2`-subgroup of `SU(3,2^n)`: the unipotent radical `U`. -/
noncomputable def suSylow (n : ℕ) (hn : 1 ≤ n) : Sylow 2 (↥(SU3 n)) :=
  (suUS_isPGroup n hn).toSylow (not_dvd_index_suUS n hn)

lemma card_suBS_index (n : ℕ) (hn : 1 ≤ n) :
    Nat.card ↥(suBS n) * (2 ^ (3 * n) + 1) = Nat.card ↥(SU3 n) := by
  rw [suBS, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (suB_le_SU3 n)).toEquiv,
    card_suB_mul_index n hn]

lemma suSylow_coe_sub (n : ℕ) (hn : 1 ≤ n) :
    (↑(suSylow n hn) : Subgroup (↥(SU3 n))) = suUS n :=
  IsPGroup.toSylow_coe (suUS_isPGroup n hn) (not_dvd_index_suUS n hn)

lemma suSylow_coe (n : ℕ) (hn : 1 ≤ n) :
    (↑(suSylow n hn) : Set (↥(SU3 n))) = (suUS n : Set (↥(SU3 n))) := by
  rw [← Sylow.coe_coe, suSylow_coe_sub n hn]

/-- The number of Sylow `2`-subgroups of `SU(3,2^n)` is `q^3 + 1`. -/
theorem card_sylow2_SU3 (n : ℕ) (hn : 1 ≤ n) :
    Nat.card (Sylow 2 (↥(SU3 n))) = 2 ^ (3 * n) + 1 := by
  rw [Sylow.card_eq_index_normalizer (suSylow n hn),
    show (↑(suSylow n hn) : Set (↥(SU3 n))) = (suUS n : Set (↥(SU3 n))) from suSylow_coe n hn,
    normalizer_suUS n hn]
  have h1 := Subgroup.card_mul_index (suBS n)
  have h2 := card_suBS_index n hn
  have hpos : 0 < Nat.card ↥(suBS n) := by
    rw [suBS, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (suB_le_SU3 n)).toEquiv, card_suB n hn]
    exact Nat.mul_pos (pow_pos (by norm_num) _) (two_pow_sub_one_pos n hn)
  exact Nat.mul_left_cancel hpos (h1.trans h2.symm)

end Submission.PSU3
