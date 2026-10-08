/-
The action of the unipotent radical `U` on the isotropic points, and the resulting
2-transitivity of `SU(3,2^n)` on the Hermitian curve.

`U` fixes the point `[e_0]` and is transitive on the remaining `q^3` isotropic points; combined
with transitivity of `SU(3,2^n)` this gives 2-transitivity, hence maximality of the Borel
subgroup `B` (which is the stabiliser of `[e_0]`).
-/
import Mathlib
import ChallengeDeps
import Submission.Work.Models.Port.PSU3.Isotropic
import Submission.Work.Models.Port.Commons.GroupTheory.GroupAction.isCoatom_stabilizer_of_forall_pair
import Submission.Work.Models.Port.Commons.GroupTheory.SL2.card_stabilizer_projectiveSpecialLinearGroup

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
open scoped LinearAlgebra.Projectivization

namespace Submission.PSU3

/-- For a non-zero isotropic vector `v` with `v 2 ≠ 0`, some element of the unipotent radical
sends `v` into the line spanned by `(0,0,1)`. -/
lemma suU_maps_to_vInf (n : ℕ) (v : Fin 3 → F n) (hv : IsIsoVec n v) (hv2 : v 2 ≠ 0) :
    ∃ b c : F n, c + c ^ (2 ^ n) = b ^ (2 ^ n + 1) ∧
      suUmat n b c *ᵥ v = v 2 • (![0, 0, 1] : Fin 3 → F n) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hvq : (v 0) ^ (2 ^ n) * v 2 + (v 2) ^ (2 ^ n) * v 0 = (v 1) ^ (2 ^ n + 1) := by
    have h := hv
    rw [IsIsoVec] at h
    refine CharTwo.add_eq_zero.mp ?_
    rw [show (v 0) ^ (2 ^ n) * v 2 + (v 2) ^ (2 ^ n) * v 0 + (v 1) ^ (2 ^ n + 1) =
        (v 0) ^ (2 ^ n) * v 2 + (v 1) ^ (2 ^ n + 1) + (v 2) ^ (2 ^ n) * v 0 by ring]
    exact h
  have hA : v 0 / v 2 + (v 0 / v 2) ^ (2 ^ n) = (v 1 / v 2) ^ (2 ^ n + 1) := by
    rw [div_pow, div_pow]
    field_simp
    rw [← hvq,
      show (v 2) * (v 2) ^ (2 ^ n) = (v 2) ^ (2 ^ n + 1) from by rw [pow_succ']]
    ring
  have hbq : ((v 1 / v 2) ^ (2 ^ n)) ^ (2 ^ n) = v 1 / v 2 := by
    rw [← pow_mul, show 2 ^ n * 2 ^ n = 2 ^ (2 * n) by rw [← pow_add]; ring, pow_card_sq]
  have hb1 : ((v 1 / v 2) ^ (2 ^ n)) ^ (2 ^ n + 1) = (v 1 / v 2) ^ (2 ^ n + 1) := by
    rw [pow_succ, hbq, ← pow_succ']
  have hc : (v 0 + (v 1 / v 2) ^ (2 ^ n) * v 1) / v 2 =
      v 0 / v 2 + (v 1 / v 2) ^ (2 ^ n + 1) := by
    rw [add_div]
    congr 1
    rw [pow_succ', div_eq_mul_inv, div_eq_mul_inv]
    ring
  have hXq : ((v 1 / v 2) ^ (2 ^ n + 1)) ^ (2 ^ n) = (v 1 / v 2) ^ (2 ^ n + 1) := by
    rw [← pow_mul, show (2 ^ n + 1) * 2 ^ n = 2 ^ (2 * n) + 2 ^ n by
      rw [add_mul, one_mul, ← pow_add]; ring, pow_add, pow_card_sq, ← pow_succ']
  refine ⟨(v 1 / v 2) ^ (2 ^ n), (v 0 + (v 1 / v 2) ^ (2 ^ n) * v 1) / v 2, ?_, ?_⟩
  · rw [hc, hb1, add_pow_char_pow, hXq]
    rw [show v 0 / v 2 + (v 1 / v 2) ^ (2 ^ n + 1) + ((v 0 / v 2) ^ (2 ^ n) + (v 1 / v 2) ^ (2 ^ n + 1))
        = (v 0 / v 2 + (v 0 / v 2) ^ (2 ^ n)) + ((v 1 / v 2) ^ (2 ^ n + 1) + (v 1 / v 2) ^ (2 ^ n + 1)) by ring]
    rw [CharTwo.add_self_eq_zero, add_zero, hA]
  · ext i
    fin_cases i <;>
      simp [suUmat, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul]
    · rw [div_mul_cancel₀ _ hv2]
      exact CharTwo.add_self_eq_zero _
    · rw [hbq, div_mul_cancel₀ _ hv2]
      exact CharTwo.add_self_eq_zero _

lemma pInf_ne_pE0 (n : ℕ) : pInf n ≠ pE0 n := by
  intro h
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' (F n) (![0, 0, 1] : Fin 3 → F n) (suE0 n)
    (vInf_ne_zero n) (suE0_ne_zero n)).mp h
  have hh := congrFun ha 2
  simp [suE0] at hh

lemma pInf'_ne_pE0' (n : ℕ) : pInf' n ≠ pE0' n :=
  fun h => pInf_ne_pE0 n (congrArg Subtype.val h)

/-- For `p ≠ [e_0]` there is `g ∈ U ≤ SU(3,2^n)` with `g • p = [(0,0,1)]`. -/
theorem suU_acts_to_pInf (n : ℕ) (p : suIsoPt n) (hp : p ≠ pE0' n) :
    ∃ g : ↥(SU3 n), g ∈ (suU n).subgroupOf (SU3 n) ∧ g • p = pInf' n := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hv := p.2
  have hvne := Projectivization.rep_nonzero p.1
  have hv2 : p.1.rep 2 ≠ 0 := by
    intro h2
    have hv1 : p.1.rep 1 = 0 := by
      have h := hv
      simp only [IsIsoPt, IsIsoVec] at h
      rw [h2] at h
      simpa using h
    refine hp (Subtype.ext ?_)
    show p.1 = pE0 n
    rw [← Projectivization.mk_rep p.1]
    refine (Projectivization.mk_eq_mk_iff' (F n) p.1.rep (suE0 n) hvne (suE0_ne_zero n)).mpr
      ⟨p.1.rep 0, ?_⟩
    funext i
    fin_cases i <;> simp [suE0, hv1, h2]
  obtain ⟨b, c, hbc, hmat⟩ := suU_maps_to_vInf n p.1.rep hv hv2
  refine ⟨⟨suUg n b c, suU_le_SU3 n ⟨b, c, hbc, rfl⟩⟩, ?_, ?_⟩
  · rw [Subgroup.mem_subgroupOf]; exact ⟨b, c, hbc, rfl⟩
  · apply Subtype.ext
    rw [suIsoPt_smul_def, pInf'_val, pInf]
    obtain ⟨hsm, hmk⟩ := smul_eq_mk n ⟨suUg n b c, suU_le_SU3 n ⟨b, c, hbc, rfl⟩⟩ p.1
    rw [hmk]
    refine (Projectivization.mk_eq_mk_iff' (F n) _ _ hsm (vInf_ne_zero n)).mpr
      ⟨p.1.rep 2, ?_⟩
    show p.1.rep 2 • (![0, 0, 1] : Fin 3 → F n) =
      ((suUg n b c : GL (Fin 3) (F n)) : Matrix (Fin 3) (Fin 3) (F n)) *ᵥ p.1.rep
    exact hmat.symm

/-- `U` fixes the point `[e_0]`. -/
theorem suU_fixes_pE0 (n : ℕ) : ∀ g ∈ (suU n).subgroupOf (SU3 n), g • pE0' n = pE0' n := by
  intro g hg
  obtain ⟨b, c, hbc, hg_eq⟩ := hg
  have hg' : (g : GL (Fin 3) (F n)) = suUg n b c := hg_eq
  apply Subtype.ext
  rw [suIsoPt_smul_def, pE0'_val]
  obtain ⟨hsm, hmk⟩ := smul_pE0 n g
  rw [hmk, pE0]
  refine (Projectivization.mk_eq_mk_iff' (F n) _ _ hsm (suE0_ne_zero n)).mpr ⟨1, ?_⟩
  rw [one_smul]
  show suE0 n = (g : GL (Fin 3) (F n)) • suE0 n
  rw [hg']
  change suE0 n = suUmat n b c *ᵥ suE0 n
  rw [suUmat_mulVec_suE0]

/-- `U` is transitive on the isotropic points other than `[e_0]`. -/
theorem suU_transitive_ne (n : ℕ) {p q : suIsoPt n} (hp : p ≠ pE0' n) (hq : q ≠ pE0' n) :
    ∃ g : ↥(SU3 n), g ∈ (suU n).subgroupOf (SU3 n) ∧ g • p = q := by
  obtain ⟨g₁, hg₁mem, hg₁⟩ := suU_acts_to_pInf n p hp
  obtain ⟨g₂, hg₂mem, hg₂⟩ := suU_acts_to_pInf n q hq
  refine ⟨g₂⁻¹ * g₁, ((suU n).subgroupOf (SU3 n)).mul_mem
    (((suU n).subgroupOf (SU3 n)).inv_mem hg₂mem) hg₁mem, ?_⟩
  have hq' : g₂⁻¹ • pInf' n = q := by
    rw [← hg₂, ← mul_smul, inv_mul_cancel, one_smul]
  rw [mul_smul, hg₁, hq']

/-- `SU(3,2^n)` is 2-transitive on the isotropic points. -/
theorem suIsoPt_two_transitive (n : ℕ) :
    ∀ p q r s : suIsoPt n, p ≠ q → r ≠ s → ∃ g : ↥(SU3 n), g • p = r ∧ g • q = s := by
  intro p q r s hpq hrs
  obtain ⟨g₁, hg₁⟩ := (suIsoPt_isPretransitive n).exists_smul_eq p r
  have hq'r : g₁ • q ≠ r := by
    intro h
    apply hpq
    rw [← hg₁] at h
    exact (smul_left_cancel_iff g₁).mp h.symm
  obtain ⟨A, hA⟩ := (suIsoPt_isPretransitive n).exists_smul_eq (pE0' n) r
  have hAr : A⁻¹ • r = pE0' n := by
    rw [← hA, ← mul_smul, inv_mul_cancel, one_smul]
  have hAp : A⁻¹ • (g₁ • q) ≠ pE0' n := by
    intro h
    apply hq'r
    rw [(smul_eq_iff_eq_inv_smul A⁻¹).mp h, inv_inv, hA]
  have hAs : A⁻¹ • s ≠ pE0' n := by
    intro h
    exact hrs (by rw [(smul_eq_iff_eq_inv_smul A⁻¹).mp h, inv_inv, hA])
  obtain ⟨u, huMem, hu⟩ := suU_transitive_ne n hAp hAs
  set h : ↥(SU3 n) := A * u * A⁻¹ with hh
  have hr : h • r = r := by
    rw [hh, mul_smul, mul_smul, hAr, suU_fixes_pE0 n u huMem, hA]
  have hqs : h • (g₁ • q) = s := by
    rw [hh, mul_smul, mul_smul, hu, ← mul_smul, mul_inv_cancel, one_smul]
  exact ⟨h * g₁, by rw [mul_smul, hg₁, hr], by rw [mul_smul, hqs]⟩

/-- There are `q^3 + 1` isotropic points (the Hermitian curve). -/
theorem card_suIsoPt (n : ℕ) (hn : 1 ≤ n) : Nat.card (suIsoPt n) = 2 ^ (3 * n) + 1 := by
  haveI := suIsoPt_isPretransitive n
  have h := Commons.GroupTheory.SL2.natCard_stabilizer_mul_natCard_eq_of_pretransitive
    (G := ↥(SU3 n)) (X := suIsoPt n) (pE0' n)
  rw [stabilizer_pE0 n] at h
  have hB : Nat.card ↥((suB n).subgroupOf (SU3 n)) = Nat.card ↥(suB n) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (suB_le_SU3 n)).toEquiv
  rw [hB, ← card_suB_mul_index n hn] at h
  have hpos : 0 < Nat.card ↥(suB n) := by
    rw [card_suB n hn]
    exact Nat.mul_pos (pow_pos (by norm_num) _) (Nat.sub_pos_of_lt (Nat.one_lt_two_pow (by omega)))
  exact (Nat.mul_left_cancel_iff hpos).mp h

/-- The Borel subgroup `B` is a maximal subgroup of `SU(3,2^n)`. -/
theorem suB_isCoatom (n : ℕ) : IsCoatom ((suB n).subgroupOf (SU3 n)) := by
  have h := Commons.GroupTheory.GroupAction.isCoatom_stabilizer_of_forall_pair
    (G := ↥(SU3 n)) (Ω := suIsoPt n) (suIsoPt_two_transitive n) (pE0' n)
    ⟨pInf' n, pInf'_ne_pE0' n⟩
  rwa [stabilizer_pE0 n] at h

end Submission.PSU3
