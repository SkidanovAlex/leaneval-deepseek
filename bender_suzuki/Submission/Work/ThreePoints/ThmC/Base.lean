/-
# `Work.ThreePoints.ThmC.Base` — two standing facts for the proof of Theorem C

* `exists_involutions_mem_of_stronglyEmbedded`: a strongly embedded subgroup `H` of a finite group
  of 2-rank `≥ 2` contains two distinct commuting involutions (Peterfalvi I Ch. I §1 (3)).
* `oddCore_eq_iInf_conj`: `O_{2'}(G) = ⋂_{g∈G} H^g` (Peterfalvi I Ch. I §1 (9)), the second half
  of `Work.ThreePoints.oddCore_le_of_stronglyEmbedded`.
-/
import Mathlib
import Submission.Work.ThreePoints.ThmC.Defs
import Submission.Work.ThreePoints.oddCore_le_of_stronglyEmbedded
import Submission.Work.ThreePoints.FourGroupCoprime
import Submission.Work.BrauerSuzuki.Defs
import Submission.Work.BrauerSuzuki.OddCore.le_of_normal_odd

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open scoped Pointwise

namespace Work.ThreePoints.ThmC

open Submission.Blueprint

/-- **Peterfalvi I Ch. I §1 (3).**  A strongly embedded subgroup of a finite group of 2-rank `≥ 2`
contains two distinct commuting involutions.

(`S ≤ H` a Sylow 2-subgroup of `G`; the four-group `⟨a₀,b₀⟩` lies in some Sylow `2`-subgroup `T`,
and Sylow conjugacy gives `T = g • S`, so `⟨a₀,b₀⟩^{g⁻¹} ≤ S ≤ H`.) -/
theorem exists_involutions_mem_of_stronglyEmbedded {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : IsStronglyEmbedded H) (hfour : HasFourGroup G) :
    ∃ a b : G, a ∈ H ∧ b ∈ H ∧ orderOf a = 2 ∧ orderOf b = 2 ∧ a ≠ b ∧ a * b = b * a := by
  obtain ⟨a₀, b₀, ha₀, hb₀, hne₀, hcomm₀⟩ := hfour
  have ha₀_mul : a₀ * a₀ = 1 := by
    have h := pow_orderOf_eq_one a₀; rw [ha₀] at h; simpa [pow_two] using h
  have hb₀_mul : b₀ * b₀ = 1 := by
    have h := pow_orderOf_eq_one b₀; rw [hb₀] at h; simpa [pow_two] using h
  let V : Subgroup G := Subgroup.closure ({a₀, b₀} : Set G)
  have hVmem : ∀ x ∈ V, x = 1 ∨ x = a₀ ∨ x = b₀ ∨ x = a₀ * b₀ :=
    fun x hx => Work.ThreePoints.closure_pair_mem_four ha₀_mul hb₀_mul hcomm₀ x hx
  have hsq : ∀ x ∈ V, x ^ 2 = 1 := by
    intro x hx
    rcases hVmem x hx with h | h | h | h
    · rw [h]; simp
    · rw [h, pow_two]; exact ha₀_mul
    · rw [h, pow_two]; exact hb₀_mul
    · rw [h]
      calc (a₀ * b₀) ^ 2 = a₀ * (b₀ * (a₀ * b₀)) := by rw [pow_two, mul_assoc]
        _ = a₀ * ((b₀ * a₀) * b₀) := by rw [mul_assoc b₀ a₀ b₀]
        _ = a₀ * ((a₀ * b₀) * b₀) := by rw [hcomm₀]
        _ = a₀ * (a₀ * (b₀ * b₀)) := by rw [mul_assoc a₀ b₀ b₀]
        _ = (a₀ * a₀) * (b₀ * b₀) := by rw [← mul_assoc a₀ a₀ (b₀ * b₀)]
        _ = 1 := by rw [ha₀_mul, hb₀_mul, mul_one]
  have hVpg : IsPGroup 2 V := by
    rw [isPGroup_iff_orderOf_dvd_pow]
    intro y
    refine ⟨1, ?_⟩
    rw [pow_one, ← Subgroup.orderOf_coe y, orderOf_dvd_iff_pow_eq_one]
    exact hsq (y : G) y.2
  obtain ⟨S, hSH⟩ := Work.ThreePoints.exists_sylow_le hH
  obtain ⟨T, hVT⟩ := hVpg.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S T
  have key : ∀ v ∈ V, (MulAut.conj g⁻¹) v ∈ H := by
    intro v hv
    have hsm : v ∈ MulAut.conj g • (S : Set G) := by
      rw [← Sylow.coe_smul, hg]
      exact hVT hv
    rw [Set.mem_smul_set] at hsm
    obtain ⟨s, hs, hsv⟩ := hsm
    rw [MulAut.smul_def, MulAut.conj_apply] at hsv
    have : (MulAut.conj g⁻¹) v = s := by rw [MulAut.conj_apply, ← hsv]; group
    rw [this]
    exact hSH hs
  refine ⟨(MulAut.conj g⁻¹) a₀, (MulAut.conj g⁻¹) b₀, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact key a₀ (Subgroup.subset_closure (by simp))
  · exact key b₀ (Subgroup.subset_closure (by simp))
  · rw [(MulAut.conj g⁻¹).orderOf_eq a₀]; exact ha₀
  · rw [(MulAut.conj g⁻¹).orderOf_eq b₀]; exact hb₀
  · intro h
    apply hne₀
    have := congrArg (MulAut.conj g) h
    simpa using this
  · rw [← map_mul, ← map_mul, hcomm₀]

/-- **Peterfalvi I Ch. I §1 (9), second half.**  `O_{2'}(G) = ⋂_{g∈G} H^g` for a strongly embedded
subgroup `H` of a finite group of 2-rank `≥ 2`. -/
theorem oddCore_eq_iInf_conj {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : IsStronglyEmbedded H) (hfour : HasFourGroup G) :
    oddCore G = ⨅ g : G, conj g H := by
  have hmain : oddCore G = H.normalCore := by
    refine le_antisymm (Subgroup.normal_le_normalCore.mpr
      (Work.ThreePoints.oddCore_le_of_stronglyEmbedded hH hfour)) ?_
    refine Work.BrauerSuzuki.OddCore.le_of_normal_odd H.normalCore_normal ?_
    obtain ⟨t, ht⟩ : ∃ t : G, t ∉ H := by
      by_contra h
      push_neg at h
      exact hH.1 (top_le_iff.mp fun x _ => h x)
    have hle : H.normalCore ≤ conj t H := by
      rw [Subgroup.normalCore_eq_iInf_map_conj]
      exact iInf_le _ t
    exact Odd.of_dvd (Subgroup.card_dvd_of_le (le_inf H.normalCore_le hle)) (hH.2.2 t ht)
  rw [hmain]
  exact Subgroup.normalCore_eq_iInf_map_conj H

end Work.ThreePoints.ThmC
