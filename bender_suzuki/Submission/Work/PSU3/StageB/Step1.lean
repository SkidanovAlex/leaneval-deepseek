/-
# Stage B / B2 — Step 1 of Peterfalvi II Ch. VII §4

The first step of §4 (pp. 278–280): under the hypotheses of B2 there is a subgroup `P` of
prime order of `V = C_D(t)` centralising a nontrivial element `y ∈ Q ∖ Q₀`.

Assembly of the three pieces:

* `exists_prime_order_fixed_mod_Q0`: `¬ DFpfBar` produces a prime-order `P₀ ≤ D` fixing `x mod Q₀`;
* `exists_mem_Q_centralized_of_fixed_mod_Q0`: the averaging/H¹-vanishing turns that into
  `y ∈ Q ∖ Q₀` genuinely centralised by `P₀`;
* `three_le_fixedPts_of_centralizes` + `Work.NormalComplement.prop2b_conj_into_centD`
  (Peterfalvi I Ch. II §4 Prop. 2 (b)): `P₀` then fixes at least three points, hence is
  `D`-conjugate into `V`.  The conjugate `P` centralises the conjugate of `y`.
-/
import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.PSU3.GaloisField
import Submission.Work.PSU3.StageB.Frame
import Submission.Work.PSU3.StageB.NotFpfAux
import Submission.Work.PSU3.StageB.exists_prime_order_fixed_mod_Q0
import Submission.Work.PSU3.StageB.exists_mem_Q_centralized_of_fixed_mod_Q0
import Submission.Work.PSU3.StageB.three_le_fixedPts_of_centralizes
import Submission.Work.NormalComplement.prop2b_conj_into_centD
import Submission.Work.ThreePoints.BenderPrelim

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

open LeanEval.GroupTheory.Defs Submission.Blueprint
open Work.ThmF

namespace Work.PSU3.StageB

/-- `U = O^{2'}(C_G(P))`, realised as a subgroup of `G` (the `F` of `ChIIFourProp` P3). -/
noncomputable def centralizerOddResidual {G : Type} [Group G] (P : Subgroup G) : Subgroup G :=
  (Submission.Blueprint.oddResidual ↥(Subgroup.centralizer (P : Set G))).map
    (Subgroup.centralizer (P : Set G)).subtype

/-- **Step 1 of Ch. VII §4.**  If `DFpfBar` fails, there is a prime-order `P ≤ V = C_D(t)`
centralising some `y ∈ Q ∖ Q₀`. -/
theorem exists_prime_order_le_centD_centralizing {G : Type} [Group G] [Finite G]
    {H Q : Subgroup G} {t : G} (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp) {n : ℕ} (fr : Work.PSU3.CoarseFrame H Q t n)
    (hnfpf : ¬ Work.PSU3.DFpfBar H Q t) :
    ∃ P : Subgroup G, P ≤ Submission.Blueprint.centD H t ∧ (Nat.card P).Prime ∧
      ∃ y ∈ Q, y ∉ fr.Q0 ∧ ∀ p ∈ P, p⁻¹ * y * p = y := by
  obtain ⟨P₀, hP₀D, hP₀prime, x, hxQ, hx0, hfix⟩ :=
    exists_prime_order_fixed_mod_Q0 hS fr hnfpf
  have hdvd : Nat.card P₀ ∣ Nat.card (Submission.Blueprint.twoPoint H t) :=
    Subgroup.card_dvd_of_le hP₀D
  have hoddD : Odd (Nat.card (Submission.Blueprint.twoPoint H t)) :=
    Work.ThmF.split_odd_card_twoPoint hS.split
  have hP₀odd : Odd (Nat.card P₀) := by
    refine hP₀prime.odd_of_ne_two ?_
    intro h2
    exact (Nat.not_even_iff_odd.mpr hoddD) (even_iff_two_dvd.mpr (h2 ▸ hdvd))
  obtain ⟨y, hyQ, hy0, hycent⟩ :=
    exists_mem_Q_centralized_of_fixed_mod_Q0 hS fr hP₀D hP₀odd hxQ hx0 hfix
  have hy1 : y ≠ 1 := fun h1 => hy0 (by rw [h1]; exact fr.Q0.one_mem)
  have h3 : 3 ≤ (Submission.Blueprint.fixedPts H P₀).ncard :=
    three_le_fixedPts_of_centralizes hS.split hP₀D hyQ hy1 hycent
  obtain ⟨d, hdD, hdle⟩ :=
    Work.NormalComplement.prop2b_conj_into_centD G hS.situation
      Work.ThreePoints.benderPrelimProp hC4 hS.split.stronglyEmbedded hS.split.invol
      hS.split.not_mem hP₀D h3
  have hdH : d ∈ H := (Subgroup.mem_inf.mp hdD).1
  refine ⟨P₀.map (MulAut.conj d).toMonoidHom, hdle, ?_, d * y * d⁻¹, ?_, ?_, ?_⟩
  · -- the prime order is preserved
    rw [Subgroup.card_map_of_injective (MulAut.conj d).injective]
    exact hP₀prime
  · -- `d * y * d⁻¹ ∈ Q`
    simpa using Work.RankOneUniqueness.conj_mem_of_mem hS.split hdH hyQ
  · -- `d * y * d⁻¹ ∉ fr.Q0`
    intro hmem
    refine hy0 ?_
    have hsq : (d * y * d⁻¹) ^ 2 = 1 := (fr.mem_Q0_iff _ (fr.Q0_le hmem)).mp hmem
    have hsq' : y ^ 2 = 1 := by
      have h2 : (d * y * d⁻¹) ^ 2 = d * y ^ 2 * d⁻¹ := by rw [pow_two, pow_two]; group
      rw [h2] at hsq
      have h3 : d * y ^ 2 * d⁻¹ = d * 1 * d⁻¹ := by rw [hsq]; group
      exact mul_left_cancel (mul_right_cancel h3)
    exact (fr.mem_Q0_iff y hyQ).mpr hsq'
  · -- `P` centralises `d * y * d⁻¹`
    intro p hp
    obtain ⟨p₀, hp₀, hp_eq⟩ := Subgroup.mem_map.mp hp
    have hc : (MulAut.conj d).toMonoidHom p₀ = d * p₀ * d⁻¹ := MulAut.conj_apply d p₀
    rw [← hp_eq, hc]
    calc (d * p₀ * d⁻¹)⁻¹ * (d * y * d⁻¹) * (d * p₀ * d⁻¹)
        = d * (p₀⁻¹ * y * p₀) * d⁻¹ := by group
      _ = d * y * d⁻¹ := by rw [hycent p₀ hp₀]

end Work.PSU3.StageB
