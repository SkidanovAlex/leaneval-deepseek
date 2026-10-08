import Mathlib
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.suzuki_unipotence
import Submission.Work.Higman.commutator_powSub_A_C

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false

open scoped commutatorElement

namespace Work.Higman

/-- The bracket pairing `⌊uA, aA²⌋ = ⁅u,a⁆ · A⁴` on `C/A × A/A²` is well defined with values in
`A²/A⁴` and is biadditive modulo `A⁴` (elementwise form; commutators written out explicitly). -/
theorem h8_bracket {P : Type} [Group P] [Finite P] (h : IsSuzuki2Grp P) {A C : Subgroup P}
    (hA : IsXiAbelNormal h A) (hAC : A ≤ C) (hCd : ⁅C, C⁆ = A) :
    (∀ u ∈ C, ∀ a ∈ A, u * a * u⁻¹ * a⁻¹ ∈ powSub A 2) ∧
    (∀ u ∈ C, ∀ a ∈ A, ∀ b ∈ A, b * a⁻¹ ∈ powSub A 2 →
      (u * b * u⁻¹ * b⁻¹) * (u * a * u⁻¹ * a⁻¹)⁻¹ ∈ powSub A 4) ∧
    (∀ u ∈ C, ∀ a' ∈ A, ∀ a ∈ A,
      (u * a') * a * (u * a')⁻¹ * a⁻¹ = u * a * u⁻¹ * a⁻¹) ∧
    (∀ u ∈ C, ∀ v ∈ C, ∀ a ∈ A,
      ((u * v) * a * (u * v)⁻¹ * a⁻¹) *
        ((u * a * u⁻¹ * a⁻¹) * (v * a * v⁻¹ * a⁻¹))⁻¹ ∈ powSub A 4) ∧
    (∀ u ∈ C, ∀ a ∈ A, ∀ b ∈ A,
      (u * (a * b) * u⁻¹ * (a * b)⁻¹) *
        ((u * a * u⁻¹ * a⁻¹) * (u * b * u⁻¹ * b⁻¹))⁻¹ ∈ powSub A 4) := by
  have hAb := hA.abelian
  -- `A²` is again a `ξ`-invariant abelian normal subgroup
  have hA2 : IsXiAbelNormal h (powSub A 2) :=
    ⟨powSub_normal hA.normal 2, map_powSub (h.xi : MulAut P) hA.map_eq 2, powSub_comm hAb 2⟩
  have hsub : powSub (powSub A 2) 2 = powSub A 4 := by
    have := powSub_powSub (A := A) hAb 2 2
    simpa using this
  -- unipotence for `A²` : `⁅u, c⁆ ∈ A⁴` for `c ∈ A²`
  have key4 : ∀ c ∈ powSub A 2, ∀ u : P, u * c * u⁻¹ * c⁻¹ ∈ powSub A 4 := by
    intro c hc u
    have h1 := commutator_mem_powSub_two h hA2 u c hc
    rw [hsub, commutatorElement_def] at h1
    exact h1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- values lie in `A²` (unipotence)
    intro u hu a ha
    have h1 := commutator_mem_powSub_two h hA u a ha
    rwa [commutatorElement_def] at h1
  · -- well-definedness in the second variable
    intro u hu a ha b hb hba
    have hmem : b * a⁻¹ ∈ A := A.mul_mem hb (A.inv_mem ha)
    have hua : ⁅u, a⁆ ∈ A := powSub_le (by norm_num) (commutator_mem_powSub_two h hA u a ha)
    have hmul : ⁅u, b⁆ = ⁅u, b * a⁻¹⁆ * ⁅u, a⁆ := by
      conv_lhs => rw [show b = (b * a⁻¹) * a from by group]
      have hstep : ⁅u, (b * a⁻¹) * a⁆
          = ⁅u, b * a⁻¹⁆ * ((b * a⁻¹) * ⁅u, a⁆ * (b * a⁻¹)⁻¹) := by
        rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]
        group
      rw [hstep, hAb (b * a⁻¹) hmem ⁅u, a⁆ hua]
      group
    have key : (u * b * u⁻¹ * b⁻¹) * (u * a * u⁻¹ * a⁻¹)⁻¹ = ⁅u, b * a⁻¹⁆ := by
      rw [show u * b * u⁻¹ * b⁻¹ = ⁅u, b⁆ from by rw [commutatorElement_def],
        show u * a * u⁻¹ * a⁻¹ = ⁅u, a⁆ from by rw [commutatorElement_def], hmul]
      group
    rw [key]
    exact key4 (b * a⁻¹) hba u
  · -- well-definedness in the first variable (exact, since `A` is abelian)
    intro u hu a' ha' a ha
    have h1 : (u * a') * a * (u * a')⁻¹ * a⁻¹ = u * (a' * a * a'⁻¹) * u⁻¹ * a⁻¹ := by
      group
    have h2 : a' * a * a'⁻¹ = a := by
      rw [hAb a' ha' a ha]; group
    rw [h1, h2]
  · -- additivity in the first variable, modulo `A⁴`
    intro u hu v hv a ha
    have hva : ⁅v, a⁆ ∈ powSub A 2 := commutator_mem_powSub_two h hA v a ha
    have hua : ⁅u, a⁆ ∈ powSub A 2 := commutator_mem_powSub_two h hA u a ha
    have hvaA : ⁅v, a⁆ ∈ A := powSub_le (by norm_num) hva
    have huaA : ⁅u, a⁆ ∈ A := powSub_le (by norm_num) hua
    have h4 : ⁅u, ⁅v, a⁆⁆ ∈ powSub A 4 := by
      have := key4 ⁅v, a⁆ hva u
      rwa [commutatorElement_def] at this
    have hstep : ⁅u * v, a⁆ = ⁅u, ⁅v, a⁆⁆ * (⁅v, a⁆ * ⁅u, a⁆) := by
      rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]
      group
    have key : ((u * v) * a * (u * v)⁻¹ * a⁻¹)
        * ((u * a * u⁻¹ * a⁻¹) * (v * a * v⁻¹ * a⁻¹))⁻¹ = ⁅u, ⁅v, a⁆⁆ := by
      rw [show (u * v) * a * (u * v)⁻¹ * a⁻¹ = ⁅u * v, a⁆ from by rw [commutatorElement_def],
        show u * a * u⁻¹ * a⁻¹ = ⁅u, a⁆ from by rw [commutatorElement_def],
        show v * a * v⁻¹ * a⁻¹ = ⁅v, a⁆ from by rw [commutatorElement_def],
        hstep, hAb ⁅v, a⁆ hvaA ⁅u, a⁆ huaA]
      group
    rw [key]
    exact h4
  · -- additivity in the second variable, modulo `A⁴` (in fact exact)
    intro u hu a ha b hb
    have hub : ⁅u, b⁆ ∈ A := powSub_le (by norm_num) (commutator_mem_powSub_two h hA u b hb)
    have hstep : ⁅u, a * b⁆ = ⁅u, a⁆ * ⁅u, b⁆ := by
      have h1 : ⁅u, a * b⁆ = ⁅u, a⁆ * (a * ⁅u, b⁆ * a⁻¹) := by
        rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]
        group
      rw [h1, hAb a ha ⁅u, b⁆ hub]
      group
    have key : (u * (a * b) * u⁻¹ * (a * b)⁻¹)
        * ((u * a * u⁻¹ * a⁻¹) * (u * b * u⁻¹ * b⁻¹))⁻¹ = 1 := by
      rw [show u * (a * b) * u⁻¹ * (a * b)⁻¹ = ⁅u, a * b⁆ from by rw [commutatorElement_def],
        show u * a * u⁻¹ * a⁻¹ = ⁅u, a⁆ from by rw [commutatorElement_def],
        show u * b * u⁻¹ * b⁻¹ = ⁅u, b⁆ from by rw [commutatorElement_def],
        hstep]
      group
    rw [key]
    exact (powSub A 4).one_mem

end Work.Higman
