import Mathlib
import Submission.Work.Higman.Q3.Defs
import Submission.Work.Higman.CoordDefs
import Submission.Work.Higman.cocy_props
import Submission.Work.Higman.TwoStepAssembly
import Submission.Work.Higman.TwoStepLift

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped commutatorElement
open IsMulCommutative

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.Higman

/-- A group in which every square is central has central commutators: its central quotient
has exponent two, hence is abelian. -/
theorem commutator_mem_center_of_sq_mem_center {P : Type} [Group P] [Finite P]
    (hsq : ∀ x : P, x ^ 2 ∈ Subgroup.center P) (a b : P) :
    a * b * a⁻¹ * b⁻¹ ∈ Subgroup.center P := by
  haveI hcomm : IsMulCommutative (P ⧸ Subgroup.center P) := by
    refine IsMulCommutative.of_comm ?_
    have hq : ∀ z : P ⧸ Subgroup.center P, z ^ 2 = 1 := by
      intro z
      induction z using QuotientGroup.induction_on with
      | _ a => rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hsq a
    have hq2 : ∀ z : P ⧸ Subgroup.center P, z * z = 1 := fun z => by simpa [pow_two] using hq z
    intro x y
    have hx : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hq2 x)
    have hy : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hq2 y)
    have hxy : (x*y)⁻¹ = x*y := inv_eq_of_mul_eq_one_right (hq2 (x*y))
    rw [← hxy, mul_inv_rev, hx, hy]
  have hmem : ⁅a, b⁆ ∈ _root_.commutator P := by
    rw [commutator_eq_closure]
    exact Subgroup.subset_closure (commutator_mem_commutatorSet a b)
  have hle := Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hcomm
  have := hle hmem
  rwa [commutatorElement_def] at this

theorem nonempty_twoStepModel {P : Type} [Group P] [Finite P]
    (hsq : ∀ x : P, x ^ 2 ∈ Subgroup.center P)
    (hexp : ∀ z : P, z ∈ Subgroup.center P → z ^ 2 = 1) :
    Nonempty (TwoStepModel P) := by
  have hc : ∀ a b : P, a * b * a⁻¹ * b⁻¹ ∈ Subgroup.center P :=
    commutator_mem_center_of_sq_mem_center hsq
  have hC : ∀ (n : ℕ) (A : Fin n → P),
      (∀ v w u : Fin n → ZMod 2, cocy n A (v + w) u = cocy n A v u * cocy n A w u) ∧
      (∀ v w u : Fin n → ZMod 2, cocy n A v (w + u) = cocy n A v w * cocy n A v u) ∧
      (∀ v w : Fin n → ZMod 2, cocy n A v w ∈ Subgroup.center P) :=
    fun n A => cocy_props hc hsq hexp n A
  obtain ⟨M0⟩ := assembly hsq hexp hC
  haveI : Biadd (fun x y : ULift M0.V => ULift.up (M0.b x.down y.down)) := biadd_ulift M0.b
  refine ⟨{ V := ULift M0.V
            W := ULift M0.W
            b := fun x y => ULift.up (M0.b x.down y.down)
            biadd_b := biadd_ulift M0.b
            card_V := (Nat.card_congr Equiv.ulift).trans M0.card_V
            card_W := (Nat.card_congr Equiv.ulift).trans M0.card_W
            iso := M0.iso.trans (twoStepULiftMulEquiv M0.b).symm }⟩

end Work.Higman
