import Mathlib
import Submission.Work.LocalPrelim.Ft72Rep

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped Pointwise commutatorElement IsMulCommutative

namespace Work.LocalPrelim

/-- **Quadratic action.**  `(ρ a - 1) ^ 2 = 0` on `Additive (↥F ⧸ Φ(↥F))`.

Proof sketch: `Work.LocalPrelim.frattiniQuotRep_apply_ofMul` computes
`ρ a (Additive.ofMul y) = Additive.ofMul (MulAut.conjNormal a y)` for `y : ↥F`.  Hence
`(ρ a - 1) (Additive.ofMul y) = Additive.ofMul w` with `w = conj_a y * y⁻¹ = ⁅a, y⁆`, and
`(ρ a - 1) (Additive.ofMul w) = Additive.ofMul (conj_a w * w⁻¹) = 0` because `a` commutes with
`w ∈ ⁅F, A⁆` (from `hcomm`).  Reduce to a general element of `Additive (↥F ⧸ Φ(↥F))` by
`Additive.ofMul.surjective` (or `Additive.toMul`) and `QuotientGroup.induction_on`. -/
theorem frattiniQuotRep_sub_one_sq_eq_zero {X : Type*} [Group X] {p : ℕ} {F : Subgroup X}
    [F.Normal] {A : Subgroup X} (hcomm : ⁅⁅F, A⁆, A⁆ = ⊥)
    [IsMulCommutative (↥F ⧸ frattini ↥F)] [Fact (∀ x : ↥F ⧸ frattini ↥F, x ^ p = 1)]
    {a : X} (ha : a ∈ A) :
    (Work.LocalPrelim.frattiniQuotRep p F a - 1) ^ 2 = 0 := by
  -- `A` centralizes `⁅F, A⁆` (the hypothesis `⁅⁅F, A⁆, A⁆ = ⊥` is commutative in its arguments).
  have hcent : A ≤ Subgroup.centralizer (((⁅F, A⁆ : Subgroup X)) : Set X) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
    rwa [Subgroup.commutator_comm A (⁅F, A⁆ : Subgroup X)]
  -- hence conjugation by `a ∈ A` fixes every element of `⁅F, A⁆`.
  have hfix : ∀ w : ↥F, (↑w : X) ∈ ⁅F, A⁆ → MulAut.conjNormal a w = w := by
    intro w hw
    have hc : Commute a (↑w : X) := by
      have h := (Subgroup.mem_centralizer_iff.mp (hcent ha)) (↑w) hw
      exact h.symm
    apply Subtype.coe_inj.mp
    rw [MulAut.conjNormal_apply]
    rw [hc.eq]
    group
  -- the first step of the computation, on a quotient generator.
  have h1 : ∀ y : ↥F, (frattiniQuotRep p F a - 1) (Additive.ofMul (↑y : ↥F ⧸ frattini ↥F))
      = Additive.ofMul (↑(MulAut.conjNormal a y * y⁻¹) : ↥F ⧸ frattini ↥F) := by
    intro y
    rw [LinearMap.sub_apply, Module.End.one_apply, frattiniQuotRep_apply_ofMul, ← ofMul_div,
      ← QuotientGroup.mk_div]
    simp [div_eq_mul_inv]
  -- the second step: the image of `⁅a, y⁆` is killed.
  have h2 : ∀ w : ↥F, (↑w : X) ∈ ⁅F, A⁆ →
      (frattiniQuotRep p F a - 1) (Additive.ofMul (↑w : ↥F ⧸ frattini ↥F)) = 0 := by
    intro w hw
    rw [LinearMap.sub_apply, Module.End.one_apply, frattiniQuotRep_apply_ofMul, hfix w hw,
      sub_self]
  -- `⁅a, y⁆ = conj_a y * y⁻¹` lies in `⁅F, A⁆`.
  have hwy : ∀ y : ↥F, ((MulAut.conjNormal a y * y⁻¹ : ↥F) : X) ∈ ⁅F, A⁆ := by
    intro y
    have hcoe : ((MulAut.conjNormal a y * y⁻¹ : ↥F) : X) = ⁅a, (y : X)⁆ := by
      simp [commutatorElement_def, MulAut.conjNormal_apply]
    rw [hcoe, ← Subgroup.commutator_comm A F]
    exact Subgroup.commutator_mem_commutator ha y.2
  refine LinearMap.ext fun v => ?_
  obtain ⟨q, rfl⟩ := Additive.ofMul.surjective v
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  rw [pow_two, Module.End.mul_apply, h1 y, h2 _ (hwy y), LinearMap.zero_apply]

end Work.LocalPrelim
