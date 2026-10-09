import Mathlib
import Submission.Work.SSGRoute.gradedStepJOne
import Submission.Work.SSGRoute.FlowGroupSuccDefs
import Submission.Work.SSGRoute.two_torsion_assembly
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open Work.CohomologicalShrinking

attribute [local instance] Classical.decEq

set_option maxHeartbeats 1000000

/-! ## The `j = 1` slice of the `p = 2` two-torsion lifting

This file proves `Work.SSGRoute.two_torsion_lift_j_one`, the `j = 1` case of Schmidt–Wingberg's
Step 1 (clause (B)) at `p = 2`: an involution `γ ∈ Γ(τ)`, `τ = (i,1)`, with non-trivial
`G`-component lifts to an involution of `Γ(τ+1)`, `τ + 1 = tauSucc i 1`.

Unlike the general `GradedStep` family (which is FALSE at `j ≥ 2`, see
`Submission/Work/SSGRoute/AUDIT_p2_two_torsion_atom.lean.md`), the `j = 1` slice is a consequence
of the *equivariant linear isomorphism* `JOne.thetaV : F(n)/F(n)² ≃ E(n,(i,1))` of
`gradedStepJOne.lean`: `E(n,(i,1))` is a free `𝔽₂[C₂]`-module, hence every `δ`-fixed element of
`E(n,(i,1))` is a `δ`-difference (`JOne.E_fixed_is_delta_difference`).

The construction of the lift is the one described in
`Submission/Work/SSGRoute/NOTE_two_torsion_lift_two_state.md` §3bis: choose a lift `b₀ ∈ Q_{(i,2)}`
of `γ.left`, set `u := b₀ · (δ • b₀) ∈ ker(flowQuotSucc)`, use the graded piece to write
`u = (δ • c) · c` with `c ∈ ker`, and set `y := ((δ • c) · b₀, δ)`. -/

/-- `flowQuotSucc` commutes with the `G`-action, in the `flowAction` form. -/
lemma flowQuotSucc_flowAction_apply (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) (g : G)
    (x : flowQuotient p G m (tauSucc i j).1 (tauSucc i j).2) :
    flowQuotSucc p G m i j ((flowAction p G m (tauSucc i j).1 (tauSucc i j).2 g) x)
      = (flowAction p G m i j g) (flowQuotSucc p G m i j x) :=
  flowQuotSucc_smul p G m i j g x

/-- **Every element of the kernel of `flowQuotSucc` at `(i,1)` is an involution.**

The kernel of `flowQuotSucc 2 G n i 1` is the graded piece `E(n,(i,1))`, an elementary abelian
`2`-group (`Proposition 5` / Lemma 4 of Schmidt–Wingberg). -/
lemma flowQuotSucc_ker_sq (G : Type*) [Group G] (n i : ℕ)
    (x : flowQuotient 2 G n (tauSucc i 1).1 (tauSucc i 1).2)
    (hx : flowQuotSucc 2 G n i 1 x = 1) : x * x = 1 := by
  obtain ⟨Z, hZ⟩ := QuotientGroup.mk'_surjective
    ((JOne.stepSucc G n i).subgroupOf (⊤ : Subgroup (JOne.FO G n))) x
  have hxZ : JOne.toQ G n i Z.1 = x := by
    rw [JOne.toQ]
    exact (congrArg (QuotientGroup.mk' ((JOne.stepSucc G n i).subgroupOf
      (⊤ : Subgroup (JOne.FO G n)))) (Subtype.ext rfl)).trans hZ
  have hZmem : Z.1 ∈ JOne.stepBase G n i := by
    have h := hx
    rw [← hxZ, JOne.toQ] at h
    rw [flowQuotSucc_mk] at h
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h)
  have h := JOne.toQ_pow_two G n i hZmem
  rw [pow_two, hxZ] at h
  exact h

/-- **Kernel-level graded step at `(i,1)`.**

Every `δ`-fixed element of the kernel of `flowQuotSucc 2 G n i 1` is a *norm* `(δ • c) · c` with
the witness `c` again inside the kernel (the "strong" form, which is *true* for `j = 1`).

This is the transfer of `JOne.E_fixed_is_delta_difference` along the identification
`E(n,(i,1)) ≅ ker(flowQuotSucc 2 G n i 1)` provided by `JOne.toQ` / `JOne.toE`. -/
lemma kerSucc_fixed_witness (G : Type*) [Group G] [Fintype G] (n i : ℕ) (hi : 1 ≤ i)
    (δ : G) (hδ : δ * δ = 1) (hδ1 : δ ≠ 1) :
    ∀ x : flowQuotient 2 G n (tauSucc i 1).1 (tauSucc i 1).2,
      flowQuotSucc 2 G n i 1 x = 1 →
      (flowAction 2 G n (tauSucc i 1).1 (tauSucc i 1).2 δ) x = x →
      ∃ c : flowQuotient 2 G n (tauSucc i 1).1 (tauSucc i 1).2,
        flowQuotSucc 2 G n i 1 c = 1 ∧
        x = (flowAction 2 G n (tauSucc i 1).1 (tauSucc i 1).2 δ) c * c := by
  intro x hxker hxfix
  obtain ⟨Z, hZ⟩ := QuotientGroup.mk'_surjective
    ((JOne.stepSucc G n i).subgroupOf (⊤ : Subgroup (JOne.FO G n))) x
  have hxZ : JOne.toQ G n i Z.1 = x := by
    rw [JOne.toQ]
    exact (congrArg (QuotientGroup.mk' ((JOne.stepSucc G n i).subgroupOf
      (⊤ : Subgroup (JOne.FO G n)))) (Subtype.ext rfl)).trans hZ
  have hZmem : Z.1 ∈ JOne.stepBase G n i := by
    have h := hxker
    rw [← hxZ, JOne.toQ] at h
    rw [flowQuotSucc_mk] at h
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h)
  have hδZmem : δ • Z.1 ∈ JOne.stepBase G n i := JOne.smul_mem_stepBase G n i δ hZmem
  have hfixE : δ • (JOne.toE G n i Z.1 hZmem) = JOne.toE G n i Z.1 hZmem := by
    rw [JOne.toE_smul G n i δ hZmem hδZmem]
    apply JOne.toE_eq_of_mem_stepSucc
    apply (JOne.toQ_eq_iff G n i).mp
    rw [← JOne.toQ_smul G n i δ Z.1, hxZ, hxfix]
  obtain ⟨y, hy⟩ := JOne.E_fixed_is_delta_difference G n i hi δ hδ hδ1
    (JOne.toE G n i Z.1 hZmem) hfixE
  obtain ⟨W, hW⟩ := QuotientGroup.mk'_surjective
    ((JOne.stepSucc G n i).subgroupOf (JOne.stepBase G n i)) (Additive.toMul y)
  have hWy : JOne.toE G n i W.1 W.2 = y := by
    show Additive.ofMul (QuotientGroup.mk' _ W) = y
    rw [hW]; rfl
  have hδW : δ • W.1 ∈ JOne.stepBase G n i := JOne.smul_mem_stepBase G n i δ W.2
  have hprod : (δ • W.1)⁻¹ * W.1 ∈ JOne.stepBase G n i :=
    (JOne.stepBase G n i).mul_mem (Subgroup.inv_mem _ hδW) W.2
  have hE : JOne.toE G n i ((δ • W.1)⁻¹ * W.1) hprod = JOne.toE G n i Z.1 hZmem := by
    rw [JOne.toE_mul G n i (Subgroup.inv_mem _ hδW) W.2 hprod,
      JOne.toE_inv G n i hδW (Subgroup.inv_mem _ hδW),
      ← JOne.toE_smul G n i δ W.2 hδW, hWy]
    rw [JOne.E_neg_self G n i (δ • y), hy, sub_eq_add_neg, JOne.E_neg_self G n i y]
  have hx_eq : JOne.toQ G n i ((δ • W.1)⁻¹ * W.1) = x := by
    rw [← hxZ]
    exact (JOne.toQ_eq_iff G n i).mpr ((JOne.toE_eq_iff G n i hprod hZmem).mp hE)
  refine ⟨JOne.toQ G n i W.1, ?_, ?_⟩
  · rw [JOne.toQ, flowQuotSucc_mk]
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr W.2)
  · have hdc_sq : ((flowAction 2 G n (tauSucc i 1).1 (tauSucc i 1).2 δ)
        (JOne.toQ G n i W.1)) ^ 2 = 1 := by
      rw [JOne.toQ_smul G n i δ W.1]
      exact JOne.toQ_pow_two G n i hδW
    have hinv : ((flowAction 2 G n (tauSucc i 1).1 (tauSucc i 1).2 δ)
          (JOne.toQ G n i W.1))⁻¹
        = (flowAction 2 G n (tauSucc i 1).1 (tauSucc i 1).2 δ) (JOne.toQ G n i W.1) := by
      rw [pow_two] at hdc_sq
      exact inv_eq_of_mul_eq_one_right hdc_sq
    have h1 : ((flowAction 2 G n (tauSucc i 1).1 (tauSucc i 1).2 δ)
            (JOne.toQ G n i W.1))⁻¹ * JOne.toQ G n i W.1
        = JOne.toQ G n i ((δ • W.1)⁻¹ * W.1) := by
      rw [JOne.toQ_smul G n i δ W.1, ← JOne.toQ_inv G n i (δ • W.1),
        ← JOne.toQ_mul G n i _ _]
    rw [← hinv, h1]
    exact hx_eq.symm

theorem two_torsion_lift_j_one (G : Type*) [Group G] [Fintype G] (n i : ℕ) (hi : 1 ≤ i)
    (γ : Work.CohomologicalShrinking.flowGroup 2 G n i 1) (hγ : γ ^ 2 = 1)
    (hδ : (Work.CohomologicalShrinking.flowQuot 2 G n i 1) γ ≠ 1) :
    ∃ y : Work.CohomologicalShrinking.flowGroup 2 G n
        (Work.CohomologicalShrinking.tauSucc i 1).1
        (Work.CohomologicalShrinking.tauSucc i 1).2,
      Work.SSGRoute.LiftsFlowAtGen 2 G n i 1
        (Work.CohomologicalShrinking.tauSucc i 1).1
        (Work.CohomologicalShrinking.tauSucc i 1).2 y γ ∧ y ^ 2 = 1 := by
  have h2 : γ * γ = 1 := by rw [← pow_two]; exact hγ
  have hδδ : γ.right * γ.right = 1 := by
    have h3 := congrArg SemidirectProduct.right h2
    rw [SemidirectProduct.mul_def] at h3
    simpa using h3
  have hleft : (flowAction 2 G n i 1 γ.right) γ.left = γ.left⁻¹ := by
    have h5 := congrArg SemidirectProduct.left h2
    rw [SemidirectProduct.mul_def] at h5
    have h6 : γ.left * (flowAction 2 G n i 1 γ.right) γ.left = 1 := by simpa using h5
    conv_rhs => rw [mul_eq_one_iff_eq_inv.mp h6]
    rw [inv_inv]
  obtain ⟨b₀, hb₀⟩ := flowQuotSucc_surjective 2 G n i 1 γ.left
  have hAsq : (flowAction 2 G n (tauSucc i 1).1 (tauSucc i 1).2 γ.right)
      * (flowAction 2 G n (tauSucc i 1).1 (tauSucc i 1).2 γ.right) = 1 :=
    flowAction_mul_self G n γ.right hδδ (tauSucc i 1).1 (tauSucc i 1).2
  have hA : ∀ y, (flowAction 2 G n (tauSucc i 1).1 (tauSucc i 1).2 γ.right)
      ((flowAction 2 G n (tauSucc i 1).1 (tauSucc i 1).2 γ.right) y) = y :=
    fun y => mulEquiv_sq_apply _ hAsq y
  set x : flowQuotient 2 G n (tauSucc i 1).1 (tauSucc i 1).2 :=
    b₀ * (flowAction 2 G n (tauSucc i 1).1 (tauSucc i 1).2 γ.right) b₀ with hxdef
  have hxker : flowQuotSucc 2 G n i 1 x = 1 := by
    rw [hxdef, map_mul, flowQuotSucc_flowAction_apply, hb₀, hleft, mul_inv_cancel]
  have hxsq : x * x = 1 := flowQuotSucc_ker_sq G n i x hxker
  have hbx : b₀ * x = x * b₀ := by
    have h := flowQuotSucc_ker_central 2 G n i 1 b₀ x hxker
    calc b₀ * x = (b₀ * x * b₀⁻¹) * b₀ := by group
      _ = x * b₀ := by rw [h]
  have hxfix : (flowAction 2 G n (tauSucc i 1).1 (tauSucc i 1).2 γ.right) x = x := by
    have h2' : b₀⁻¹ * x * b₀ = x := by
      rw [mul_assoc, ← hbx, ← mul_assoc, inv_mul_cancel, one_mul]
    have hb : (flowAction 2 G n (tauSucc i 1).1 (tauSucc i 1).2 γ.right) b₀ * b₀ = x := by
      have h1 : (flowAction 2 G n (tauSucc i 1).1 (tauSucc i 1).2 γ.right) b₀ * b₀
          = b₀⁻¹ * (b₀ * (flowAction 2 G n (tauSucc i 1).1 (tauSucc i 1).2 γ.right) b₀) * b₀ :=
        by group
      rw [h1, ← hxdef, h2']
    rw [hxdef, map_mul, hA b₀, hb, hxdef]
  obtain ⟨c, hcker, hcx⟩ := kerSucc_fixed_witness G n i hi γ.right hδδ hδ x hxker hxfix
  have hbcx : b₀ * c = c * b₀ := by
    have h := flowQuotSucc_ker_central 2 G n i 1 b₀ c hcker
    calc b₀ * c = (b₀ * c * b₀⁻¹) * b₀ := by group
      _ = c * b₀ := by rw [h]
  have hck' : flowQuotSucc 2 G n i 1
      ((flowAction 2 G n (tauSucc i 1).1 (tauSucc i 1).2 γ.right) c) = 1 := by
    rw [flowQuotSucc_flowAction_apply, hcker, map_one]
  refine ⟨SemidirectProduct.mk
      ((flowAction 2 G n (tauSucc i 1).1 (tauSucc i 1).2 γ.right) c * b₀) γ.right, ?_, ?_⟩
  · rw [liftsFlowAtGen_iff_flowGroupSucc]
    refine SemidirectProduct.ext ?_ ?_
    · show (flowGroupSucc 2 G n i 1 (SemidirectProduct.mk
        ((flowAction 2 G n (tauSucc i 1).1 (tauSucc i 1).2 γ.right) c * b₀) γ.right)).left
        = γ.left
      rw [flowGroupSucc_mk, map_mul, hck', one_mul, hb₀]
    · show (flowGroupSucc 2 G n i 1 (SemidirectProduct.mk
        ((flowAction 2 G n (tauSucc i 1).1 (tauSucc i 1).2 γ.right) c * b₀) γ.right)).right
        = γ.right
      rw [flowGroupSucc_mk]
  · rw [pow_two, SemidirectProduct.mul_def]
    refine SemidirectProduct.ext ?_ ?_
    · show (flowAction 2 G n (tauSucc i 1).1 (tauSucc i 1).2 γ.right) c * b₀
          * (flowAction 2 G n (tauSucc i 1).1 (tauSucc i 1).2 γ.right)
              ((flowAction 2 G n (tauSucc i 1).1 (tauSucc i 1).2 γ.right) c * b₀)
        = (1 : flowGroup 2 G n (tauSucc i 1).1 (tauSucc i 1).2).left
      rw [show (1 : flowGroup 2 G n (tauSucc i 1).1 (tauSucc i 1).2).left = 1 from rfl]
      rw [map_mul, hA c]
      calc (flowAction 2 G n (tauSucc i 1).1 (tauSucc i 1).2 γ.right) c * b₀
            * (c * (flowAction 2 G n (tauSucc i 1).1 (tauSucc i 1).2 γ.right) b₀)
          = (flowAction 2 G n (tauSucc i 1).1 (tauSucc i 1).2 γ.right) c * (b₀ * c)
            * (flowAction 2 G n (tauSucc i 1).1 (tauSucc i 1).2 γ.right) b₀ := by group
        _ = (flowAction 2 G n (tauSucc i 1).1 (tauSucc i 1).2 γ.right) c * (c * b₀)
            * (flowAction 2 G n (tauSucc i 1).1 (tauSucc i 1).2 γ.right) b₀ := by rw [hbcx]
        _ = ((flowAction 2 G n (tauSucc i 1).1 (tauSucc i 1).2 γ.right) c * c)
            * (b₀ * (flowAction 2 G n (tauSucc i 1).1 (tauSucc i 1).2 γ.right) b₀) := by group
        _ = x * x := by rw [hcx.symm, hxdef.symm]
        _ = 1 := hxsq
    · show γ.right * γ.right = (1 : flowGroup 2 G n (tauSucc i 1).1 (tauSucc i 1).2).right
      rw [show (1 : flowGroup 2 G n (tauSucc i 1).1 (tauSucc i 1).2).right = 1 from rfl]
      exact hδδ

end Work.SSGRoute
