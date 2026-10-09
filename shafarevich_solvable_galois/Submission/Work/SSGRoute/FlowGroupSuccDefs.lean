import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.GroupCohomology.Basic
import Submission.Work.AbsoluteGalois.Obstruction
import Submission.Work.AbsoluteGalois.Cohomology
import Submission.Work.AbsoluteGalois.exists_hom_lift_iff_pullbackCocycle_mem_B2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END


namespace Work.SSGRoute

open Work.CohomologicalShrinking

attribute [local instance] Classical.decEq

/-! ## The projection `Γ(τ+1) ↠ Γ(τ)` -/

/-- The refined term at `τ + 1` is contained in the refined term at `τ`. -/
theorem refinedTerm_tauSucc_le (p : ℕ) (P : Type*) [Group P] (i j : ℕ) :
    refinedTerm p P (tauSucc i j).1 (tauSucc i j).2 ≤ refinedTerm p P i j := by
  by_cases h : j < i
  · rw [tauSucc_of_lt h]
    exact refinedTerm_antitone_snd p P i j
  · rw [tauSucc_of_le (Nat.le_of_not_lt h), refinedTerm_one]
    exact le_sup_right

/-- The quotient map `F/Q →* F/P` for `Q = F^{(τ+1)} ≤ P = F^{(τ)}`. -/
noncomputable def flowQuotSucc (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) :
    flowQuotient p G m (tauSucc i j).1 (tauSucc i j).2 →* flowQuotient p G m i j :=
  QuotientGroup.map _ _ (MonoidHom.id _) (by
    rw [Subgroup.comap_id]
    exact Subgroup.subgroupOf_mono _
      (refinedTerm_tauSucc_le p (Work.Shrinking.freeOperatorGroup G m) i j))

@[simp] theorem flowQuotSucc_mk (p : ℕ) (G : Type*) [Group G] (m i j : ℕ)
    (x : ↥(⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m))) :
    flowQuotSucc p G m i j (QuotientGroup.mk' _ x) = QuotientGroup.mk' _ x :=
  QuotientGroup.map_mk' _ _ _ _ x

/-- The same, in the `QuotientGroup.mk` form used by `SSGRoute.LiftsFlowAt`. -/
theorem flowQuotSucc_mk_apply (p : ℕ) (G : Type*) [Group G] (m i j : ℕ)
    (x : ↥(⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m))) :
    flowQuotSucc p G m i j
        (QuotientGroup.mk x : flowQuotient p G m (tauSucc i j).1 (tauSucc i j).2)
      = (QuotientGroup.mk x : flowQuotient p G m i j) :=
  QuotientGroup.map_mk' _ _ _ _ x

theorem flowQuotSucc_surjective (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) :
    Function.Surjective (flowQuotSucc p G m i j) := by
  intro a
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective
    ((flowTerm p G m i j).subgroupOf (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m))) a
  exact ⟨QuotientGroup.mk' _ x, by rw [flowQuotSucc_mk, hx]⟩

/-- The quotient map is `G`-equivariant for the descended actions. -/
theorem flowQuotSucc_smul (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) (g : G)
    (x : flowQuotient p G m (tauSucc i j).1 (tauSucc i j).2) :
    flowQuotSucc p G m i j (g • x) = g • flowQuotSucc p G m i j x := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective
    ((flowTerm p G m (tauSucc i j).1 (tauSucc i j).2).subgroupOf
      (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m))) x
  have hP : (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m)).map
      (MulDistribMulAction.toMulAut G (Work.Shrinking.freeOperatorGroup G m) g).toMonoidHom
      = ⊤ :=
    Subgroup.map_top_of_surjective _ (MulDistribMulAction.toMulAut G _ g).surjective
  have hKP : (flowTerm p G m (tauSucc i j).1 (tauSucc i j).2).map
      (MulDistribMulAction.toMulAut G (Work.Shrinking.freeOperatorGroup G m) g).toMonoidHom
      = flowTerm p G m (tauSucc i j).1 (tauSucc i j).2 :=
    map_refinedTerm_eq p
      (MulDistribMulAction.toMulAut G (Work.Shrinking.freeOperatorGroup G m) g)
      (tauSucc i j).1 (tauSucc i j).2
  have hKQ : (flowTerm p G m i j).map
      (MulDistribMulAction.toMulAut G (Work.Shrinking.freeOperatorGroup G m) g).toMonoidHom
      = flowTerm p G m i j :=
    map_refinedTerm_eq p
      (MulDistribMulAction.toMulAut G (Work.Shrinking.freeOperatorGroup G m) g) i j
  have keyP : g • (QuotientGroup.mk'
        ((flowTerm p G m (tauSucc i j).1 (tauSucc i j).2).subgroupOf
          (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m))) y)
      = QuotientGroup.mk'
        ((flowTerm p G m (tauSucc i j).1 (tauSucc i j).2).subgroupOf
          (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m)))
        (Work.Shrinking.subAut ⊤ g hP y) := by
    change Work.Shrinking.quotAut ⊤ (flowTerm p G m (tauSucc i j).1 (tauSucc i j).2) g hP hKP
      (QuotientGroup.mk' _ y) = _
    rw [Work.Shrinking.quotAut_mk]
  have keyQ : g • (QuotientGroup.mk'
        ((flowTerm p G m i j).subgroupOf (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m))) y)
      = QuotientGroup.mk'
        ((flowTerm p G m i j).subgroupOf (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m)))
        (Work.Shrinking.subAut ⊤ g hP y) := by
    change Work.Shrinking.quotAut ⊤ (flowTerm p G m i j) g hP hKQ
      (QuotientGroup.mk' _ y) = _
    rw [Work.Shrinking.quotAut_mk]
  rw [keyP, flowQuotSucc_mk]
  exact keyQ.symm

/-- The canonical projection `Γ(τ+1) = F(m)/F(m)^{(τ+1)} ⋊ G →* Γ(τ) = F(m)/F(m)^{(τ)} ⋊ G`. -/
noncomputable def flowGroupSucc (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) :
    flowGroup p G m (tauSucc i j).1 (tauSucc i j).2 →* flowGroup p G m i j :=
  SemidirectProduct.map (flowQuotSucc p G m i j) (MonoidHom.id G)
    (fun g => MonoidHom.ext (fun x => flowQuotSucc_smul p G m i j g x))

@[simp] theorem flowGroupSucc_mk (p : ℕ) (G : Type*) [Group G] (m i j : ℕ)
    (a : flowQuotient p G m (tauSucc i j).1 (tauSucc i j).2) (g : G) :
    flowGroupSucc p G m i j (SemidirectProduct.mk a g) =
      SemidirectProduct.mk (flowQuotSucc p G m i j a) g := by
  refine SemidirectProduct.ext ?_ ?_
  · rw [flowGroupSucc, SemidirectProduct.map_left]
  · rw [flowGroupSucc, SemidirectProduct.map_right]; rfl

@[simp] theorem flowGroupSucc_left (p : ℕ) (G : Type*) [Group G] (m i j : ℕ)
    (y : flowGroup p G m (tauSucc i j).1 (tauSucc i j).2) :
    (flowGroupSucc p G m i j y).left = flowQuotSucc p G m i j y.left := by
  conv_lhs => rw [show y = SemidirectProduct.mk y.left y.right from rfl, flowGroupSucc_mk]

@[simp] theorem flowGroupSucc_right (p : ℕ) (G : Type*) [Group G] (m i j : ℕ)
    (y : flowGroup p G m (tauSucc i j).1 (tauSucc i j).2) :
    (flowGroupSucc p G m i j y).right = y.right := by
  conv_lhs => rw [show y = SemidirectProduct.mk y.left y.right from rfl, flowGroupSucc_mk]

@[simp] theorem flowGroupMap_left (p : ℕ) (G : Type*) [Group G] (i j : ℕ) {m n : ℕ}
    (Φ : OperatorMap G m n) (x : flowGroup p G m i j) :
    (flowGroupMap p G i j Φ x).left = flowQuotMap p G i j Φ x.left := by
  conv_lhs => rw [show x = SemidirectProduct.mk x.left x.right from rfl]
  rw [flowGroupMap, SemidirectProduct.map_left]

@[simp] theorem flowGroupMap_right (p : ℕ) (G : Type*) [Group G] (i j : ℕ) {m n : ℕ}
    (Φ : OperatorMap G m n) (x : flowGroup p G m i j) :
    (flowGroupMap p G i j Φ x).right = x.right := by
  conv_lhs => rw [show x = SemidirectProduct.mk x.left x.right from rfl]
  rw [flowGroupMap, SemidirectProduct.map_right, MonoidHom.id_apply]

theorem flowGroupSucc_surjective (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) :
    Function.Surjective (flowGroupSucc p G m i j) := by
  intro γ
  obtain ⟨z, hz⟩ := QuotientGroup.mk'_surjective
    ((flowTerm p G m i j).subgroupOf (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m))) γ.left
  refine ⟨SemidirectProduct.mk (QuotientGroup.mk' _ z) γ.right, ?_⟩
  rw [flowGroupSucc_mk, flowQuotSucc_mk, hz]

/-! ## `LiftsFlowAt` as the projection -/

/-- The generic form of `SSGRoute.LiftsFlowAt` (the two definitions are equal by `rfl`). -/
def LiftsFlowAtGen (p : ℕ) (G : Type*) [Group G] (m i j i' j' : ℕ)
    (y : flowGroup p G m i' j') (x : flowGroup p G m i j) : Prop :=
  y.right = x.right ∧
    ∃ z : (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m)),
      y.left = (QuotientGroup.mk z : flowQuotient p G m i' j') ∧
      x.left = (QuotientGroup.mk z : flowQuotient p G m i j)

/-- `LiftsFlowAt y x` is exactly `flowGroupSucc y = x`. -/
theorem liftsFlowAtGen_iff_flowGroupSucc (p : ℕ) (G : Type*) [Group G] (m i j : ℕ)
    (y : flowGroup p G m (tauSucc i j).1 (tauSucc i j).2) (x : flowGroup p G m i j) :
    LiftsFlowAtGen p G m i j (tauSucc i j).1 (tauSucc i j).2 y x ↔
      flowGroupSucc p G m i j y = x := by
  constructor
  · rintro ⟨hr, z, h1, h2⟩
    refine SemidirectProduct.ext ?_ ?_
    · show (flowGroupSucc p G m i j y).left = x.left
      conv_lhs => rw [show y = SemidirectProduct.mk y.left y.right from rfl, flowGroupSucc_mk]
      rw [h1, flowQuotSucc_mk_apply, h2]
    · show (flowGroupSucc p G m i j y).right = x.right
      conv_lhs => rw [show y = SemidirectProduct.mk y.left y.right from rfl, flowGroupSucc_mk]
      rw [hr]
  · intro h
    have hr : y.right = x.right := by
      have := congrArg SemidirectProduct.right h
      rwa [show (flowGroupSucc p G m i j y).right = y.right from by
        rw [show y = SemidirectProduct.mk y.left y.right from rfl, flowGroupSucc_mk]] at this
    refine ⟨hr, ?_⟩
    obtain ⟨z, hz⟩ := QuotientGroup.mk'_surjective
      ((flowTerm p G m (tauSucc i j).1 (tauSucc i j).2).subgroupOf
        (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m))) y.left
    refine ⟨z, hz.symm, ?_⟩
    have h2 : flowQuotSucc p G m i j y.left = x.left := by
      have := congrArg SemidirectProduct.left h
      rwa [show (flowGroupSucc p G m i j y).left = flowQuotSucc p G m i j y.left from by
        rw [show y = SemidirectProduct.mk y.left y.right from rfl, flowGroupSucc_mk]] at this
    rw [← hz, flowQuotSucc_mk] at h2
    exact h2.symm

/-- `LiftsFlowAt` is exactly the vanishing of the projection `flowGroupSucc`. -/
theorem liftsFlowAt_iff_flowGroupSucc (p : ℕ) (K : IntermediateField ℚ SSGRoute.QBar)
    (m i j : ℕ)
    (y : flowGroup p (K ≃ₐ[ℚ] K) m (tauSucc i j).1 (tauSucc i j).2)
    (x : flowGroup p (K ≃ₐ[ℚ] K) m i j) :
    SSGRoute.LiftsFlowAt y x ↔ flowGroupSucc p (K ≃ₐ[ℚ] K) m i j y = x :=
  liftsFlowAtGen_iff_flowGroupSucc p (K ≃ₐ[ℚ] K) m i j y x

/-! ## A section of `flowGroupSucc` -/

/-- A set-theoretic section of `flowGroupSucc`, normalized at `1`. -/
noncomputable def flowGroupSection (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) :
    flowGroup p G m i j → flowGroup p G m (tauSucc i j).1 (tauSucc i j).2 := fun x =>
  if h : x = 1 then 1
  else Classical.choose (flowGroupSucc_surjective p G m i j x)

@[simp] theorem flowGroupSection_one (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) :
    flowGroupSection p G m i j 1 = 1 := dif_pos rfl

theorem flowGroupSucc_section (p : ℕ) (G : Type*) [Group G] (m i j : ℕ)
    (x : flowGroup p G m i j) :
    flowGroupSucc p G m i j (flowGroupSection p G m i j x) = x := by
  rw [flowGroupSection]
  split
  · next h => rw [h, map_one]
  · next h => exact Classical.choose_spec (flowGroupSucc_surjective p G m i j x)

/-- The section `2`-cocycle of the projection `flowGroupSucc`, valued in its kernel. -/
noncomputable def kerSuccCocycleMul (p : ℕ) (G : Type*) [Group G] (m i j : ℕ)
    {H : Type*} [Group H] (ρ : H →* flowGroup p G m i j)
    (s : flowGroup p G m i j → flowGroup p G m (tauSucc i j).1 (tauSucc i j).2)
    (hs : ∀ x, flowGroupSucc p G m i j (s x) = x) :
    H → H → ↥(flowGroupSucc p G m i j).ker := fun σ τ =>
  ⟨s (ρ σ) * s (ρ τ) * (s (ρ (σ * τ)))⁻¹, by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv, hs]
    group⟩

/-- The same cocycle, written additively. -/
noncomputable def kerSuccCocycle (p : ℕ) (G : Type*) [Group G] (m i j : ℕ)
    {H : Type*} [Group H] (ρ : H →* flowGroup p G m i j)
    (s : flowGroup p G m i j → flowGroup p G m (tauSucc i j).1 (tauSucc i j).2)
    (hs : ∀ x, flowGroupSucc p G m i j (s x) = x) :
    H → H → Additive ↥(flowGroupSucc p G m i j).ker :=
  fun σ τ => Additive.ofMul (kerSuccCocycleMul p G m i j ρ s hs σ τ)

/-! ## The kernel map induced by a rank change and the correction cochain -/

/-- The quotient maps commute with the rank change `Φ`. -/
theorem flowQuotSucc_flowQuotMap (p : ℕ) (G : Type*) [Group G] (i j : ℕ) {m n : ℕ}
    (Φ : OperatorMap G m n) :
    (flowQuotSucc p G n i j).comp (flowQuotMap p G (tauSucc i j).1 (tauSucc i j).2 Φ) =
      (flowQuotMap p G i j Φ).comp (flowQuotSucc p G m i j) := by
  refine MonoidHom.ext fun x => ?_
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective
    ((flowTerm p G m (tauSucc i j).1 (tauSucc i j).2).subgroupOf
      (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m))) x
  simp only [MonoidHom.comp_apply, flowQuotMap_mk, flowQuotSucc_mk]

/-- The projections commute with the rank change `Φ`. -/
theorem flowGroupSucc_flowGroupMap (p : ℕ) (G : Type*) [Group G] (i j : ℕ) {m n : ℕ}
    (Φ : OperatorMap G m n) :
    (flowGroupSucc p G n i j).comp (flowGroupMap p G (tauSucc i j).1 (tauSucc i j).2 Φ) =
      (flowGroupMap p G i j Φ).comp (flowGroupSucc p G m i j) := by
  refine MonoidHom.ext fun x => ?_
  refine SemidirectProduct.ext ?_ ?_
  · simp only [MonoidHom.comp_apply, flowGroupSucc_left, flowGroupMap_left]
    exact DFunLike.congr_fun (flowQuotSucc_flowQuotMap p G i j Φ) x.left
  · simp only [MonoidHom.comp_apply, flowGroupSucc_right, flowGroupMap_right]

/-- The map induced by an operator map on the kernels of the projections. -/
noncomputable def flowGroupSuccKernelMap (p : ℕ) (G : Type*) [Group G] (i j : ℕ) {m n : ℕ}
    (Φ : OperatorMap G m n) :
    ↥(flowGroupSucc p G m i j).ker →* ↥(flowGroupSucc p G n i j).ker :=
  ((flowGroupMap p G (tauSucc i j).1 (tauSucc i j).2 Φ).comp (Subgroup.subtype _)).codRestrict _
    (fun x => by
      rw [MonoidHom.mem_ker]
      show flowGroupSucc p G n i j (flowGroupMap p G (tauSucc i j).1 (tauSucc i j).2 Φ
        (x : flowGroup p G m (tauSucc i j).1 (tauSucc i j).2)) = 1
      have h := DFunLike.congr_fun (flowGroupSucc_flowGroupMap p G i j Φ)
        (x : flowGroup p G m (tauSucc i j).1 (tauSucc i j).2)
      simp only [MonoidHom.comp_apply] at h
      rw [h, x.2, map_one])


@[simp] theorem flowGroupSuccKernelMap_apply (p : ℕ) (G : Type*) [Group G] (i j : ℕ) {m n : ℕ}
    (Φ : OperatorMap G m n) (x : ↥(flowGroupSucc p G m i j).ker) :
    ((flowGroupSuccKernelMap p G i j Φ x : ↥(flowGroupSucc p G n i j).ker) :
        flowGroup p G n (tauSucc i j).1 (tauSucc i j).2)
      = flowGroupMap p G (tauSucc i j).1 (tauSucc i j).2 Φ
          (x : flowGroup p G m (tauSucc i j).1 (tauSucc i j).2) := rfl

/-- The correction cochain `β_σ = Φ_{τ+1}(s_m(ρ σ)) s_n(ρ' σ)^{-1}` of the naturality of the
section cocycle. -/
noncomputable def kerSuccBeta (p : ℕ) (G : Type*) [Group G] (i j : ℕ) {m n : ℕ}
    (Φ : OperatorMap G m n) {H : Type*} [Group H]
    (ρ : H →* flowGroup p G m i j) (ρ' : H →* flowGroup p G n i j)
    (hρ : ∀ σ : H, ρ' σ = flowGroupMap p G i j Φ (ρ σ))
    (s : flowGroup p G m i j → flowGroup p G m (tauSucc i j).1 (tauSucc i j).2)
    (s' : flowGroup p G n i j → flowGroup p G n (tauSucc i j).1 (tauSucc i j).2)
    (hs : ∀ x, flowGroupSucc p G m i j (s x) = x)
    (hs' : ∀ x, flowGroupSucc p G n i j (s' x) = x) :
    H → ↥(flowGroupSucc p G n i j).ker := fun σ =>
  ⟨flowGroupMap p G (tauSucc i j).1 (tauSucc i j).2 Φ (s (ρ σ)) * (s' (ρ' σ))⁻¹, by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hs']
    have h := DFunLike.congr_fun (flowGroupSucc_flowGroupMap p G i j Φ) (s (ρ σ))
    simp only [MonoidHom.comp_apply] at h
    rw [h, hs, hρ σ, mul_inv_cancel]⟩

/-! ## The lifting criterion for `flowGroupSucc` -/

/-- The pullback of the abstract `sectionCocycle` is the cocycle `kerSuccCocycle`. -/
theorem pullbackCocycle_sectionCocycle_eq (p : ℕ) (G : Type*) [Group G] (m i j : ℕ)
    {H : Type*} [Group H] (ρ : H →* flowGroup p G m i j)
    (s : flowGroup p G m i j → flowGroup p G m (tauSucc i j).1 (tauSucc i j).2)
    (hs : ∀ x, flowGroupSucc p G m i j (s x) = x) :
    Work.AbsoluteGalois.pullbackCocycle ρ
        (Work.AbsoluteGalois.sectionCocycle (flowGroupSucc p G m i j) s hs)
      = fun x : H × H => kerSuccCocycle p G m i j ρ s hs x.1 x.2 := by
  funext x
  obtain ⟨σ, τ⟩ := x
  rw [Work.AbsoluteGalois.pullbackCocycle_apply]
  apply Additive.ofMul.injective
  have hK : s (ρ σ) * s (ρ τ) * (s (ρ (σ * τ)))⁻¹
      = s (ρ σ) * s (ρ τ) * (s (ρ σ * ρ τ))⁻¹ := by
    rw [map_mul ρ σ τ]
  exact Subtype.ext hK.symm

theorem exists_lift_iff_kerSuccCocycle (p : ℕ) (G : Type*) [Group G] (m i j : ℕ)
    {H : Type*} [Group H] (ρ : H →* flowGroup p G m i j)
    (s : flowGroup p G m i j → flowGroup p G m (tauSucc i j).1 (tauSucc i j).2)
    (hs : ∀ x, flowGroupSucc p G m i j (s x) = x) (h1 : s 1 = 1)
    (hcomm : ∀ a b : ↥(flowGroupSucc p G m i j).ker, a * b = b * a) :
    letI : CommGroup ↥(flowGroupSucc p G m i j).ker :=
      { (inferInstance : Group ↥(flowGroupSucc p G m i j).ker) with mul_comm := hcomm }
    letI : DistribMulAction (flowGroup p G m i j) (Additive ↥(flowGroupSucc p G m i j).ker) :=
      Work.AbsoluteGalois.kernelAction (flowGroupSucc p G m i j) s hs h1 hcomm
    letI : DistribMulAction H (Additive ↥(flowGroupSucc p G m i j).ker) :=
      DistribMulAction.compHom (Additive ↥(flowGroupSucc p G m i j).ker) ρ
    ((∃ ψ : H →* flowGroup p G m (tauSucc i j).1 (tauSucc i j).2,
        (flowGroupSucc p G m i j).comp ψ = ρ) ↔
      (fun x : H × H => kerSuccCocycle p G m i j ρ s hs x.1 x.2) ∈
        Work.GroupCohomology.B2 H (Additive ↥(flowGroupSucc p G m i j).ker)) := by
  letI : CommGroup ↥(flowGroupSucc p G m i j).ker :=
    { (inferInstance : Group ↥(flowGroupSucc p G m i j).ker) with mul_comm := hcomm }
  letI : DistribMulAction (flowGroup p G m i j) (Additive ↥(flowGroupSucc p G m i j).ker) :=
    Work.AbsoluteGalois.kernelAction (flowGroupSucc p G m i j) s hs h1 hcomm
  letI : DistribMulAction H (Additive ↥(flowGroupSucc p G m i j).ker) :=
    DistribMulAction.compHom (Additive ↥(flowGroupSucc p G m i j).ker) ρ
  have h := Work.AbsoluteGalois.exists_hom_lift_iff_pullbackCocycle_mem_B2
    (G := flowGroup p G m (tauSucc i j).1 (tauSucc i j).2)
    (Q := flowGroup p G m i j) (H := H)
    (flowGroupSucc p G m i j) s hs h1 hcomm ρ
  rwa [pullbackCocycle_sectionCocycle_eq p G m i j ρ s hs] at h

end Work.SSGRoute
