import Mathlib
import Submission.Work.SSGRoute.FlowGroupSuccDefs
import Submission.Work.SSGRoute.ProperStageDefs
import Submission.Work.SSGRoute.kerSucc_conj_eq_mk_one
import Submission.Work.CohomologicalShrinking.flow.flowQuotMap_smul
import Submission.Work.CohomologicalShrinking.functorial.gradedMapAdd_smul
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open Work.CohomologicalShrinking

set_option maxHeartbeats 1000000

/-!
# The kernel of `flowGroupSucc` is the graded piece `E(m,τ)`, equivariantly

The projection `flowGroupSucc p G m i j : F(m)/F(m)^{(τ+1)} ⋊ G →* F(m)/F(m)^{(τ)} ⋊ G`
(`τ+1 = tauSucc i j`) has kernel the copy of the graded piece
`E(m,τ) = F(m)^{(τ)}/F(m)^{(τ+1)}` inside the semidirect product.  This file constructs the
canonical identification

* `succKerIso p G m i j : E(m,τ) ≃* ker (flowGroupSucc p G m i j)`,

proves that it is `G`-equivariant for the conjugation action on the kernel
(`succKerIso_smul`) and natural in the rank (`succKerIso_naturality`), and deduces the existence
of the pair of additive `G`-equivariant identifications of the lemma
`exists_kerSuccAddEquiv_equivariant`.

The identification is the first isomorphism theorem applied to the composite
`F(m)^{(τ)} ↪ F(m) ↠ F(m)/F(m)^{(τ+1)}` (whose image is exactly the kernel of the projection, and
whose kernel is `F(m)^{(τ+1)}`), transported along the inclusion of the free factor.
-/

/-! ## The map `F(m)^{(τ)} →* ker (flowGroupSucc p G m i j)` -/

/-- The element of `F(m)/F(m)^{(τ+1)} ⋊ G` determined by an element of the refined term
`F(m)^{(τ)}`. -/
noncomputable def succLiftToGroup (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) :
    ↥(flowTerm p G m i j) →* flowGroup p G m (tauSucc i j).1 (tauSucc i j).2 :=
  (SemidirectProduct.inl :
    flowQuotient p G m (tauSucc i j).1 (tauSucc i j).2 →*
      flowGroup p G m (tauSucc i j).1 (tauSucc i j).2).comp
    ((QuotientGroup.mk'
      ((flowTerm p G m (tauSucc i j).1 (tauSucc i j).2).subgroupOf
        (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m)))).comp
      (Subgroup.inclusion (le_top : flowTerm p G m i j ≤ ⊤)))

@[simp] theorem succLiftToGroup_apply (p : ℕ) (G : Type*) [Group G] (m i j : ℕ)
    (s : ↥(flowTerm p G m i j)) :
    succLiftToGroup p G m i j s =
      SemidirectProduct.mk
        (QuotientGroup.mk'
          ((flowTerm p G m (tauSucc i j).1 (tauSucc i j).2).subgroupOf ⊤)
          ⟨(s : Work.Shrinking.freeOperatorGroup G m), Subgroup.mem_top _⟩) 1 := rfl

/-- The element of the free factor determined by `s ∈ F(m)^{(τ)}` lies in the kernel of the
projection. -/
theorem succLiftToGroup_mem_ker (p : ℕ) (G : Type*) [Group G] (m i j : ℕ)
    (s : ↥(flowTerm p G m i j)) :
    succLiftToGroup p G m i j s ∈ (flowGroupSucc p G m i j).ker := by
  rw [MonoidHom.mem_ker, succLiftToGroup_apply, flowGroupSucc_mk, flowQuotSucc_mk]
  apply SemidirectProduct.ext
  · change (QuotientGroup.mk'
        ((flowTerm p G m i j).subgroupOf
          (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m)))
        ⟨(s : Work.Shrinking.freeOperatorGroup G m), Subgroup.mem_top _⟩ :
          flowQuotient p G m i j) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact s.2
  · change (1 : G) = 1
    rfl

/-- The map `F(m)^{(τ)} →* ker (flowGroupSucc p G m i j)` sending `s` to the class of `s` in
`F(m)/F(m)^{(τ+1)} ⋊ G` (which is in the kernel because `s ∈ F(m)^{(τ)}`). -/
noncomputable def succKerMap (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) :
    ↥(flowTerm p G m i j) →* ↥(flowGroupSucc p G m i j).ker :=
  MonoidHom.codRestrict (succLiftToGroup p G m i j) (flowGroupSucc p G m i j).ker
    (succLiftToGroup_mem_ker p G m i j)

@[simp] theorem succKerMap_apply (p : ℕ) (G : Type*) [Group G] (m i j : ℕ)
    (s : ↥(flowTerm p G m i j)) :
    ((succKerMap p G m i j s : ↥(flowGroupSucc p G m i j).ker) :
        flowGroup p G m (tauSucc i j).1 (tauSucc i j).2) = succLiftToGroup p G m i j s := rfl

/-- The kernel of `succKerMap` is the next term of the refined filtration, so that the graded
piece `E(m,τ)` is the quotient `F(m)^{(τ)}/F(m)^{(τ+1)}`. -/
theorem succKerMap_ker (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) :
    (succKerMap p G m i j).ker =
      (flowTerm p G m (tauSucc i j).1 (tauSucc i j).2).subgroupOf (flowTerm p G m i j) := by
  ext s
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    have h1 : succLiftToGroup p G m i j s = 1 := by
      have := congrArg Subtype.val h
      simpa using this
    have h2 := congrArg SemidirectProduct.left h1
    simp only [succLiftToGroup_apply, SemidirectProduct.one_left] at h2
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h2
    exact h2
  · intro hs
    apply Subtype.ext
    have h1 : succLiftToGroup p G m i j s = 1 := by
      apply SemidirectProduct.ext
      · change (QuotientGroup.mk'
            ((flowTerm p G m (tauSucc i j).1 (tauSucc i j).2).subgroupOf
              (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m)))
            ⟨(s : Work.Shrinking.freeOperatorGroup G m), Subgroup.mem_top _⟩ :
              flowQuotient p G m (tauSucc i j).1 (tauSucc i j).2) = 1
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        exact hs
      · change (1 : G) = 1
        rfl
    simpa using h1

/-- Every element of the kernel of the projection is the class of an element of `F(m)^{(τ)}`. -/
theorem succKerMap_surjective (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) :
    Function.Surjective (succKerMap p G m i j) := by
  intro y
  set Y : flowGroup p G m (tauSucc i j).1 (tauSucc i j).2 :=
    (y : flowGroup p G m (tauSucc i j).1 (tauSucc i j).2) with hY
  have hy : flowGroupSucc p G m i j Y = 1 := y.2
  have hYr : Y.right = (1 : G) := by
    have := congrArg SemidirectProduct.right hy
    simpa using this
  have hYl : flowQuotSucc p G m i j Y.left = 1 := by
    have := congrArg SemidirectProduct.left hy
    simpa using this
  obtain ⟨r, hr⟩ := QuotientGroup.mk'_surjective
    ((flowTerm p G m (tauSucc i j).1 (tauSucc i j).2).subgroupOf
      (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m))) Y.left
  have hrS : (r : Work.Shrinking.freeOperatorGroup G m) ∈ flowTerm p G m i j := by
    rw [← hr, flowQuotSucc_mk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at hYl
    exact hYl
  refine ⟨⟨(r : Work.Shrinking.freeOperatorGroup G m), hrS⟩, ?_⟩
  apply Subtype.ext
  apply SemidirectProduct.ext
  · change (QuotientGroup.mk'
        ((flowTerm p G m (tauSucc i j).1 (tauSucc i j).2).subgroupOf
          (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m)))
        ⟨(r : Work.Shrinking.freeOperatorGroup G m), Subgroup.mem_top _⟩ :
          flowQuotient p G m (tauSucc i j).1 (tauSucc i j).2) = Y.left
    rw [← hr]
  · change (1 : G) = Y.right
    rw [hYr]

/-! ## Equivariance and naturality of `succKerMap` -/

/-- The descended `G`-action on the level-`τ+1` quotient, computed on the class of an element of
`F(m)^{(τ)}`. -/
theorem flowAction_mk_of_subAut (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) (g : G)
    (s : ↥(flowTerm p G m i j)) :
    flowAction p G m (tauSucc i j).1 (tauSucc i j).2 g
        (QuotientGroup.mk'
          ((flowTerm p G m (tauSucc i j).1 (tauSucc i j).2).subgroupOf
            (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m)))
          ⟨(s : Work.Shrinking.freeOperatorGroup G m), Subgroup.mem_top _⟩)
      = QuotientGroup.mk'
          ((flowTerm p G m (tauSucc i j).1 (tauSucc i j).2).subgroupOf
            (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m)))
          ⟨(Work.Shrinking.subAut (flowTerm p G m i j) g
              (map_refinedTerm_eq p (MulDistribMulAction.toMulAut G
                (Work.Shrinking.freeOperatorGroup G m) g) i j) s :
              Work.Shrinking.freeOperatorGroup G m), Subgroup.mem_top _⟩ := by
  have htop : (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m)).map
      (MulDistribMulAction.toMulAut G (Work.Shrinking.freeOperatorGroup G m) g).toMonoidHom
      = ⊤ :=
    Subgroup.map_top_of_surjective _ (MulDistribMulAction.toMulAut G _ g).surjective
  have hT : (flowTerm p G m (tauSucc i j).1 (tauSucc i j).2).map
      (MulDistribMulAction.toMulAut G (Work.Shrinking.freeOperatorGroup G m) g).toMonoidHom
      = flowTerm p G m (tauSucc i j).1 (tauSucc i j).2 :=
    map_refinedTerm_eq p (MulDistribMulAction.toMulAut G _ g) _ _
  change Work.Shrinking.quotAut ⊤ (flowTerm p G m (tauSucc i j).1 (tauSucc i j).2) g htop hT
    (QuotientGroup.mk' _ ⟨(s : Work.Shrinking.freeOperatorGroup G m), Subgroup.mem_top _⟩) = _
  rw [Work.Shrinking.quotAut_mk]
  exact congrArg (QuotientGroup.mk' _) (Subtype.ext (by
    rw [Work.Shrinking.subAut_coe, Work.Shrinking.subAut_coe]))

/-- `succKerMap` is equivariant for the conjugation action of `G` on the kernel. -/
theorem succKerMap_subAut (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) (g : G)
    (s : ↥(flowTerm p G m i j)) :
    succKerMap p G m i j
        (Work.Shrinking.subAut (flowTerm p G m i j) g
          (map_refinedTerm_eq p (MulDistribMulAction.toMulAut G
            (Work.Shrinking.freeOperatorGroup G m) g) i j) s)
      = Work.AbsoluteGalois.conjKernelMul (flowGroupSucc p G m i j)
          (SemidirectProduct.mk (1 : flowQuotient p G m (tauSucc i j).1 (tauSucc i j).2) g)
          (succKerMap p G m i j s) := by
  apply Subtype.ext
  change succLiftToGroup p G m i j
      (Work.Shrinking.subAut (flowTerm p G m i j) g
        (map_refinedTerm_eq p (MulDistribMulAction.toMulAut G
          (Work.Shrinking.freeOperatorGroup G m) g) i j) s)
    = SemidirectProduct.mk (1 : flowQuotient p G m (tauSucc i j).1 (tauSucc i j).2) g
      * succLiftToGroup p G m i j s
      * (SemidirectProduct.mk (1 : flowQuotient p G m (tauSucc i j).1 (tauSucc i j).2) g)⁻¹
  rw [succLiftToGroup_apply, succLiftToGroup_apply,
    semidirect_mk_conj (flowAction p G m (tauSucc i j).1 (tauSucc i j).2)
      (1 : flowQuotient p G m (tauSucc i j).1 (tauSucc i j).2) _ g]
  rw [flowAction_mk_of_subAut p G m i j g s]
  simp

/-- `succKerMap` is natural in the rank: the rank-change map `flowGroupMap` restricts to the
kernels, and on `F(m)^{(τ)}` it is the induced map on the graded pieces. -/
theorem succKerMap_naturality (p : ℕ) (G : Type*) [Group G] (i j : ℕ) {m n : ℕ}
    (Φ : OperatorMap G m n) (s : ↥(flowTerm p G m i j)) :
    flowGroupSuccKernelMap p G i j Φ (succKerMap p G m i j s)
      = succKerMap p G n i j (refinedMap p Φ.toHom Φ.surjective i j s) := by
  apply Subtype.ext
  apply SemidirectProduct.ext
  · change (flowGroupMap p G (tauSucc i j).1 (tauSucc i j).2 Φ
        (succLiftToGroup p G m i j s)).left
      = (succLiftToGroup p G n i j (refinedMap p Φ.toHom Φ.surjective i j s)).left
    rw [flowGroupMap_left, succLiftToGroup_apply, succLiftToGroup_apply, flowQuotMap_mk,
      refinedMap_coe]
  · change (flowGroupMap p G (tauSucc i j).1 (tauSucc i j).2 Φ
        (succLiftToGroup p G m i j s)).right
      = (succLiftToGroup p G n i j (refinedMap p Φ.toHom Φ.surjective i j s)).right
    rw [flowGroupMap_right, succLiftToGroup_apply, succLiftToGroup_apply]

/-! ## The isomorphism `E(m,τ) ≃* ker (flowGroupSucc p G m i j)` -/

/-- The map on the graded piece induced by `succKerMap` (first isomorphism theorem). -/
noncomputable def succKerLift (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) :
    refinedQuotient p (Work.Shrinking.freeOperatorGroup G m) i j →*
      ↥(flowGroupSucc p G m i j).ker :=
  QuotientGroup.lift
    ((flowTerm p G m (tauSucc i j).1 (tauSucc i j).2).subgroupOf (flowTerm p G m i j))
    (succKerMap p G m i j)
    (by rw [succKerMap_ker])

theorem succKerLift_mk (p : ℕ) (G : Type*) [Group G] (m i j : ℕ)
    (s : ↥(flowTerm p G m i j)) :
    succKerLift p G m i j
        (QuotientGroup.mk'
          ((flowTerm p G m (tauSucc i j).1 (tauSucc i j).2).subgroupOf
            (flowTerm p G m i j)) s)
      = succKerMap p G m i j s := by
  rw [QuotientGroup.mk'_apply]
  exact QuotientGroup.lift_mk' _ _ s

theorem succKerLift_injective (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) :
    Function.Injective (succKerLift p G m i j) := by
  intro a b hab
  obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective
    ((flowTerm p G m (tauSucc i j).1 (tauSucc i j).2).subgroupOf (flowTerm p G m i j)) a
  obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective
    ((flowTerm p G m (tauSucc i j).1 (tauSucc i j).2).subgroupOf (flowTerm p G m i j)) b
  rw [succKerLift_mk, succKerLift_mk] at hab
  have h2 : succKerMap p G m i j (s * t⁻¹) = 1 := by
    rw [map_mul, map_inv, hab, mul_inv_cancel]
  have h3 : s / t ∈ (succKerMap p G m i j).ker := by
    rw [MonoidHom.mem_ker, div_eq_mul_inv]
    exact h2
  rw [succKerMap_ker] at h3
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply]
  exact QuotientGroup.eq_iff_div_mem.mpr h3

theorem succKerLift_surjective (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) :
    Function.Surjective (succKerLift p G m i j) := by
  intro y
  obtain ⟨s, hs⟩ := succKerMap_surjective p G m i j y
  exact ⟨QuotientGroup.mk'
    ((flowTerm p G m (tauSucc i j).1 (tauSucc i j).2).subgroupOf (flowTerm p G m i j)) s,
    by rw [succKerLift_mk, hs]⟩

/-- **The graded piece is the kernel of the projection.**  The canonical identification
`E(m,τ) = F(m)^{(τ)}/F(m)^{(τ+1)} ≃* ker (flowGroupSucc p G m i j)`. -/
noncomputable def succKerIso (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) :
    refinedQuotient p (Work.Shrinking.freeOperatorGroup G m) i j ≃*
      ↥(flowGroupSucc p G m i j).ker :=
  MulEquiv.ofBijective (succKerLift p G m i j)
    ⟨succKerLift_injective p G m i j, succKerLift_surjective p G m i j⟩

theorem succKerIso_mk (p : ℕ) (G : Type*) [Group G] (m i j : ℕ)
    (s : ↥(flowTerm p G m i j)) :
    succKerIso p G m i j
        (QuotientGroup.mk'
          ((flowTerm p G m (tauSucc i j).1 (tauSucc i j).2).subgroupOf
            (flowTerm p G m i j)) s)
      = succKerMap p G m i j s := by
  show succKerLift p G m i j
      (QuotientGroup.mk'
        ((flowTerm p G m (tauSucc i j).1 (tauSucc i j).2).subgroupOf
          (flowTerm p G m i j)) s) = succKerMap p G m i j s
  exact succKerLift_mk p G m i j s

/-- The identification `E(m,τ) ≃* ker (flowGroupSucc p G m i j)` is `G`-equivariant. -/
theorem succKerIso_smul (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) (g : G)
    (x : refinedQuotient p (Work.Shrinking.freeOperatorGroup G m) i j) :
    succKerIso p G m i j (g • x)
      = Work.AbsoluteGalois.conjKernelMul (flowGroupSucc p G m i j)
          (SemidirectProduct.mk (1 : flowQuotient p G m (tauSucc i j).1 (tauSucc i j).2) g)
          (succKerIso p G m i j x) := by
  obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective
    ((flowTerm p G m (tauSucc i j).1 (tauSucc i j).2).subgroupOf (flowTerm p G m i j)) x
  rw [succKerIso_mk]
  have hsub : g • (QuotientGroup.mk'
        ((flowTerm p G m (tauSucc i j).1 (tauSucc i j).2).subgroupOf
          (flowTerm p G m i j)) s)
      = QuotientGroup.mk'
        ((flowTerm p G m (tauSucc i j).1 (tauSucc i j).2).subgroupOf (flowTerm p G m i j))
        (Work.Shrinking.subAut (flowTerm p G m i j) g
          (map_refinedTerm_eq p (MulDistribMulAction.toMulAut G
            (Work.Shrinking.freeOperatorGroup G m) g) i j) s) := by
    change Work.Shrinking.quotAut
      (refinedTerm p (Work.Shrinking.freeOperatorGroup G m) i j)
      (refinedTerm p (Work.Shrinking.freeOperatorGroup G m)
        (tauSucc i j).1 (tauSucc i j).2) g
      (map_refinedTerm_eq p (MulDistribMulAction.toMulAut G
        (Work.Shrinking.freeOperatorGroup G m) g) i j)
      (map_refinedTerm_eq p (MulDistribMulAction.toMulAut G
        (Work.Shrinking.freeOperatorGroup G m) g) (tauSucc i j).1 (tauSucc i j).2)
      (QuotientGroup.mk' _ s) = _
    rw [Work.Shrinking.quotAut_mk]
  rw [hsub, succKerIso_mk, succKerMap_subAut]

/-- The identification `E(m,τ) ≃* ker (flowGroupSucc p G m i j)` is natural in the rank. -/
theorem succKerIso_naturality (p : ℕ) (G : Type*) [Group G] (i j : ℕ) {m n : ℕ}
    (Φ : OperatorMap G m n)
    (x : refinedQuotient p (Work.Shrinking.freeOperatorGroup G m) i j) :
    flowGroupSuccKernelMap p G i j Φ (succKerIso p G m i j x)
      = succKerIso p G n i j (gradedMapMul p Φ.toHom Φ.surjective i j x) := by
  obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective
    ((flowTerm p G m (tauSucc i j).1 (tauSucc i j).2).subgroupOf (flowTerm p G m i j)) x
  rw [succKerIso_mk, gradedMapMul_of, succKerIso_mk]
  exact succKerMap_naturality p G i j Φ s

/-! ## The additive form of the identification -/

/-- The additive equivalence `Additive (ker π) ≃+ E(m,τ)` underlying the lemma: it is the inverse
of `succKerIso`. -/
theorem succKerAddEquiv_symm_apply (p : ℕ) (G : Type*) [Group G] (m i j : ℕ)
    (x : Additive ↥(flowGroupSucc p G m i j).ker) :
    (succKerIso p G m i j).toAdditive.symm x
      = Additive.ofMul ((succKerIso p G m i j).symm (Additive.toMul x)) := rfl

/-- The scalar multiplication on `E(m,τ) = Additive (refinedQuotient …)`, computed on
`Additive.ofMul`. -/
theorem smul_additive_apply (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) (g : G)
    (y : refinedQuotient p (Work.Shrinking.freeOperatorGroup G m) i j) :
    g • (Additive.ofMul y : E p G m i j) = Additive.ofMul (g • y) := rfl

/-- The `𝔽_p`-linear map on the graded pieces, computed on `Additive.ofMul`. -/
theorem gradedMapLin_apply (p : ℕ) (G : Type*) [Group G] (i j : ℕ) {m n : ℕ}
    (Φ : OperatorMap G m n) (y : E p G m i j) :
    gradedMapLin p Φ.toHom Φ.surjective i j y
      = Additive.ofMul (gradedMapMul p Φ.toHom Φ.surjective i j (Additive.toMul y)) := rfl

theorem exists_kerSuccAddEquiv_equivariant (p : ℕ) (G : Type*) [Group G] [Fintype G]
    (i j m n : ℕ) (Φ : Work.CohomologicalShrinking.OperatorMap G m n) :
    ∃ (e : Additive ↥(Work.SSGRoute.flowGroupSucc p G m i j).ker ≃+
          Work.CohomologicalShrinking.E p G m i j)
      (e' : Additive ↥(Work.SSGRoute.flowGroupSucc p G n i j).ker ≃+
          Work.CohomologicalShrinking.E p G n i j),
      (∀ (g : G) (x : Additive ↥(Work.SSGRoute.flowGroupSucc p G m i j).ker),
          e (Additive.ofMul (Work.AbsoluteGalois.conjKernelMul (Work.SSGRoute.flowGroupSucc p G m i j)
            ((SemidirectProduct.mk 1 g : Work.CohomologicalShrinking.flowGroup p G m
              (Work.CohomologicalShrinking.tauSucc i j).1
              (Work.CohomologicalShrinking.tauSucc i j).2)) (Additive.toMul x))) = g • e x)
      ∧ (∀ (g : G) (x : Additive ↥(Work.SSGRoute.flowGroupSucc p G n i j).ker),
          e' (Additive.ofMul (Work.AbsoluteGalois.conjKernelMul (Work.SSGRoute.flowGroupSucc p G n i j)
            ((SemidirectProduct.mk 1 g : Work.CohomologicalShrinking.flowGroup p G n
              (Work.CohomologicalShrinking.tauSucc i j).1
              (Work.CohomologicalShrinking.tauSucc i j).2)) (Additive.toMul x))) = g • e' x)
      ∧ (∀ x : ↥(Work.SSGRoute.flowGroupSucc p G m i j).ker,
          e' (Additive.ofMul (Work.SSGRoute.flowGroupSuccKernelMap p G i j Φ x))
            = Work.CohomologicalShrinking.gradedMapLin p Φ.toHom Φ.surjective i j
                (e (Additive.ofMul x))) := by
  refine ⟨(succKerIso p G m i j).toAdditive.symm, (succKerIso p G n i j).toAdditive.symm,
    ?_, ?_, ?_⟩
  · intro g x
    have h := succKerIso_smul p G m i j g ((succKerIso p G m i j).symm (Additive.toMul x))
    rw [MulEquiv.apply_symm_apply] at h
    have h2 : (succKerIso p G m i j).symm
        (Work.AbsoluteGalois.conjKernelMul (flowGroupSucc p G m i j)
          (SemidirectProduct.mk (1 : flowQuotient p G m (tauSucc i j).1 (tauSucc i j).2) g)
          (Additive.toMul x))
        = g • (succKerIso p G m i j).symm (Additive.toMul x) := by
      have h3 := congrArg (succKerIso p G m i j).symm h
      rw [MulEquiv.symm_apply_apply] at h3
      exact h3.symm
    rw [succKerAddEquiv_symm_apply, succKerAddEquiv_symm_apply, smul_additive_apply,
      toMul_ofMul]
    exact congrArg Additive.ofMul h2
  · intro g x
    have h := succKerIso_smul p G n i j g ((succKerIso p G n i j).symm (Additive.toMul x))
    rw [MulEquiv.apply_symm_apply] at h
    have h2 : (succKerIso p G n i j).symm
        (Work.AbsoluteGalois.conjKernelMul (flowGroupSucc p G n i j)
          (SemidirectProduct.mk (1 : flowQuotient p G n (tauSucc i j).1 (tauSucc i j).2) g)
          (Additive.toMul x))
        = g • (succKerIso p G n i j).symm (Additive.toMul x) := by
      have h3 := congrArg (succKerIso p G n i j).symm h
      rw [MulEquiv.symm_apply_apply] at h3
      exact h3.symm
    rw [succKerAddEquiv_symm_apply, succKerAddEquiv_symm_apply, smul_additive_apply,
      toMul_ofMul]
    exact congrArg Additive.ofMul h2
  · intro x
    have h := succKerIso_naturality p G i j Φ ((succKerIso p G m i j).symm (Additive.toMul x))
    rw [MulEquiv.apply_symm_apply] at h
    have h2 : (succKerIso p G n i j).symm
        (flowGroupSuccKernelMap p G i j Φ (Additive.toMul x))
        = gradedMapMul p Φ.toHom Φ.surjective i j
            ((succKerIso p G m i j).symm (Additive.toMul x)) := by
      have h3 := congrArg (succKerIso p G n i j).symm h
      rw [MulEquiv.symm_apply_apply] at h3
      exact h3
    rw [succKerAddEquiv_symm_apply, succKerAddEquiv_symm_apply, gradedMapLin_apply,
      toMul_ofMul, toMul_ofMul]
    exact congrArg Additive.ofMul h2

end Work.SSGRoute
