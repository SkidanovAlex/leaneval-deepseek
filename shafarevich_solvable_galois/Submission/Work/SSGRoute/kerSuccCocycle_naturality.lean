import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Tactic.Group
import Mathlib.GroupTheory.FreeGroup.Basic
import Submission.Work.SSGRoute.FlowGroupSuccDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open Work.CohomologicalShrinking

open scoped commutatorElement

/-! ## The kernel of the projection `flowGroupSucc` is commutative

The kernel of `flowGroupSucc p G m i j : Γ(τ+1) →* Γ(τ)` is (isomorphic to) the graded piece
`F(m)_{(i,j)}/F(m)_{(τ+1)} = E(m,τ)` of the refined `p`-central filtration, which is an
elementary abelian `p`-group.  These two lemmas record the resulting commutativity, which is
what makes the section `2`-cocycle `kerSuccCocycle` well behaved. -/

/-- The kernel of `flowQuotSucc` is commutative: it is the image of the refined term
`F(m)_{(i,j)}` in `F(m)/F(m)_{(τ+1)}`, and the commutator of that term lies in `F(m)_{(τ+1)}`
(Lemma 4 of Schmidt–Wingberg). -/
theorem flowQuotSucc_ker_isMulCommutative (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) :
    IsMulCommutative ↥(flowQuotSucc p G m i j).ker := by
  rw [flowQuotSucc, QuotientGroup.ker_map, Subgroup.comap_id]
  rw [← Subgroup.commutator_self_eq_bot_iff, ← Subgroup.map_commutator]
  rw [(Subgroup.map_eq_bot_iff _)]
  rw [QuotientGroup.ker_mk']
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [Subgroup.mem_subgroupOf]
  exact commutator_refinedTerm_le p i j (Subgroup.commutator_mem_commutator hx hy)

/-- The kernel of the projection `flowGroupSucc p G m i j` is commutative. -/
theorem flowGroupSucc_ker_isMulCommutative (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) :
    IsMulCommutative ↥(flowGroupSucc p G m i j).ker := by
  have h2 : IsMulCommutative ↥(flowQuotSucc p G m i j).ker :=
    flowQuotSucc_ker_isMulCommutative p G m i j
  refine ⟨⟨fun a b => ?_⟩⟩
  have har : (a : flowGroup p G m (tauSucc i j).1 (tauSucc i j).2).right = 1 := by
    have h := congrArg SemidirectProduct.right a.2
    simpa using h
  have hbr : (b : flowGroup p G m (tauSucc i j).1 (tauSucc i j).2).right = 1 := by
    have h := congrArg SemidirectProduct.right b.2
    simpa using h
  have hal : flowQuotSucc p G m i j
      (a : flowGroup p G m (tauSucc i j).1 (tauSucc i j).2).left = 1 := by
    have h := congrArg SemidirectProduct.left a.2
    simpa using h
  have hbl : flowQuotSucc p G m i j
      (b : flowGroup p G m (tauSucc i j).1 (tauSucc i j).2).left = 1 := by
    have h := congrArg SemidirectProduct.left b.2
    simpa using h
  apply Subtype.ext
  apply SemidirectProduct.ext
  · simp only [Subgroup.coe_mul, SemidirectProduct.mul_left, har, hbr, map_one, MulAut.one_apply]
    exact congrArg Subtype.val (h2.is_comm.comm
      (⟨_, hal⟩ : ↥(flowQuotSucc p G m i j).ker)
      (⟨_, hbl⟩ : ↥(flowQuotSucc p G m i j).ker))
  · simp only [Subgroup.coe_mul, SemidirectProduct.mul_right, har, hbr, mul_one]

/-! ## Naturality of the section cocycle -/

/-- The abstract group-theoretic core of the naturality of the section `2`-cocycle of a
surjection with commutative kernel.  For a commutative subgroup `K` of a group `Γ` and elements
`X Y Z α β γ ∈ Γ` whose "differences" `X α⁻¹`, `Y β⁻¹`, `Z γ⁻¹` and `α β γ⁻¹` lie in `K`,

`X Y Z⁻¹ = α β γ⁻¹ · (X (β Y⁻¹) X⁻¹ · (γ Z⁻¹)⁻¹ · α X⁻¹)⁻¹`.

This is the multiplicative form of
`c' = Φ_*(c) - (conj(s'(ρ'σ), β_τ) - β_{στ} + β_σ)` once the section cocycle is written out. -/
private theorem cocycle_nat_aux {Γ : Type*} [Group Γ] (K : Subgroup Γ) [K.Normal]
    (hK : ∀ a b : ↥K, a * b = b * a)
    (X Y Z α β γ : Γ)
    (hX : X * α⁻¹ ∈ K) (hY : Y * β⁻¹ ∈ K) (hZ : Z * γ⁻¹ ∈ K)
    (hΔ : α * β * γ⁻¹ ∈ K) :
    X * Y * Z⁻¹ =
      α * β * γ⁻¹ * (X * (β * Y⁻¹) * X⁻¹ * (γ * Z⁻¹)⁻¹ * (α * X⁻¹))⁻¹ := by
  let u : ↥K := ⟨X * α⁻¹, hX⟩
  let v : ↥K := ⟨Y * β⁻¹, hY⟩
  let w : ↥K := ⟨Z * γ⁻¹, hZ⟩
  let c : ↥K := ⟨α * β * γ⁻¹, hΔ⟩
  have hsmem : α * (v : Γ) * α⁻¹ ∈ K :=
    Subgroup.Normal.conj_mem (inferInstance : K.Normal) (v : Γ) v.2 α
  let s : ↥K := ⟨α * (v : Γ) * α⁻¹, hsmem⟩
  have hu : X = (u : Γ) * α := by show X = X * α⁻¹ * α; group
  have hv : Y = (v : Γ) * β := by show Y = Y * β⁻¹ * β; group
  have hw : Z = (w : Γ) * γ := by show Z = Z * γ⁻¹ * γ; group
  have hc : (c : Γ) = α * β * γ⁻¹ := rfl
  have hγ : γ = (c : Γ)⁻¹ * α * β := by rw [hc]; group
  have hs : (s : Γ) = α * (v : Γ) * α⁻¹ := rfl
  have hconj : ∀ k1 k2 : ↥K, (k1 : Γ) * (k2 : Γ) * (k1 : Γ)⁻¹ = (k2 : Γ) := by
    intro k1 k2
    rw [← Subgroup.coe_mul, ← Subgroup.coe_inv, ← Subgroup.coe_mul]
    congr 1
    rw [hK k1 k2, mul_assoc, mul_inv_cancel, mul_one]
  have hbeta : X * (β * Y⁻¹) * X⁻¹ = (s : Γ)⁻¹ := by
    have e2 : (↑s : Γ)⁻¹ = α * (↑v : Γ)⁻¹ * α⁻¹ := by rw [hs]; group
    rw [hu, hv]
    have e1 : (↑u * α) * (β * (↑v * β)⁻¹) * (↑u * α)⁻¹
        = (↑u : Γ) * (α * (↑v : Γ)⁻¹ * α⁻¹) * (↑u : Γ)⁻¹ := by group
    rw [e1, ← e2, ← Subgroup.coe_inv]
    exact hconj u s⁻¹
  have hgammaz : γ * Z⁻¹ = (w : Γ)⁻¹ := by
    rw [hw, hγ]
    group
  have hαX : α * X⁻¹ = (u : Γ)⁻¹ := by
    rw [hu]; group
  letI : CommGroup ↥K := { toGroup := inferInstance, mul_comm := hK }
  have hL : X * Y * Z⁻¹ = ((u * s * c * w⁻¹ : ↥K) : Γ) := by
    rw [hu, hv, hw, hγ]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hs]
    group
  have hKident : (c : ↥K) * ((s⁻¹ : ↥K) * w * (u⁻¹ : ↥K))⁻¹ = u * s * c * w⁻¹ := by
    simp only [mul_inv_rev, inv_inv]
    ac_rfl
  have hR : α * β * γ⁻¹ * (X * (β * Y⁻¹) * X⁻¹ * (γ * Z⁻¹)⁻¹ * (α * X⁻¹))⁻¹
      = ((u * s * c * w⁻¹ : ↥K) : Γ) := by
    rw [← hc, hbeta, hgammaz, hαX]
    simp only [inv_inv]
    have hcoe : ((↑s : Γ)⁻¹ * ↑w * (↑u : Γ)⁻¹)
        = (↑((s⁻¹ : ↥K) * w * (u⁻¹ : ↥K)) : Γ) := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv]
    rw [hcoe, ← Subgroup.coe_inv, ← Subgroup.coe_mul]
    exact congrArg Subtype.val hKident
  rw [hL, hR]

theorem kerSuccCocycle_naturality (p : ℕ) (G : Type*) [Group G] (m n i j : ℕ)
    (Φ : Work.CohomologicalShrinking.OperatorMap G m n) {H : Type*} [Group H]
    (ρ : H →* Work.CohomologicalShrinking.flowGroup p G m i j)
    (ρ' : H →* Work.CohomologicalShrinking.flowGroup p G n i j)
    (hρ : ∀ σ : H, ρ' σ = Work.CohomologicalShrinking.flowGroupMap p G i j Φ (ρ σ))
    (s : Work.CohomologicalShrinking.flowGroup p G m i j →
      Work.CohomologicalShrinking.flowGroup p G m (Work.CohomologicalShrinking.tauSucc i j).1
        (Work.CohomologicalShrinking.tauSucc i j).2)
    (hs : ∀ x, Work.SSGRoute.flowGroupSucc p G m i j (s x) = x)
    (s' : Work.CohomologicalShrinking.flowGroup p G n i j →
      Work.CohomologicalShrinking.flowGroup p G n (Work.CohomologicalShrinking.tauSucc i j).1
        (Work.CohomologicalShrinking.tauSucc i j).2)
    (hs' : ∀ x, Work.SSGRoute.flowGroupSucc p G n i j (s' x) = x)
    (σ τ : H) :
    Work.SSGRoute.kerSuccCocycle p G n i j ρ' s' hs' σ τ =
      Additive.ofMul (Work.SSGRoute.flowGroupSuccKernelMap p G i j Φ
          (Work.SSGRoute.kerSuccCocycleMul p G m i j ρ s hs σ τ))
        - (Additive.ofMul (Work.AbsoluteGalois.conjKernelMul (Work.SSGRoute.flowGroupSucc p G n i j)
              (s' (ρ' σ)) (Work.SSGRoute.kerSuccBeta p G i j Φ ρ ρ' hρ s s' hs hs' τ))
            - Additive.ofMul (Work.SSGRoute.kerSuccBeta p G i j Φ ρ ρ' hρ s s' hs hs' (σ * τ))
            + Additive.ofMul (Work.SSGRoute.kerSuccBeta p G i j Φ ρ ρ' hρ s s' hs hs' σ)) := by
  have hcomm : IsMulCommutative ↥(flowGroupSucc p G n i j).ker :=
    flowGroupSucc_ker_isMulCommutative p G n i j
  apply Additive.ext
  simp only [toMul_sub, toMul_add, toMul_ofMul, div_eq_mul_inv]
  apply Subtype.ext
  simp only [kerSuccCocycle, toMul_ofMul, kerSuccCocycleMul, flowGroupSuccKernelMap_apply,
    kerSuccBeta, Work.AbsoluteGalois.conjKernelMul, Subtype.coe_mk, Subgroup.coe_mul,
    Subgroup.coe_inv, map_mul, map_inv]
  have hΔs : ∀ x : flowGroup p G m i j,
      flowGroupSucc p G n i j
          ((flowGroupMap p G (tauSucc i j).1 (tauSucc i j).2 Φ) (s x))
        = (flowGroupMap p G i j Φ) x := by
    intro x
    have h := DFunLike.congr_fun (flowGroupSucc_flowGroupMap p G i j Φ) (s x)
    simpa only [MonoidHom.comp_apply, hs x] using h
  have hZT : (flowGroupMap p G i j Φ) (ρ σ * ρ τ) = ρ' σ * ρ' τ := by
    rw [map_mul, ← hρ σ, ← hρ τ]
  refine cocycle_nat_aux (flowGroupSucc p G n i j).ker (fun a b => hcomm.is_comm.comm a b)
    (s' (ρ' σ)) (s' (ρ' τ)) (s' (ρ' σ * ρ' τ))
    ((flowGroupMap p G (tauSucc i j).1 (tauSucc i j).2 Φ) (s (ρ σ)))
    ((flowGroupMap p G (tauSucc i j).1 (tauSucc i j).2 Φ) (s (ρ τ)))
    ((flowGroupMap p G (tauSucc i j).1 (tauSucc i j).2 Φ) (s (ρ σ * ρ τ)))
    ?_ ?_ ?_ ?_
  · rw [MonoidHom.mem_ker, map_mul, map_inv, hs' (ρ' σ), hΔs (ρ σ), hρ σ]
    exact mul_inv_cancel _
  · rw [MonoidHom.mem_ker, map_mul, map_inv, hs' (ρ' τ), hΔs (ρ τ), hρ τ]
    exact mul_inv_cancel _
  · rw [MonoidHom.mem_ker, map_mul, map_inv, hs' (ρ' σ * ρ' τ), hΔs (ρ σ * ρ τ), hZT]
    exact mul_inv_cancel _
  · rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, hΔs (ρ σ), hΔs (ρ τ),
      hΔs (ρ σ * ρ τ), ← hρ σ, ← hρ τ, hZT]
    exact mul_inv_cancel _

end Work.SSGRoute
