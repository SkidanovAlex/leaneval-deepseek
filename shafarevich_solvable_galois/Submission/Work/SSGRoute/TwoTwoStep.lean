import Mathlib
import Submission.Work.SSGRoute.two_two_graded_pieces
import Submission.Work.SSGRoute.TwoTwoModelDefs
import Submission.Work.SSGRoute.tt_commutator_le_of_generators
import Submission.Work.SSGRoute.tt_detector_props
import Submission.Work.SSGRoute.tt_prod_zmodTwo_val
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open Work.CohomologicalShrinking
open scoped commutatorElement

set_option maxHeartbeats 1000000

instance instNormalFlowTerm31 (G : Type*) [Group G] (n : ℕ) :
    (flowTerm 2 G n 3 1).Normal :=
  refinedTerm_normal 2 _ 3 1

variable {G : Type*} [Group G] [Fintype G] {n : ℕ}

/-- The projection `F(n) → Q_{(3,1)} = F(n)/F(n)^{(3,1)}`. -/
noncomputable def mkQ31 : Work.Shrinking.freeOperatorGroup G n →* flowQuotient 2 G n 3 1 where
  toFun x := QuotientGroup.mk' ((flowTerm 2 G n 3 1).subgroupOf
    (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n))) ⟨x, Subgroup.mem_top x⟩
  map_one' := map_one _
  map_mul' x y := by
    rw [show (⟨x * y, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)))
        = ⟨x, Subgroup.mem_top _⟩ * ⟨y, Subgroup.mem_top _⟩ from rfl, map_mul]

@[simp] theorem mkQ31_apply (x : Work.Shrinking.freeOperatorGroup G n) :
    mkQ31 (G := G) (n := n) x
      = QuotientGroup.mk' ((flowTerm 2 G n 3 1).subgroupOf
          (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)))
        ⟨x, Subgroup.mem_top x⟩ := rfl

theorem mkQ31_surjective : Function.Surjective (mkQ31 (G := G) (n := n)) := by
  intro c
  obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective
    ((flowTerm 2 G n 3 1).subgroupOf (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n))) c
  exact ⟨(a : Work.Shrinking.freeOperatorGroup G n), by rw [mkQ31_apply]; exact ha⟩

/-- The image of the `α`-th free generator of `F(n)` in `Q_{(3,1)}`. -/
noncomputable def xGen (α : Fin n × G) : flowQuotient 2 G n 3 1 :=
  mkQ31 (G := G) (n := n) (FreeGroup.of α)

/-- The image of the commutator `⁅x_α, x_β⁆` in `Q_{(3,1)}`. -/
noncomputable def bPair (α β : Fin n × G) : flowQuotient 2 G n 3 1 :=
  ⁅xGen (G := G) (n := n) α, xGen (G := G) (n := n) β⁆

theorem xGen_generates : Subgroup.closure (Set.range (xGen (G := G) (n := n))) = ⊤ := by
  rw [eq_top_iff]
  intro c _
  obtain ⟨x, rfl⟩ := mkQ31_surjective (G := G) (n := n) c
  have hx : x ∈ Subgroup.closure (Set.range (FreeGroup.of : Fin n × G → _)) := by
    rw [FreeGroup.closure_range_of]
    exact Subgroup.mem_top x
  have hmap : Subgroup.map (mkQ31 (G := G) (n := n))
      (Subgroup.closure (Set.range (FreeGroup.of : Fin n × G → _)))
      = Subgroup.closure (Set.range (xGen (G := G) (n := n))) := by
    rw [MonoidHom.map_closure]
    congr 1
    ext y
    simp only [Set.mem_image, Set.mem_range, xGen]
    constructor
    · rintro ⟨a, ⟨b, rfl⟩, rfl⟩
      exact ⟨b, rfl⟩
    · rintro ⟨b, rfl⟩
      exact ⟨FreeGroup.of b, ⟨b, rfl⟩, rfl⟩
  rw [← hmap]
  exact Subgroup.mem_map_of_mem _ hx

section Structural

local notation "FF" => Work.Shrinking.freeOperatorGroup G n
local notation "QQ" => flowQuotient 2 G n 3 1

theorem powSubgroup_mono {H K : Subgroup FF} (h : H ≤ K) :
    Work.Shrinking.powSubgroup 2 H ≤ Work.Shrinking.powSubgroup 2 K := by
  rw [Work.Shrinking.powSubgroup, Work.Shrinking.powSubgroup, Subgroup.closure_le]
  rintro _ ⟨x, hx, rfl⟩
  exact Subgroup.subset_closure ⟨x, h hx, rfl⟩

/-- `P₃ = F(n)^{(3,1)}` written as the second `p`-central step of `F(n)_2`. -/
theorem flowTerm31_eq :
    flowTerm 2 G n 3 1
      = Work.Shrinking.powSubgroup 2 (pSeries 2 FF 2) ⊔ ⁅pSeries 2 FF 2, (⊤ : Subgroup FF)⁆ := by
  rw [flowTerm, refinedTerm_one, show (3 : ℕ) = 1 + 2 from rfl, pSeries_succ_succ,
    Work.Shrinking.pCentralStep]

theorem commutator_le_pSeries_two : ⁅(⊤ : Subgroup FF), (⊤ : Subgroup FF)⁆ ≤ pSeries 2 FF 2 := by
  rw [show (2 : ℕ) = 0 + 2 from rfl, pSeries_succ_succ, pSeries_one, Work.Shrinking.pCentralStep]
  exact le_sup_right

theorem powSubgroup_commutator_le_P3 :
    Work.Shrinking.powSubgroup 2 ⁅(⊤ : Subgroup FF), (⊤ : Subgroup FF)⁆ ≤ flowTerm 2 G n 3 1 := by
  rw [flowTerm31_eq]
  exact (powSubgroup_mono (commutator_le_pSeries_two (G := G) (n := n))).trans le_sup_left

theorem commutator_commutator_le_P3 :
    ⁅⁅(⊤ : Subgroup FF), (⊤ : Subgroup FF)⁆, (⊤ : Subgroup FF)⁆ ≤ flowTerm 2 G n 3 1 := by
  rw [flowTerm31_eq]
  exact (Subgroup.commutator_mono (commutator_le_pSeries_two (G := G) (n := n)) le_rfl).trans
    le_sup_right

theorem map_mkQ31_P3 : Subgroup.map (mkQ31 (G := G) (n := n)) (flowTerm 2 G n 3 1) = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [Subgroup.mem_bot]
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hv
  rw [mkQ31_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  exact hx

theorem map_commutator_eq : Subgroup.map (mkQ31 (G := G) (n := n))
      ⁅(⊤ : Subgroup FF), (⊤ : Subgroup FF)⁆ = ⁅(⊤ : Subgroup QQ), (⊤ : Subgroup QQ)⁆ := by
  rw [Subgroup.map_commutator,
    Subgroup.map_top_of_surjective _ (mkQ31_surjective (G := G) (n := n))]

theorem commutator_le_center :
    ⁅(⊤ : Subgroup QQ), (⊤ : Subgroup QQ)⁆ ≤ Subgroup.center QQ := by
  rw [← Subgroup.commutator_top_right_eq_bot_iff_le_center]
  have h1 : ⁅⁅(⊤ : Subgroup QQ), (⊤ : Subgroup QQ)⁆, (⊤ : Subgroup QQ)⁆
      = Subgroup.map (mkQ31 (G := G) (n := n))
          ⁅⁅(⊤ : Subgroup FF), (⊤ : Subgroup FF)⁆, (⊤ : Subgroup FF)⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ (mkQ31_surjective (G := G) (n := n))]
  rw [h1]
  exact eq_bot_iff.mpr ((Subgroup.map_mono (commutator_commutator_le_P3 (G := G) (n := n))).trans
    (le_of_eq (map_mkQ31_P3 (G := G) (n := n))))

theorem sq_eq_one_of_mem_commutator {u : QQ} (hu : u ∈ ⁅(⊤ : Subgroup QQ), (⊤ : Subgroup QQ)⁆) :
    u * u = 1 := by
  rw [← map_commutator_eq (G := G) (n := n)] at hu
  obtain ⟨y, hy, hyu⟩ := Subgroup.mem_map.mp hu
  have hy2 : y ^ 2 ∈ Work.Shrinking.powSubgroup 2 ⁅(⊤ : Subgroup FF), (⊤ : Subgroup FF)⁆ :=
    Subgroup.subset_closure ⟨y, hy, rfl⟩
  have hyP : y * y ∈ flowTerm 2 G n 3 1 := by
    rw [(pow_two y).symm]
    exact powSubgroup_commutator_le_P3 (G := G) (n := n) hy2
  rw [← hyu, ← map_mul, mkQ31_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf]
  exact hyP

end Structural

section Structure2

local notation "FF" => Work.Shrinking.freeOperatorGroup G n
local notation "QQ" => flowQuotient 2 G n 3 1

/-- The action of `G` on `Q_{(3,1)}` in terms of the projection `mkQ31`. -/
theorem flowAction_mkQ31 (g : G) (x : FF) :
    flowAction 2 G n 3 1 g (mkQ31 (G := G) (n := n) x)
      = mkQ31 (G := G) (n := n) (g • x) := by
  have hH : ∀ g' : G, Subgroup.map (MulDistribMulAction.toMulAut G FF g').toMonoidHom
      (⊤ : Subgroup FF) = ⊤ :=
    fun g' => Subgroup.map_top_of_surjective _ (MulDistribMulAction.toMulAut G FF g').surjective
  have hK : ∀ g' : G, Subgroup.map (MulDistribMulAction.toMulAut G FF g').toMonoidHom
      (flowTerm 2 G n 3 1) = flowTerm 2 G n 3 1 :=
    fun g' => map_refinedTerm_eq 2 (MulDistribMulAction.toMulAut G FF g') 3 1
  have key : (Work.Shrinking.subAut (⊤ : Subgroup FF) g (hH g) ⟨x, Subgroup.mem_top x⟩ :
        ↥(⊤ : Subgroup FF)) = ⟨g • x, Subgroup.mem_top _⟩ :=
    Subtype.ext (Work.Shrinking.subAut_coe (⊤ : Subgroup FF) g (hH g) ⟨x, Subgroup.mem_top x⟩)
  rw [mkQ31_apply]
  change Work.Shrinking.quotAut (⊤ : Subgroup FF) (flowTerm 2 G n 3 1) g (hH g) (hK g)
      (QuotientGroup.mk' _ ⟨x, Subgroup.mem_top x⟩) = _
  rw [Work.Shrinking.quotAut_mk, key, mkQ31_apply]

theorem flowAction_xGen (g : G) (α : Fin n × G) :
    flowAction 2 G n 3 1 g (xGen (G := G) (n := n) α)
      = xGen (G := G) (n := n) (α.1, g * α.2) := by
  simp only [xGen]
  rw [flowAction_mkQ31, Work.Shrinking.smul_freeOperator_of]

/-- The commutator subgroup of `Q_{(3,1)}` is generated by the images of the pair commutators. -/
theorem commutator_eq_closure_bPair :
    ⁅(⊤ : Subgroup QQ), (⊤ : Subgroup QQ)⁆
      = Subgroup.closure (Set.range (fun p : (Fin n × G) × (Fin n × G) =>
          bPair (G := G) (n := n) p.1 p.2)) := by
  set N : Subgroup QQ := Subgroup.closure (Set.range (fun p : (Fin n × G) × (Fin n × G) =>
      bPair (G := G) (n := n) p.1 p.2)) with hN
  have hNV : N ≤ ⁅(⊤ : Subgroup QQ), (⊤ : Subgroup QQ)⁆ := by
    rw [hN, Subgroup.closure_le]
    rintro _ ⟨p, rfl⟩
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  haveI : N.Normal := ⟨fun x hx g => by
    have hx' := Subgroup.mem_center_iff.mp (commutator_le_center (G := G) (n := n) (hNV hx)) g
    rw [hx', mul_assoc, mul_inv_cancel, mul_one]
    exact hx⟩
  refine le_antisymm ?_ hNV
  refine tt_commutator_le_of_generators (Set.range (xGen (G := G) (n := n)))
    (xGen_generates (G := G) (n := n)) N
    (hNV.trans (commutator_le_center (G := G) (n := n))) ?_
  rintro s ⟨α, rfl⟩ s' ⟨β, rfl⟩
  exact Subgroup.subset_closure ⟨(α, β), rfl⟩

end Structure2

section Psi

local notation "FF" => Work.Shrinking.freeOperatorGroup G n
local notation "QQ" => flowQuotient 2 G n 3 1

variable (δ : G)

/-- The map `e ↦ δ(e)⁻¹ e` on `Q_{(3,1)}`. -/
noncomputable def psi_tts (e : QQ) : QQ := (flowAction 2 G n 3 1 δ e)⁻¹ * e

/-- `psi_tts` is multiplicative as soon as its value on the first factor lies in the commutator
subgroup (which is central). -/
theorem psi_mul {a b : QQ} (ha : psi_tts (G := G) (n := n) δ a ∈ ⁅(⊤ : Subgroup QQ), (⊤ : Subgroup QQ)⁆) :
    psi_tts (G := G) (n := n) δ (a * b) = psi_tts (G := G) (n := n) δ a * psi_tts (G := G) (n := n) δ b := by
  have hc : ∀ x : QQ, ((flowAction 2 G n 3 1 δ a)⁻¹ * a) * x
      = x * ((flowAction 2 G n 3 1 δ a)⁻¹ * a) := by
    intro x
    have h := Subgroup.mem_center_iff.mp (commutator_le_center (G := G) (n := n) ha) x
    rw [psi_tts] at h
    exact h.symm
  simp only [psi_tts, map_mul, mul_inv_rev]
  rw [show (flowAction 2 G n 3 1 δ b)⁻¹ * (flowAction 2 G n 3 1 δ a)⁻¹ * (a * b)
      = (flowAction 2 G n 3 1 δ b)⁻¹
        * (((flowAction 2 G n 3 1 δ a)⁻¹ * a) * b) from by group,
    hc b,
    show (flowAction 2 G n 3 1 δ b)⁻¹ * (b * ((flowAction 2 G n 3 1 δ a)⁻¹ * a))
      = ((flowAction 2 G n 3 1 δ b)⁻¹ * b) * ((flowAction 2 G n 3 1 δ a)⁻¹ * a) from by group,
    hc ((flowAction 2 G n 3 1 δ b)⁻¹ * b)]

/-- For an element of the commutator subgroup, `psi_tts v = δ v * v`. -/
theorem psi_of_mem_commutator {v : QQ} (hv : v ∈ ⁅(⊤ : Subgroup QQ), (⊤ : Subgroup QQ)⁆) :
    psi_tts (G := G) (n := n) δ v = flowAction 2 G n 3 1 δ v * v := by
  have hv2 : v * v = 1 := sq_eq_one_of_mem_commutator (G := G) (n := n) hv
  have hv2' : flowAction 2 G n 3 1 δ v * flowAction 2 G n 3 1 δ v = 1 := by
    rw [← map_mul (flowAction 2 G n 3 1 δ) v v, hv2, map_one]
  rw [psi_tts, inv_eq_of_mul_eq_one_right hv2']

/-- The witness for the "diagonal" pair `{α, δ α}`. -/
theorem psi_short (hδ : δ * δ = 1) (α : Fin n × G) :
    psi_tts (G := G) (n := n) δ
        ((xGen (G := G) (n := n) α)⁻¹ * (xGen (G := G) (n := n) (α.1, δ * α.2))⁻¹)
      = bPair (G := G) (n := n) α (α.1, δ * α.2) := by
  have h1 : flowAction 2 G n 3 1 δ
        ((xGen (G := G) (n := n) α)⁻¹ * (xGen (G := G) (n := n) (α.1, δ * α.2))⁻¹)
      = (xGen (G := G) (n := n) (α.1, δ * α.2))⁻¹ * (xGen (G := G) (n := n) α)⁻¹ := by
    rw [map_mul, map_inv, map_inv, flowAction_xGen, flowAction_xGen,
      show ((α.1, δ * α.2).1, δ * (α.1, δ * α.2).2) = α from by
        refine Prod.ext rfl ?_
        show δ * (δ * α.2) = α.2
        rw [← mul_assoc, hδ, one_mul]]
  rw [psi_tts, h1, bPair]
  simp only [mul_inv_rev, inv_inv]
  group

end Psi

section Coords

open Classical

attribute [local instance] Classical.propDecidable

local notation "FF" => Work.Shrinking.freeOperatorGroup G n
local notation "QQ" => flowQuotient 2 G n 3 1

/-- The commutator subgroup `V = ⁅⊤,⊤⁆` of `Q_{(3,1)}`. -/
noncomputable abbrev V : Subgroup QQ := ⁅(⊤ : Subgroup QQ), (⊤ : Subgroup QQ)⁆

theorem bPair_mem_V (α β : Fin n × G) :
    bPair (G := G) (n := n) α β ∈ V (G := G) (n := n) :=
  Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem mul_comm_of_mem_V (a b : ↥(V (G := G) (n := n))) : a * b = b * a := by
  refine Subtype.ext ?_
  have h := Subgroup.mem_center_iff.mp (commutator_le_center (G := G) (n := n) a.2) (b : QQ)
  exact h.symm

noncomputable instance instCommGroupV (G : Type*) [Group G] [Fintype G] (n : ℕ) :
    CommGroup ↥(V (G := G) (n := n)) :=
  { (inferInstance : Group ↥(V (G := G) (n := n))) with
      mul_comm := mul_comm_of_mem_V (G := G) (n := n) }

variable (δ : G)

/-- The permutation `(i,h) ↦ (i, δ h)` of the index set of the free generators of `F(n)`. -/
noncomputable abbrev sigPerm : (Fin n × G) ≃ (Fin n × G) := Work.Shrinking.freeOperatorGenPerm n δ

@[simp] theorem sigPerm_apply (α : Fin n × G) :
    sigPerm (G := G) (n := n) δ α = (α.1, δ * α.2) := rfl

/-- A concrete identification of the index set with `Fin _`, used to choose representatives of
unordered pairs. -/
noncomputable def eI : (Fin n × G) ≃ Fin (Fintype.card (Fin n × G)) :=
  Fintype.equivFin (Fin n × G)

/-- The index set of unordered pairs of generators, represented by the ordered pair whose first
component is `eI`-smaller. -/
noncomputable abbrev PairIdx : Type _ :=
  {p : (Fin n × G) × (Fin n × G) // (eI p.1).val < (eI p.2).val}

noncomputable instance instLOPairIdx (G : Type*) [Group G] [Fintype G] (n : ℕ) :
    LinearOrder (PairIdx (G := G) (n := n)) :=
  LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective

/-- The involution induced by `δ` on the set of unordered pairs. -/
noncomputable def pairSig (p : PairIdx (G := G) (n := n)) : PairIdx (G := G) (n := n) :=
  if h : (eI (sigPerm (G := G) (n := n) δ p.1.1)).val <
      (eI (sigPerm (G := G) (n := n) δ p.1.2)).val
  then ⟨(sigPerm (G := G) (n := n) δ p.1.1, sigPerm (G := G) (n := n) δ p.1.2), h⟩
  else ⟨(sigPerm (G := G) (n := n) δ p.1.2, sigPerm (G := G) (n := n) δ p.1.1), by
    have hne : p.1.1 ≠ p.1.2 := fun hh => absurd (by rw [hh]) (ne_of_lt p.2)
    have hne' : sigPerm (G := G) (n := n) δ p.1.1
        ≠ sigPerm (G := G) (n := n) δ p.1.2 := fun hh => hne ((sigPerm (G := G) (n := n) δ).injective hh)
    have h2 : (eI (sigPerm (G := G) (n := n) δ p.1.2)).val
        ≠ (eI (sigPerm (G := G) (n := n) δ p.1.1)).val := by
      intro hh
      exact (eI.injective.ne hne') (Fin.ext hh).symm
    exact lt_of_le_of_ne (le_of_not_gt h) h2⟩

/-- The pair element attached to an unordered pair. -/
noncomputable def bP (p : PairIdx (G := G) (n := n)) : ↥(V (G := G) (n := n)) :=
  ⟨bPair (G := G) (n := n) p.1.1 p.1.2, bPair_mem_V (G := G) (n := n) p.1.1 p.1.2⟩

/-- The coordinate map: the product of the pair elements with `ZMod 2` exponents. -/
noncomputable def Phi_tts (ε : PairIdx (G := G) (n := n) → ZMod 2) : ↥(V (G := G) (n := n)) :=
  ∏ p : PairIdx (G := G) (n := n), (bP (G := G) (n := n) p) ^ ((ε p).val)

theorem Phi_zero :
    Phi_tts (G := G) (n := n) (fun _ => 0) = 1 := by
  simp [Phi_tts]

theorem bP_sq (p : PairIdx (G := G) (n := n)) :
    bP (G := G) (n := n) p * bP (G := G) (n := n) p = 1 := by
  refine Subtype.ext ?_
  show bPair (G := G) (n := n) p.1.1 p.1.2 * bPair (G := G) (n := n) p.1.1 p.1.2 = 1
  exact sq_eq_one_of_mem_commutator (G := G) (n := n) (bPair_mem_V (G := G) (n := n) _ _)

theorem Phi_mul (ε ε' : PairIdx (G := G) (n := n) → ZMod 2) :
    Phi_tts (G := G) (n := n) (ε + ε')
      = Phi_tts (G := G) (n := n) ε * Phi_tts (G := G) (n := n) ε' := by
  rw [Phi_tts, Phi_tts, Phi_tts]
  exact tt_prod_zmodTwo_val ↥(V (G := G) (n := n)) (PairIdx (G := G) (n := n))
    (bP (G := G) (n := n)) (bP_sq (G := G) (n := n)) ε ε'

/-- The witness for a pair of generators `{a, b}` with `b = δ a`. -/
noncomputable def shortWit (p : PairIdx (G := G) (n := n)) : QQ :=
  (xGen (G := G) (n := n) p.1.1)⁻¹ * (xGen (G := G) (n := n) p.1.2)⁻¹


end Coords

end Work.SSGRoute
