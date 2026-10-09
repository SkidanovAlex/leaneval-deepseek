import Mathlib
import Submission.Work.SSGRoute.two_two_graded_pieces
import Submission.Work.SSGRoute.TwoTwoModelDefs
import Submission.Work.SSGRoute.tt_commutator_le_of_generators
import Submission.Work.SSGRoute.tt_detector_props
import Submission.Work.SSGRoute.tt_prod_zmodTwo_val
import Submission.Work.SSGRoute.tt_fixed_decomp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# vendored copy of the chain-A proof of the `(2,2)` graded step

Copy of `Submission/Work/SSGRoute/TwoTwoStep.lean` and
`Submission/Work/SSGRoute/TwoTwoAssembly.lean`, wrapped in the fresh namespace
`Work.SSGRoute.LNS3A` so that its internal name `V` does not clash with `Work.SSGRoute.V`
of the `bf4_defs` (Magnus degree-4) chain.  Provides
`Work.SSGRoute.LNS3A.two_two_graded_step` (the graded step at `(2,2)`).
-/

namespace Work.SSGRoute.LNS3A


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



/-!
# The `ℤ/4`-model computation of the graded step at `σ = (2,2)`

This file computes the graded piece `E(n,(2,2)) = F(n)^{(2,2)}/F(n)^{(3,1)}` of the refined
filtration of the free `G`-operator group `F(n)` by exhibiting a `G`-equivariant surjection from
the presentation

  `⟨x_i (i ∈ Fin n × G), γ_ij central ∣ x_i^4 = 1, γ_ij^2 = 1, [x_i,x_j] = γ_ij, [x_i^2,x_j] = 1⟩`

onto `Q_{(3,1)} = F(n)/F(n)^{(3,1)}`, and using it to solve the "coboundary equation"
`δ(e)⁻¹ e = c` for every `δ`-antisymmetric `c` in the graded piece, where `δ ∈ G` is an
involution with `δ ≠ 1`.  This is the elementary (but explicit) Step 1a (B) of Schmidt–Wingberg.
-/


open Work.CohomologicalShrinking
open scoped commutatorElement

set_option maxHeartbeats 1000000

variable {G : Type*} [Group G] [Fintype G] {n : ℕ}

/-! ## The model computation: the detector on `V = [Q,Q]` -/

section ModelCalc

open Classical

attribute [local instance] Classical.propDecidable

local notation "FF" => Work.Shrinking.freeOperatorGroup G n
local notation "QQ" => flowQuotient 2 G n 3 1

/-- `F(n)^{(3,1)}` is the second step of the `2`-central series of `F(n)`. -/
theorem P3_eq :
    flowTerm 2 G n 3 1 = Work.Shrinking.pCentralSeries 2 (FreeGroup (Fin n × G)) 2 := by
  rw [flowTerm, refinedTerm_one]

/-- The `ℤ/4`-model detector descended to `Q_{(3,1)}`. -/
noncomputable def phibar : QQ →* TTModel (Fin n × G) :=
  QuotientGroup.lift ((flowTerm 2 G n 3 1).subgroupOf (⊤ : Subgroup FF))
    ((ttDetector (Fin n × G)).comp (Subgroup.topEquiv : ↥(⊤ : Subgroup FF) ≃* FF).toMonoidHom)
    (by
      intro a ha
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
      refine (tt_detector_props (Fin n × G)).2.1 ?_
      have h := Subgroup.mem_subgroupOf.mp ha
      rwa [P3_eq (G := G) (n := n)] at h)

theorem phibar_mkQ31 (x : FF) :
    phibar (G := G) (n := n) (mkQ31 (G := G) (n := n) x) = ttDetector (Fin n × G) x := by
  rw [phibar, mkQ31_apply, QuotientGroup.mk'_apply]
  exact QuotientGroup.lift_mk' (φ := (ttDetector (Fin n × G)).comp
    (Subgroup.topEquiv : ↥(⊤ : Subgroup FF) ≃* FF).toMonoidHom)
    (N := (flowTerm 2 G n 3 1).subgroupOf ⊤) _ ⟨x, Subgroup.mem_top x⟩

theorem phibar_eq_of_commutator (α β : Fin n × G) :
    phibar (G := G) (n := n) (bPair (G := G) (n := n) α β) = TTModel.pairElt α β := by
  simp only [bPair, xGen, ← map_commutatorElement]
  rw [phibar_mkQ31]
  exact (tt_detector_props (Fin n × G)).1 α β

theorem phibar_bP (p : PairIdx (G := G) (n := n)) :
    phibar (G := G) (n := n) ((bP (G := G) (n := n) p : ↥(V (G := G) (n := n))) : QQ)
      = TTModel.pairElt p.1.1 p.1.2 := by
  rw [bP, phibar_eq_of_commutator]

/-- Multiplication in the `{0} × matrices` part of the model group. -/
theorem mul_zero_zero (κ κ' : (Fin n × G) × (Fin n × G) → ZMod 2) :
    (⟨0, κ⟩ : TTModel (Fin n × G)) * ⟨0, κ'⟩ = ⟨0, κ + κ'⟩ := by
  refine TTModel.ext' ?_ ?_
  · intro i; simp [TTModel.fst_mul]
  · intro q; simp [TTModel.snd_mul, TTModel.coc]

theorem zero_pow (κ : (Fin n × G) × (Fin n × G) → ZMod 2) (m : ℕ) :
    ((⟨0, κ⟩ : TTModel (Fin n × G)) ^ m) = ⟨0, m • κ⟩ := by
  induction m with
  | zero => rfl
  | succ m ih => rw [pow_succ, ih, mul_zero_zero, succ_nsmul]

/-- The subgroup `{x | x.fst = 0}` of the model group. -/
noncomputable def kerFst : Subgroup (TTModel (Fin n × G)) where
  carrier := {x | x.fst = 0}
  one_mem' := rfl
  mul_mem' := by
    intro a b ha hb
    show (a * b).fst = 0
    rw [TTModel.fst_mul, ha, hb]
    simp
  inv_mem' := by
    intro a ha
    show a⁻¹.fst = 0
    rw [TTModel.fst_inv, ha]
    simp

theorem commutator_fst (x y : TTModel (Fin n × G)) : ⁅x, y⁆.fst = 0 := by
  rw [commutatorElement_def]
  simp only [TTModel.fst_mul, TTModel.fst_inv, Pi.neg_apply]
  abel

theorem phibar_fst (v : ↥(V (G := G) (n := n))) :
    (phibar (G := G) (n := n) ((v : ↥(V (G := G) (n := n))) : QQ)).fst = 0 := by
  have hle : Subgroup.map (phibar (G := G) (n := n)) (V (G := G) (n := n))
      ≤ ⁅(⊤ : Subgroup (TTModel (Fin n × G))), (⊤ : Subgroup (TTModel (Fin n × G)))⁆ := by
    rw [V, Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top le_top
  have hmem : phibar (G := G) (n := n) ((v : ↥(V (G := G) (n := n))) : QQ)
      ∈ ⁅(⊤ : Subgroup (TTModel (Fin n × G))), (⊤ : Subgroup (TTModel (Fin n × G)))⁆ :=
    hle (Subgroup.mem_map_of_mem _ v.2)
  have hker : ⁅(⊤ : Subgroup (TTModel (Fin n × G))), (⊤ : Subgroup (TTModel (Fin n × G)))⁆
      ≤ kerFst (G := G) (n := n) :=
    Subgroup.commutator_le.mpr (fun a _ b _ => commutator_fst a b)
  exact hker hmem

theorem phibar_snd_add (u w : Additive ↥(V (G := G) (n := n))) :
    (phibar (G := G) (n := n)
        ((Additive.toMul (u + w) : ↥(V (G := G) (n := n))) : QQ)).snd
      = (phibar (G := G) (n := n)
          ((Additive.toMul u : ↥(V (G := G) (n := n))) : QQ)).snd
        + (phibar (G := G) (n := n)
          ((Additive.toMul w : ↥(V (G := G) (n := n))) : QQ)).snd := by
  rw [show ((Additive.toMul (u + w) : ↥(V (G := G) (n := n))) : QQ)
      = ((Additive.toMul u : ↥(V (G := G) (n := n))) : QQ)
        * ((Additive.toMul w : ↥(V (G := G) (n := n))) : QQ) from rfl, map_mul,
    TTModel.snd_mul, phibar_fst, phibar_fst]
  funext q
  simp [TTModel.coc]

/-- The additive character of `V` reading off the coefficient at an unordered pair. -/
noncomputable def chi (p : PairIdx (G := G) (n := n)) :
    Additive ↥(V (G := G) (n := n)) →+ ZMod 2 where
  toFun u := (phibar (G := G) (n := n)
    ((Additive.toMul u : ↥(V (G := G) (n := n))) : QQ)).snd p.1
  map_zero' := by
    rw [show ((Additive.toMul (0 : Additive ↥(V (G := G) (n := n))) :
        ↥(V (G := G) (n := n))) : QQ) = 1 from rfl, map_one]
    rfl
  map_add' u w := by
    rw [phibar_snd_add u w]
    rfl

/-- The second component of a pair element, as a sum of two `Pi.single`s. -/
theorem pairElt_snd_apply (a b : Fin n × G) (q : (Fin n × G) × (Fin n × G)) :
    (TTModel.pairElt a b).snd q
      = (if q = (a, b) then 1 else 0) + (if q = (b, a) then 1 else 0) := by
  rw [TTModel.pairElt_snd, Pi.add_apply, Pi.single_apply, Pi.single_apply]

theorem pairIdx_fst_ne_snd (p : PairIdx (G := G) (n := n)) : p.1.1 ≠ p.1.2 := by
  intro h
  have h2 : (eI (G := G) (n := n) p.1.1).val = (eI (G := G) (n := n) p.1.2).val := by rw [h]
  exact absurd p.2 (not_lt_of_ge (le_of_eq h2.symm))

theorem chi_bP (p q : PairIdx (G := G) (n := n)) :
    chi (G := G) (n := n) p (Additive.ofMul (bP (G := G) (n := n) q)) =
      if q = p then 1 else 0 := by
  show (phibar (G := G) (n := n)
      ((bP (G := G) (n := n) q : ↥(V (G := G) (n := n))) : QQ)).snd p.1
      = if q = p then 1 else 0
  rw [phibar_bP]
  show (TTModel.pairElt q.1.1 q.1.2).snd p.1 = if q = p then 1 else 0
  rw [pairElt_snd_apply]
  by_cases h : q = p
  · subst h
    have hne : q.1 ≠ (q.1.2, q.1.1) := fun hh => pairIdx_fst_ne_snd q (congrArg Prod.fst hh)
    rw [if_pos rfl, if_neg hne, if_pos rfl, add_zero]
  · rw [if_neg h]
    have h1 : p.1 ≠ (q.1.1, q.1.2) := fun hh => h (Subtype.ext hh.symm)
    have h2 : p.1 ≠ (q.1.2, q.1.1) := by
      intro hh
      have hlt : (eI (G := G) (n := n) q.1.2).val < (eI (G := G) (n := n) q.1.1).val := by
        have h4 := p.2
        rw [show p.1.1 = q.1.2 from congrArg Prod.fst hh,
          show p.1.2 = q.1.1 from congrArg Prod.snd hh] at h4
        exact h4
      exact absurd hlt (lt_asymm q.2)
    rw [if_neg h1, if_neg h2, add_zero]

theorem zmodTwo_natCast_val (x : ZMod 2) : ((x.val : ℕ) : ZMod 2) = x := by
  rw [ZMod.natCast_val, ZMod.cast_id]

theorem zmodTwo_neg_self : ∀ x : ZMod 2, -x = x := by decide

theorem chi_Phi (p : PairIdx (G := G) (n := n)) (ε : PairIdx (G := G) (n := n) → ZMod 2) :
    chi (G := G) (n := n) p (Additive.ofMul (Phi_tts (G := G) (n := n) ε)) = ε p := by
  have h : (Additive.ofMul (Phi_tts (G := G) (n := n) ε) : Additive ↥(V (G := G) (n := n)))
      = ∑ q : PairIdx (G := G) (n := n),
          (ε q).val • Additive.ofMul (bP (G := G) (n := n) q) := by
    rw [Phi_tts]
    have hofmul : ∀ x y : ↥(V (G := G) (n := n)),
        Additive.ofMul (x * y) = Additive.ofMul x + Additive.ofMul y := fun x y => rfl
    have hpow : ∀ (x : ↥(V (G := G) (n := n))) (m : ℕ),
        Additive.ofMul (x ^ m) = m • Additive.ofMul x := by
      intro x m
      induction m with
      | zero => rfl
      | succ m ih => rw [pow_succ, hofmul, ih, succ_nsmul]
    induction (Finset.univ : Finset (PairIdx (G := G) (n := n))) using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, hofmul, hpow, ih]
  rw [h, map_sum]
  refine (Finset.sum_eq_single p ?_ ?_).trans ?_
  · intro q _ hq
    rw [map_nsmul, chi_bP, if_neg hq, nsmul_zero]
  · intro hp
    exact absurd (Finset.mem_univ p) hp
  · rw [map_nsmul, chi_bP, if_pos rfl, nsmul_one]
    exact zmodTwo_natCast_val (ε p)

theorem Phi_injective : Function.Injective (Phi_tts (G := G) (n := n)) := by
  intro ε ε' h
  have hsq : (Phi_tts (G := G) (n := n) ε : QQ) * (Phi_tts (G := G) (n := n) ε : QQ) = 1 :=
    sq_eq_one_of_mem_commutator (G := G) (n := n) (Phi_tts (G := G) (n := n) ε).2
  have h1 : Phi_tts (G := G) (n := n) (ε + ε') = 1 := by
    rw [Phi_mul, h, ← h]
    exact Subtype.ext hsq
  funext p
  have h2 : (ε p + ε' p) = 0 := by
    have h3 := chi_Phi (G := G) (n := n) p (ε + ε')
    rw [h1, show Additive.ofMul (1 : ↥(V (G := G) (n := n))) = 0 from rfl, map_zero,
      Pi.add_apply] at h3
    exact h3.symm
  have h4 : ε p = -ε' p := eq_neg_of_add_eq_zero_left h2
  rwa [zmodTwo_neg_self] at h4

theorem Phi_single (p : PairIdx (G := G) (n := n)) :
    Phi_tts (G := G) (n := n) (fun q => if q = p then 1 else 0) = bP (G := G) (n := n) p := by
  have h2 : (2 : ℕ) ≠ 1 := by norm_num
  have h1 : Phi_tts (G := G) (n := n) (fun q => if q = p then 1 else 0)
      = (bP (G := G) (n := n) p) ^ ((if p = p then (1 : ZMod 2) else 0).val) := by
    rw [Phi_tts]
    exact Finset.prod_eq_single p
      (fun q _ hq => by rw [if_neg hq, ZMod.val_zero, pow_zero])
      (fun hp => absurd (Finset.mem_univ p) hp)
  rw [h1, if_pos rfl, ZMod.val_one'' h2, pow_one]

end ModelCalc

/-! ## The involution `pairSig` on unordered pairs -/

section PairSigProps

variable (δ : G)

theorem sigPerm_sigPerm (hδ : δ * δ = 1) (α : Fin n × G) :
    sigPerm (G := G) (n := n) δ (sigPerm (G := G) (n := n) δ α) = α := by
  rw [sigPerm_apply, sigPerm_apply, ← mul_assoc, hδ, one_mul]

/-- The two components of `pairSig δ p` are the images of the components of `p`, in one order or
the other. -/
theorem pairSig_fst_snd (p : PairIdx (G := G) (n := n)) :
    (((pairSig (G := G) (n := n) δ p).1.1 = sigPerm (G := G) (n := n) δ p.1.1 ∧
        (pairSig (G := G) (n := n) δ p).1.2 = sigPerm (G := G) (n := n) δ p.1.2) ∨
      ((pairSig (G := G) (n := n) δ p).1.1 = sigPerm (G := G) (n := n) δ p.1.2 ∧
        (pairSig (G := G) (n := n) δ p).1.2 = sigPerm (G := G) (n := n) δ p.1.1)) := by
  unfold pairSig
  split_ifs with h
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

theorem pairIdx_eq_of (p q : PairIdx (G := G) (n := n))
    (h : (p.1.1 = q.1.1 ∧ p.1.2 = q.1.2) ∨ (p.1.1 = q.1.2 ∧ p.1.2 = q.1.1)) : p = q := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Subtype.ext (Prod.ext h1 h2)
  · exfalso
    have h3 : (eI (G := G) (n := n) q.1.2).val < (eI (G := G) (n := n) q.1.1).val := by
      have h4 := p.2
      rw [h1, h2] at h4
      exact h4
    exact absurd h3 (lt_asymm q.2)

theorem pairSig_involutive (hδ : δ * δ = 1) (p : PairIdx (G := G) (n := n)) :
    pairSig (G := G) (n := n) δ (pairSig (G := G) (n := n) δ p) = p := by
  refine pairIdx_eq_of (G := G) (n := n) _ _ ?_
  rcases pairSig_fst_snd (G := G) (n := n) δ p with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rcases pairSig_fst_snd (G := G) (n := n) δ (pairSig (G := G) (n := n) δ p) with
      ⟨g1, g2⟩ | ⟨g1, g2⟩
    · exact Or.inl ⟨by rw [g1, h1, sigPerm_sigPerm (G := G) (n := n) δ hδ],
        by rw [g2, h2, sigPerm_sigPerm (G := G) (n := n) δ hδ]⟩
    · exact Or.inr ⟨by rw [g1, h2, sigPerm_sigPerm (G := G) (n := n) δ hδ],
        by rw [g2, h1, sigPerm_sigPerm (G := G) (n := n) δ hδ]⟩
  · rcases pairSig_fst_snd (G := G) (n := n) δ (pairSig (G := G) (n := n) δ p) with
      ⟨g1, g2⟩ | ⟨g1, g2⟩
    · exact Or.inr ⟨by rw [g1, h1, sigPerm_sigPerm (G := G) (n := n) δ hδ],
        by rw [g2, h2, sigPerm_sigPerm (G := G) (n := n) δ hδ]⟩
    · exact Or.inl ⟨by rw [g1, h2, sigPerm_sigPerm (G := G) (n := n) δ hδ],
        by rw [g2, h1, sigPerm_sigPerm (G := G) (n := n) δ hδ]⟩

theorem pairSig_eq_self_iff (hδ : δ * δ = 1) (hδ1 : δ ≠ 1)
    (p : PairIdx (G := G) (n := n)) :
    pairSig (G := G) (n := n) δ p = p ↔ p.1.2 = sigPerm (G := G) (n := n) δ p.1.1 := by
  constructor
  · intro hp
    rcases pairSig_fst_snd (G := G) (n := n) δ p with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exfalso
      have ha : p.1.1 = sigPerm (G := G) (n := n) δ p.1.1 := by
        rw [hp] at h1
        exact h1
      have hs : p.1.1.2 = δ * p.1.1.2 := by
        have h5 := congrArg Prod.snd ha
        rwa [sigPerm_apply] at h5
      refine hδ1 ?_
      have h6 : (1 : G) * p.1.1.2 = δ * p.1.1.2 := by rw [one_mul]; exact hs
      exact (mul_right_cancel h6).symm
    · have h2' : p.1.2 = sigPerm (G := G) (n := n) δ p.1.1 := by
        rw [hp] at h2
        exact h2
      exact h2'
  · intro hb
    have hσ : sigPerm (G := G) (n := n) δ p.1.2 = p.1.1 := by
      rw [hb, sigPerm_sigPerm (G := G) (n := n) δ hδ]
    have hcond : ¬ ((eI (G := G) (n := n) (sigPerm (G := G) (n := n) δ p.1.1)).val
        < (eI (G := G) (n := n) (sigPerm (G := G) (n := n) δ p.1.2)).val) := by
      rw [← hb, hσ]
      exact not_lt_of_ge (le_of_lt p.2)
    unfold pairSig
    rw [dif_neg hcond]
    refine Subtype.ext (Prod.ext ?_ ?_)
    · show sigPerm (G := G) (n := n) δ p.1.2 = p.1.1
      exact hσ
    · show sigPerm (G := G) (n := n) δ p.1.1 = p.1.2
      exact hb.symm

end PairSigProps

/-! ## The action of `G` on `V` -/

section VAction

open Classical

attribute [local instance] Classical.propDecidable

local notation "FF" => Work.Shrinking.freeOperatorGroup G n
local notation "QQ" => flowQuotient 2 G n 3 1

theorem V_sq (x : ↥(V (G := G) (n := n))) : x * x = 1 :=
  Subtype.ext (sq_eq_one_of_mem_commutator (G := G) (n := n) x.2)

theorem V_inv (x : ↥(V (G := G) (n := n))) : x⁻¹ = x :=
  inv_eq_of_mul_eq_one_right (V_sq (G := G) (n := n) x)

theorem V_sq_coe (x : ↥(V (G := G) (n := n))) : (x : QQ) * (x : QQ) = 1 := by
  simpa using congrArg (fun y : ↥(V (G := G) (n := n)) => (y : QQ)) (V_sq (G := G) (n := n) x)

theorem bPair_comm (α β : Fin n × G) :
    bPair (G := G) (n := n) α β = bPair (G := G) (n := n) β α := by
  have h2 : bPair (G := G) (n := n) α β * bPair (G := G) (n := n) α β = 1 :=
    sq_eq_one_of_mem_commutator (G := G) (n := n) (bPair_mem_V (G := G) (n := n) α β)
  have h3 : bPair (G := G) (n := n) β α = (bPair (G := G) (n := n) α β)⁻¹ := by
    rw [bPair, bPair, commutatorElement_inv]
  rw [h3, inv_eq_of_mul_eq_one_right h2]

theorem V_eq_closure_bP :
    V (G := G) (n := n)
      = Subgroup.closure (Set.range (fun p => (bP (G := G) (n := n) p : QQ))) := by
  change ⁅(⊤ : Subgroup QQ), (⊤ : Subgroup QQ)⁆
      = Subgroup.closure (Set.range (fun p => (bP (G := G) (n := n) p : QQ)))
  rw [commutator_eq_closure_bPair]
  refine le_antisymm ?_ ?_
  · rw [Subgroup.closure_le]
    rintro _ ⟨⟨α, β⟩, rfl⟩
    change bPair (G := G) (n := n) α β
      ∈ Subgroup.closure (Set.range (fun p => (bP (G := G) (n := n) p : QQ)))
    by_cases hab : α = β
    · subst hab
      have h1 : bPair (G := G) (n := n) α α = 1 := by rw [bPair, commutatorElement_self]
      rw [h1]
      exact Subgroup.one_mem _
    · have hne : (eI (G := G) (n := n) α).val ≠ (eI (G := G) (n := n) β).val :=
        fun hh => hab (eI.injective (Fin.ext hh))
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · exact Subgroup.subset_closure ⟨⟨(α, β), hlt⟩, rfl⟩
      · have h4 : bPair (G := G) (n := n) α β
            = (bP (G := G) (n := n) ⟨(β, α), hlt⟩ : QQ) := by
          rw [bPair_comm]
          rfl
        rw [h4]
        exact Subgroup.subset_closure ⟨⟨(β, α), hlt⟩, rfl⟩
  · rw [Subgroup.closure_le]
    rintro _ ⟨p, rfl⟩
    exact Subgroup.subset_closure ⟨(p.1.1, p.1.2), rfl⟩

/-- The commutator subgroup is the closure of the pair elements, in unfolded form. -/
theorem closure_bP_eq_commutator :
    Subgroup.closure (Set.range (fun p => (bP (G := G) (n := n) p : QQ)))
      = ⁅(⊤ : Subgroup QQ), (⊤ : Subgroup QQ)⁆ :=
  (V_eq_closure_bP (G := G) (n := n)).symm

theorem mem_closure_bP_of_mem_V {x : QQ} (hx : x ∈ V (G := G) (n := n)) :
    x ∈ Subgroup.closure (Set.range (fun p => (bP (G := G) (n := n) p : QQ))) :=
  V_eq_closure_bP (G := G) (n := n) ▸ hx

theorem flowAction_bPair (g : G) (α β : Fin n × G) :
    flowAction 2 G n 3 1 g (bPair (G := G) (n := n) α β)
      = bPair (G := G) (n := n) (sigPerm (G := G) (n := n) g α)
          (sigPerm (G := G) (n := n) g β) := by
  rw [bPair, map_commutatorElement, bPair, flowAction_xGen, flowAction_xGen, sigPerm_apply,
    sigPerm_apply]

theorem flowAction_mem_V (g : G) {v : QQ} (hv : v ∈ V (G := G) (n := n)) :
    flowAction 2 G n 3 1 g v ∈ V (G := G) (n := n) := by
  have h : Subgroup.map (flowAction 2 G n 3 1 g) (V (G := G) (n := n))
      ≤ V (G := G) (n := n) := by
    change Subgroup.map (flowAction 2 G n 3 1 g) ⁅(⊤ : Subgroup QQ), (⊤ : Subgroup QQ)⁆
      ≤ ⁅(⊤ : Subgroup QQ), (⊤ : Subgroup QQ)⁆
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top le_top
  exact h (Subgroup.mem_map_of_mem _ hv)

noncomputable def flowActionV (g : G) :
    ↥(V (G := G) (n := n)) →* ↥(V (G := G) (n := n)) where
  toFun v := ⟨flowAction 2 G n 3 1 g (v : QQ), flowAction_mem_V (G := G) (n := n) g v.2⟩
  map_one' := Subtype.ext (by
    show flowAction 2 G n 3 1 g (1 : QQ) = (1 : QQ)
    exact map_one _)
  map_mul' a b := Subtype.ext (by
    show flowAction 2 G n 3 1 g ((a : QQ) * (b : QQ))
        = flowAction 2 G n 3 1 g (a : QQ) * flowAction 2 G n 3 1 g (b : QQ)
    exact map_mul _ _ _)

theorem flowActionV_bP (g : G) (p : PairIdx (G := G) (n := n)) :
    flowActionV (G := G) (n := n) g (bP (G := G) (n := n) p)
      = bP (G := G) (n := n) (pairSig (G := G) (n := n) g p) := by
  refine Subtype.ext ?_
  show flowAction 2 G n 3 1 g (bPair (G := G) (n := n) p.1.1 p.1.2)
      = bPair (G := G) (n := n) (pairSig (G := G) (n := n) g p).1.1
          (pairSig (G := G) (n := n) g p).1.2
  rw [flowAction_bPair]
  rcases pairSig_fst_snd (G := G) (n := n) g p with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, bPair_comm]

variable (δ : G)

theorem flowActionV_Phi (hδ : δ * δ = 1)
    (ε : PairIdx (G := G) (n := n) → ZMod 2) :
    flowActionV (G := G) (n := n) δ (Phi_tts (G := G) (n := n) ε)
      = Phi_tts (G := G) (n := n) (fun p => ε (pairSig (G := G) (n := n) δ p)) := by
  have hinv : ∀ p, pairSig (G := G) (n := n) δ (pairSig (G := G) (n := n) δ p) = p :=
    pairSig_involutive (G := G) (n := n) δ hδ
  have hinj : Function.Injective (pairSig (G := G) (n := n) δ) := fun a b h => by
    have h' := congrArg (pairSig (G := G) (n := n) δ) h
    rwa [hinv a, hinv b] at h'
  have hsurj : Function.Surjective (pairSig (G := G) (n := n) δ) :=
    fun b => ⟨pairSig (G := G) (n := n) δ b, hinv b⟩
  rw [Phi_tts, Phi_tts, map_prod]
  rw [show (∏ x ∈ (Finset.univ : Finset (PairIdx (G := G) (n := n))),
        flowActionV (G := G) (n := n) δ (bP (G := G) (n := n) x ^ (ε x).val))
      = (∏ x ∈ (Finset.univ : Finset (PairIdx (G := G) (n := n))),
        bP (G := G) (n := n) (pairSig (G := G) (n := n) δ x) ^ (ε x).val) from
      Finset.prod_congr rfl (fun x _ => by rw [map_pow, flowActionV_bP])]
  refine Finset.prod_bij (fun a _ => pairSig (G := G) (n := n) δ a)
    (fun a _ => Finset.mem_univ _) (fun a _ b _ h => hinj h)
    (fun b _ => ⟨pairSig (G := G) (n := n) δ b, Finset.mem_univ _, hinv b⟩) (fun a _ => ?_)
  rw [hinv a]

end VAction

/-! ## The `psi_tts`-computation on the graded piece -/

section Assembly

open Classical

attribute [local instance] Classical.propDecidable

local notation "FF" => Work.Shrinking.freeOperatorGroup G n
local notation "QQ" => flowQuotient 2 G n 3 1

/-- The product of the pair elements over the support of `s`, as a finset product in the
commutative group `V`. -/
theorem zmodTwo_val_eq_one {x : ZMod 2} (hx : x ≠ 0) : x.val = 1 := by
  haveI : NeZero 2 := ⟨by norm_num⟩
  have h1 : x.val < 2 := ZMod.val_lt x
  have h2 : x.val ≠ 0 := fun hh => hx ((ZMod.val_eq_zero x).mp hh)
  omega

theorem Phi_eq_prod_support (s : PairIdx (G := G) (n := n) → ZMod 2) :
    Phi_tts (G := G) (n := n) s
      = ∏ p ∈ (Finset.univ.filter (fun p => s p ≠ 0)), bP (G := G) (n := n) p := by
  rw [Phi_tts]
  trans ∏ p ∈ (Finset.univ.filter (fun p => s p ≠ 0)), (bP (G := G) (n := n) p) ^ ((s p).val)
  · exact (Finset.prod_subset
      (s₁ := Finset.univ.filter (fun p => s p ≠ 0))
      (s₂ := (Finset.univ : Finset (PairIdx (G := G) (n := n))))
      (f := fun p => (bP (G := G) (n := n) p) ^ ((s p).val))
      (fun x hx => (Finset.mem_filter.mp hx).1) (fun p _ hp => by
        have hp0 : s p = 0 := by
          by_contra hne
          exact hp (Finset.mem_filter.mpr ⟨Finset.mem_univ p, hne⟩)
        rw [hp0, ZMod.val_zero, pow_zero])).symm
  · refine Finset.prod_congr rfl (fun p hp => ?_)
    rw [zmodTwo_val_eq_one (Finset.mem_filter.mp hp).2, pow_one]


/-- The `F(n)^{(2,2)}`-part of `Q_{(3,1)}` is the commutator subgroup. -/
theorem map_mkQ31_P2 :
    Subgroup.map (mkQ31 (G := G) (n := n)) (flowTerm 2 G n 2 2) = V (G := G) (n := n) := by
  rw [TwoTwo.flowTerm_two_two, Subgroup.map_sup, map_mkQ31_P3 (G := G) (n := n),
    map_commutator_eq (G := G) (n := n), sup_bot_eq]

/-- Elements of the kernel of the level projection `Q_{(3,1)} → Q_{(2,2)}` lie in the commutator
subgroup. -/
theorem mem_V_of_flowQuotSucc_eq_one {c : QQ} (hc : flowQuotSucc 2 G n 2 2 c = 1) :
    c ∈ V (G := G) (n := n) := by
  obtain ⟨y, hy, hyc⟩ := TwoTwo.ker_flowQuotSucc_two_two_exists_commutator (G := G) (n := n) hc
  have hmem : mkQ31 (G := G) (n := n) y ∈ V (G := G) (n := n) := by
    have h1 : mkQ31 (G := G) (n := n) y ∈ Subgroup.map (mkQ31 (G := G) (n := n))
        ⁅(⊤ : Subgroup FF), (⊤ : Subgroup FF)⁆ := Subgroup.mem_map_of_mem _ hy
    rwa [map_commutator_eq (G := G) (n := n)] at h1
  have h2 : c = mkQ31 (G := G) (n := n) y := by
    rw [← hyc]
    exact (rfl : QuotientGroup.mk'
      ((flowTerm 2 G n (tauSucc 2 2).1 (tauSucc 2 2).2).subgroupOf (⊤ : Subgroup FF))
      ⟨y, Subgroup.mem_top y⟩ = mkQ31 (G := G) (n := n) y)
  rwa [h2]

/-- The product of the witnesses over the support of `s`. -/
noncomputable def witList (s : PairIdx (G := G) (n := n) → ZMod 2) :
    List (PairIdx (G := G) (n := n)) :=
  ((Finset.univ : Finset (PairIdx (G := G) (n := n))).filter (fun p => s p ≠ 0)).sort (· ≤ ·)

noncomputable def witProd (s : PairIdx (G := G) (n := n) → ZMod 2) : QQ :=
  ((witList (G := G) (n := n) s).map (fun p => shortWit (G := G) (n := n) p)).prod

theorem mem_witList {s : PairIdx (G := G) (n := n) → ZMod 2}
    {p : PairIdx (G := G) (n := n)} (hp : p ∈ witList (G := G) (n := n) s) : s p ≠ 0 := by
  rw [witList, Finset.mem_sort, Finset.mem_filter] at hp
  exact hp.2

/-- Every element of the closure of the pair elements is a `Phi_tts ε`. -/
theorem Phi_mem_closure {x : QQ}
    (hx : x ∈ Subgroup.closure (Set.range (fun p => (bP (G := G) (n := n) p : QQ)))) :
    ∃ ε : PairIdx (G := G) (n := n) → ZMod 2, Phi_tts (G := G) (n := n) ε = x := by
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨p, rfl⟩ := hy
    exact ⟨fun q => if q = p then 1 else 0,
      congrArg (fun w : ↥(V (G := G) (n := n)) => (w : QQ)) (Phi_single (G := G) (n := n) p)⟩
  | one => exact ⟨0,
      congrArg (fun w : ↥(V (G := G) (n := n)) => (w : QQ)) (Phi_zero (G := G) (n := n))⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨ε, hε⟩ := ihx
    obtain ⟨ε', hε'⟩ := ihy
    refine ⟨ε + ε', ?_⟩
    rw [Phi_mul, Subgroup.coe_mul, hε, hε']
  | inv x hx ih =>
    obtain ⟨ε, hε⟩ := ih
    refine ⟨ε, ?_⟩
    rw [hε]
    exact eq_inv_of_mul_eq_one_right
      (sq_eq_one_of_mem_commutator (G := G) (n := n)
        ((closure_bP_eq_commutator (G := G) (n := n)) ▸ hx))

/-- The model elements `Phi_tts ε` exhaust the commutator subgroup. -/
theorem Phi_surjective (v : ↥(V (G := G) (n := n))) :
    ∃ ε : PairIdx (G := G) (n := n) → ZMod 2, Phi_tts (G := G) (n := n) ε = v := by
  obtain ⟨ε, hε⟩ := Phi_mem_closure (G := G) (n := n)
    (mem_closure_bP_of_mem_V (G := G) (n := n) v.2)
  exact ⟨ε, Subtype.ext hε⟩

variable (δ : G)

/-- The general multiplicativity rule for `psi_tts`, valid when the first value is central. -/
theorem psi_mul_of_central {a b : QQ}
    (ha : ∀ x : QQ, psi_tts (G := G) (n := n) δ a * x = x * psi_tts (G := G) (n := n) δ a) :
    psi_tts (G := G) (n := n) δ (a * b)
      = psi_tts (G := G) (n := n) δ a * psi_tts (G := G) (n := n) δ b := by
  have hb : ((flowAction 2 G n 3 1 δ a)⁻¹ * a) * (flowAction 2 G n 3 1 δ b)⁻¹
      = (flowAction 2 G n 3 1 δ b)⁻¹ * ((flowAction 2 G n 3 1 δ a)⁻¹ * a) :=
    ha (flowAction 2 G n 3 1 δ b)⁻¹
  calc psi_tts (G := G) (n := n) δ (a * b)
      = (flowAction 2 G n 3 1 δ (a * b))⁻¹ * (a * b) := rfl
    _ = (flowAction 2 G n 3 1 δ b)⁻¹ * (flowAction 2 G n 3 1 δ a)⁻¹ * (a * b) := by
          rw [map_mul, mul_inv_rev]
    _ = (flowAction 2 G n 3 1 δ b)⁻¹ * ((flowAction 2 G n 3 1 δ a)⁻¹ * a) * b := by group
    _ = ((flowAction 2 G n 3 1 δ a)⁻¹ * a) * (flowAction 2 G n 3 1 δ b)⁻¹ * b := by
          rw [← hb]
    _ = (flowAction 2 G n 3 1 δ a)⁻¹ * a
          * ((flowAction 2 G n 3 1 δ b)⁻¹ * b) := by group
    _ = psi_tts (G := G) (n := n) δ a * psi_tts (G := G) (n := n) δ b := rfl

/-- `psi_tts` of the model element `Phi_tts ε` (an element of `V`). -/
theorem psi_Phi (hδ : δ * δ = 1) (ε : PairIdx (G := G) (n := n) → ZMod 2) :
    psi_tts (G := G) (n := n) δ ((Phi_tts (G := G) (n := n) ε : ↥(V (G := G) (n := n))) : QQ)
      = ((Phi_tts (G := G) (n := n) (fun p => ε (pairSig (G := G) (n := n) δ p))
            * Phi_tts (G := G) (n := n) ε : ↥(V (G := G) (n := n))) : QQ) := by
  rw [psi_tts]
  rw [show flowAction 2 G n 3 1 δ ((Phi_tts (G := G) (n := n) ε : ↥(V (G := G) (n := n))) : QQ)
      = ((flowActionV (G := G) (n := n) δ (Phi_tts (G := G) (n := n) ε)
          : ↥(V (G := G) (n := n))) : QQ) from rfl]
  rw [flowActionV_Phi (G := G) (n := n) δ hδ ε]
  rw [← Subgroup.coe_inv, V_inv (G := G) (n := n), ← Subgroup.coe_mul]

/-- The bridge between a sorted-list product and a finset product. -/
theorem list_prod_sort_eq (s : Finset (PairIdx (G := G) (n := n)))
    (f : PairIdx (G := G) (n := n) → ↥(V (G := G) (n := n))) :
    ((s.sort (· ≤ ·)).map f).prod = ∏ i ∈ s, f i := by
  rw [Finset.prod_eq_multiset_prod s f, ← Finset.sort_eq s (· ≤ ·), Multiset.map_coe,
    Multiset.prod_coe]

/-- On the "short" pairs `{α, δ α}`, `psi_tts` of the witness is the corresponding pair element. -/
theorem psi_shortWit (hδ : δ * δ = 1) (hδ1 : δ ≠ 1) (p : PairIdx (G := G) (n := n))
    (hp : pairSig (G := G) (n := n) δ p = p) :
    psi_tts (G := G) (n := n) δ (shortWit (G := G) (n := n) p)
      = ((bP (G := G) (n := n) p : ↥(V (G := G) (n := n))) : QQ) := by
  have h2 : p.1.2 = sigPerm (G := G) (n := n) δ p.1.1 :=
    (pairSig_eq_self_iff (G := G) (n := n) δ hδ hδ1 p).mp hp
  have h3 : shortWit (G := G) (n := n) p
      = (xGen (G := G) (n := n) p.1.1)⁻¹
        * (xGen (G := G) (n := n) (sigPerm (G := G) (n := n) δ p.1.1))⁻¹ := by
    rw [shortWit, h2]
  have hR : ((bP (G := G) (n := n) p : ↥(V (G := G) (n := n))) : QQ)
      = bPair (G := G) (n := n) p.1.1 (sigPerm (G := G) (n := n) δ p.1.1) := by
    rw [← h2]
    rfl
  rw [hR, h3]
  exact psi_short (G := G) (n := n) δ hδ p.1.1

/-- On the short pairs, the group action turns the witness into witness times pair element. -/
theorem flowAction_shortWit (hδ : δ * δ = 1) (hδ1 : δ ≠ 1) (p : PairIdx (G := G) (n := n))
    (hp : pairSig (G := G) (n := n) δ p = p) :
    flowAction 2 G n 3 1 δ (shortWit (G := G) (n := n) p)
      = shortWit (G := G) (n := n) p
        * ((bP (G := G) (n := n) p : ↥(V (G := G) (n := n))) : QQ) := by
  have h := psi_shortWit (G := G) (n := n) δ hδ hδ1 p hp
  have hb2 : ((bP (G := G) (n := n) p : ↥(V (G := G) (n := n))) : QQ)
      * ((bP (G := G) (n := n) p : ↥(V (G := G) (n := n))) : QQ) = 1 :=
    V_sq_coe (G := G) (n := n) (bP (G := G) (n := n) p)
  have h2 : (flowAction 2 G n 3 1 δ (shortWit (G := G) (n := n) p))⁻¹
      = ((bP (G := G) (n := n) p : ↥(V (G := G) (n := n))) : QQ)
        * (shortWit (G := G) (n := n) p)⁻¹ := by
    rw [psi_tts] at h
    exact eq_mul_inv_of_mul_eq h
  rw [← inv_inv (flowAction 2 G n 3 1 δ (shortWit (G := G) (n := n) p)), h2, mul_inv_rev,
    inv_inv, inv_eq_of_mul_eq_one_right hb2]

/-- `psi_tts` of a product of witnesses over a list of short pairs. -/
theorem psi_witList (hδ : δ * δ = 1) (hδ1 : δ ≠ 1) (L : List (PairIdx (G := G) (n := n)))
    (hL : ∀ p ∈ L, pairSig (G := G) (n := n) δ p = p) :
    psi_tts (G := G) (n := n) δ ((L.map (fun p => shortWit (G := G) (n := n) p)).prod)
      = (((L.map (fun p => bP (G := G) (n := n) p)).prod
          : ↥(V (G := G) (n := n))) : QQ) := by
  induction L with
  | nil => simp [psi_tts]
  | cons a L ih =>
    have hL' : ∀ p ∈ L, pairSig (G := G) (n := n) δ p = p :=
      fun p hp => hL p (List.mem_cons_of_mem a hp)
    have ha : pairSig (G := G) (n := n) δ a = a := hL a (by simp)
    have hc : ∀ x : QQ, psi_tts (G := G) (n := n) δ (shortWit (G := G) (n := n) a) * x
        = x * psi_tts (G := G) (n := n) δ (shortWit (G := G) (n := n) a) := by
      intro x
      rw [psi_shortWit (G := G) (n := n) δ hδ hδ1 a ha]
      exact (Subgroup.mem_center_iff.mp
        (commutator_le_center (G := G) (n := n) (bP (G := G) (n := n) a).2) x).symm
    rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons]
    rw [psi_mul_of_central (G := G) (n := n) δ
      (a := shortWit (G := G) (n := n) a)
      (b := (L.map (fun p => shortWit (G := G) (n := n) p)).prod) hc]
    rw [psi_shortWit (G := G) (n := n) δ hδ hδ1 a ha, ih hL', Subgroup.coe_mul]

/-- `psi_tts` of the witness product is the model element `Phi_tts s`. -/
theorem psi_witProd (hδ : δ * δ = 1) (hδ1 : δ ≠ 1) (s : PairIdx (G := G) (n := n) → ZMod 2)
    (hs0 : ∀ p, pairSig (G := G) (n := n) δ p ≠ p → s p = 0) :
    psi_tts (G := G) (n := n) δ (witProd (G := G) (n := n) s)
      = ((Phi_tts (G := G) (n := n) s : ↥(V (G := G) (n := n))) : QQ) := by
  have hL : ∀ p ∈ witList (G := G) (n := n) s, pairSig (G := G) (n := n) δ p = p := by
    intro p hp
    by_contra hne
    exact mem_witList (G := G) (n := n) hp (hs0 p hne)
  have hbridge : ((witList (G := G) (n := n) s).map
        (fun p => (bP (G := G) (n := n) p : ↥(V (G := G) (n := n))))).prod
      = Phi_tts (G := G) (n := n) s := by
    unfold witList
    rw [list_prod_sort_eq]
    exact (Phi_eq_prod_support (G := G) (n := n) s).symm
  rw [witProd, psi_witList (G := G) (n := n) δ hδ hδ1 _ hL, hbridge]

/-- **The graded step at `σ = (2,2)`**: every `δ`-antisymmetric element of `E(n,(2,2))` is a
"coboundary" `δ(e)⁻¹ e`. -/
theorem two_two_graded_step (hδ : δ * δ = 1) (hδ1 : δ ≠ 1)
    (c : QQ) (hc : flowQuotSucc 2 G n 2 2 c = 1)
    (hc2 : flowAction 2 G n 3 1 δ c = c⁻¹) :
    ∃ e : QQ, c = (flowAction 2 G n 3 1 δ e)⁻¹ * e := by
  have hcV : c ∈ V (G := G) (n := n) := mem_V_of_flowQuotSucc_eq_one (G := G) (n := n) hc
  obtain ⟨ε, hε⟩ := Phi_surjective (G := G) (n := n) ⟨c, hcV⟩
  have hc2' : flowActionV (G := G) (n := n) δ ⟨c, hcV⟩ = ⟨c, hcV⟩ := by
    refine Subtype.ext ?_
    show flowAction 2 G n 3 1 δ c = c
    rw [hc2, inv_eq_of_mul_eq_one_right
      (sq_eq_one_of_mem_commutator (G := G) (n := n) hcV)]
  have hεfix : ∀ p, ε (pairSig (G := G) (n := n) δ p) = ε p := by
    have h1 : Phi_tts (G := G) (n := n) (fun p => ε (pairSig (G := G) (n := n) δ p))
        = Phi_tts (G := G) (n := n) ε := by
      rw [← flowActionV_Phi (G := G) (n := n) δ hδ ε]
      simp only [hε, hc2']
    intro p
    exact congrFun (Phi_injective (G := G) (n := n) h1) p
  obtain ⟨lam, s, hs0, hdecomp⟩ :=
    tt_fixed_decomp (pairSig (G := G) (n := n) δ)
      (pairSig_involutive (G := G) (n := n) δ hδ) ε hεfix
  refine ⟨((Phi_tts (G := G) (n := n) lam : ↥(V (G := G) (n := n))) : QQ)
    * witProd (G := G) (n := n) s, ?_⟩
  have hpsi1 : psi_tts (G := G) (n := n) δ
      ((Phi_tts (G := G) (n := n) lam : ↥(V (G := G) (n := n))) : QQ)
      = ((Phi_tts (G := G) (n := n) (fun p => lam (pairSig (G := G) (n := n) δ p))
          * Phi_tts (G := G) (n := n) lam : ↥(V (G := G) (n := n))) : QQ) :=
    psi_Phi (G := G) (n := n) δ hδ lam
  have hVmem : psi_tts (G := G) (n := n) δ
      ((Phi_tts (G := G) (n := n) lam : ↥(V (G := G) (n := n))) : QQ)
      ∈ V (G := G) (n := n) := by
    rw [hpsi1]
    exact (Phi_tts (G := G) (n := n) (fun p => lam (pairSig (G := G) (n := n) δ p))
      * Phi_tts (G := G) (n := n) lam).2
  have hmul := psi_mul (G := G) (n := n) δ
    (a := ((Phi_tts (G := G) (n := n) lam : ↥(V (G := G) (n := n))) : QQ))
    (b := witProd (G := G) (n := n) s) hVmem
  have hpsi2 : psi_tts (G := G) (n := n) δ (witProd (G := G) (n := n) s)
      = ((Phi_tts (G := G) (n := n) s : ↥(V (G := G) (n := n))) : QQ) :=
    psi_witProd (G := G) (n := n) δ hδ hδ1 s hs0
  show c = psi_tts (G := G) (n := n) δ
    (((Phi_tts (G := G) (n := n) lam : ↥(V (G := G) (n := n))) : QQ)
      * witProd (G := G) (n := n) s)
  rw [hmul, hpsi1, hpsi2]
  trans ((Phi_tts (G := G) (n := n) ε : ↥(V (G := G) (n := n))) : QQ)
  · rw [hε]
  · rw [← Subgroup.coe_mul]
    congr 1
    rw [← Phi_mul, ← Phi_mul]
    congr 1
    funext p
    rw [Pi.add_apply, Pi.add_apply, hdecomp p]
    abel

end Assembly



end Work.SSGRoute.LNS3A
