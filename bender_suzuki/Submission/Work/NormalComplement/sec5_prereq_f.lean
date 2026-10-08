import Mathlib
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.Sections
import Submission.Work.NormalComplement.p3Normal_of_chIIFourP3Subnormal
import Submission.Work.NormalComplement.sec5_setup
import Submission.Work.NormalComplement.appIII
import Submission.Work.NormalComplement.sec5_prop2a
import Submission.Work.NormalComplement.p2a_appIII_cyclic
import Submission.Work.NormalComplement.appI_five_b
import Submission.Work.ThreePoints.P3NeBot.p3_twoTransitive
import Submission.Work.BrauerSuzuki.Group.isCyclicOrGenQuaternion_of_uniqueInvolution
import Submission.Work.BrauerSuzuki.Quaternion.genQuaternionData_basic
import Submission.Work.NormalComplement.sec5f_setup
import Submission.Work.NormalComplement.card_sup_mul_card_inf
import Submission.Work.ThreePoints.P3NeBot.oddResidual_basic
import Submission.Work.NormalComplement.Sec5Fix.sec5f_quot_action_facts

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement

open Classical
open LeanEval.GroupTheory.Defs

set_option autoImplicit false
set_option maxHeartbeats 8000000

/-! ## Preparatory lemmas for `sec5_prereq_f` (Peterfalvi I Ch. III §5 Prop. 2 (a)) -/

/-- An element of `2`-power order lies in `O^{2'}`. -/
theorem sec5f_mem_oddResidual_of_pow_two_eq_one {L : Type} [Group L] [Finite L] {x : L} {k : ℕ}
    (hx : x ^ 2 ^ k = 1) : x ∈ Submission.Blueprint.oddResidual L := by
  induction k generalizing x with
  | zero =>
      rw [pow_zero, pow_one] at hx
      rw [hx]
      exact Subgroup.one_mem _
  | succ k ih =>
      have h2 : (x * x) ^ 2 ^ k = 1 := by
        rw [← pow_two, ← pow_mul, ← pow_succ', hx]
      exact Work.Reductions.mem_oddResidual_of_mul_self_mem (ih h2)

/-- An element of `C` of `2`-power order lies in `O^{2'}(C)` (as a subgroup of `G`). -/
theorem sec5f_mem_map_oddResidual_of_orderOf_two_pow {G : Type} [Group G] [Finite G]
    {C : Subgroup G} {x : G} (hx : x ∈ C) {k : ℕ} (h : orderOf x = 2 ^ k) :
    x ∈ (Submission.Blueprint.oddResidual C).map C.subtype := by
  refine Subgroup.mem_map.mpr ⟨⟨x, hx⟩, ?_, rfl⟩
  refine sec5f_mem_oddResidual_of_pow_two_eq_one (x := (⟨x, hx⟩ : ↥C)) (k := k) ?_
  apply Subtype.ext
  rw [Subgroup.coe_pow, ← h, pow_orderOf_eq_one]
  rfl

/-- `F = O^{2'}(C_G(V))`, the odd residual of the centraliser of `V = centD H t`. -/
noncomputable abbrev sec5fF {G : Type} [Group G] (H : Subgroup G) (t : G) : Subgroup G :=
  Work.ThreePoints.p3F (Submission.Blueprint.centD H t)

/-! ### The Ch. II §4 Prop. 3 package for `X = V = centD H t` (with subnormal `Y = A`) -/

/-- Ch. II §4 Prop. 3 at `X = V = centD H t` with the subnormal subgroup `Y = A`: the
`P3Pkg` of `V` (clauses (a), (b)) and the double transitivity of `N_G(V)` on `Ω_V`. -/
theorem sec5f_p3_hyp (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC : Submission.Blueprint.ThmCProp) {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}
    (h : Work.NormalComplement.Design.Setup5 G H t W p P A r) :
    Work.ThreePoints.P3Pkg H t (Submission.Blueprint.centD H t) := by
  have hBrSz : Submission.Blueprint.BrauerSuzukiProp := Work.BrauerSuzuki.brauerSuzuki
  have hZJ : Submission.Blueprint.GlaubermanZJProp := Work.ThmF.ChV12.glaubermanZJ_free
  have hA : Submission.Blueprint.ThmAProp := Work.DoubleTransitivity.Sec7.ThmA hFT hZJ hBrSz
  have hMod : Submission.Blueprint.ModelFactsProp := Work.Models.models hFT
  exact Work.ThreePoints.p3pkg hFT hC hA hZJ hBrSz hMod h.sit h.se h.invol h.notMem
    (Submission.Blueprint.centD H t) le_rfl
    ⟨A, h.A_ne, p2a_IsSubnormalIn_A_V h, p2a_HasNonTrivialNK_A h⟩

/-- `N_G(V) = O^{2'}(C_G(V)) ⊔ V`: the §5 group `𝒩` is the product of `F = p3F V` and `V`. -/
theorem sec5f_NN_eq (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC : Submission.Blueprint.ThmCProp) {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}
    (h : Work.NormalComplement.Design.Setup5 G H t W p P A r) :
    Work.NormalComplement.Sec5f.NN H t = sec5fF H t ⊔ Submission.Blueprint.centD H t := by
  have h1 := (sec5f_p3_hyp hFT hC h).1.1
  show Subgroup.normalizer (Submission.Blueprint.centD H t : Set G) = _
  rw [h1, inf_eq_left.mpr Subgroup.le_normalizer]

/-- `N_G(V)` acts 2-transitively on `Ω_V`. -/
theorem sec5f_twoTransitive (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC : Submission.Blueprint.ThmCProp) {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}
    (h : Work.NormalComplement.Design.Setup5 G H t W p P A r) :
    Work.DoubleTransitivity.IsTwoTransitiveOnSub (Work.NormalComplement.Sec5f.NN H t)
      (Submission.Blueprint.fixedPts H (Submission.Blueprint.centD H t)) :=
  (sec5f_p3_hyp hFT hC h).2

/-- `F = O^{2'}(C_G(V)) ≤ 𝒩 = N_G(V)`. -/
theorem sec5f_F_le_NN {G : Type} [Group G] [Finite G] {H : Subgroup G} {t : G} :
    sec5fF H t ≤ Work.NormalComplement.Sec5f.NN H t :=
  Work.ThreePoints.p3F_le_normalizer _

/-- Distinct conjugates of a strongly embedded `H` meet in odd order. -/
theorem sec5f_odd_twoPoint {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}
    (h : Work.NormalComplement.Design.Setup5 G H t W p P A r) :
    Odd (Nat.card ↥(Submission.Blueprint.twoPoint H t)) := by
  have hne : Submission.Blueprint.conj (1 : G) H ≠ Submission.Blueprint.conj t H := by
    rw [Work.ThreePoints.conj_one]
    intro hcon
    refine h.notMem ?_
    have ht : t ∈ Subgroup.normalizer (H : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr hcon.symm
    rwa [Work.ThreePoints.IsStronglyEmbedded.normalizer_eq h.se] at ht
  have hthis := Work.ThreePoints.card_inf_conj_odd h.se hne
  rw [Work.ThreePoints.conj_one] at hthis
  exact hthis

/-- The index `|𝒩 : F|` is odd (`𝒩 = F·V` with `V` of odd order). -/
theorem sec5f_index_NN_F_odd (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC : Submission.Blueprint.ThmCProp) {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}
    (h : Work.NormalComplement.Design.Setup5 G H t W p P A r) :
    Odd ((sec5fF H t).subgroupOf (Work.NormalComplement.Sec5f.NN H t)).index := by
  have hNN := sec5f_NN_eq hFT hC h
  have hVleF : Submission.Blueprint.centD H t ≤ Subgroup.normalizer (sec5fF H t : Set G) := by
    intro v hv
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hcomm : v * x = x * v :=
        (Subgroup.mem_centralizer_iff.mp (Work.ThreePoints.p3F_le_centralizer _ hx)) v hv
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
      exact hx
    · intro hx
      have hcomm : v⁻¹ * (v * x * v⁻¹) = (v * x * v⁻¹) * v⁻¹ :=
        (Subgroup.mem_centralizer_iff.mp (Work.ThreePoints.p3F_le_centralizer _ hx))
          v⁻¹ ((Submission.Blueprint.centD H t).inv_mem hv)
      have h1 : x = v⁻¹ * (v * x * v⁻¹) * v := by group
      rw [h1, hcomm, mul_assoc, inv_mul_cancel, mul_one]
      exact hx
  have hcard_sup : Nat.card ↥(sec5fF H t ⊔ Submission.Blueprint.centD H t) *
      Nat.card ↥(sec5fF H t ⊓ Submission.Blueprint.centD H t) =
      Nat.card ↥(sec5fF H t) * Nat.card ↥(Submission.Blueprint.centD H t) :=
    card_sup_mul_card_inf hVleF
  have hLag : ((sec5fF H t).subgroupOf (Work.NormalComplement.Sec5f.NN H t)).index *
      Nat.card ↥(sec5fF H t) = Nat.card ↥(Work.NormalComplement.Sec5f.NN H t) := by
    have h1 := Subgroup.index_mul_card ((sec5fF H t).subgroupOf
      (Work.NormalComplement.Sec5f.NN H t))
    have hc : Nat.card ↥((sec5fF H t).subgroupOf (Work.NormalComplement.Sec5f.NN H t)) =
        Nat.card ↥(sec5fF H t) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (sec5f_F_le_NN (H := H) (t := t))).toEquiv
    rwa [hc] at h1
  have hrel : (sec5fF H t ⊓ Submission.Blueprint.centD H t).relIndex
      (Submission.Blueprint.centD H t) * Nat.card ↥(sec5fF H t ⊓ Submission.Blueprint.centD H t) =
      Nat.card ↥(Submission.Blueprint.centD H t) :=
    relIndex_mul_card_of_le' inf_le_right
  have hne : Submission.Blueprint.conj (1 : G) H ≠ Submission.Blueprint.conj t H := by
    rw [Work.ThreePoints.conj_one]
    intro hcon
    refine h.notMem ?_
    have ht : t ∈ Subgroup.normalizer (H : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr hcon.symm
    rwa [Work.ThreePoints.IsStronglyEmbedded.normalizer_eq h.se] at ht
  have hVodd : Odd (Nat.card ↥(Submission.Blueprint.centD H t)) :=
    Odd.of_dvd_nat (sec5f_odd_twoPoint h)
      (Subgroup.card_dvd_of_le (inf_le_left : Submission.Blueprint.centD H t ≤
        Submission.Blueprint.twoPoint H t))
  have key : ((sec5fF H t).subgroupOf (Work.NormalComplement.Sec5f.NN H t)).index =
      (sec5fF H t ⊓ Submission.Blueprint.centD H t).relIndex
        (Submission.Blueprint.centD H t) := by
    have h1 : 0 < Nat.card ↥(sec5fF H t) := Nat.card_pos
    have h2 : 0 < Nat.card ↥(sec5fF H t ⊓ Submission.Blueprint.centD H t) := Nat.card_pos
    refine Nat.mul_right_cancel (Nat.mul_pos h1 h2) ?_
    calc ((sec5fF H t).subgroupOf (Work.NormalComplement.Sec5f.NN H t)).index *
            (Nat.card ↥(sec5fF H t) * Nat.card ↥(sec5fF H t ⊓ Submission.Blueprint.centD H t))
        = (((sec5fF H t).subgroupOf (Work.NormalComplement.Sec5f.NN H t)).index *
            Nat.card ↥(sec5fF H t)) * Nat.card ↥(sec5fF H t ⊓ Submission.Blueprint.centD H t) := by
          ring
      _ = Nat.card ↥(Work.NormalComplement.Sec5f.NN H t) *
            Nat.card ↥(sec5fF H t ⊓ Submission.Blueprint.centD H t) := by rw [hLag]
      _ = Nat.card ↥(sec5fF H t ⊔ Submission.Blueprint.centD H t) *
            Nat.card ↥(sec5fF H t ⊓ Submission.Blueprint.centD H t) := by rw [← hNN]
      _ = Nat.card ↥(sec5fF H t) * Nat.card ↥(Submission.Blueprint.centD H t) := hcard_sup
      _ = Nat.card ↥(sec5fF H t) *
            ((sec5fF H t ⊓ Submission.Blueprint.centD H t).relIndex
              (Submission.Blueprint.centD H t) *
              Nat.card ↥(sec5fF H t ⊓ Submission.Blueprint.centD H t)) := by rw [hrel]
      _ = (sec5fF H t ⊓ Submission.Blueprint.centD H t).relIndex
              (Submission.Blueprint.centD H t) *
            (Nat.card ↥(sec5fF H t) *
              Nat.card ↥(sec5fF H t ⊓ Submission.Blueprint.centD H t)) := by ring
  rw [key]
  exact Odd.of_dvd_nat hVodd ⟨Nat.card ↥(sec5fF H t ⊓ Submission.Blueprint.centD H t), hrel.symm⟩

/-- **`2`-rank one of `𝒩 = N_G(V)`.**  Every involution of `𝒩` lies in `F = O^{2'}(C_G(V))`
(since `|𝒩 : F|` is odd); two distinct commuting involutions `a, b ∈ 𝒩` therefore have a common
fixed point `ω ∈ Ω`, which is a translate of `H` by some `y ∈ 𝒩`; conjugating back by `y` gives
two elements of `F ⊓ H` of order two, both equal to the unique involution `u` of `S`. -/
theorem sec5f_not_hasFourGroup_NN (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC : Submission.Blueprint.ThmCProp) {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}
    (h : Work.NormalComplement.Design.Setup5 G H t W p P A r)
    (hun : ∃! u : G, u ∈ H ∧ orderOf u = 2 ∧
        u ∈ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G)) :
    ¬ Submission.Blueprint.HasFourGroup ↥(Work.NormalComplement.Sec5f.NN H t) := by
  obtain ⟨S, hSpg, hSle, hSidx, hSnorm, hSD, hSsup, hcardS⟩ := p2a_p3_data hFT hC h
  obtain ⟨u, hu, huniq⟩ := hun
  -- ## `S ⊴ F ⊓ H` and `S` has a unique involution
  have hFHnorm : (S.subgroupOf (sec5fF H t ⊓ H)).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hSle).mpr ?_
    intro x hx
    exact hSnorm (Subgroup.mem_inf.mpr ⟨hx.2, (Work.ThreePoints.p3F_le_normalizer _) hx.1⟩)
  have hFHodd : Odd (S.subgroupOf (sec5fF H t ⊓ H)).index :=
    Nat.not_even_iff_odd.mp (by rw [even_iff_two_dvd]; exact hSidx)
  have huS : u ∈ S := by
    have huFH : u ∈ sec5fF H t ⊓ H := by
      refine Subgroup.mem_inf.mpr ⟨?_, hu.1⟩
      exact sec5f_mem_map_oddResidual_of_orderOf_two_pow hu.2.2 (k := 1) (by rw [hu.2.1, pow_one])
    haveI := hFHnorm
    have h1 : (⟨u, huFH⟩ : ↥(sec5fF H t ⊓ H)) ∈ S.subgroupOf (sec5fF H t ⊓ H) :=
      Sec5f.mem_of_orderOf_eq_two_pow_of_normal_odd_index hFHodd
        (k := 1) (by rw [← Subgroup.orderOf_coe, hu.2.1, pow_one])
    exact Subgroup.mem_subgroupOf.mp h1
  have hSinv : ∀ x : G, x ∈ S → orderOf x = 2 → x = u := by
    intro x hxS hx2
    exact huniq x ⟨(hSle hxS).2, hx2, Work.ThreePoints.p3F_le_centralizer _ (hSle hxS).1⟩
  have hFHmem : ∀ x : G, x ∈ sec5fF H t ⊓ H → orderOf x = 2 → x ∈ S := by
    intro x hx hx2
    haveI := hFHnorm
    have h1 : (⟨x, hx⟩ : ↥(sec5fF H t ⊓ H)) ∈ S.subgroupOf (sec5fF H t ⊓ H) :=
      Sec5f.mem_of_orderOf_eq_two_pow_of_normal_odd_index hFHodd
        (k := 1) (by rw [← Subgroup.orderOf_coe, hx2, pow_one])
    exact Subgroup.mem_subgroupOf.mp h1
  -- ## every involution of `𝒩` lies in `F`
  have hNNnorm : ((sec5fF H t).subgroupOf (Work.NormalComplement.Sec5f.NN H t)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer (sec5f_F_le_NN (H := H) (t := t))]
    rw [sec5f_NN_eq hFT hC h]
    refine sup_le Subgroup.le_normalizer ?_
    intro v hv
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hcomm : v * x = x * v :=
        (Subgroup.mem_centralizer_iff.mp (Work.ThreePoints.p3F_le_centralizer _ hx)) v hv
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
      exact hx
    · intro hx
      have hcomm : v⁻¹ * (v * x * v⁻¹) = (v * x * v⁻¹) * v⁻¹ :=
        (Subgroup.mem_centralizer_iff.mp (Work.ThreePoints.p3F_le_centralizer _ hx))
          v⁻¹ ((Submission.Blueprint.centD H t).inv_mem hv)
      have h1 : x = v⁻¹ * (v * x * v⁻¹) * v := by group
      rw [h1, hcomm, mul_assoc, inv_mul_cancel, mul_one]
      exact hx
  have hmemF : ∀ x : G, x ∈ Work.NormalComplement.Sec5f.NN H t → orderOf x = 2 →
      x ∈ sec5fF H t := by
    intro x hxN hx2
    haveI := hNNnorm
    have h1 : (⟨x, hxN⟩ : ↥(Work.NormalComplement.Sec5f.NN H t)) ∈
        (sec5fF H t).subgroupOf (Work.NormalComplement.Sec5f.NN H t) :=
      Sec5f.mem_of_orderOf_eq_two_pow_of_normal_odd_index (sec5f_index_NN_F_odd hFT hC h)
        (k := 1) (by rw [← Subgroup.orderOf_coe, hx2, pow_one])
    exact Subgroup.mem_subgroupOf.mp h1
  -- ## the argument
  rintro ⟨a, b, ha2, hb2, habne, habcomm⟩
  have ha2G : orderOf (a : G) = 2 := by rw [Subgroup.orderOf_coe]; exact ha2
  have hb2G : orderOf (b : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hb2
  have hcommG : (a : G) * (b : G) = (b : G) * (a : G) :=
    congrArg (fun z : ↥(Work.NormalComplement.Sec5f.NN H t) => (z : G)) habcomm
  have hneG : (a : G) ≠ (b : G) := fun hcon => habne (Subtype.ext hcon)
  have haF : (a : G) ∈ sec5fF H t := hmemF _ a.2 ha2G
  have hbF : (b : G) ∈ sec5fF H t := hmemF _ b.2 hb2G
  -- ## the (unique) fixed point `ω` of `a` lies in `Ω_V`
  obtain ⟨ω, hω⟩ := Set.ncard_eq_one.mp
    (Work.ThreePoints.ncard_fixedPts_zpowers (H := H) (t := (a : G)) h.se ha2G)
  have haω : (a : G) • ω = ω := by
    have hmem : ω ∈ Submission.Blueprint.fixedPts H (Subgroup.zpowers (a : G)) := by
      rw [hω]; exact Set.mem_singleton ω
    exact Work.ThreePoints.mem_fixedPts.mp hmem _ (Subgroup.mem_zpowers _)
  have hVleCa : Submission.Blueprint.centD H t ≤
      Subgroup.centralizer ({(a : G)} : Set G) := by
    intro v hv
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (Work.ThreePoints.p3F_le_centralizer _ haF)) v hv
  have hωV : ω ∈ Submission.Blueprint.fixedPts H (Submission.Blueprint.centD H t) := by
    rw [Work.ThreePoints.mem_fixedPts_iff_le_stabilizer]
    exact hVleCa.trans (Work.ThreePoints.centralizer_le_stabilizer h.se ha2G haω)
  -- ## `b` fixes `ω` too
  have hbω : (b : G) • ω = ω := by
    have hfix : (a : G) • ((b : G) • ω) = (b : G) • ω := by
      rw [← mul_smul, hcommG, mul_smul, haω]
    have hmem : (b : G) • ω ∈ Submission.Blueprint.fixedPts H (Subgroup.zpowers (a : G)) := by
      rw [Work.ThreePoints.mem_fixedPts_iff_le_stabilizer]
      exact Subgroup.zpowers_le.mpr (by rw [MulAction.mem_stabilizer_iff]; exact hfix)
    rw [hω] at hmem
    exact Set.mem_singleton_iff.mp hmem
  -- ## `ω` is a `𝒩`-translate of `H`
  have hbase : (QuotientGroup.mk (1 : G) : G ⧸ H) ∈
      Submission.Blueprint.fixedPts H (Submission.Blueprint.centD H t) :=
    Work.ThreePoints.pt_mem_fixedPts_of_le_centD le_rfl
  obtain ⟨y, hy, hyω⟩ := (sec5f_twoTransitive hFT hC h).isTransitiveOnSub
    (QuotientGroup.mk (1 : G)) hbase ω hωV
  have hstab : MulAction.stabilizer G ω = Submission.Blueprint.conj y H := by
    rw [← hyω, MulAction.stabilizer_smul_eq_stabilizer_map_conj, Work.ThreePoints.stabilizer_mk,
      Work.ThreePoints.conj_one]
  have haHy : (a : G) ∈ Submission.Blueprint.conj y H := by
    rw [← hstab, MulAction.mem_stabilizer_iff]; exact haω
  have hbHy : (b : G) ∈ Submission.Blueprint.conj y H := by
    rw [← hstab, MulAction.mem_stabilizer_iff]; exact hbω
  -- ## conjugating back by `y` produces elements of `F ⊓ H` of order two, hence equal to `u`
  have hkey : ∀ x : G, x ∈ Work.NormalComplement.Sec5f.NN H t →
      x ∈ Submission.Blueprint.conj y H → orderOf x = 2 → x = y * u * y⁻¹ := by
    intro x hxN hxH hx2
    have hxH' : y⁻¹ * x * y ∈ H := Work.ThreePoints.mem_conj_iff.mp hxH
    have hxN' : y⁻¹ * x * y ∈ Work.NormalComplement.Sec5f.NN H t :=
      (Work.NormalComplement.Sec5f.NN H t).mul_mem
        ((Work.NormalComplement.Sec5f.NN H t).mul_mem
          ((Work.NormalComplement.Sec5f.NN H t).inv_mem hy) hxN) hy
    have hx2' : orderOf (y⁻¹ * x * y) = 2 := by
      rw [← MulEquiv.orderOf_eq (MulAut.conj y) (y⁻¹ * x * y)]
      rw [show (MulAut.conj y) (y⁻¹ * x * y) = x from by rw [MulAut.conj_apply]; group]
      exact hx2
    have hxF' : y⁻¹ * x * y ∈ sec5fF H t := hmemF _ hxN' hx2'
    have hmem : y⁻¹ * x * y ∈ S := hFHmem _ (Subgroup.mem_inf.mpr ⟨hxF', hxH'⟩) hx2'
    have h1 : y⁻¹ * x * y = u := hSinv _ hmem hx2'
    calc x = y * (y⁻¹ * x * y) * y⁻¹ := by group
      _ = y * u * y⁻¹ := by rw [h1]
  have haeq : (a : G) = y * u * y⁻¹ := hkey _ a.2 haHy ha2G
  have hbeq : (b : G) = y * u * y⁻¹ := hkey _ b.2 hbHy hb2G
  exact hneG (haeq.trans hbeq.symm)

/-- An element of a `2`-subgroup has `2`-power order. -/
theorem sec5f_orderOf_eq_two_pow_of_mem_isPGroup {L : Type} [Group L] {Q : Subgroup L}
    (hQ : IsPGroup 2 Q) {x : L} (hx : x ∈ Q) : ∃ k, orderOf x = 2 ^ k := by
  obtain ⟨k, hk⟩ := hQ (⟨x, hx⟩ : ↥Q)
  have hdvd : orderOf (⟨x, hx⟩ : ↥Q) ∣ 2 ^ k := orderOf_dvd_iff_pow_eq_one.mpr hk
  obtain ⟨j, -, hje⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  exact ⟨j, (Subgroup.orderOf_coe (⟨x, hx⟩ : ↥Q)).trans hje⟩

/-- **The Sylow `2`-subgroup `S` of `F ⊓ H`** (`F = O^{2'}(C_G(V))`): it has a unique involution
(by `hun`), exponent dividing `4` (`BenderModelFacts2Prop` 1° via `p2a_pow_four`), hence order
`2`, `4` or `8`; consequently `|Ω_V| = |S| + 1 ∈ {3, 5, 9}`. -/
theorem sec5f_S_card (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC : Submission.Blueprint.ThmCProp) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hMF2 : Submission.Blueprint.BenderModelFacts2Prop) {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}
    (h : Work.NormalComplement.Design.Setup5 G H t W p P A r)
    (hun : ∃! u : G, u ∈ H ∧ orderOf u = 2 ∧
        u ∈ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G)) :
    ∃ S : Subgroup G, IsPGroup 2 S ∧ S ≤ sec5fF H t ⊓ H ∧
      ¬ 2 ∣ (S.subgroupOf (sec5fF H t ⊓ H)).index ∧
      {x : G | x ∈ S ∧ orderOf x = 2}.ncard = 1 ∧
      (∀ x ∈ S, x ^ 4 = 1) ∧
      ((S : Set G).ncard = 2 ∨ (S : Set G).ncard = 4 ∨ (S : Set G).ncard = 8) ∧
      (Submission.Blueprint.fixedPts H (Submission.Blueprint.centD H t)).ncard ∈
        ({3, 5, 9} : Set ℕ) := by
  obtain ⟨S, hSpg, hSle, hSidx, hSnorm, hSD, hSsup, hcardS⟩ := p2a_p3_data hFT hC h
  obtain ⟨u, hu, huniq⟩ := hun
  -- ## `S ⊴ F ⊓ H`
  have hFHnorm : (S.subgroupOf (sec5fF H t ⊓ H)).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hSle).mpr ?_
    intro x hx
    exact hSnorm (Subgroup.mem_inf.mpr ⟨hx.2, (Work.ThreePoints.p3F_le_normalizer _) hx.1⟩)
  have hFHodd : Odd (S.subgroupOf (sec5fF H t ⊓ H)).index :=
    Nat.not_even_iff_odd.mp (by rw [even_iff_two_dvd]; exact hSidx)
  -- ## the unique involution of `S` is `u`
  have huS : u ∈ S := by
    have huFH : u ∈ sec5fF H t ⊓ H :=
      ⟨sec5f_mem_map_oddResidual_of_orderOf_two_pow hu.2.2 (k := 1)
        (by rw [hu.2.1, pow_one]), hu.1⟩
    haveI := hFHnorm
    have h1 : (⟨u, huFH⟩ : ↥(sec5fF H t ⊓ H)) ∈ S.subgroupOf (sec5fF H t ⊓ H) :=
      Sec5f.mem_of_orderOf_eq_two_pow_of_normal_odd_index hFHodd
        (k := 1) (by rw [← Subgroup.orderOf_coe, hu.2.1, pow_one])
    exact Subgroup.mem_subgroupOf.mp h1
  have huniqS : {x : G | x ∈ S ∧ orderOf x = 2}.ncard = 1 := by
    have hset : {x : G | x ∈ S ∧ orderOf x = 2} = {u} := by
      ext x
      constructor
      · rintro ⟨hxS, hx2⟩
        rw [Set.mem_singleton_iff]
        exact huniq x ⟨(hSle hxS).2, hx2, Work.ThreePoints.p3F_le_centralizer _ (hSle hxS).1⟩
      · intro hx
        rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact ⟨huS, hu.2.1⟩
    rw [hset, Set.ncard_singleton]
  -- ## the exponent of `S` divides `4`
  have hexp : ∀ x ∈ S, x ^ 4 = 1 := by
    intro x hxS
    obtain ⟨k, hk⟩ := sec5f_orderOf_eq_two_pow_of_mem_isPGroup hSpg hxS
    have hxV : x ∈ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G) :=
      Work.ThreePoints.p3F_le_centralizer _ (hSle hxS).1
    have hxA : x ∈ Subgroup.centralizer (A : Set G) := Subgroup.centralizer_le h.A_le hxV
    have hxF : x ∈ Work.ThreePoints.p3F A := sec5f_mem_map_oddResidual_of_orderOf_two_pow hxA hk
    exact p2a_pow_four hFT hC hC4 hMF2 h x (hSle hxS).2 hxF ⟨k, hk⟩
  -- ## `|S| ∈ {2, 4, 8}`
  have hScard : (S : Set G).ncard = 2 ∨ (S : Set G).ncard = 4 ∨ (S : Set G).ncard = 8 := by
    have huniqInv : Work.BrauerSuzuki.HasUniqueInvolution ↥S :=
      p2a_appIII_hasUniqueInvolution_of_ncard_eq_one (by
        rw [Submission.Blueprint.involutions]
        exact huniqS)
    have hge : 2 ≤ Nat.card ↥S := by
      have h3 : 3 ≤ (Submission.Blueprint.fixedPts H (Submission.Blueprint.centD H t)).ncard :=
        Work.ThreePoints.P3NeBot.three_le_ncard_fixedPts_of_le_centD h.se h.invol h.notMem
          (X := Submission.Blueprint.centD H t) le_rfl
      rw [← p2a_appIII_ncard_sub_eq_natCard S]
      omega
    rcases Work.BrauerSuzuki.Group.isCyclicOrGenQuaternion_of_uniqueInvolution hSpg huniqInv with
      hcyc | hgen
    · have hle : Nat.card ↥S ≤ 4 := p2a_appIII_cyclic_card_le_four hcyc hexp
      obtain ⟨k, hk⟩ := hSpg.exists_card_eq
      have hk1 : 1 ≤ k := by
        by_contra hcon
        have h0 : k = 0 := by omega
        rw [hk, h0] at hge
        norm_num at hge
      have hk2 : k ≤ 2 := by
        by_contra hcon
        have h3 : 3 ≤ k := by omega
        have h8 : 8 ≤ 2 ^ k := by
          calc 8 = 2 ^ 3 := by norm_num
            _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h3
        rw [hk] at hle
        omega
      rw [p2a_appIII_ncard_sub_eq_natCard S]
      interval_cases k <;> simp [hk]
    · have h8 : Nat.card ↥S = 8 := p2a_appIII_genQuaternion_card_eq_eight hgen hexp
      rw [p2a_appIII_ncard_sub_eq_natCard S, h8]
      exact Or.inr (Or.inr rfl)
  refine ⟨S, hSpg, hSle, hSidx, huniqS, hexp, hScard, ?_⟩
  -- ## `|Ω_V| ∈ {3, 5, 9}`
  rw [hcardS]
  rcases hScard with h2 | h4 | h8
  · rw [h2]; norm_num
  · rw [h4]; norm_num
  · rw [h8]; norm_num

/-- **Appendix III (2)–(5) applied to `𝒩 ⧸ K`** (Peterfalvi I Ch. III §5 Prop. 2 (a)): there is
a prime `f` with `f ∣ |Ω_V|` and `(ut)^f ∈ K` for every involution `u ∈ H` centralising `V`. -/
theorem sec5f_appIII_step (hFT : Submission.Blueprint.FeitThompsonProp)
    (hIII : Work.NormalComplement.AppIIIProp) {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}
    (h : Work.NormalComplement.Design.Setup5 G H t W p P A r)
    (h2t : MulAction.IsMultiplyPretransitive (↥(Work.NormalComplement.Sec5f.NN H t)
        ⧸ Work.NormalComplement.Sec5f.KK H t) (Work.NormalComplement.Sec5f.Omega H t) 2)
    (hfaith : ∀ g : ↥(Work.NormalComplement.Sec5f.NN H t)
        ⧸ Work.NormalComplement.Sec5f.KK H t,
      (∀ ω : Work.NormalComplement.Sec5f.Omega H t, g • ω = ω) → g = 1)
    (hSE : LeanEval.GroupTheory.Defs.IsStronglyEmbedded
      (MulAction.stabilizer (↥(Work.NormalComplement.Sec5f.NN H t)
        ⧸ Work.NormalComplement.Sec5f.KK H t) (Work.NormalComplement.Sec5f.ptV H t)))
    (hcoatom : IsCoatom
      (MulAction.stabilizer (↥(Work.NormalComplement.Sec5f.NN H t)
        ⧸ Work.NormalComplement.Sec5f.KK H t) (Work.NormalComplement.Sec5f.ptV H t)))
    (hNE : ¬ Submission.Blueprint.HasFourGroup
      (↥(Work.NormalComplement.Sec5f.NN H t) ⧸ Work.NormalComplement.Sec5f.KK H t))
    {u : G} (hu : u ∈ H ∧ orderOf u = 2 ∧
      u ∈ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G)) :
    ∃ f : ℕ, f.Prime ∧
      f ∣ (Submission.Blueprint.fixedPts H (Submission.Blueprint.centD H t)).ncard ∧
      (u * t) ^ f ∈ (Work.NormalComplement.Sec5f.KK H t).map
        (Work.NormalComplement.Sec5f.NN H t).subtype := by
  classical
  have hinvol : orderOf t = 2 := h.invol
  have hnotMem : t ∉ H := h.notMem
  obtain ⟨f, Q, hfprime, hQnorm, hQne, hQab, hQexp, hQinf, hQsup, huniqInv, hcl4, -, -⟩ :=
    hIII (↥(Work.NormalComplement.Sec5f.NN H t) ⧸ Work.NormalComplement.Sec5f.KK H t)
      (Work.NormalComplement.Sec5f.Omega H t) (Work.NormalComplement.Sec5f.ptV H t)
      MulAction.isPretransitive_of_is_two_pretransitive hfaith hNE hSE hcoatom
  haveI := hQnorm
  set Fq := ↥(Work.NormalComplement.Sec5f.NN H t) ⧸ Work.NormalComplement.Sec5f.KK H t with hFq
  set stab := MulAction.stabilizer
    (↥(Work.NormalComplement.Sec5f.NN H t) ⧸ Work.NormalComplement.Sec5f.KK H t)
    (Work.NormalComplement.Sec5f.ptV H t) with hstabdef
  -- ## `f` divides `|Q|`
  have hfQ : f ∣ Nat.card ↥Q := by
    have hQbot : Q ≠ ⊥ := hQne
    have hnotle : ¬ Q ≤ ⊥ := fun hle => hQbot (le_bot_iff.mp hle)
    obtain ⟨x, hxQ, hxbot⟩ := SetLike.not_le_iff_exists.mp hnotle
    have hxne : x ≠ 1 := fun hcon => hxbot (hcon ▸ Subgroup.mem_bot.mpr rfl)
    have h1 : orderOf x ∣ f := orderOf_dvd_iff_pow_eq_one.mpr (hQexp x hxQ)
    have h2 : orderOf x = f := by
      rcases hfprime.eq_one_or_self_of_dvd _ h1 with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hxne
      · exact h
    rw [← h2]
    exact Subgroup.orderOf_dvd_natCard Q hxQ
  -- ## `|Q| = |Ω_V|`
  have hQcard : Nat.card ↥Q = (Submission.Blueprint.fixedPts H
      (Submission.Blueprint.centD H t)).ncard := by
    have hinj : Function.Injective (fun q : ↥Q => (q : Fq) • Work.NormalComplement.Sec5f.ptV H t) := by
      intro q q' hqq'
      have hqq'' : (q : Fq) • Work.NormalComplement.Sec5f.ptV H t
          = (q' : Fq) • Work.NormalComplement.Sec5f.ptV H t := hqq'
      have hmem : (q : Fq)⁻¹ * (q' : Fq) ∈ Q ⊓ stab := by
        refine Subgroup.mem_inf.mpr ⟨Q.mul_mem (Q.inv_mem q.2) q'.2, ?_⟩
        rw [hstabdef, MulAction.mem_stabilizer_iff]
        rw [mul_smul, ← hqq'', inv_smul_smul]
      rw [hQinf] at hmem
      rw [Subgroup.mem_bot] at hmem
      rw [inv_mul_eq_one] at hmem
      exact Subtype.ext hmem
    haveI : MulAction.IsMultiplyPretransitive Fq (Work.NormalComplement.Sec5f.Omega H t) 2 := h2t
    haveI : MulAction.IsPretransitive Fq (Work.NormalComplement.Sec5f.Omega H t) :=
      MulAction.isPretransitive_of_is_two_pretransitive
    have hsurj : Function.Surjective (fun q : ↥Q => (q : Fq) • Work.NormalComplement.Sec5f.ptV H t) := by
      intro ω
      obtain ⟨g, hg⟩ := (MulAction.IsPretransitive.exists_smul_eq
        (M := Fq) (Work.NormalComplement.Sec5f.ptV H t) ω)
      obtain ⟨q, hqQ, h₂, hh, hqh⟩ := Subgroup.mem_sup_of_normal_left.mp
        ((le_of_eq hQsup.symm) (Subgroup.mem_top g))
      refine ⟨⟨q, hqQ⟩, ?_⟩
      show q • Work.NormalComplement.Sec5f.ptV H t = ω
      calc q • Work.NormalComplement.Sec5f.ptV H t
          = q • (h₂ • Work.NormalComplement.Sec5f.ptV H t) := by
            rw [MulAction.mem_stabilizer_iff.mp hh]
        _ = (q * h₂) • Work.NormalComplement.Sec5f.ptV H t := (mul_smul q h₂ _).symm
        _ = g • Work.NormalComplement.Sec5f.ptV H t := by rw [hqh]
        _ = ω := hg
    have hbij : Function.Bijective
        (fun q : ↥Q => (q : Fq) • Work.NormalComplement.Sec5f.ptV H t) := ⟨hinj, hsurj⟩
    have hcard := Nat.card_congr (Equiv.ofBijective _ hbij)
    rw [Set.ncard_def]
    exact hcard
  -- ## the images of `u` and `t` in `𝒩 ⧸ K`
  have huN : u ∈ Work.NormalComplement.Sec5f.NN H t :=
    Subgroup.centralizer_le_normalizer _ hu.2.2
  have htN : t ∈ Work.NormalComplement.Sec5f.NN H t := by
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact Subgroup.mem_centralizer_singleton_iff.mp
      ((inf_le_right : Submission.Blueprint.centD H t ≤
        Subgroup.centralizer ({t} : Set G)) hv)
  set ub := QuotientGroup.mk' (Work.NormalComplement.Sec5f.KK H t)
    (⟨u, huN⟩ : ↥(Work.NormalComplement.Sec5f.NN H t)) with hubdef
  set tb := QuotientGroup.mk' (Work.NormalComplement.Sec5f.KK H t)
    (⟨t, htN⟩ : ↥(Work.NormalComplement.Sec5f.NN H t)) with htbdef
  have hubeq : ub = QuotientGroup.mk' (Work.NormalComplement.Sec5f.KK H t)
      (⟨u, huN⟩ : ↥(Work.NormalComplement.Sec5f.NN H t)) := rfl
  have htbneq : tb = QuotientGroup.mk' (Work.NormalComplement.Sec5f.KK H t)
      (⟨t, htN⟩ : ↥(Work.NormalComplement.Sec5f.NN H t)) := rfl
  -- `u ∉ K` and `t ∉ K`
  have huK : (⟨u, huN⟩ : ↥(Work.NormalComplement.Sec5f.NN H t)) ∉
      Work.NormalComplement.Sec5f.KK H t := by
    intro hmem
    have h1 : u ∈ Submission.Blueprint.twoPoint H t :=
      Work.NormalComplement.Sec5f.KK_map_le_twoPoint
        (Subgroup.mem_map.mpr ⟨⟨u, huN⟩, hmem, rfl⟩)
    have hodd : Odd (Nat.card ↥(Submission.Blueprint.twoPoint H t)) := sec5f_odd_twoPoint h
    have h2 : orderOf u ∣ Nat.card ↥(Submission.Blueprint.twoPoint H t) :=
      Subgroup.orderOf_dvd_natCard _ h1
    rw [hu.2.1] at h2
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  have htK : (⟨t, htN⟩ : ↥(Work.NormalComplement.Sec5f.NN H t)) ∉
      Work.NormalComplement.Sec5f.KK H t := by
    intro hmem
    have h1 : t ∈ Submission.Blueprint.twoPoint H t :=
      Work.NormalComplement.Sec5f.KK_map_le_twoPoint
        (Subgroup.mem_map.mpr ⟨⟨t, htN⟩, hmem, rfl⟩)
    exact h.notMem (Subgroup.mem_inf.mp h1).1
  have hub2 : orderOf ub = 2 := by
    have hdvd : orderOf ub ∣ 2 := by
      have h := orderOf_map_dvd (QuotientGroup.mk' (Work.NormalComplement.Sec5f.KK H t))
        (⟨u, huN⟩ : ↥(Work.NormalComplement.Sec5f.NN H t))
      rw [← Subgroup.orderOf_coe, hu.2.1] at h
      rw [hubeq]; exact h
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exfalso
      apply huK
      have h1' : QuotientGroup.mk' (Work.NormalComplement.Sec5f.KK H t)
          (⟨u, huN⟩ : ↥(Work.NormalComplement.Sec5f.NN H t)) = 1 := by
        rw [← hubeq]; exact orderOf_eq_one_iff.mp h
      exact (QuotientGroup.eq_one_iff _).mp h1'
    · exact h
  have htb2 : orderOf tb = 2 := by
    have hdvd : orderOf tb ∣ 2 := by
      have h := orderOf_map_dvd (QuotientGroup.mk' (Work.NormalComplement.Sec5f.KK H t))
        (⟨t, htN⟩ : ↥(Work.NormalComplement.Sec5f.NN H t))
      rw [← Subgroup.orderOf_coe, hinvol] at h
      rw [htbneq]; exact h
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exfalso
      apply htK
      have h1' : QuotientGroup.mk' (Work.NormalComplement.Sec5f.KK H t)
          (⟨t, htN⟩ : ↥(Work.NormalComplement.Sec5f.NN H t)) = 1 := by
        rw [← htbneq]; exact orderOf_eq_one_iff.mp h
      exact (QuotientGroup.eq_one_iff _).mp h1'
    · exact h
  -- `ub` lies in the point stabiliser, `tb` does not
  have hubStab : ub ∈ stab := by
    rw [hstabdef, Work.NormalComplement.Sec5f.stabilizer_ptV_quot, Subgroup.mem_map]
    refine ⟨⟨u, huN⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨huN, hu.1⟩), rfl⟩
  have htbStab : tb ∉ stab := by
    intro hmem
    rw [hstabdef, MulAction.mem_stabilizer_iff] at hmem
    rw [htbneq, Work.NormalComplement.Sec5f.quotient_smul_mk] at hmem
    exact h.notMem ((Work.NormalComplement.Sec5f.smul_ptV_eq_iff
      (⟨t, htN⟩ : ↥(Work.NormalComplement.Sec5f.NN H t))).mp hmem)
  have hne' : ub ≠ tb := fun hcon => htbStab (hcon ▸ hubStab)
  obtain ⟨-, hord⟩ := hcl4 ub tb hub2 htb2 hne'
  -- ## `(ut)^f ∈ K`
  have hutN : u * t ∈ Work.NormalComplement.Sec5f.NN H t :=
    (Work.NormalComplement.Sec5f.NN H t).mul_mem huN htN
  have hmk : QuotientGroup.mk' (Work.NormalComplement.Sec5f.KK H t)
      (⟨u * t, hutN⟩ : ↥(Work.NormalComplement.Sec5f.NN H t)) = ub * tb := by
    rw [hubeq, htbneq, ← map_mul]
    rfl
  have hker_eq : QuotientGroup.mk' (Work.NormalComplement.Sec5f.KK H t)
      ((⟨u * t, hutN⟩ : ↥(Work.NormalComplement.Sec5f.NN H t)) ^ f) = 1 := by
    rw [map_pow, hmk, ← hord, pow_orderOf_eq_one]
  have hker : ((⟨u * t, hutN⟩ : ↥(Work.NormalComplement.Sec5f.NN H t)) ^ f) ∈
      Work.NormalComplement.Sec5f.KK H t := by
    rw [← QuotientGroup.ker_mk' (Work.NormalComplement.Sec5f.KK H t)]
    exact MonoidHom.mem_ker.mpr hker_eq
  refine ⟨f, hfprime, ?_, ?_⟩
  · rw [← hQcard]
    exact hfQ
  · refine Subgroup.mem_map.mpr ⟨(⟨u * t, hutN⟩ : ↥(Work.NormalComplement.Sec5f.NN H t)) ^ f,
      hker, ?_⟩
    exact Subgroup.coe_pow (Work.NormalComplement.Sec5f.NN H t)
      (⟨u * t, hutN⟩ : ↥(Work.NormalComplement.Sec5f.NN H t)) f

/-- **The final step of §5 Prop. 2 (a)**: with `f` the prime produced by Appendix III, the element
`(ut)^f` lies in the kernel `K` and is inverted by `u`; Theorem C (`hC`) shows that `u` centralises
`K` (its image lies in the two-point stabiliser `H ⊓ H^t`), so `(ut)^f = 1` and `ut` has order
`f ∈ {3,5}`. -/
theorem sec5f_final (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC : Submission.Blueprint.ThmCProp) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hIII : Work.NormalComplement.AppIIIProp)
    (hMF2 : Submission.Blueprint.BenderModelFacts2Prop) {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}
    (h : Work.NormalComplement.Design.Setup5 G H t W p P A r)
    (hun : ∃! u : G, u ∈ H ∧ orderOf u = 2 ∧
        u ∈ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G))
    (h2t : MulAction.IsMultiplyPretransitive (↥(Work.NormalComplement.Sec5f.NN H t)
        ⧸ Work.NormalComplement.Sec5f.KK H t) (Work.NormalComplement.Sec5f.Omega H t) 2)
    (hfaith : ∀ g : ↥(Work.NormalComplement.Sec5f.NN H t)
        ⧸ Work.NormalComplement.Sec5f.KK H t,
      (∀ ω : Work.NormalComplement.Sec5f.Omega H t, g • ω = ω) → g = 1)
    (hSE : LeanEval.GroupTheory.Defs.IsStronglyEmbedded
      (MulAction.stabilizer (↥(Work.NormalComplement.Sec5f.NN H t)
        ⧸ Work.NormalComplement.Sec5f.KK H t) (Work.NormalComplement.Sec5f.ptV H t)))
    (hcoatom : IsCoatom
      (MulAction.stabilizer (↥(Work.NormalComplement.Sec5f.NN H t)
        ⧸ Work.NormalComplement.Sec5f.KK H t) (Work.NormalComplement.Sec5f.ptV H t)))
    (u : G) (huH : u ∈ H) (hu2 : orderOf u = 2)
    (huC : u ∈ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G)) :
    orderOf (u * t) = 3 ∨ orderOf (u * t) = 5 := by
  classical
  -- ## `¬HasFourGroup` for `𝒩` and for `𝒩 ⧸ K`
  have hKle : Work.NormalComplement.Sec5f.KK H t ≤
      (Work.NormalComplement.Sec5f.NN H t ⊓ H).subgroupOf (Work.NormalComplement.Sec5f.NN H t) :=
    Work.NormalComplement.Sec5f.KK_le_subgroupOf
  have hKodd : Odd (Nat.card ↥(Work.NormalComplement.Sec5f.KK H t)) := by
    have h1 : Nat.card ↥(Work.NormalComplement.Sec5f.KK H t) =
        Nat.card ↥((Work.NormalComplement.Sec5f.KK H t).map
          (Work.NormalComplement.Sec5f.NN H t).subtype) :=
      (Subgroup.card_map_of_injective (f := (Work.NormalComplement.Sec5f.NN H t).subtype)
        Subtype.coe_injective).symm
    rw [h1]
    exact Odd.of_dvd_nat (sec5f_odd_twoPoint h)
      (Subgroup.card_dvd_of_le Work.NormalComplement.Sec5f.KK_map_le_twoPoint)
  have hNE : ¬ Submission.Blueprint.HasFourGroup
      (↥(Work.NormalComplement.Sec5f.NN H t) ⧸ Work.NormalComplement.Sec5f.KK H t) :=
    Work.ThreePoints.P3NeBot.not_hasFourGroup_quotient (Work.NormalComplement.Sec5f.KK H t)
      hKodd (sec5f_not_hasFourGroup_NN hFT hC h hun)
  -- ## Appendix III: a prime `f ∣ |Ω_V|` with `(ut)^f ∈ K`
  obtain ⟨f, hfprime, hfdvd, hfk⟩ :=
    sec5f_appIII_step hFT hIII h h2t hfaith hSE hcoatom hNE ⟨huH, hu2, huC⟩
  -- ## the Sylow `2`-subgroup `S` and `|Ω_V| ∈ {3,5,9}`
  obtain ⟨S, hSpg, hSle, hSidx, huniqS, hexp, hScard, hΩmem⟩ :=
    sec5f_S_card hFT hC hC4 hMF2 h hun
  -- ## `f ∈ {3,5}`
  have hf35 : f = 3 ∨ f = 5 := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hΩmem
    rcases hΩmem with h3 | h5 | h9
    · rw [h3] at hfdvd
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hfdvd with hh | hh
      · exact absurd hh hfprime.ne_one
      · exact Or.inl hh
    · rw [h5] at hfdvd
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hfdvd with hh | hh
      · exact absurd hh hfprime.ne_one
      · exact Or.inr hh
    · rw [h9, show (9 : ℕ) = 3 ^ 2 from by norm_num] at hfdvd
      have h3dvd : f ∣ 3 := hfprime.dvd_of_dvd_pow hfdvd
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp h3dvd with hh | hh
      · exact absurd hh hfprime.ne_one
      · exact Or.inl hh
  -- ## the image `Z` of `K` in `G` is centralised by `u` (Theorem C)
  set Z : Subgroup G := (Work.NormalComplement.Sec5f.KK H t).map
    (Work.NormalComplement.Sec5f.NN H t).subtype with hZdef
  have hZle : Z ≤ Submission.Blueprint.twoPoint H t :=
    Work.NormalComplement.Sec5f.KK_map_le_twoPoint
  have huN : u ∈ Work.NormalComplement.Sec5f.NN H t :=
    Subgroup.centralizer_le_normalizer _ huC
  have hZodd : Odd (Nat.card ↥Z) :=
    Odd.of_dvd_nat (sec5f_odd_twoPoint h) (Subgroup.card_dvd_of_le hZle)
  have hKnormal : (Work.NormalComplement.Sec5f.KK H t).Normal := inferInstance
  have huZ : u ∈ Subgroup.normalizer (Z : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine Subgroup.mem_map.mpr ⟨(⟨u, huN⟩ : ↥(Work.NormalComplement.Sec5f.NN H t)) * y *
        (⟨u, huN⟩ : ↥(Work.NormalComplement.Sec5f.NN H t))⁻¹,
        hKnormal.conj_mem y hy ⟨u, huN⟩, ?_⟩
      rfl
    · rintro ⟨y, hy, hyx⟩
      refine Subgroup.mem_map.mpr ⟨(⟨u, huN⟩ : ↥(Work.NormalComplement.Sec5f.NN H t))⁻¹ * y *
        ((⟨u, huN⟩ : ↥(Work.NormalComplement.Sec5f.NN H t))⁻¹)⁻¹, ?_, ?_⟩
      · simpa only [inv_inv] using hKnormal.conj_mem y hy
          (⟨u, huN⟩ : ↥(Work.NormalComplement.Sec5f.NN H t))⁻¹
      · have hyx' : (y : G) = u * x * u⁻¹ := hyx
        show ((⟨u, huN⟩ : ↥(Work.NormalComplement.Sec5f.NN H t))⁻¹ : G) * (y : G) *
            (((⟨u, huN⟩ : ↥(Work.NormalComplement.Sec5f.NN H t))⁻¹)⁻¹ : G) = x
        rw [hyx']
        group
  have hcentZ : ∀ x ∈ Z, u * x = x * u :=
    hC G h.sit H h.se t h.notMem u ⟨huH, hu2⟩ Z hZle huZ
  -- ## `(ut)^f = 1`
  have hzinv : u * ((u * t) ^ f) * u⁻¹ = ((u * t) ^ f)⁻¹ := by
    have hu1 : u * u = 1 := by rw [← pow_two, ← hu2]; exact pow_orderOf_eq_one u
    have ht1 : t * t = 1 := by rw [← pow_two, ← h.invol]; exact pow_orderOf_eq_one t
    have h1 : MulAut.conj u (u * t) = (u * t)⁻¹ := by
      rw [MulAut.conj_apply,
        show u * (u * t) * u⁻¹ = (u * u) * t * u⁻¹ from by group, hu1, one_mul,
        mul_inv_rev, inv_eq_of_mul_eq_one_right ht1, inv_eq_of_mul_eq_one_right hu1]
    calc u * ((u * t) ^ f) * u⁻¹ = (MulAut.conj u) ((u * t) ^ f) := by
          rw [MulAut.conj_apply]
      _ = ((MulAut.conj u) (u * t)) ^ f := map_pow (MulAut.conj u) (u * t) f
      _ = ((u * t)⁻¹) ^ f := by rw [h1]
      _ = ((u * t) ^ f)⁻¹ := inv_pow _ _
  have hz1 : (u * t) ^ f = 1 := by
    have heq : (u * t) ^ f = ((u * t) ^ f)⁻¹ := by
      rw [← hzinv, hcentZ _ hfk, mul_assoc, mul_inv_cancel, mul_one]
    have h2 : (u * t) ^ f * (u * t) ^ f = 1 :=
      (mul_eq_one_iff_eq_inv).mpr heq
    have hdvd2 : orderOf ((u * t) ^ f) ∣ 2 :=
      orderOf_dvd_iff_pow_eq_one.mpr (by rwa [pow_two])
    have hle : orderOf ((u * t) ^ f) ∣ Nat.card ↥Z :=
      Subgroup.orderOf_dvd_natCard Z hfk
    have hone : orderOf ((u * t) ^ f) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with hh | hh
      · exact hh
      · exfalso
        have h2dvd : 2 ∣ Nat.card ↥Z := hh ▸ hle
        exact (Nat.not_even_iff_odd.mpr hZodd) (even_iff_two_dvd.mpr h2dvd)
    exact orderOf_eq_one_iff.mp hone
  -- ## conclusion
  have hdvd : orderOf (u * t) ∣ f := orderOf_dvd_iff_pow_eq_one.mpr hz1
  have hne1 : orderOf (u * t) ≠ 1 := by
    intro hcon
    have h1 : u * t = 1 := orderOf_eq_one_iff.mp hcon
    have h2 : t = u⁻¹ := eq_inv_of_mul_eq_one_right h1
    have hu1 : u * u = 1 := by rw [← pow_two, ← hu2]; exact pow_orderOf_eq_one u
    exact h.notMem (by rw [h2, inv_eq_of_mul_eq_one_right hu1]; exact huH)
  have hfeq : orderOf (u * t) = f := by
    rcases hfprime.eq_one_or_self_of_dvd _ hdvd with hh | hh
    · exact absurd hh hne1
    · exact hh
  rw [hfeq]
  exact hf35

theorem sec5_prereq_f (hFT : Submission.Blueprint.FeitThompsonProp) (hC : Submission.Blueprint.ThmCProp)
    (hC4 : Submission.Blueprint.ChIIFourProp)
    (hP3 : Submission.Blueprint.ChIIFourP3SubnormalProp)
    (hIII : Work.NormalComplement.AppIIIProp)
    (hMF2 : Submission.Blueprint.BenderModelFacts2Prop) {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}
    (h : Work.NormalComplement.Design.Setup5 G H t W p P A r)
    (hun : ∃! u : G, u ∈ H ∧ orderOf u = 2 ∧
        u ∈ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G))
    (hbd : ∀ u : G, u ∈ H → orderOf u = 2 →
        u ∈ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G) →
        let C := Subgroup.centralizer (A : Set G)
        let F₀ := (Submission.Blueprint.oddResidual ↥C).map C.subtype
        ∃ (Y : Type) (_ : Group Y) (_ : Finite Y) (φ : F₀ →* Y) (HY : Subgroup Y),
          Function.Surjective φ ∧ φ.ker = Subgroup.center ↥F₀ ∧
          LeanEval.GroupTheory.Defs.IsSimpleBenderGroup Y ∧
          LeanEval.GroupTheory.Defs.IsStronglyEmbedded HY ∧
          Submission.Blueprint.IsZassenhaus HY ∧
          (Submission.Blueprint.involutions (HY : Set Y)).ncard = 2 ^ p - 1 ∧
          ∃ (hu0 : u ∈ F₀) (ht0 : t ∈ F₀),
            φ ⟨u, hu0⟩ ∈ HY ∧ orderOf (φ ⟨u, hu0⟩) = 2 ∧ φ ⟨t, ht0⟩ ∉ HY ∧
            orderOf (φ ⟨t, ht0⟩) = 2 ∧
            ∀ x : F₀, (x : G) ∈ H → φ x ∈ HY) :
    ∀ u : G, u ∈ H → orderOf u = 2 →
      u ∈ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G) →
      orderOf (u * t) = 3 ∨ orderOf (u * t) = 5 := by
  intro u huH hu2 huC
  obtain ⟨-, h2t, hfaith, hSE, hcoatom⟩ :=
    Work.NormalComplement.Sec5Fix.sec5f_quot_action_facts hFT hC h
  exact sec5f_final hFT hC hC4 hIII hMF2 h hun h2t hfaith hSE hcoatom u huH hu2 huC

end Work.NormalComplement
