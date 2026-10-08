import Mathlib
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.Sections
import Submission.Work.NormalComplement.appIII
import Submission.Work.NormalComplement.appI_five_b
import Submission.Work.NormalComplement.sec4_one_c
import Submission.Work.NormalComplement.sec5_setup
import Submission.Work.NormalComplement.sec5_prop1
import Submission.Work.NormalComplement.bender_prelim
import Submission.Work.NormalComplement.burnsideClassProp
import Submission.Work.ThreePoints.ThmC.ch2_sec2_lem1
import Submission.Work.ThreePoints.P3NeBot.app3_1
import Submission.Work.ThreePoints.involutions_conj_of_stronglyEmbedded
import Submission.Work.BrauerSuzuki.Main
import Submission.Work.BrauerSuzuki.Group.isCyclicOrGenQuaternion_of_uniqueInvolution
import Submission.Work.NormalComplement.Sec5CKappa.prop2a_orderof

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 1600000

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.NormalComplement

variable {G : Type} [Group G] [Finite G]

/-! ## The action of `N_G(P)` on `Ω_P = fixedPts H P` -/

/-- `N_G(P)` acts on the set `Ω_P = fixedPts H P` of fixed points of `P` in `G ⧸ H`: an element
normalising `P` permutes the fixed points of `P`. -/
instance instSMulNormalizerFixedPts {H P : Subgroup G} :
    SMul (Subgroup.normalizer (P : Set G)) ↥(Submission.Blueprint.fixedPts H P) where
  smul m ω := ⟨(m : G) • (ω : G ⧸ H),
    Work.ThreePoints.ThmC.fixedPts_smul_mem (H := H) (P := P) m.2 ω.2⟩

instance instMulActionNormalizerFixedPts {H P : Subgroup G} :
    MulAction (Subgroup.normalizer (P : Set G)) ↥(Submission.Blueprint.fixedPts H P) :=
  { one_smul := fun ω => Subtype.ext (one_smul G (ω : G ⧸ H))
    mul_smul := fun m n ω => Subtype.ext (mul_smul (m : G) (n : G) (ω : G ⧸ H)) }

theorem kappa_smul_val {H P : Subgroup G} (m : Subgroup.normalizer (P : Set G))
    (ω : ↥(Submission.Blueprint.fixedPts H P)) :
    ((m • ω : ↥(Submission.Blueprint.fixedPts H P)) : G ⧸ H) = (m : G) • (ω : G ⧸ H) :=
  rfl

/-- `P` is normal in `N_G(P)`. -/
instance instNormalSubgroupOfNormalizer (P : Subgroup G) :
    (P.subgroupOf (Subgroup.normalizer (P : Set G))).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.le_normalizer (H := P))).mpr le_rfl

/-- The action of `N_G(P)` on `Ω_P = fixedPts H P` factors through `N_G(P)/P` (elements of `P`
fix every point of `Ω_P`). -/
noncomputable def kappaQuotPermHom {H P : Subgroup G} :
    (Subgroup.normalizer (P : Set G) ⧸ P.subgroupOf (Subgroup.normalizer (P : Set G))) →*
      Equiv.Perm ↥(Submission.Blueprint.fixedPts H P) :=
  QuotientGroup.lift (P.subgroupOf (Subgroup.normalizer (P : Set G)))
    (MulAction.toPermHom (Subgroup.normalizer (P : Set G))
      ↥(Submission.Blueprint.fixedPts H P))
    (by
      intro m hm
      rw [MonoidHom.mem_ker]
      have hpt : ∀ ω : ↥(Submission.Blueprint.fixedPts H P),
          MulAction.toPermHom (Subgroup.normalizer (P : Set G))
            ↥(Submission.Blueprint.fixedPts H P) m ω = ω := by
        intro ω
        rw [MulAction.toPermHom_apply, MulAction.toPerm_apply]
        exact Subtype.ext (by
          rw [kappa_smul_val]
          exact ω.2 (m : G) (Subgroup.mem_subgroupOf.mp hm))
      exact Equiv.ext hpt)

/-- `N_G(P)/P` acts on `Ω_P = fixedPts H P`. -/
noncomputable instance kappaQuotMulAction {H P : Subgroup G} :
    MulAction (Subgroup.normalizer (P : Set G) ⧸ P.subgroupOf (Subgroup.normalizer (P : Set G)))
      ↥(Submission.Blueprint.fixedPts H P) :=
  MulAction.compHom _ (kappaQuotPermHom (H := H) (P := P))

theorem kappa_quot_smul_mk {H P : Subgroup G}
    (m : Subgroup.normalizer (P : Set G)) (ω : ↥(Submission.Blueprint.fixedPts H P)) :
    (QuotientGroup.mk' (P.subgroupOf (Subgroup.normalizer (P : Set G))) m) • ω = m • ω :=
  rfl

/-- The kernel of the action of `M = N_G(P)` on `Ω_P = fixedPts H P`, transported to a subgroup
of `G`. -/
noncomputable def kappaKernel {H P : Subgroup G} : Subgroup G :=
  (MulAction.toPermHom (Subgroup.normalizer (P : Set G))
    ↥(Submission.Blueprint.fixedPts H P)).ker.map (Subgroup.subtype (Subgroup.normalizer (P : Set G)))

theorem kappaKernel_le {H P : Subgroup G} :
    kappaKernel (H := H) (P := P) ≤ Subgroup.normalizer (P : Set G) :=
  Subgroup.map_subtype_le _

theorem mem_kappaKernel_iff {H P : Subgroup G} {x : G} :
    x ∈ kappaKernel (H := H) (P := P) ↔
      x ∈ Subgroup.normalizer (P : Set G) ∧
        ∀ ω : G ⧸ H, ω ∈ Submission.Blueprint.fixedPts H P → x • ω = ω := by
  constructor
  · intro hx
    obtain ⟨m, hm, hmx⟩ := Subgroup.mem_map.mp hx
    rw [MonoidHom.mem_ker] at hm
    refine ⟨hmx ▸ m.2, fun ω hω => ?_⟩
    have h2 : (m • (⟨ω, hω⟩ : ↥(Submission.Blueprint.fixedPts H P))) = ⟨ω, hω⟩ := by
      have h3 := congrArg
        (fun e : Equiv.Perm ↥(Submission.Blueprint.fixedPts H P) => e ⟨ω, hω⟩) hm
      rw [MulAction.toPermHom_apply, MulAction.toPerm_apply] at h3
      simpa using h3
    have h4 : (m : G) • ω = ω := by
      have := congrArg (fun z : ↥(Submission.Blueprint.fixedPts H P) => (z : G ⧸ H)) h2
      rwa [kappa_smul_val] at this
    have hmx' : (m : G) = x := hmx
    rw [hmx'] at h4
    exact h4
  · rintro ⟨hxM, hfix⟩
    refine Subgroup.mem_map.mpr ⟨⟨x, hxM⟩, ?_, rfl⟩
    rw [MonoidHom.mem_ker]
    refine Equiv.ext (fun ω => ?_)
    rw [MulAction.toPermHom_apply, MulAction.toPerm_apply]
    exact Subtype.ext (by rw [kappa_smul_val]; exact hfix (ω : G ⧸ H) ω.2)

/-- **The kernel of the action of `M = N_G(P)` on `Ω_P` is `P`** (Ch. III §5 Lemma 1 = `hL1`). -/
theorem kappaKernel_eq_P (hFT : Submission.Blueprint.FeitThompsonProp)
    {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G}
    {r : ℕ} (h : Design.Setup5 G H t W p P A r)
    (hL1 : ∀ X : Subgroup G, P ≤ X → X ≤ Submission.Blueprint.centD H t →
      H ⊓ Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (X : Set G) → X = P) :
    kappaKernel (H := H) (P := P) = P := by
  classical
  have hPleH : P ≤ H := (h.P_le.trans inf_le_right).trans (le_trans inf_le_left inf_le_left)
  have hPleHt : P ≤ Submission.Blueprint.conj t H :=
    (h.P_le.trans inf_le_right).trans (le_trans inf_le_left inf_le_right)
  have hPK : P ≤ kappaKernel (H := H) (P := P) := by
    intro x hxP
    rw [mem_kappaKernel_iff]
    refine ⟨Subgroup.le_normalizer (H := P) hxP, fun ω hω => ?_⟩
    exact hω x hxP
  -- `K ≤ twoPoint H t`
  have hKD : kappaKernel (H := H) (P := P) ≤ Submission.Blueprint.twoPoint H t := by
    intro x hx
    obtain ⟨hxM, hfix⟩ := mem_kappaKernel_iff.mp hx
    have h1α : (((1 : G)) : G ⧸ H) ∈ Submission.Blueprint.fixedPts H P := by
      rw [Work.ThreePoints.mem_fixedPts_iff_le_stabilizer]
      have : MulAction.stabilizer G (((1 : G)) : G ⧸ H) = H := by
        rw [Work.ThreePoints.stabilizer_mk, Work.ThreePoints.conj_one]
      rw [this]; exact hPleH
    have htα : (QuotientGroup.mk t : G ⧸ H) ∈ Submission.Blueprint.fixedPts H P := by
      rw [Work.ThreePoints.mem_fixedPts_iff_le_stabilizer]
      have : MulAction.stabilizer G (QuotientGroup.mk t : G ⧸ H) =
          Submission.Blueprint.conj t H := by rw [Work.ThreePoints.stabilizer_mk]
      rw [this]; exact hPleHt
    have hxH : x ∈ H := by
      have hfix' := hfix (((1 : G)) : G ⧸ H) h1α
      have : x ∈ MulAction.stabilizer G (((1 : G)) : G ⧸ H) :=
        MulAction.mem_stabilizer_iff.mpr hfix'
      rwa [show MulAction.stabilizer G (((1 : G)) : G ⧸ H) = H from by
        rw [Work.ThreePoints.stabilizer_mk, Work.ThreePoints.conj_one]] at this
    have hxHt : x ∈ Submission.Blueprint.conj t H := by
      have hfix' := hfix (QuotientGroup.mk t) htα
      have : x ∈ MulAction.stabilizer G (QuotientGroup.mk t : G ⧸ H) :=
        MulAction.mem_stabilizer_iff.mpr hfix'
      rwa [Work.ThreePoints.stabilizer_mk] at this
    exact ⟨hxH, hxHt⟩
  -- `N_G(P) ⊓ D ≤ centD H t`
  have hMDV : Subgroup.normalizer (P : Set G) ⊓ Submission.Blueprint.twoPoint H t ≤
      Submission.Blueprint.centD H t := by
    have hc := (sec4_one_c hFT h.toSetup45A).1
    intro x hx
    rw [inf_comm] at hx
    rw [hc] at hx
    exact (sup_le (le_trans inf_le_left h.A_le) (h.P_le.trans inf_le_right)) hx
  have hKV : kappaKernel (H := H) (P := P) ≤ Submission.Blueprint.centD H t :=
    (le_inf kappaKernel_le hKD).trans hMDV
  -- `N_G(P) ≤ N_G(K)`
  have hKNM : Subgroup.normalizer (P : Set G) ≤
      Subgroup.normalizer (kappaKernel (H := H) (P := P) : Set G) := by
    have hle : ∀ m ∈ Subgroup.normalizer (P : Set G), ∀ y ∈ kappaKernel (H := H) (P := P),
        m * y * m⁻¹ ∈ kappaKernel (H := H) (P := P) := by
      intro m hm y hy
      obtain ⟨hyM, hfix⟩ := mem_kappaKernel_iff.mp hy
      rw [mem_kappaKernel_iff]
      refine ⟨Subgroup.normalizer (P : Set G) |>.mul_mem
        (Subgroup.normalizer (P : Set G) |>.mul_mem hm hyM)
        (Subgroup.normalizer (P : Set G) |>.inv_mem hm), fun ω hω => ?_⟩
      have hmem : (m : G)⁻¹ • ω ∈ Submission.Blueprint.fixedPts H P :=
        Work.ThreePoints.ThmC.fixedPts_smul_mem (H := H) (P := P)
          (Subgroup.normalizer (P : Set G) |>.inv_mem hm) hω
      have hfixv : y • ((m : G)⁻¹ • ω) = (m : G)⁻¹ • ω := hfix _ hmem
      calc (m * y * m⁻¹) • ω = m • (y • (m⁻¹ • ω)) := by rw [mul_smul, mul_smul]
        _ = m • (m⁻¹ • ω) := by rw [hfixv]
        _ = ω := by rw [← mul_smul]; simp
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact hle m hm y
    · intro hy
      have h2 := hle m⁻¹ (Subgroup.normalizer (P : Set G) |>.inv_mem hm)
        (m * y * m⁻¹) hy
      have h3 : m⁻¹ * (m * y * m⁻¹) * (m⁻¹)⁻¹ = y := by group
      rwa [h3] at h2
  have hKN : H ⊓ Subgroup.normalizer (P : Set G) ≤
      Subgroup.normalizer (kappaKernel (H := H) (P := P) : Set G) :=
    fun n hn => hKNM hn.2
  exact hL1 _ hPK hKV hKN

/-- A `p`-Sylow subgroup of `E` is a `p`-Sylow subgroup of any intermediate subgroup. -/
theorem isSylowOf_of_isSylowIn {p : ℕ} (hp : p.Prime) {P D E : Subgroup G}
    (h : IsSylowIn p P E) (hPD : P ≤ D) (hDE : D ≤ E) :
    Work.ThreePoints.ThmC.IsSylowOf p P D := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine ⟨hPD, h.1, fun Q hPQ hQD hQp => ?_⟩
  have hQE : Q ≤ E := hQD.trans hDE
  have hsid : ¬ p ∣ (P.subgroupOf Q).index := by
    intro hdvd
    apply h.2.2
    have h1 : P.relIndex Q * Q.relIndex E = P.relIndex E :=
      Subgroup.relIndex_mul_relIndex P Q E hPQ hQE
    have h2 : (P.subgroupOf Q).index = P.relIndex Q := rfl
    have h3 : (P.subgroupOf E).index = P.relIndex E := rfl
    rw [h3, ← h1, ← h2]
    exact dvd_mul_of_dvd_left hdvd _
  have hdvdQ : (P.subgroupOf Q).index ∣ Nat.card ↥Q := by
    have h5 := Subgroup.card_mul_index (P.subgroupOf Q)
    rw [← h5]
    exact dvd_mul_left _ _
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQp
  have hcop : Nat.Coprime (P.subgroupOf Q).index (p ^ k) :=
    ((Nat.Prime.coprime_iff_not_dvd hp).mpr hsid).symm.pow_right k
  have hidx1 : (P.subgroupOf Q).index = 1 := hcop.eq_one_of_dvd (hk ▸ hdvdQ)
  have hcard : Nat.card ↥(P.subgroupOf Q) = Nat.card ↥(⊤ : Subgroup ↥Q) := by
    rw [Subgroup.card_top]
    have h5 := Subgroup.card_mul_index (P.subgroupOf Q)
    rw [hidx1, mul_one] at h5
    exact h5
  have htop : P.subgroupOf Q = ⊤ := Subgroup.eq_of_le_of_card_ge le_top (le_of_eq hcard.symm)
  exact (le_antisymm hPQ (Subgroup.subgroupOf_eq_top.mp htop)).symm

/-- **§5 Prop. 2 (c), step 1** (Ch. II §2 Lemma 1 with `g = t`): `M = N_G(P)` acts
`2`-transitively on `Ω_P = fixedPts H P` and `M ⊓ H` is strongly embedded in `M`. -/
theorem kappa_M_data (hA : Submission.Blueprint.ThmAProp)
    (hFT : Submission.Blueprint.FeitThompsonProp)
    {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}
    (h : Design.Setup5 G H t W p P A r) (u : G)
    (hu : u ∈ H ∧ orderOf u = 2 ∧
      u ∈ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G)) :
    Work.DoubleTransitivity.IsTwoTransitiveOnSub (Subgroup.normalizer (P : Set G))
        (Submission.Blueprint.fixedPts H P) ∧
      IsStronglyEmbedded ((Subgroup.normalizer (P : Set G) ⊓ H).subgroupOf
        (Subgroup.normalizer (P : Set G))) := by
  have h2t : Submission.Blueprint.IsTwoTransitiveOn H := hA G h.sit.1.1 H h.se
  have hBrSz : Submission.Blueprint.BrauerSuzukiProp := Work.BrauerSuzuki.brauerSuzuki
  have hPleH : P ≤ H := (h.P_le.trans inf_le_right).trans (le_trans inf_le_left inf_le_left)
  have hPleT : P ≤ Submission.Blueprint.twoPoint H t :=
    (h.P_le.trans inf_le_right).trans inf_le_left
  have hcommP : ∀ x ∈ P, u * x * u⁻¹ = x := by
    intro x hx
    have hc : x * u = u * x := (Subgroup.mem_centralizer_iff.mp hu.2.2) x (h.P_le hx).2
    rw [← hc]; group
  have hu2 : u * u = 1 := by
    have h' := pow_orderOf_eq_one u; rw [hu.2.1] at h'; simpa [pow_two] using h'
  have huP : u ∈ Subgroup.normalizer (P : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx; rw [hcommP x hx]; exact hx
    · intro hx
      have h2 : u * (u * x * u⁻¹) * u⁻¹ = u * x * u⁻¹ := hcommP _ hx
      have h3 : u * (u * x * u⁻¹) * u⁻¹ = x := by
        have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
        rw [hui, show u * (u * x * u) * u = (u * u) * x * (u * u) from by group, hu2]
        simp
      rw [h3] at h2
      rw [h2.symm] at hx
      exact hx
  have huInv : u ∈ Submission.Blueprint.involutions (H : Set G) := ⟨hu.1, hu.2.1⟩
  have hpodd : p ≠ 2 := by
    intro hp2
    have hdvd : p ∣ Nat.card ↥(Submission.Blueprint.twoPoint H t) := by
      rw [← h.P_card]
      exact Subgroup.card_dvd_of_le hPleT
    rw [hp2] at hdvd
    exact Nat.not_even_iff_odd.mpr (h.se.2.2 t h.notMem) (even_iff_two_dvd.mpr hdvd)
  -- `P` is a Sylow `p`-subgroup of `D ⊓ D^u`
  have hPleDu : P ≤ Submission.Blueprint.conj u (Submission.Blueprint.twoPoint H t) := by
    intro x hx
    refine Subgroup.mem_map.mpr ⟨x, hPleT hx, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact hcommP x hx
  have hP1 : Work.ThreePoints.ThmC.IsSylowOf p P
      (Submission.Blueprint.twoPoint H t ⊓ Submission.Blueprint.conj u
        (Submission.Blueprint.twoPoint H t)) :=
    isSylowOf_of_isSylowIn h.prime h.P_syl (le_inf hPleT hPleDu) inf_le_left
  have hres := Work.ThreePoints.ThmC.ch2_sec2_lem1 h.se h2t hBrSz hFT h.notMem huInv h.prime
    hpodd hP1 huP
  refine ⟨hres.2.1.1, ?_⟩
  have h1 := hres.2.1.2 1 (by rw [Work.ThreePoints.conj_one]; exact hPleH)
  rwa [Work.ThreePoints.conj_one] at h1

/-- `M/P` acts `2`-transitively on `Ω_P = fixedPts H P`. -/
theorem kappa_quot_twoTransitive {H P : Subgroup G}
    (h2 : Work.DoubleTransitivity.IsTwoTransitiveOnSub (Subgroup.normalizer (P : Set G))
        (Submission.Blueprint.fixedPts H P)) :
    MulAction.IsMultiplyPretransitive
      (Subgroup.normalizer (P : Set G) ⧸ P.subgroupOf (Subgroup.normalizer (P : Set G)))
      ↥(Submission.Blueprint.fixedPts H P) 2 := by
  rw [MulAction.is_two_pretransitive_iff]
  intro a b c d hab hcd
  obtain ⟨y, hy, hyac, hybd⟩ :=
    h2 a.1 a.2 b.1 b.2 (fun h => hab (Subtype.ext h)) c.1 c.2 d.1 d.2
      (fun h => hcd (Subtype.ext h))
  exact ⟨QuotientGroup.mk' (P.subgroupOf (Subgroup.normalizer (P : Set G))) ⟨y, hy⟩,
    Subtype.ext (by rw [kappa_quot_smul_mk, kappa_smul_val]; exact hyac),
    Subtype.ext (by rw [kappa_quot_smul_mk, kappa_smul_val]; exact hybd)⟩

/-- A point stabiliser of the `2`-transitive action of `M/P` on `Ω_P` is maximal. -/
theorem kappa_coatom {H P : Subgroup G}
    (h2 : Work.DoubleTransitivity.IsTwoTransitiveOnSub (Subgroup.normalizer (P : Set G))
        (Submission.Blueprint.fixedPts H P))
    (h3 : 3 ≤ (Submission.Blueprint.fixedPts H P).ncard)
    (a : ↥(Submission.Blueprint.fixedPts H P)) :
    IsCoatom (MulAction.stabilizer
      (Subgroup.normalizer (P : Set G) ⧸ P.subgroupOf (Subgroup.normalizer (P : Set G))) a) := by
  haveI : MulAction.IsMultiplyPretransitive
      (Subgroup.normalizer (P : Set G) ⧸ P.subgroupOf (Subgroup.normalizer (P : Set G)))
      ↥(Submission.Blueprint.fixedPts H P) 2 := kappa_quot_twoTransitive h2
  haveI : Nontrivial ↥(Submission.Blueprint.fixedPts H P) := by
    obtain ⟨x, hx⟩ := Set.nonempty_of_ncard_ne_zero (by omega :
      (Submission.Blueprint.fixedPts H P).ncard ≠ 0)
    obtain ⟨y, hy, hne⟩ := Set.exists_ne_of_one_lt_ncard (s := Submission.Blueprint.fixedPts H P)
      (by omega : 1 < (Submission.Blueprint.fixedPts H P).ncard) x
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩, fun h => hne (congrArg Subtype.val h).symm⟩
  haveI : MulAction.IsPreprimitive
      (Subgroup.normalizer (P : Set G) ⧸ P.subgroupOf (Subgroup.normalizer (P : Set G)))
      ↥(Submission.Blueprint.fixedPts H P) :=
    MulAction.isPreprimitive_of_is_two_pretransitive
      (h2 := kappa_quot_twoTransitive h2)
  exact MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive
    (Subgroup.normalizer (P : Set G) ⧸ P.subgroupOf (Subgroup.normalizer (P : Set G))) a

/-- The point stabiliser of the point `H` in `M/P` is the image of `M ⊓ H = N_H(P)`. -/
theorem kappa_stabilizer_eq {H P : Subgroup G}
    (hpt : (QuotientGroup.mk (1 : G) : G ⧸ H) ∈ Submission.Blueprint.fixedPts H P) :
    MulAction.stabilizer (Subgroup.normalizer (P : Set G) ⧸
        P.subgroupOf (Subgroup.normalizer (P : Set G)))
      (⟨(QuotientGroup.mk (1 : G) : G ⧸ H), hpt⟩ : ↥(Submission.Blueprint.fixedPts H P)) =
    ((Subgroup.normalizer (P : Set G) ⊓ H).subgroupOf (Subgroup.normalizer (P : Set G))).map
      (QuotientGroup.mk' (P.subgroupOf (Subgroup.normalizer (P : Set G)))) := by
  ext x
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro hx
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective
      (P.subgroupOf (Subgroup.normalizer (P : Set G))) x
    have h2 : (m : G) • (QuotientGroup.mk (1 : G) : G ⧸ H) =
        (QuotientGroup.mk (1 : G) : G ⧸ H) := by
      have := congrArg (fun z : ↥(Submission.Blueprint.fixedPts H P) => (z : G ⧸ H)) hx
      rwa [kappa_quot_smul_mk, kappa_smul_val] at this
    have hmH : (m : G) ∈ H := by
      rw [Work.DoubleTransitivity.smul_mk, mul_one] at h2
      exact Work.DoubleTransitivity.mk_one_eq_iff.mp h2
    exact Subgroup.mem_map.mpr
      ⟨m, Subgroup.mem_subgroupOf.mpr ⟨m.2, hmH⟩, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    rw [kappa_quot_smul_mk]
    apply Subtype.ext
    rw [kappa_smul_val]
    have hyH : (y : G) ∈ H := (Subgroup.mem_subgroupOf.mp hy).2
    rw [Work.DoubleTransitivity.smul_mk, mul_one]
    exact Work.DoubleTransitivity.mk_one_eq_iff.mpr hyH

/-- The point stabiliser is strongly embedded in `M/P`. -/
theorem kappa_quot_stronglyEmbedded {H P : Subgroup G}
    (hse : IsStronglyEmbedded ((Subgroup.normalizer (P : Set G) ⊓ H).subgroupOf
      (Subgroup.normalizer (P : Set G))))
    (hPMH : P ≤ Subgroup.normalizer (P : Set G) ⊓ H)
    (hodd : Odd (Nat.card (P.subgroupOf (Subgroup.normalizer (P : Set G)))))
    (hpt : (QuotientGroup.mk (1 : G) : G ⧸ H) ∈ Submission.Blueprint.fixedPts H P) :
    IsStronglyEmbedded (MulAction.stabilizer (Subgroup.normalizer (P : Set G) ⧸
        P.subgroupOf (Subgroup.normalizer (P : Set G)))
      (⟨(QuotientGroup.mk (1 : G) : G ⧸ H), hpt⟩ : ↥(Submission.Blueprint.fixedPts H P))) := by
  rw [kappa_stabilizer_eq hpt]
  exact Work.NormalComplement.isStronglyEmbedded_map_of_surjective
    (QuotientGroup.mk' (P.subgroupOf (Subgroup.normalizer (P : Set G))))
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) hodd
    (Subgroup.subgroupOf_mono (Subgroup.normalizer (P : Set G)) hPMH) hse

/-- `N_G(P)` has 2-rank `1` (its point stabiliser `N_H(P)` has a unique involution `u`, and `u`
has a unique fixed point in `Ω_P`). -/
theorem kappa_noFour_M {H P : Subgroup G} (hse : IsStronglyEmbedded H) (u : G)
    (huH : u ∈ H) (hu2 : orderOf u = 2) (huM : u ∈ Subgroup.normalizer (P : Set G))
    (hPH : P ≤ H)
    (huniq : ∀ w ∈ H ⊓ Subgroup.normalizer (P : Set G), orderOf w = 2 → w = u)
    (h2 : Work.DoubleTransitivity.IsTwoTransitiveOnSub (Subgroup.normalizer (P : Set G))
        (Submission.Blueprint.fixedPts H P))
    (hseL : IsStronglyEmbedded ((Subgroup.normalizer (P : Set G) ⊓ H).subgroupOf
        (Subgroup.normalizer (P : Set G)))) :
    ¬ HasFourGroup ↥(Subgroup.normalizer (P : Set G)) := by
  set M : Subgroup G := Subgroup.normalizer (P : Set G) with hM
  set S : Set (G ⧸ H) := Submission.Blueprint.fixedPts H P with hS
  have hpt : (QuotientGroup.mk (1 : G) : G ⧸ H) ∈ S := by
    rw [hS, Work.ThreePoints.mem_fixedPts_iff_le_stabilizer]
    rw [show MulAction.stabilizer G (QuotientGroup.mk (1 : G) : G ⧸ H) = H from by
      rw [Work.ThreePoints.stabilizer_mk, Work.ThreePoints.conj_one]]
    exact hPH
  let a0 : ↥S := ⟨(QuotientGroup.mk (1 : G) : G ⧸ H), hpt⟩
  have huL : (⟨u, huM⟩ : ↥M) ∈ (M ⊓ H).subgroupOf M :=
    Subgroup.mem_subgroupOf.mpr ⟨huM, huH⟩
  have huL2 : orderOf (⟨u, huM⟩ : ↥M) = 2 := by
    rw [← Subgroup.orderOf_coe]; exact hu2
  have huniqL : ∀ w : ↥M, w ∈ (M ⊓ H).subgroupOf M → orderOf w = 2 → w = ⟨u, huM⟩ := by
    intro w hw hw2
    refine Subtype.ext ?_
    have hwG : (w : G) ∈ H ⊓ M :=
      ⟨(Subgroup.mem_subgroupOf.mp hw).2, (Subgroup.mem_subgroupOf.mp hw).1⟩
    exact huniq (w : G) hwG ((Subgroup.orderOf_coe w).trans hw2)
  have hstab : MulAction.stabilizer (↥M) a0 = (M ⊓ H).subgroupOf M := by
    ext y
    rw [MulAction.mem_stabilizer_iff]
    constructor
    · intro hy
      refine Subgroup.mem_subgroupOf.mpr ⟨y.2, ?_⟩
      have h2' : (y : G) • (QuotientGroup.mk (1 : G) : G ⧸ H) =
          (QuotientGroup.mk (1 : G) : G ⧸ H) := by
        have h3 := congrArg (fun z : ↥S => (z : G ⧸ H)) hy
        rwa [kappa_smul_val] at h3
      rw [Work.DoubleTransitivity.smul_mk, mul_one] at h2'
      exact Work.DoubleTransitivity.mk_one_eq_iff.mp h2'
    · intro hy
      rw [Subgroup.mem_subgroupOf] at hy
      apply Subtype.ext
      rw [kappa_smul_val]
      rw [Work.DoubleTransitivity.smul_mk, mul_one]
      exact Work.DoubleTransitivity.mk_one_eq_iff.mpr hy.2
  have hufix : ∀ ω : ↥S, (⟨u, huM⟩ : ↥M) • ω = ω → ω = a0 := by
    intro ω hω
    obtain ⟨ω₀, -, huniq0⟩ := Work.ThreePoints.existsUnique_fixedPts_of_orderOf_eq_two hse hu2
    have hmk : u • (QuotientGroup.mk (1 : G) : G ⧸ H) =
        (QuotientGroup.mk (1 : G) : G ⧸ H) := by
      rw [Work.DoubleTransitivity.smul_mk, mul_one]
      exact Work.DoubleTransitivity.mk_one_eq_iff.mpr huH
    have hωval : u • (ω : G ⧸ H) = (ω : G ⧸ H) := by
      have h3 := congrArg (fun z : ↥S => (z : G ⧸ H)) hω
      rwa [kappa_smul_val] at h3
    exact Subtype.ext ((huniq0 _ hωval).trans (huniq0 _ hmk).symm)
  have key : ∀ x : ↥M, orderOf x = 2 → ∃! ω : ↥S, x • ω = ω := by
    intro x hx2
    obtain ⟨c, hc⟩ := Work.ThreePoints.involutions_conj_of_stronglyEmbedded hseL hx2 huL2
    set g : ↥M := (↑c : ↥M) with hgc
    have hg : g * x = ⟨u, huM⟩ * g := hc
    have hx : x = g⁻¹ * ⟨u, huM⟩ * g := by
      calc x = g⁻¹ * (g * x) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
        _ = g⁻¹ * (⟨u, huM⟩ * g) := by rw [hg]
        _ = g⁻¹ * ⟨u, huM⟩ * g := by rw [mul_assoc]
    have hu'fix : (⟨u, huM⟩ : ↥M) • a0 = a0 :=
      MulAction.mem_stabilizer_iff.mp (hstab ▸ huL)
    refine ⟨g⁻¹ • a0, ?_, fun ω hω => ?_⟩
    · rw [hx]
      simp only [mul_smul, smul_inv_smul, inv_smul_smul, hu'fix]
    · have h4 : g⁻¹ • ((⟨u, huM⟩ : ↥M) • (g • ω)) = g⁻¹ • (g • ω) := by
        have h2' : (g⁻¹ * ⟨u, huM⟩ * g) • ω = ω := by rw [← hx]; exact hω
        have h7 : g⁻¹ • ((⟨u, huM⟩ : ↥M) • (g • ω)) = ω := by
          calc g⁻¹ • ((⟨u, huM⟩ : ↥M) • (g • ω))
              = (g⁻¹ * ⟨u, huM⟩) • (g • ω) :=
                (mul_smul g⁻¹ (⟨u, huM⟩ : ↥M) (g • ω)).symm
            _ = (g⁻¹ * ⟨u, huM⟩ * g) • ω :=
                (mul_smul (g⁻¹ * ⟨u, huM⟩) g ω).symm
            _ = ω := h2'
        rw [h7]; exact (inv_smul_smul g ω).symm
      have h3 : (⟨u, huM⟩ : ↥M) • (g • ω) = g • ω := by
        have h5 := congrArg (fun z => g • z) h4
        simpa only [smul_inv_smul] using h5
      have h6 := hufix (g • ω) h3
      calc ω = g⁻¹ • (g • ω) := (inv_smul_smul g ω).symm
        _ = g⁻¹ • a0 := by rw [h6]
  intro h4
  obtain ⟨a, b, ha2, hb2, hab, hcomm⟩ := h4
  obtain ⟨ωa, hωa, huniqa⟩ := key a ha2
  have hbω : b • ωa = ωa := by
    have h1 : a • (b • ωa) = b • ωa := by
      rw [← mul_smul, hcomm, mul_smul, hωa]
    exact huniqa (b • ωa) h1
  obtain ⟨g, hgmem, hga⟩ := h2.isTransitiveOnSub (QuotientGroup.mk (1 : G) : G ⧸ H) hpt
    (ωa : G ⧸ H) ωa.2
  let gg : ↥M := ⟨g, hgmem⟩
  have hgga : gg • a0 = ωa := Subtype.ext (by rw [kappa_smul_val]; exact hga)
  have hconjfix : ∀ y : ↥M, y • ωa = ωa → gg⁻¹ * y * gg ∈ (M ⊓ H).subgroupOf M := by
    intro y hy
    rw [← hstab, MulAction.mem_stabilizer_iff]
    calc (gg⁻¹ * y * gg) • a0 = gg⁻¹ • (y • (gg • a0)) := by rw [mul_smul, mul_smul]
      _ = gg⁻¹ • (y • ωa) := by rw [hgga]
      _ = gg⁻¹ • ωa := by rw [hy]
      _ = gg⁻¹ • (gg • a0) := by rw [hgga]
      _ = a0 := by rw [inv_smul_smul]
  have hconj2 : ∀ y : ↥M, orderOf y = 2 →
      orderOf (gg⁻¹ * y * gg) = 2 := by
    intro y hy
    have hsem : SemiconjBy gg (gg⁻¹ * y * gg) y := by
      show gg * (gg⁻¹ * y * gg) = y * gg
      group
    exact (SemiconjBy.orderOf_eq gg hsem).trans hy
  have haeq : gg⁻¹ * a * gg = ⟨u, huM⟩ :=
    huniqL _ (hconjfix a hωa) (hconj2 a ha2)
  have hbeq : gg⁻¹ * b * gg = ⟨u, huM⟩ :=
    huniqL _ (hconjfix b hbω) (hconj2 b hb2)
  have h2' : gg⁻¹ * a * gg = gg⁻¹ * b * gg := haeq.trans hbeq.symm
  have : a = b := mul_left_cancel (mul_right_cancel h2')
  exact hab this



/-- **§5 Prop. 2 (c): the subgroup `κ`.**  In the §5 configuration there is a subgroup
`κ ≤ G` with `κ ⊆ Mset u t = {x ∈ C_G(u*t) | t x t⁻¹ = x⁻¹}`, containing `u * t`, and normalised
by `N_H(P) = H ⊓ N_G(P)`.  For the source this is `J(Q,u) = O_f(Q)` where `Q ⊴ N_G(P)` is the
normal subgroup produced by Appendix III applied to `N_G(P)/P` acting on `Ω_P = fixedPts H P`.

Suggested route (this is the whole mathematical content of §5 Prop. 2 (c)):

* `hA` applied to `G` (`h.sit.1.1 : HasFourGroup G`) gives `IsTwoTransitiveOn H`, and
  `Work.ThreePoints.ThmC.ch2_sec2_lem1` (Ch. II §2 Lemma 1) applied with `g := t`, `u`, `p`,
  `P` gives: `M := N_G(P)` acts 2-transitively on `Ω_P` and `M ⊓ H` is strongly embedded in `M`.
* The kernel of the action of `M` on `Ω_P` is `P`: an element `k` of the kernel fixes every point
  of `Ω_P`, so `⟨P, k⟩ ≤ M ⊓ H` fixes `Ω_P` pointwise; as `Ω_P ∋ H, t·H` this gives
  `⟨P, k⟩ ≤ D ⊓ M = N_D(P) ≤ centD H t` (`sec4_one_c`, with `h.toSetup45A`), and then `hL1`
  (with `X = ⟨P,k⟩`) forces `⟨P, k⟩ = P`.  Hence `M/P` acts faithfully on `Ω_P`.
* `M/P` has 2-rank 1: `N_H(P)/P` is strongly embedded in `M/P` with a unique involution (from
  `huniq`), and `[M : N_H(P)]` is odd, so a Sylow 2 of `M/P` has a unique involution, hence is
  cyclic or generalised quaternion (`Work.BrauerSuzuki.Group.isCyclicOrGenQuaternion_of_uniqueInvolution`).
* Apply `hIII` (`AppIIIProp`) to `F := ↥M ⧸ P.subgroupOf M`, `α := ↥(fixedPts H P)`,
  `a := ⟨H, ·⟩`: get `f` and `Q̄ ≤ F` (abelian of exponent `f`, normal, disjoint from the point
  stabiliser, and `ū * t̄ ∈ Q̄` with `orderOf (ū * t̄) = f`, where `ū`, `t̄` are the images of
  `u`, `t`).
* `Q := Q̄.comap (mk' P.subgroupOf M)` (transported to `G` by `M.subtype`) satisfies `P ≤ Q ⊴ M`,
  `Q/P ≅ Q̄`, and `Q` is an extension of the `p`-group `P` by an abelian `f`-group.  Moreover
  `f ≠ p`: `P` is a Sylow `p`-subgroup of `M` (the points fixed by any `p`-subgroup `R ≥ P` of
  `M` contain `Ω_P`, so `R` is a `p`-subgroup with `≥ 3` fixed points, so `R = P`), so
  `p ∤ |F| = |Q̄| * |N_H(P)/P|` while `|Q̄|` is an `f`-power.
* `appI_five_b` with `d = 2`, `t := u`, `X := Q` (`Q` is `u`-normalised and solvable, `|Q|` odd,
  and `|Kapp u Q| = |Q : C_Q(u)| = |Q : P|` is a power of `f ≠ p`, while `C_Q(u) = P` so
  `F(C_Q(u)) = P` has order `p`) gives that `κ := Kapp u Q = {q ∈ Q | u q u⁻¹ = q⁻¹}` is the
  underlying set of a subgroup `κ ≤ Q`, with `Q = P ⋊ κ` and `Q/P ≅ κ` abelian; hence `κ` is
  abelian and `[κ, P] ≤ κ ⊓ P = ⊥`.
* `u * t ∈ Q` (its image `ū * t̄` lies in `Q̄`) and `u * t` is inverted by `u`; since
  `{q ∈ Q : u q u⁻¹ = q⁻¹}` has `|Q : C_Q(u)| = |Q/P| = |Kapp u Q|` elements, `u * t ∈ κ`.
* `κ ⊆ Mset u t`: elements of `Kapp u Q` are inverted by `u`, and they commute with `u * t`
  because `κ` is abelian and centralises `P` while `u * t ∈ Q = P ⋊ κ`.  For `x ∈ C_G(u*t)`,
  inversion by `u` is inversion by `t`: `t = u·(u*t)`, `u = (u*t)·t`, `(u*t)² = 1`.
* `κ` is normalised by `N_H(P)`: `Q ⊴ M` and every `n ∈ N_H(P)` centralises `u` (`huniq`), so
  `n κ n⁻¹ = Kapp (n u n⁻¹) (n Q n⁻¹) = Kapp u Q = κ`.

The hypotheses `hFT`, `hC`, `hMF2`, `hCor1` are unused but keep the interface uniform. -/
theorem orderOf_conj3 (a b : G) : orderOf (a * b * a⁻¹) = orderOf b := by
  have hsem : SemiconjBy a⁻¹ (a * b * a⁻¹) b := by
    show a⁻¹ * (a * b * a⁻¹) = b * a⁻¹
    group
  exact SemiconjBy.orderOf_eq a⁻¹ hsem

theorem kappa_u_fix {H P : Subgroup G} (hse : IsStronglyEmbedded H) (u : G)
    (huH : u ∈ H) (hu2 : orderOf u = 2) (huM : u ∈ Subgroup.normalizer (P : Set G)) :
    ∀ ω : ↥(Submission.Blueprint.fixedPts H P),
      (⟨u, huM⟩ : ↥(Subgroup.normalizer (P : Set G))) • ω = ω →
        (ω : G ⧸ H) = (QuotientGroup.mk (1 : G) : G ⧸ H) := by
  intro ω hω
  obtain ⟨ω₀, -, huniq0⟩ := Work.ThreePoints.existsUnique_fixedPts_of_orderOf_eq_two hse hu2
  have hmk : u • (QuotientGroup.mk (1 : G) : G ⧸ H) = (QuotientGroup.mk (1 : G) : G ⧸ H) := by
    rw [Work.DoubleTransitivity.smul_mk, mul_one]
    exact Work.DoubleTransitivity.mk_one_eq_iff.mpr huH
  have hωval : u • (ω : G ⧸ H) = (ω : G ⧸ H) := by
    have h3 := congrArg (fun z : ↥(Submission.Blueprint.fixedPts H P) => (z : G ⧸ H)) hω
    rwa [kappa_smul_val] at h3
  exact (huniq0 _ hωval).trans (huniq0 _ hmk).symm

theorem sec5c_kappa (hFT : Submission.Blueprint.FeitThompsonProp)
    (hA : Submission.Blueprint.ThmAProp) (hC : Submission.Blueprint.ThmCProp)
    (hC4 : Submission.Blueprint.ChIIFourProp)
    (hP3 : Submission.Blueprint.ChIIFourP3SubnormalProp)
    (hIII : Work.NormalComplement.AppIIIProp)
    (hMF2 : Submission.Blueprint.BenderModelFacts2Prop)
    (hCor1 : Work.NormalComplement.Design.ChISixCor1Prop) {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}
    (h : Work.NormalComplement.Design.Setup5 G H t W p P A r) (u : G)
    (hu : u ∈ H ∧ orderOf u = 2 ∧
      u ∈ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G))
    (hL1 : ∀ X : Subgroup G, P ≤ X → X ≤ Submission.Blueprint.centD H t →
      H ⊓ Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (X : Set G) → X = P)
    (huniq : ∀ w ∈ H ⊓ Subgroup.normalizer (P : Set G), orderOf w = 2 → w = u) :
    ∃ κ : Subgroup G, (κ : Set G) ⊆ Work.NormalComplement.Design.Mset u t ∧ u * t ∈ κ ∧
      H ⊓ Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (κ : Set G) := by
  set M : Subgroup G := Subgroup.normalizer (P : Set G) with hM
  set S : Set (G ⧸ H) := Submission.Blueprint.fixedPts H P with hS
  have hPleH : P ≤ H := (h.P_le.trans inf_le_right).trans (le_trans inf_le_left inf_le_left)
  have hPleT : P ≤ Submission.Blueprint.twoPoint H t :=
    (h.P_le.trans inf_le_right).trans inf_le_left
  have hPMH : P ≤ M ⊓ H := le_inf (Subgroup.le_normalizer (H := P)) hPleH
  have hpt : (QuotientGroup.mk (1 : G) : G ⧸ H) ∈ S := by
    rw [hS, Work.ThreePoints.mem_fixedPts_iff_le_stabilizer]
    rw [show MulAction.stabilizer G (QuotientGroup.mk (1 : G) : G ⧸ H) = H from by
      rw [Work.ThreePoints.stabilizer_mk, Work.ThreePoints.conj_one]]
    exact hPleH
  let a0 : ↥S := ⟨(QuotientGroup.mk (1 : G) : G ⧸ H), hpt⟩
  have hpodd : p ≠ 2 := by
    intro hp2
    have hdvd : p ∣ Nat.card ↥(Submission.Blueprint.twoPoint H t) := by
      rw [← h.P_card]; exact Subgroup.card_dvd_of_le hPleT
    rw [hp2] at hdvd
    exact Nat.not_even_iff_odd.mpr (h.se.2.2 t h.notMem) (even_iff_two_dvd.mpr hdvd)
  have huM : u ∈ M := by
    have hcomm : ∀ x ∈ P, u * x * u⁻¹ = x := by
      intro x hx
      have hc : x * u = u * x := (Subgroup.mem_centralizer_iff.mp hu.2.2) x (h.P_le hx).2
      rw [← hc]; group
    rw [hM, Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx; rw [hcomm x hx]; exact hx
    · intro hx
      have hu2 : u * u = 1 := by
        have h' := pow_orderOf_eq_one u; rw [hu.2.1] at h'; simpa [pow_two] using h'
      have h2 : u * (u * x * u⁻¹) * u⁻¹ = u * x * u⁻¹ := hcomm _ hx
      have h3 : u * (u * x * u⁻¹) * u⁻¹ = x := by
        have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_left hu2
        rw [hui, show u * (u * x * u) * u = (u * u) * x * (u * u) from by group, hu2]
        simp
      rw [h3] at h2; rw [h2.symm] at hx; exact hx
  have htM : t ∈ M := by
    rw [hM, Subgroup.mem_normalizer_iff]
    intro x
    have ht2 : t * t = 1 := by
      have h' := pow_orderOf_eq_one t; rw [h.invol] at h'; simpa [pow_two] using h'
    have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
    have hconj : ∀ y ∈ P, t * y * t⁻¹ = y := fun y hy => by
      have hct : y * t = t * y :=
        Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (h.P_le hy).2).2
      rw [← hct]; group
    constructor
    · intro hx; rw [hconj x hx]; exact hx
    · intro hx
      have h5 : t * (t * x * t⁻¹) * t⁻¹ = x := by
        rw [hti, show t * (t * x * t) * t = (t * t) * x * (t * t) from by group, ht2]
        simp
      have h6 : t * (t * x * t⁻¹) * t⁻¹ = t * x * t⁻¹ := hconj _ hx
      rw [h5] at h6
      rwa [← h6] at hx
  -- Ch. II §2 Lemma 1 with `g = t`
  have hMdata := kappa_M_data hA hFT h u hu
  have h2t : Work.DoubleTransitivity.IsTwoTransitiveOnSub M S := hMdata.1
  have hseL : IsStronglyEmbedded ((M ⊓ H).subgroupOf M) := hMdata.2
  have h3 : 3 ≤ S.ncard := by
    rw [hS]
    exact Work.ThreePoints.P3NeBot.three_le_ncard_fixedPts_of_le_centD h.se h.invol h.notMem
      (h.P_le.trans inf_le_right)
  have hodd : Odd (Nat.card (P.subgroupOf M)) := by
    have h1 : Nat.card ↥(P.subgroupOf M) = Nat.card ↥P :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer (H := P))).toEquiv
    rw [h1, h.P_card]
    exact h.prime.odd_of_ne_two hpodd
  -- the appIII inputs
  have hse_stab : IsStronglyEmbedded (MulAction.stabilizer (M ⧸ P.subgroupOf M) a0) :=
    kappa_quot_stronglyEmbedded hseL hPMH hodd hpt
  have hcoat : IsCoatom (MulAction.stabilizer (M ⧸ P.subgroupOf M) a0) :=
    kappa_coatom h2t h3 a0
  have hfaith : ∀ g : M ⧸ P.subgroupOf M, (∀ x : ↥S, g • x = x) → g = 1 := by
    intro g hg
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (P.subgroupOf M) g
    have hmK : (m : G) ∈ kappaKernel (H := H) (P := P) := by
      rw [mem_kappaKernel_iff]
      refine ⟨m.2, fun ω hω => ?_⟩
      have h1 := congrArg (fun z : ↥S => (z : G ⧸ H)) (hg ⟨ω, hω⟩)
      rwa [kappa_quot_smul_mk, kappa_smul_val] at h1
    have hmP : (m : G) ∈ P := by
      rw [kappaKernel_eq_P hFT h hL1] at hmK; exact hmK
    rw [QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff m).mpr (Subgroup.mem_subgroupOf.mpr hmP)
  have hpre : MulAction.IsPretransitive (M ⧸ P.subgroupOf M) ↥S :=
    ⟨fun c d => by
      obtain ⟨y, hy, hyd⟩ := h2t.isTransitiveOnSub c.1 c.2 d.1 d.2
      exact ⟨QuotientGroup.mk' (P.subgroupOf M) ⟨y, hy⟩,
        Subtype.ext (by rw [kappa_quot_smul_mk, kappa_smul_val]; exact hyd)⟩⟩
  have hfour : ¬ HasFourGroup (M ⧸ P.subgroupOf M) :=
    Work.ThreePoints.P3NeBot.not_hasFourGroup_quotient (P.subgroupOf M) hodd
      (kappa_noFour_M h.se u hu.1 hu.2.1 huM hPleH huniq h2t hseL)
  -- Appendix III
  obtain ⟨f, Qbar, hfprime, hQbarN, hQbar_ne, hQbar_ab, hQbar_exp, hQbar_inf, hQbar_sup,
    huuniq, hinv_mul, hinv_odd, hlast⟩ :=
    hIII (M ⧸ P.subgroupOf M) ↥S a0 hpre hfaith hfour hse_stab hcoat
  -- ## the images of `u` and `t` in `M/P`, and the element `u * t`
  have huM2 : orderOf (⟨u, huM⟩ : ↥M) = 2 := by
    rw [← Subgroup.orderOf_coe]; exact hu.2.1
  have htM2 : orderOf (⟨t, htM⟩ : ↥M) = 2 := by
    rw [← Subgroup.orderOf_coe]; exact h.invol
  have hneUt : QuotientGroup.mk' (P.subgroupOf M) ⟨u, huM⟩ ≠
      QuotientGroup.mk' (P.subgroupOf M) ⟨t, htM⟩ := by
    intro h1
    have h2 : QuotientGroup.mk' (P.subgroupOf M) (⟨u, huM⟩ * ⟨t, htM⟩⁻¹) = 1 := by
      rw [map_mul, map_inv, h1, mul_inv_cancel]
    rw [QuotientGroup.mk'_apply] at h2
    have h3 : (u : G) * t⁻¹ ∈ P :=
      Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff (⟨u, huM⟩ * ⟨t, htM⟩⁻¹)).mp h2)
    have h4 : u * t⁻¹ ∈ H := hPleH h3
    have h5 : t ∈ H := by
      have ht : t = (u * t⁻¹)⁻¹ * u := by group
      rw [ht]; exact H.mul_mem (H.inv_mem h4) hu.1
    exact h.notMem h5
  have huhat2 : orderOf (QuotientGroup.mk' (P.subgroupOf M) ⟨u, huM⟩) = 2 := by
    apply orderOf_eq_prime
    · rw [← map_pow, show (⟨u, huM⟩ : ↥M) ^ 2 = 1 from by
        rw [← huM2]; exact pow_orderOf_eq_one _, map_one]
    · intro h1
      rw [QuotientGroup.mk'_apply] at h1
      have h3 : (u : G) ∈ P :=
        Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff ⟨u, huM⟩).mp h1)
      have h2p : 2 ∣ p := by
        rw [← h.P_card, ← hu.2.1]; exact Subgroup.orderOf_dvd_natCard P h3
      exact hpodd ((Nat.prime_dvd_prime_iff_eq Nat.prime_two h.prime).mp h2p).symm
  have hthat2 : orderOf (QuotientGroup.mk' (P.subgroupOf M) ⟨t, htM⟩) = 2 := by
    apply orderOf_eq_prime
    · rw [← map_pow, show (⟨t, htM⟩ : ↥M) ^ 2 = 1 from by
        rw [← htM2]; exact pow_orderOf_eq_one _, map_one]
    · intro h1
      rw [QuotientGroup.mk'_apply] at h1
      have h3 : (t : G) ∈ P :=
        Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff ⟨t, htM⟩).mp h1)
      exact h.notMem (hPleH h3)
  have hQbar_ut : QuotientGroup.mk' (P.subgroupOf M) ⟨u, huM⟩ *
      QuotientGroup.mk' (P.subgroupOf M) ⟨t, htM⟩ ∈ Qbar :=
    (hinv_mul _ _ huhat2 hthat2 hneUt).1
  have hf_eq : orderOf (QuotientGroup.mk' (P.subgroupOf M) ⟨u, huM⟩ *
      QuotientGroup.mk' (P.subgroupOf M) ⟨t, htM⟩) = f :=
    (hinv_mul _ _ huhat2 hthat2 hneUt).2
  -- ## transport `Qbar` to a subgroup of `G`
  let Q : Subgroup G := (Qbar.comap (QuotientGroup.mk' (P.subgroupOf M))).map (Subgroup.subtype M)
  have hQM : Q ≤ M := Subgroup.map_subtype_le _
  have hQmem : ∀ x : G, x ∈ Q ↔ ∃ (hxM : x ∈ M),
      QuotientGroup.mk' (P.subgroupOf M) ⟨x, hxM⟩ ∈ Qbar := by
    intro x
    constructor
    · intro hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
      exact ⟨hyx ▸ y.2, hyx ▸ hy⟩
    · rintro ⟨hxM, hx⟩
      exact Subgroup.mem_map.mpr ⟨⟨x, hxM⟩, hx, rfl⟩
  have hPQ : P ≤ Q := by
    intro x hx
    rw [hQmem]
    refine ⟨Subgroup.le_normalizer (H := P) hx, ?_⟩
    have h1 : QuotientGroup.mk' (P.subgroupOf M) ⟨x, Subgroup.le_normalizer (H := P) hx⟩ = 1 := by
      rw [QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq_one_iff ⟨x, Subgroup.le_normalizer (H := P) hx⟩).mpr
        (Subgroup.mem_subgroupOf.mpr hx)
    rw [h1]; exact Qbar.one_mem
  have hconjQ : ∀ mm ∈ M, ∀ x ∈ Q, mm * x * mm⁻¹ ∈ Q := by
    intro mm hmm x hx
    obtain ⟨hxM, hxq⟩ := (hQmem x).mp hx
    rw [hQmem]
    refine ⟨M.mul_mem (M.mul_mem hmm hxM) (M.inv_mem hmm), ?_⟩
    have h2 : QuotientGroup.mk' (P.subgroupOf M)
          (⟨mm * x * mm⁻¹, M.mul_mem (M.mul_mem hmm hxM) (M.inv_mem hmm)⟩ : ↥M) =
        QuotientGroup.mk' (P.subgroupOf M) ⟨mm, hmm⟩ *
          QuotientGroup.mk' (P.subgroupOf M) ⟨x, hxM⟩ *
          (QuotientGroup.mk' (P.subgroupOf M) ⟨mm, hmm⟩)⁻¹ := by
      rw [show (⟨mm * x * mm⁻¹, M.mul_mem (M.mul_mem hmm hxM) (M.inv_mem hmm)⟩ : ↥M) =
        ⟨mm, hmm⟩ * ⟨x, hxM⟩ * ⟨mm, hmm⟩⁻¹ from Subtype.ext rfl, map_mul, map_mul, map_inv]
    rw [h2]
    exact hQbarN.conj_mem _ hxq _
  have hQN : M ≤ Subgroup.normalizer (Q : Set G) := by
    intro mm hmm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact ⟨hconjQ mm hmm x, fun hx => by
      have h2 := hconjQ mm⁻¹ (M.inv_mem hmm) (mm * x * mm⁻¹) hx
      rwa [show mm⁻¹ * (mm * x * mm⁻¹) * (mm⁻¹)⁻¹ = x from by group] at h2⟩
  have hutQ : u * t ∈ Q := by
    rw [hQmem]
    refine ⟨M.mul_mem huM htM, ?_⟩
    have h1 : QuotientGroup.mk' (P.subgroupOf M) (⟨u * t, M.mul_mem huM htM⟩ : ↥M) =
        QuotientGroup.mk' (P.subgroupOf M) ⟨u, huM⟩ *
          QuotientGroup.mk' (P.subgroupOf M) ⟨t, htM⟩ := by
      rw [show (⟨u * t, M.mul_mem huM htM⟩ : ↥M) = ⟨u, huM⟩ * ⟨t, htM⟩ from Subtype.ext rfl,
        map_mul]
    rw [h1]; exact hQbar_ut
  -- ## the canonical surjection `Q ↠ Qbar`
  let ψ : ↥Q →* M ⧸ P.subgroupOf M :=
    (QuotientGroup.mk' (P.subgroupOf M)).comp (Subgroup.inclusion hQM)
  have hψrange : ∀ y : ↥Q, ψ y ∈ Qbar := by
    intro y
    obtain ⟨hxM, hxq⟩ := (hQmem (y : G)).mp y.2
    have h2 : QuotientGroup.mk' (P.subgroupOf M) (⟨(y : G), hQM y.2⟩ : ↥M) =
        QuotientGroup.mk' (P.subgroupOf M) (⟨(y : G), hxM⟩ : ↥M) := by
      rw [show (⟨(y : G), hQM y.2⟩ : ↥M) = ⟨(y : G), hxM⟩ from Subtype.ext rfl]
    show ψ y ∈ Qbar
    rw [show ψ y = QuotientGroup.mk' (P.subgroupOf M) (⟨(y : G), hQM y.2⟩ : ↥M) from rfl, h2]
    exact hxq
  let φ : ↥Q →* ↥Qbar := ψ.codRestrict Qbar hψrange
  have hφcoe : ∀ y : ↥Q, ((φ y : ↥Qbar) : M ⧸ P.subgroupOf M) =
      QuotientGroup.mk' (P.subgroupOf M) ⟨(y : G), hQM y.2⟩ := fun y => rfl
  have hφsurj : Function.Surjective φ := by
    intro y
    obtain ⟨m, hm⟩ := QuotientGroup.mk'_surjective (P.subgroupOf M) (y : M ⧸ P.subgroupOf M)
    have hxq : (m : G) ∈ Q := by
      rw [hQmem]
      exact ⟨m.2, hm ▸ y.2⟩
    refine ⟨⟨(m : G), hxq⟩, Subtype.ext ?_⟩
    rw [hφcoe,
      show (⟨(m : G), hQM hxq⟩ : ↥M) = m from Subtype.ext rfl]
    exact hm
  have hφker : φ.ker = P.subgroupOf Q := by
    ext y
    rw [MonoidHom.mem_ker]
    constructor
    · intro hy
      have hy' : QuotientGroup.mk' (P.subgroupOf M) ⟨(y : G), hQM y.2⟩ = 1 := by
        have h2 := congrArg (fun z : ↥Qbar => (z : M ⧸ P.subgroupOf M)) hy
        rwa [hφcoe] at h2
      rw [QuotientGroup.mk'_apply] at hy'
      refine Subgroup.mem_subgroupOf.mpr ?_
      exact Subgroup.mem_subgroupOf.mp
        ((QuotientGroup.eq_one_iff (⟨(y : G), hQM y.2⟩ : ↥M)).mp hy')
    · intro hy
      apply Subtype.ext
      show ((φ y : ↥Qbar) : M ⧸ P.subgroupOf M) = ((1 : ↥Qbar) : M ⧸ P.subgroupOf M)
      rw [hφcoe]
      show QuotientGroup.mk' (P.subgroupOf M) ⟨(y : G), hQM y.2⟩ = 1
      refine (QuotientGroup.eq_one_iff (⟨(y : G), hQM y.2⟩ : ↥M)).mpr ?_
      exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hy)
  -- ## `Qbar` is an `f`-group of odd order; `Q` has odd order
  have hQbar_pg : IsPGroup f ↥Qbar := by
    rw [isPGroup_iff_orderOf_dvd_pow]
    intro y
    exact ⟨1, by rw [pow_one]; exact orderOf_dvd_iff_pow_eq_one.mpr (Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hQbar_exp _ y.2))⟩
  have hf35 : f = 3 ∨ f = 5 := by
    have hf_dvd : f ∣ orderOf (u * t) := by
      have h1 : orderOf (QuotientGroup.mk' (P.subgroupOf M)
          (⟨u * t, M.mul_mem huM htM⟩ : ↥M)) = f := by
        rw [show (⟨u * t, M.mul_mem huM htM⟩ : ↥M) = ⟨u, huM⟩ * ⟨t, htM⟩ from Subtype.ext rfl,
          map_mul]
        exact hf_eq
      have h2 := orderOf_map_dvd (QuotientGroup.mk' (P.subgroupOf M))
        (⟨u * t, M.mul_mem huM htM⟩ : ↥M)
      have h3 : orderOf (⟨u * t, M.mul_mem huM htM⟩ : ↥M) = orderOf (u * t) :=
        (Subgroup.orderOf_coe (⟨u * t, M.mul_mem huM htM⟩ : ↥M)).symm
      rw [h3] at h2
      rw [h1] at h2
      exact h2
    have h := Work.NormalComplement.Sec5CKappa.prop2a_orderof hFT hC hC4 hP3 hIII hMF2 h u hu
    rcases h with h3 | h5
    · left
      rw [h3] at hf_dvd
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hf_dvd with h1 | h1
      · exact absurd h1 hfprime.ne_one
      · exact h1
    · right
      rw [h5] at hf_dvd
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hf_dvd with h1 | h1
      · exact absurd h1 hfprime.ne_one
      · exact h1
  have hfodd : Odd f :=
    hf35.elim (fun h => by rw [h]; norm_num) (fun h => by rw [h]; norm_num)
  have hp7 : 7 ≤ p := sec5_prop1 hFT hC4 Work.NormalComplement.bender_prelim
    Work.NormalComplement.burnsideClassProp h
  have hf_ne_p : f ≠ p := by rcases hf35 with h | h <;> rw [h] at * <;> omega
  have hQbar_odd : Odd (Nat.card ↥Qbar) := by
    haveI : Fact f.Prime := ⟨hfprime⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := f)).mp hQbar_pg
    rw [hk]; exact hfodd.pow
  have hkerodd : Odd (Nat.card ↥(φ.ker)) := by
    rw [hφker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show P ≤ Q from hPQ)).toEquiv,
      h.P_card]
    exact h.prime.odd_of_ne_two hpodd
  have hQodd : Odd (Nat.card ↥Q) := by
    have h1 : Nat.card ↥Q = Nat.card ↥(φ.ker) * Nat.card ↥Qbar := by
      rw [← Subgroup.card_mul_index (φ.ker), Subgroup.index_eq_card,
        Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφsurj).toEquiv]
    rw [h1]; exact hkerodd.mul hQbar_odd
  -- ## `C_{Qbar}(û) = 1`
  have huhat_stab : QuotientGroup.mk' (P.subgroupOf M) ⟨u, huM⟩ ∈
      MulAction.stabilizer (M ⧸ P.subgroupOf M) a0 := by
    rw [kappa_stabilizer_eq hpt]
    exact Subgroup.mem_map.mpr ⟨⟨u, huM⟩, Subgroup.mem_subgroupOf.mpr ⟨huM, hu.1⟩, rfl⟩
  have hCQbar : ∀ y ∈ Qbar, QuotientGroup.mk' (P.subgroupOf M) ⟨u, huM⟩ * y =
      y * QuotientGroup.mk' (P.subgroupOf M) ⟨u, huM⟩ → y = 1 := by
    intro y hy hcomm
    have h2 : ((y • a0 : ↥S) : G ⧸ H) = (QuotientGroup.mk (1 : G) : G ⧸ H) := by
      have h3 : (⟨u, huM⟩ : ↥M) • (y • a0) = y • a0 := by
        rw [← kappa_quot_smul_mk (H := H) (P := P) ⟨u, huM⟩ (y • a0)]
        rw [← mul_smul, hcomm, mul_smul, MulAction.mem_stabilizer_iff.mp huhat_stab]
      exact kappa_u_fix h.se u hu.1 hu.2.1 huM (y • a0) h3
    have hy_stab : y ∈ MulAction.stabilizer (M ⧸ P.subgroupOf M) a0 := by
      rw [MulAction.mem_stabilizer_iff]
      exact Subtype.ext h2
    have hmem : y ∈ Qbar ⊓ MulAction.stabilizer (M ⧸ P.subgroupOf M) a0 := ⟨hy, hy_stab⟩
    rw [hQbar_inf] at hmem
    exact Subgroup.mem_bot.mp hmem
  -- ## `C_Q(u) = P`
  have hCQ : Subgroup.centralizer ({u} : Set G) ⊓ Q = P := by
    refine le_antisymm ?_ ?_
    · intro x hx
      obtain ⟨hxC, hxQ⟩ := Subgroup.mem_inf.mp hx
      obtain ⟨hxM, hxq⟩ := (hQmem x).mp hxQ
      have hcomm : QuotientGroup.mk' (P.subgroupOf M) ⟨u, huM⟩ *
          QuotientGroup.mk' (P.subgroupOf M) ⟨x, hxM⟩ =
          QuotientGroup.mk' (P.subgroupOf M) ⟨x, hxM⟩ *
            QuotientGroup.mk' (P.subgroupOf M) ⟨u, huM⟩ := by
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hxC).symm
      have hxq1 : QuotientGroup.mk' (P.subgroupOf M) ⟨x, hxM⟩ = 1 := hCQbar _ hxq hcomm
      rw [QuotientGroup.mk'_apply] at hxq1
      exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff ⟨x, hxM⟩).mp hxq1)
    · intro x hx
      refine Subgroup.mem_inf.mpr ⟨?_, hPQ hx⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hu.2.2) x (h.P_le hx).2
  -- ## `Q/P` is abelian, i.e. `[Q,Q] ≤ P`
  have hqq : ∀ a ∈ Q, ∀ b ∈ Q, ⁅a, b⁆ ∈ P := by
    intro a ha b hb
    obtain ⟨haM, haq⟩ := (hQmem a).mp ha
    obtain ⟨hbM, hbq⟩ := (hQmem b).mp hb
    have h1 : (QuotientGroup.mk' (P.subgroupOf M) ⟨a, haM⟩) *
        (QuotientGroup.mk' (P.subgroupOf M) ⟨b, hbM⟩) =
        (QuotientGroup.mk' (P.subgroupOf M) ⟨b, hbM⟩) *
          (QuotientGroup.mk' (P.subgroupOf M) ⟨a, haM⟩) :=
      hQbar_ab _ haq _ hbq
    have hcommQ : ⁅a, b⁆ ∈ Q := by
      rw [commutatorElement_def]
      exact Q.mul_mem (Q.mul_mem (Q.mul_mem ha hb) (Q.inv_mem ha)) (Q.inv_mem hb)
    obtain ⟨habM, -⟩ := (hQmem ⁅a, b⁆).mp hcommQ
    have h2 : QuotientGroup.mk' (P.subgroupOf M) ⟨⁅a, b⁆, habM⟩ = 1 := by
      have h3 : (⟨⁅a, b⁆, habM⟩ : ↥M) =
          ⟨a, haM⟩ * ⟨b, hbM⟩ * ⟨a, haM⟩⁻¹ * ⟨b, hbM⟩⁻¹ :=
        Subtype.ext (commutatorElement_def a b)
      rw [h3, map_mul, map_mul, map_mul, map_inv, map_inv, h1]
      group
    rw [QuotientGroup.mk'_apply] at h2
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff ⟨⁅a, b⁆, habM⟩).mp h2)
  -- ## the coprimality hypothesis of App. I (5)(b)
  have huXn : NormalizedBy u Q := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp (hQN huM) x).mp hx
  have hu2cop : Nat.Coprime (Nat.card Q) 2 := Nat.coprime_two_right.mpr hQodd
  have hQsolv : Group.IsSolvable ↥Q := hFT ↥Q hQodd
  have hKappKset : Kapp u Q = Kset Q u :=
    ((appI_one (d := 2) Nat.prime_two hu.2.1 huXn hu2cop).2 rfl).1
  have hKapp : (Kapp u Q).ncard = (P.subgroupOf Q).index := by
    have h1 := (appI_one (d := 2) Nat.prime_two hu.2.1 huXn hu2cop).1
    rwa [hCQ] at h1
  have hcop : Nat.Coprime (Kapp u Q).ncard
      (Nat.card ↥(Work.Fitting.fitting ↥(Subgroup.centralizer ({u} : Set G) ⊓ Q))) := by
    rw [hKapp, ← hφker, Subgroup.index_eq_card,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφsurj).toEquiv]
    refine Nat.coprime_of_dvd' (fun q hq hqK hqF => ?_)
    have hqFp : q ∣ p := by
      have h2 := Subgroup.card_dvd_of_le (le_top :
        Work.Fitting.fitting ↥(Subgroup.centralizer ({u} : Set G) ⊓ Q) ≤ ⊤)
      rw [Subgroup.card_top] at h2
      rw [hCQ] at hqF
      rw [hCQ, h.P_card] at h2
      exact hqF.trans h2
    have hqp : q = p := (Nat.prime_dvd_prime_iff_eq hq h.prime).mp hqFp
    rw [hqp] at hqK
    haveI : Fact f.Prime := ⟨hfprime⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := f)).mp hQbar_pg
    rw [hk] at hqK
    have hpf : p = f := (Nat.prime_dvd_prime_iff_eq h.prime hfprime).mp (h.prime.dvd_of_dvd_pow hqK)
    exact absurd hpf.symm hf_ne_p
  -- ## App. I (5)(b)
  obtain ⟨K, hKset, hKcomp⟩ :=
    appI_five_b (d := 2) Nat.prime_two hu.2.1 huXn hu2cop hQsolv hcop
  have hKle : K ≤ Q := hKcomp.1
  have hQK : Q ≤ Subgroup.normalizer (K : Set G) := hKcomp.2.1
  have hKinf : K ⊓ (Subgroup.centralizer ({u} : Set G) ⊓ Q) = ⊥ := hKcomp.2.2.1
  have hKP : K ⊓ P = ⊥ := by rw [← hCQ]; exact hKinf
  have hKset' : (K : Set G) = Kset Q u := hKset.trans hKappKset
  have hu2 : u * u = 1 := by
    have h' := pow_orderOf_eq_one u; rw [hu.2.1] at h'; simpa [pow_two] using h'
  have ht2 : t * t = 1 := by
    have h' := pow_orderOf_eq_one t; rw [h.invol] at h'; simpa [pow_two] using h'
  refine ⟨K, ?_, ?_, ?_⟩
  · -- `κ ⊆ Mset u t`
    intro x hx
    have hxK : x ∈ K := hx
    rw [hKset'] at hx
    rw [show Work.NormalComplement.Design.Mset u t =
        {y : G | y ∈ Subgroup.centralizer ({u * t} : Set G) ∧ t * y * t⁻¹ = y⁻¹} from rfl]
    have hcomm_ut : x * (u * t) = (u * t) * x := by
      have h1 : ⁅x, u * t⁆ ∈ P := hqq x hx.1 (u * t) hutQ
      have h2 : ⁅x, u * t⁆ ∈ K := by
        have h3 : (u * t) * x⁻¹ * (u * t)⁻¹ ∈ K :=
          (Subgroup.mem_normalizer_iff.mp (hQK hutQ) x⁻¹).mp (K.inv_mem hxK)
        have h4 : x * ((u * t) * x⁻¹ * (u * t)⁻¹) ∈ K := K.mul_mem hxK h3
        rwa [show x * ((u * t) * x⁻¹ * (u * t)⁻¹) = ⁅x, u * t⁆ from by
          rw [commutatorElement_def]; group] at h4
      have h5 : ⁅x, u * t⁆ = 1 := by
        have h6 : ⁅x, u * t⁆ ∈ K ⊓ P := ⟨h2, h1⟩
        rw [hKP] at h6
        exact Subgroup.mem_bot.mp h6
      rw [commutatorElement_def] at h5
      calc x * (u * t) = ((x * (u * t)) * x⁻¹ * (u * t)⁻¹) * (u * t) * x := by group
        _ = 1 * (u * t) * x := by rw [h5]
        _ = (u * t) * x := by rw [one_mul]
    refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr hcomm_ut, ?_⟩
    have hux : (u * t) * x * (u * t)⁻¹ = x := by rw [← hcomm_ut]; group
    calc t * x * t⁻¹ = (u * (u * t)) * x * (u * (u * t))⁻¹ := by
          rw [← mul_assoc, hu2, one_mul]
      _ = u * ((u * t) * x * (u * t)⁻¹) * u⁻¹ := by group
      _ = u * x * u⁻¹ := by rw [hux]
      _ = x⁻¹ := hx.2
  · -- `u * t ∈ κ`
    change u * t ∈ (K : Set G)
    rw [hKset']
    exact ⟨hutQ, by
      calc u * (u * t) * u⁻¹ = (u * u) * t * u⁻¹ := by group
        _ = t * u⁻¹ := by rw [hu2, one_mul]
        _ = t * u := by rw [inv_eq_of_mul_eq_one_right hu2]
        _ = (u * t)⁻¹ := by rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ht2,
            inv_eq_of_mul_eq_one_right hu2]⟩
  · -- `N_H(P) ≤ N_G(κ)`
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    have hnu : ∀ m ∈ H ⊓ Subgroup.normalizer (P : Set G), m * u * m⁻¹ = u := by
      intro m hm2
      have h1 : m * u * m⁻¹ ∈ H ⊓ Subgroup.normalizer (P : Set G) :=
        ⟨H.mul_mem (H.mul_mem hm2.1 hu.1) (H.inv_mem hm2.1),
          (Subgroup.normalizer (P : Set G)).mul_mem
            ((Subgroup.normalizer (P : Set G)).mul_mem hm2.2 huM)
            ((Subgroup.normalizer (P : Set G)).inv_mem hm2.2)⟩
      exact huniq _ h1 ((orderOf_conj3 (m : G) u).trans hu.2.1)
    have hforward : ∀ m ∈ H ⊓ Subgroup.normalizer (P : Set G), ∀ y ∈ Kset Q u,
        m * y * m⁻¹ ∈ Kset Q u := by
      intro m hm2 y hy
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hQN hm2.2) y).mp hy.1, ?_⟩
      have hmu := hnu m hm2
      have hmu' : m⁻¹ * u * m = u := by
        calc m⁻¹ * u * m = m⁻¹ * (m * u * m⁻¹) * m := by rw [hmu]
          _ = u := by group
      have hmu'' : m⁻¹ * u⁻¹ * m = u⁻¹ := by
        calc m⁻¹ * u⁻¹ * m = m⁻¹ * (m * u * m⁻¹)⁻¹ * m := by rw [hmu]
          _ = u⁻¹ := by group
      calc u * (m * y * m⁻¹) * u⁻¹
          = m * (m⁻¹ * u * m) * y * (m⁻¹ * u⁻¹ * m) * m⁻¹ := by group
        _ = m * u * y * u⁻¹ * m⁻¹ := by rw [hmu', hmu'']
        _ = m * (u * y * u⁻¹) * m⁻¹ := by group
        _ = m * y⁻¹ * m⁻¹ := by rw [hy.2]
        _ = (m * y * m⁻¹)⁻¹ := by group
    have hKiff : ∀ y : G, (y ∈ K) ↔ (y ∈ Kset Q u) := by
      intro y
      change y ∈ (K : Set G) ↔ y ∈ Kset Q u
      rw [hKset']
    intro x
    rw [hKiff x, hKiff (n * x * n⁻¹)]
    exact ⟨hforward n hn x, fun hx => by
      have hmem : x = n⁻¹ * (n * x * n⁻¹) * n := by group
      rw [hmem]
      simpa using hforward n⁻¹ ⟨H.inv_mem hn.1, (Subgroup.normalizer (P : Set G)).inv_mem hn.2⟩
        (n * x * n⁻¹) hx⟩


end Work.NormalComplement
