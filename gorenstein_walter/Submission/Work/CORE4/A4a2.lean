import Mathlib
import Submission.Work.CORE4.Defs10
import Submission.Work.CORE4.Defs17
import Submission.Work.CORE4.NotA7Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.A4aAux.U_eq_F_sup_invSet
import Submission.Work.CORE4.A7Split
import Submission.Work.CORE4.A7KBound.K_le_layerIn_and_inf_center

namespace Work.CORE4

open Work.GW2 Subgroup
open scoped Pointwise

/-- In a group of prime order `p`, a nontrivial element generates the whole group. -/
private theorem eq_zpowers_of_card_prime {G : Type} [Group G] [Finite G] {H : Subgroup G}
    {p : ℕ} (hp : Nat.Prime p) (hcard : Nat.card ↥H = p) {g : G} (hg : g ∈ H) (hg1 : g ≠ 1) :
    H = Subgroup.zpowers g := by
  have hdvd : orderOf g ∣ p := by
    rw [← hcard]
    exact Subgroup.orderOf_dvd_natCard H hg
  have hne : orderOf g ≠ 1 := fun h => hg1 (orderOf_eq_one_iff.mp h)
  have hord : orderOf g = p := by
    rcases hp.eq_one_or_self_of_dvd (orderOf g) hdvd with h | h
    · exact absurd h hne
    · exact h
  refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hg) ?_).symm
  rw [hcard, Nat.card_zpowers, hord]

/-- A cyclic subgroup is commutative. -/
private theorem zpowers_isMulCommutative {G : Type} [Group G] (g : G) :
    IsMulCommutative ↥(Subgroup.zpowers g) :=
  IsMulCommutative.of_comm fun a b => by
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp a.2
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp b.2
    refine Subtype.ext ?_
    show a.1 * b.1 = b.1 * a.1
    rw [← hm, ← hn, ← zpow_add, ← zpow_add, add_comm]

/-- If `H` centralizes `K` and both are commutative, then `H ⊔ K` is commutative.

Every element of `H ⊔ K` is a product `h · k` (`K` is normalized by `H`, so the product is the
subgroup `H ⊔ K`), and all the cross terms commute. -/
private theorem sup_isMulCommutative {G : Type} [Group G] (H K : Subgroup G)
    (h : H ≤ Subgroup.centralizer (K : Set G))
    (hH : IsMulCommutative ↥H) (hK : IsMulCommutative ↥K) :
    IsMulCommutative ↥(H ⊔ K) := by
  have hN : H ≤ Subgroup.normalizer (K : Set G) :=
    le_trans h (Subgroup.centralizer_le_normalizer (K : Set G))
  have hcoe : ((H ⊔ K : Subgroup G) : Set G) = (H : Set G) * (K : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right H K hN
  -- all cross terms commute
  have hcross : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.mp (h hx) y hy).symm
  refine IsMulCommutative.of_comm fun a b => ?_
  obtain ⟨h1, hh1, k1, hk1, ha⟩ : ∃ h1 ∈ H, ∃ k1 ∈ K, h1 * k1 = a.1 := by
    have ha : a.1 ∈ (H : Set G) * (K : Set G) := by rw [← hcoe]; exact a.2
    simpa using Set.mem_mul.mp ha
  obtain ⟨h2, hh2, k2, hk2, hb⟩ : ∃ h2 ∈ H, ∃ k2 ∈ K, h2 * k2 = b.1 := by
    have hb : b.1 ∈ (H : Set G) * (K : Set G) := by rw [← hcoe]; exact b.2
    simpa using Set.mem_mul.mp hb
  have hHc : h1 * h2 = h2 * h1 :=
    congrArg Subtype.val (isMulCommutative_iff.mp hH ⟨h1, hh1⟩ ⟨h2, hh2⟩)
  have hKc : k1 * k2 = k2 * k1 :=
    congrArg Subtype.val (isMulCommutative_iff.mp hK ⟨k1, hk1⟩ ⟨k2, hk2⟩)
  have e1 : (h1 * k1) * (h2 * k2) = (h1 * h2) * (k1 * k2) := by
    rw [mul_assoc h1 k1 (h2 * k2), ← mul_assoc k1 h2 k2, ← hcross h2 hh2 k1 hk1,
      mul_assoc h2 k1 k2, ← mul_assoc h1 h2 (k1 * k2)]
  have e2 : (h2 * k2) * (h1 * k1) = (h2 * h1) * (k2 * k1) := by
    rw [mul_assoc h2 k2 (h1 * k1), ← mul_assoc k2 h1 k1, ← hcross h1 hh1 k2 hk2,
      mul_assoc h1 k2 k1, ← mul_assoc h2 h1 (k2 * k1)]
  have hgoal : (a : G) * (b : G) = (b : G) * (a : G) := by
    rw [show (a : G) = h1 * k1 from ha.symm, show (b : G) = h2 * k2 from hb.symm,
      e1, hHc, hKc, ← e2]
  exact Subtype.ext hgoal

/-- `U = O(H)` is **not** abelian in the `A₇` case of §4 (any `A7Facts2` budget).

If `U` were commutative then, as `F ≤ U`, `U ≤ C_G(F) ≤ N_G(F) = M` (`Case2Pre.F_cent` composed
with `Case2Pre.N_F`); together with `S ≤ E(M) ≤ M` (`A7Facts2`) and `H = U ⊔ S` (`A7Split`) this
gives `H ≤ M`, contradicting `Case2Pre.not_H_le`. -/
private theorem U_not_isMulCommutative (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G] (B : Work.GW2.BenderSetup G)
      (C : Work.GW2.Case2Ctx6 B),
      Work.GW2.BenderCtx G → Work.GW2.A7Facts2 B C.D → ¬ IsMulCommutative ↥B.U := by
  intro G _ _ B C hbc h2 hab
  have hsplit : B.H = B.U ⊔ (B.S : Subgroup G) := Work.CORE4.A7Split I hbc h2
  -- `U ≤ C_G(F)`, because `F ≤ U` and `U` is commutative.
  have hUleC : B.U ≤ Subgroup.centralizer (C.D.F : Set G) := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have h := congrArg Subtype.val
      (isMulCommutative_iff.mp hab ⟨u, hu⟩ ⟨f, Work.GW2.Case2Data.F_le_U B C.D hf⟩)
    simpa using h.symm
  -- `N_G(F) = M`, so `U ≤ M`.
  have hUleM : B.U ≤ C.D.M := by
    rw [← Work.GW2.Case2Pre.N_F B C.D C.pre]
    exact le_trans hUleC (Subgroup.centralizer_le_normalizer (C.D.F : Set G))
  -- `S ≤ E(M) ≤ M`.
  have hSleM : (B.S : Subgroup G) ≤ C.D.M :=
    le_trans h2.2.2.1 (Subgroup.map_subtype_le (layer C.D.M))
  exact C.pre.1 (hsplit ▸ sup_le hUleM hSleM)

/-- **A4a2 (design pass 17 ruling on `NOTES_TO_LEAD.md` §14).**  In the exceptional case
`Case2InvNormal B C.D` (i.e. `I_U(s) ⊴ Ĥ`): `K = Z(U)`, **and** the export
`(U : Set G) = (F : Set G) * I_U(s)` as sets, which `A4c`'s step 1 needs (to get
`K' ≤ C_G(U)` from `K' ≤ C_G(F) ∩ C_G(I_U(s))`).

`A4a2Prop I` = `A4aProp I`'s conclusion conjoined with the export, under the same hypotheses.

Route: `A4a` is PROVED (`Submission.Work.CORE4/A4a.lean`, whose proof already establishes the
export internally via `Work.CORE4.A4aAux.U_eq_F_sup_invSet`: `U = F ⊔ I` with `(I : Set G) =
invSet B.U s`, and `F` normalises `I`, so the sup is the pointwise product).  So this leaf is
`A4a`'s proof plus the export: reuse `A4aAux.U_eq_F_sup_invSet` (the subgroup `Is` is the witness
supplied by `Case2InvNormal`) and `Subgroup.coe_sup`/`Set.sup_eq_mul` for the set product.

The export is Bender 1.5's cardinality clause `|I_U(s)| · |C_U(s)| = |U|` together with
`C_U(s) = B₀ = F` (proved: `Work.CORE4.Case2CU_s`) and `F ∩ I_U(s) = 1`. -/
theorem A4a2 (I : Work.GW2.C4Inputs) : Work.CORE4.C15.A4a2Prop I := by
  intro G _ _ B C hHyp hA7 h1F h2F hUData hInv
  obtain ⟨hbc, _hcase2, hplus, _hseven, _height⟩ := hHyp
  obtain ⟨_hKcard, hFcard, _hK0eq, _hpi⟩ := h1F
  obtain ⟨_hU3, hB0F, _hoddCoreF, _hbound⟩ := hUData
  obtain ⟨Is, hIset, _hIleHhat, hInormal⟩ := hInv
  have hIset' : ∀ y : G, y ∈ Is ↔ y ∈ invSet B.U C.D.s := fun y => Set.ext_iff.mp hIset y
  have hKdef : ∀ y : G, y ∈ C.D.K ↔ y ∈ invSet (B.U ⊓ C.D.M) C.D.s :=
    fun y => Set.ext_iff.mp C.D.K_def y
  -- `I_U(s) ≤ U`.
  have hIsleU : Is ≤ B.U := fun x hx => ((hIset' x).mp hx).1
  -- `s ∈ N_G(U)`: `s ∈ S ≤ H` and `U = O(H) ⊴ H`.
  have hsNU : C.D.s ∈ Subgroup.normalizer ((B.U : Subgroup G) : Set G) := by
    have hsH : C.D.s ∈ B.H := B.S_le_H C.D.s_mem_S
    have hUnorm : ∀ y ∈ B.U, ∀ k ∈ B.H, k * y * k⁻¹ ∈ B.U := fun y hy k hk =>
      (Subgroup.normal_subgroupOf_iff B.U_le_H).mp B.U_normal y k hy hk
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hUnorm y hy C.D.s hsH, fun hy => ?_⟩
    have h2 := hUnorm (C.D.s * y * C.D.s⁻¹) hy C.D.s⁻¹ (B.H.inv_mem hsH)
    have h3 : C.D.s⁻¹ * (C.D.s * y * C.D.s⁻¹) * (C.D.s⁻¹)⁻¹ = y := by group
    rwa [h3] at h2
  -- Bender 1.5 (`I.toolkit.c15`) applied to `U` and `s`.
  have hc15 := I.toolkit.c15 G I.toolkit.ft B.U C.D.s C.D.s_order B.U_odd hsNU
  have hIscomm : ∀ a b : ↥Is, a * b = b * a := isMulCommutative_iff.mp (hc15.2.2 Is hIset).1
  have hInormBU : (Is.subgroupOf B.U).Normal := (hc15.2.2 Is hIset).2.1
  -- `U = F ⊔ I_U(s)`; `U` is not abelian.
  have hUeq : B.U = C.D.F ⊔ Is :=
    Work.CORE4.A4aAux.U_eq_F_sup_invSet I G B C.D C.pre hB0F Is hIset
  have hUnotAb : ¬ IsMulCommutative ↥B.U :=
    U_not_isMulCommutative I G B C hbc h2F
  -- `F` normalises `I_U(s)` (as `I_U(s) ⊴ U` and `F ≤ U`).
  have hDFnorm : C.D.F ≤ Subgroup.normalizer (Is : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro f hf x hx
    exact (Subgroup.normal_subgroupOf_iff hIsleU).mp hInormBU x f hx (Case2Data.F_le_U B C.D hf)
  -- `K ≤ I_U(s)` and `K ≤ E(M)`.
  have hKleIs : C.D.K ≤ Is := fun x hx =>
    (hIset' x).mpr ⟨Case2Data.K_le_U B C.D hx, Case2Data.K_inv B C.D x hx⟩
  have hKleE : C.D.K ≤ layerIn C.D.M :=
    (A7KBound.K_le_layerIn_and_inf_center (B := B) (D := C.D) hplus B.U_odd).1
  -- `K ≤ Z(U)`.
  have hKleZ : C.D.K ≤ (Subgroup.center ↥B.U).map B.U.subtype := by
    intro k hk
    have hkU : k ∈ B.U := Case2Data.K_le_U B C.D hk
    have hkIs : k ∈ Is := hKleIs hk
    have hkE : k ∈ layerIn C.D.M := hKleE hk
    refine Subgroup.mem_map.mpr ⟨⟨k, hkU⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    have hcent : B.U ≤ Subgroup.centralizer ({k} : Set G) := by
      rw [hUeq]
      refine sup_le ?_ ?_
      · intro f hf
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact ((Subgroup.mem_centralizer_iff.mp (Case2Pre.F_cent B C.D C.pre hf)) k hkE).symm
      · intro y hy
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact congrArg Subtype.val (hIscomm ⟨y, hy⟩ ⟨k, hkIs⟩)
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hcent g.2))
  -- `Z(U) ≤ K`.
  have hZleK : (Subgroup.center ↥B.U).map B.U.subtype ≤ C.D.K := by
    intro z hz
    obtain ⟨z0, hz0, hzeq⟩ := Subgroup.mem_map.mp hz
    rw [← hzeq]
    change (z0 : G) ∈ C.D.K
    have hz0c : ∀ g : ↥B.U, g * z0 = z0 * g := Subgroup.mem_center_iff.mp hz0
    -- write `z0` in the product `I_U(s) · F` (which is `U`)
    have hz0sup : z0.1 ∈ (Is ⊔ C.D.F : Subgroup G) := by
      rw [sup_comm, ← hUeq]
      exact z0.2
    have hz0mul : z0.1 ∈ (Is : Set G) * (C.D.F : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left Is C.D.F hDFnorm]
      exact hz0sup
    obtain ⟨i, hiIs, f, hfF, hif⟩ := Set.mem_mul.mp hz0mul
    -- the `F`-coordinate of a central element is `1`
    have hfcent : ∀ y ∈ Is, f * y = y * f := by
      intro y hy
      have hyU : y ∈ B.U := hIsleU hy
      have hzy : y * z0.1 = z0.1 * y := congrArg Subtype.val (hz0c ⟨y, hyU⟩)
      have hyi : y * i = i * y := congrArg Subtype.val (hIscomm ⟨y, hy⟩ ⟨i, hiIs⟩)
      have hiy : i⁻¹ * y * i = y := by
        rw [mul_assoc, hyi, ← mul_assoc, inv_mul_cancel, one_mul]
      calc f * y = (i⁻¹ * (i * f)) * y := by group
        _ = (i⁻¹ * z0.1) * y := by rw [hif]
        _ = i⁻¹ * (z0.1 * y) := by group
        _ = i⁻¹ * (y * z0.1) := by rw [← hzy]
        _ = (i⁻¹ * y) * z0.1 := by group
        _ = (i⁻¹ * y) * (i * f) := by rw [← hif]
        _ = ((i⁻¹ * y) * i) * f := by group
        _ = y * f := by rw [hiy]
    have hf1 : f = 1 := by
      by_contra hf1
      have hDFeq : C.D.F = Subgroup.zpowers f :=
        eq_zpowers_of_card_prime (by norm_num : Nat.Prime 3) hFcard hfF hf1
      have hDFcent : C.D.F ≤ Subgroup.centralizer (Is : Set G) := by
        rw [hDFeq, Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
        intro y hy
        exact (hfcent y hy).symm
      have hDFcomm : IsMulCommutative ↥C.D.F := hDFeq.symm ▸ zpowers_isMulCommutative f
      have hFIs : IsMulCommutative ↥(C.D.F ⊔ Is) :=
        sup_isMulCommutative C.D.F Is hDFcent hDFcomm
          (IsMulCommutative.of_comm hIscomm)
      exact hUnotAb (hUeq.symm ▸ hFIs)
    -- hence `z0 ∈ I_U(s)`, and `z0 ∈ C(F) ≤ N_G(F) = M`
    have hz0Is : z0.1 ∈ Is := by
      rw [← hif, hf1, mul_one]
      exact hiIs
    have hz0inv : C.D.s * z0.1 * C.D.s⁻¹ = z0.1⁻¹ := ((hIset' z0.1).mp hz0Is).2
    have hz0M : z0.1 ∈ C.D.M := by
      have hcen : z0.1 ∈ Subgroup.centralizer (C.D.F : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        exact congrArg Subtype.val (hz0c ⟨a, Case2Data.F_le_U B C.D ha⟩)
      have hnorm : z0.1 ∈ Subgroup.normalizer (C.D.F : Set G) :=
        Subgroup.centralizer_le_normalizer (C.D.F : Set G) hcen
      rwa [Case2Pre.N_F B C.D C.pre] at hnorm
    exact (hKdef z0.1).mpr ⟨Subgroup.mem_inf.mpr ⟨z0.2, hz0M⟩, hz0inv⟩
  refine ⟨le_antisymm hKleZ hZleK, ?_⟩
  -- the export `U = F · I_U(s)` as sets
  rw [← hIset, hUeq]
  exact Subgroup.coe_mul_of_left_le_normalizer_right C.D.F Is hDFnorm

end Work.CORE4
