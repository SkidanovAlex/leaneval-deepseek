import Mathlib
import Submission.Work.CORE4.Defs10
import Submission.Work.CORE4.NotA7Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.A7Split
import Submission.Work.CORE4.A7KBound.K_le_layerIn_and_inf_center
import Submission.Work.CORE4.A4aAux.sup_isMulCommutative
import Submission.Work.CORE4.A4aAux.U_not_isMulCommutative
import Submission.Work.CORE4.A4aAux.U_eq_F_sup_invSet

open scoped Pointwise

namespace Work.CORE4

open Work.GW2 Subgroup

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

/-- **A4a (design pass 15).** In the exceptional case `Case2InvNormal B C.D` (i.e. `I_U(s) ⊴ Ĥ`),
`K = Z(U)`.

Statement copied verbatim from `_design_gw/Core15C4.lean` (and `NotA7Defs.lean`):
`A4aProp I` gives, from `Hyp9 G B C`, `IsA7Case C.D`, `A7Facts1 C.D`, `A7Facts2 B C.D`,
`A7UData B C.D` and `Case2InvNormal B C.D`: `C.D.K = (center ↥B.U).map B.U.subtype`.

Route (design pass 15 §1.3, A4a):
* `I := I_U(s)` is abelian (every element is inverted by `s`), and `U = F·I` (the cardinality
  clause of `I.toolkit.c15`, `C_U(s) = B₀ = F` from `Case2Pre`, `F ∩ I = 1`);
* `K = I_{U∩M}(s) ⊆ I` (`Case2Data.K_def`), so `I` centralizes `K`; `F ≤ C(E)` (`Case2Pre`) and
  `K ≤ E` (`Case2PrePlus`: `K = [S∩E, U∩M]`) give `K ≤ Z(U)`;
* `U` is non-abelian: otherwise `U ≤ C(F) ≤ N(F) = M` and `H = U S` (`I.toolkit.split`) with
  `S ≤ E ≤ M` (`A7Facts2`) gives `H ≤ M`, contradicting `Case2Pre.not_H_le`;
* for `z = f i ∈ Z(U)` with `f ∈ F`, `i ∈ I`: `f ≠ 1` would make `F = ⟨f⟩` centralize `I`, hence
  `U = F I` abelian; so `z ∈ I`, and `z ∈ C(F) ≤ N(F) = M`, whence `z ∈ invSet (U ⊓ M) s = K`. -/
theorem A4a (I : Work.GW2.C4Inputs) : Work.CORE4.C15.A4aProp I := by
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
    Work.CORE4.A4aAux.U_not_isMulCommutative I G B C hbc h2F
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
        Work.CORE4.A4aAux.sup_isMulCommutative C.D.F Is hDFcent hDFcomm
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
  exact le_antisymm hKleZ hZleK

end Work.CORE4
