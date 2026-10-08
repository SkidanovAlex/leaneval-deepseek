import Mathlib
import Submission.Work.BrauerSuzuki.Defs
import Submission.Work.BrauerSuzuki.OddCore.oddCard_oddCore
import Submission.Work.BrauerSuzuki.OddCore.le_of_normal_odd
import Submission.Work.BrauerSuzuki.Group.uniqueInvolution_of_pgroup
import Submission.Work.BrauerSuzuki.Group.isConj_of_orderOf_eq_two
import Submission.Work.BrauerSuzuki.Quaternion.genQuaternionData_basic
import Submission.Work.BrauerSuzuki.Glue.cyclic_sylow_case
import Submission.Work.BrauerSuzuki.Glue.sup_oddCore_centralizer_eq_top
import Submission.Work.ThreePoints.map_oddCore_le_oddCore

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BrauerSuzuki.Glue

open Submission.Blueprint
open scoped Pointwise

/-! ## Helper lemmas for the assembly -/

/-- A subgroup of a group without a four-group has no four-group: a four-group inside `H` maps
to a four-group inside `G` along the inclusion. -/
theorem not_hasFourGroup_subgroup {G : Type*} [Group G] {H : Subgroup G}
    (h : ¬ HasFourGroup G) : ¬ HasFourGroup ↥H := by
  rintro ⟨a, b, ha, hb, hab, hcomm⟩
  refine h ⟨(a : G), (b : G), ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe]; exact ha
  · rw [Subgroup.orderOf_coe]; exact hb
  · intro hh; exact hab (Subtype.ext hh)
  · simpa using congrArg Subtype.val hcomm

/-- In a finite group without a four-group, any two involutions are conjugate: each lies in a
Sylow `2`-subgroup, each such Sylow has a unique involution (`uniqueInvolution_of_pgroup`), and
the Sylow subgroups are conjugate. -/
theorem isConj_involutions_of_not_hasFourGroup {G : Type*} [Group G] [Finite G]
    (h4 : ¬ HasFourGroup G) {u v : G} (hu : orderOf u = 2) (hv : orderOf v = 2) :
    IsConj u v := by
  obtain ⟨Su, huS⟩ := Work.BrauerSuzuki.Group.exists_sylow_mem_of_orderOf_eq_two hu
  obtain ⟨Sv, hvS⟩ := Work.BrauerSuzuki.Group.exists_sylow_mem_of_orderOf_eq_two hv
  have huniqSu : ∀ w : G, w ∈ (Su : Subgroup G) → orderOf w = 2 → w = u :=
    fun w hw hw2 =>
      Work.BrauerSuzuki.Group.uniqueInvolution_of_pgroup Su.isPGroup' h4 hw huS hw2 hu
  obtain ⟨c, hc⟩ := (Sylow.isPretransitive_of_finite (p := 2) (G := G)).exists_smul_eq Sv Su
  have hmem : c * v * c⁻¹ ∈ (Su : Subgroup G) := by
    have hsub : (MulAut.conj c • (Sv : Subgroup G)) = (Su : Subgroup G) := by
      rw [← Sylow.pointwise_smul_def (g := MulAut.conj c) (P := Sv), ← Sylow.smul_def, hc]
    have h0 : (MulAut.conj c) • v ∈ (Su : Subgroup G) := by
      rw [← hsub]
      exact Subgroup.smul_mem_pointwise_smul v (MulAut.conj c) (Sv : Subgroup G) hvS
    simpa [MulAut.smul_def, MulAut.conj_apply] using h0
  have hord : orderOf (c * v * c⁻¹) = 2 := by
    rw [Work.BrauerSuzuki.Group.orderOf_conj_eq, hv]
  have hcv : c * v * c⁻¹ = u := huniqSu (c * v * c⁻¹) hmem hord
  rw [isConj_iff]
  exact ⟨c⁻¹, by rw [← hcv]; group⟩

/-- If `H ◁ G` and `H ⊔ K = ⊤`, every element of `G` is `h * k` with `h ∈ H`, `k ∈ K`:
`H ⊔ K = H K` as sets when `H` is normal. -/
theorem exists_mul_of_sup_eq_top_of_normal {G : Type*} [Group G] {H K : Subgroup G}
    (hH : H.Normal) (hsup : H ⊔ K = ⊤) (x : G) : ∃ h ∈ H, ∃ k ∈ K, h * k = x := by
  haveI : H.Normal := hH
  have hx : x ∈ K ⊔ H := by rw [sup_comm, hsup]; exact Subgroup.mem_top x
  obtain ⟨k, hk, h, hh, hkh⟩ := Subgroup.mem_sup_of_normal_right.mp hx
  refine ⟨k * h * k⁻¹, ?_, k, hk, ?_⟩
  · exact Subgroup.Normal.conj_mem hH h hh k
  · rw [show k * h * k⁻¹ * k = k * h by group, hkh]

/-! The assembly of brauer_suzuki.md §1.1–§1.2: the Prop follows from the weak Brauer–Suzuki
theorem, the classification of 2-groups with a unique involution, and the fact that `G ⧸ O(G)`
has a generalized quaternion Sylow 2-subgroup when `G` does.

Proof route: strong induction on `|G|`.  Let `S` be a Sylow 2-subgroup containing the involution
`t`; by `uniqueInvolution_of_pgroup` (with `¬ HasFourGroup G`) `t` is the unique involution of
`S`, so `hClass` makes `S` cyclic or generalized quaternion.
* cyclic: `Glue/cyclic_sylow_case`.
* generalized quaternion: apply `hW` to `G ⧸ O(G)` (whose generalized quaternion Sylow exists by
  `hQuot`), obtaining `N̄ ⊴ G ⧸ O(G)` proper containing all involutions; let `N` be its preimage,
  so `N ⊴ G`, `N ≠ ⊤`, `O(G) ≤ N`, `t ∈ N`, and every `G`-conjugate of `t` lies in `N` (as
  `N ⊴ G`); moreover every involution of `N` is `N`-conjugate to `t` (`t^g` is the unique
  involution of a Sylow 2-subgroup of `N` and Sylow subgroups of `N` are `N`-conjugate).  Apply
  the induction hypothesis to `N` (which inherits `¬ HasFourGroup`) to get
  `N = O(N) C_N(t)`, hence `t^G = t^N = t^{O(N)} ⊆ t · O(N) ⊆ t · O(G)`.  So
  `t g t⁻¹ g⁻¹ ∈ O(G)` for all `g`, and `Glue/sup_oddCore_centralizer_eq_top` finishes. -/
theorem brauerSuzuki_of_weak (hW : Work.BrauerSuzuki.BrauerSuzukiWeak)
    (hClass : ∀ (P : Type) [Group P] [Finite P], IsPGroup 2 P →
      Work.BrauerSuzuki.HasUniqueInvolution P → Work.BrauerSuzuki.IsCyclicOrGenQuaternion P)
    (hQuot : ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G),
      Work.BrauerSuzuki.IsGenQuaternion ↥S →
      ∃ T : Sylow 2 (G ⧸ Submission.Blueprint.oddCore G),
        Work.BrauerSuzuki.IsGenQuaternion ↥T) :
    Submission.Blueprint.BrauerSuzukiProp := by
  have key : ∀ n : ℕ, ∀ (G : Type) [Group G] [Finite G], Nat.card G = n →
      ¬ HasFourGroup G → ∀ t : G, orderOf t = 2 →
      oddCore G ⊔ Subgroup.centralizer ({t} : Set G) = ⊤ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro G _instG _finG hcard h4 t ht
      obtain ⟨S, htS⟩ := Work.BrauerSuzuki.Group.exists_sylow_mem_of_orderOf_eq_two ht
      have hSUI : Work.BrauerSuzuki.HasUniqueInvolution ↥S := by
        refine ⟨⟨t, htS⟩, (Subgroup.orderOf_mk t htS).trans ht, ?_⟩
        intro w hw
        have hw2 : orderOf (w : G) = 2 := (Subgroup.orderOf_coe w).trans hw
        exact Subtype.ext
          (Work.BrauerSuzuki.Group.uniqueInvolution_of_pgroup S.isPGroup' h4 htS w.2 ht hw2).symm
      rcases hClass ↥S S.isPGroup' hSUI with hcyc | hgen
      · exact cyclic_sylow_case S hcyc ht
      · obtain ⟨T, hTgen⟩ := hQuot G S hgen
        obtain ⟨Nb, hNbnorm, hNbne, hNbinv⟩ := hW (G ⧸ oddCore G) ⟨T, hTgen⟩
        let N : Subgroup G := Subgroup.comap (QuotientGroup.mk' (oddCore G)) Nb
        have hNnorm : N.Normal := hNbnorm.comap (QuotientGroup.mk' (oddCore G))
        haveI : N.Normal := hNnorm
        -- `N` is proper
        have hNne : N ≠ ⊤ := by
          intro htop
          apply hNbne
          have hmap : Subgroup.map (QuotientGroup.mk' (oddCore G)) N = ⊤ := by
            rw [htop, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
          rwa [Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) Nb] at hmap
        -- `t ∉ O(G)`
        have htK : t ∉ oddCore G := by
          intro hmem
          have hdvd : orderOf t ∣ Nat.card (oddCore G) := by
            have h1 := orderOf_dvd_natCard (⟨t, hmem⟩ : oddCore G)
            rwa [Subgroup.orderOf_mk t hmem] at h1
          rw [ht] at hdvd
          exact (Nat.not_even_iff_odd.mpr (Work.BrauerSuzuki.OddCore.oddCard_oddCore (G := G)))
            (even_iff_two_dvd.mpr hdvd)
        -- `t ∈ N`
        have htN : t ∈ N := by
          rw [Subgroup.mem_comap]
          apply hNbinv
          have hne : QuotientGroup.mk' (oddCore G) t ≠ 1 := by
            intro h1
            apply htK
            rw [← QuotientGroup.ker_mk' (oddCore G)]
            exact MonoidHom.mem_ker.mpr h1
          have hdvd : orderOf (QuotientGroup.mk' (oddCore G) t) ∣ 2 := by
            rw [← ht]
            exact orderOf_map_dvd (QuotientGroup.mk' (oddCore G)) t
          rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
          · exact absurd (orderOf_eq_one_iff.mp h1) hne
          · exact h1
        have hcardN : Nat.card ↥N < n := by
          rw [← hcard]
          calc Nat.card ↥N < Nat.card ↥(⊤ : Subgroup G) :=
                Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hNne)
            _ = Nat.card G := Subgroup.card_top
        have h4N : ¬ HasFourGroup ↥N := not_hasFourGroup_subgroup h4
        have htnN : orderOf (⟨t, htN⟩ : ↥N) = 2 := (Subgroup.orderOf_mk t htN).trans ht
        have hdec : oddCore ↥N ⊔ Subgroup.centralizer ({⟨t, htN⟩} : Set ↥N) = ⊤ :=
          ih (Nat.card ↥N) hcardN ↥N rfl h4N ⟨t, htN⟩ htnN
        -- every element of `N` is `O(N) · C_N(t)`
        have decomp : ∀ x : ↥N, ∃ o ∈ oddCore ↥N,
            ∃ c ∈ Subgroup.centralizer ({⟨t, htN⟩} : Set ↥N), o * c = x :=
          fun x => exists_mul_of_sup_eq_top_of_normal
            (inferInstance : (oddCore ↥N).Normal) hdec x
        -- every `N`-conjugate of `t` is `t · k` with `k ∈ O(G)`
        have hclaim : ∀ x : ↥N, ∃ k ∈ oddCore G, (x : G) * t * (x : G)⁻¹ = k * t := by
          intro x
          obtain ⟨o, ho, c, hc, hoc⟩ := decomp x
          have hoG : (o : G) ∈ oddCore G :=
            Work.ThreePoints.map_oddCore_le_oddCore N (Subgroup.mem_map.mpr ⟨o, ho, rfl⟩)
          have hc_comm : t * (c : G) = (c : G) * t := by
            have h := (Subgroup.mem_centralizer_iff.mp hc) ⟨t, htN⟩ (Set.mem_singleton _)
            simpa using congrArg Subtype.val h
          refine ⟨(o : G) * t * (o : G)⁻¹ * t⁻¹, ?_, ?_⟩
          · have hconj : t * (o : G) * t⁻¹ ∈ oddCore G :=
              Subgroup.Normal.conj_mem
                (inferInstance : (oddCore G).Normal) (o : G) hoG t
            have hinv := (oddCore G).inv_mem hconj
            rw [show (o : G) * t * (o : G)⁻¹ * t⁻¹ = (o : G) * (t * (o : G) * t⁻¹)⁻¹ by group]
            exact (oddCore G).mul_mem hoG hinv
          · rw [← hoc]
            have hct : (c : G) * t * (c : G)⁻¹ = t := by rw [← hc_comm]; group
            simp only [Subgroup.coe_mul, Subgroup.coe_inv]
            rw [show (o : G) * (c : G) * t * ((o : G) * (c : G))⁻¹
                  = (o : G) * ((c : G) * t * (c : G)⁻¹) * (o : G)⁻¹ from by group, hct]
            group
        have hmain : ∀ g : G, g⁻¹ * t * g * t⁻¹ ∈ oddCore G := by
          intro g
          have hxN : g⁻¹ * t * g ∈ N := by
            have h := hNnorm.conj_mem t htN g⁻¹
            simpa using h
          let xN : ↥N := ⟨g⁻¹ * t * g, hxN⟩
          have hxord : orderOf xN = 2 := by
            rw [show orderOf xN = orderOf (g⁻¹ * t * g) from
              Subgroup.orderOf_mk (g⁻¹ * t * g) hxN]
            rw [show g⁻¹ * t * g = g⁻¹ * t * (g⁻¹)⁻¹ from by group]
            exact (Work.BrauerSuzuki.Group.orderOf_conj_eq g⁻¹ t).trans ht
          obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_involutions_of_not_hasFourGroup h4N htnN hxord)
          obtain ⟨k, hk, hk_eq⟩ := hclaim c
          have hxg : g⁻¹ * t * g = k * t := by
            have h1 := congrArg (fun z : ↥N => (z : G)) hc
            simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
            exact h1.symm.trans hk_eq
          rw [show g⁻¹ * t * g * t⁻¹ = k by rw [hxg]; group]
          exact hk
        have hcomm : ∀ g : G, t * g * t⁻¹ * g⁻¹ ∈ oddCore G := by
          intro g
          have h := hmain g⁻¹
          rw [show (g⁻¹)⁻¹ = g from inv_inv g] at h
          have hinv := (oddCore G).inv_mem h
          rwa [show (g * t * g⁻¹ * t⁻¹)⁻¹ = t * g * t⁻¹ * g⁻¹ from by group] at hinv
        exact sup_oddCore_centralizer_eq_top ht hcomm
  intro G _instG _finG h4 t ht
  exact key (Nat.card G) G rfl h4 t ht

end Work.BrauerSuzuki.Glue
