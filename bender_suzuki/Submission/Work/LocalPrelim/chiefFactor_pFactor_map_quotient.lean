import Mathlib
import Submission.Work.LocalPrelim.Defs
import Submission.Work.Fitting.Defs
import Submission.Work.Fitting.Main

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.LocalPrelim.chiefFactor_pFactor_map_quotient`

Let `N ⊴ S` have order a `p'`-number, and let `K/H` be a chief factor of `S` of `p`-power
order.  Then `K ⊓ N ≤ H`, the images of `H` and `K` in `S ⧸ N` still form a chief factor of
`S ⧸ N`, and that factor again has `p`-power order.

The key point is that a `p'`-subgroup `N` cannot meet the `p`-part `K/H` of a chief factor
non-trivially: `(K ⊓ N) H / H` is at the same time a `p`-group and a `p'`-group, hence trivial.
-/

open scoped Classical Pointwise

noncomputable section

namespace Work.LocalPrelim

/-- Auxiliary index computation: for a normal subgroup `N`, if `H ≤ K` and `K ⊓ N ≤ H`, then the
relative index `[K ⊔ N : H ⊔ N]` coincides with `[K : H]`.  Indeed both `K ⊔ N = K N` and
`H ⊔ N = H N`, and the two extra factors `N / (K ⊓ N) = N / (H ⊓ N)` cancel. -/
theorem relIndex_sup_eq_of_inf_le {S : Type*} [Group S] [Finite S]
    {N H K : Subgroup S} [N.Normal] (hHK : H ≤ K) (hKN : K ⊓ N ≤ H) :
    (H ⊔ N).relIndex (K ⊔ N) = H.relIndex K := by
  have hNK : N ⊓ K ≤ H := by rwa [inf_comm] at hKN
  have hNH : N ⊓ K = N ⊓ H := by
    refine le_antisymm (le_inf inf_le_left hNK) ?_
    exact le_inf inf_le_left ((inf_le_right : N ⊓ H ≤ H).trans hHK)
  have hi := Subgroup.relIndex_mul_relIndex (H := N) (K := H ⊔ N) (L := K ⊔ N)
    (le_sup_right : N ≤ H ⊔ N) (sup_le_sup_right hHK N)
  rw [Subgroup.relIndex_sup_right H N, Subgroup.relIndex_sup_right K N] at hi
  have hii : N.relIndex H * H.relIndex K = N.relIndex K := by
    have h := Subgroup.relIndex_mul_relIndex (H := N ⊓ K) (K := H) (L := K) hNK hHK
    have h1 : (N ⊓ K).relIndex H = N.relIndex H := by
      rw [hNH, Subgroup.inf_relIndex_right]
    have h2 : (N ⊓ K).relIndex K = N.relIndex K := Subgroup.inf_relIndex_right N K
    rw [h1, h2] at h
    exact h
  have hcardH : Nat.card ↥H ≠ 0 := by
    rw [Nat.card_ne_zero]
    exact ⟨⟨1, H.one_mem⟩, inferInstance⟩
  have hne : N.relIndex H ≠ 0 := fun h0 =>
    hcardH (Nat.zero_dvd.mp (h0 ▸ Subgroup.relIndex_dvd_card N H))
  exact Nat.mul_left_cancel (Nat.pos_of_ne_zero hne) (hi.trans hii.symm)

theorem chiefFactor_pFactor_map_quotient {S : Type*} [Group S] [Finite S] {p : ℕ}
    {N H K : Subgroup S} [N.Normal] (hHK : Work.Fitting.IsChiefFactor H K)
    (hpf : Work.LocalPrelim.IsPFactor p H K)
    (hN : Work.Fitting.IsPiNat (fun q => q ≠ p) (Nat.card ↥N)) :
    Work.Fitting.IsChiefFactor (H.map (QuotientGroup.mk' N)) (K.map (QuotientGroup.mk' N)) ∧
      Work.LocalPrelim.IsPFactor p (H.map (QuotientGroup.mk' N)) (K.map (QuotientGroup.mk' N)) ∧
      K ⊓ N ≤ H := by
  haveI hHn : H.Normal := hHK.1
  have hKn : K.Normal := hHK.2.1
  have hlt : H < K := hHK.2.2.1
  have hmin : ∀ M : Subgroup S, M.Normal → H ≤ M → M ≤ K → M = H ∨ M = K := hHK.2.2.2
  have hHKle : H ≤ K := hpf.1
  have hpfidx : Work.Fitting.IsPiNat (fun q => q = p) (H.subgroupOf K).index := hpf.2
  -- ### The `p'`-part of `N` inside `K` lies in `H`.
  have hKN : K ⊓ N ≤ H := by
    have hcard_map : Nat.card ↥(K.map (QuotientGroup.mk' H)) = (H.subgroupOf K).index := by
      rw [← Subgroup.relIndex_ker K (QuotientGroup.mk' H), QuotientGroup.ker_mk']
      simp only [Subgroup.relIndex]
    have hle : (K ⊓ N).map (QuotientGroup.mk' H) ≤ K.map (QuotientGroup.mk' H) :=
      Subgroup.map_mono inf_le_left
    have hdiv1 : Nat.card ↥((K ⊓ N).map (QuotientGroup.mk' H)) ∣ Nat.card ↥(K ⊓ N) :=
      Subgroup.card_map_dvd (K ⊓ N) (QuotientGroup.mk' H)
    have hdiv2 : Nat.card ↥((K ⊓ N).map (QuotientGroup.mk' H)) ∣
        Nat.card ↥(K.map (QuotientGroup.mk' H)) := by
      have h := Subgroup.card_subgroup_dvd_card
        (((K ⊓ N).map (QuotientGroup.mk' H)).subgroupOf (K.map (QuotientGroup.mk' H)))
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at h
    have hdivN : Nat.card ↥(K ⊓ N) ∣ Nat.card ↥N := by
      have h := Subgroup.card_subgroup_dvd_card ((K ⊓ N).subgroupOf N)
      rwa [Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (inf_le_right : K ⊓ N ≤ N)).toEquiv] at h
    have hp' : Work.Fitting.IsPiNat (fun q => q ≠ p)
        (Nat.card ↥((K ⊓ N).map (QuotientGroup.mk' H))) :=
      Work.Fitting.isPiNat_of_dvd hdiv1 (Work.Fitting.isPiNat_of_dvd hdivN hN)
    have hp : Work.Fitting.IsPiNat (fun q => q = p)
        (Nat.card ↥((K ⊓ N).map (QuotientGroup.mk' H))) :=
      Work.Fitting.isPiNat_of_dvd hdiv2 (hcard_map.symm ▸ hpfidx)
    have hone : Nat.card ↥((K ⊓ N).map (QuotientGroup.mk' H)) = 1 := by
      by_contra h
      obtain ⟨q, hq, hdvd⟩ := Nat.exists_prime_and_dvd h
      exact (hp' q hq hdvd) (hp q hq hdvd)
    have hbot : (K ⊓ N).map (QuotientGroup.mk' H) = ⊥ := Subgroup.card_eq_one.mp hone
    have hker := (Subgroup.map_eq_bot_iff (K ⊓ N)).mp hbot
    rwa [QuotientGroup.ker_mk'] at hker
  refine ⟨?_, ?_, hKN⟩
  · -- ### `H.map f`, `K.map f` is a chief factor of `S ⧸ N`.
    set f := QuotientGroup.mk' N with hf
    have hsurj : Function.Surjective f := QuotientGroup.mk'_surjective N
    have hNbot : Subgroup.map f N = ⊥ :=
      (Subgroup.map_eq_bot_iff N).mpr (by rw [hf, QuotientGroup.ker_mk'])
    have hfker : f.ker = N := by rw [hf, QuotientGroup.ker_mk']
    refine ⟨hHn.map f hsurj, hKn.map f hsurj, ?_, ?_⟩
    · refine lt_of_le_of_ne (Subgroup.map_mono hHKle) ?_
      intro heq
      have hKH : K ≤ H := by
        intro k hk
        have hmem : f k ∈ H.map f := by
          rw [heq]; exact ⟨k, hk, rfl⟩
        obtain ⟨h, hh, hfh⟩ := hmem
        have hhK : h ∈ K := hHKle hh
        have hmemN : h⁻¹ * k ∈ N := by
          rw [← hfker, MonoidHom.mem_ker, map_mul, map_inv, hfh, inv_mul_cancel]
        have hmemK : h⁻¹ * k ∈ K := K.mul_mem (K.inv_mem hhK) hk
        have hmemH : h⁻¹ * k ∈ H := hKN ⟨hmemK, hmemN⟩
        have hk_eq : k = h * (h⁻¹ * k) := by group
        rw [hk_eq]; exact H.mul_mem hh hmemH
      exact hlt.ne (le_antisymm hHKle hKH)
    · intro M hMn hHM hMK
      set L := M.comap f with hL
      have hLn : L.Normal := hMn.comap f
      have hNL : N ≤ L := by
        intro x hx
        rw [Subgroup.mem_comap, hf]
        have hx1 : (QuotientGroup.mk' N) x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
        rw [hx1]; exact M.one_mem
      have hHL : H ≤ L := by
        intro x hx
        rw [Subgroup.mem_comap]
        exact hHM ⟨x, hx, rfl⟩
      have hLK : L ≤ K ⊔ N := by
        intro x hx
        have hx' : f x ∈ K.map f := hMK ((Subgroup.mem_comap).mp hx)
        have : x ∈ (K.map f).comap f := hx'
        rwa [Subgroup.comap_map_eq, hfker] at this
      have hMmap : L.map f = M := Subgroup.map_comap_eq_self_of_surjective hsurj M
      have hinf : (L ⊓ K).Normal := @Subgroup.normal_inf_normal S _ L K hLn hKn
      rcases hmin (L ⊓ K) hinf (le_inf hHL hHKle) inf_le_right with hcase | hcase
      · left
        have hLeq : L = H ⊔ N := by
          refine le_antisymm ?_ (sup_le hHL hNL)
          intro x hx
          have hxKN : x ∈ K ⊔ N := hLK hx
          have hx' : x ∈ (K : Set S) * (N : Set S) := by
            rw [← Subgroup.mul_normal K N]; exact hxKN
          obtain ⟨k, hk, n, hn, hkn⟩ := Set.mem_mul.mp hx'
          have hnL : n ∈ L := hNL hn
          have hkL : k ∈ L := by
            have hkx : k = x * n⁻¹ := by rw [← hkn]; group
            rw [hkx]; exact L.mul_mem hx (L.inv_mem hnL)
          have hkH : k ∈ H := by rw [← hcase]; exact ⟨hkL, hk⟩
          rw [← hkn]
          have h1 : k * n ∈ (H : Set S) * (N : Set S) :=
            Set.mem_mul.mpr ⟨k, hkH, n, hn, rfl⟩
          rwa [← Subgroup.mul_normal H N] at h1
        rw [← hMmap, hLeq, Subgroup.map_sup, hNbot, sup_bot_eq]
      · right
        have hKL : K ≤ L := by rw [← hcase]; exact inf_le_left
        have hLeq : L = K ⊔ N := le_antisymm hLK (sup_le hKL hNL)
        rw [← hMmap, hLeq, Subgroup.map_sup, hNbot, sup_bot_eq]
  · -- ### The factor `K.map f / H.map f` still has `p`-power order.
    refine ⟨Subgroup.map_mono hHKle, ?_⟩
    have hrel : ((H.map (QuotientGroup.mk' N)).subgroupOf
        (K.map (QuotientGroup.mk' N))).index = (H.subgroupOf K).index := by
      show (H.map (QuotientGroup.mk' N)).relIndex (K.map (QuotientGroup.mk' N))
        = (H.subgroupOf K).index
      rw [Subgroup.relIndex_map_map, QuotientGroup.ker_mk']
      have hkey := relIndex_sup_eq_of_inf_le hHKle hKN
      simp only [Subgroup.relIndex] at hkey ⊢
      exact hkey
    rw [hrel]; exact hpfidx

end Work.LocalPrelim
