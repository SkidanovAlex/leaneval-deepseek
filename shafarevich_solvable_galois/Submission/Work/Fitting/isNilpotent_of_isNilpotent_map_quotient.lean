import Mathlib.GroupTheory.Frattini
import Mathlib.Order.CompletePartialOrder
import Mathlib.FieldTheory.Normal.Defs

set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false

namespace Work.Fitting

open Subgroup

/-- For a subgroup `X` of `↥H`, the subgroup of `↥H` obtained by first mapping into `G` and
then restricting is `X` again. -/
theorem subgroupOf_map_subtype_eq {G : Type*} [Group G] {H : Subgroup G} (X : Subgroup ↥H) :
    (X.map H.subtype).subgroupOf H = X := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hxy⟩
    have : y = x := Subtype.ext hxy
    simpa [this] using hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- **The Sylow subgroup of `H` together with `M` generates a normal subgroup of `H`.**

If `M ◁ G`, `M ≤ H` and `H/M` is nilpotent, then for every prime `p` and every Sylow
`p`-subgroup `P` of `H` the subgroup `P · M` of `H` is normal in `H`:  indeed `PM/M` is the
unique Sylow `p`-subgroup of the nilpotent group `H/M`. -/
theorem sylow_sup_subgroupOf_normal {G : Type*} [Group G] [Finite G]
    (M H : Subgroup G) [M.Normal] (_hMH : M ≤ H)
    (hnil : Group.IsNilpotent ↥(H.map (QuotientGroup.mk' M)))
    {p : ℕ} [Fact p.Prime] (P : Sylow p ↥H) :
    ((P : Subgroup ↥H) ⊔ M.subgroupOf H).Normal := by
  classical
  let Q : Subgroup (G ⧸ M) := H.map (QuotientGroup.mk' M)
  let ψ : ↥H →* ↥Q :=
    ((QuotientGroup.mk' M).comp H.subtype).codRestrict Q
      (fun x => Subgroup.mem_map_of_mem (QuotientGroup.mk' M) x.2)
  have hψsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨h, hh, heq⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨h, hh⟩, Subtype.ext heq⟩
  have hψker : ψ.ker = M.subgroupOf H := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have hv : QuotientGroup.mk' M ↑x = 1 := by
        have := congrArg Subtype.val hx
        simpa [ψ] using this
      exact (QuotientGroup.eq_one_iff (N := M) ↑x).mp hv
    · intro hx
      apply Subtype.ext
      simp only [ψ, MonoidHom.codRestrict_apply, MonoidHom.comp_apply, Subgroup.coe_one]
      exact (QuotientGroup.eq_one_iff (N := M) ↑x).mpr hx
  haveI hQnil : Group.IsNilpotent ↥Q := hnil
  have hSnorm : ((P : Subgroup ↥H).map ψ).Normal := by
    have hSp : (Sylow.mapSurjective (f := ψ) hψsurj P : Subgroup ↥Q).Normal := inferInstance
    rwa [Sylow.coe_mapSurjective hψsurj] at hSp
  have hmap : ((P : Subgroup ↥H) ⊔ M.subgroupOf H).map ψ = (P : Subgroup ↥H).map ψ := by
    rw [Subgroup.map_sup]
    have hbot : (M.subgroupOf H).map ψ = ⊥ := by
      rw [Subgroup.map_eq_bot_iff]
      rw [hψker]
    rw [hbot, sup_bot_eq]
  have hnormmap : (((P : Subgroup ↥H) ⊔ M.subgroupOf H).map ψ).Normal := by
    rw [hmap]; exact hSnorm
  have hker : ψ.ker ≤ (P : Subgroup ↥H) ⊔ M.subgroupOf H := by
    rw [hψker]; exact le_sup_right
  rw [← Subgroup.comap_map_eq_self hker]
  exact hnormmap.comap ψ

/-- **Frattini/non-generating step.**  Let `M ◁ G` with `M ≤ Φ(G)` and let `K ◁ G` with
`M ≤ K`.  If `P` is a Sylow `p`-subgroup of `K` and `P · M ◁ K`, then the image of `P` in `G`
is normal in `G`. -/
theorem sylow_map_normal_of_le_frattini {G : Type*} [Group G] [Finite G]
    {M K : Subgroup G} [M.Normal] [K.Normal] (hMK : M ≤ K) (hMΦ : M ≤ frattini G)
    {p : ℕ} [Fact p.Prime] (P : Sylow p ↥K)
    (hPM : ((P : Subgroup ↥K) ⊔ M.subgroupOf K).Normal) :
    ((P : Subgroup ↥K).map K.subtype).Normal := by
  classical
  set P' : Subgroup G := (P : Subgroup ↥K).map K.subtype with hP'def
  set N : Subgroup G := Subgroup.normalizer P' with hNdef
  have hP'le : P' ≤ K := by rw [hP'def]; exact Subgroup.map_subtype_le _
  have hP'sub : P'.subgroupOf K = (P : Subgroup ↥K) := by
    rw [hP'def]; exact subgroupOf_map_subtype_eq _
  -- Frattini argument in `G` for the normal subgroup `K`
  have houter : N ⊔ K = ⊤ := by
    rw [hNdef, hP'def]; exact Sylow.normalizer_sup_eq_top P
  -- Frattini argument in `K` for the normal subgroup `P · M`
  haveI : ((P : Subgroup ↥K) ⊔ M.subgroupOf K).Normal := hPM
  have hinner : Subgroup.normalizer (P : Subgroup ↥K) ⊔ ((P : Subgroup ↥K) ⊔ M.subgroupOf K) = ⊤ := by
    have hle : (P : Subgroup ↥K) ≤ (P : Subgroup ↥K) ⊔ M.subgroupOf K := le_sup_left
    have h := Sylow.normalizer_sup_eq_top (P.subtype hle)
    rw [Sylow.coe_subtype, Subgroup.subgroupOf_map_subtype, inf_of_le_left hle] at h
    exact h
  have hinner2 : N.subgroupOf K ⊔ (P' ⊔ M).subgroupOf K = ⊤ := by
    rw [hNdef, Subgroup.subgroupOf_normalizer_eq hP'le, hP'sub]
    rw [Subgroup.subgroupOf_sup hP'le hMK, hP'sub]
    exact hinner
  have htop_sub : (⊤ : Subgroup ↥K).map K.subtype = K := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  -- transport the equality of subgroups of `↥K` back to `G`
  have hkey : (N ⊓ K) ⊔ (P' ⊔ M) = K := by
    have h := congrArg (Subgroup.map K.subtype) hinner2
    rw [Subgroup.map_sup] at h
    rw [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype] at h
    rw [htop_sub] at h
    rw [inf_of_le_left (sup_le hP'le hMK)] at h
    exact h
  have hKG : K ≤ N ⊔ (P' ⊔ M) := by
    rw [← hkey]
    exact sup_le_sup_right inf_le_left (P' ⊔ M)
  have hKM : K ≤ N ⊔ M := by
    calc K ≤ N ⊔ (P' ⊔ M) := hKG
      _ = N ⊔ M := by
            rw [← sup_assoc, hNdef, sup_eq_left.mpr Subgroup.le_normalizer]
  have htop : N ⊔ M = ⊤ := top_le_iff.mp (by
    rw [← houter]
    exact sup_le le_sup_left hKM)
  have hfr : N ⊔ frattini G = ⊤ := top_le_iff.mp (by
    rw [← htop]
    exact sup_le le_sup_left (hMΦ.trans le_sup_right))
  haveI : IsCoatomic (Subgroup G) := inferInstance
  have htop' : N = ⊤ := frattini_nongenerating hfr
  have hfin : P'.Normal := by
    rw [hNdef] at htop'
    exact Subgroup.normalizer_eq_top_iff.mp htop'
  rwa [hP'def] at hfin

/-- **Shafarevich/Fitting lemma.**  If `M ◁ G` lies in the Frattini subgroup `Φ(G)`, if
`H ◁ G` with `M ≤ H`, and if `H/M` is nilpotent, then `H` is nilpotent. -/
theorem isNilpotent_of_isNilpotent_map_quotient {G : Type*} [Group G] [Finite G]
    (M H : Subgroup G) [M.Normal] (hMH : M ≤ H) (hH : H.Normal) (hMΦ : M ≤ frattini G)
    (hnil : Group.IsNilpotent ↥(H.map (QuotientGroup.mk' M))) :
    Group.IsNilpotent ↥H := by
  -- it suffices that every Sylow subgroup of `H` is normal
  have q := (Group.isNilpotent_of_finite_tfae (G := H)).out 1 4
  rw [q]
  intro p hp P
  exact Subgroup.Normal.of_map_subtype
    (sylow_map_normal_of_le_frattini (K := H) hMH hMΦ P
      (sylow_sup_subgroupOf_normal M H hMH hnil P))

end Work.Fitting
