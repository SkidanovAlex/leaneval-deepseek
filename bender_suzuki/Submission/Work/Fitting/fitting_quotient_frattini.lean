import Mathlib
import Submission.Work.Fitting.Defs
import Submission.Work.Fitting.fitting_eq_iSup_pCore
import Submission.Work.Fitting.frattini_le_fitting

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

noncomputable section

open Classical

namespace Work.Fitting

/-- A surjective image of a nilpotent group is nilpotent. -/
theorem isNilpotent_map_of_surjective {G H : Type*} [Group G] [Group H] {N : Subgroup G}
    [Group.IsNilpotent ↥N] (f : G →* H) (hf : Function.Surjective f) :
    Group.IsNilpotent ↥(N.map f) := by
  have hker : (f.comp N.subtype).range = N.map f := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have h := Group.nilpotent_of_surjective (f.comp N.subtype).rangeRestrict
    (MonoidHom.rangeRestrict_surjective _)
  rwa [hker] at h

/-- Every Sylow subgroup of `M` is normal in `M`, when `M ⊴ G` contains `Φ(G)` and
`M / Φ(G)` is nilpotent. -/
theorem sylow_normal_of_isNilpotent_quotient_frattini (G : Type*) [Group G] [Finite G]
    (M : Subgroup G) [hM : M.Normal] (hle : frattini G ≤ M)
    (hnil : Group.IsNilpotent ↥(M.map (QuotientGroup.mk' (frattini G))))
    {p : ℕ} [Fact p.Prime] (P : Sylow p ↥M) : (↑P : Subgroup ↥M).Normal := by
  haveI : Group.IsNilpotent ↥(M.map (QuotientGroup.mk' (frattini G))) := hnil
  let f := QuotientGroup.mk' (frattini G)
  have hfsurj : Function.Surjective f := QuotientGroup.mk'_surjective _
  let PG : Subgroup G := (↑P : Subgroup ↥M).map M.subtype
  have hPG_le : PG ≤ M := Subgroup.map_subtype_le _
  let A : Subgroup G := PG ⊔ frattini G
  have hA_le : A ≤ M := sup_le hPG_le hle
  let gM : ↥M →* ↥(M.map f) :=
    MonoidHom.codRestrict (f.comp M.subtype) (M.map f) (fun x =>
      Subgroup.mem_map_of_mem f x.2)
  have hgM : Function.Surjective gM := by
    rintro ⟨y, hy⟩
    rw [Subgroup.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  let Pbar : Sylow p ↥(M.map f) := Sylow.mapSurjective hgM P
  have hPbar_char : (↑Pbar : Subgroup ↥(M.map f)).Characteristic :=
    Sylow.characteristic_of_normal Pbar (inferInstance)
  have hchar_map : (((↑Pbar : Subgroup ↥(M.map f)).map (M.map f).subtype)).Normal :=
    map_characteristic_normal (inferInstance : (M.map f).Normal) hPbar_char
  have hcompl : (((↑Pbar : Subgroup ↥(M.map f)).map (M.map f).subtype)).comap f = A := by
    have e1 : (↑Pbar : Subgroup ↥(M.map f)) = (↑P : Subgroup ↥M).map gM :=
      Sylow.coe_mapSurjective hgM P
    have hcomp : (M.map f).subtype.comp gM = f.comp M.subtype := by ext x; rfl
    rw [e1, Subgroup.map_map, hcomp, ← Subgroup.map_map, Subgroup.comap_map_eq,
      QuotientGroup.ker_mk']
  have hA_normal : A.Normal := by
    rw [← hcompl]
    exact Subgroup.Normal.comap hchar_map f
  have hMbar_normal : (M.map f).Normal := hM.map f hfsurj
  have hPleA : (↑P : Subgroup ↥M) ≤ A.subgroupOf M := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_sup_left (Subgroup.mem_map_of_mem M.subtype hx)
  haveI : A.Normal := hA_normal
  have hfrM : Subgroup.normalizer (↑P : Set ↥M) ⊔ A.subgroupOf M = ⊤ :=
    Sylow.normalizer_sup_eq_top' P hPleA
  have hmapM : Subgroup.map M.subtype (Subgroup.normalizer (↑P : Set ↥M)) ⊔ A = M := by
    have h := congrArg (Subgroup.map M.subtype) hfrM
    rw [Subgroup.map_sup] at h
    rw [Subgroup.map_subgroupOf_eq_of_le hA_le] at h
    rw [Subgroup.map_top, Subgroup.range_subtype] at h
    exact h
  have hM_le : M ≤ Subgroup.normalizer (PG : Set G) ⊔ frattini G := by
    have h1 : Subgroup.map M.subtype (Subgroup.normalizer (↑P : Set ↥M)) ≤
        Subgroup.normalizer (PG : Set G) := by
      exact Subgroup.le_normalizer_map (H := (↑P : Subgroup ↥M)) M.subtype
    calc M = Subgroup.map M.subtype (Subgroup.normalizer (↑P : Set ↥M)) ⊔ A := hmapM.symm
      _ ≤ Subgroup.normalizer (PG : Set G) ⊔ frattini G :=
            sup_le (h1.trans le_sup_left)
              (show A ≤ Subgroup.normalizer (PG : Set G) ⊔ frattini G from
                sup_le (Subgroup.le_normalizer.trans le_sup_left) le_sup_right)
  have hfrG : Subgroup.normalizer (PG : Set G) ⊔ M = ⊤ := by
    exact Sylow.normalizer_sup_eq_top P
  have htop : Subgroup.normalizer (PG : Set G) ⊔ frattini G = ⊤ := by
    apply le_antisymm le_top
    rw [← hfrG]
    exact sup_le le_sup_left hM_le
  have hPGnorm : PG.Normal :=
    Subgroup.normalizer_eq_top_iff.mp (frattini_nongenerating htop)
  exact Subgroup.Normal.of_map_subtype hPGnorm

/-- **Key lemma.** If `M ⊴ G` contains `Φ(G)` and `M/Φ(G)` is nilpotent, then `M` is nilpotent. -/
theorem isNilpotent_of_isNilpotent_quotient_frattini (G : Type*) [Group G] [Finite G]
    (M : Subgroup G) [hM : M.Normal] (hle : frattini G ≤ M)
    (hnil : Group.IsNilpotent ↥(M.map (QuotientGroup.mk' (frattini G)))) :
    Group.IsNilpotent ↥M := by
  rw [(Group.isNilpotent_of_finite_tfae (G := ↥M)).out 1 4 rfl rfl]
  intro p hp P
  haveI := hp
  exact sylow_normal_of_isNilpotent_quotient_frattini G M hle hnil P

theorem fitting_quotient_frattini (G : Type*) [Group G] [Finite G] :
    Work.Fitting.fitting (G ⧸ frattini G) =
      (Work.Fitting.fitting G).map (QuotientGroup.mk' (frattini G)) := by
  refine le_antisymm ?_ ?_
  · rw [fitting]
    apply sSup_le
    intro L hL
    rw [mem_fittingSet] at hL
    obtain ⟨hLnorm, hLnil⟩ := hL
    let f := QuotientGroup.mk' (frattini G)
    have hfsurj : Function.Surjective f := QuotientGroup.mk'_surjective _
    let M : Subgroup G := L.comap f
    have hMnorm : M.Normal := hLnorm.comap f
    haveI : M.Normal := hMnorm
    have hMle : frattini G ≤ M := by
      intro x hx
      rw [Subgroup.mem_comap]
      have h1 : f x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
      rw [h1]
      exact L.one_mem
    have hMmap : M.map f = L := Subgroup.map_comap_eq_self_of_surjective hfsurj L
    have hMnil : Group.IsNilpotent ↥M :=
      isNilpotent_of_isNilpotent_quotient_frattini G M hMle (by rw [hMmap]; exact hLnil)
    have hMlefit : M ≤ fitting G := le_fitting hMnorm hMnil
    calc L = M.map f := hMmap.symm
      _ ≤ (fitting G).map f := Subgroup.map_mono hMlefit
  · rw [fitting, map_sSup]
    apply sSup_le
    rintro N ⟨N₀, hN₀, rfl⟩
    rw [mem_fittingSet] at hN₀
    haveI := hN₀.2
    exact le_sSup ⟨hN₀.1.map _ (QuotientGroup.mk'_surjective _),
      isNilpotent_map_of_surjective _ (QuotientGroup.mk'_surjective _)⟩

end Work.Fitting
