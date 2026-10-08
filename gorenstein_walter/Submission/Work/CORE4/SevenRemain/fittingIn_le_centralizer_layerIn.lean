import Mathlib
import Submission.Work.CORE4.Defs

set_option linter.style.haveILetI false

namespace Work.CORE4.SevenRemain

/-! ## 1. The key group-theoretic fact

A nilpotent normal subgroup commutes with a normal quasisimple subgroup.  Mathlib has no
Fitting/layer theory, so this is proved from scratch here. -/

/-- **Key lemma.**  A nilpotent normal subgroup commutes with a normal quasisimple subgroup:
`N ≤ C_X(E)`, i.e. `⁅E,N⁆ = 1`.

The hypotheses are the two halves of `Work.GW2.IsQuasisimple E` (`⁅E,E⁆ = E` and `E/Z(E)`
simple), separated so that the proof can use them directly. -/
theorem nilpotent_normal_le_centralizer_of_quasisimple {X : Type*} [Group X]
    {E N : Subgroup X} (hEn : E.Normal) (hEE : ⁅E, E⁆ = E)
    (hEsimp : IsSimpleGroup (↥E ⧸ Subgroup.center ↥E))
    (hNn : N.Normal) (hNnil : Group.IsNilpotent N) :
    N ≤ Subgroup.centralizer (E : Set X) := by
  haveI := hEn
  haveI := hNn
  set M : Subgroup X := ⁅E, N⁆ with hMdef
  have hME : M ≤ E := Subgroup.commutator_le_left E N
  have hMN : M ≤ N := Subgroup.commutator_le_right E N
  have hMnor : M.Normal := Subgroup.commutator_normal E N
  haveI := hMnor
  -- `M` viewed inside `E`, and the centre `Z` of `E`
  set Z : Subgroup ↥E := Subgroup.center ↥E with hZdef
  set ME : Subgroup ↥E := M.subgroupOf E with hMEdef
  have hMEnor : ME.Normal := hMnor.subgroupOf E
  haveI := hMEnor
  have hmapnor : (ME.map (QuotientGroup.mk' Z)).Normal :=
    Subgroup.Normal.map hMEnor _ (QuotientGroup.mk'_surjective Z)
  haveI := hmapnor
  -- `E/Z(E)` is simple, so the image of `M` is `⊥` or `⊤`
  rcases hEsimp.eq_bot_or_eq_top_of_normal (ME.map (QuotientGroup.mk' Z)) with hbot | htop
  · -- Case `M ≤ Z(E)`: `M` commutes with `E`, and the three subgroups lemma finishes.
    have hMEleZ : ME ≤ Z := by
      have h := (Subgroup.map_eq_bot_iff ME).mp hbot
      rwa [QuotientGroup.ker_mk' Z] at h
    have hMcent : M ≤ Subgroup.centralizer (E : Set X) := by
      intro m hm
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      have hmE : m ∈ E := hME hm
      have hz : (⟨m, hmE⟩ : ↥E) ∈ ME := hm
      have hzu : (⟨m, hmE⟩ : ↥E) ∈ Z := hMEleZ hz
      have hcomm := Subgroup.mem_center_iff.mp hzu (⟨e, he⟩ : ↥E)
      simpa using congrArg Subtype.val hcomm
    have hMEbot : ⁅M, E⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hMcent
    -- `⁅E,E,N⁆ ≤ ⁅E,N,E⁆ = ⊥`
    have h2 : ⁅⁅N, E⁆, E⁆ = ⊥ := by
      rw [Subgroup.commutator_comm N E]
      exact hMEbot
    have h3 : ⁅⁅E, E⁆, N⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate hMEbot h2
    have hMbot : ⁅E, N⁆ = ⊥ := by
      rw [hEE] at h3
      exact h3
    exact Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hMbot)
  · -- Case `M Z(E) = E`: then `E = M ≤ N` and `E` is perfect, contradicting nilpotency.
    exfalso
    have hsup : ME ⊔ Z = ⊤ := by
      have h := QuotientGroup.comap_map_mk' Z ME
      rw [htop, Subgroup.comap_top] at h
      rw [sup_comm] at h
      exact h.symm
    -- the same equality transported to the ambient group `X`
    have hsupX : M ⊔ Z.map E.subtype = E := by
      have h1 := congrArg (Subgroup.map E.subtype) hsup
      rw [Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype] at h1
      rw [hMEdef, Subgroup.subgroupOf_map_subtype M E, inf_eq_left.mpr hME] at h1
      exact h1
    have hZm_cen : ⁅Z.map E.subtype, E⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      obtain ⟨z', hz', rfl⟩ := hz
      have hcomm := Subgroup.mem_center_iff.mp hz' (⟨e, he⟩ : ↥E)
      simpa using congrArg Subtype.val hcomm
    -- `E = ⁅E,E⁆ ≤ ⁅M Z(E), E⁆ = ⁅M,E⁆ ≤ M`
    have hEEleM : ⁅E, E⁆ ≤ M := by
      have hmono : ⁅E, E⁆ ≤ ⁅M ⊔ Z.map E.subtype, E⁆ :=
        Subgroup.commutator_mono (le_of_eq hsupX.symm) le_rfl
      have hsplit : ⁅M ⊔ Z.map E.subtype, E⁆ = ⁅M, E⁆ ⊔ ⁅Z.map E.subtype, E⁆ :=
        Subgroup.commutator_sup_right M (Z.map E.subtype) E
      have hMEleM : ⁅M, E⁆ ≤ M := Subgroup.commutator_le_left M E
      calc ⁅E, E⁆ ≤ ⁅M ⊔ Z.map E.subtype, E⁆ := hmono
        _ = ⁅M, E⁆ ⊔ ⁅Z.map E.subtype, E⁆ := hsplit
        _ = ⁅M, E⁆ := by rw [hZm_cen, sup_bot_eq]
        _ ≤ M := hMEleM
    have hEM : E ≤ M := le_trans (le_of_eq hEE.symm) hEEleM
    have hEN : E ≤ N := le_trans hEM hMN
    -- `E` is nilpotent (a subgroup of `N`) and perfect (hypothesis) and nontrivial
    haveI : Group.IsNilpotent ↥N := hNnil
    have hEiso : ↥(E.subgroupOf N) ≃* ↥E := Subgroup.subgroupOfEquivOfLe hEN
    haveI : Group.IsNilpotent ↥E := (Group.isNilpotent_congr hEiso).mp inferInstance
    haveI : Nontrivial ↥E := (QuotientGroup.mk'_surjective Z).nontrivial
    haveI : Group.IsPerfect ↥E := Subgroup.isPerfect_iff.mpr hEE
    exact Group.IsPerfect.not_isNilpotent ↥E inferInstance

/-- The same fact for `Work.GW2.IsQuasisimple`. -/
theorem nilpotent_normal_le_centralizer_of_isQuasisimple {X : Type*} [Group X]
    {E N : Subgroup X} (hEn : E.Normal) (hEquasi : Work.GW2.IsQuasisimple E)
    (hNn : N.Normal) (hNnil : Group.IsNilpotent N) :
    N ≤ Subgroup.centralizer (E : Set X) :=
  nilpotent_normal_le_centralizer_of_quasisimple hEn hEquasi.1 hEquasi.2 hNn hNnil

/-! ## 2. `E(A)` centralizes `F(A)` -/

/-- **`[E(A), F(A)] = 1`.**  Every element of the layer commutes with every element of the
Fitting subgroup.

`layer A` is the join of the normal quasisimple subgroups `E`, and it suffices for each such
`E` to show that `fitting A ≤ C(E)`: `fitting A` is (the normal core of) the join of the
normal nilpotent subgroups `N`, and each `N ≤ C(E)` by the key lemma. -/
theorem layer_le_centralizer_fitting {X : Type*} [Group X] (A : Subgroup X) :
    Work.GW2.layer A ≤ Subgroup.centralizer (Work.GW2.fitting A : Set ↥A) := by
  refine sSup_le ?_
  intro E hE
  obtain ⟨hEn, hEquasi⟩ := hE
  rw [Subgroup.le_centralizer_iff]
  refine le_trans (Subgroup.normalCore_le _) ?_
  refine sSup_le ?_
  intro N hN
  obtain ⟨hNn, hNnil⟩ := hN
  exact nilpotent_normal_le_centralizer_of_isQuasisimple hEn hEquasi hNn hNnil

/-- Transport of a containment into a centralizer along a monoid homomorphism. -/
theorem map_le_centralizer_map {X Y : Type*} [Group X] [Group Y] (f : X →* Y) {H K : Subgroup X}
    (h : H ≤ Subgroup.centralizer (K : Set X)) :
    H.map f ≤ Subgroup.centralizer ((K.map f : Subgroup Y) : Set Y) := by
  rintro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  obtain ⟨a, ha, rfl⟩ := hy
  rw [Subgroup.coe_map] at hz
  obtain ⟨b, hb, rfl⟩ := hz
  rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp (h ha) b hb]

/-- **`[F(A), E(A)] = 1`**: every element of the Fitting subgroup `Work.GW2.fittingIn A` of a
subgroup `A ≤ G` centralizes the layer `Work.GW2.layerIn A` (the join of the normal quasisimple
subgroups, `Work.GW2.layer`).

Standard proof: for a normal quasisimple `E` and a normal nilpotent `N` one shows `N ≤ C(E)`
(the commutator `⁅E,N⁆` is normal in `E` and lies in `E ⊓ N`; modulo `Z(E)` it is `⊥` or `⊤`; in
the second case `E = ⁅E,E⁆ ≤ ⁅E N, E N⁆ ≤ ⁅E,N⁆ ≤ N` makes the nontrivial perfect group `E`
nilpotent, impossible), and then one takes the two `sSup`s in the definitions of `layer` and
`fitting` apart and transports along `A.subtype`.

A copy of exactly this argument, in the symmetric form
`Work.BMAX.LayerCentralizesFitting : layerIn A ≤ centralizer (fittingIn A)`
(equivalently the statement below, `centralizer` being symmetric), lives in
`Submission/Work/BMAX/LayerCentralizesFitting.lean`.  That module CANNOT be imported from a
CORE4 module: it (via `Submission.Work.ASM.Defs`) and `Submission.Work.CORE4.Defs` both declare
`Work.GW2.fittingIn`, `Work.GW2.layerIn`, … so importing both is a hard error.  Port its proof
into the new module instead (`Work.GW2.IsQuasisimple`, `Work.GW2.layer`, `Work.GW2.fitting` are
available from `Submission.Work.CORE4.Defs`). -/
theorem fittingIn_le_centralizer_layerIn {G : Type} [Group G] [Finite G] (A : Subgroup G) :
    Work.GW2.fittingIn A ≤ Subgroup.centralizer (Work.GW2.layerIn A : Set G) := by
  have h : Work.GW2.layerIn A ≤ Subgroup.centralizer (Work.GW2.fittingIn A : Set G) := by
    rw [Work.GW2.layerIn, Work.GW2.fittingIn]
    exact map_le_centralizer_map A.subtype (layer_le_centralizer_fitting A)
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (Subgroup.mem_centralizer_iff.mp (h hy) x hx).symm

end Work.CORE4.SevenRemain
