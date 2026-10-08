/-
# Two distinct mutually normalizing quasisimple subgroups commute

This file proves

* `Work.BMAX.commutator_eq_bot_of_isQuasisimple_of_isQuasisimple` :
  if `Q, P ≤ G` are quasisimple (`⁅E,E⁆ = E` and `E/Z(E)` simple, Bender's convention),
  each normalizes the other (`Q ≤ N(P)`, `P ≤ N(Q)`), and `Q ≠ P`, then `⁅Q, P⁆ = ⊥`.

## Mathematics

The argument is the standard "components commute" computation.  Put `M = ⁅Q,P⁆` and
`H = Q ⊔ P`.  Since `Q` and `P` normalize each other they are both normal in `H`, hence
`M ◁ H` and `M ≤ Q ⊓ P`.  Write `Z(E)` for the centre of `E`.

*`M` is central in `Q`, or else `Q = M·Z(Q)`.*  `M ◁ Q`, so its image in the simple group
`Q/Z(Q)` is `⊥` or `⊤`.  The second possibility gives
`Q = ⁅Q,Q⁆ ≤ ⁅M·Z(Q), M·Z(Q)⁆ ≤ M ≤ P` (using `⁅M,Q⁆ ≤ M` and `⁅Z(Q),Z(Q)⁆ = 1`),
i.e. `Q ≤ P`; then `Q ◁ P` and the same dichotomy for `P/Z(P)` forces `P = Q`, against
`hne`.  Symmetrically `M ≤ Z(P)` or `P = Q`, so in fact `M` centralizes `Q` and `P`.

*`M = ⁅⁅Q,Q⁆,P⁆ ≤ ⁅⁅Q,P⁆,Q⁆⁅⁅P,Q⁆,Q⁆ = ⁅M,Q⁆⁅M,Q⁆ = 1`* (the Three Subgroups Lemma /
Hall–Witt identity, `Subgroup.commutator_commutator_eq_bot_of_rotate`), and `⁅Q,Q⁆ = Q`
because `Q` is perfect.  Hence `M = 1`.

## Formalisation

The dichotomy "the image of `M` in `E/Z(E)` is `⊥` or `⊤`" is packaged as
`Work.BMAX.QuasiComm.le_centralizer_or_le_of_isQuasisimple`: for a *normal* subgroup `M` of a
quasisimple `E` normal in `X` it produces `M ≤ C(E)` or `E ≤ M`.  The passage from `Q,P ≤ G`
to the normal situation takes place inside the subgroup `H = Q ⊔ P`, using the transport of
`IsQuasisimple` to `subgroupOf` and `Subgroup.map_commutator`.
-/
import Mathlib
import Submission.Work.BMAX.Defs

set_option linter.style.haveILetI false

namespace Work.BMAX

open Subgroup

namespace QuasiComm

variable {X : Type*} [Group X]

/-- A quasisimple subgroup is nontrivial: `E/Z(E)` is simple, so it has at least two elements,
and hence so does `E`. -/
lemma isQuasisimple_ne_bot {E : Subgroup X} (h : Work.GW2.IsQuasisimple E) : E ≠ ⊥ := by
  haveI := h.2
  haveI : Nontrivial ↥E := (QuotientGroup.mk'_surjective (Subgroup.center ↥E)).nontrivial
  exact (Subgroup.nontrivial_iff_ne_bot E).mp inferInstance

/-- If `M ≤ K` and `M`, viewed as a subgroup of `↥K`, lies in the centre of `↥K`, then `M`
centralizes `K` in the ambient group. -/
lemma le_centralizer_of_le_of_subgroupOf_le_center {M K : Subgroup X} (hMK : M ≤ K)
    (h : M.subgroupOf K ≤ Subgroup.center ↥K) : M ≤ Subgroup.centralizer (K : Set X) := by
  intro m hm
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have hz : (⟨m, hMK hm⟩ : ↥K) ∈ Subgroup.center ↥K := h hm
  have hcomm := Subgroup.mem_center_iff.mp hz (⟨k, hk⟩ : ↥K)
  simpa using congrArg Subtype.val hcomm

/-- **The dichotomy.**  Let `M ◁ X` be a normal subgroup contained in a quasisimple
subgroup `E ◁ X`.  Then either `M` is central in `E`, or `E ≤ M` (which happens precisely when
`E = M·Z(E)`).

The subgroup `M.subgroupOf E` is normal in `↥E`, so its image in the simple group `E/Z(E)` is
`⊥` or `⊤`.  In the first case `M ≤ Z(E)`.  In the second case
`M ⊔ Z(E) = E` and `⁅Z(E), E⁆ = ⊥`, so `E = ⁅E,E⁆ ≤ ⁅M,E⁆ ≤ M`. -/
lemma le_centralizer_or_le_of_isQuasisimple {M E : Subgroup X} (hMn : M.Normal) (hME : M ≤ E)
    (hEn : E.Normal) (hE : Work.GW2.IsQuasisimple E) :
    M ≤ Subgroup.centralizer (E : Set X) ∨ E ≤ M := by
  haveI := hMn
  haveI := hEn
  set Z : Subgroup ↥E := Subgroup.center ↥E with hZdef
  set ME : Subgroup ↥E := M.subgroupOf E with hMEdef
  have hMEnor : ME.Normal := hMn.subgroupOf E
  haveI := hMEnor
  haveI := hE.2
  have hmapnor : (ME.map (QuotientGroup.mk' Z)).Normal :=
    Subgroup.Normal.map hMEnor _ (QuotientGroup.mk'_surjective Z)
  haveI := hmapnor
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (ME.map (QuotientGroup.mk' Z)) with hbot | htop
  · left
    have hMEleZ : ME ≤ Z := by
      have h := (Subgroup.map_eq_bot_iff ME).mp hbot
      rwa [QuotientGroup.ker_mk' Z] at h
    exact le_centralizer_of_le_of_subgroupOf_le_center hME hMEleZ
  · right
    -- `E = M ⊔ Z(E)` in `↥E`, hence in `X`
    have hsup : ME ⊔ Z = ⊤ := by
      have h := QuotientGroup.comap_map_mk' Z ME
      rw [htop, Subgroup.comap_top] at h
      rw [sup_comm] at h
      exact h.symm
    have hsupX : M ⊔ Z.map E.subtype = E := by
      have h1 := congrArg (Subgroup.map E.subtype) hsup
      rw [Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype] at h1
      rw [hMEdef, Subgroup.subgroupOf_map_subtype M E, inf_eq_left.mpr hME] at h1
      exact h1
    -- `Z(E)` commutes with `E`
    have hZcen : ⁅Z.map E.subtype, E⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      obtain ⟨z', hz', rfl⟩ := hz
      have hcomm := Subgroup.mem_center_iff.mp hz' (⟨e, he⟩ : ↥E)
      simpa using congrArg Subtype.val hcomm
    have hEEleM : ⁅E, E⁆ ≤ M := by
      have hmono : ⁅E, E⁆ ≤ ⁅M ⊔ Z.map E.subtype, E⁆ :=
        Subgroup.commutator_mono (le_of_eq hsupX.symm) le_rfl
      have hsplit : ⁅M ⊔ Z.map E.subtype, E⁆ = ⁅M, E⁆ ⊔ ⁅Z.map E.subtype, E⁆ :=
        Subgroup.commutator_sup_right M (Z.map E.subtype) E
      have hMEleM : ⁅M, E⁆ ≤ M := Subgroup.commutator_le_left M E
      calc ⁅E, E⁆ ≤ ⁅M ⊔ Z.map E.subtype, E⁆ := hmono
        _ = ⁅M, E⁆ ⊔ ⁅Z.map E.subtype, E⁆ := hsplit
        _ = ⁅M, E⁆ := by rw [hZcen, sup_bot_eq]
        _ ≤ M := hMEleM
    rw [hE.1] at hEEleM
    exact hEEleM

/-- `IsQuasisimple` passes to the subgroup-of-the-generator version: if `E ≤ H` and `E` is
quasisimple then `E.subgroupOf H` is quasisimple in `↥H`. -/
lemma isQuasisimple_subgroupOf {E H : Subgroup X} (hEH : E ≤ H)
    (hE : Work.GW2.IsQuasisimple E) : Work.GW2.IsQuasisimple (E.subgroupOf H) := by
  obtain ⟨h1, h2⟩ := hE
  haveI := h2
  refine ⟨?_, ?_⟩
  · apply Subgroup.map_injective (f := H.subtype) H.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hEH]
    exact h1
  · have hcen : Subgroup.map (Subgroup.subgroupOfEquivOfLe hEH : ↥(E.subgroupOf H) →* ↥E)
        (Subgroup.center ↥(E.subgroupOf H)) = Subgroup.center ↥E :=
      Subgroup.map_center_eq (Subgroup.subgroupOfEquivOfLe hEH)
    exact MulEquiv.isSimpleGroup
      (QuotientGroup.congr (Subgroup.center ↥(E.subgroupOf H)) (Subgroup.center ↥E)
        (Subgroup.subgroupOfEquivOfLe hEH) hcen)

/-- Two normal quasisimple subgroups, one contained in the other, are equal. -/
lemma eq_of_le_of_isQuasisimple {E F : Subgroup X} (hEn : E.Normal) (hFn : F.Normal)
    (hEq : Work.GW2.IsQuasisimple E) (hFq : Work.GW2.IsQuasisimple F) (hEF : E ≤ F) : E = F := by
  rcases le_centralizer_or_le_of_isQuasisimple hEn hEF hFn hFq with hcen | hFE
  · -- `E` centralizes `F`, hence `E = ⁅E,E⁆ ≤ ⁅E,F⁆ = ⊥`, contradicting `E ≠ ⊥`
    exfalso
    have hbot : ⁅E, F⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcen
    have h2 : ⁅E, E⁆ ≤ ⁅E, F⁆ := Subgroup.commutator_mono le_rfl hEF
    rw [hbot] at h2
    have hEbot : E = ⊥ := by rw [← hEq.1]; exact le_bot_iff.mp h2
    exact isQuasisimple_ne_bot hEq hEbot
  · exact le_antisymm hEF hFE

/-- **Two distinct normal quasisimple subgroups commute** (the "components commute" lemma,
in the form where both subgroups are normal in the ambient group). -/
theorem commutator_eq_bot_of_normal_isQuasisimple {E F : Subgroup X} (hEn : E.Normal)
    (hFn : F.Normal) (hEq : Work.GW2.IsQuasisimple E) (hFq : Work.GW2.IsQuasisimple F)
    (hne : E ≠ F) : ⁅E, F⁆ = ⊥ := by
  haveI := hEn
  haveI := hFn
  have hME : ⁅E, F⁆ ≤ E := Subgroup.commutator_le_left E F
  have hMF : ⁅E, F⁆ ≤ F := Subgroup.commutator_le_right E F
  have hMn : (⁅E, F⁆).Normal := Subgroup.commutator_normal E F
  rcases le_centralizer_or_le_of_isQuasisimple hMn hME hEn hEq with hcenE | hEM
  · rcases le_centralizer_or_le_of_isQuasisimple hMn hMF hFn hFq with hcenF | hFM
    · -- `⁅E,F⁆` centralizes `E`: the Three Subgroups Lemma with `E = ⁅E,E⁆` finishes.
      have h1 : ⁅⁅E, F⁆, E⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcenE
      have h2 : ⁅⁅F, E⁆, E⁆ = ⊥ := by rw [Subgroup.commutator_comm F E]; exact h1
      have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := E) (H₂ := E) (H₃ := F)
        h1 h2
      rw [hEq.1] at h3
      exact h3
    · exact absurd (eq_of_le_of_isQuasisimple hFn hEn hFq hEq (le_trans hFM hME)).symm hne
  · exact absurd (eq_of_le_of_isQuasisimple hEn hFn hEq hFq (le_trans hEM hMF)) hne

end QuasiComm

/-- **Two distinct mutually normalizing quasisimple subgroups of a group commute.**

Reduce to the normal situation inside `H = Q ⊔ P`: there both `Q` and `P` are normal (their
mutual normalization is exactly the hypothesis that `H` lies in both normalizers), and
`⁅Q,P⁆ = ⊥` inside `↥H` transports back along `H.subtype`. -/
theorem commutator_eq_bot_of_isQuasisimple_of_isQuasisimple {G : Type*} [Group G]
    {Q P : Subgroup G} (hQ : Work.GW2.IsQuasisimple Q) (hP : Work.GW2.IsQuasisimple P)
    (hQP : Q ≤ Subgroup.normalizer (P : Set G)) (hPQ : P ≤ Subgroup.normalizer (Q : Set G))
    (hne : Q ≠ P) : ⁅Q, P⁆ = ⊥ := by
  have hQH : Q ≤ Q ⊔ P := le_sup_left
  have hPH : P ≤ Q ⊔ P := le_sup_right
  have hQn : (Q.subgroupOf (Q ⊔ P)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQH).mpr (sup_le Subgroup.le_normalizer hPQ)
  have hPn : (P.subgroupOf (Q ⊔ P)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPH).mpr (sup_le hQP Subgroup.le_normalizer)
  have hQq : Work.GW2.IsQuasisimple (Q.subgroupOf (Q ⊔ P)) :=
    QuasiComm.isQuasisimple_subgroupOf hQH hQ
  have hPq : Work.GW2.IsQuasisimple (P.subgroupOf (Q ⊔ P)) :=
    QuasiComm.isQuasisimple_subgroupOf hPH hP
  have hne' : (Q.subgroupOf (Q ⊔ P)) ≠ (P.subgroupOf (Q ⊔ P)) := by
    intro h
    refine hne ?_
    have h1 := congrArg (Subgroup.map (Q ⊔ P).subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hQH, Subgroup.map_subgroupOf_eq_of_le hPH] at h1
  have hmain := QuasiComm.commutator_eq_bot_of_normal_isQuasisimple hQn hPn hQq hPq hne'
  have h2 := congrArg (Subgroup.map (Q ⊔ P).subtype) hmain
  rw [Subgroup.map_bot, Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hQH,
    Subgroup.map_subgroupOf_eq_of_le hPH] at h2
  exact h2

end Work.BMAX
