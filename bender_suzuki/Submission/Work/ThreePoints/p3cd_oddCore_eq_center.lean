import Mathlib
import Submission.Work.ThreePoints.P3Sub.Basic
import Submission.Work.ThreePoints.Basic
import Submission.Work.ThreePoints.Omega
import Submission.Work.ThreePoints.involutions_conj_of_stronglyEmbedded
import Submission.Work.ThreePoints.oddCore_le_of_stronglyEmbedded
import Submission.Work.BrauerSuzuki.OddCore.le_of_normal_odd
import Submission.Work.BrauerSuzuki.OddCore.oddCard_oddCore

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `O_{2'}(F) = Z(F)` for the `F` of Ch. II §4 Prop. 3 (c)

Peterfalvi I, Ch. II §4, Proposition 3 (c), first half: for `X ≠ 1`, `X ≤ V = C_D(t)` (with
`D = H ∩ H^t`, `H` strongly embedded, `t ∉ H` an involution) and `F = O^{2'}(C_G(X))`,
one has `O_{2'}(F) = Z(F)`.

The file proves the requested lemma from the exact hypotheses supplied by the caller: the
subgroups `F ⊓ M` (`M` a conjugate of `H` containing `X`) are strongly embedded in `F`
(`hSE`), `F = ⟨Inv F⟩` (`hgen`), and `F/O_{2'}(F)` is simple (`hBC`).  Only `hSE`, `hgen` and
Theorem C (`hC`) are used, together with two elementary group-theoretic facts:

* a finite group with a strongly embedded subgroup has **odd-order center**
  (`odd_card_center_of_isStronglyEmbedded`): every central element lies in every strongly
  embedded subgroup, so a central involution would lie in `K ⊓ K^g` for every `g`, forcing
  `|K ⊓ K^g|` to be even, contradicting strong embeddedness.  Since the center is normal,
  `Z(F) ≤ O_{2'}(F)`.
* conversely, `O_{2'}(F) ≤ Z(F)`: pick `f ∈ F ∖ H` (possible because `F ⊓ H` is strongly
  embedded in `F`, so proper), so that `H` and `H^f` are two conjugates containing `X`; then
  both contain `O_{2'}(F)` (`oddCore_le_of_stronglyEmbedded`).  For an involution `v ∈ F ⊓ H`
  (which exists since `F ⊓ H` has even order) and any `o ∈ O_{2'}(F)`, Theorem C applied to
  `(H, f, v, O_{2'}(F))` says `v` centralises `o`; since all involutions of `F` are conjugate in
  `F` (`involutions_conj_of_stronglyEmbedded`) and `O_{2'}(F)` is normal in `F`, every
  involution of `F` centralises `o`, and `F = ⟨Inv F⟩` gives `o ∈ Z(F)`.
-/

namespace Work.ThreePoints

open LeanEval.GroupTheory.Defs

/-! ## Elementary facts used in the proof -/

/-- A finite group with a strongly embedded subgroup has odd-order center.

Every central element lies in every strongly embedded subgroup: if `z ∈ Z(F)` and `z ∉ K`, then
conjugation by `z` is the identity, so `K ⊓ K^z = K` has even order, contradicting the oddness
required by strong embeddedness.  Hence a central involution `z` would lie in `K ⊓ K^g` for every
`g`; taking `g ∉ K` makes `|K ⊓ K^g|` even, again a contradiction. -/
theorem odd_card_center_of_isStronglyEmbedded {F : Type} [Group F] [Finite F] {K : Subgroup F}
    (hK : IsStronglyEmbedded K) : Odd (Nat.card (Subgroup.center F)) := by
  have hcle : Subgroup.center F ≤ K := by
    intro z hz
    by_contra hzK
    have hodd := hK.2.2 z hzK
    have hmap : K.map (MulAut.conj z).toMonoidHom = K :=
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp
        ((Subgroup.center_le_normalizer (K : Set F)) hz))
    rw [hmap, inf_idem] at hodd
    exact absurd hK.2.1 (Nat.not_even_iff_odd.mpr hodd)
  rw [← Nat.not_even_iff_odd]
  intro heven
  haveI : Fintype ↥(Subgroup.center F) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card] at heven
  obtain ⟨z0, hz0⟩ := exists_prime_orderOf_dvd_card 2 (even_iff_two_dvd.mp heven)
  have hzc : (z0 : F) ∈ Subgroup.center F := z0.2
  have hz2 : orderOf (z0 : F) = 2 := by
    have := Subgroup.orderOf_coe z0
    rw [← this] at hz0
    exact hz0
  obtain ⟨g, hgK⟩ : ∃ g : F, g ∉ K := by
    by_contra h; push Not at h
    exact hK.1 ((Subgroup.eq_top_iff' K).mpr h)
  have hodd' := hK.2.2 g hgK
  have hgz : (z0 : F) ∈ K.map (MulAut.conj g).toMonoidHom := by
    refine Subgroup.mem_map.mpr ⟨(z0 : F), hcle hzc, ?_⟩
    show (MulAut.conj g) (z0 : F) = (z0 : F)
    rw [MulAut.conj_apply]
    rw [Subgroup.mem_center_iff.mp hzc g]
    group
  have hzmem : (z0 : F) ∈ K ⊓ K.map (MulAut.conj g).toMonoidHom := ⟨hcle hzc, hgz⟩
  have hdvd : 2 ∣ Nat.card ↥(K ⊓ K.map (MulAut.conj g).toMonoidHom) := by
    have h1 := orderOf_dvd_natCard
      (⟨(z0 : F), hzmem⟩ : ↥(K ⊓ K.map (MulAut.conj g).toMonoidHom))
    rw [← Subgroup.orderOf_coe] at h1
    simpa [hz2] using h1
  exact (Nat.not_even_iff_odd.mpr hodd') (even_iff_two_dvd.mpr hdvd)

/-- A normal subgroup `O ⊴ K` of a subgroup `K ≤ G` is normalised by every element of `K`,
viewed in `G`: the image of `O` in `G` is invariant under conjugation by `v ∈ K`. -/
theorem mem_normalizer_map_subtype {G : Type} [Group G] {K : Subgroup G} {O : Subgroup ↥K}
    (hO : O.Normal) (v : ↥K) :
    (v : G) ∈ Subgroup.normalizer ((O.map K.subtype : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hcomp : (↑(MulAut.conj (v : G)) : G →* G).comp K.subtype
      = K.subtype.comp (↑(MulAut.conj (G := ↥K) v) : ↥K →* ↥K) := by
    ext x
    simp [MulAut.conj_apply]
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, Subgroup.Normal.map_conj_eq]

/-- If `O ⊴ F` and `O` centralises `v`, then `O` centralises every conjugate of `v`. -/
theorem le_centralizer_of_isConj {F : Type} [Group F] {O : Subgroup F} (hO : O.Normal) {v w : F}
    (hvw : IsConj v w) (hcv : O ≤ Subgroup.centralizer ({v} : Set F)) :
    O ≤ Subgroup.centralizer ({w} : Set F) := by
  rw [isConj_iff] at hvw
  obtain ⟨c, hc⟩ := hvw
  intro o ho
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  have hco : c⁻¹ * o * c ∈ O := by simpa using hO.conj_mem o ho c⁻¹
  have h1 := hcv hco
  rw [Subgroup.mem_centralizer_iff] at h1
  have h1' := h1 v (Set.mem_singleton v)
  rw [← hc]
  calc c * v * c⁻¹ * o = c * (v * (c⁻¹ * o * c)) * c⁻¹ := by group
    _ = c * ((c⁻¹ * o * c) * v) * c⁻¹ := by rw [h1']
    _ = o * (c * v * c⁻¹) := by group

/-! ## The target lemma -/

theorem p3cd_oddCore_eq_center {G : Type} [Group G] [Finite G]
    (hC : Submission.Blueprint.ThmCProp) (hS : Submission.Blueprint.Situation G)
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {t : G}
    (ht : orderOf t = 2) (htH : t ∉ H) (X : Subgroup G) (hX0 : X ≠ ⊥)
    (hX : X ≤ Submission.Blueprint.centD H t)
    (hfour : Submission.Blueprint.HasFourGroup ↥(Work.ThreePoints.p3F X))
    (hSE : ∀ M : Subgroup G, X ≤ M → (∃ g : G, M = Submission.Blueprint.conj g H) →
      LeanEval.GroupTheory.Defs.IsStronglyEmbedded
        ((Work.ThreePoints.p3F X ⊓ M).subgroupOf (Work.ThreePoints.p3F X)))
    (htrans : ∀ g : G, X ≤ Submission.Blueprint.conj g H →
      ∃ f ∈ Work.ThreePoints.p3F X, Submission.Blueprint.conj g H = Submission.Blueprint.conj f H)
    (hgen : Subgroup.closure
      (Submission.Blueprint.involutions ((⊤ : Subgroup ↥(Work.ThreePoints.p3F X)) : Set ↥(Work.ThreePoints.p3F X))) = ⊤)
    (hBC : ∃ (Y : Type) (_ : Group Y) (φ : ↥(Work.ThreePoints.p3F X) →* Y), Function.Surjective φ ∧
      φ.ker = Submission.Blueprint.oddCore ↥(Work.ThreePoints.p3F X) ∧ IsSimpleGroup Y) :
    Submission.Blueprint.oddCore ↥(Work.ThreePoints.p3F X) =
      Subgroup.center ↥(Work.ThreePoints.p3F X) := by
  -- `X ≤ H`
  have hXH : X ≤ H := le_trans (le_trans hX inf_le_left) inf_le_left
  -- `F ⊓ H` is strongly embedded in `F = ↥(p3F X)`
  have hK : IsStronglyEmbedded
      ((Work.ThreePoints.p3F X ⊓ H).subgroupOf (Work.ThreePoints.p3F X)) :=
    hSE H hXH ⟨1, by simp⟩
  refine le_antisymm ?_ ?_
  · -- `O_{2'}(F) ≤ Z(F)`
    -- an element of `F` outside `H`
    obtain ⟨f, hfH⟩ : ∃ f : ↥(Work.ThreePoints.p3F X), (f : G) ∉ H := by
      by_contra h; push Not at h
      exact hK.1 ((Subgroup.eq_top_iff' _).mpr
        (fun x => Subgroup.mem_subgroupOf.mpr ⟨x.2, h x⟩))
    -- an involution of `F` lying in `H`
    haveI : Fintype ↥((Work.ThreePoints.p3F X ⊓ H).subgroupOf (Work.ThreePoints.p3F X)) :=
      Fintype.ofFinite _
    have h2dvd : 2 ∣ Fintype.card
        ↥((Work.ThreePoints.p3F X ⊓ H).subgroupOf (Work.ThreePoints.p3F X)) := by
      rw [← Nat.card_eq_fintype_card]
      exact even_iff_two_dvd.mp hK.2.1
    obtain ⟨vK, hvK2⟩ := exists_prime_orderOf_dvd_card 2 h2dvd
    let v : ↥(Work.ThreePoints.p3F X) := (vK : ↥(Work.ThreePoints.p3F X))
    have hv2 : orderOf v = 2 := by
      change orderOf (vK : ↥(Work.ThreePoints.p3F X)) = 2
      rw [Subgroup.orderOf_coe vK]
      exact hvK2
    have hvH : (v : G) ∈ H := by
      have h1 : (v : G) ∈ Work.ThreePoints.p3F X ⊓ H := Subgroup.mem_subgroupOf.mp vK.2
      exact h1.2
    have hvG2 : orderOf (v : G) = 2 := by
      rw [Subgroup.orderOf_coe v]
      exact hv2
    -- `v` normalises the image of `O_{2'}(F)` in `G`
    have hv_norm : (v : G) ∈ Subgroup.normalizer
        (((Submission.Blueprint.oddCore ↥(Work.ThreePoints.p3F X)).map
          (Work.ThreePoints.p3F X).subtype : Subgroup G) : Set G) :=
      mem_normalizer_map_subtype (K := Work.ThreePoints.p3F X)
        (O := Submission.Blueprint.oddCore ↥(Work.ThreePoints.p3F X)) inferInstance v
    -- `H` and `H^f` both contain `X` (and hence the image of `O_{2'}(F)`)
    have hXf : X ≤ Submission.Blueprint.conj (f : G) H := by
      intro y hy
      rw [Work.ThreePoints.mem_conj_iff]
      have hcomm : y * (f : G) = (f : G) * y := by
        have hcf := Work.ThreePoints.p3F_le_centralizer X f.2
        rw [Subgroup.mem_centralizer_iff] at hcf
        exact hcf y hy
      rw [mul_assoc, hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
      exact hXH hy
    have hKf : IsStronglyEmbedded
        ((Work.ThreePoints.p3F X ⊓ Submission.Blueprint.conj (f : G) H).subgroupOf
          (Work.ThreePoints.p3F X)) :=
      hSE (Submission.Blueprint.conj (f : G) H) hXf ⟨f, rfl⟩
    have hO_H : ((Submission.Blueprint.oddCore ↥(Work.ThreePoints.p3F X)).map
        (Work.ThreePoints.p3F X).subtype) ≤ H := by
      have h1 : Submission.Blueprint.oddCore ↥(Work.ThreePoints.p3F X) ≤
          (Work.ThreePoints.p3F X ⊓ H).subgroupOf (Work.ThreePoints.p3F X) :=
        Work.ThreePoints.oddCore_le_of_stronglyEmbedded hK hfour
      calc ((Submission.Blueprint.oddCore ↥(Work.ThreePoints.p3F X)).map
            (Work.ThreePoints.p3F X).subtype)
          ≤ (((Work.ThreePoints.p3F X ⊓ H).subgroupOf (Work.ThreePoints.p3F X)).map
              (Work.ThreePoints.p3F X).subtype) := Subgroup.map_mono h1
        _ = Work.ThreePoints.p3F X ⊓ H := Subgroup.map_subgroupOf_eq_of_le inf_le_left
        _ ≤ H := inf_le_right
    have hO_Hf : ((Submission.Blueprint.oddCore ↥(Work.ThreePoints.p3F X)).map
        (Work.ThreePoints.p3F X).subtype) ≤ Submission.Blueprint.conj (f : G) H := by
      have h1 : Submission.Blueprint.oddCore ↥(Work.ThreePoints.p3F X) ≤
          (Work.ThreePoints.p3F X ⊓ Submission.Blueprint.conj (f : G) H).subgroupOf
            (Work.ThreePoints.p3F X) :=
        Work.ThreePoints.oddCore_le_of_stronglyEmbedded hKf hfour
      calc ((Submission.Blueprint.oddCore ↥(Work.ThreePoints.p3F X)).map
            (Work.ThreePoints.p3F X).subtype)
          ≤ (((Work.ThreePoints.p3F X ⊓ Submission.Blueprint.conj (f : G) H).subgroupOf
                (Work.ThreePoints.p3F X)).map (Work.ThreePoints.p3F X).subtype) :=
              Subgroup.map_mono h1
        _ = Work.ThreePoints.p3F X ⊓ Submission.Blueprint.conj (f : G) H :=
              Subgroup.map_subgroupOf_eq_of_le inf_le_left
        _ ≤ Submission.Blueprint.conj (f : G) H := inf_le_right
    -- Theorem C: `v` centralises `O_{2'}(F)`
    have hcent_v : ∀ o ∈ Submission.Blueprint.oddCore ↥(Work.ThreePoints.p3F X), v * o = o * v := by
      intro o ho
      have hO_mem : (o : G) ∈ ((Submission.Blueprint.oddCore ↥(Work.ThreePoints.p3F X)).map
          (Work.ThreePoints.p3F X).subtype) := Subgroup.mem_map.mpr ⟨o, ho, rfl⟩
      have hG := hC G hS H hH (f : G) hfH (v : G) ⟨hvH, hvG2⟩
        (((Submission.Blueprint.oddCore ↥(Work.ThreePoints.p3F X)).map
          (Work.ThreePoints.p3F X).subtype)) (le_inf hO_H hO_Hf) hv_norm (o : G) hO_mem
      refine Subtype.ext ?_
      show ((v * o : ↥(Work.ThreePoints.p3F X)) : G) = ((o * v : ↥(Work.ThreePoints.p3F X)) : G)
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      exact hG
    -- transport to every involution of `F`
    have hcen_all : ∀ u : ↥(Work.ThreePoints.p3F X), orderOf u = 2 →
        ∀ o ∈ Submission.Blueprint.oddCore ↥(Work.ThreePoints.p3F X), u * o = o * u := by
      intro u hu2 o ho
      have hconj : IsConj v u :=
        Work.ThreePoints.involutions_conj_of_stronglyEmbedded
          (G := ↥(Work.ThreePoints.p3F X))
          (H := (Work.ThreePoints.p3F X ⊓ H).subgroupOf (Work.ThreePoints.p3F X)) hK hv2 hu2
      have hcv : Submission.Blueprint.oddCore ↥(Work.ThreePoints.p3F X) ≤
          Subgroup.centralizer ({v} : Set ↥(Work.ThreePoints.p3F X)) := by
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact hcent_v x hx
      have hcu := le_centralizer_of_isConj
        (O := Submission.Blueprint.oddCore ↥(Work.ThreePoints.p3F X)) inferInstance hconj hcv
      have hmem := hcu ho
      rw [Subgroup.mem_centralizer_iff] at hmem
      exact hmem u (Set.mem_singleton u)
    -- `F = ⟨Inv F⟩` turns this into `O_{2'}(F) ≤ Z(F)`
    intro o ho
    rw [Subgroup.mem_center_iff]
    intro y
    have hle : Subgroup.closure
        (Submission.Blueprint.involutions ((⊤ : Subgroup ↥(Work.ThreePoints.p3F X)) :
          Set ↥(Work.ThreePoints.p3F X))) ≤
        Subgroup.centralizer ({o} : Set ↥(Work.ThreePoints.p3F X)) := by
      rw [Subgroup.closure_le]
      intro u hu
      change u ∈ Subgroup.centralizer ({o} : Set ↥(Work.ThreePoints.p3F X))
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact (hcen_all u (Work.ThreePoints.mem_involutions.mp hu).2 o ho).symm
    have hy : y ∈ Subgroup.centralizer ({o} : Set ↥(Work.ThreePoints.p3F X)) := by
      apply hle
      rw [hgen]
      exact Subgroup.mem_top y
    rw [Subgroup.mem_centralizer_iff] at hy
    exact (hy o (Set.mem_singleton o)).symm
  · -- `Z(F) ≤ O_{2'}(F)`
    exact Work.BrauerSuzuki.OddCore.le_of_normal_odd (inferInstance)
      (odd_card_center_of_isStronglyEmbedded hK)

end Work.ThreePoints
