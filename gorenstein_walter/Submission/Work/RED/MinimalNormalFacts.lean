import Mathlib
import Submission.Work.RED.Basic
import Submission.Work.RED.MNF_char_free
import Submission.Work.RED.MNF_char_normal
import Submission.Work.RED.MNF_commute_of_minimalNormalIn
import Submission.Work.RED.MNF_abelian_elementary

/-!
# RED: `MinimalNormalFactsProp`

The elementary theory of minimal normal subgroups needed by the non-simple step of the
Gorenstein–Walter / Bender argument (`Work.RED.GW2.MinimalNormalFactsProp`).

The four independent "field" lemmas proved by colleagues (`char_free`, `char_normal`,
`commute_of_minimalNormalIn`, `abelian_elementary`) are imported; everything else --
existence (fields 1, 2), the structure theory around a minimal normal subgroup of a normal
subgroup (fields 5, 7, 8), the supporting lemmas and the assembly -- is here.
-/

namespace Work.RED

namespace MNF

open Subgroup

variable {G : Type*} [Group G]

/-! ## Basic subgroup helper lemmas -/

/-- A subgroup of `↥N` is the `subgroupOf N` of its image in `G`. -/
theorem map_subtype_subgroupOf (N : Subgroup G) (L : Subgroup ↥N) :
    (L.map N.subtype).subgroupOf N = L := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · rintro ⟨l, hl, hlx⟩
    have hlx' : l = x := Subtype.ext hlx
    rwa [← hlx']
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- Monotonicity of `Nat.card` for subgroups. -/
theorem card_le_card_of_le {H K : Subgroup G} [Finite K] (h : H ≤ K) : Nat.card H ≤ Nat.card K :=
  Nat.card_le_card_of_injective (fun x : ↥H => (⟨(x : G), h x.2⟩ : ↥K))
    (fun a b hab => Subtype.ext (by simpa using hab))

/-- If the elements of a set commute pairwise, so do the elements of the subgroup it
generates. -/
theorem closure_commute {s : Set G} (h : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x) :
    ∀ x ∈ Subgroup.closure s, ∀ y ∈ Subgroup.closure s, x * y = y * x := by
  have h1 : ∀ x ∈ s, x ∈ Subgroup.centralizer s :=
    fun x hx => Subgroup.mem_centralizer_iff.mpr (fun y hy => h y hy x hx)
  have h2 : Subgroup.closure s ≤ Subgroup.centralizer s := (Subgroup.closure_le _).mpr h1
  have h3 : ∀ x ∈ s, x ∈ Subgroup.centralizer (Subgroup.closure s) :=
    fun x hx => Subgroup.mem_centralizer_iff.mpr
      (fun y hy => ((Subgroup.mem_centralizer_iff.mp (h2 hy)) x hx).symm)
  have h4 : Subgroup.closure s ≤ Subgroup.centralizer (Subgroup.closure s) :=
    (Subgroup.closure_le _).mpr h3
  intro x hx y hy
  exact (Subgroup.mem_centralizer_iff.mp (h4 hx) y hy).symm

/-! ## Existence of minimal normal subgroups (fields 1 and 2) -/

theorem exists_minimal (G : Type*) [Group G] [Finite G] [Nontrivial G] :
    ∃ N : Subgroup G, GW2.IsMinimalNormal N := by
  classical
  let p : ℕ → Prop := fun n => ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ Nat.card N = n
  have htop : (⊤ : Subgroup G) ≠ ⊥ := by
    intro h
    obtain ⟨x, hx⟩ := exists_ne (1 : G)
    have hx' : x ∈ (⊥ : Subgroup G) := by rw [← h]; trivial
    rw [Subgroup.mem_bot] at hx'
    exact hx hx'
  have hex : ∃ n, p n := ⟨Nat.card (⊤ : Subgroup G), ⊤, inferInstance, htop, rfl⟩
  obtain ⟨N, hNnorm, hNne, hNcard⟩ := Nat.find_spec hex
  refine ⟨N, hNnorm, hNne, ?_⟩
  intro M hMnorm hMne hMle
  have hMp : p (Nat.card M) := ⟨M, hMnorm, hMne, rfl⟩
  have h1 : Nat.find hex ≤ Nat.card M := Nat.find_min' hex hMp
  have h2 : Nat.card M ≤ Nat.card N := card_le_card_of_le hMle
  exact le_of_eq (Subgroup.eq_of_le_of_card_ge hMle (by rw [hNcard]; exact h1)).symm

theorem exists_minimalIn (G : Type*) [Group G] [Finite G] (N : Subgroup G) (hN : N ≠ ⊥) :
    ∃ K : Subgroup G, GW2.IsMinimalNormalIn N K := by
  classical
  let p : ℕ → Prop := fun n =>
    ∃ K : Subgroup G, K ≤ N ∧ (K.subgroupOf N).Normal ∧ K ≠ ⊥ ∧ Nat.card K = n
  have hself : (N.subgroupOf N).Normal := by
    rw [Subgroup.subgroupOf_self]; exact Subgroup.normal_top
  have hex : ∃ n, p n := ⟨Nat.card N, N, le_rfl, hself, hN, rfl⟩
  obtain ⟨K, hKle, hKnorm, hKne, hKcard⟩ := Nat.find_spec hex
  refine ⟨K, hKle, hKnorm, hKne, ?_⟩
  intro M hMK hMnorm hMne
  have hMp : p (Nat.card M) := ⟨M, le_trans hMK hKle, hMnorm, hMne, rfl⟩
  have h1 : Nat.find hex ≤ Nat.card M := Nat.find_min' hex hMp
  have h2 : Nat.card M ≤ Nat.card K := card_le_card_of_le hMK
  exact Subgroup.eq_of_le_of_card_ge hMK (by rw [hKcard]; exact h1)

/-! ## Minimal normal subgroups and isomorphisms -/

/-- Minimal normal subgroups are preserved by group isomorphisms. -/
theorem IsMinimalNormal.map_mulEquiv {M M' : Type*} [Group M] [Group M'] (e : M ≃* M')
    {L : Subgroup M} (h : GW2.IsMinimalNormal L) :
    GW2.IsMinimalNormal (L.map e.toMonoidHom) := by
  obtain ⟨hNorm, hne, hmin⟩ := h
  refine ⟨hNorm.map e.toMonoidHom e.surjective, ?_, ?_⟩
  · intro hbot
    exact hne ((Subgroup.map_eq_bot_iff_of_injective L e.injective).mp hbot)
  · intro L'' hL''norm hL''ne hL''le
    have hcomap : L''.comap e.toMonoidHom ≤ L := by
      intro x hx
      obtain ⟨l, hl, hlx⟩ := Subgroup.mem_map.mp (hL''le (Subgroup.mem_comap.mp hx))
      have hlx' : l = x := e.injective hlx
      rwa [← hlx']
    have hcomapNorm : (L''.comap e.toMonoidHom).Normal := hL''norm.comap e.toMonoidHom
    have hcomap_ne : L''.comap e.toMonoidHom ≠ ⊥ := by
      intro hbot
      apply hL''ne
      rw [← Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective L'',
        hbot, Subgroup.map_bot]
    have hLN : L ≤ L''.comap e.toMonoidHom := hmin _ hcomapNorm hcomap_ne hcomap
    calc L.map e.toMonoidHom ≤ (L''.comap e.toMonoidHom).map e.toMonoidHom :=
          Subgroup.map_mono hLN
      _ = L'' := Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective L''

/-- `IsMinimalNormalIn N K` is `K.subgroupOf N` being a minimal normal subgroup of `↥N`. -/
theorem isMinimalNormalIn_iff {N K : Subgroup G} (hle : K ≤ N) :
    GW2.IsMinimalNormalIn N K ↔ GW2.IsMinimalNormal (K.subgroupOf N) := by
  have hmap : (K.subgroupOf N).map N.subtype = K := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hle]
  have hbot : K.subgroupOf N = ⊥ ↔ K = ⊥ := by
    constructor
    · intro hc
      rw [← hmap, hc, Subgroup.map_bot]
    · intro hc
      rw [hc, Subgroup.bot_subgroupOf]
  constructor
  · intro h
    refine ⟨h.normal, ?_, ?_⟩
    · intro hc
      exact h.ne_bot (hbot.mp hc)
    · intro L' hL'norm hL'ne hL'le
      have hL' : ((L'.map N.subtype).subgroupOf N).Normal := by
        rw [map_subtype_subgroupOf]; exact hL'norm
      have hne' : L'.map N.subtype ≠ ⊥ := by
        intro hc
        exact hL'ne ((Subgroup.map_eq_bot_iff_of_injective L' N.subtype_injective).mp hc)
      have hle' : L'.map N.subtype ≤ K := by
        rw [← hmap]; exact Subgroup.map_mono hL'le
      have hthis : L'.map N.subtype = K := h.minimal _ hle' hL' hne'
      intro y hy
      have hyK : (y : G) ∈ K := Subgroup.mem_subgroupOf.mp hy
      rw [← hthis] at hyK
      obtain ⟨l, hl, hlq⟩ := Subgroup.mem_map.mp hyK
      have hlq' : l = y := Subtype.ext hlq
      rwa [← hlq']
  · intro h
    refine ⟨hle, h.1, ?_, ?_⟩
    · intro hc
      exact h.2.1 (hbot.mpr hc)
    · intro M hMK hMnorm hMne
      have hle' : M.subgroupOf N ≤ K.subgroupOf N := fun x hx => hMK hx
      have hne' : M.subgroupOf N ≠ ⊥ := by
        intro hc
        apply hMne
        have hM : (M.subgroupOf N).map N.subtype = M := by
          rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (le_trans hMK hle)]
        rw [← hM, hc, Subgroup.map_bot]
      have hthis : K.subgroupOf N ≤ M.subgroupOf N := h.2.2 _ hMnorm hne' hle'
      have hKM : K ≤ M := by
        rw [← hmap]
        calc (K.subgroupOf N).map N.subtype ≤ (M.subgroupOf N).map N.subtype :=
              Subgroup.map_mono hthis
          _ = M := by
              rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (le_trans hMK hle)]
      exact le_antisymm hMK hKM

/-! ## Conjugation of minimal normal subgroups -/

/-- Conjugating the `subgroupOf` picture inside `↥N` and mapping back to `G`. -/
theorem map_conjNormal_map_subtype {A N : Subgroup G} (hN : N.Normal) (hAN : A ≤ N) (c : G) :
    ((A.subgroupOf N).map (MulAut.conjNormal c).toMonoidHom).map N.subtype =
      A.map (MulAut.conj c).toMonoidHom := by
  haveI : N.Normal := hN
  have hA : (A.subgroupOf N).map N.subtype = A := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAN]
  rw [Subgroup.map_map]
  conv_rhs => rw [← hA, Subgroup.map_map]
  have hcomp : N.subtype.comp (MulAut.conjNormal c).toMonoidHom =
      (MulAut.conj c).toMonoidHom.comp N.subtype := by
    ext n
    simp [MulAut.conj_apply]
  rw [hcomp]

/-- `G`-conjugates of a minimal normal subgroup of `N` are again minimal normal subgroups
of `N`. -/
theorem conj_minimal {N K : Subgroup G} (hN : GW2.IsMinimalNormal N)
    (hK : GW2.IsMinimalNormalIn N K) (c : G) :
    GW2.IsMinimalNormalIn N (K.map (MulAut.conj c).toMonoidHom) := by
  haveI : N.Normal := hN.normal
  have hKN : K ≤ N := hK.le
  have h1 : GW2.IsMinimalNormal (K.subgroupOf N) := (isMinimalNormalIn_iff hKN).mp hK
  have h2 : GW2.IsMinimalNormal ((K.subgroupOf N).map (MulAut.conjNormal c).toMonoidHom) :=
    IsMinimalNormal.map_mulEquiv (MulAut.conjNormal c) h1
  have h3 : GW2.IsMinimalNormal
      ((((K.subgroupOf N).map (MulAut.conjNormal c).toMonoidHom).map N.subtype).subgroupOf N) := by
    rw [map_subtype_subgroupOf]; exact h2
  have h4 := (isMinimalNormalIn_iff
      (Subgroup.map_subtype_le ((K.subgroupOf N).map (MulAut.conjNormal c).toMonoidHom))).mpr h3
  rwa [map_conjNormal_map_subtype hN.normal hKN c] at h4

/-! ## Fields 7 and 8 -/

/-- A minimal normal subgroup of `N` inside a nonabelian minimal normal subgroup `N` is
nonabelian. -/
theorem nonabelian_of_minimalNormalIn (G : Type*) [Group G] [Finite G] (N K : Subgroup G)
    (hN : GW2.IsMinimalNormal N) (hK : GW2.IsMinimalNormalIn N K)
    (hnab : ¬ IsMulCommutative N) : ¬ IsMulCommutative K := by
  classical
  intro hKab
  apply hnab
  haveI : N.Normal := hN.normal
  have hKcomm : IsMulCommutative ↥K := hKab
  haveI := hKcomm
  have hKN : K ≤ N := hK.le
  have hMle : Subgroup.normalClosure (K : Set G) ≤ N :=
    Subgroup.normalClosure_le_normal (fun x hx => hKN hx)
  have hMne : Subgroup.normalClosure (K : Set G) ≠ ⊥ := by
    intro hbot
    have h1 : K ≤ (⊥ : Subgroup G) := by rw [← hbot]; exact Subgroup.le_normalClosure
    exact hK.ne_bot (le_bot_iff.mp h1)
  have hNM : N ≤ Subgroup.normalClosure (K : Set G) :=
    hN.2.2 _ inferInstance hMne hMle
  have hMN : Subgroup.normalClosure (K : Set G) = N := le_antisymm hMle hNM
  have hgen : ∀ x ∈ Group.conjugatesOfSet (K : Set G),
      ∀ y ∈ Group.conjugatesOfSet (K : Set G), x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, ha, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨c, hc⟩ := isConj_iff.mp hconj
    obtain ⟨b, hb, hconj2⟩ := Group.mem_conjugatesOfSet_iff.mp hy
    obtain ⟨d, hd⟩ := isConj_iff.mp hconj2
    have hxL : x ∈ K.map (MulAut.conj c).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨a, ha, by simpa [MulAut.conj_apply] using hc⟩
    have hyL : y ∈ K.map (MulAut.conj d).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨b, hb, by simpa [MulAut.conj_apply] using hd⟩
    by_cases hcd : K.map (MulAut.conj c).toMonoidHom = K.map (MulAut.conj d).toMonoidHom
    · haveI : IsMulCommutative ↥(K.map (MulAut.conj c).toMonoidHom) :=
        Subgroup.map_isMulCommutative K (MulAut.conj c).toMonoidHom
      rw [hcd] at hxL
      exact setLike_mul_comm hxL hyL
    · exact (MNF_commute_of_minimalNormalIn G N _ _ hN (conj_minimal hN hK c)
        (conj_minimal hN hK d) hcd).2 x hxL y hyL
  have hMcomm : IsMulCommutative ↥(Subgroup.normalClosure (K : Set G)) :=
    IsMulCommutative.of_setLike_mul_comm (fun a ha b hb => closure_commute hgen a ha b hb)
  rw [hMN] at hMcomm
  exact hMcomm

/-- `N` is simple as a group when it is a minimal normal subgroup of itself. -/
theorem isSimpleGroup_of_minimalNormalIn_self (G : Type*) [Group G] [Finite G] (N : Subgroup G)
    (h : GW2.IsMinimalNormalIn N N) : IsSimpleGroup ↥N := by
  have hne : ∃ x ∈ N, x ≠ 1 := by
    by_contra hc
    apply h.ne_bot
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    by_contra hx1
    exact hc ⟨x, hx, hx1⟩
  haveI : Nontrivial ↥N := by
    obtain ⟨x, hxN, hx1⟩ := hne
    exact ⟨⟨x, hxN⟩, 1, fun hcon => hx1 (Subtype.ext_iff.mp hcon)⟩
  refine IsSimpleGroup.mk fun L hL => ?_
  have hL'le : L.map N.subtype ≤ N := Subgroup.map_subtype_le L
  have hsub : (L.map N.subtype).subgroupOf N = L := map_subtype_subgroupOf N L
  rcases eq_or_ne (L.map N.subtype) ⊥ with hbot | hne'
  · left
    rw [← hsub, hbot, Subgroup.bot_subgroupOf]
  · right
    have h1 : ((L.map N.subtype).subgroupOf N).Normal := by rw [hsub]; exact hL
    have h2 : L.map N.subtype = N := h.minimal _ hL'le h1 hne'
    rw [← hsub, h2, Subgroup.subgroupOf_self]

end MNF

theorem MinimalNormalFacts : Work.RED.GW2.MinimalNormalFactsProp where
  exists_minimal := MNF.exists_minimal
  exists_minimalIn := MNF.exists_minimalIn
  char_free := MNF_char_free
  char_normal := MNF_char_normal
  commute_of_minimalNormalIn := MNF_commute_of_minimalNormalIn
  abelian_elementary := MNF_abelian_elementary
  nonabelian_of_minimalNormalIn := MNF.nonabelian_of_minimalNormalIn
  isSimpleGroup_of_minimalNormalIn_self := MNF.isSimpleGroup_of_minimalNormalIn_self

end Work.RED
