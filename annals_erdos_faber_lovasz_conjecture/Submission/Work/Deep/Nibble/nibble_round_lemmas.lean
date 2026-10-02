import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.nibble_state

set_option autoImplicit false
open scoped BigOperators

namespace Work.Deep.Nibble

variable {n : ℕ}

/-! ## Basic counting helpers -/

/-- `Nat.card` of a set-as-a-type is its `ncard`. -/
theorem natCard_eq_ncard {α : Type*} (s : Set α) : Nat.card s = s.ncard := by
  rw [← Set.ncard_univ (α := s), Set.ncard_coe]

/-- `hd` counts the edges through `v` as a family of sets. -/
theorem hd_eq_ncard {V : Type*} (𝓖 : Set (Set V)) (v : V) :
    hd 𝓖 v = ({s : Set V | s ∈ 𝓖 ∧ v ∈ s} : Set (Set V)).ncard := by
  classical
  have h1 : hd 𝓖 v = Nat.card {e : 𝓖 // v ∈ (e : Set V)} := rfl
  have h2 : Nat.card {e : 𝓖 // v ∈ (e : Set V)}
      = ((Set.univ : Set {e : 𝓖 // v ∈ (e : Set V)}).ncard) := by
    rw [Set.ncard_univ]
  have h3 : ((Set.univ : Set {e : 𝓖 // v ∈ (e : Set V)}).ncard)
      = (((fun x : {e : 𝓖 // v ∈ (e : Set V)} => (x.1.1 : Set V)) '' Set.univ).ncard) :=
    (Set.ncard_image_of_injective Set.univ
      (fun a b hab => Subtype.ext (Subtype.ext hab))).symm
  have h4 : ((fun x : {e : 𝓖 // v ∈ (e : Set V)} => (x.1.1 : Set V)) '' Set.univ)
      = ({s : Set V | s ∈ 𝓖 ∧ v ∈ s} : Set (Set V)) := by
    ext s
    constructor
    · rintro ⟨x, -, rfl⟩; exact ⟨x.1.2, x.2⟩
    · rintro ⟨hs, hv⟩; exact ⟨⟨⟨s, hs⟩, hv⟩, Set.mem_univ _, rfl⟩
  rw [h1, h2, h3, h4]

/-- `kAt` counts the kept edges through `v` as a family of sets. -/
theorem kAt_eq_ncard {V : Type*} (𝓖 : Set (Set V)) (ω : 𝓖 → Bool) (v : V) :
    kAt 𝓖 ω v = ({s : Set V | s ∈ kept 𝓖 ω ∧ v ∈ s} : Set (Set V)).ncard := by
  classical
  have h1 : kAt 𝓖 ω v = Nat.card {e : 𝓖 // v ∈ (e : Set V) ∧ ω e = true} := rfl
  have h2 : Nat.card {e : 𝓖 // v ∈ (e : Set V) ∧ ω e = true}
      = ((Set.univ : Set {e : 𝓖 // v ∈ (e : Set V) ∧ ω e = true}).ncard) := by
    rw [Set.ncard_univ]
  have h3 : ((Set.univ : Set {e : 𝓖 // v ∈ (e : Set V) ∧ ω e = true}).ncard)
      = (((fun x : {e : 𝓖 // v ∈ (e : Set V) ∧ ω e = true} => (x.1.1 : Set V)) ''
          Set.univ).ncard) :=
    (Set.ncard_image_of_injective Set.univ
      (fun a b hab => Subtype.ext (Subtype.ext hab))).symm
  have h4 : ((fun x : {e : 𝓖 // v ∈ (e : Set V) ∧ ω e = true} => (x.1.1 : Set V)) '' Set.univ)
      = ({s : Set V | s ∈ kept 𝓖 ω ∧ v ∈ s} : Set (Set V)) := by
    ext s
    constructor
    · rintro ⟨x, -, rfl⟩; exact ⟨⟨x.1.2, x.2.2⟩, x.2.1⟩
    · rintro ⟨⟨hs, hw⟩, hv⟩; exact ⟨⟨⟨s, hs⟩, hv, hw⟩, Set.mem_univ _, rfl⟩
  rw [h1, h2, h3, h4]

/-- Degrees of the restricted hypergraph. -/
theorem hd_res_eq_deg (𝓗 : Set (Set (Fin n))) (U : Set (Fin n)) (v : ↥U) :
    hd (res 𝓗 U) v = deg 𝓗 U (v : Fin n) := by
  classical
  have hkey : ∀ {t : Set (Fin n)}, t ⊆ U →
      ((Subtype.val : ↥U → Fin n) '' ((Subtype.val : ↥U → Fin n) ⁻¹' t)) = t := by
    intro t hsub
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩; exact hy
    · intro hx; exact ⟨⟨x, hsub hx⟩, hx, rfl⟩
  have h1 := hd_eq_ncard (res 𝓗 U) v
  have h2 : deg 𝓗 U (v : Fin n) = (star 𝓗 U (v : Fin n)).ncard := rfl
  have h3 : (({s : Set ↥U | s ∈ res 𝓗 U ∧ v ∈ s} : Set (Set ↥U)).ncard)
      = ((((fun x : Set ↥U => (Subtype.val '' x : Set (Fin n))) ''
          ({s : Set ↥U | s ∈ res 𝓗 U ∧ v ∈ s} : Set (Set ↥U)))).ncard) :=
    (Set.ncard_image_of_injective _ (valn_injective (U := U))).symm
  rw [h1, h2, h3]
  congr 1
  ext t
  constructor
  · rintro ⟨s, ⟨hs, hv⟩, rfl⟩
    exact ⟨fun x hx => by obtain ⟨y, hy, rfl⟩ := hx; exact y.2, hs, ⟨v, hv, rfl⟩⟩
  · rintro ⟨hsub, ht, hv⟩
    exact ⟨(Subtype.val : ↥U → Fin n) ⁻¹' t, ⟨by
      show ((Subtype.val : ↥U → Fin n) '' ((Subtype.val : ↥U → Fin n) ⁻¹' t)) ∈ 𝓗
      rw [hkey hsub]; exact ht, hv⟩, hkey hsub⟩

/-- The standard linear-hypergraph degree bound: `deg v` edges of size `r` through `v`
cover `1 + (r-1)·deg v` vertices. -/
theorem deg_le_card {r : ℕ} {𝓗 : Set (Set (Fin n))} {U : Set (Fin n)} {v : Fin n}
    (hl : HLin 𝓗) (hu : HUnif 𝓗 r) (hv : v ∈ U) :
    1 + (r - 1) * deg 𝓗 U v ≤ U.ncard := by
  classical
  have hSfin : (star 𝓗 U v).Finite := Set.toFinite _
  have hdisj : (star 𝓗 U v).PairwiseDisjoint (fun s : Set (Fin n) => s \ {v}) := by
    intro s hs t ht hst
    show Disjoint (s \ {v}) (t \ {v})
    rw [Set.disjoint_iff_inter_eq_empty]
    ext x
    constructor
    · intro hx
      obtain ⟨⟨hxs, hxv⟩, hxt, -⟩ := hx
      have hsub : (s ∩ t).Subsingleton := hl hs.2.1 ht.2.1 hst
      exact hxv (hsub ⟨hxs, hxt⟩ ⟨hs.2.2, ht.2.2⟩)
    · intro hx; exact absurd hx (by simp)
  have htail : ∀ s ∈ star 𝓗 U v, (s \ {v}).ncard = r - 1 := by
    intro s hs
    rw [Set.ncard_sdiff_singleton_of_mem hs.2.2, hu s hs.2.1]
  have hunion : (⋃ s ∈ star 𝓗 U v, s \ {v}).ncard = ∑ᶠ s ∈ star 𝓗 U v, (s \ {v}).ncard :=
    hSfin.ncard_biUnion (fun s _ => Set.toFinite _) hdisj
  have hsum : (∑ᶠ s ∈ star 𝓗 U v, (s \ {v}).ncard) = (star 𝓗 U v).ncard * (r - 1) := by
    rw [finsum_mem_congr rfl htail]
    rw [finsum_mem_eq_finite_toFinset_sum (fun _ => r - 1) hSfin]
    rw [Finset.sum_const, smul_eq_mul]
    congr 1
    exact (Set.ncard_eq_toFinset_card (star 𝓗 U v) hSfin).symm
  have hmem : ∀ x : Fin n, x ∈ (⋃ s ∈ star 𝓗 U v, s \ {v}) ↔
      ∃ s ∈ star 𝓗 U v, x ∈ s ∧ x ≠ v := by
    intro x
    rw [Set.mem_iUnion₂]
    constructor
    · rintro ⟨s, hs, hxs⟩
      exact ⟨s, hs, (Set.mem_sdiff x).mp hxs⟩
    · rintro ⟨s, hs, hxs, hxv⟩
      exact ⟨s, hs, (Set.mem_sdiff x).mpr ⟨hxs, hxv⟩⟩
  have hsub : ({v} : Set (Fin n)) ∪ (⋃ s ∈ star 𝓗 U v, s \ {v}) ⊆ U := by
    intro x hx
    rw [Set.mem_union] at hx
    rcases hx with hx | hx
    · rw [Set.mem_singleton_iff] at hx; exact hx ▸ hv
    · rcases (hmem x).mp hx with ⟨s, hs, hxs, -⟩
      exact hs.1 hxs
  have hdisjv : Disjoint ({v} : Set (Fin n)) (⋃ s ∈ star 𝓗 U v, s \ {v}) := by
    rw [Set.disjoint_iff_inter_eq_empty]
    ext x
    constructor
    · intro hx
      rw [Set.mem_inter_iff, Set.mem_singleton_iff] at hx
      rcases (hmem x).mp hx.2 with ⟨s, -, -, hxv⟩
      exact hxv hx.1
    · intro hx; exact absurd hx (by simp)
  have hle : ({v} : Set (Fin n)).ncard + (⋃ s ∈ star 𝓗 U v, s \ {v}).ncard ≤ U.ncard := by
    rw [← Set.ncard_union_eq hdisjv (Set.toFinite _) (Set.toFinite _)]
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_singleton, hunion, hsum] at hle
  have hSe : (star 𝓗 U v).ncard = deg 𝓗 U v := rfl
  rw [hSe] at hle
  rw [Nat.mul_comm]
  exact hle

/-- `isoFam` is a matching of `r`-sets: its members are pairwise disjoint, they are kept
edges, and its vertex set has cardinality `r * |isoFam|`. -/
theorem isofam_matching {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
    (𝓖 : Set (Set V)) (ω : 𝓖 → Bool) (hu : HUnif 𝓖 r) :
    (∀ e f : 𝓖, e ∈ isoFam 𝓖 ω → f ∈ isoFam 𝓖 ω → e ≠ f →
        Disjoint (e : Set V) (f : Set V)) ∧
    (∀ e : 𝓖, e ∈ isoFam 𝓖 ω → (e : Set V) ∈ kept 𝓖 ω) ∧
    (⋃ e ∈ isoFam 𝓖 ω, (e : Set V)).ncard = r * (isoFam 𝓖 ω).ncard := by
  classical
  have hdisj : ∀ e f : 𝓖, e ∈ isoFam 𝓖 ω → f ∈ isoFam 𝓖 ω → e ≠ f →
      Disjoint (e : Set V) (f : Set V) := by
    intro e f he hf hne
    have h := he.2 f (Ne.symm hne) hf.1
    have hfe : (f : Set V) ∩ (e : Set V) = ∅ := by
      by_contra hc
      exact absurd (Set.nonempty_iff_ne_empty.mpr hc) (fun hx => h ▸ hx)
    rw [Set.disjoint_iff_inter_eq_empty, ← hfe, Set.inter_comm]
  refine ⟨hdisj, fun e he => ⟨e.2, he.1⟩, ?_⟩
  have hfinS : (isoFam 𝓖 ω).Finite := Set.toFinite _
  have hU : (⋃ e ∈ isoFam 𝓖 ω, (e : Set V)).Finite := Set.toFinite _
  rw [Set.ncard_eq_toFinset_card _ hU, Set.ncard_eq_toFinset_card _ hfinS]
  have hEq : hU.toFinset = hfinS.toFinset.biUnion
      (fun e : ↥𝓖 => (Set.Finite.toFinset (Set.toFinite (e : Set V)))) := by
    ext a
    simp only [Set.Finite.mem_toFinset, Finset.mem_biUnion]
    simp
  have hpd : (hfinS.toFinset : Set ↥𝓖).PairwiseDisjoint
      (fun e : ↥𝓖 => (Set.Finite.toFinset (Set.toFinite (e : Set V)))) := by
    intro e he f hf hef
    have hd := hdisj e f ((Set.Finite.mem_toFinset hfinS).mp he)
      ((Set.Finite.mem_toFinset hfinS).mp hf) hef
    refine disjoint_iff.mpr ?_
    rw [Finset.inf_eq_inter, Finset.bot_eq_empty]
    apply Finset.ext
    intro a
    have hI : (e : Set V) ∩ (f : Set V) = ∅ := Set.disjoint_iff_inter_eq_empty.mp hd
    constructor
    · intro ham
      rw [Finset.mem_inter] at ham
      obtain ⟨ha1, ha2⟩ := ham
      have hmem : a ∈ (e : Set V) ∩ (f : Set V) :=
        ⟨(Set.Finite.mem_toFinset _).mp ha1, (Set.Finite.mem_toFinset _).mp ha2⟩
      rw [hI] at hmem
      simp at hmem
    · intro ha
      simp at ha
  rw [hEq, Finset.card_biUnion hpd,
    Finset.sum_congr rfl (fun e (_ : e ∈ hfinS.toFinset) => by
      rw [← Set.ncard_eq_toFinset_card _ (Set.toFinite (e : Set V)), hu (e : Set V) e.2])]
  rw [Finset.sum_const]
  exact Nat.mul_comm _ _

/-- Vertices covered by a kept edge but not by an isolated kept edge are charged to the
collision multiplicity. -/
theorem round_waste {V : Type*} [Fintype V] [DecidableEq V] (r : ℕ)
    (𝓖 : Set (Set V)) (ω : 𝓖 → Bool) (hu : HUnif 𝓖 r) :
    (covX 𝓖 ω \ ⋃ e ∈ isoFam 𝓖 ω, (e : Set V)).ncard ≤ r * collMult 𝓖 ω := by
  classical
  set Bad : Set (Set V) := kept 𝓖 ω \ (fun e : 𝓖 => (e : Set V)) '' (isoFam 𝓖 ω) with hBad
  have hA : covX 𝓖 ω \ ⋃ e ∈ isoFam 𝓖 ω, (e : Set V) ⊆ ⋃₀ Bad := by
    intro x hx
    rw [Set.mem_sdiff] at hx
    obtain ⟨hx1, hx2⟩ := hx
    rw [covX, Set.mem_iUnion₂] at hx1
    obtain ⟨e, he, hxe⟩ := hx1
    have hnotIso : e ∉ (fun f : 𝓖 => (f : Set V)) '' (isoFam 𝓖 ω) := by
      rintro ⟨f, hf, hfe⟩
      refine hx2 ?_
      rw [Set.mem_iUnion₂]
      refine ⟨f, hf, ?_⟩
      have hfe' : (f : Set V) = e := hfe
      rw [hfe']
      exact hxe
    exact Set.mem_sUnion.mpr ⟨e, ⟨he, hnotIso⟩, hxe⟩
  have hB : (⋃₀ Bad).ncard ≤ r * Bad.ncard := by
    have h1 : (⋃ e ∈ Bad, e).ncard ≤ ∑ᶠ e ∈ Bad, e.ncard :=
      (Set.toFinite Bad).ncard_biUnion_le (fun e => e)
    have h2 : ∀ e ∈ Bad, e.ncard = r := by
      intro e he
      exact hu e he.1.1
    rw [finsum_mem_congr rfl h2] at h1
    rw [finsum_mem_eq_finite_toFinset_sum (fun _ => r) (Set.toFinite Bad)] at h1
    rw [Finset.sum_const, smul_eq_mul] at h1
    have h3 : (Set.Finite.toFinset (Set.toFinite Bad)).card = Bad.ncard :=
      (Set.ncard_eq_toFinset_card Bad (Set.toFinite Bad)).symm
    rw [h3] at h1
    rw [Set.sUnion_eq_biUnion]
    calc (⋃ i ∈ Bad, i).ncard ≤ Bad.ncard * r := h1
      _ = r * Bad.ncard := Nat.mul_comm _ _
  have hC : Bad.ncard ≤ collMult 𝓖 ω := by
    have hBadcard : Bad.ncard = Nat.card {e : 𝓖 // ω e = true ∧ e ∉ isoFam 𝓖 ω} := by
      have h2 : (Subtype.val '' ({e : 𝓖 | ω e = true ∧ e ∉ isoFam 𝓖 ω} : Set 𝓖)) = Bad := by
        ext t
        constructor
        · rintro ⟨e, ⟨he, hni⟩, rfl⟩
          refine ⟨⟨e.2, he⟩, ?_⟩
          rintro ⟨f, hf, hfe⟩
          have hef : e = f := Subtype.ext hfe.symm
          exact hni (by rw [hef]; exact hf)
        · rintro ⟨hkeep, hnotimg⟩
          obtain ⟨he, hw⟩ := hkeep
          refine ⟨⟨t, he⟩, ⟨hw, ?_⟩, rfl⟩
          intro hmem
          exact hnotimg ⟨⟨t, he⟩, hmem, rfl⟩
      calc Bad.ncard
          = ((Subtype.val '' ({e : 𝓖 | ω e = true ∧ e ∉ isoFam 𝓖 ω} : Set 𝓖)) : Set (Set V)).ncard := by
            rw [h2]
        _ = (({e : 𝓖 | ω e = true ∧ e ∉ isoFam 𝓖 ω} : Set 𝓖)).ncard :=
            Set.ncard_image_of_injective _ Subtype.val_injective
        _ = Nat.card {e : 𝓖 // ω e = true ∧ e ∉ isoFam 𝓖 ω} :=
            (natCard_eq_ncard _).symm
    rw [hBadcard]
    have hex : ∀ e : {e : 𝓖 // ω e = true ∧ e ∉ isoFam 𝓖 ω},
        ∃ w : V, w ∈ (e.1 : Set V) ∧ 2 ≤ kAt 𝓖 ω w := by
      intro e
      have hcon : ∃ f : 𝓖, f ≠ e.1 ∧ ω f = true ∧ (f.1 ∩ e.1.1).Nonempty := by
        by_contra hcon
        apply e.2.2
        refine ⟨e.2.1, fun f hfne hfw => ?_⟩
        have hempty : f.1 ∩ e.1.1 = ∅ := by
          ext x
          simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
          intro hx1 hx2
          exact hcon ⟨f, hfne, hfw, ⟨x, hx1, hx2⟩⟩
        rw [hempty]
        simp
      obtain ⟨f, hfne, hfw, hfint⟩ := hcon
      obtain ⟨w, hw1, hw2⟩ := hfint
      refine ⟨w, hw2, ?_⟩
      have hsub : ({f.1, e.1.1} : Set (Set V)) ⊆ {s : Set V | s ∈ kept 𝓖 ω ∧ w ∈ s} := by
        intro s hs
        rcases hs with rfl | rfl
        · exact ⟨⟨f.2, hfw⟩, hw1⟩
        · exact ⟨⟨e.1.2, e.2.1⟩, hw2⟩
      have hne : f.1 ≠ e.1.1 := fun hc => hfne (Subtype.ext hc)
      calc (2 : ℕ) = ({f.1, e.1.1} : Set (Set V)).ncard := (Set.ncard_pair hne).symm
        _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)
        _ = kAt 𝓖 ω w := (kAt_eq_ncard 𝓖 ω w).symm
    let Φ : {e : 𝓖 // ω e = true ∧ e ∉ isoFam 𝓖 ω} →
        (Sigma fun w : {w : V // 2 ≤ kAt 𝓖 ω w} =>
          {e : 𝓖 // (w : V) ∈ (e : Set V) ∧ ω e = true}) :=
      fun e => ⟨⟨(hex e).choose, (hex e).choose_spec.2⟩,
        ⟨e.1, (hex e).choose_spec.1, e.2.1⟩⟩
    have hΦ : Function.Injective Φ := by
      intro a b hab
      have h2 := congrArg (fun x => ((x.2.1 : 𝓖) : Set V)) hab
      exact Subtype.ext (Subtype.ext h2)
    calc Nat.card {e : 𝓖 // ω e = true ∧ e ∉ isoFam 𝓖 ω}
        ≤ Nat.card (Sigma fun w : {w : V // 2 ≤ kAt 𝓖 ω w} =>
            {e : 𝓖 // (w : V) ∈ (e : Set V) ∧ ω e = true}) :=
          Nat.card_le_card_of_injective Φ hΦ
      _ = collMult 𝓖 ω := by
        rw [Nat.card_sigma, collMult]
        have hsum : (∑ w : {w : V // 2 ≤ kAt 𝓖 ω w},
            Nat.card {e : 𝓖 // (w : V) ∈ (e : Set V) ∧ ω e = true})
            = ∑ w : {w : V // 2 ≤ kAt 𝓖 ω w}, kAt 𝓖 ω (w : V) :=
          Finset.sum_congr rfl (fun w _ => rfl)
        rw [hsum, ← Finset.sum_subtype (Finset.univ.filter (fun v : V => 2 ≤ kAt 𝓖 ω v))
          (by intro x; simp) (fun v => kAt 𝓖 ω v)]
        rw [Finset.sum_filter]
  calc (covX 𝓖 ω \ ⋃ e ∈ isoFam 𝓖 ω, (e : Set V)).ncard
      ≤ (⋃₀ Bad).ncard := Set.ncard_le_ncard hA (Set.toFinite _)
    _ ≤ r * Bad.ncard := hB
    _ ≤ r * collMult 𝓖 ω := Nat.mul_le_mul_left r hC

/-- One round of the iteration, seen on the ambient vertex set: the residual vertex set is
`U` minus the covered vertices, it carries the residual hypergraph, and the degrees transfer. -/
theorem round_state {n : ℕ} (𝓗 : Set (Set (Fin n))) (U : Set (Fin n))
    (ω : res 𝓗 U → Bool) :
    let U' : Set (Fin n) := Subtype.val '' (residV (res 𝓗 U) ω)
    U' = U \ (Subtype.val '' (covX (res 𝓗 U) ω)) ∧
    U'.ncard + (covX (res 𝓗 U) ω).ncard = U.ncard ∧
    (fam 𝓗 U' = (fun e : Set ↥U => (Subtype.val '' e : Set (Fin n))) ''
        (residH (res 𝓗 U) ω)) ∧
    (∀ (v : ↥U) (hv : v ∈ residV (res 𝓗 U) ω),
      hd (res 𝓗 U') ⟨(v : Fin n), ⟨v, hv, rfl⟩⟩ = hd (residH (res 𝓗 U) ω) v) := by
  classical
  set U' : Set (Fin n) := Subtype.val '' (residV (res 𝓗 U) ω) with hU'def
  have hkey : ∀ {t : Set (Fin n)}, t ⊆ U →
      ((Subtype.val : ↥U → Fin n) '' ((Subtype.val : ↥U → Fin n) ⁻¹' t)) = t := by
    intro t hsub
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩; exact hy
    · intro hx; exact ⟨⟨x, hsub hx⟩, hx, rfl⟩
  have hU'sub : U' ⊆ U := by
    rintro x ⟨y, -, rfl⟩
    exact y.2
  have himgU' : ∀ {s : Set ↥U'}, ((Subtype.val : ↥U' → Fin n) '' s) ⊆ U' := by
    rintro s x ⟨p, -, rfl⟩
    exact p.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      rintro ⟨z, hz, hzy⟩
      exact hy ((Subtype.val_injective hzy) ▸ hz)
    · rintro ⟨hxU, hxnot⟩
      exact ⟨⟨x, hxU⟩, fun hmem => hxnot ⟨⟨x, hxU⟩, hmem, rfl⟩, rfl⟩
  · have h1 : U'.ncard = (residV (res 𝓗 U) ω).ncard :=
      Set.ncard_image_of_injective _ Subtype.val_injective
    have h2 : (covX (res 𝓗 U) ω).ncard + (residV (res 𝓗 U) ω).ncard = U.ncard := by
      have hdisj : Disjoint (covX (res 𝓗 U) ω) (residV (res 𝓗 U) ω) := by
        rw [residV]; exact disjoint_compl_right
      have hun : covX (res 𝓗 U) ω ∪ residV (res 𝓗 U) ω = Set.univ := by
        rw [residV]; exact Set.union_compl_self _
      rw [← Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _), hun]
      exact Set.ncard_coe U
    rw [h1, Nat.add_comm, h2]
  · ext t
    constructor
    · rintro ⟨hsub, ht⟩
      have htU : t ⊆ U := fun x hx => hU'sub (hsub hx)
      refine ⟨(Subtype.val : ↥U → Fin n) ⁻¹' t, ⟨?_, ?_⟩, hkey htU⟩
      · show ((Subtype.val : ↥U → Fin n) '' ((Subtype.val : ↥U → Fin n) ⁻¹' t)) ∈ 𝓗
        rw [hkey htU]; exact ht
      · intro y hy
        obtain ⟨z, hz, hzy⟩ := hsub hy
        exact (Subtype.val_injective hzy) ▸ hz
    · rintro ⟨e, ⟨he, hesub⟩, rfl⟩
      refine ⟨?_, he⟩
      intro x hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨y, hesub hy, rfl⟩
  · intro v hv
    have hx0 : (⟨(v : Fin n), ⟨v, hv, rfl⟩⟩ : ↥U') = ⟨(v : Fin n), ⟨v, hv, rfl⟩⟩ := rfl
    have hL : hd (residH (res 𝓗 U) ω) v
        = ({e : Set ↥U | e ∈ residH (res 𝓗 U) ω ∧ v ∈ e} : Set (Set ↥U)).ncard :=
      hd_eq_ncard _ _
    have hR : hd (res 𝓗 U') (⟨(v : Fin n), ⟨v, hv, rfl⟩⟩ : ↥U')
        = ({s : Set ↥U' | s ∈ res 𝓗 U' ∧ (⟨(v : Fin n), ⟨v, hv, rfl⟩⟩ : ↥U') ∈ s}
            : Set (Set ↥U')).ncard :=
      hd_eq_ncard _ _
    rw [hL, hR]
    have hesub1 : ∀ {e : Set ↥U}, e ∈ residH (res 𝓗 U) ω → e ⊆ residV (res 𝓗 U) ω := by
      intro e he
      exact (show e ∈ res 𝓗 U ∧ e ⊆ residV (res 𝓗 U) ω from he).2
    have hval_eq : ∀ {a : Set ↥U}, a ⊆ residV (res 𝓗 U) ω →
        ((Subtype.val : ↥U' → Fin n) '' ({p : ↥U' | (p : Fin n) ∈ (Subtype.val '' a)} : Set ↥U'))
          = (Subtype.val '' a : Set (Fin n)) := by
      intro a ha
      ext x
      constructor
      · rintro ⟨p, hp, rfl⟩; exact hp
      · intro hx
        obtain ⟨y, hy, rfl⟩ := hx
        exact ⟨⟨(y : Fin n), ⟨y, ha hy, rfl⟩⟩, ⟨y, hy, rfl⟩, rfl⟩
    refine (Set.ncard_congr
      (f := fun e (_ : e ∈ ({e : Set ↥U | e ∈ residH (res 𝓗 U) ω ∧ v ∈ e} : Set (Set ↥U))) =>
        ({p : ↥U' | (p : Fin n) ∈ (Subtype.val '' e)} : Set ↥U')) ?_ ?_ ?_).symm
    · intro e he
      refine ⟨?_, ?_⟩
      · show ((Subtype.val '' ({p : ↥U' | (p : Fin n) ∈ (Subtype.val '' e)} : Set ↥U'))
            : Set (Fin n)) ∈ 𝓗
        rw [hval_eq (hesub1 he.1)]
        exact he.1.1
      · exact ⟨v, he.2, rfl⟩
    · intro e f he hf hef
      have h2 : (Subtype.val '' e : Set (Fin n)) = (Subtype.val '' f : Set (Fin n)) := by
        rw [← hval_eq (hesub1 he.1), ← hval_eq (hesub1 hf.1), hef]
      exact valn_injective h2
    · intro s hs
      have hsH : (Subtype.val '' s : Set (Fin n)) ∈ 𝓗 := hs.1
      have hsv : (⟨(v : Fin n), ⟨v, hv, rfl⟩⟩ : ↥U') ∈ s := hs.2
      have hsU : (Subtype.val '' s : Set (Fin n)) ⊆ U := fun x hx => hU'sub (himgU' hx)
      refine ⟨(Subtype.val : ↥U → Fin n) ⁻¹' (Subtype.val '' s : Set (Fin n)),
        ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      · show ((Subtype.val : ↥U → Fin n) '' ((Subtype.val : ↥U → Fin n) ⁻¹'
            (Subtype.val '' s : Set (Fin n)))) ∈ 𝓗
        rw [hkey hsU]
        exact hsH
      · intro y hy
        have hy' : (y : Fin n) ∈ (Subtype.val : ↥U' → Fin n) '' s := hy
        obtain ⟨p, hp, hpy⟩ := hy'
        obtain ⟨z, hz, hzy⟩ := (himgU' ⟨p, hp, hpy⟩ : (y : Fin n) ∈ U')
        exact (Subtype.val_injective hzy) ▸ hz
      · exact ⟨⟨(v : Fin n), ⟨v, hv, rfl⟩⟩, hsv, rfl⟩
      · have hvalE : ((Subtype.val : ↥U → Fin n) '' ((Subtype.val : ↥U → Fin n) ⁻¹'
            (Subtype.val '' s : Set (Fin n)))) = (Subtype.val '' s : Set (Fin n)) := hkey hsU
        ext p
        rw [Set.mem_ofPred_eq, hvalE]
        constructor
        · intro hp
          obtain ⟨q, hq, hqp⟩ := hp
          exact (Subtype.val_injective hqp) ▸ hq
        · intro hp
          exact ⟨p, hp, rfl⟩

end Work.Deep.Nibble
