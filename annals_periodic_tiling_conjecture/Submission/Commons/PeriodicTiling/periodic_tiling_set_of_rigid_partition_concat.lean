import Mathlib.GroupTheory.Complement
import Mathlib.Order.CompletePartialOrder
import Submission.Commons.PeriodicTiling.periodicTilingSet_lattice_period

namespace Commons.PeriodicTiling

open scoped Pointwise

/-- Right addition of an element to a set.  This is the notation used in the statement
of `periodic_tiling_set_of_rigid_partition_concat`. -/
instance Set.instHAddSetElement {α : Type*} [Add α] : HAdd (Set α) α (Set α) :=
  ⟨fun s a => s + ({a} : Set α)⟩

/-- Left addition of an element to a set. -/
instance Set.instHAddElementSet {α : Type*} [Add α] : HAdd α (Set α) (Set α) :=
  ⟨fun a s => ({a} : Set α) + s⟩

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

noncomputable section

/-- The image of a periodic tiling set under a surjective additive group homomorphism is periodic. -/
lemma IsPeriodicTilingSet.map_addMonoidHom
    {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (φ : G →+ H) (hφ : Function.Surjective φ) {A : Set G}
    (hA : IsPeriodicTilingSet A) : IsPeriodicTilingSet (φ '' A) := by
  classical
  rcases hA with ⟨L, hLfin, s, rfl⟩
  let L' : AddSubgroup H := L.map φ
  have hL_le_comap : L ≤ L'.comap φ := by
    intro x hx
    rw [AddSubgroup.mem_comap]
    exact AddSubgroup.mem_map.mpr ⟨x, hx, rfl⟩
  have hcomap_fin : (L'.comap φ).FiniteIndex :=
    AddSubgroup.finiteIndex_of_le (H := L) (K := L'.comap φ) hL_le_comap
  have hidx : (L'.comap φ).index = L'.index := by
    exact AddSubgroup.index_comap_of_surjective L' hφ
  have hL'fin : L'.FiniteIndex := by
    rw [AddSubgroup.finiteIndex_iff]
    rw [← hidx]
    exact AddSubgroup.finiteIndex_iff.mp hcomap_fin
  refine ⟨L', hL'fin, s.image φ, ?_⟩
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Set.mem_add] at hx ⊢
    rcases hx with ⟨a, ha, b, hb, hsum⟩
    refine ⟨φ a, ?_, φ b, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨a, by simpa using ha, rfl⟩
    · exact AddSubgroup.mem_map.mpr ⟨b, by simpa using hb, rfl⟩
    · simpa [map_add] using congrArg φ hsum
  · intro hy
    rw [Set.mem_add] at hy
    rcases hy with ⟨a, ha, b, hb, hy⟩
    rw [Finset.mem_coe, Finset.mem_image] at ha
    rcases ha with ⟨a0, ha0, rfl⟩
    rcases AddSubgroup.mem_map.mp hb with ⟨b0, hb0, rfl⟩
    rw [Set.mem_image]
    refine ⟨a0 + b0, ?_, ?_⟩
    · rw [Set.mem_add]
      exact ⟨a0, by simpa using ha0, b0, by simpa using hb0, rfl⟩
    · simpa [map_add] using hy

theorem periodic_tiling_set_of_rigid_partition_concat
    {G : Type*} [AddCommGroup G] {M N : ℕ}
    (F : Fin M → Set G)
    (E : Fin M → Set (ZMod N))
    (hN : 0 < N)
    (hFne : ∀ i : Fin M, (F i).Nonempty)
    (hEne : ∀ i : Fin M, (E i).Nonempty)
    (hEcover : ∀ x : ZMod N, ∃ i : Fin M, x ∈ E i)
    (hEdisj : ∀ i j : Fin M, i ≠ j → Disjoint (E i) (E j))
    (hErigid : ∀ i j : Fin M, ∀ h : ZMod N, h ≠ 0 → (E i ∩ (E j + h)).Nonempty)
    {B : Set (G × ZMod N)}
    (hB : AddSubgroup.IsComplement B {x : G × ZMod N | ∃ i : Fin M, x.1 ∈ F i ∧ x.2 ∈ E i})
    (hBper : IsPeriodicTilingSet B) :
    ∃ A : Set G, (∀ i : Fin M, AddSubgroup.IsComplement A (F i)) ∧ IsPeriodicTilingSet A := by
  classical
  haveI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  haveI : Fintype (ZMod N) := ZMod.fintype N
  let C : Set (G × ZMod N) := {x : G × ZMod N | ∃ i : Fin M, x.1 ∈ F i ∧ x.2 ∈ E i}
  have hB' : AddSubgroup.IsComplement B C := by
    simpa [C] using hB
  let π : G × ZMod N →+ G := AddMonoidHom.fst G (ZMod N)
  have hπ_surj : Function.Surjective π := by
    intro g
    exact ⟨(g, 0), rfl⟩
  let A : Set G := π '' B
  have hAper : IsPeriodicTilingSet A := by
    simpa [A] using IsPeriodicTilingSet.map_addMonoidHom π hπ_surj hBper
  refine ⟨A, ?_, hAper⟩
  intro i
  have hA_complement : AddSubgroup.IsComplement A (F i) := by
    classical
    rw [AddSubgroup.IsComplement]
    constructor
    · -- injectivity of `A + F i -> G`
      intro p q hsum
      rcases p with ⟨⟨a, haA⟩, ⟨f, hfF⟩⟩
      rcases q with ⟨⟨a', haA'⟩, ⟨f', hfF'⟩⟩
      rcases haA with ⟨b, hbB, hb_eq⟩
      rcases haA' with ⟨b', hbB', hb'_eq⟩
      subst a
      subst a'
      have hsumG : b.1 + f = b'.1 + f' := by
        simpa [π] using hsum
      -- choose `e, e' ∈ E i` so that `b.2 + e = b'.2 + e'`
      have hchoose : ∃ e : ZMod N, e ∈ E i ∧ ∃ e' : ZMod N, e' ∈ E i ∧ b.2 + e = b'.2 + e' := by
        by_cases hbb : b.2 = b'.2
        · obtain ⟨e, he⟩ := hEne i
          exact ⟨e, he, e, he, by simp [hbb]⟩
        · have hdiff : b'.2 - b.2 ≠ 0 := by
            intro hz
            apply hbb
            exact (sub_eq_zero.mp hz).symm
          rcases hErigid i i (b'.2 - b.2) hdiff with ⟨x, hxE, hxshift⟩
          change x ∈ E i + ({b'.2 - b.2} : Set (ZMod N)) at hxshift
          rw [Set.mem_add] at hxshift
          rcases hxshift with ⟨e, heE, d, hd, hed⟩
          have hd_eq : d = b'.2 - b.2 := by simpa using hd
          refine ⟨x, hxE, e, heE, ?_⟩
          have hx_eq : x = e + (b'.2 - b.2) := by
            rw [hd_eq] at hed
            exact hed.symm
          calc
            b.2 + x = b.2 + (e + (b'.2 - b.2)) := by rw [hx_eq]
            _ = b'.2 + e := by abel
      rcases hchoose with ⟨e, heE, e', heE', hsumZ⟩
      have hc1 : (f, e) ∈ C := ⟨i, hfF, heE⟩
      have hc2 : (f', e') ∈ C := ⟨i, hfF', heE'⟩
      have hdecomp : b + (f, e) = b' + (f', e') := by
        ext
        · exact hsumG
        · exact hsumZ
      have hpair_eq : (⟨⟨b, hbB⟩, ⟨(f, e), hc1⟩⟩ : B × C) =
          (⟨⟨b', hbB'⟩, ⟨(f', e'), hc2⟩⟩ : B × C) := by
        apply hB'.1
        change b + (f, e) = b' + (f', e')
        exact hdecomp
      have hb_eq : b = b' := Subtype.ext_iff.mp (Prod.ext_iff.mp hpair_eq).1
      have hc_eq : (f, e) = (f', e') := Subtype.ext_iff.mp (Prod.ext_iff.mp hpair_eq).2
      have hf_eq : f = f' := congrArg Prod.fst hc_eq
      apply Prod.ext
      · apply Subtype.ext
        exact congrArg π hb_eq
      · apply Subtype.ext
        exact hf_eq
    · -- surjectivity of `A + F i -> G`
      intro g
      let S : Set (B × Fin M) :=
        {p | ∃ f : G, f ∈ F p.2 ∧ (p.1 : G × ZMod N).1 + f = g}
      let piece : B × Fin M → Set (ZMod N) :=
        fun p => (p.1 : G × ZMod N).2 + E p.2
      have hS_cover : ∀ t : ZMod N, ∃ p ∈ S, t ∈ piece p := by
        intro t
        obtain ⟨y, hy⟩ := hB'.2 (g, t)
        rcases y with ⟨⟨b, hbB⟩, ⟨c, hcC⟩⟩
        have hsum : b + c = (g, t) := by simpa using hy
        rcases hcC with ⟨j, hcF, hcE⟩
        refine ⟨⟨⟨b, hbB⟩, j⟩, ?_, ?_⟩
        · refine ⟨c.1, hcF, ?_⟩
          have hg := congrArg Prod.fst hsum
          simpa using hg
        · have ht := congrArg Prod.snd hsum
          change t ∈ ({b.2} : Set (ZMod N)) + E j
          rw [Set.mem_add]
          refine ⟨b.2, by simp, c.2, hcE, ht⟩
      let cover : ZMod N → B × Fin M := fun t => Classical.choose (hS_cover t)
      have hcoverS : ∀ t, cover t ∈ S := fun t => (Classical.choose_spec (hS_cover t)).1
      have hcover_piece : ∀ t, t ∈ piece (cover t) := fun t => (Classical.choose_spec (hS_cover t)).2
      let T : Finset (B × Fin M) := Finset.univ.image cover
      have hT_subset_S : ∀ p ∈ T, p ∈ S := by
        intro p hp
        rcases Finset.mem_image.mp hp with ⟨t, ht, rfl⟩
        exact hcoverS t
      have hT_cover : ∀ x : ZMod N, ∃ p ∈ T, x ∈ piece p := by
        intro x
        refine ⟨cover x, ?_, hcover_piece x⟩
        exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩
      have hS_disjoint : S.PairwiseDisjoint piece := by
        rw [Set.pairwiseDisjoint_iff]
        intro p hp q hq hnonempty
        rcases hnonempty with ⟨z, hzp, hzq⟩
        rcases p with ⟨⟨bp, hbpB⟩, jp⟩
        rcases q with ⟨⟨bq, hbqB⟩, jq⟩
        rcases hp with ⟨fp, hfp, hg_p⟩
        rcases hq with ⟨fq, hfq, hg_q⟩
        change z ∈ ({bp.2} : Set (ZMod N)) + E jp at hzp
        change z ∈ ({bq.2} : Set (ZMod N)) + E jq at hzq
        rw [Set.mem_add] at hzp hzq
        rcases hzp with ⟨xp, hxp, ep, hep, hxpe⟩
        rcases hzq with ⟨xq, hxq, eq, heq, hxqe⟩
        have hxp_eq : xp = bp.2 := by simpa using hxp
        have hxq_eq : xq = bq.2 := by simpa using hxq
        have hc1 : (fp, ep) ∈ C := ⟨jp, hfp, hep⟩
        have hc2 : (fq, eq) ∈ C := ⟨jq, hfq, heq⟩
        have hdecomp : bp + (fp, ep) = bq + (fq, eq) := by
          ext
          · calc
              bp.1 + fp = g := hg_p
              _ = bq.1 + fq := hg_q.symm
          · calc
              bp.2 + ep = z := by simpa [hxp_eq] using hxpe
              _ = bq.2 + eq := by simpa [hxq_eq] using hxqe.symm
        have hpair_eq : (⟨⟨bp, hbpB⟩, ⟨(fp, ep), hc1⟩⟩ : B × C) =
            (⟨⟨bq, hbqB⟩, ⟨(fq, eq), hc2⟩⟩ : B × C) := by
          apply hB'.1
          change bp + (fp, ep) = bq + (fq, eq)
          exact hdecomp
        have hb_eq : bp = bq := Subtype.ext_iff.mp (Prod.ext_iff.mp hpair_eq).1
        have hc_eq : (fp, ep) = (fq, eq) := Subtype.ext_iff.mp (Prod.ext_iff.mp hpair_eq).2
        have hep_eq : ep = eq := congrArg Prod.snd hc_eq
        have hjp_eq : jp = jq := by
          by_contra hj
          have hdis := hEdisj jp jq hj
          have hep_mem_jq : ep ∈ E jq := by
            simpa [hep_eq] using heq
          exact Set.disjoint_left.mp hdis hep hep_mem_jq
        apply Prod.ext
        · exact Subtype.ext hb_eq
        · exact hjp_eq
      have hsame_overlap : ∀ {p q : B × Fin M}, p ∈ S → q ∈ S → p.2 = q.2 →
          (piece p ∩ piece q).Nonempty := by
        intro p q hp hq hpq
        let hpz : ZMod N := (p.1 : G × ZMod N).2
        let hqz : ZMod N := (q.1 : G × ZMod N).2
        by_cases hh : hpz = hqz
        · obtain ⟨e, he⟩ := hEne p.2
          refine ⟨hpz + e, ?_, ?_⟩
          · change hpz + e ∈ ({hpz} : Set (ZMod N)) + E p.2
            rw [Set.mem_add]
            exact ⟨hpz, by simp, e, he, rfl⟩
          · change hpz + e ∈ ({hqz} : Set (ZMod N)) + E q.2
            rw [Set.mem_add]
            refine ⟨hqz, by simp, e, ?_, ?_⟩
            · simpa [hpq, hh] using he
            · simp [hh]
        · have hdiff : hqz - hpz ≠ 0 := by
            intro hz
            apply hh
            exact (sub_eq_zero.mp hz).symm
          rcases hErigid p.2 p.2 (hqz - hpz) hdiff with ⟨x, hxE, hxshift⟩
          change x ∈ E p.2 + ({hqz - hpz} : Set (ZMod N)) at hxshift
          rw [Set.mem_add] at hxshift
          rcases hxshift with ⟨e, heE, d, hd, hed⟩
          have hd_eq : d = hqz - hpz := by simpa using hd
          have hx_eq : x = e + (hqz - hpz) := by
            rw [hd_eq] at hed
            exact hed.symm
          refine ⟨hpz + x, ?_, ?_⟩
          · change hpz + x ∈ ({hpz} : Set (ZMod N)) + E p.2
            rw [Set.mem_add]
            exact ⟨hpz, by simp, x, hxE, rfl⟩
          · change hpz + x ∈ ({hqz} : Set (ZMod N)) + E q.2
            rw [Set.mem_add]
            refine ⟨hqz, by simp, e, ?_, ?_⟩
            · simpa [hpq] using heE
            · calc
                hqz + e = hpz + (e + (hqz - hpz)) := by abel
                _ = hpz + x := by rw [hx_eq]
      have hT_inj_j : Set.InjOn (fun p : B × Fin M => p.2) (T : Set (B × Fin M)) := by
        intro p hpT q hqT hpq
        by_contra hne
        have hpS : p ∈ S := hT_subset_S p hpT
        have hqS : q ∈ S := hT_subset_S q hqT
        have hoverlap : (piece p ∩ piece q).Nonempty := hsame_overlap hpS hqS hpq
        have hpeq : p = q := Set.pairwiseDisjoint_iff.mp hS_disjoint hpS hqS hoverlap
        exact hne hpeq
      have hE_finite (j : Fin M) : (E j).Finite :=
        Set.finite_univ.subset (fun x hx => Set.mem_univ x)
      have hpiece_finite (p : B × Fin M) : (piece p).Finite :=
        Set.finite_univ.subset (fun x hx => Set.mem_univ x)
      let EFin : Fin M → Finset (ZMod N) := fun j => (hE_finite j).toFinset
      let pieceFin : B × Fin M → Finset (ZMod N) := fun p => (hpiece_finite p).toFinset
      have hE_biUnion : (Finset.univ : Finset (Fin M)).biUnion EFin = (Finset.univ : Finset (ZMod N)) := by
        ext x
        constructor
        · intro hx
          exact Finset.mem_univ x
        · intro hx
          rcases hEcover x with ⟨j, hj⟩
          exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, by simpa [EFin, hE_finite] using hj⟩
      have hE_disj : ((Finset.univ : Finset (Fin M)) : Set (Fin M)).PairwiseDisjoint EFin := by
        refine Finset.pairwiseDisjoint_iff.mpr ?_
        intro j hj k hk hnonempty
        rcases hnonempty with ⟨x, hx⟩
        have hxj : x ∈ E j := by simpa [EFin, hE_finite] using (Finset.mem_inter.mp hx).1
        have hxk : x ∈ E k := by simpa [EFin, hE_finite] using (Finset.mem_inter.mp hx).2
        by_contra hjk
        exact Set.disjoint_left.mp (hEdisj j k hjk) hxj hxk
      have hE_card_sum : (Finset.univ : Finset (ZMod N)).card = ∑ j : Fin M, (EFin j).card := by
        calc
          (Finset.univ : Finset (ZMod N)).card =
              ((Finset.univ : Finset (Fin M)).biUnion EFin).card := by rw [hE_biUnion]
          _ = ∑ j ∈ (Finset.univ : Finset (Fin M)), (EFin j).card := by
            exact Finset.card_biUnion (s := (Finset.univ : Finset (Fin M))) (t := EFin) hE_disj
          _ = ∑ j : Fin M, (EFin j).card := by simp
      have hpieceFin_disjoint : (T : Set (B × Fin M)).PairwiseDisjoint pieceFin := by
        refine Finset.pairwiseDisjoint_iff.mpr ?_
        intro p hpT q hqT hnonempty
        rcases hnonempty with ⟨x, hx⟩
        have hxp : x ∈ piece p := by simpa [pieceFin, hpiece_finite] using (Finset.mem_inter.mp hx).1
        have hxq : x ∈ piece q := by simpa [pieceFin, hpiece_finite] using (Finset.mem_inter.mp hx).2
        exact Set.pairwiseDisjoint_iff.mp hS_disjoint (hT_subset_S p hpT) (hT_subset_S q hqT)
          ⟨x, hxp, hxq⟩
      have hT_card_biUnion : (T.biUnion pieceFin).card = ∑ p ∈ T, (pieceFin p).card :=
        Finset.card_biUnion (s := T) (t := pieceFin) hpieceFin_disjoint
      have hT_union_eq : T.biUnion pieceFin = (Finset.univ : Finset (ZMod N)) := by
        ext x
        constructor
        · intro hx
          exact Finset.mem_univ x
        · intro hx
          obtain ⟨p, hpT, htp⟩ := hT_cover x
          exact Finset.mem_biUnion.mpr ⟨p, hpT, by simpa [pieceFin, hpiece_finite] using htp⟩
      have hT_card_univ : (Finset.univ : Finset (ZMod N)).card = ∑ p ∈ T, (pieceFin p).card := by
        rw [← hT_card_biUnion, hT_union_eq]
      have hpiece_card (p : B × Fin M) : (pieceFin p).card = (EFin p.2).card := by
        dsimp [pieceFin, EFin]
        change ((hpiece_finite p).toFinset).card = ((hE_finite p.2).toFinset).card
        rw [← Set.ncard_eq_toFinset_card (piece p) (hpiece_finite p),
          ← Set.ncard_eq_toFinset_card (E p.2) (hE_finite p.2)]
        have htrans : piece p = (fun x : ZMod N => (p.1 : G × ZMod N).2 + x) '' E p.2 := by
          change ({((p.1 : G × ZMod N).2)} : Set (ZMod N)) + E p.2 =
            (fun x : ZMod N => (p.1 : G × ZMod N).2 + x) '' E p.2
          rw [Set.singleton_add]
        rw [htrans]
        apply Set.ncard_image_of_injective
        intro x y hxy
        exact add_left_cancel hxy
      -- now obtain a piece with second index `i`
      have hex_i : ∃ p ∈ S, p.2 = i := by
        by_contra hno
        have hnoS : ∀ p ∈ S, p.2 ≠ i := by
          intro p hp hpi
          exact hno ⟨p, hp, hpi⟩
        have hnoT : ∀ p ∈ T, p.2 ≠ i := by
          intro p hp
          exact hnoS p (hT_subset_S p hp)
        let J : Finset (Fin M) := T.image (fun p : B × Fin M => p.2)
        have hJ_subset : J ⊆ (Finset.univ : Finset (Fin M)).erase i := by
          intro j hj
          rcases Finset.mem_image.mp hj with ⟨p, hpT, hpj⟩
          exact Finset.mem_erase.mpr ⟨by simpa [hpj] using hnoT p hpT, Finset.mem_univ j⟩
        have hsum_piece_as_E : ∑ p ∈ T, (pieceFin p).card = ∑ p ∈ T, (EFin p.2).card := by
          refine Finset.sum_congr rfl ?_
          intro p hp
          exact hpiece_card p
        have hsum_image : ∑ j ∈ J, (EFin j).card = ∑ p ∈ T, (EFin p.2).card := by
          exact Finset.sum_image (s := T) (g := fun p : B × Fin M => p.2)
            (f := fun j : Fin M => (EFin j).card) hT_inj_j
        have hJ_sum_eq_N : ∑ j ∈ J, (EFin j).card = (Finset.univ : Finset (ZMod N)).card := by
          calc
            ∑ j ∈ J, (EFin j).card = ∑ p ∈ T, (EFin p.2).card := hsum_image
            _ = ∑ p ∈ T, (pieceFin p).card := hsum_piece_as_E.symm
            _ = (Finset.univ : Finset (ZMod N)).card := hT_card_univ.symm
        have hEi_pos : 0 < (EFin i).card := by
          rw [Finset.card_pos]
          rcases hEne i with ⟨x, hx⟩
          exact ⟨x, by simpa [EFin, hE_finite] using hx⟩
        have hJ_disj_i : Disjoint J {i} := by
          rw [Finset.disjoint_singleton_right]
          intro hi
          rcases Finset.mem_image.mp hi with ⟨p, hpT, rfl⟩
          exact hnoT p hpT rfl
        have hsum_union : ∑ j ∈ J ∪ {i}, (EFin j).card =
            (∑ j ∈ J, (EFin j).card) + (EFin i).card := by
          rw [Finset.sum_union hJ_disj_i]
          simp
        have hle : (∑ j ∈ J, (EFin j).card) + (EFin i).card ≤
            ∑ j ∈ (Finset.univ : Finset (Fin M)), (EFin j).card := by
          rw [← hsum_union]
          exact Finset.sum_le_sum_of_subset (Finset.subset_univ (J ∪ {i}))
        have hNcard : (Finset.univ : Finset (ZMod N)).card = N := by
          rw [Finset.card_univ, ZMod.card]
        have hle' : N + (EFin i).card ≤ N := by
          simpa [hJ_sum_eq_N, hE_card_sum, hNcard] using hle
        omega
      rcases hex_i with ⟨p, hpS, hpi⟩
      rcases hpS with ⟨f, hfF, hg⟩
      refine ⟨(⟨π p.1, ?_⟩, ⟨f, ?_⟩), ?_⟩
      · exact ⟨p.1.1, p.1.2, rfl⟩
      · simpa [hpi] using hfF
      · simpa [π, hpi] using hg
  exact hA_complement

end

end Commons.PeriodicTiling