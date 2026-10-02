import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.RegVocab

/-!
# `Work.Deep.GKO.Abs.hallBipClean`

The matching-absorber form of Hall's condition for a bipartite pair after deleting `t` matchings:
`A` and `B` are disjoint, `Aj ⊆ A` and `Bj ⊆ B` have equal size, every `H`-edge of a large
`A`-`B` rectangle is a `K`-edge up to `t` deleted matchings, and every vertex of `Aj ∪ Bj` has
at least `ε * n` `K`-edges into the other side.  Then `K` contains a perfect matching between `Aj`
and `Bj`.

The proof is self-contained in this module (the sibling module `hallBip.lean` contains, besides
the same result, the unfinishable statement `hallBip` — false without the disjointness of `Aj` and
`Bj` — so a consumer must not import it).

Structure of the argument:

* `hallBipClean_hallCondition` — the counting core, a three-way case split.  Let `N` be the union
  of the `K`-neighbourhoods in `Bj` of the vertices of `S ⊆ Aj`.
  - if `|S| < ε n`, any `v ∈ S` already has `ε n` neighbours inside `N`;
  - if `ε n ≤ |S|` and still `ε n ≤ |Bj ∖ N|`, lower regularity on the rectangle `(S, Bj ∖ N)` —
    on which `K` has no edge at all — contradicts `t < q ε n`;
  - otherwise `|Bj ∖ N| < ε n`, and a vertex of `Bj ∖ N` has all its `K`-neighbours in
    `Aj ∖ S`, so `ε n ≤ |Aj| - |S|` and `|S| ≤ |N|`.
* `Finset.all_card_le_biUnion_card_iff_exists_injective` (Mathlib's Hall theorem) turns the Hall
  condition into an injective assignment `f : Aj → Bj`, which is a bijection because the two
  sides have equal size (this is where `Disjoint Aj Bj` is used: the `∃!` clauses must not see
  two partners, and the second `∃!` runs over `Bj`, whose partner must lie in `Aj`, not in `Bj`).
  The graph of the resulting bijection is the matching `P`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.Deep.GKO.Abs

/-! ## Counting helpers -/

/-- `crossEdges` counts ordered pairs, hence it is the sum over `A` of the degrees into `B`. -/
private theorem crossEdges_eq_sum_degIn {n : ℕ} (G : SimpleGraph (Fin n)) (A B : Finset (Fin n)) :
    Work.Deep.GKO.crossEdges G A B = ∑ a ∈ A, Work.Deep.GKO.degIn G a B := by
  unfold Work.Deep.GKO.crossEdges Work.Deep.GKO.degIn Work.Deep.GKO.nbrFinset
  rw [Finset.product_eq_sprod, Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.card_filter]

/-! ## The Hall condition -/

/-- **Hall's condition for the neighbourhoods in `K`.**  For every `S ⊆ Aj`, the union of the
`K`-neighbourhoods of the vertices of `S` inside `Bj` has at least `|S|` elements. -/
private theorem hallBipClean_hallCondition {n : ℕ} {A B Aj Bj : Finset (Fin n)}
    {H K : SimpleGraph (Fin n)} {q ε : ℝ} {t : ℕ}
    (hAjA : Aj ⊆ A) (hBjB : Bj ⊆ B) (hcard : Aj.card = Bj.card)
    (hlr : ∀ S : Finset (Fin n), S ⊆ A → ∀ T : Finset (Fin n), T ⊆ B →
      ε * (n : ℝ) ≤ (S.card : ℝ) → ε * (n : ℝ) ≤ (T.card : ℝ) →
      q * (S.card : ℝ) * (T.card : ℝ) ≤ (Work.Deep.GKO.crossEdges H S T : ℝ))
    (hKle : K ≤ H)
    (hrem : ∀ S : Finset (Fin n), S ⊆ Aj → ∀ T : Finset (Fin n), T ⊆ Bj →
      (Work.Deep.GKO.crossEdges H S T : ℝ)
        ≤ (Work.Deep.GKO.crossEdges K S T : ℝ) + (t : ℝ) * min (S.card : ℝ) (T.card : ℝ))
    (hdegA : ∀ v : Fin n, v ∈ Aj → ε * (n : ℝ) ≤ (Work.Deep.GKO.degIn K v Bj : ℝ))
    (hdegB : ∀ v : Fin n, v ∈ Bj → ε * (n : ℝ) ≤ (Work.Deep.GKO.degIn K v Aj : ℝ))
    (hε : 0 < ε) (hroomq : (t : ℝ) < q * ε * (n : ℝ)) :
    ∀ S : Finset (Fin n), S ⊆ Aj →
      S.card ≤ (S.biUnion (fun v => Work.Deep.GKO.nbrFinset K v Bj)).card := by
  classical
  intro S hSAj
  rcases S.eq_empty_or_nonempty with hS0 | hSne
  · simp [hS0]
  set N : Finset (Fin n) := S.biUnion (fun v => Work.Deep.GKO.nbrFinset K v Bj) with hNdef
  have hNB : N ⊆ Bj := by
    intro x hx
    rw [hNdef, Finset.mem_biUnion] at hx
    obtain ⟨v, -, hxv⟩ := hx
    exact Work.Deep.GKO.nbrFinset_subset K v Bj hxv
  have hqεn : 0 < q * ε * (n : ℝ) :=
    lt_of_le_of_lt (Nat.cast_nonneg t : (0 : ℝ) ≤ (t : ℝ)) hroomq
  have hqε : 0 < q * ε := pos_of_mul_pos_left hqεn (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))
  have hqpos : 0 < q := pos_of_mul_pos_left hqε hε.le
  have hnpos : 0 < (n : ℝ) := pos_of_mul_pos_right hqεn hqε.le
  have hεnpos : 0 < ε * (n : ℝ) := mul_pos hε hnpos
  by_cases hTbig : ε * (n : ℝ) ≤ ((Bj \ N).card : ℝ)
  · by_cases hSsmall : (S.card : ℝ) < ε * (n : ℝ)
    · -- `|S| < εn`: any `v ∈ S` has `≥ εn` neighbours, all of them inside `N`
      obtain ⟨v, hv⟩ := hSne
      have hsub : Work.Deep.GKO.nbrFinset K v Bj ⊆ N := by
        intro x hx
        rw [hNdef, Finset.mem_biUnion]
        exact ⟨v, hv, hx⟩
      have hle : ε * (n : ℝ) ≤ (N.card : ℝ) := by
        calc ε * (n : ℝ) ≤ (Work.Deep.GKO.degIn K v Bj : ℝ) := hdegA v (hSAj hv)
          _ ≤ (N.card : ℝ) := by
              rw [Work.Deep.GKO.degIn]
              exact_mod_cast Finset.card_le_card hsub
      have : (S.card : ℝ) ≤ (N.card : ℝ) := le_trans hSsmall.le hle
      exact_mod_cast this
    · -- `εn ≤ |S|`: lower regularity on `(S, Bj ∖ N)` contradicts `t < qεn`
      exfalso
      have hSε : ε * (n : ℝ) ≤ (S.card : ℝ) := not_lt.mp hSsmall
      have hlr' := hlr S (hSAj.trans hAjA) (Bj \ N) ((Finset.sdiff_subset).trans hBjB) hSε hTbig
      have hrem' := hrem S hSAj (Bj \ N) Finset.sdiff_subset
      have hzero : Work.Deep.GKO.crossEdges K S (Bj \ N) = 0 := by
        rw [crossEdges_eq_sum_degIn]
        refine Finset.sum_eq_zero (fun a ha => ?_)
        rw [Work.Deep.GKO.degIn, Work.Deep.GKO.nbrFinset, Finset.card_eq_zero,
          Finset.eq_empty_iff_forall_notMem]
        intro b hb
        rw [Finset.mem_filter] at hb
        obtain ⟨hbb, hab⟩ := hb
        have hbN : b ∈ N := by
          rw [hNdef, Finset.mem_biUnion]
          refine ⟨a, ha, ?_⟩
          rw [Work.Deep.GKO.mem_nbrFinset]
          exact ⟨(Finset.mem_sdiff.mp hbb).1, hab⟩
        exact (Finset.mem_sdiff.mp hbb).2 hbN
      rw [hzero, Nat.cast_zero, zero_add] at hrem'
      have hkey : q * (S.card : ℝ) * ((Bj \ N).card : ℝ)
          ≤ (t : ℝ) * min (S.card : ℝ) ((Bj \ N).card : ℝ) := le_trans hlr' hrem'
      have hTpos : 0 < ((Bj \ N).card : ℝ) := lt_of_lt_of_le hεnpos hTbig
      have hqS : q * (S.card : ℝ) ≤ (t : ℝ) := by
        have h1 : (q * (S.card : ℝ)) * ((Bj \ N).card : ℝ)
            ≤ (t : ℝ) * ((Bj \ N).card : ℝ) := by
          calc (q * (S.card : ℝ)) * ((Bj \ N).card : ℝ)
              = q * (S.card : ℝ) * ((Bj \ N).card : ℝ) := by ring
            _ ≤ (t : ℝ) * min (S.card : ℝ) ((Bj \ N).card : ℝ) := hkey
            _ ≤ (t : ℝ) * ((Bj \ N).card : ℝ) :=
                mul_le_mul_of_nonneg_left (min_le_right _ _) (Nat.cast_nonneg t)
        exact le_of_mul_le_mul_right h1 hTpos
      have hqS' : q * (ε * (n : ℝ)) ≤ q * (S.card : ℝ) :=
        mul_le_mul_of_nonneg_left hSε hqpos.le
      linarith [hroomq, hqS, hqS']
  · -- `|Bj ∖ N| < εn`: a vertex of `Bj ∖ N` has all its neighbours in `Aj ∖ S`
    have hTlt : ((Bj \ N).card : ℝ) < ε * (n : ℝ) := lt_of_not_ge hTbig
    rcases (Bj \ N).eq_empty_or_nonempty with h0 | ⟨w, hw⟩
    · have hsub : Bj ⊆ N := Finset.sdiff_eq_empty_iff_subset.mp h0
      have hcardN : N.card = Bj.card :=
        le_antisymm (Finset.card_le_card hNB) (Finset.card_le_card hsub)
      calc S.card ≤ Aj.card := Finset.card_le_card hSAj
        _ = Bj.card := hcard
        _ = N.card := hcardN.symm
    · obtain ⟨hwBj, hwN⟩ := Finset.mem_sdiff.mp hw
      have hsub : Work.Deep.GKO.nbrFinset K w Aj ⊆ Aj \ S := by
        intro x hx
        rw [Work.Deep.GKO.mem_nbrFinset] at hx
        refine Finset.mem_sdiff.mpr ⟨hx.1, fun hxS => hwN ?_⟩
        rw [hNdef, Finset.mem_biUnion]
        exact ⟨x, hxS, by
          rw [Work.Deep.GKO.mem_nbrFinset]
          exact ⟨hwBj, (K.adj_comm w x).mp hx.2⟩⟩
      have hAcard : ε * (n : ℝ) ≤ ((Aj \ S).card : ℝ) :=
        le_trans (hdegB w hwBj) (by
          rw [Work.Deep.GKO.degIn]
          exact_mod_cast Finset.card_le_card hsub)
      have hNcast : ((Bj \ N).card : ℝ) = (Bj.card : ℝ) - (N.card : ℝ) :=
        Finset.cast_card_sdiff hNB
      have hAjcast : ((Aj \ S).card : ℝ) = (Aj.card : ℝ) - (S.card : ℝ) :=
        Finset.cast_card_sdiff hSAj
      have hcardR : (Aj.card : ℝ) = (Bj.card : ℝ) := by exact_mod_cast hcard
      have hNgt : (S.card : ℝ) < (N.card : ℝ) := by linarith
      exact_mod_cast hNgt.le

/-! ## The requested statement (unchanged) -/

/-- Hall's condition for a bipartite pair after deleting matchings, and the resulting perfect
matching, in the form used by the matching absorber: `A` and `B` are disjoint, `Aj ⊆ A` and
`Bj ⊆ B` have equal size, every `H`-edge of a large `A`-`B` rectangle is an edge of `K` up to `t`
deleted matchings, and every vertex of `Aj ∪ Bj` has at least `ε * n` `K`-edges into the other
side.  Then `K` contains a perfect matching between `Aj` and `Bj`.

This is a copy of the already proved `Work.Deep.GKO.Abs.hallBip_of_disjAB` in
`Submission/Work/Deep/GKO/Abs/hallBip.lean`; the requested version lives in a fresh module because
that file also contains the unfinished statement `hallBip` (which is false without the
disjointness of `Aj` and `Bj`), so a consumer importing it inherits an unfinished proof. -/
theorem hallBipClean {n : ℕ} {A B Aj Bj : Finset (Fin n)} {H K : SimpleGraph (Fin n)}
    {q ε : ℝ} {t : ℕ}
    (hAB : Disjoint A B)
    (hAjA : Aj ⊆ A) (hBjB : Bj ⊆ B) (hcard : Aj.card = Bj.card)
    (hlr : ∀ S : Finset (Fin n), S ⊆ A → ∀ T : Finset (Fin n), T ⊆ B →
      ε * (n : ℝ) ≤ (S.card : ℝ) → ε * (n : ℝ) ≤ (T.card : ℝ) →
      q * (S.card : ℝ) * (T.card : ℝ) ≤ (Work.Deep.GKO.crossEdges H S T : ℝ))
    (hKle : K ≤ H)
    (hrem : ∀ S : Finset (Fin n), S ⊆ Aj → ∀ T : Finset (Fin n), T ⊆ Bj →
      (Work.Deep.GKO.crossEdges H S T : ℝ)
        ≤ (Work.Deep.GKO.crossEdges K S T : ℝ) + (t : ℝ) * min (S.card : ℝ) (T.card : ℝ))
    (hdegA : ∀ v : Fin n, v ∈ Aj → ε * (n : ℝ) ≤ (Work.Deep.GKO.degIn K v Bj : ℝ))
    (hdegB : ∀ v : Fin n, v ∈ Bj → ε * (n : ℝ) ≤ (Work.Deep.GKO.degIn K v Aj : ℝ))
    (hε : 0 < ε) (hroomq : (t : ℝ) < q * ε * (n : ℝ)) :
    ∃ P : SimpleGraph (Fin n), P ≤ K ∧
      (∀ u v : Fin n, P.Adj u v → (u ∈ Aj ∧ v ∈ Bj) ∨ (u ∈ Bj ∧ v ∈ Aj)) ∧
      (∀ v : Fin n, v ∈ Aj → ∃! w : Fin n, w ∈ Bj ∧ P.Adj v w) ∧
      (∀ v : Fin n, v ∈ Bj → ∃! w : Fin n, w ∈ Aj ∧ P.Adj v w) := by
  classical
  have hhall := hallBipClean_hallCondition hAjA hBjB hcard hlr hKle hrem hdegA hdegB hε hroomq
  -- the union of the neighbourhoods of `s` is that of the image of `s` in `Aj`
  have hbiUnion : ∀ s : Finset {v : Fin n // v ∈ Aj},
      (s.biUnion fun x => Work.Deep.GKO.nbrFinset K x.1 Bj)
        = (s.image Subtype.val).biUnion (fun v => Work.Deep.GKO.nbrFinset K v Bj) := by
    intro s
    ext y
    constructor
    · intro hy
      rw [Finset.mem_biUnion] at hy ⊢
      obtain ⟨a, ha, hya⟩ := hy
      exact ⟨a.1, Finset.mem_image.mpr ⟨a, ha, rfl⟩, hya⟩
    · intro hy
      rw [Finset.mem_biUnion] at hy ⊢
      obtain ⟨v, hv, hyv⟩ := hy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv
      exact ⟨a, ha, hyv⟩
  -- Hall's theorem gives an injective assignment on `Aj`
  obtain ⟨f, hfinj, hfmem⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective
      (fun (x : {v : Fin n // v ∈ Aj}) => Work.Deep.GKO.nbrFinset K x.1 Bj)).mp (fun s => by
    have hs := hhall (s.image Subtype.val) (by
      intro x hx
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
      exact v.2)
    rw [Finset.card_image_of_injective _ Subtype.val_injective] at hs
    rwa [hbiUnion s])
  have hfBj : ∀ x : {v : Fin n // v ∈ Aj}, f x ∈ Bj := fun x =>
    (Work.Deep.GKO.mem_nbrFinset.mp (hfmem x)).1
  have hfadj : ∀ x : {v : Fin n // v ∈ Aj}, K.Adj x.1 (f x) := fun x =>
    (Work.Deep.GKO.mem_nbrFinset.mp (hfmem x)).2
  -- the assignment is a bijection `Aj ≃ Bj`
  let σ : {v : Fin n // v ∈ Aj} → {w : Fin n // w ∈ Bj} :=
    fun x => ⟨f x, hfBj x⟩
  have hσinj : Function.Injective σ := by
    intro x y hxy
    exact hfinj (Subtype.ext_iff.mp hxy)
  have hcardσ : Fintype.card {v : Fin n // v ∈ Aj} = Fintype.card {w : Fin n // w ∈ Bj} := by
    rw [Fintype.card_coe, Fintype.card_coe, hcard]
  have hσsurj : Function.Surjective σ :=
    ((Fintype.bijective_iff_injective_and_card σ).mpr ⟨hσinj, hcardσ⟩).2
  -- the matching, as a function on all of `Fin n`
  let g : Fin n → Fin n := fun v => if h : v ∈ Aj then f ⟨v, h⟩ else v
  have hgBj : ∀ v (hv : v ∈ Aj), g v ∈ Bj := by
    intro v hv
    simp only [g, dif_pos hv]
    exact hfBj ⟨v, hv⟩
  have hgadj : ∀ v (hv : v ∈ Aj), K.Adj v (g v) := by
    intro v hv
    simp only [g, dif_pos hv]
    exact hfadj ⟨v, hv⟩
  have hnotmem : ∀ ⦃x : Fin n⦄, x ∈ Aj → x ∉ Bj :=
    Finset.disjoint_left.mp (hAB.mono hAjA hBjB)
  refine ⟨{ Adj := fun u v => (u ∈ Aj ∧ v = g u) ∨ (v ∈ Aj ∧ u = g v)
            symm := Std.Symm.mk (fun u v h =>
              h.elim (fun h1 => Or.inr h1) (fun h2 => Or.inl h2))
            loopless := Std.Irrefl.mk (fun u h => by
              rcases h with ⟨hu, hueq⟩ | ⟨hu, hueq⟩
              · have hg := hgadj u hu
                rw [← hueq] at hg
                exact K.loopless.irrefl u hg
              · have hg := hgadj u hu
                rw [← hueq] at hg
                exact K.loopless.irrefl u hg) },
    ?_, ?_, ?_, ?_⟩
  · -- `P ≤ K`
    intro u v h
    rcases h with ⟨hu, hv⟩ | ⟨hv, hu⟩
    · rw [hv]; exact hgadj u hu
    · rw [hu]; exact (hgadj v hv).symm
  · -- every edge joins `Aj` to `Bj`
    intro u v h
    rcases h with ⟨hu, hv⟩ | ⟨hv, hu⟩
    · exact Or.inl ⟨hu, hv ▸ hgBj u hu⟩
    · exact Or.inr ⟨hu.symm ▸ hgBj v hv, hv⟩
  · -- every `v ∈ Aj` has exactly one partner in `Bj`
    intro v hv
    refine ⟨g v, ⟨hgBj v hv, Or.inl ⟨hv, rfl⟩⟩, ?_⟩
    intro w hw
    rcases hw with ⟨hwBj, hwadj⟩
    rcases hwadj with ⟨-, hwge⟩ | ⟨hwAj, -⟩
    · exact hwge
    · exact absurd hwBj (hnotmem hwAj)
  · -- every `v ∈ Bj` has exactly one partner in `Aj`
    intro v hv
    obtain ⟨x, hx⟩ := hσsurj ⟨v, hv⟩
    have hfx : f x = v := congrArg Subtype.val hx
    have hgx : g x.1 = v := by
      have h1 : g x.1 = f x := by simp only [g, dif_pos x.2]
      rw [h1, hfx]
    refine ⟨x.1, ⟨x.2, Or.inr ⟨x.2, hgx.symm⟩⟩, ?_⟩
    intro w hw
    rcases hw with ⟨hwAj, hwadj⟩
    rcases hwadj with ⟨hvAj, -⟩ | ⟨-, hvge⟩
    · exact absurd hv (hnotmem hvAj)
    · have hgw : g w = f ⟨w, hwAj⟩ := by simp only [g, dif_pos hwAj]
      have h1 : f ⟨w, hwAj⟩ = v := by
        rw [← hgw, hvge]
      exact congrArg Subtype.val (hfinj (h1.trans hfx.symm))

end Work.Deep.GKO.Abs
