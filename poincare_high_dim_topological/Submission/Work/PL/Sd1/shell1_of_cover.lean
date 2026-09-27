import Mathlib
import Submission.Work.PL.Sd1.Red
import Submission.Work.PL.Sd1.Defs
import Submission.Work.PL.Sd1.Witness
import Submission.Work.PL.Sd1.Geom
import Submission.Work.PL.Sd1.face_inter
import Submission.Work.PL.Sd1.crit_to_idx
import Submission.Work.PL.Sd1.splitOf_nonempty
import Submission.Work.PL.Shell.face_trace
import Submission.Work.PL.Shell.simp_inter_erase_eq_face
import Submission.Work.PL.Shell.simp_inter_simp_sameIdx
import Submission.Work.PL.Shell.flagEnum_mem
import Submission.Work.PL.Shell.exists_flag_contains
import Submission.Work.PL.Shell.flagEnum_sorted
import Submission.Work.PL.Shell.convexHull_inter_bary
import Submission.Work.PL.Shell.bary_inj

/-!
# The `r = 1` shelling of the barycentric subdivision of a simplex, given the cover

`Work.PL.Sd1.shell1_of_cover` assembles the `r = 1` shelling statement
`Work.PL.Sd1.Shell1` from

* the non-emptiness and properness of the attaching set,
* the trace identity for the subdivision simplex of a flag, which is the content of
  `Work.PL.Shell.face_trace` (characterising which faces of the flag simplex lie in the
  floor `B` or in the simplices of the strictly earlier flags) combined with the index
  criterion `Work.PL.Sd1.crit_to_idx`,
* `Work.PL.Sd1.flagEnum_nodup` for the list of flags, and
* the covering hypothesis `hcover` for the last conjunct.

The trace identity is proved here in the sharp form
`simp (prefixes l) ∩ (B ∪ earlier) = ⋃_{k ∈ wit l} simp ((prefixes l) \ {bary (prefAt l k)})`
where `wit l` is the index set of the attaching set (`Work.PL.Sd1.wit`), and then
translated to the attaching set `Work.PL.Shell.splitOf` by
`Work.PL.Sd1.splitOf_eq_wit_image`.

The intersection `simp (prefixes l) ∩ simp (Δ \ {w})` of the flag simplex with a facet of the
ambient simplex is `Work.PL.Shell.simp_inter_erase_eq_face`, and the intersection of the
simplices of two flags is `Work.PL.Shell.simp_inter_simp_sameIdx`; both are used to turn a
point of the trace into a face of the flag simplex to which `face_trace` applies.
-/

open Set Metric Finset
open scoped BigOperators

namespace Work.PL.Sd1

noncomputable section

variable {N : ℕ}

/-! ### Elementary size facts -/

/-- A non-empty proper subset leaves at least two vertices. -/
private theorem two_le_card_of_ssubset {Δ T : Finset (PL.E N)} (hT₁ : T.Nonempty)
    (hT₂ : T ⊂ Δ) : 2 ≤ Δ.card := by
  obtain ⟨w₀, hw₀T, hw₀sub⟩ := Finset.ssubset_iff.mp hT₂
  have hTsub : T ⊆ Δ := fun x hx => hw₀sub (Finset.mem_insert_of_mem hx)
  have hw₀Δ : w₀ ∈ Δ := hw₀sub (Finset.mem_insert_self w₀ T)
  have hsub' : T ⊂ Δ := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hTsub, ?_⟩
    intro h
    exact hw₀T (h ▸ hw₀Δ)
  have h1 : T.card < Δ.card := Finset.card_lt_card hsub'
  have h2 : 0 < T.card := Finset.card_pos.mpr hT₁
  omega

/-- The `Nodup` list of vertices `l` is non-empty as soon as `T ⊆ Δ` is non-empty. -/
private theorem ne_nil_of_card {Δ T : Finset (PL.E N)} {l : List (PL.E N)}
    (hld : l.toFinset = Δ) (hT₁ : T.Nonempty) (hT₂ : T ⊂ Δ) : l ≠ [] := by
  obtain ⟨w₀, hw₀T, hw₀sub⟩ := Finset.ssubset_iff.mp hT₂
  have hw₀Δ : w₀ ∈ Δ := hw₀sub (Finset.mem_insert_self w₀ T)
  intro hcon
  rw [hcon] at hld
  rw [List.toFinset_nil] at hld
  exact Finset.notMem_empty w₀ (by rw [hld]; exact hw₀Δ)

/-- The last vertex of a `Nodup` list does not occur in any prefix set that stops before it. -/
private theorem getLast_notMem_prefAt {l : List (PL.E N)} (hl : l.Nodup) {v : PL.E N}
    (hv : l.getLast? = some v) {j : ℕ} (hj : j + 1 < l.length) :
    v ∉ Work.PL.Shell.prefAt l j := by
  intro hcon
  rw [Work.PL.Shell.prefAt, List.mem_toFinset, List.mem_take_iff_getElem] at hcon
  obtain ⟨i, hi, hiv⟩ := hcon
  have hi' : i < l.length := lt_of_lt_of_le hi (Nat.min_le_right _ _)
  have hsome_i : l[i]? = some v := by rw [List.getElem?_eq_getElem hi', hiv]
  have hsome_last : l[l.length - 1]? = some v := by
    rw [← List.getLast?_eq_getElem?]; exact hv
  have hidx : i = l.length - 1 :=
    (List.Nodup.getElem?_inj (by omega : i < l.length) hl).mp (by rw [hsome_i, hsome_last])
  omega

/-- A union over the image of a finite set is the union over the source. -/
private theorem iUnion_image_eq {N : ℕ} (s : Finset ℕ) (f : ℕ → PL.E N)
    (g : PL.E N → Set (PL.E N)) :
    (⋃ w ∈ s.image f, g w) = ⋃ k ∈ s, g (f k) := by
  ext x
  simp only [Set.mem_iUnion, Finset.mem_image]
  constructor
  · rintro ⟨w, ⟨k, hk, rfl⟩, hx⟩
    exact ⟨k, hk, hx⟩
  · rintro ⟨k, hk, hx⟩
    exact ⟨f k, ⟨k, hk, rfl⟩, hx⟩

/-! ### Local copies of two facts about the prefix chain

`Work.PL.Shell.prefixes_subset_toFinset` and `Work.PL.Shell.prefixes_nonempty` are declared
both in `Submission.Work.PL.Shell.cover_bary` and in `Submission.Work.PL.Shell.face_trace`
(with different signatures), so *no* module importing both can be built; the local copies
below keep this file independent of that (pre-existing) clash.  The clash still affects any
module that reaches both, e.g. `Submission.Work.PL.Shell.Main`, which imports
`Work.PL.Shell.sd_iter_shelling_strong` (and with it this file, hence `face_trace`) together
with `Work.PL.Shell.shellOrd_mem_sdIter` (hence `cover_bary`); deleting one of the two
duplicate declarations repairs it.  -/

/-- Every prefix set consists of vertices of the list. -/
private theorem prefixes_subset_toFinset_aux {l : List (PL.E N)} :
    ∀ A ∈ Work.PL.Shell.prefixes l, A ⊆ l.toFinset := by
  intro A hA
  obtain ⟨k, hk, rfl⟩ := Work.PL.Sd1.mem_prefixes_iff'.mp hA
  exact Work.PL.Shell.prefAt_subset_toFinset

/-- Every prefix set of a `Nodup` list is non-empty. -/
private theorem prefixes_nonempty_aux {l : List (PL.E N)} (hl : l.Nodup) :
    ∀ A ∈ Work.PL.Shell.prefixes l, A.Nonempty := by
  intro A hA
  obtain ⟨k, hk, rfl⟩ := Work.PL.Sd1.mem_prefixes_iff'.mp hA
  exact Work.PL.Shell.prefAt_nonempty hl hk

/-- The `j`-th prefix set is a member of the prefix chain. -/
private theorem prefAt_mem_prefixes_aux {l : List (PL.E N)} {j : ℕ} (hj : j < l.length) :
    Work.PL.Shell.prefAt l j ∈ Work.PL.Shell.prefixes l :=
  Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, rfl⟩

/-! ### `splitOf` as the image of its index set -/

/-- The attaching set is the image of the index set `wit` under the centroid map. -/
private theorem splitOf_eq_wit_image {Δ T : Finset (PL.E N)} (rk : PL.E N → ℕ)
    {l : List (PL.E N)} (hl : l.Nodup) (hlt : l.toFinset = Δ) (hne : l ≠ []) :
    Work.PL.Shell.splitOf Δ T rk l =
      (wit T rk l).image (fun j => Work.PL.Shell.bary (Work.PL.Shell.prefAt l j)) := by
  classical
  have hlast : Work.PL.Shell.prefAt l (l.length - 1) = Δ := by
    rw [Work.PL.Shell.prefAt, Nat.sub_add_cancel (by
      have : 0 < l.length := List.length_pos_iff.mpr hne
      omega), List.take_length, hlt]
  simp only [Work.PL.Shell.splitOf, wit]
  by_cases hc : ∃ v, l.getLast? = some v ∧ v ∈ T
  · simp only [hc, if_true, Finset.image_insert, hlast]
  · simp only [hc, if_false]

/-! ### A vertex of the subdivision simplex outside the attaching set -/

/-- Some index of the flag is not in the attaching index set `wit`. -/
private theorem exists_notMem_wit {N : ℕ} {Δ T : Finset (PL.E N)}
    (vs : List (PL.E N)) (rk : PL.E N → ℕ)
    (hvs : vs.toFinset = Δ) (hvs' : vs.Nodup) (hrk : (vs.map rk).Pairwise (· < ·))
    (hT₁ : T.Nonempty) (hT₂ : T ⊂ Δ)
    (hT : ∀ u ∈ T, ∀ w ∈ Δ, w ∉ T → rk u < rk w)
    {l : List (PL.E N)} (hl : l ∈ Work.PL.Shell.flagEnum vs) :
    ∃ k, k ∈ Finset.range l.length ∧ k ∉ wit T rk l := by
  classical
  have hlperm : l.Perm vs := Work.PL.Shell.flagEnum_mem.mp hl
  have hlnod : l.Nodup := hlperm.nodup_iff.mpr hvs'
  have hlΔ : l.toFinset = Δ := by rw [List.toFinset_eq_of_perm _ _ hlperm, hvs]
  have hlne : l ≠ [] := ne_nil_of_card hlΔ hT₁ hT₂
  have hlpos : 0 < l.length := List.length_pos_iff.mpr hlne
  by_cases hlastT : ∃ v, l.getLast? = some v ∧ v ∈ T
  · obtain ⟨w₀, hw₀T, hw₀sub⟩ := Finset.ssubset_iff.mp hT₂
    have hw₀Δ : w₀ ∈ Δ := hw₀sub (Finset.mem_insert_self w₀ T)
    have hw₀l : w₀ ∈ l := by rw [← List.mem_toFinset, hlΔ]; exact hw₀Δ
    obtain ⟨t₀, ht₀lt, ht₀eq⟩ := List.getElem_of_mem hw₀l
    set S : Finset ℕ :=
      (Finset.range l.length).filter (fun t => ∃ u, l[t]? = some u ∧ u ∉ T) with hSdef
    have hSne : S.Nonempty := by
      refine ⟨t₀, ?_⟩
      rw [hSdef, Finset.mem_filter]
      exact ⟨Finset.mem_range.mpr ht₀lt, w₀, by rw [List.getElem?_eq_getElem ht₀lt, ht₀eq],
        hw₀T⟩
    set k := S.max' hSne with hkdef
    have hkS : k ∈ S := by rw [hkdef]; exact Finset.max'_mem S hSne
    have hkmax : ∀ t ∈ S, t ≤ k := by
      intro t ht
      rw [hkdef]
      exact Finset.le_max' S t ht
    rw [hSdef] at hkS
    obtain ⟨hk_lt, u, hu, huT⟩ := Finset.mem_filter.mp hkS
    have hklen : k < l.length := Finset.mem_range.mp hk_lt
    have hdmem : k ≠ l.length - 1 := by
      intro heq
      obtain ⟨v, hv, hvT⟩ := hlastT
      have h2 : l[l.length - 1]? = some v := by
        rw [← List.getLast?_eq_getElem?]; exact hv
      rw [heq] at hu
      have huv : u = v := Option.some.inj (hu.symm.trans h2)
      exact huT (huv ▸ hvT)
    have hk1 : k + 1 < l.length := by omega
    have hnextT : ∀ u', l[k + 1]? = some u' → u' ∈ T := by
      intro u' hu'
      by_contra hu'T
      have hmem : k + 1 ∈ S := by
        rw [hSdef, Finset.mem_filter]
        exact ⟨Finset.mem_range.mpr hk1, u', hu', hu'T⟩
      have hle := hkmax (k + 1) hmem
      omega
    have hnotasc : k ∉ Work.PL.Shell.ascIdx rk l := by
      intro hasc
      have hlt1 : rk (l[k]'hklen) < rk (l[k + 1]'hk1) :=
        (Work.PL.Shell.ascIdx_mem.mp hasc).2
      have hu_eq : l[k]'hklen = u := by
        have h := List.getElem?_eq_getElem (l := l) (i := k) hklen
        rw [h] at hu
        exact Option.some.inj hu
      obtain ⟨u', hu'⟩ : ∃ u', l[k + 1]? = some u' :=
        ⟨l[k + 1]'hk1, List.getElem?_eq_getElem hk1⟩
      have hu'_eq : l[k + 1]'hk1 = u' := by
        have h := List.getElem?_eq_getElem (l := l) (i := k + 1) hk1
        rw [h] at hu'
        exact Option.some.inj hu'
      have huΔ : u ∈ Δ := by
        rw [← hlΔ, List.mem_toFinset]
        exact hu_eq ▸ List.getElem_mem hklen
      have hcontr := hT u' (hnextT u' hu') u huΔ huT
      rw [hu_eq, hu'_eq] at hlt1
      omega
    refine ⟨k, Finset.mem_range.mpr hklen, ?_⟩
    rw [mem_wit]
    rintro (hasc | ⟨-, heq⟩)
    · exact hnotasc hasc
    · exact hdmem heq
  · refine ⟨l.length - 1, Finset.mem_range.mpr (Nat.sub_lt hlpos Nat.one_pos), ?_⟩
    rw [wit, if_neg hlastT]
    exact last_notMem_ascIdx rk l

/-- The attaching set is a proper subset of the vertex set of the subdivision simplex. -/
private theorem wit_image_ssubset {N : ℕ} {Δ T : Finset (PL.E N)}
    (hΔ : AffineIndependent ℝ ((↑) : Δ → PL.E N)) (rk : PL.E N → ℕ)
    {l : List (PL.E N)} (hlnod : l.Nodup) (hlΔ : l.toFinset = Δ)
    (hk : ∃ k, k ∈ Finset.range l.length ∧ k ∉ wit T rk l) :
    (wit T rk l).image (fun j => Work.PL.Shell.bary (Work.PL.Shell.prefAt l j)) ⊂
      (Work.PL.Shell.prefixes l).image Work.PL.Shell.bary := by
  obtain ⟨k, hkmem, hkwit⟩ := hk
  have hsub : (wit T rk l).image (fun j => Work.PL.Shell.bary (Work.PL.Shell.prefAt l j)) ⊆
      (Work.PL.Shell.prefixes l).image Work.PL.Shell.bary := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (by simpa using hx)
    exact Finset.mem_image.mpr ⟨Work.PL.Shell.prefAt l j,
      prefAt_mem_prefixes_aux
        (Finset.mem_range.mp (wit_subset_range T rk l hj)), rfl⟩
  have hinj : Set.InjOn (fun j => Work.PL.Shell.bary (Work.PL.Shell.prefAt l j))
      ↑(wit T rk l) := by
    intro a ha b hb hab
    have hal : a < l.length := Finset.mem_range.mp (wit_subset_range T rk l (by simpa using ha))
    have hbl : b < l.length := Finset.mem_range.mp (wit_subset_range T rk l (by simpa using hb))
    refine Work.PL.Shell.prefAt_inj hlnod hal hbl (Work.PL.Shell.bary_inj hΔ ?_ ?_ ?_ ?_ hab)
    · exact Work.PL.Shell.prefAt_nonempty hlnod hal
    · exact Work.PL.Shell.prefAt_nonempty hlnod hbl
    · rw [← hlΔ]; exact Work.PL.Shell.prefAt_subset_toFinset
    · rw [← hlΔ]; exact Work.PL.Shell.prefAt_subset_toFinset
  have hcardwit :
      ((wit T rk l).image (fun j => Work.PL.Shell.bary (Work.PL.Shell.prefAt l j))).card
        = (wit T rk l).card := Finset.card_image_of_injOn hinj
  have hcardpref : (Work.PL.Shell.prefixes l).card = l.length := by
    rw [Work.PL.Shell.prefixes]
    rw [Finset.card_image_of_injOn]
    · simp
    · intro a ha b hb hab
      exact Work.PL.Shell.prefAt_inj hlnod (Finset.mem_range.mp ha) (Finset.mem_range.mp hb) hab
  have hcardV : ((Work.PL.Shell.prefixes l).image Work.PL.Shell.bary).card
      = (Work.PL.Shell.prefixes l).card := by
    refine Finset.card_image_of_injOn ?_
    intro A hA B hB hAB
    exact Work.PL.Shell.bary_inj hΔ (prefixes_nonempty_aux hlnod A (by simpa using hA))
      (prefixes_nonempty_aux hlnod B (by simpa using hB))
      (by rw [← hlΔ]; exact prefixes_subset_toFinset_aux A (by simpa using hA))
      (by rw [← hlΔ]; exact prefixes_subset_toFinset_aux B (by simpa using hB)) hAB
  have hwit_lt : (wit T rk l).card < l.length := by
    have hss : wit T rk l ⊂ Finset.range l.length := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨wit_subset_range T rk l, ?_⟩
      intro heq
      exact hkwit (heq ▸ hkmem)
    have hc := Finset.card_lt_card hss
    simpa using hc
  refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub, ?_⟩
  intro heq
  have h1 := congrArg Finset.card heq
  rw [hcardwit, hcardV, hcardpref] at h1
  omega

/-- The attaching set is a proper subset of the vertex set of the subdivision simplex. -/
private theorem splitOf_ssubset_here {N : ℕ} {Δ T : Finset (PL.E N)}
    (hΔ : AffineIndependent ℝ ((↑) : Δ → PL.E N))
    (vs : List (PL.E N)) (rk : PL.E N → ℕ)
    (hvs : vs.toFinset = Δ) (hvs' : vs.Nodup) (hrk : (vs.map rk).Pairwise (· < ·))
    (hT₁ : T.Nonempty) (hT₂ : T ⊂ Δ)
    (hT : ∀ u ∈ T, ∀ w ∈ Δ, w ∉ T → rk u < rk w)
    {l : List (PL.E N)} (hl : l ∈ Work.PL.Shell.flagEnum vs) :
    Work.PL.Shell.splitOf Δ T rk l ⊂ (Work.PL.Shell.prefixes l).image Work.PL.Shell.bary := by
  have hlperm : l.Perm vs := Work.PL.Shell.flagEnum_mem.mp hl
  have hlnod : l.Nodup := hlperm.nodup_iff.mpr hvs'
  have hlΔ : l.toFinset = Δ := by rw [List.toFinset_eq_of_perm _ _ hlperm, hvs]
  have hlne : l ≠ [] := ne_nil_of_card hlΔ hT₁ hT₂
  rw [splitOf_eq_wit_image rk hlnod hlΔ hlne]
  exact wit_image_ssubset hΔ rk hlnod hlΔ (exists_notMem_wit vs rk hvs hvs' hrk hT₁ hT₂ hT hl)

/-! ### The trace identity -/

/-- The trace of the floor and of the strictly earlier simplices on the subdivision simplex
of the flag `l`, indexed by the attaching index set `wit`. -/
private theorem wit_trace {N : ℕ} {Δ T : Finset (PL.E N)}
    (hΔ : AffineIndependent ℝ ((↑) : Δ → PL.E N))
    (vs : List (PL.E N)) (rk : PL.E N → ℕ)
    (hvs : vs.toFinset = Δ) (hvs' : vs.Nodup) (hrk : (vs.map rk).Pairwise (· < ·))
    (hT₁ : T.Nonempty) (hT₂ : T ⊂ Δ)
    (hT : ∀ u ∈ T, ∀ w ∈ Δ, w ∉ T → rk u < rk w)
    {l : List (PL.E N)} (hl : l ∈ Work.PL.Shell.flagEnum vs) :
    PL.simp ((Work.PL.Shell.prefixes l).image Work.PL.Shell.bary) ∩
        ((⋃ w ∈ T, PL.simp (Δ.erase w)) ∪
          ⋃ j ∈ Finset.range ((Work.PL.Shell.flagEnum vs).idxOf l),
            PL.simp ((Work.PL.Shell.prefixes ((Work.PL.Shell.flagEnum vs).getD j [])).image
              Work.PL.Shell.bary)) =
      ⋃ k ∈ wit T rk l,
        PL.simp (((Work.PL.Shell.prefixes l).image Work.PL.Shell.bary).erase
          (Work.PL.Shell.bary (Work.PL.Shell.prefAt l k))) := by
  classical
  have hlperm : l.Perm vs := Work.PL.Shell.flagEnum_mem.mp hl
  have hlnod : l.Nodup := hlperm.nodup_iff.mpr hvs'
  have hlΔ : l.toFinset = Δ := by rw [List.toFinset_eq_of_perm _ _ hlperm, hvs]
  have hlen : 1 < l.length := by
    have h1 : l.length = l.toFinset.card := (List.toFinset_card_of_nodup hlnod).symm
    have h2 : 2 ≤ Δ.card := two_le_card_of_ssubset hT₁ hT₂
    rw [hlΔ] at h1
    omega
  have hTΔ : T ⊆ Δ := hT₂.1
  -- a facet opposite a vertex of the attaching set is covered by the floor or an earlier simplex
  have hfac : ∀ k ∈ wit T rk l, Work.PL.Sd1.face l (Work.PL.Sd1.flagIdx l \ {k}) ⊆
      (⋃ w ∈ T, PL.simp (Δ.erase w)) ∪
        ⋃ j ∈ Finset.range ((Work.PL.Shell.flagEnum vs).idxOf l),
          PL.simp ((Work.PL.Shell.prefixes ((Work.PL.Shell.flagEnum vs).getD j [])).image
            Work.PL.Shell.bary) := by
    intro k hkwit
    have hklt : k < l.length := Finset.mem_range.mp (wit_subset_range T rk l hkwit)
    have hJsub : Work.PL.Sd1.flagIdx l \ {k} ⊆ Work.PL.Sd1.flagIdx l := Finset.sdiff_subset
    have hJne : (Work.PL.Sd1.flagIdx l \ {k}).Nonempty := by
      refine Finset.card_pos.mp ?_
      rw [Finset.sdiff_singleton_eq_erase,
        Finset.card_erase_of_mem (show k ∈ Work.PL.Sd1.flagIdx l from
          Finset.mem_range.mpr hklt)]
      rw [Work.PL.Sd1.flagIdx, Finset.card_range]
      omega
    rcases mem_wit.mp hkwit with hkasc | ⟨hcond, hkeq⟩
    · refine (Work.PL.Shell.face_trace hΔ vs rk hvs hrk hT₁ hT₂ hT hl hJne
        (fun j hj => Finset.mem_range.mp (hJsub hj))).mpr (Or.inr ?_)
      intro hsub
      exact (Finset.mem_sdiff.mp (hsub hkasc)).2 (Finset.mem_singleton_self k)
    · obtain ⟨v, hvlast, hvT⟩ := hcond
      refine (Work.PL.Shell.face_trace hΔ vs rk hvs hrk hT₁ hT₂ hT hl hJne
        (fun j hj => Finset.mem_range.mp (hJsub hj))).mpr (Or.inl ⟨v, hvT, ?_⟩)
      have hJ'sub : Work.PL.Sd1.flagIdx l \ {k} ⊆ Finset.range (l.length - 1) := by
        intro j hj
        obtain ⟨hj1, hj2⟩ := Finset.mem_sdiff.mp hj
        rw [Work.PL.Sd1.flagIdx] at hj1
        rw [Finset.mem_singleton] at hj2
        rw [Finset.mem_range] at hj1 ⊢
        omega
      have hmaxlt : (Work.PL.Sd1.flagIdx l \ {k}).max' hJne < l.length - 1 :=
        Finset.mem_range.mp (hJ'sub (Finset.max'_mem _ hJne))
      exact getLast_notMem_prefAt hlnod hvlast (by omega)
  have htriv : ∀ k ∈ wit T rk l,
      PL.simp (((Work.PL.Shell.prefixes l).image Work.PL.Shell.bary).erase
        (Work.PL.Shell.bary (Work.PL.Shell.prefAt l k))) =
      Work.PL.Sd1.face l (Work.PL.Sd1.flagIdx l \ {k}) :=
    fun k hk => Work.PL.Sd1.simp_erase_eq_face hΔ hlnod hlΔ
      (Finset.mem_range.mp (wit_subset_range T rk l hk))
  -- the attaching union is contained in the trace
  have hfacets : (⋃ k ∈ wit T rk l,
      PL.simp (((Work.PL.Shell.prefixes l).image Work.PL.Shell.bary).erase
        (Work.PL.Shell.bary (Work.PL.Shell.prefAt l k)))) ⊆
      PL.simp ((Work.PL.Shell.prefixes l).image Work.PL.Shell.bary) ∩
        ((⋃ w ∈ T, PL.simp (Δ.erase w)) ∪
          ⋃ j ∈ Finset.range ((Work.PL.Shell.flagEnum vs).idxOf l),
            PL.simp ((Work.PL.Shell.prefixes ((Work.PL.Shell.flagEnum vs).getD j [])).image
              Work.PL.Shell.bary)) := by
    rintro x hx
    rw [Set.mem_iUnion₂] at hx
    obtain ⟨k, hk, hxk⟩ := hx
    rw [htriv k hk] at hxk
    refine ⟨?_, hfac k hk hxk⟩
    show x ∈ Work.PL.Sd1.face l (Work.PL.Sd1.flagIdx l)
    exact Work.PL.Sd1.face_mono Finset.sdiff_subset hxk
  -- the trace is contained in the attaching union
  have htrace : PL.simp ((Work.PL.Shell.prefixes l).image Work.PL.Shell.bary) ∩
        ((⋃ w ∈ T, PL.simp (Δ.erase w)) ∪
          ⋃ j ∈ Finset.range ((Work.PL.Shell.flagEnum vs).idxOf l),
            PL.simp ((Work.PL.Shell.prefixes ((Work.PL.Shell.flagEnum vs).getD j [])).image
              Work.PL.Shell.bary)) ⊆
      ⋃ k ∈ wit T rk l,
        PL.simp (((Work.PL.Shell.prefixes l).image Work.PL.Shell.bary).erase
          (Work.PL.Shell.bary (Work.PL.Shell.prefAt l k))) := by
    rintro x ⟨hxσ, hxBE⟩
    have hxσ' : x ∈ Work.PL.Sd1.face l (Work.PL.Sd1.flagIdx l) := hxσ
    obtain ⟨J₀, hJ₀sub, hxJ₀, hJ₀min⟩ :=
      Work.PL.Sd1.exists_min_face hΔ hlnod hlΔ (J := Work.PL.Sd1.flagIdx l)
        Finset.Subset.rfl hxσ'
    have hJ₀ne : J₀.Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      rw [h, Work.PL.Sd1.face, Finset.image_empty, Finset.image_empty, PL.simp,
        Finset.coe_empty, convexHull_empty] at hxJ₀
      exact hxJ₀
    have hsub : Work.PL.Sd1.face l J₀ ⊆
        (⋃ w ∈ T, PL.simp (Δ.erase w)) ∪
          ⋃ j ∈ Finset.range ((Work.PL.Shell.flagEnum vs).idxOf l),
            PL.simp ((Work.PL.Shell.prefixes ((Work.PL.Shell.flagEnum vs).getD j [])).image
              Work.PL.Shell.bary) := by
      rcases hxBE with hxB | hxE
      · obtain ⟨w, hwT, hxw⟩ := Set.mem_iUnion₂.mp hxB
        have hwΔ : w ∈ Δ := hTΔ hwT
        have hmiss_sub : Work.PL.Sd1.missIdx l w ⊆ Work.PL.Sd1.flagIdx l :=
          fun j hj => (Finset.mem_filter.mp hj).1
        have hinter : x ∈ Work.PL.Sd1.face l (Work.PL.Sd1.missIdx l w) := by
          rw [← Work.PL.Shell.simp_inter_erase_eq_face (Δ := Δ) hΔ hlnod hlΔ hwΔ]
          exact ⟨hxσ, hxw⟩
        have hJ₀miss : J₀ ⊆ Work.PL.Sd1.missIdx l w := by
          have hxI : x ∈ Work.PL.Sd1.face l (J₀ ∩ Work.PL.Sd1.missIdx l w) := by
            rw [Work.PL.Sd1.face_inter hΔ hlnod hlΔ hJ₀sub hmiss_sub]
            exact ⟨hxJ₀, hinter⟩
          have hmin := hJ₀min (J₀ ∩ Work.PL.Sd1.missIdx l w)
            (Finset.inter_subset_left.trans hJ₀sub) hxI
          exact fun a ha => Finset.mem_of_mem_inter_right (hmin ha)
        have hwB : Work.PL.Sd1.face l (Work.PL.Sd1.missIdx l w) ⊆
            ⋃ w ∈ T, PL.simp (Δ.erase w) := by
          intro y hy
          have hy' : y ∈ PL.simp ((Work.PL.Shell.prefixes l).image Work.PL.Shell.bary) ∩
              PL.simp (Δ.erase w) := by
            rw [Work.PL.Shell.simp_inter_erase_eq_face (Δ := Δ) hΔ hlnod hlΔ hwΔ]
            exact hy
          exact Set.mem_iUnion₂.mpr ⟨w, hwT, hy'.2⟩
        exact Set.Subset.trans (Work.PL.Sd1.face_mono hJ₀miss)
          (fun y hy => Set.mem_union_left _ (hwB hy))
      · obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hxE
        have hidxlt : (Work.PL.Shell.flagEnum vs).idxOf l < (Work.PL.Shell.flagEnum vs).length :=
          List.idxOf_lt_length_iff.mpr hl
        have hjlt : j < (Work.PL.Shell.flagEnum vs).length :=
          lt_of_lt_of_le (Finset.mem_range.mp hj) (Nat.le_of_lt hidxlt)
        have hl'mem : (Work.PL.Shell.flagEnum vs)[j]'hjlt ∈ Work.PL.Shell.flagEnum vs :=
          List.getElem_mem hjlt
        have hl'perm : ((Work.PL.Shell.flagEnum vs)[j]'hjlt).Perm vs :=
          Work.PL.Shell.flagEnum_mem.mp hl'mem
        have hl'nod : ((Work.PL.Shell.flagEnum vs)[j]'hjlt).Nodup := hl'perm.nodup_iff.mpr hvs'
        have hl'Δ : ((Work.PL.Shell.flagEnum vs)[j]'hjlt).toFinset = Δ := by
          rw [List.toFinset_eq_of_perm _ _ hl'perm, hvs]
        have hxE' : x ∈ PL.simp ((Work.PL.Shell.prefixes
            ((Work.PL.Shell.flagEnum vs)[j]'hjlt)).image Work.PL.Shell.bary) := by
          rw [List.getD_eq_getElem (Work.PL.Shell.flagEnum vs) [] hjlt] at hxj
          exact hxj
        have hinter : x ∈ Work.PL.Sd1.face l
            (Work.PL.Sd1.sameIdx l ((Work.PL.Shell.flagEnum vs)[j]'hjlt)) := by
          rw [← Work.PL.Shell.simp_inter_simp_sameIdx (Δ := Δ) hΔ hlnod hl'nod hlΔ hl'Δ]
          exact ⟨hxσ, hxE'⟩
        have hsame_sub : Work.PL.Sd1.sameIdx l ((Work.PL.Shell.flagEnum vs)[j]'hjlt) ⊆
            Work.PL.Sd1.flagIdx l := fun a ha => (Finset.mem_filter.mp ha).1
        have hJ₀same : J₀ ⊆ Work.PL.Sd1.sameIdx l ((Work.PL.Shell.flagEnum vs)[j]'hjlt) := by
          have hxI : x ∈ Work.PL.Sd1.face l
              (J₀ ∩ Work.PL.Sd1.sameIdx l ((Work.PL.Shell.flagEnum vs)[j]'hjlt)) := by
            rw [Work.PL.Sd1.face_inter hΔ hlnod hlΔ hJ₀sub hsame_sub]
            exact ⟨hxJ₀, hinter⟩
          have hmin := hJ₀min (J₀ ∩ Work.PL.Sd1.sameIdx l ((Work.PL.Shell.flagEnum vs)[j]'hjlt))
            (Finset.inter_subset_left.trans hJ₀sub) hxI
          exact fun a ha => Finset.mem_of_mem_inter_right (hmin ha)
        have hEsub : Work.PL.Sd1.face l
            (Work.PL.Sd1.sameIdx l ((Work.PL.Shell.flagEnum vs)[j]'hjlt)) ⊆
            ⋃ j ∈ Finset.range ((Work.PL.Shell.flagEnum vs).idxOf l),
              PL.simp ((Work.PL.Shell.prefixes ((Work.PL.Shell.flagEnum vs).getD j [])).image
                Work.PL.Shell.bary) := by
          intro y hy
          have hy' : y ∈ PL.simp ((Work.PL.Shell.prefixes l).image Work.PL.Shell.bary) ∩
              PL.simp ((Work.PL.Shell.prefixes
                ((Work.PL.Shell.flagEnum vs)[j]'hjlt)).image Work.PL.Shell.bary) := by
            rw [Work.PL.Shell.simp_inter_simp_sameIdx (Δ := Δ) hΔ hlnod hl'nod hlΔ hl'Δ]
            exact hy
          refine Set.mem_iUnion₂.mpr ⟨j, hj, ?_⟩
          rw [List.getD_eq_getElem (Work.PL.Shell.flagEnum vs) [] hjlt]
          exact hy'.2
        exact Set.Subset.trans (Work.PL.Sd1.face_mono hJ₀same)
          (fun y hy => Set.mem_union_right _ (hEsub hy))
    have hcond := (Work.PL.Shell.face_trace hΔ vs rk hvs hrk hT₁ hT₂ hT hl hJ₀ne
      (fun a ha => Finset.mem_range.mp (hJ₀sub ha))).mp hsub
    have hlne : l ≠ [] := ne_nil_of_card hlΔ hT₁ hT₂
    rcases Work.PL.Sd1.crit_to_idx hΔ hvs hvs' hrk hT₁ hT₂ hT hl hJ₀sub hJ₀ne hcond with
      ⟨a, ha, hna⟩ | ⟨hlast, hd⟩
    · have haasc : a ∈ wit T rk l := mem_wit.mpr (Or.inl ha)
      refine Set.mem_iUnion₂.mpr ⟨a, haasc, ?_⟩
      rw [htriv a haasc]
      refine Work.PL.Sd1.face_mono ?_ hxJ₀
      intro b hb
      rw [Finset.mem_sdiff]
      exact ⟨hJ₀sub hb, by
        rw [Finset.mem_singleton]
        intro hba
        exact hna (hba ▸ hb)⟩
    · have hdasc : l.length - 1 ∈ wit T rk l := mem_wit.mpr (Or.inr ⟨hlast, rfl⟩)
      refine Set.mem_iUnion₂.mpr ⟨l.length - 1, hdasc, ?_⟩
      rw [htriv (l.length - 1) hdasc]
      refine Work.PL.Sd1.face_mono ?_ hxJ₀
      intro b hb
      rw [Finset.mem_sdiff]
      exact ⟨hJ₀sub hb, by
        rw [Finset.mem_singleton]
        intro hbd
        exact hd (hbd ▸ hb)⟩
  exact Set.Subset.antisymm htrace hfacets

/-- The union of the facets indexed by the attaching set, written with `splitOf`. -/
private theorem splitOf_iUnion_eq {Δ T : Finset (PL.E N)} (rk : PL.E N → ℕ)
    {l : List (PL.E N)} (hlnod : l.Nodup) (hlΔ : l.toFinset = Δ) (hlne : l ≠ []) :
    (⋃ w ∈ Work.PL.Shell.splitOf Δ T rk l,
        PL.simp (((Work.PL.Shell.prefixes l).image Work.PL.Shell.bary).erase w)) =
      ⋃ k ∈ wit T rk l,
        PL.simp (((Work.PL.Shell.prefixes l).image Work.PL.Shell.bary).erase
          (Work.PL.Shell.bary (Work.PL.Shell.prefAt l k))) := by
  rw [splitOf_eq_wit_image rk hlnod hlΔ hlne]
  exact iUnion_image_eq (wit T rk l) (fun k => Work.PL.Shell.bary (Work.PL.Shell.prefAt l k))
    (fun w => PL.simp (((Work.PL.Shell.prefixes l).image Work.PL.Shell.bary).erase w))

/-- The trace identity in the form used by `Work.PL.Sd1.Shell1`. -/
private theorem splitOf_trace_at {N : ℕ} {Δ T : Finset (PL.E N)}
    (hΔ : AffineIndependent ℝ ((↑) : Δ → PL.E N))
    (vs : List (PL.E N)) (rk : PL.E N → ℕ)
    (hvs : vs.toFinset = Δ) (hvs' : vs.Nodup) (hrk : (vs.map rk).Pairwise (· < ·))
    (hT₁ : T.Nonempty) (hT₂ : T ⊂ Δ)
    (hT : ∀ u ∈ T, ∀ w ∈ Δ, w ∉ T → rk u < rk w)
    (i : ℕ) (hi : i < (Work.PL.Shell.flagEnum vs).length) :
    let l := (Work.PL.Shell.flagEnum vs).get ⟨i, hi⟩
    PL.simp ((Work.PL.Shell.prefixes l).image Work.PL.Shell.bary) ∩
        ((⋃ w ∈ T, PL.simp (Δ.erase w)) ∪
          ⋃ j ∈ Finset.range i,
            PL.simp ((Work.PL.Shell.prefixes ((Work.PL.Shell.flagEnum vs).getD j [])).image
              Work.PL.Shell.bary)) =
      ⋃ w ∈ Work.PL.Shell.splitOf Δ T rk l,
        PL.simp (((Work.PL.Shell.prefixes l).image Work.PL.Shell.bary).erase w) := by
  dsimp only
  have hl : (Work.PL.Shell.flagEnum vs).get ⟨i, hi⟩ ∈ Work.PL.Shell.flagEnum vs :=
    List.get_mem _ _
  have hLnod : (Work.PL.Shell.flagEnum vs).Nodup := Work.PL.Sd1.flagEnum_nodup hvs' hrk
  have hidx : (Work.PL.Shell.flagEnum vs).idxOf ((Work.PL.Shell.flagEnum vs).get ⟨i, hi⟩) = i :=
    hLnod.idxOf_getElem i hi
  have hlperm : ((Work.PL.Shell.flagEnum vs).get ⟨i, hi⟩).Perm vs :=
    Work.PL.Shell.flagEnum_mem.mp hl
  have hlnod : ((Work.PL.Shell.flagEnum vs).get ⟨i, hi⟩).Nodup := hlperm.nodup_iff.mpr hvs'
  have hlΔ : ((Work.PL.Shell.flagEnum vs).get ⟨i, hi⟩).toFinset = Δ := by
    rw [List.toFinset_eq_of_perm _ _ hlperm, hvs]
  have hlne : ((Work.PL.Shell.flagEnum vs).get ⟨i, hi⟩) ≠ [] := ne_nil_of_card hlΔ hT₁ hT₂
  have h := wit_trace hΔ vs rk hvs hvs' hrk hT₁ hT₂ hT hl
  rw [hidx] at h
  exact h.trans (splitOf_iUnion_eq rk hlnod hlΔ hlne).symm

/-! ### The statement -/

theorem shell1_of_cover {N : ℕ} {Δ T : Finset (PL.E N)}
    (hΔ : AffineIndependent ℝ ((↑) : Δ → PL.E N))
    (vs : List (PL.E N)) (rk : PL.E N → ℕ)
    (hvs : vs.toFinset = Δ) (hvs' : vs.Nodup) (hrk : (vs.map rk).Pairwise (· < ·))
    (hT₁ : T.Nonempty) (hT₂ : T ⊂ Δ)
    (hT : ∀ u ∈ T, ∀ w ∈ Δ, w ∉ T → rk u < rk w)
    (hcover : (⋃ l ∈ (Work.PL.Shell.flagEnum vs).toFinset,
        PL.simp ((Work.PL.Shell.prefixes l).image Work.PL.Shell.bary)) = PL.simp Δ) :
    Work.PL.Sd1.Shell1 Δ T vs rk := by
  refine ⟨?_, Work.PL.Sd1.flagEnum_nodup hvs' hrk, hcover⟩
  intro i hi
  exact ⟨Work.PL.Sd1.splitOf_nonempty hΔ hvs hvs' hrk hT₁ hT₂ hT (List.get_mem _ _),
    splitOf_ssubset_here hΔ vs rk hvs hvs' hrk hT₁ hT₂ hT (List.get_mem _ _),
    splitOf_trace_at hΔ vs rk hvs hvs' hrk hT₁ hT₂ hT i hi⟩

end

end Work.PL.Sd1
