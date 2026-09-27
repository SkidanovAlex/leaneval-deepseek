import Submission.Work.PL.Subdiv.SdCover

/-!
# The barycentric subdivision (blueprint G3)

The main definitions of the area:

* `sd K` : the barycentric subdivision of a geometric complex `K` in `ℝᴺ`.  Its faces are the
  barycenters of chains of faces of `K` (`mem_sd_faces_iff`).
* `sdIter r K hK` : the `r`-fold subdivision (the `SubdivTools.sdIter` of the lead's A9 design).

The three `SimplicialComplex` axioms are `affineIndependent_bary_image`, `inter_subset_bary` and
the down-closure of `sdFaces`; the covering lemma is `exists_chain_subset_of_mem_simp`.
-/

open Set Metric
open scoped BigOperators
open PL

namespace Work.PL.Subdiv

noncomputable section

variable {N : ℕ}

/-- The set of barycenters of chains of faces is closed under passing to subsets. -/
theorem isLowerSet_sdFaces (K : Cx N) : IsLowerSet (sdFaces K) := by
  rintro a b hab hb
  obtain ⟨C, hC, ha⟩ := hb
  refine ⟨C.filter (fun ρ => bary ρ ∈ b), hC.mono (Finset.filter_subset _ _), ?_⟩
  apply Finset.ext
  intro x
  constructor
  · intro hx
    have hxa : x ∈ a := hab hx
    rw [ha] at hxa
    obtain ⟨ρ, hρC, hρx⟩ := Finset.mem_image.mp hxa
    exact Finset.mem_image.mpr ⟨ρ, Finset.mem_filter.mpr ⟨hρC, hρx ▸ hx⟩, hρx⟩
  · intro hx
    obtain ⟨ρ, hρ, hρx⟩ := Finset.mem_image.mp hx
    rw [← hρx]
    exact (Finset.mem_filter.mp hρ).2

/-- **Barycentric subdivision** of a finite geometric complex: the faces are the barycenters of
chains of faces. -/
noncomputable def sd (K : Cx N) : Cx N :=
  Geometry.SimplicialComplex.ofErase (sdFaces K)
    (fun _ hs => by
      obtain ⟨C, hC, rfl⟩ := hs
      exact affineIndependent_bary_image hC)
    (isLowerSet_sdFaces K)
    (fun s hs t ht => by
      obtain ⟨C, hC, rfl⟩ := hs
      obtain ⟨D, hD, rfl⟩ := ht
      refine (inter_subset_bary hC hD).trans (convexHull_mono ?_)
      intro b hb
      obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hb
      exact ⟨Finset.mem_image.mpr ⟨ρ, (Finset.mem_inter.mp hρ).1, rfl⟩,
        Finset.mem_image.mpr ⟨ρ, (Finset.mem_inter.mp hρ).2, rfl⟩⟩)

/-- The faces of `sd K` are exactly the barycenters of nonempty chains of faces of `K`. -/
theorem mem_sd_faces_iff {K : Cx N} {t : Finset (E N)} :
    t ∈ (sd K).faces ↔ t.Nonempty ∧ ∃ C : Finset (Finset (E N)), IsChain K C ∧
      t = C.image bary := by
  rw [sd, Geometry.SimplicialComplex.ofErase_faces]
  simp only [Set.mem_diff, Set.mem_singleton_iff, sdFaces, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨C, hC, rfl⟩, hne⟩
    exact ⟨Finset.nonempty_iff_ne_empty.mpr hne, C, hC, rfl⟩
  · rintro ⟨hne, C, hC, rfl⟩
    exact ⟨⟨C, hC, rfl⟩, Finset.nonempty_iff_ne_empty.mp hne⟩

lemma mem_sd_faces_of_chain {K : Cx N} {C : Finset (Finset (E N))} (hC : IsChain K C)
    (hne : C.Nonempty) : C.image bary ∈ (sd K).faces :=
  mem_sd_faces_iff.mpr ⟨hne.image _, C, hC, rfl⟩

/-- Every face of `sd K` lies in a simplex spanned by a face of `K`. -/
theorem sd_face_subset_of_face {K : Cx N} {t : Finset (E N)} (ht : t ∈ (sd K).faces) :
    ∃ s ∈ K.faces, simp t ⊆ simp s := by
  obtain ⟨htne, C, hC, rfl⟩ := mem_sd_faces_iff.mp ht
  have hCne : C.Nonempty := by
    rcases Finset.eq_empty_or_nonempty C with h | h
    · rw [h] at htne
      simp at htne
    · exact h
  refine ⟨chainTop C, hC.1 _ (chainTop_mem_chain hC.2 hCne), ?_⟩
  refine convexHull_min ?_ (convex_convexHull ℝ _)
  intro b hb
  obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hb
  exact convexHull_mono (Finset.coe_subset.mpr (le_chainTop hρ))
    (bary_mem_simp (K.nonempty_of_mem_faces (hC.1 ρ hρ)))

/-- The underlying space of a subdivided complex is the underlying space of the original. -/
theorem space_sd {K : Cx N} : (sd K).space = K.space := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp hx
    obtain ⟨s, hs, hsub⟩ := sd_face_subset_of_face ht
    exact mem_iUnion₂.mpr ⟨s, hs, hsub hxt⟩
  · intro x hx
    obtain ⟨σ, hσ, hxσ⟩ := mem_iUnion₂.mp hx
    obtain ⟨C, hC, -, hxC⟩ := exists_chain_subset_of_mem_simp σ hσ x hxσ
    have hCne : C.Nonempty := by
      rcases Finset.eq_empty_or_nonempty C with h | h
      · rw [h] at hxC
        simp [PL.simp] at hxC
      · exact h
    exact mem_iUnion₂.mpr ⟨C.image bary, mem_sd_faces_of_chain hC hCne, hxC⟩

/-- **The barycentric subdivision is a subdivision.** -/
theorem sd_subdivides (K : Cx N) : Subdivides (sd K) K :=
  ⟨space_sd, fun t ht => sd_face_subset_of_face ht⟩

/-- **`sd_sub`**: subcomplexes go to subcomplexes. -/
theorem sd_isSub {K L : Cx N} (h : IsSub L K) : IsSub (sd L) (sd K) := by
  intro t ht
  obtain ⟨-, C, hC, rfl⟩ := mem_sd_faces_iff.mp ht
  exact mem_sd_faces_of_chain ⟨fun ρ hρ => h (hC.1 ρ hρ), hC.2⟩ (by
    rcases C.eq_empty_or_nonempty with h0 | h0
    · rw [h0] at ht
      simp [mem_sd_faces_iff] at ht
    · exact h0)

/-- The faces of `sd K` are finite when those of `K` are. -/
theorem sd_faces_finite {K : Cx N} (hK : K.faces.Finite) : (sd K).faces.Finite := by
  have h1 : (hK.toFinset.powerset : Set (Finset (Finset (E N)))).Finite := Finset.finite_toSet _
  have h2 : ((fun C : Finset (Finset (E N)) => C.image bary) ''
      (hK.toFinset.powerset : Set (Finset (Finset (E N))))).Finite := h1.image _
  refine h2.subset ?_
  intro t ht
  obtain ⟨-, C, hC, rfl⟩ := mem_sd_faces_iff.mp ht
  exact ⟨C, Finset.mem_powerset.mpr fun ρ hρ =>
    (Set.Finite.mem_toFinset hK).mpr (hC.1 ρ hρ), rfl⟩

/-- **Subcomplexes are preserved by subdivision.**  A region which is a union of faces of `K` is
again a union of faces of `sd K`. -/
theorem biUnion_simp_sd {K : Cx N} (hK : K.faces.Finite) (T : Finset (Finset (E N)))
    (hT : ∀ s ∈ T, s ∈ K.faces) :
    ∃ T' : Finset (Finset (E N)), (∀ t ∈ T', t ∈ (sd K).faces) ∧
      ⋃ s ∈ T, simp s = ⋃ t ∈ T', simp t := by
  classical
  refine ⟨(sd_faces_finite hK).toFinset.filter (fun t => ∃ s ∈ T, simp t ⊆ simp s), ?_, ?_⟩
  · intro t ht
    exact (Set.Finite.mem_toFinset (sd_faces_finite hK)).mp (Finset.mem_filter.mp ht).1
  · refine le_antisymm ?_ ?_
    · intro x hx
      obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.mp hx
      obtain ⟨C, hC, hCsub, hxC⟩ := exists_chain_subset_of_mem_simp s (hT s hs) x hxs
      have hCne : C.Nonempty := by
        rcases Finset.eq_empty_or_nonempty C with h | h
        · rw [h] at hxC
          simp [PL.simp] at hxC
        · exact h
      have hmem : C.image bary ∈ (sd_faces_finite hK).toFinset :=
        (Set.Finite.mem_toFinset (sd_faces_finite hK)).mpr (mem_sd_faces_of_chain hC hCne)
      have hsub : simp (C.image bary) ⊆ simp s := by
        refine convexHull_min ?_ (convex_convexHull ℝ _)
        intro b hb
        obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hb
        exact convexHull_mono (Finset.coe_subset.mpr (hCsub ρ hρ))
          (bary_mem_simp (K.nonempty_of_mem_faces (hC.1 ρ hρ)))
      exact mem_iUnion₂.mpr ⟨C.image bary, Finset.mem_filter.mpr ⟨hmem, s, hs, hsub⟩, hxC⟩
    · intro x hx
      obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp hx
      obtain ⟨-, s, hs, hsub⟩ := Finset.mem_filter.mp ht
      exact mem_iUnion₂.mpr ⟨s, hs, hsub hxt⟩

/-- **`sd_face`.**  The subdivision of a single face: `simp s` is the union of the `sd K`-faces
whose chains consist of faces of `s`. -/
theorem simp_sd_decomp {K : Cx N} {s : Finset (E N)} (hs : s ∈ K.faces) :
    simp s = ⋃ C ∈ {C : Finset (Finset (E N)) | IsChain K C ∧ ∀ ρ ∈ C, ρ ⊆ s}, simp (C.image bary) := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨C, hC, hCsub, hxC⟩ := exists_chain_subset_of_mem_simp s hs x hx
    exact mem_iUnion₂.mpr ⟨C, ⟨hC, hCsub⟩, hxC⟩
  · intro x hx
    obtain ⟨C, ⟨hC, hCsub⟩, hxC⟩ := mem_iUnion₂.mp hx
    refine convexHull_min (fun b hb => ?_) (convex_convexHull ℝ _) hxC
    obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hb
    exact convexHull_mono (Finset.coe_subset.mpr (hCsub ρ hρ))
      (bary_mem_simp (K.nonempty_of_mem_faces (hC.1 ρ hρ)))

/-! ### Iterated subdivision (`SubdivTools.sdIter`) -/

/-- `r`-fold barycentric subdivision.  The finiteness hypothesis keeps the signature of the lead's
`SubdivTools.sdIter`; the definition itself does not need it. -/
def sdIter : ℕ → (K : Cx N) → K.faces.Finite → Cx N
  | 0, K, _ => K
  | r + 1, K, hK => sd (sdIter r K hK)

@[simp] theorem sdIter_zero (K : Cx N) (hK : K.faces.Finite) : sdIter 0 K hK = K := rfl

theorem sdIter_succ (r : ℕ) (K : Cx N) (hK : K.faces.Finite) :
    sdIter (r + 1) K hK = sd (sdIter r K hK) := rfl

theorem sdIter_faces_finite (r : ℕ) (K : Cx N) (hK : K.faces.Finite) :
    (sdIter r K hK).faces.Finite := by
  induction r with
  | zero => exact hK
  | succ n ih => rw [sdIter_succ]; exact sd_faces_finite ih

theorem subdivides_trans {K K' K'' : Cx N} (h1 : Subdivides K' K) (h2 : Subdivides K'' K') :
    Subdivides K'' K :=
  ⟨h2.1.trans h1.1, fun t ht => by
    obtain ⟨t', ht', hsub⟩ := h2.2 t ht
    obtain ⟨s, hs, hsub'⟩ := h1.2 t' ht'
    exact ⟨s, hs, hsub.trans hsub'⟩⟩

theorem sdIter_subdivides (r : ℕ) (K : Cx N) (hK : K.faces.Finite) :
    Subdivides (sdIter r K hK) K := by
  induction r with
  | zero => exact ⟨rfl, fun t ht => ⟨t, ht, subset_rfl⟩⟩
  | succ n ih => rw [sdIter_succ]; exact subdivides_trans ih (sd_subdivides _)

/-- A chain of faces has at most as many elements as its top face has vertices. -/
lemma card_le_card_chainTop {K : Cx N} {C : Finset (Finset (E N))} (hC : IsChain K C) :
    C.card ≤ (chainTop C).card := by
  have hinj : Set.InjOn (fun ρ : Finset (E N) => ρ.card) (↑C : Set (Finset (E N))) := by
    intro ρ hρ ρ' hρ' h
    rcases hC.2 ρ hρ ρ' hρ' with hsub | hsub
    · exact Finset.eq_of_subset_of_card_le hsub (le_of_eq h.symm)
    · exact (Finset.eq_of_subset_of_card_le hsub (le_of_eq h)).symm
  calc C.card = (C.image (fun ρ => ρ.card)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.Icc 1 (chainTop C).card).card := Finset.card_le_card fun n hn => by
        obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hn
        exact Finset.mem_Icc.mpr
          ⟨Finset.card_pos.mpr (K.nonempty_of_mem_faces (hC.1 ρ hρ)),
           Finset.card_le_card (le_chainTop hρ)⟩
    _ = (chainTop C).card := by simp

/-- Subdivision does not increase the dimension. -/
theorem sd_dimle (K : Cx N) (d : ℕ) (h : DimLE K d) : DimLE (sd K) d := by
  intro s hs
  obtain ⟨hsne, C, hC, rfl⟩ := mem_sd_faces_iff.mp hs
  have hCne : C.Nonempty := by
    rcases Finset.eq_empty_or_nonempty C with h0 | h0
    · rw [h0] at hsne
      simp at hsne
    · exact h0
  have hcard : (C.image bary).card = C.card :=
    Finset.card_image_of_injOn fun ρ hρ ρ' hρ' hxy => bary_eq_of_chain hC hρ hρ' hxy
  rw [hcard]
  exact le_trans (card_le_card_chainTop hC) (h _ (hC.1 _ (chainTop_mem_chain hC.2 hCne)))

theorem sdIter_dimle (r d : ℕ) (K : Cx N) (hK : K.faces.Finite) (h : DimLE K d) :
    DimLE (sdIter r K hK) d := by
  induction r with
  | zero => exact h
  | succ n ih => rw [sdIter_succ]; exact sd_dimle _ d ih

end

end Work.PL.Subdiv
