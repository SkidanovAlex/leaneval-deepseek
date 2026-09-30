import Mathlib
import Submission.Work.SSS.HornDefs

/-!
# Gluing a matching family of faces into a map on the topological horn

`Work.SSS.exists_hornGlue`: a compatible family of continuous maps `Δⁿ → X`, one for each face
`j ≠ i` of the horn `Λ[n+1, i] ⊆ Δ^{n+1}`, glues into a single continuous map `Λ[n+1, i] → X`
whose restriction to the `j`-th face is the `j`-th member of the family.

The compatibility hypothesis `hcomp` is *exactly* the statement that two members of the family
agree on the overlap of their faces, read in the two possible ways.
-/

set_option autoImplicit false

namespace Work.SSS

noncomputable section

open CategoryTheory

/-! ## Elementary facts about `Fin.succAbove`

The face inclusions of `Δ^{n+1}` insert a zero coordinate; deleting a vanishing coordinate is the
map `Work.SSS.stdSimplexDel`.  The lemmas below are the index bookkeeping behind the gluing.
-/

/-- The value formula for `Fin.succAbove`. -/
theorem val_succAbove {n : ℕ} (p : Fin (n + 1)) (i : Fin n) :
    (p.succAbove i).val = if i.val < p.val then i.val else i.val + 1 := by
  by_cases h : i.castSucc < p
  · rw [Fin.succAbove_of_castSucc_lt p i h, Fin.val_castSucc,
      if_pos (by simpa [Fin.lt_def, Fin.val_castSucc] using h)]
  · rw [Fin.succAbove_of_le_castSucc p i (le_of_not_gt h), Fin.val_succ,
      if_neg (by simpa [Fin.lt_def, Fin.val_castSucc] using h)]

/-- `succAbove j` sends the index of the `l`-th face of `Δⁿ` to `l` (for `j < l`). -/
theorem succAbove_pred_eq {n : ℕ} (j l : Fin (n + 2)) (h : j < l) :
    Fin.succAbove j (l.pred (Fin.ne_zero_of_lt h)) = l := by
  have hp : l.pred (Fin.ne_zero_of_lt h)
      = l.pred (Fin.ne_of_gt (Fin.lt_of_le_of_lt j.zero_le h)) := by
    apply Fin.ext
    rfl
  rw [hp]
  exact Fin.succAbove_pred_of_lt j l h

/-- `succAbove l` sends the index of the `j`-th face of `Δⁿ` to `j` (for `j < l`). -/
theorem succAbove_castPred_eq {n : ℕ} (j l : Fin (n + 2)) (h : j < l) :
    Fin.succAbove l (j.castPred (Fin.ne_last_of_lt h)) = j := by
  have hp : j.castPred (Fin.ne_last_of_lt h)
      = j.castPred (Fin.ne_of_lt (Nat.lt_of_lt_of_le h l.le_last)) := by
    apply Fin.ext
    rfl
  rw [hp]
  exact Fin.succAbove_castPred_of_lt l j h

/-- The two iterated cofaces that skip the pair of vertices `{j, l}` coincide: the overlap of the
`j`-th and the `l`-th face of `Δ^{n+1}` is a single `(n-1)`-simplex, read in the two ways. -/
theorem succAbove_succAbove_face {n : ℕ} (j l : Fin (n + 2)) (h : j < l) (t : Fin n) :
    Fin.succAbove j (Fin.succAbove (l.pred (Fin.ne_zero_of_lt h)) t) =
    Fin.succAbove l (Fin.succAbove (j.castPred (Fin.ne_last_of_lt h)) t) := by
  apply Fin.ext
  have hjc : ((j.castPred (Fin.ne_last_of_lt h)) : Fin (n + 1)).val = j.val := by
    simp [Fin.castPred]
  simp only [val_succAbove, Fin.val_pred]
  rw [hjc]
  split_ifs <;> omega

/-- Re-inserting the coordinate deleted by `Work.SSS.stdSimplexDel` recovers the point. -/
theorem map_succAbove_stdSimplexDel {n : ℕ} (j : Fin (n + 1)) (q : stdSimplex ℝ (Fin (n + 1)))
    (hq : (q : Fin (n + 1) → ℝ) j = 0) :
    stdSimplex.map (Fin.succAbove j) (stdSimplexDel (k := n) j q hq) = q := by
  ext k
  show (stdSimplex.map (Fin.succAbove j) (stdSimplexDel (k := n) j q hq) :
      Fin (n + 1) → ℝ) k = (q : Fin (n + 1) → ℝ) k
  rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  by_cases hk : k = j
  · rw [hk, Finset.filter_eq_empty_iff.mpr (fun x _ hx => Fin.succAbove_ne j x hx),
      Finset.sum_empty, hq]
  · obtain ⟨l, hl⟩ := Fin.exists_succAbove_eq hk
    have hfil : Finset.univ.filter (fun x : Fin n => j.succAbove x = k) = {l} := by
      refine Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩
      · intro b hb
        exact Fin.succAbove_right_injective ((Finset.mem_filter.mp hb).2.trans hl.symm)
    rw [hfil, Finset.sum_singleton, stdSimplexDel_apply, hl]

/-- Deleting the coordinate inserted by a coface recovers the point. -/
theorem stdSimplexDel_map_succAbove {n : ℕ} (j : Fin (n + 2)) (q : stdSimplex ℝ (Fin (n + 1)))
    (hq : (stdSimplex.map (Fin.succAbove j) q : Fin (n + 2) → ℝ) j = 0) :
    stdSimplexDel (k := n + 1) j (stdSimplex.map (Fin.succAbove j) q) hq = q := by
  ext l
  show (stdSimplex.map (Fin.succAbove j) q : Fin (n + 2) → ℝ) (Fin.succAbove j l)
      = (q : Fin (n + 1) → ℝ) l
  rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply, Finset.sum_filter]
  rw [Finset.sum_eq_single l]
  · rw [if_pos rfl]
  · intro b _ hbl
    rw [if_neg]
    exact fun hh => hbl (Fin.succAbove_right_injective hh)
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The `j`-th coordinate of a coface vanishes. -/
theorem map_succAbove_apply_self {n : ℕ} (j : Fin (n + 2)) (q : stdSimplex ℝ (Fin (n + 1))) :
    (stdSimplex.map (Fin.succAbove j) q : Fin (n + 2) → ℝ) j = 0 := by
  rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply,
    Finset.filter_eq_empty_iff.mpr (fun y _ hy => Fin.succAbove_ne j y hy), Finset.sum_empty]

/-- The two ways of deleting the two vanishing coordinates of a point of `Δ^{n+1}` agree. -/
theorem stdSimplexDel_stdSimplexDel {n : ℕ} (j l : Fin (n + 2)) (h : j < l)
    (z : ↥(stdSimplex ℝ (Fin (n + 2)))) (hzj : (z : Fin (n + 2) → ℝ) j = 0)
    (hzl : (z : Fin (n + 2) → ℝ) l = 0)
    (h1 : ((stdSimplexDel (k := n + 1) j z hzj) : Fin (n + 1) → ℝ)
        (l.pred (Fin.ne_zero_of_lt h)) = 0)
    (h2 : ((stdSimplexDel (k := n + 1) l z hzl) : Fin (n + 1) → ℝ)
        (j.castPred (Fin.ne_last_of_lt h)) = 0) :
    stdSimplexDel (k := n) (l.pred (Fin.ne_zero_of_lt h))
        (stdSimplexDel (k := n + 1) j z hzj) h1 =
      stdSimplexDel (k := n) (j.castPred (Fin.ne_last_of_lt h))
        (stdSimplexDel (k := n + 1) l z hzl) h2 := by
  apply Subtype.ext
  funext m
  change (z : Fin (n + 2) → ℝ)
        (Fin.succAbove j (Fin.succAbove (l.pred (Fin.ne_zero_of_lt h)) m)) =
      (z : Fin (n + 2) → ℝ)
        (Fin.succAbove l (Fin.succAbove (j.castPred (Fin.ne_last_of_lt h)) m))
  rw [succAbove_succAbove_face j l h m]

/-! ## The gluing -/

theorem exists_hornGlue {X : Type} [TopologicalSpace X] {n : ℕ} {i : Fin (n + 2)}
    (g : ∀ (j : Fin (n + 2)), j ≠ i → C(stdSimplex ℝ (Fin (n + 1)), X))
    (hcomp : ∀ (j l : Fin (n + 2)) (hj : j ≠ i) (hl : l ≠ i) (hjl : j < l),
      ⇑(g j hj) ∘ (stdSimplex.map ((l.pred (Fin.ne_zero_of_lt hjl)).succAbove)) =
      ⇑(g l hl) ∘ (stdSimplex.map ((j.castPred (Fin.ne_last_of_lt hjl)).succAbove))) :
    ∃ u : C(↥(Work.SSS.TopHorn (n + 1) i), X),
      ∀ (j : Fin (n + 2)) (hj : j ≠ i),
        u.comp (Work.SSS.faceIncl (n + 1) i j hj) = g j hj := by
  classical
  -- a fixed point of `Δⁿ`, used only in the junk branch of the piece maps
  let pt : ↥(stdSimplex ℝ (Fin (n + 1))) :=
    ⟨fun _ => (Fintype.card (Fin (n + 1)) : ℝ)⁻¹, by
      refine ⟨fun _ => by positivity, ?_⟩
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp⟩
  -- the `j`-th closed face of the horn
  let E : {j : Fin (n + 2) // j ≠ i} → Set ↥(TopHorn (n + 1) i) :=
    fun t => {z | (z.1 : Fin (n + 2) → ℝ) t.1 = 0}
  -- the piece map attached to the `j`-th face
  let G : (t : {j : Fin (n + 2) // j ≠ i}) → ↥(TopHorn (n + 1) i) → X := fun t z =>
    g t.1 t.2 (if h : (z.1 : Fin (n + 2) → ℝ) t.1 = 0
      then stdSimplexDel (k := n + 1) t.1 z.1 h else pt)
  have hEclosed : ∀ t, IsClosed (E t) := by
    intro t
    have hcont : Continuous fun z : ↥(TopHorn (n + 1) i) => (z.1 : Fin (n + 2) → ℝ) t.1 :=
      (continuous_apply t.1).comp
        ((continuous_subtype_val (p := fun w : Fin (n + 2) → ℝ =>
            w ∈ stdSimplex ℝ (Fin (n + 2)))).comp
          (continuous_subtype_val (p := TopHorn (n + 1) i)))
    exact isClosed_eq hcont continuous_const
  -- the piece maps are continuous on their own faces
  have hGcont : ∀ t, ContinuousOn (G t) (E t) := by
    intro t
    rw [continuousOn_iff_continuous_domRestrict]
    have hpiece : ∀ z : ↥(E t), G t z.1 =
        g t.1 t.2 (stdSimplexDel (k := n + 1) t.1 z.1.1 z.2) := by
      intro z
      show g t.1 t.2 (if h : (z.1.1 : Fin (n + 2) → ℝ) t.1 = 0
          then stdSimplexDel (k := n + 1) t.1 z.1.1 h else pt)
        = g t.1 t.2 (stdSimplexDel (k := n + 1) t.1 z.1.1 z.2)
      exact congrArg _ (dif_pos z.2)
    refine Continuous.congr ?_ (fun z => (hpiece z).symm)
    refine (g t.1 t.2).continuous.comp ?_
    refine Continuous.subtype_mk (continuous_pi fun l => ?_) _
    exact (continuous_apply (Fin.succAbove t.1 l)).comp
      (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_subtype_val))
  -- the key compatibility: two pieces agree on the overlap of their faces
  have hGpair : ∀ (s t : {j : Fin (n + 2) // j ≠ i}) (z : ↥(TopHorn (n + 1) i)),
      s.1 < t.1 → z ∈ E s → z ∈ E t → G s z = G t z := by
    intro s t z hlt hs ht
    have hs' : (z.1 : Fin (n + 2) → ℝ) s.1 = 0 := hs
    have ht' : (z.1 : Fin (n + 2) → ℝ) t.1 = 0 := ht
    have hGs : G s z = g s.1 s.2 (stdSimplexDel (k := n + 1) s.1 z.1 hs') := by
      show g s.1 s.2 (if h : (z.1 : Fin (n + 2) → ℝ) s.1 = 0
          then stdSimplexDel (k := n + 1) s.1 z.1 h else pt)
        = g s.1 s.2 (stdSimplexDel (k := n + 1) s.1 z.1 hs')
      exact congrArg _ (dif_pos hs')
    have hGt : G t z = g t.1 t.2 (stdSimplexDel (k := n + 1) t.1 z.1 ht') := by
      show g t.1 t.2 (if h : (z.1 : Fin (n + 2) → ℝ) t.1 = 0
          then stdSimplexDel (k := n + 1) t.1 z.1 h else pt)
        = g t.1 t.2 (stdSimplexDel (k := n + 1) t.1 z.1 ht')
      exact congrArg _ (dif_pos ht')
    rw [hGs, hGt]
    -- the deleted points
    have hw0 : ((stdSimplexDel (k := n + 1) s.1 z.1 hs') : Fin (n + 1) → ℝ)
        (t.1.pred (Fin.ne_zero_of_lt hlt)) = 0 := by
      rw [stdSimplexDel_apply, succAbove_pred_eq s.1 t.1 hlt, ht']
    have hw0' : ((stdSimplexDel (k := n + 1) t.1 z.1 ht') : Fin (n + 1) → ℝ)
        (s.1.castPred (Fin.ne_last_of_lt hlt)) = 0 := by
      rw [stdSimplexDel_apply, succAbove_castPred_eq s.1 t.1 hlt, hs']
    -- the double deletion of the two vanishing coordinates is the same point of `Δ^{n-1}`
    have hww : stdSimplexDel (k := n) (t.1.pred (Fin.ne_zero_of_lt hlt))
          (stdSimplexDel (k := n + 1) s.1 z.1 hs') hw0
        = stdSimplexDel (k := n) (s.1.castPred (Fin.ne_last_of_lt hlt))
          (stdSimplexDel (k := n + 1) t.1 z.1 ht') hw0' :=
      stdSimplexDel_stdSimplexDel s.1 t.1 hlt z.1 hs' ht' hw0 hw0'
    -- the two ways of reading the common `(n-1)`-simplex
    have hmap_s : stdSimplex.map (Fin.succAbove (t.1.pred (Fin.ne_zero_of_lt hlt)))
        (stdSimplexDel (k := n) (t.1.pred (Fin.ne_zero_of_lt hlt))
          (stdSimplexDel (k := n + 1) s.1 z.1 hs') hw0)
        = stdSimplexDel (k := n + 1) s.1 z.1 hs' :=
      map_succAbove_stdSimplexDel _ _ hw0
    have hmap_t : stdSimplex.map (Fin.succAbove (s.1.castPred (Fin.ne_last_of_lt hlt)))
        (stdSimplexDel (k := n) (t.1.pred (Fin.ne_zero_of_lt hlt))
          (stdSimplexDel (k := n + 1) s.1 z.1 hs') hw0)
        = stdSimplexDel (k := n + 1) t.1 z.1 ht' := by
      rw [hww]
      exact map_succAbove_stdSimplexDel _ _ hw0'
    calc g s.1 s.2 (stdSimplexDel (k := n + 1) s.1 z.1 hs')
        = g s.1 s.2 (stdSimplex.map (Fin.succAbove (t.1.pred (Fin.ne_zero_of_lt hlt)))
            (stdSimplexDel (k := n) (t.1.pred (Fin.ne_zero_of_lt hlt))
              (stdSimplexDel (k := n + 1) s.1 z.1 hs') hw0)) := by rw [hmap_s]
      _ = (⇑(g s.1 s.2) ∘ (stdSimplex.map (Fin.succAbove (t.1.pred (Fin.ne_zero_of_lt hlt)))))
            (stdSimplexDel (k := n) (t.1.pred (Fin.ne_zero_of_lt hlt))
              (stdSimplexDel (k := n + 1) s.1 z.1 hs') hw0) := rfl
      _ = (⇑(g t.1 t.2) ∘ (stdSimplex.map (Fin.succAbove (s.1.castPred (Fin.ne_last_of_lt hlt)))))
            (stdSimplexDel (k := n) (t.1.pred (Fin.ne_zero_of_lt hlt))
              (stdSimplexDel (k := n + 1) s.1 z.1 hs') hw0) := by
            rw [hcomp s.1 t.1 s.2 t.2 hlt]
      _ = g t.1 t.2 (stdSimplex.map (Fin.succAbove (s.1.castPred (Fin.ne_last_of_lt hlt)))
            (stdSimplexDel (k := n) (t.1.pred (Fin.ne_zero_of_lt hlt))
              (stdSimplexDel (k := n + 1) s.1 z.1 hs') hw0)) := rfl
      _ = g t.1 t.2 (stdSimplexDel (k := n + 1) t.1 z.1 ht') := by rw [hmap_t]
  have hGagree : ∀ s t : {j : Fin (n + 2) // j ≠ i}, ∀ z, z ∈ E s → z ∈ E t → G s z = G t z := by
    intro s t z hs ht
    by_cases hst : s = t
    · rw [hst]
    · have hne : s.1 ≠ t.1 := fun h => hst (Subtype.ext h)
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · exact hGpair s t z hlt hs ht
      · exact (hGpair t s z hlt ht hs).symm
  -- the faces cover the horn
  have hwit : ∀ z : ↥(TopHorn (n + 1) i), ∃ t : {j : Fin (n + 2) // j ≠ i}, z ∈ E t := by
    intro z
    obtain ⟨j, hj, hz⟩ := z.2
    exact ⟨⟨j, hj⟩, hz⟩
  let bfun : ↥(TopHorn (n + 1) i) → X := fun z => G (Classical.choose (hwit z)) z
  have hbval : ∀ (z : ↥(TopHorn (n + 1) i)) (t : {j : Fin (n + 2) // j ≠ i}),
      z ∈ E t → bfun z = G t z := by
    intro z t ht
    exact hGagree (Classical.choose (hwit z)) t z (Classical.choose_spec (hwit z)) ht
  have hcont : Continuous bfun := by
    rw [continuous_iff_isClosed]
    intro T hT
    have hsub : bfun ⁻¹' T = ⋃ t, (E t ∩ G t ⁻¹' T) := by
      ext z
      constructor
      · intro hz
        refine Set.mem_iUnion.mpr ⟨Classical.choose (hwit z), Classical.choose_spec (hwit z), ?_⟩
        rw [Set.mem_preimage, ← hbval z (Classical.choose (hwit z))
          (Classical.choose_spec (hwit z))]
        exact hz
      · intro hz
        obtain ⟨t, ht1, ht2⟩ := Set.mem_iUnion.mp hz
        rw [Set.mem_preimage] at ht2
        rw [Set.mem_preimage, hbval z t ht1]
        exact ht2
    rw [hsub]
    refine isClosed_iUnion_of_finite fun t => ?_
    obtain ⟨U, hU, hUeq⟩ := (continuousOn_iff_isClosed.mp (hGcont t)) T hT
    have hset : E t ∩ G t ⁻¹' T = U ∩ E t := by
      ext z; constructor
      · rintro ⟨hzE, hzT⟩
        refine ⟨?_, hzE⟩
        have hmem : z ∈ (G t) ⁻¹' T ∩ E t := ⟨hzT, hzE⟩
        rw [hUeq] at hmem
        exact hmem.1
      · rintro ⟨hzU, hzE⟩
        refine ⟨hzE, ?_⟩
        have hmem : z ∈ U ∩ E t := ⟨hzU, hzE⟩
        rw [← hUeq] at hmem
        exact hmem.1
    rw [hset]
    exact hU.inter (hEclosed t)
  refine ⟨⟨bfun, hcont⟩, ?_⟩
  intro j hj
  ext q
  change bfun (faceIncl (n + 1) i j hj q) = g j hj q
  have hzE : faceIncl (n + 1) i j hj q ∈ E ⟨j, hj⟩ := by
    change ((faceIncl (n + 1) i j hj q : ↥(TopHorn (n + 1) i)) :
      Fin (n + 2) → ℝ) j = 0
    rw [faceIncl_coe]
    exact map_succAbove_apply_self j q
  have h1 : bfun (faceIncl (n + 1) i j hj q) = G ⟨j, hj⟩ (faceIncl (n + 1) i j hj q) :=
    hbval _ ⟨j, hj⟩ hzE
  rw [h1]
  have h2 : G ⟨j, hj⟩ (faceIncl (n + 1) i j hj q)
      = g j hj (stdSimplexDel (k := n + 1) j (faceIncl (n + 1) i j hj q).1 hzE) := by
    show g j hj (if h : ((faceIncl (n + 1) i j hj q).1 : Fin (n + 2) → ℝ) j = 0
        then stdSimplexDel (k := n + 1) j (faceIncl (n + 1) i j hj q).1 h else pt)
      = g j hj (stdSimplexDel (k := n + 1) j (faceIncl (n + 1) i j hj q).1 hzE)
    exact congrArg _ (dif_pos hzE)
  rw [h2]
  congr 1
  exact stdSimplexDel_map_succAbove j q hzE

end

end Work.SSS
