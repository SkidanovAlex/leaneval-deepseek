import Mathlib
import Submission.Work.Cohomology.SingBridge

/-!
# The singular simplicial set of a topological space is a Kan complex

The singular simplicial set `TopCat.toSSet.obj X` of a topological space has as `n`-simplices
the continuous maps `stdSimplex ℝ (Fin (n+1)) → X`.  We show that it satisfies the horn filling
condition: every morphism `Λ[n+1,i] ⟶ Sing X` extends to `Δ[n+1] ⟶ Sing X`.  The extension is
constructed explicitly by

* gluing the face maps on the *topological* horn `{p | ∃ j ≠ i, p j = 0}` of the standard
  simplex (the compatibility of the faces is the `horn.IsCompatible` condition, transported
  through the orbit of `toSSetObjEquivT`), and
* pushing forward along an explicit continuous retraction of the standard simplex onto the horn
  which fixes the horn pointwise (the "cut off the smallest non-`i` coordinate" retraction).

This implies `SSet.KanComplex (TopCat.toSSet.obj X)` via `SSet.KanComplex.iff`.
-/

namespace Work.StemsB

open CategoryTheory

noncomputable section

/-! ## The formula for `stdSimplex.map` on a fibre -/

private lemma stdSimplex_map_apply_eq {α β : Type*} [Fintype α] [Fintype β] {f : α → β}
    (hf : Function.Injective f) (q : stdSimplex ℝ α) (x : α) :
    (stdSimplex.map f q : β → ℝ) (f x) = (q : α → ℝ) x := by
  classical
  rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  have h : Finset.univ.filter (fun y : α => f y = f x) = {x} := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun h => hf h, fun h => by rw [h]⟩
  rw [h, Finset.sum_singleton]

private lemma stdSimplex_map_apply_of_forall_ne {α β : Type*} [Fintype α] [Fintype β] {f : α → β}
    {k : β} (hk : ∀ y, f y ≠ k) (q : stdSimplex ℝ α) :
    (stdSimplex.map f q : β → ℝ) k = 0 := by
  classical
  rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  rw [Finset.filter_eq_empty_iff.mpr (fun y _ hy => hk y hy), Finset.sum_empty]

private lemma stdSimplex_map_injective {α β : Type*} [Fintype α] [Fintype β] {f : α → β}
    (hf : Function.Injective f) : Function.Injective (stdSimplex.map (S := ℝ) f) := by
  intro q q' h
  ext x
  have h1 := congrArg (fun s : stdSimplex ℝ β => (s : β → ℝ) (f x)) h
  simpa only [stdSimplex_map_apply_eq hf] using h1

/-! ## Deleting a vanishing coordinate -/

private noncomputable def stdSimplexDel {n : ℕ} (j : Fin (n+2)) (p : stdSimplex ℝ (Fin (n+2)))
    (hp : (p : Fin (n+2) → ℝ) j = 0) : stdSimplex ℝ (Fin (n+1)) :=
  ⟨fun l => (p : Fin (n+2) → ℝ) (j.succAbove l),
    ⟨fun l => p.2.1 _, by
      have h := Fin.sum_univ_succAbove (p : Fin (n+2) → ℝ) j
      have hp2 : ∑ i : Fin (n+2), (p : Fin (n+2) → ℝ) i = 1 := p.2.2
      have : ∑ i : Fin (n+1), (p : Fin (n+2) → ℝ) (j.succAbove i) = 1 := by linarith
      simpa using this⟩⟩

private lemma stdSimplexDel_apply {n : ℕ} (j : Fin (n+2)) (p : stdSimplex ℝ (Fin (n+2)))
    (hp : (p : Fin (n+2) → ℝ) j = 0) (l : Fin (n+1)) :
    (stdSimplexDel j p hp : Fin (n+1) → ℝ) l = (p : Fin (n+2) → ℝ) (j.succAbove l) := rfl

/-- A point of the standard simplex with vanishing `j`-th coordinate is the image under the
`j`-th face map of its coordinate-deleted point. -/
private lemma stdSimplex_map_succAbove_del {n : ℕ} (j : Fin (n+2)) (p : stdSimplex ℝ (Fin (n+2)))
    (hp : (p : Fin (n+2) → ℝ) j = 0) :
    stdSimplex.map (j.succAbove) (stdSimplexDel j p hp) = p := by
  classical
  ext k
  show (stdSimplex.map (j.succAbove) (stdSimplexDel j p hp) : Fin (n+2) → ℝ) k =
    (p : Fin (n+2) → ℝ) k
  rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  by_cases hk : k = j
  · rw [hk]
    rw [Finset.filter_eq_empty_iff.mpr (fun x _ hx => Fin.succAbove_ne j x hx), Finset.sum_empty, hp]
  · obtain ⟨x0, hx0⟩ := Fin.exists_succAbove_eq (show k ≠ j from hk)
    have hfil : Finset.univ.filter (fun x : Fin (n+1) => j.succAbove x = k) = {x0} := by
      refine Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx0⟩
      · intro b hb
        exact Fin.succAbove_right_injective ((Finset.mem_filter.mp hb).2.trans hx0.symm)
    rw [hfil, Finset.sum_singleton, stdSimplexDel_apply, hx0]

private lemma continuous_stdSimplexDel {n : ℕ} (j : Fin (n+2)) :
    Continuous (fun p : {p : stdSimplex ℝ (Fin (n+2)) // (p : Fin (n+2) → ℝ) j = 0} =>
      stdSimplexDel j p.1 p.2) := by
  have h : Continuous (fun p : {p : stdSimplex ℝ (Fin (n+2)) // (p : Fin (n+2) → ℝ) j = 0} =>
      ⇑(stdSimplexDel j p.1 p.2)) := by
    rw [continuous_pi_iff]
    intro l
    exact (continuous_apply (j.succAbove l)).comp (continuous_subtype_val.comp continuous_subtype_val)
  exact h.subtype_mk (fun p => (stdSimplexDel j p.1 p.2).2)

/-! ## Three order-theoretic identities for the face maps -/

private lemma succAbove_pred_eq {n : ℕ} {j k : Fin (n+2)} (hjk : j < k) :
    j.succAbove (k.pred (Fin.ne_zero_of_lt hjk)) = k := by
  rw [Fin.succAbove_of_le_castSucc]
  · exact Fin.succ_pred k _
  · simp only [Fin.le_def, Fin.val_castSucc, Fin.val_pred]
    have := hjk; simp only [Fin.lt_def] at this; omega

private lemma succAbove_castPred_eq {n : ℕ} {j k : Fin (n+2)} (hjk : j < k) :
    k.succAbove (j.castPred (Fin.ne_last_of_lt hjk)) = j := by
  rw [Fin.succAbove_of_castSucc_lt]
  · exact Fin.castSucc_castPred j _
  · rw [Fin.castSucc_castPred j _]; exact hjk

private lemma succAbove_comp_eq {n : ℕ} {j k : Fin (n+2)} (hjk : j < k) :
    j.succAbove ∘ (k.pred (Fin.ne_zero_of_lt hjk)).succAbove =
      k.succAbove ∘ (j.castPred (Fin.ne_last_of_lt hjk)).succAbove := by
  funext l
  simp only [Function.comp_apply]
  have hA := succAbove_pred_eq hjk
  have hB : (k.pred (Fin.ne_zero_of_lt hjk)).predAbove j = j.castPred (Fin.ne_last_of_lt hjk) := by
    have hle : j ≤ (k.pred (Fin.ne_zero_of_lt hjk)).castSucc := by
      simp only [Fin.le_def, Fin.val_castSucc, Fin.val_pred]
      have := hjk; simp only [Fin.lt_def] at this; omega
    rw [Fin.predAbove_of_le_castSucc _ _ hle]
  have h := Fin.succAbove_succAbove_succAbove_predAbove j (k.pred (Fin.ne_zero_of_lt hjk)) l
  simp only [hA, hB] at h
  exact h.symm

/-! ## The retraction of the standard simplex onto the horn -/

private theorem hmin_finset_nonempty {n : ℕ} (i : Fin (n+2)) :
    (Finset.univ : Finset {j : Fin (n+2) // j ≠ i}).Nonempty := by
  have hcard : 1 < Fintype.card (Fin (n+2)) := by rw [Fintype.card_fin]; omega
  obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card hcard i
  exact ⟨⟨j, hj⟩, Finset.mem_univ _⟩

/-- The minimum of the coordinates other than `i`. -/
private noncomputable def hmin {n : ℕ} (i : Fin (n+2)) (p : stdSimplex ℝ (Fin (n+2))) : ℝ :=
  (Finset.univ : Finset {j : Fin (n+2) // j ≠ i}).inf' (hmin_finset_nonempty i)
    (fun j => (p : Fin (n+2) → ℝ) j.1)

private lemma hmin_le {n : ℕ} (i : Fin (n+2)) (p : stdSimplex ℝ (Fin (n+2)))
    (j : Fin (n+2)) (hj : j ≠ i) : hmin i p ≤ (p : Fin (n+2) → ℝ) j :=
  Finset.inf'_le (s := (Finset.univ : Finset {j : Fin (n+2) // j ≠ i})) _ (Finset.mem_univ ⟨j, hj⟩)

private lemma hmin_nonneg {n : ℕ} (i : Fin (n+2)) (p : stdSimplex ℝ (Fin (n+2))) :
    0 ≤ hmin i p := by
  obtain ⟨b, -, hb2⟩ := (Finset.inf'_le_iff (hmin_finset_nonempty i)).mp
    (le_refl (hmin i p))
  exact le_trans (p.2.1 b.1) hb2

private lemma exists_hmin_eq {n : ℕ} (i : Fin (n+2)) (p : stdSimplex ℝ (Fin (n+2))) :
    ∃ j : Fin (n+2), j ≠ i ∧ hmin i p = (p : Fin (n+2) → ℝ) j := by
  obtain ⟨b, -, hb2⟩ := (Finset.inf'_le_iff (hmin_finset_nonempty i)).mp
    (le_refl (hmin i p))
  exact ⟨b.1, b.2, le_antisymm (hmin_le i p b.1 b.2) hb2⟩

/-- The retraction of the standard simplex onto the horn, obtained by subtracting the smallest
non-`i` coordinate from every non-`i` coordinate and adding it back (with multiplicity) to the
`i`-th coordinate.  It fixes the horn pointwise. -/
private noncomputable def hret {n : ℕ} (i : Fin (n+2)) (p : stdSimplex ℝ (Fin (n+2))) :
    stdSimplex ℝ (Fin (n+2)) :=
  ⟨fun l => if l = i then (p : Fin (n+2) → ℝ) l + ((n+1 : ℕ) : ℝ) * hmin i p
            else (p : Fin (n+2) → ℝ) l - hmin i p,
   ⟨fun l => by
      rw [show (fun l => if l = i then (p : Fin (n+2) → ℝ) l + ((n+1 : ℕ) : ℝ) * hmin i p
              else (p : Fin (n+2) → ℝ) l - hmin i p) l
            = (if l = i then (p : Fin (n+2) → ℝ) l + ((n+1 : ℕ) : ℝ) * hmin i p
              else (p : Fin (n+2) → ℝ) l - hmin i p) from rfl]
      by_cases hl : l = i
      · rw [if_pos hl, hl]
        have h1 : (0:ℝ) ≤ (p : Fin (n+2) → ℝ) i := p.2.1 i
        have h2 : (0:ℝ) ≤ ((n+1 : ℕ) : ℝ) * hmin i p := by
          have := hmin_nonneg i p; positivity
        linarith
      · rw [if_neg hl]
        have := hmin_le i p l hl
        linarith,
    by
      rw [← Finset.sum_erase_add (Finset.univ : Finset (Fin (n+2))) _ (Finset.mem_univ i)]
      have hcongr : ∑ x ∈ (Finset.univ : Finset (Fin (n+2))).erase i,
            (if x = i then (p : Fin (n+2) → ℝ) x + ((n+1 : ℕ) : ℝ) * hmin i p
              else (p : Fin (n+2) → ℝ) x - hmin i p)
          = ∑ x ∈ (Finset.univ : Finset (Fin (n+2))).erase i,
            ((p : Fin (n+2) → ℝ) x - hmin i p) := by
        refine Finset.sum_congr rfl (fun x hx => ?_)
        rw [if_neg (Finset.mem_erase.mp hx).1]
      rw [hcongr, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
        Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_fin]
      have h1 : ∑ x ∈ (Finset.univ : Finset (Fin (n+2))).erase i, (p : Fin (n+2) → ℝ) x
          = 1 - (p : Fin (n+2) → ℝ) i := by
        have h2 := Finset.sum_erase_add (Finset.univ : Finset (Fin (n+2)))
          (fun x => (p : Fin (n+2) → ℝ) x) (Finset.mem_univ i)
        have h3 : (Finset.univ : Finset (Fin (n+2))).sum
            (fun x => (p : Fin (n+2) → ℝ) x) = 1 := p.2.2
        linarith
      rw [h1, if_pos rfl]
      have hcard : ((n + 2 - 1 : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) := rfl
      rw [hcard]
      ring⟩⟩

private lemma hret_coord {n : ℕ} (i : Fin (n+2)) (p : stdSimplex ℝ (Fin (n+2)))
    (l : Fin (n+2)) :
    (hret i p : Fin (n+2) → ℝ) l
      = if l = i then (p : Fin (n+2) → ℝ) l + ((n+1 : ℕ) : ℝ) * hmin i p
        else (p : Fin (n+2) → ℝ) l - hmin i p := rfl

private lemma hret_mem_horn {n : ℕ} (i : Fin (n+2)) (p : stdSimplex ℝ (Fin (n+2))) :
    ∃ j : Fin (n+2), j ≠ i ∧ (hret i p : Fin (n+2) → ℝ) j = 0 := by
  obtain ⟨j, hj, hj2⟩ := exists_hmin_eq i p
  refine ⟨j, hj, ?_⟩
  rw [hret_coord, if_neg hj]
  linarith [hj2]

private lemma hret_fixed {n : ℕ} (i : Fin (n+2)) (p : stdSimplex ℝ (Fin (n+2)))
    (j : Fin (n+2)) (hj : j ≠ i) (hp : (p : Fin (n+2) → ℝ) j = 0) : hret i p = p := by
  have hμ0 : hmin i p = 0 := le_antisymm (by rw [← hp]; exact hmin_le i p j hj) (hmin_nonneg i p)
  ext l
  rw [hret_coord]
  by_cases hl : l = i
  · rw [if_pos hl, hμ0]; ring
  · rw [if_neg hl, hμ0]; ring

private lemma continuous_hmin {n : ℕ} (i : Fin (n+2)) : Continuous (hmin i) := by
  have h : hmin i = (Finset.univ : Finset {j : Fin (n+2) // j ≠ i}).inf' (hmin_finset_nonempty i)
      (fun j (p : stdSimplex ℝ (Fin (n+2))) => (p : Fin (n+2) → ℝ) j.1) := by
    funext p
    rw [Finset.inf'_apply]
    rfl
  rw [h]
  exact Continuous.finset_inf' _ (fun j _ => (continuous_apply j.1).comp continuous_subtype_val)

private lemma continuous_hret {n : ℕ} (i : Fin (n+2)) : Continuous (hret i) := by
  have h : Continuous (fun p : stdSimplex ℝ (Fin (n+2)) => ⇑(hret i p)) := by
    rw [continuous_pi_iff]
    intro l
    by_cases hl : l = i
    · have hh : (fun p : stdSimplex ℝ (Fin (n+2)) => ⇑(hret i p) l) =
          fun (p : stdSimplex ℝ (Fin (n+2))) =>
            (p : Fin (n+2) → ℝ) l + ((n+1 : ℕ) : ℝ) * hmin i p := by
        funext p
        rw [hret_coord, if_pos hl]
      rw [hh]
      exact ((continuous_apply l).comp continuous_subtype_val).add
        (continuous_const.mul (continuous_hmin i))
    · have hh : (fun p : stdSimplex ℝ (Fin (n+2)) => ⇑(hret i p) l) =
          fun (p : stdSimplex ℝ (Fin (n+2))) => (p : Fin (n+2) → ℝ) l - hmin i p := by
        funext p
        rw [hret_coord, if_neg hl]
      rw [hh]
      exact ((continuous_apply l).comp continuous_subtype_val).sub (continuous_hmin i)
  exact h.subtype_mk fun p => (hret i p).2

/-! ## The topological horn -/

/-- The horn `Λ[n+1,i]` of the standard simplex, as a subset of the topological simplex. -/
private abbrev HornSpace (n : ℕ) (i : Fin (n+2)) : Type :=
  {p : stdSimplex ℝ (Fin (n+2)) // ∃ j : Fin (n+2), j ≠ i ∧ (p : Fin (n+2) → ℝ) j = 0}

/-! ## The agreement of the face maps -/

variable {X : Type*} [TopologicalSpace X]

/-- The face maps attached to a compatible family of `(m+1)`-simplices agree on the overlaps of
the corresponding faces of the `(m+2)`-simplex. -/
private lemma agree_lt {m : ℕ} {i : Fin (m+3)}
    {g : (j : Fin (m+3)) → j ≠ i → C(stdSimplex ℝ (Fin (m+2)), X)}
    (hcomp : ∀ (j k : Fin (m+3)) (hj : j ≠ i) (hk : k ≠ i) (hjk : j < k),
      ⇑(g j hj) ∘ (stdSimplex.map (k.pred (Fin.ne_zero_of_lt hjk)).succAbove) =
      ⇑(g k hk) ∘ (stdSimplex.map (j.castPred (Fin.ne_last_of_lt hjk)).succAbove))
    {j k : Fin (m+3)} (hjk : j < k) (hj : j ≠ i) (hk : k ≠ i)
    (qj qk : stdSimplex ℝ (Fin (m+2)))
    (h : stdSimplex.map (j.succAbove) qj = stdSimplex.map (k.succAbove) qk) :
    g j hj qj = g k hk qk := by
  have hA := succAbove_pred_eq hjk
  have hB := succAbove_castPred_eq hjk
  have hC := succAbove_comp_eq hjk
  have h1 : (stdSimplex.map (j.succAbove) qj : Fin (m+3) → ℝ) k = 0 := by
    rw [h]
    exact stdSimplex_map_apply_of_forall_ne (f := k.succAbove) (fun y => Fin.succAbove_ne k y) qk
  have h2 : (stdSimplex.map (j.succAbove) qj : Fin (m+3) → ℝ)
      (j.succAbove (k.pred (Fin.ne_zero_of_lt hjk)))
      = (qj : Fin (m+2) → ℝ) (k.pred (Fin.ne_zero_of_lt hjk)) :=
    stdSimplex_map_apply_eq Fin.succAbove_right_injective qj _
  rw [hA] at h2
  have hqj : (qj : Fin (m+2) → ℝ) (k.pred (Fin.ne_zero_of_lt hjk)) = 0 := by
    rw [h2] at h1; exact h1
  have h3 : (stdSimplex.map (k.succAbove) qk : Fin (m+3) → ℝ) j = 0 := by
    rw [← h]
    exact stdSimplex_map_apply_of_forall_ne (f := j.succAbove) (fun y => Fin.succAbove_ne j y) qj
  have h4 : (stdSimplex.map (k.succAbove) qk : Fin (m+3) → ℝ)
      (k.succAbove (j.castPred (Fin.ne_last_of_lt hjk)))
      = (qk : Fin (m+2) → ℝ) (j.castPred (Fin.ne_last_of_lt hjk)) :=
    stdSimplex_map_apply_eq Fin.succAbove_right_injective qk _
  rw [hB] at h4
  have hqk : (qk : Fin (m+2) → ℝ) (j.castPred (Fin.ne_last_of_lt hjk)) = 0 := by
    rw [h4] at h3; exact h3
  obtain ⟨r, hr⟩ : ∃ r : stdSimplex ℝ (Fin (m+1)),
      stdSimplex.map (k.pred (Fin.ne_zero_of_lt hjk)).succAbove r = qj :=
    ⟨stdSimplexDel _ qj hqj, stdSimplex_map_succAbove_del _ qj hqj⟩
  obtain ⟨r', hr'⟩ : ∃ r : stdSimplex ℝ (Fin (m+1)),
      stdSimplex.map (j.castPred (Fin.ne_last_of_lt hjk)).succAbove r = qk :=
    ⟨stdSimplexDel _ qk hqk, stdSimplex_map_succAbove_del _ qk hqk⟩
  have hrr : r = r' := by
    have hm : stdSimplex.map (j.succAbove)
          (stdSimplex.map (k.pred (Fin.ne_zero_of_lt hjk)).succAbove r)
        = stdSimplex.map (k.succAbove)
          (stdSimplex.map (j.castPred (Fin.ne_last_of_lt hjk)).succAbove r') := by
      rw [hr, hr']; exact h
    rw [stdSimplex.map_comp_apply (k.pred (Fin.ne_zero_of_lt hjk)).succAbove j.succAbove r,
      stdSimplex.map_comp_apply (j.castPred (Fin.ne_last_of_lt hjk)).succAbove k.succAbove r'] at hm
    rw [hC] at hm
    exact stdSimplex_map_injective
      (hC ▸ Fin.succAbove_right_injective.comp Fin.succAbove_right_injective) hm
  rw [← hr, ← hr', ← hrr]
  have := congrFun (hcomp j k hj hk hjk) r
  simpa only [Function.comp_apply] using this

private lemma agree {m : ℕ} {i : Fin (m+3)}
    {g : (j : Fin (m+3)) → j ≠ i → C(stdSimplex ℝ (Fin (m+2)), X)}
    (hcomp : ∀ (j k : Fin (m+3)) (hj : j ≠ i) (hk : k ≠ i) (hjk : j < k),
      ⇑(g j hj) ∘ (stdSimplex.map (k.pred (Fin.ne_zero_of_lt hjk)).succAbove) =
      ⇑(g k hk) ∘ (stdSimplex.map (j.castPred (Fin.ne_last_of_lt hjk)).succAbove))
    {j k : Fin (m+3)} (hj : j ≠ i) (hk : k ≠ i)
    (qj qk : stdSimplex ℝ (Fin (m+2)))
    (h : stdSimplex.map (j.succAbove) qj = stdSimplex.map (k.succAbove) qk) :
    g j hj qj = g k hk qk := by
  rcases lt_trichotomy j k with hlt | heq | hgt
  · exact agree_lt hcomp hlt hj hk qj qk h
  · subst heq
    have hq : qj = qk := stdSimplex_map_injective Fin.succAbove_right_injective h
    rw [hq]
  · exact (agree_lt hcomp hgt hk hj qk qj h.symm).symm

/-! ## The glued map on the horn -/

private noncomputable def hglue {m : ℕ} (i : Fin (m+3))
    (g : (j : Fin (m+3)) → j ≠ i → C(stdSimplex ℝ (Fin (m+2)), X))
    (p : HornSpace (m+1) i) : X :=
  g (Classical.choose p.2) (Classical.choose_spec p.2).1
    (stdSimplexDel (Classical.choose p.2) p.1 (Classical.choose_spec p.2).2)

private lemma hglue_apply {m : ℕ} {i : Fin (m+3)}
    {g : (j : Fin (m+3)) → j ≠ i → C(stdSimplex ℝ (Fin (m+2)), X)}
    (hcomp : ∀ (j k : Fin (m+3)) (hj : j ≠ i) (hk : k ≠ i) (hjk : j < k),
      ⇑(g j hj) ∘ (stdSimplex.map (k.pred (Fin.ne_zero_of_lt hjk)).succAbove) =
      ⇑(g k hk) ∘ (stdSimplex.map (j.castPred (Fin.ne_last_of_lt hjk)).succAbove))
    (p : HornSpace (m+1) i) (j : Fin (m+3)) (hj : j ≠ i)
    (hp : (p.1 : Fin (m+3) → ℝ) j = 0) :
    hglue i g p = g j hj (stdSimplexDel j p.1 hp) :=
  agree hcomp (show Classical.choose p.2 ≠ i from (Classical.choose_spec p.2).1) hj _ _
    (by rw [stdSimplex_map_succAbove_del, stdSimplex_map_succAbove_del])

private lemma continuous_hglue {m : ℕ} (i : Fin (m+3))
    (g : (j : Fin (m+3)) → j ≠ i → C(stdSimplex ℝ (Fin (m+2)), X))
    (hcomp : ∀ (j k : Fin (m+3)) (hj : j ≠ i) (hk : k ≠ i) (hjk : j < k),
      ⇑(g j hj) ∘ (stdSimplex.map (k.pred (Fin.ne_zero_of_lt hjk)).succAbove) =
      ⇑(g k hk) ∘ (stdSimplex.map (j.castPred (Fin.ne_last_of_lt hjk)).succAbove)) :
    Continuous (hglue (m := m) i g) := by
  have hcov : (⋃ j : {j : Fin (m+3) // j ≠ i},
      {p : HornSpace (m+1) i | (p.1 : Fin (m+3) → ℝ) j.1 = 0}) = Set.univ := by
    refine Set.eq_univ_of_forall (fun p => ?_)
    obtain ⟨j, hj, hp⟩ := p.2
    exact Set.mem_iUnion.mpr ⟨⟨j, hj⟩, hp⟩
  rw [← continuousOn_univ, ← hcov]
  refine LocallyFinite.continuousOn_iUnion (locallyFinite_of_finite _) (fun j => ?_)
    (fun j => ?_)
  · exact isClosed_eq ((continuous_apply j.1).comp
      (continuous_subtype_val.comp continuous_subtype_val)) continuous_const
  · rw [continuousOn_iff_continuous_domRestrict]
    refine Continuous.congr ?_ (fun p => (hglue_apply hcomp p.1 j j.2 p.2).symm)
    have hχ : Continuous (fun p : ↥{p : HornSpace (m+1) i | (p.1 : Fin (m+3) → ℝ) j.1 = 0} =>
        (⟨p.1.1, p.2⟩ : {q : stdSimplex ℝ (Fin (m+3)) // (q : Fin (m+3) → ℝ) j.1 = 0})) :=
      Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) (fun p => p.2)
    exact (g j j.2).continuous.comp ((continuous_stdSimplexDel j.1).comp hχ)

/-! ## The singular simplicial set is a Kan complex -/

private lemma stdSimplex_delta_comp_sigma_zero (j : Fin 2) :
    SSet.stdSimplex.δ j ≫ SSet.stdSimplex.σ (0 : Fin 1) =
      𝟙 (SSet.stdSimplex.obj (SimplexCategory.mk 0)) := by
  fin_cases j
  · exact CosimplicialObject.δ_comp_σ_self (X := SSet.stdSimplex) (i := (0 : Fin 1))
  · exact CosimplicialObject.δ_comp_σ_succ (X := SSet.stdSimplex) (i := (0 : Fin 1))

/-- The face maps of the singular simplicial set, as continuous maps of the topological
standard simplices. -/
private noncomputable def hornData (X : TopCat) (m : ℕ) (i : Fin (m+3))
    (f : (j : Fin (m+3)) → j ≠ i →
      (SSet.stdSimplex.obj (SimplexCategory.mk (m+1)) ⟶ TopCat.toSSet.obj X))
    (j : Fin (m+3)) (hj : j ≠ i) : C(stdSimplex ℝ (Fin (m+2)), ↥X) :=
  X.toSSetObjEquivT (Opposite.op (SimplexCategory.mk (m+1))) (SSet.yonedaEquiv (f j hj))

theorem kanComplex_singularSet (X : TopCat) : SSet.KanComplex (TopCat.toSSet.obj X) := by
  rw [SSet.KanComplex.iff]
  intro n i f hf
  rcases n with _ | m
  · -- `n = 0`: the horn `Λ[1,i]` has a single face, which is a degenerate `1`-simplex.
    obtain ⟨j₀, hj₀⟩ := Fintype.exists_ne_of_one_lt_card (α := Fin 2) (by decide) i
    refine ⟨SSet.stdSimplex.σ (0 : Fin 1) ≫ f j₀ hj₀, fun j hj => ?_⟩
    have hjj : j = j₀ := by
      fin_cases i <;> fin_cases j <;> fin_cases j₀ <;> simp_all
    subst hjj
    rw [← Category.assoc, stdSimplex_delta_comp_sigma_zero, Category.id_comp]
  · -- `n = m + 1`
    have hcomp : ∀ (j k : Fin (m+3)) (hj : j ≠ i) (hk : k ≠ i) (hjk : j < k),
        ⇑(hornData X m i f j hj) ∘ (stdSimplex.map (k.pred (Fin.ne_zero_of_lt hjk)).succAbove) =
        ⇑(hornData X m i f k hk) ∘
          (stdSimplex.map (j.castPred (Fin.ne_last_of_lt hjk)).succAbove) := by
      intro j k hj hk hjk
      have h1 : SSet.stdSimplex.δ (k.pred (Fin.ne_zero_of_lt hjk)) ≫ f j hj =
          SSet.stdSimplex.δ (j.castPred (Fin.ne_last_of_lt hjk)) ≫ f k hk :=
        (SSet.horn.isCompatible_iff (n := m) f).mp hf j k hj hk hjk
      have h2 := congrArg (fun (φ : SSet.stdSimplex.obj (SimplexCategory.mk m) ⟶
          TopCat.toSSet.obj X) => X.toSSetObjEquivT (Opposite.op (SimplexCategory.mk m))
            (SSet.yonedaEquiv φ)) h1
      rw [SSet.stdSimplex.yonedaEquiv_δ_comp, SSet.stdSimplex.yonedaEquiv_δ_comp] at h2
      ext z
      have h3 := congrArg (fun (ψ : C(stdSimplex ℝ (Fin (m+1)), ↥X)) => ψ z) h2
      simpa only [Function.comp_apply, TopCat.toSSetObjEquivT_δ_apply, hornData] using h3
    have hFex : ∃ F : C(stdSimplex ℝ (Fin (m+3)), ↥X),
        ∀ (j : Fin (m+3)) (hj : j ≠ i),
          ⇑F ∘ (stdSimplex.map (j.succAbove)) = ⇑(hornData X m i f j hj) := by
      refine ⟨⟨fun p => hglue i (hornData X m i f) ⟨hret i p, hret_mem_horn i p⟩,
        (continuous_hglue i (hornData X m i f) hcomp).comp
          ((continuous_hret i).subtype_mk (fun p => hret_mem_horn i p))⟩, ?_⟩
      intro j hj
      funext q
      have hmem : (stdSimplex.map (j.succAbove) q : Fin (m+3) → ℝ) j = 0 :=
        stdSimplex_map_apply_of_forall_ne (f := j.succAbove) (fun y => Fin.succAbove_ne j y) q
      have hphi : hret i (stdSimplex.map (j.succAbove) q) = stdSimplex.map (j.succAbove) q :=
        hret_fixed i _ j hj hmem
      show hglue i (hornData X m i f)
          ⟨hret i (stdSimplex.map (j.succAbove) q), hret_mem_horn i _⟩ = hornData X m i f j hj q
      rw [show (⟨hret i (stdSimplex.map (j.succAbove) q), hret_mem_horn i _⟩ : HornSpace (m+1) i)
            = ⟨stdSimplex.map (j.succAbove) q, ⟨j, hj, hmem⟩⟩ from Subtype.ext hphi,
        hglue_apply hcomp _ j hj hmem]
      show (hornData X m i f j hj)
          (stdSimplexDel j (stdSimplex.map (j.succAbove) q) hmem) = hornData X m i f j hj q
      rw [show stdSimplexDel j (stdSimplex.map (j.succAbove) q) hmem = q from
        stdSimplex_map_injective (f := j.succAbove) Fin.succAbove_right_injective
          (by rw [stdSimplex_map_succAbove_del])]
    obtain ⟨F, hF⟩ := hFex
    have hy : X.toSSetObjEquivT (Opposite.op (SimplexCategory.mk (m+2)))
        ((X.toSSetObjEquivT (Opposite.op (SimplexCategory.mk (m+2)))).symm F) = F :=
      Equiv.apply_symm_apply _ F
    refine ⟨SSet.yonedaEquiv.symm ((X.toSSetObjEquivT (Opposite.op (SimplexCategory.mk (m+2)))).symm F),
      fun j hj => ?_⟩
    have hinj : Function.Injective (fun ψ : SSet.stdSimplex.obj (SimplexCategory.mk (m+1)) ⟶
        TopCat.toSSet.obj X =>
        X.toSSetObjEquivT (Opposite.op (SimplexCategory.mk (m+1))) (SSet.yonedaEquiv ψ)) :=
      (X.toSSetObjEquivT (Opposite.op (SimplexCategory.mk (m+1)))).injective.comp
        SSet.yonedaEquiv.injective
    apply hinj
    ext z
    show (X.toSSetObjEquivT (Opposite.op (SimplexCategory.mk (m+1))))
        (SSet.yonedaEquiv (SSet.stdSimplex.δ j ≫ SSet.yonedaEquiv.symm
          ((X.toSSetObjEquivT (Opposite.op (SimplexCategory.mk (m+2)))).symm F))) z
      = (X.toSSetObjEquivT (Opposite.op (SimplexCategory.mk (m+1))))
          (SSet.yonedaEquiv (f j hj)) z
    rw [show SSet.yonedaEquiv (SSet.stdSimplex.δ j ≫ SSet.yonedaEquiv.symm
          ((X.toSSetObjEquivT (Opposite.op (SimplexCategory.mk (m+2)))).symm F))
        = (TopCat.toSSet.obj X).δ j
          ((X.toSSetObjEquivT (Opposite.op (SimplexCategory.mk (m+2)))).symm F) from by
      rw [SSet.stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]]
    rw [TopCat.toSSetObjEquivT_δ_apply, hy]
    simpa only [Function.comp_apply, hornData] using congrFun (hF j hj) z

end

end Work.StemsB
