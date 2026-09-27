import Mathlib
import Submission.Work.Drive.boxParity

/-!
# Grouping the boundary contributions of a transversally cut-out zero set

`Submission.Drive.ParityProp` (proved as `Work.Drive.boxParity`) says that the zeros of a smooth
`F : ℝ^{m+1} → ℝ^m` on the boundary of the box are even in number, and the chapters
`intersection_parity`/`intersection_triple` split that number according to which block of coordinates
of the box carries the face.  In the applications one wants to group the faces further, by the
*geometric* meaning of the face — for Hugelmeyer's Lemmas 3 and 4 the boundary components of the
capped manifold are the tubular neighbourhoods of the planes and the two ends of `ℝ × ℝP³`, and
`n_P + n_Q + n_R + n_λ + n_{−λ}` is the resulting five-fold sum.

This file records the grouping in general form: for an arbitrary labelling `Fin (m+1) → σ` of the
faces of the box, the sum over the labels of the number of boundary zeros lying on a face with that
label equals the total number of boundary zeros, hence is even.  The only input is the "exactly one
face" hypothesis of `ParityProp`, which makes each boundary zero lie on a *unique* face, so that the
pieces are disjoint.

This is the step that turns the parity theorems of the intersection chapters into the paper's
`n_P + n_Q + n_R + n_λ + n_{−λ} ≡ 0` bookkeeping.
-/

namespace Work.Drive

open Submission.Drive
open scoped Manifold ContDiff Topology

noncomputable section

/-- **A boundary point cannot lie on two faces.**  If all coordinates of `x` other than the `i`-th
are strictly inside the box, then any coordinate which is `0` or `1` must be the `i`-th one. -/
lemma eq_of_mem_Ioo_of_eq_zero_or_one' {m : ℕ} {x : Amb m} {i i' : Fin (m + 1)}
    (hother : ∀ j, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1) (hxi : x i' = 0 ∨ x i' = 1) : i' = i := by
  by_contra hne
  have hmem := hother i' hne
  rcases hxi with h | h
  · rw [h] at hmem; exact absurd hmem.1 (by norm_num)
  · rw [h] at hmem; exact absurd hmem.2 (by norm_num)

/-- The set of boundary zeros of `F` lying on a face whose label is `s`. -/
def labelMeet {m : ℕ} {σ : Type*} (F : Amb m → Tgt m) (label : Fin (m + 1) → σ) (s : σ) :
    Set (Amb m) :=
  bdyZeros F ∩ {x | ∃ i : Fin (m + 1), label i = s ∧ (x i = 0 ∨ x i = 1)}

/-- A boundary zero lies on at most one face, so the pieces `labelMeet F label s` are pairwise
disjoint. -/
lemma disjoint_labelMeet {m : ℕ} {σ : Type*} (F : Amb m → Tgt m) (label : Fin (m + 1) → σ)
    (hface : ∀ x ∈ unitBoxBdry m, F x = 0 → ∃ i : Fin (m + 1),
      (x i = 0 ∨ x i = 1) ∧ (∀ j, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1))
    {s s' : σ} (h : s ≠ s') : Disjoint (labelMeet F label s) (labelMeet F label s') := by
  rw [Set.disjoint_left]
  rintro x ⟨hxz, i, hi, hxi⟩ ⟨-, i', hi', hxi'⟩
  obtain ⟨k, hk, hother⟩ := hface x hxz.1 hxz.2
  have hik : i = k := eq_of_mem_Ioo_of_eq_zero_or_one' hother hxi
  have hi'k : i' = k := eq_of_mem_Ioo_of_eq_zero_or_one' hother hxi'
  exact h (by rw [← hi, ← hi', hik, hi'k])

/-- The boundary zeros are covered by the pieces `labelMeet F label s`. -/
lemma labelMeet_cover {m : ℕ} {σ : Type*} (F : Amb m → Tgt m) (label : Fin (m + 1) → σ)
    (hface : ∀ x ∈ unitBoxBdry m, F x = 0 → ∃ i : Fin (m + 1),
      (x i = 0 ∨ x i = 1) ∧ (∀ j, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1)) :
    bdyZeros F = ⋃ s, labelMeet F label s := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi, -⟩ := hface x hx.1 hx.2
    exact Set.mem_iUnion.mpr ⟨label i, hx, i, rfl, hi⟩
  · intro hx
    obtain ⟨s, hx'⟩ := Set.mem_iUnion.mp hx
    exact hx'.1

/-- **A sum of cardinalities of pairwise disjoint subsets of a finite set.** -/
lemma ncard_biUnion_eq_sum {α σ : Type*} (A : σ → Set α) (t : Finset σ)
    (hdisj : ∀ s ∈ t, ∀ s' ∈ t, s ≠ s' → Disjoint (A s) (A s')) (hfin : ∀ s ∈ t, (A s).Finite) :
    (⋃ s ∈ t, A s).ncard = ∑ s ∈ t, (A s).ncard := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simp
  | insert a t ha ih =>
      have hdisj_t : ∀ s ∈ t, ∀ s' ∈ t, s ≠ s' → Disjoint (A s) (A s') :=
        fun s hs s' hs' hne =>
          hdisj s (Finset.mem_insert_of_mem hs) s' (Finset.mem_insert_of_mem hs') hne
      have hfin_t : ∀ s ∈ t, (A s).Finite := fun s hs =>
        hfin s (Finset.mem_insert_of_mem hs)
      have ih' := ih hdisj_t hfin_t
      have hdisj_a : Disjoint (A a) (⋃ s ∈ t, A s) := by
        rw [Set.disjoint_left]
        rintro x hx hxu
        obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hxu
        obtain ⟨hst, hxs⟩ := Set.mem_iUnion.mp hs
        refine Set.disjoint_left.mp (hdisj a (Finset.mem_insert_self a t) s
          (Finset.mem_insert_of_mem hst) ?_) hx hxs
        intro habs
        exact ha (by rw [habs]; exact hst)
      have hunion : (⋃ s ∈ insert a t, A s) = A a ∪ ⋃ s ∈ t, A s := by
        ext x
        simp only [Set.mem_iUnion, Finset.mem_insert, Set.mem_union, exists_prop]
        constructor
        · rintro ⟨s, hs | hs, hx⟩
          · rw [hs] at hx
            exact Or.inl hx
          · exact Or.inr ⟨s, hs, hx⟩
        · rintro (hx | ⟨s, hs, hx⟩)
          · exact ⟨a, Or.inl rfl, hx⟩
          · exact ⟨s, Or.inr hs, hx⟩
      have hfinU : (⋃ s ∈ t, A s).Finite :=
        t.finite_toSet.biUnion fun s hs => hfin_t s hs
      rw [hunion, Set.ncard_union_eq hdisj_a (hfin a (Finset.mem_insert_self a t)) hfinU, ih',
        Finset.sum_insert ha]

/-- **Finiteness of each labelled piece.**  Under the hypotheses of `Submission.Drive.ParityProp` the
set of boundary zeros of `F` is finite, hence so is each `labelMeet F label s`; the sum in
`Work.Drive.even_sum_ncard_labelMeet` is therefore a sum of natural numbers. -/
theorem finite_labelMeet {m : ℕ} {σ : Type*} (F : Amb m → Tgt m) (label : Fin (m + 1) → σ)
    (hF : ContDiff ℝ Ctop F)
    (hreg : ∀ x ∈ unitBox m, F x = 0 → Function.Surjective (fderiv ℝ F x))
    (hface : ∀ x ∈ unitBoxBdry m, F x = 0 → ∃ i : Fin (m + 1),
      (x i = 0 ∨ x i = 1) ∧ (∀ j, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1) ∧
      Function.Surjective (fun v : {v : Amb m // v i = 0} => fderiv ℝ F x v.1)) (s : σ) :
    (labelMeet F label s).Finite :=
  (boxParity m F hF hreg hface).1.subset fun _ hx => hx.1

/-- **The parity bookkeeping with the boundary faces grouped by an arbitrary labelling.**  Under the
hypotheses of `Submission.Drive.ParityProp`, the number of boundary zeros of `F` lying on a face with
label `s`, summed over the labels, is even. -/
theorem even_sum_ncard_labelMeet {m : ℕ} {σ : Type*} [Fintype σ]
    (F : Amb m → Tgt m) (hF : ContDiff ℝ Ctop F)
    (hreg : ∀ x ∈ unitBox m, F x = 0 → Function.Surjective (fderiv ℝ F x))
    (hface : ∀ x ∈ unitBoxBdry m, F x = 0 → ∃ i : Fin (m + 1),
      (x i = 0 ∨ x i = 1) ∧ (∀ j, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1) ∧
      Function.Surjective (fun v : {v : Amb m // v i = 0} => fderiv ℝ F x v.1))
    (label : Fin (m + 1) → σ) :
    Even (∑ s : σ, (labelMeet F label s).ncard) := by
  classical
  have hface' : ∀ x ∈ unitBoxBdry m, F x = 0 → ∃ i : Fin (m + 1),
      (x i = 0 ∨ x i = 1) ∧ (∀ j, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1) :=
    fun x hx h0 => (hface x hx h0).imp fun _ h => ⟨h.1, h.2.1⟩
  obtain ⟨hfin, heven⟩ := boxParity m F hF hreg hface
  have hcover := labelMeet_cover F label hface'
  have hsum : (∑ s : σ, (labelMeet F label s).ncard)
      = (⋃ s ∈ (Finset.univ : Finset σ), labelMeet F label s).ncard := by
    rw [ncard_biUnion_eq_sum (A := labelMeet F label) (t := (Finset.univ : Finset σ))]
    · intro s _ s' _ hne
      exact disjoint_labelMeet F label hface' hne
    · intro s _
      exact hfin.subset fun x hx => hx.1
  have hcoverU : (⋃ s ∈ (Finset.univ : Finset σ), labelMeet F label s)
      = ⋃ s, labelMeet F label s := by
    ext x
    simp only [Set.mem_iUnion, Finset.mem_univ, true_and, exists_prop]
  have hsum' : (∑ s : σ, (labelMeet F label s).ncard) = (bdyZeros F).ncard := by
    rw [hsum, hcoverU, ← hcover]
  rw [hsum']
  exact heven

end

end Work.Drive
