import Mathlib
import Submission.Work.Layout.MergeDefs
import Submission.Work.Layout.MergeTraceDefs
import Submission.Work.Layout.MergeLocal

set_option autoImplicit false

/-!
# Bounds on the column and row records of `cmpCost`

`colSum_le`/`rowSum_le` bound the total cost charged to the column records (resp. the row records) by
`9 * Σ_{ks} size + 10 * Σ_{ls} size + 9 * (lengths)`, using `Work.Layout.mergeLocal` per record and the
fact that the records peel off disjoint pieces of `ls` (resp. of `ks`).
-/

namespace Work.Layout

open HvdH

local infixl:50 " <+ " => List.Sublist

/-! ## `dropWhile` and append are sublists -/

theorem sublist_append_left' (l₁ l₂ : List ℕ) : l₁ <+ l₁ ++ l₂ := by
  induction l₁ with
  | nil => simp
  | cons a l ih => simpa using List.Sublist.cons_cons a ih

theorem sublist_append_right' (l₁ l₂ : List ℕ) : l₂ <+ l₁ ++ l₂ := by
  induction l₁ with
  | nil => simp
  | cons a l ih => exact List.Sublist.cons a ih

theorem sublist_sum_le {l₁ l₂ : List ℕ} (h : l₁ <+ l₂) : l₁.sum ≤ l₂.sum := by
  induction h with
  | slnil => simp
  | cons a _ ih => simp only [List.sum_cons]; omega
  | cons_cons a _ ih => simp only [List.sum_cons]; omega

/-- the consumed elements of a column record are `<` its head -/
theorem colRecs_lt (ks ls : List ℕ) : ∀ p ∈ colRecs ks ls, ∀ v ∈ p.2, v < p.1 := by
  induction ks, ls using colRecs.induct with
  | case1 x => simp [colRecs]
  | case2 k ks ls ih =>
      intro p hp v hv
      rw [colRecs] at hp
      simp only [List.mem_cons] at hp
      rcases hp with hp | hp
      · rw [hp] at hv ⊢
        have := List.mem_takeWhile_imp hv
        simpa using this
      · exact ih p hp v hv

/-- the consumed elements of a row record are `≤` its head -/
theorem rowRecs_le (ks ls : List ℕ) : ∀ p ∈ rowRecs ks ls, ∀ v ∈ p.2, v ≤ p.1 := by
  induction ks, ls using rowRecs.induct with
  | case1 x => simp [rowRecs]
  | case2 ks l ls ih =>
      intro p hp v hv
      rw [rowRecs] at hp
      simp only [List.mem_cons] at hp
      rcases hp with hp | hp
      · rw [hp] at hv ⊢
        have := List.mem_takeWhile_imp hv
        simpa using this
      · exact ih p hp v hv

/-- the per-record estimate, from `mergeLocal` -/
theorem pCost_le_of (K : ℕ) (vs : List ℕ) (hnd : vs.Nodup) (hlt : ∀ v ∈ vs, v < K) :
    pCost (K, vs) ≤ 9 * K.size + 10 * (vs.map (fun v => v.size)).sum + 9 * vs.length := by
  have h1 : vs.length * szc K ≤ 9 * K.size + 9 * (vs.map (fun v => v.size)).sum + 5 * vs.length := by
    simpa only [szc] using mergeLocal K vs hnd hlt
  have h2 : (vs.map szc).sum ≤ (vs.map (fun v => v.size)).sum :=
    List.sum_le_sum (fun v _ => size_le_self v.size)
  simp only [pCost]
  omega

theorem colSum_le : ∀ ks ls : List ℕ, (ks ++ ls).Nodup →
    ((colRecs ks ls).map pCost).sum
      ≤ 9 * (ks.map (fun k => k.size)).sum + 10 * (ls.map (fun l => l.size)).sum + 9 * ls.length := by
  intro ks ls
  induction ks, ls using colRecs.induct with
  | case1 x => intro _; simp [colRecs]
  | case2 k ks ls ih =>
      intro hnd
      have hlsnd : ls.Nodup := hnd.sublist (sublist_append_right' (k :: ks) ls)
      have hnd' : (ks ++ ls.dropWhile (fun x => decide (x < k))).Nodup :=
        hnd.sublist (List.Sublist.append (List.Sublist.cons k (List.Sublist.refl ks))
          (List.dropWhile_sublist (p := fun x => decide (x < k)) (l := ls)))
      rw [colSum_cons]
      have htake : (ls.takeWhile (fun x => decide (x < k))).Nodup :=
        hlsnd.sublist (List.takeWhile_sublist _)
      have hlt : ∀ v ∈ ls.takeWhile (fun x => decide (x < k)), v < k := by
        intro v hv
        have := List.mem_takeWhile_imp hv
        simpa using this
      have h1 := pCost_le_of k _ htake hlt
      have h2 := ih hnd'
      have hsplit : ((ls.takeWhile (fun x => decide (x < k))).map (fun l => l.size)).sum
            + ((ls.dropWhile (fun x => decide (x < k))).map (fun l => l.size)).sum
            = (ls.map (fun l => l.size)).sum := by
        conv_rhs => rw [← List.takeWhile_append_dropWhile (p := fun x => decide (x < k)) (l := ls)]
        rw [List.map_append, List.sum_append]
      have hsplitlen : (ls.takeWhile (fun x => decide (x < k))).length
            + (ls.dropWhile (fun x => decide (x < k))).length = ls.length := by
        conv_rhs => rw [← List.takeWhile_append_dropWhile (p := fun x => decide (x < k)) (l := ls)]
        rw [List.length_append]
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega

theorem rowSum_le : ∀ ks ls : List ℕ, (ks ++ ls).Nodup →
    ((rowRecs ks ls).map pCost).sum
      ≤ 9 * (ls.map (fun l => l.size)).sum + 10 * (ks.map (fun k => k.size)).sum + 9 * ks.length := by
  intro ks ls
  induction ks, ls using rowRecs.induct with
  | case1 ks => intro _; simp [rowRecs]
  | case2 ks l ls ih =>
      intro hnd
      have hksnd : ks.Nodup := hnd.sublist (sublist_append_left' ks (l :: ls))
      have hdisj : ∀ a ∈ ks, ∀ b ∈ l :: ls, a ≠ b := (List.nodup_append.mp hnd).2.2
      have hnd' : (ks.dropWhile (fun x => decide (x ≤ l)) ++ ls).Nodup :=
        hnd.sublist (List.Sublist.append (List.dropWhile_sublist (p := fun x => decide (x ≤ l)) (l := ks))
          (List.Sublist.cons l (List.Sublist.refl ls)))
      rw [rowSum_cons]
      have htake : (ks.takeWhile (fun x => decide (x ≤ l))).Nodup :=
        hksnd.sublist (List.takeWhile_sublist _)
      have hlt : ∀ u ∈ ks.takeWhile (fun x => decide (x ≤ l)), u < l := by
        intro u hu
        have hle : u ≤ l := by
          have := List.mem_takeWhile_imp hu
          simpa using this
        have humem : u ∈ ks := List.Sublist.mem hu (List.takeWhile_sublist (fun x => decide (x ≤ l)))
        have hne : u ≠ l := fun h => (hdisj u humem l (by simp [h])) h
        omega
      have h1 := pCost_le_of l _ htake hlt
      have h2 := ih hnd'
      have hsplit : ((ks.takeWhile (fun x => decide (x ≤ l))).map (fun k => k.size)).sum
            + ((ks.dropWhile (fun x => decide (x ≤ l))).map (fun k => k.size)).sum
            = (ks.map (fun k => k.size)).sum := by
        conv_rhs => rw [← List.takeWhile_append_dropWhile (p := fun x => decide (x ≤ l)) (l := ks)]
        rw [List.map_append, List.sum_append]
      have hsplitlen : (ks.takeWhile (fun x => decide (x ≤ l))).length
            + (ks.dropWhile (fun x => decide (x ≤ l))).length = ks.length := by
        conv_rhs => rw [← List.takeWhile_append_dropWhile (p := fun x => decide (x ≤ l)) (l := ks)]
        rw [List.length_append]
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega

/-- `Σ_{e ∈ l} (e.size + 2) = Σ_{e ∈ l} e.size + 2|l|` -/
theorem sum_map_add_two (l : List ℕ) :
    (l.map (fun k => k.size + 2)).sum = (l.map (fun k => k.size)).sum + 2 * l.length := by
  induction l with
  | nil => simp
  | cons k l ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring

end Work.Layout
