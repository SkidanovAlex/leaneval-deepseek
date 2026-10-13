/-
  Area E7 / PadAux: the bounds on `Work.WilE7.tidy X`.

  `tidy X` replaces the list of basic sets of `X` by its `dedup` (same chain, same format).
  Two things are proved here:

  * `(tidy X).deg ≤ X.deg`: the degree of `tidy X` is the sum of the degrees of the *distinct*
    basic sets of `X`, and `dedup` is a sublist of the original list, so its total degree only
    decreases;
  * `(tidy X).basics.length ≤ 1 + X.deg`: the distinct basic sets are at most one more than the
    total degree, because every basic set has degree `0` only if it is the empty basic set
    `⟨[], []⟩` (the atoms have degree `totalDegree + 1 ≥ 1`), and there is at most one such entry
    in a list without repetitions.

  Everything is unconditional and depends only on the frozen vocabulary of area E and on
  `Work.WilE7.PadDefs`.
-/
import Mathlib
import Submission.Work.WilE7.PadDefs

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7.PadAux

open WilkiesDesign WilkiesDesign.E

/-! ## List arithmetic -/

/-- The sum of the images of a sublist is at most the sum of the images of the whole list
(for nonnegative summands, here `ℕ`-valued). -/
theorem tidy_sublist_sum_le {α : Type*} (f : α → ℕ) {l₁ l₂ : List α}
    (h : List.Sublist l₁ l₂) : (l₁.map f).sum ≤ (l₂.map f).sum := by
  induction h with
  | slnil => simp
  | cons a _ ih => simp only [List.map_cons, List.sum_cons]; omega
  | cons_cons a _ ih => simp only [List.map_cons, List.sum_cons]; omega

/-! ## Basic sets of degree zero -/

/-- A nonempty basic set has degree at least `1`: every atom `Q` has degree
`Q.totalDegree + 1 ≥ 1`. -/
theorem tidy_one_le_deg {k r : ℕ} {B : Basic k r} (h : B.eqs ++ B.pos ≠ []) : 1 ≤ B.deg := by
  rw [Basic.deg]
  have hne : (B.eqs ++ B.pos).map atomDeg ≠ [] := fun hc => h (List.map_eq_nil_iff.mp hc)
  have h1 : 1 ≤ ((B.eqs ++ B.pos).map atomDeg).length := by
    cases hmap : (B.eqs ++ B.pos).map atomDeg with
    | nil => exact absurd hmap hne
    | cons a t => simp
  refine le_trans h1 ?_
  simpa using List.length_le_sum_of_one_le ((B.eqs ++ B.pos).map atomDeg) (fun i hi => by
    obtain ⟨Q, -, rfl⟩ := List.mem_map.mp hi
    simp only [atomDeg]
    omega)

/-- The only basic set of degree `0` is the empty basic set `⟨[], []⟩`. -/
theorem tidy_eq_empty_of_deg_eq_zero {k r : ℕ} {B : Basic k r} (h : B.deg = 0) :
    B = ⟨[], []⟩ := by
  have hB : B.eqs = [] ∧ B.pos = [] := by
    have hnil : B.eqs ++ B.pos = [] := by
      by_contra hc
      have := tidy_one_le_deg (k := k) (r := r) hc
      omega
    exact List.append_eq_nil_iff.mp hnil
  cases B
  simp_all

/-! ## The number of distinct basic sets -/

/-- A list of basic sets without repetitions has at most `1 + (sum of the degrees)` entries:
all its entries have degree at least `1`, except for the (at most one) empty basic set. -/
theorem tidy_nodup_length_le_sum {k r : ℕ} :
    ∀ d : List (Basic k r), d.Nodup → d.length ≤ (d.map Basic.deg).sum + 1 := by
  intro d
  induction d with
  | nil => intro _; simp
  | cons B t ih =>
      intro hd
      rw [List.nodup_cons] at hd
      obtain ⟨hBt, htn⟩ := hd
      have iht := ih htn
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      rcases Nat.eq_zero_or_pos B.deg with h0 | hpos
      · rw [h0]
        have hB : B = (⟨[], []⟩ : Basic k r) := tidy_eq_empty_of_deg_eq_zero h0
        have hge : ∀ x ∈ t.map Basic.deg, 1 ≤ x := by
          intro x hx
          obtain ⟨B', hB't, rfl⟩ := List.mem_map.mp hx
          rcases Nat.eq_zero_or_pos B'.deg with h0' | hp'
          · exfalso
            have hB' : B' = (⟨[], []⟩ : Basic k r) := tidy_eq_empty_of_deg_eq_zero h0'
            have hB'B : B' = B := by rw [hB', hB]
            exact hBt (hB'B ▸ hB't)
          · omega
        have hlen : t.length ≤ (t.map Basic.deg).sum := by
          simpa using List.length_le_sum_of_one_le (t.map Basic.deg) hge
        omega
      · omega

/-! ## The bounds for `tidy` -/

theorem tidy_bounds (k : ℕ) (X : WilkiesDesign.E.SemiPf k) :
    (Work.WilE7.tidy X).deg ≤ X.deg ∧ (Work.WilE7.tidy X).basics.length ≤ 1 + X.deg := by
  have hsub : ((X.basics.dedup).map (Basic.deg (k := k) (r := X.r))).sum ≤
      (X.basics.map (Basic.deg (k := k) (r := X.r))).sum :=
    tidy_sublist_sum_le _ (List.dedup_sublist X.basics)
  refine ⟨?_, ?_⟩
  · show ((X.basics.dedup).map (Basic.deg (k := k) (r := X.r))).sum ≤
      (X.basics.map (Basic.deg (k := k) (r := X.r))).sum
    exact hsub
  · show (X.basics.dedup).length ≤ 1 + (X.basics.map (Basic.deg (k := k) (r := X.r))).sum
    have hlen := tidy_nodup_length_le_sum (k := k) (r := X.r) X.basics.dedup
      (List.nodup_dedup X.basics)
    omega

end Work.WilE7.PadAux
