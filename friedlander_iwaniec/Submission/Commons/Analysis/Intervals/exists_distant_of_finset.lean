import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Finset.Sort

namespace Commons.Analysis.Intervals

/-!
# A point at distance `≥ t` from a finite set of reals

If `S` is a finite set of reals, `t > 0`, and the interval `[a,b]` is long enough
(`2 * t * #S ≤ b - a`), then `[a,b]` contains a point whose distance to every element
of `S` is at least `t`.

The proof is a greedy sweep from the left: starting at `a`, walk right, and whenever
the current point `acc` falls strictly inside a forbidden interval `(s - t, s + t)`,
jump to its right endpoint `s + t`.  Processing the points of `S` in increasing order
guarantees that no earlier constraint is ever violated again, and each jump advances
`acc` by less than `2*t`, so after processing all of `S` the point has moved by less
than `2 * t * #S ≤ b - a`.
-/

/-- One greedy step: if `acc` lies strictly inside the forbidden open interval
`(s - t, s + t)`, move it to the right endpoint `s + t`; otherwise keep it. -/
private noncomputable def step (t acc s : ℝ) : ℝ :=
  if s - t < acc ∧ acc < s + t then s + t else acc

private lemma le_step (t : ℝ) (acc s : ℝ) : acc ≤ step t acc s := by
  unfold step
  split <;> rename_i h
  · linarith [h.2]
  · exact le_refl acc

private lemma step_le (t : ℝ) (ht : 0 < t) (acc s : ℝ) : step t acc s ≤ acc + 2 * t := by
  unfold step
  split <;> rename_i h
  · linarith [h.1]
  · linarith

/-- If `acc` is at most `m - t` for every `m` in a list `M`, then the greedy fold leaves
`acc` unchanged. -/
private lemma foldl_step_of_le (t : ℝ) (M : List ℝ) (acc : ℝ)
    (h : ∀ m ∈ M, acc ≤ m - t) : M.foldl (step t) acc = acc := by
  induction M generalizing acc with
  | nil => rfl
  | cons m rest ih =>
      rw [List.foldl_cons]
      have hm : acc ≤ m - t := h m (by simp)
      have hstep : step t acc m = acc := by
        unfold step
        rw [if_neg]
        intro hc
        exact absurd hm (not_le.mpr hc.1)
      rw [hstep]
      exact ih acc (fun x hx => h x (by simp [hx]))

/-- Specification of the greedy sweep.  For any list `L` and starting point `acc0`,
the result `acc` of folding `step` over `L` satisfies

* `acc0 ≤ acc`;
* `acc ≤ acc0 + 2 * t * L.length`;
* if `L` is sorted increasingly, then every `s ∈ L` satisfies `acc ≤ s - t` or
  `s + t ≤ acc`. -/
private lemma foldl_step_spec (t : ℝ) (ht : 0 < t) (L : List ℝ) (acc0 : ℝ) :
    acc0 ≤ L.foldl (step t) acc0 ∧
      L.foldl (step t) acc0 ≤ acc0 + 2 * t * (L.length : ℝ) ∧
      (L.Pairwise (· ≤ ·) → ∀ s ∈ L,
        s + t ≤ L.foldl (step t) acc0 ∨ L.foldl (step t) acc0 ≤ s - t) := by
  induction L generalizing acc0 with
  | nil =>
      refine ⟨le_refl _, by simp, ?_⟩
      intro _ s hs
      simp at hs
  | cons s0 rest ih =>
      rw [List.foldl_cons]
      set acc1 : ℝ := step t acc0 s0 with hacc1
      have hih := ih acc1
      refine ⟨?_, ?_, ?_⟩
      · have h1 : acc0 ≤ acc1 := by rw [hacc1]; exact le_step t acc0 s0
        exact le_trans h1 hih.1
      · have h1 : acc1 ≤ acc0 + 2 * t := by rw [hacc1]; exact step_le t ht acc0 s0
        have hlen1 : (((s0 :: rest).length : ℕ) : ℝ) = (rest.length : ℝ) + 1 := by
          simp [List.length_cons]
        calc rest.foldl (step t) acc1
            ≤ acc1 + 2 * t * (rest.length : ℝ) := hih.2.1
          _ ≤ (acc0 + 2 * t) + 2 * t * (rest.length : ℝ) := by linarith
          _ = acc0 + 2 * t * (((s0 :: rest).length : ℕ) : ℝ) := by
              rw [hlen1]; ring
      · intro hpair
        have hp := List.pairwise_cons.1 hpair
        have hs0_goal :
            s0 + t ≤ rest.foldl (step t) acc1 ∨ rest.foldl (step t) acc1 ≤ s0 - t := by
          by_cases hcase : s0 - t < acc0 ∧ acc0 < s0 + t
          · left
            have ha1 : acc1 = s0 + t := by
              rw [hacc1]; unfold step; rw [if_pos hcase]
            linarith [hih.1, ha1]
          · have ha1 : acc1 = acc0 := by
              rw [hacc1]; unfold step; rw [if_neg hcase]
            have hle_or : acc0 ≤ s0 - t ∨ s0 + t ≤ acc0 := by
              rcases not_and_or.mp hcase with h | h
              · exact Or.inl (not_lt.mp h)
              · exact Or.inr (not_lt.mp h)
            rcases hle_or with hle | hge
            · right
              have hmem : ∀ m ∈ rest, acc1 ≤ m - t := by
                intro m hm
                have hs0m : s0 ≤ m := hp.1 m hm
                rw [ha1]; linarith
              rw [foldl_step_of_le t rest acc1 hmem, ha1]
              exact hle
            · left
              linarith [hih.1, ha1, hge]
        intro s hs
        rcases List.mem_cons.mp hs with heq | hs'
        · rw [heq]
          exact hs0_goal
        · exact hih.2.2 hp.2 s hs'

theorem exists_distant_of_finset {S : Finset ℝ} {t a b : ℝ} (ht : 0 < t)
    (hcard : 2 * t * (S.card : ℝ) ≤ b - a) :
    ∃ v : ℝ, a ≤ v ∧ v ≤ b ∧ ∀ s ∈ S, t ≤ |v - s| := by
  set L : List ℝ := S.sort (· ≤ ·) with hL
  have hpair : L.Pairwise (· ≤ ·) := by
    rw [hL]; exact Finset.pairwise_sort S (· ≤ ·)
  have hlen : (L.length : ℝ) = (S.card : ℝ) := by
    rw [hL, Finset.length_sort]
  have hmem : ∀ s : ℝ, s ∈ L ↔ s ∈ S := by
    intro s; rw [hL, Finset.mem_sort (r := (· ≤ ·))]
  have hspec := foldl_step_spec t ht L a
  refine ⟨L.foldl (step t) a, hspec.1, ?_, ?_⟩
  · have := hspec.2.1
    rw [hlen] at this
    linarith
  · intro s hs
    have hsL : s ∈ L := (hmem s).mpr hs
    have h3 := hspec.2.2 hpair s hsL
    rcases h3 with h3 | h3
    · rw [abs_of_nonneg (by linarith)]
      linarith
    · rw [abs_of_nonpos (by linarith), neg_sub]
      linarith

end Commons.Analysis.Intervals