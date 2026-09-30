import Mathlib
import Submission.Work.ConvexCells.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ConvexCells

/-- If every face can be enlarged by an extra constraint (`addF f i` is a face containing the
constraints of `f` and also `i`, and the constraints of `addF f i` are all tight on the region where
`f` is tight and `i` is tight), then every point of the polytope has its tight set among the listed
faces. The hypothesis `himp` is discharged in practice by a Farkas certificate for `addF f i`.

Suggested proof: for `x ∈ P.Pset`, start from `f := P.top` (its tight set is empty by `h.1`) and
iterate: if `tight f ⊊ tightAt x`, pick `i ∈ tightAt x \ tight f` and replace `f` by `addF f i`,
which (by `hsub`, `hmem` and `himp` at `y = x`) satisfies `tight f ⊊ tight (addF f i) ⊆ tightAt x`;
the cardinality of `tight f` increases strictly, so the iteration terminates with
`tight f = tightAt x`. -/
theorem Carriers_of_addF {d : ℕ} (P : PolytopeData d) (h : P.Ok)
    (addF : Fin P.K → Fin P.m → Fin P.K)
    (hsub : ∀ f i, P.tight f ⊆ P.tight (addF f i))
    (hmem : ∀ f i, i ∈ P.tight (addF f i))
    (himp : ∀ f i (y : E d), y ∈ P.Pset → (∀ k ∈ P.tight f, inner ℝ (P.nR k) y = P.bR k) →
      inner ℝ (P.nR i) y = P.bR i →
      ∀ j ∈ P.tight (addF f i), inner ℝ (P.nR j) y = P.bR j) :
    P.Carriers := by
  classical
  intro x hx
  -- Membership in `tightAt` is exactly being an equality at the point, for points of `Pset`.
  have hTAt : ∀ (y : E d), y ∈ P.Pset → ∀ k : Fin P.m,
      (k ∈ P.tightAt y ↔ inner ℝ (P.nR k) y = P.bR k) := by
    intro y hy k
    unfold PolytopeData.tightAt
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    exact ⟨fun hlk => le_antisymm (hy k) hlk, fun heq => by rw [heq]⟩
  -- `step f` enlarges the tight set of `f` by one constraint of `tightAt x` not yet in it,
  -- or is the identity if there is nothing to enlarge by.
  let step : Fin P.K → Fin P.K := fun f =>
    if hh : ∃ i : Fin P.m, i ∈ P.tightAt x ∧ i ∉ P.tight f
    then addF f (Classical.choose hh) else f
  have hstep_pos : ∀ f (hh : ∃ i : Fin P.m, i ∈ P.tightAt x ∧ i ∉ P.tight f),
      step f = addF f (Classical.choose hh) := fun f hh => dite_eq_left hh
  have hstep_neg : ∀ f, ¬ (∃ i : Fin P.m, i ∈ P.tightAt x ∧ i ∉ P.tight f) → step f = f :=
    fun f hh => dite_eq_right hh
  -- The invariant `tight f ⊆ tightAt x` is preserved.
  have hstep_sub2 : ∀ f, P.tight f ⊆ P.tightAt x → P.tight (step f) ⊆ P.tightAt x := by
    intro f hf j hj
    by_cases hh : ∃ i : Fin P.m, i ∈ P.tightAt x ∧ i ∉ P.tight f
    · rw [hstep_pos f hh] at hj
      have hchoose := Classical.choose_spec hh
      exact (hTAt x hx j).mpr
        (himp f (Classical.choose hh) x hx
          (fun k hk => (hTAt x hx k).mp (hf hk))
          ((hTAt x hx (Classical.choose hh)).mp hchoose.1) j hj)
    · rw [hstep_neg f hh] at hj
      exact hf hj
  -- If `f` does not already have the full tight set of `x`, one step strictly enlarges it.
  have hstep_strict : ∀ f, P.tight f ⊆ P.tightAt x → P.tight f ≠ P.tightAt x →
      P.tight f ⊂ P.tight (step f) := by
    intro f hf hne
    have hss : P.tight f ⊂ P.tightAt x := Finset.ssubset_iff_subset_ne.mpr ⟨hf, hne⟩
    obtain ⟨i, hi_mem, hi_not⟩ := Finset.exists_of_ssubset hss
    have hh : ∃ k : Fin P.m, k ∈ P.tightAt x ∧ k ∉ P.tight f := ⟨i, hi_mem, hi_not⟩
    rw [hstep_pos f hh]
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub f _, ?_⟩
    intro hcontra
    have hmem_i : Classical.choose hh ∈ P.tight (addF f (Classical.choose hh)) := hmem f _
    rw [← hcontra] at hmem_i
    exact (Classical.choose_spec hh).2 hmem_i
  -- The iteration starting from the top face.
  let g : ℕ → Fin P.K := fun n => step^[n] P.top
  have hg0 : g 0 = P.top := by simp [g]
  have hgsucc : ∀ n, g (n + 1) = step (g n) := fun n => by
    simp [g, Function.iterate_succ_apply']
  have hinv : ∀ n, P.tight (g n) ⊆ P.tightAt x := by
    intro n
    induction n with
    | zero => rw [hg0, h.tight_top]; exact Finset.empty_subset _
    | succ n ih => rw [hgsucc n]; exact hstep_sub2 (g n) ih
  have hgrow : ∀ n, P.tight (g n) ≠ P.tightAt x →
      (P.tight (g n)).card < (P.tight (g (n + 1))).card := by
    intro n hne
    rw [hgsucc n]
    exact Finset.card_lt_card (hstep_strict (g n) (hinv n) hne)
  -- The cardinality grows by at least one per step, but is bounded by `P.m`.
  have hcard_ge : ∀ n, (∀ k ≤ n, P.tight (g k) ≠ P.tightAt x) →
      n ≤ (P.tight (g n)).card := by
    intro n
    induction n with
    | zero => intro _; exact Nat.zero_le _
    | succ n ih =>
        intro hk
        have h1 := ih (fun k hk' => hk k (le_trans hk' (Nat.le_succ n)))
        have h2 := hgrow n (hk n (Nat.le_succ n))
        omega
  have hcard_le : ∀ n, (P.tight (g n)).card ≤ P.m := by
    intro n
    have h1 : (P.tight (g n)).card ≤ (P.tightAt x).card := Finset.card_le_card (hinv n)
    have h2 : (P.tightAt x).card ≤ P.m := by
      unfold PolytopeData.tightAt
      calc (Finset.univ.filter (fun i : Fin P.m => P.bR i ≤ inner ℝ (P.nR i) x)).card
          ≤ (Finset.univ : Finset (Fin P.m)).card := Finset.card_filter_le _ _
        _ = P.m := by simp
    omega
  by_contra hno
  push Not at hno
  have h1 := hcard_ge (P.m + 1) (fun k _ => hno (g k))
  have h2 := hcard_le (P.m + 1)
  omega

end Work.ConvexCells
