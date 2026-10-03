import Mathlib
import Submission.Work.OROneRel.mrslDefs
import Submission.Work.OROneRel.substDefs
import Submission.Work.OROneRel.FreiheitssatzDefs

/-!
# The Magnus rewriting of a substituted reduced word is reduced

For the localisation of the Magnus substitution (`magRew_subst_localisation`) one needs that the
decorated word `rewrite t (substList t x p q L)` associated with a reduced word `L` is again
reduced.  In `mrslDefs` the blocks of the substitution `t ↦ t^p`, `x ↦ x * t^(-q)` are analysed,
and `rewriteAux_blkLetter_of_eq` / `rewriteAux_blkLetter_of_ne` show that the Magnus rewriting of a
block word is computed one block at a time: the block of a `t`-letter contributes nothing (but
shifts the running exponent sum by `± p`), and the block of a letter `c` with `c.1 ≠ t` contributes
the single decorated letter `((c.1, acc + blkPre c), c.2)`, the accumulator being shifted by
`blkSigma c = blkPre c + blkPost c`.

Two consecutive output letters therefore cancel only if they come from two consecutive non-`t`
letters of `L` (a nonempty `t`-run between them has a nonzero exponent sum: it is a single-signed
reduced run, so its `blkSigma`-sum is `± p · (length) ≠ 0`), and in the remaining case the two
non-`t` letters are adjacent in the reduced word `L`, so they cannot cancel either.

The main result is `mrsl_rewrite_substList_isReduced`; the two ingredients of the argument are
`mrslRed_blkSigma_sum_run_ne_zero` (the nonzero exponent sum of a reduced run of `t`-letters) and
`mrslRed_output_pair_nocancel` (two consecutive output letters never cancel).
-/

namespace Work.OROneRel

universe u

variable {β : Type u}

/-! ### Splitting off the initial run of `t`-letters -/

/-- A word is either made of `t`-letters only, or it starts with a (possibly empty) run of
`t`-letters followed by a letter different from `t`. -/
private lemma mrslRed_exists_decomp (t : β) (L : List (β × Bool)) :
    (∀ c ∈ L, c.1 = t) ∨
      (∃ (Mid : List (β × Bool)) (v : β × Bool) (Q : List (β × Bool)),
        L = Mid ++ v :: Q ∧ (∀ c ∈ Mid, c.1 = t) ∧ v.1 ≠ t) := by
  classical
  induction L with
  | nil => exact Or.inl (by simp)
  | cons c L ih =>
      rcases ih with hall | ⟨Mid, v, Q, heq, hMid, hv⟩
      · by_cases hc : c.1 = t
        · refine Or.inl ?_
          rintro d hd
          rcases List.mem_cons.mp hd with hdc | hdL
          · rw [hdc]; exact hc
          · exact hall d hdL
        · exact Or.inr ⟨[], c, L, rfl, by simp, hc⟩
      · by_cases hc : c.1 = t
        · refine Or.inr ⟨c :: Mid, v, Q, ?_, ?_, hv⟩
          · rw [heq, List.cons_append]
          · rintro d hd
            rcases List.mem_cons.mp hd with hdc | hdM
            · rw [hdc]; exact hc
            · exact hMid d hdM
        · exact Or.inr ⟨[], c, L, rfl, by simp, hc⟩

/-! ### A reduced run of `t`-letters has nonzero exponent sum -/

/-- In a reduced word all of whose letters are `t`, the sign of the letters is constant. -/
lemma mrslRed_mono_const (t : β) :
    ∀ (R : List (β × Bool)), FreeGroup.IsReduced R → (∀ c ∈ R, c.1 = t) →
      ∀ (hne : R ≠ []), ∀ c ∈ R, c.2 = (R.head hne).2 := by
  intro R
  induction R with
  | nil => intro _ _ hne; exact absurd rfl hne
  | cons r R ih =>
      intro hR hall hne c hc
      rcases List.mem_cons.mp hc with hc | hc
      · rw [hc, List.head_cons]
      · have hneR : R ≠ [] := by rintro h; rw [h] at hc; simp at hc
        have hR' : FreeGroup.IsReduced R := List.IsChain.of_cons hR
        have hhead : R.head hneR ∈ R := List.head_mem hneR
        have hy : R.head hneR ∈ R.head? := by
          rw [List.head?_eq_some_head hneR]; exact Option.mem_some.mpr rfl
        have hrel : r.1 = (R.head hneR).1 → r.2 = (R.head hneR).2 := hR.rel_head? hy
        have hrt : r.2 = (R.head hneR).2 :=
          hrel (by rw [hall r (by simp), hall (R.head hneR) (List.mem_cons_of_mem r hhead)])
        have hcd : c.2 = (R.head hneR).2 := ih hR' (fun c hc => hall c (by simp [hc])) hneR c hc
        rw [List.head_cons, hrt, hcd]

/-- The exponent sum of a monochromatic run of `t`-letters. -/
lemma mrslRed_sum_map_blkSigma (t x : β) (p q : ℤ) : ∀ (R : List (β × Bool)) (b : Bool),
    (∀ c ∈ R, c.1 = t) → (∀ c ∈ R, c.2 = b) →
    (R.map (blkSigma t x p q)).sum = (R.length : ℤ) * (if b then p else -p) := by
  intro R
  induction R with
  | nil => intro b _ _; simp
  | cons r R ih =>
      intro b hall hb
      rw [List.map_cons, List.sum_cons, List.length_cons,
        ih b (fun c hc => hall c (by simp [hc])) (fun c hc => hb c (by simp [hc]))]
      rw [blkSigma_of_eq (hall r (by simp)), hb r (by simp)]
      push_cast
      ring

/-- A nonempty reduced word all of whose letters are `t` has nonzero exponent sum (with respect to
the substitution exponents `p`, `q`). -/
theorem mrslRed_blkSigma_sum_run_ne_zero (t x : β) (p q : ℤ) (hp : p ≠ 0)
    {R : List (β × Bool)} (hR : FreeGroup.IsReduced R) (hne : R ≠ [])
    (hall : ∀ c ∈ R, c.1 = t) :
    (R.map (blkSigma t x p q)).sum ≠ 0 := by
  have hb : ∀ c ∈ R, c.2 = (R.head hne).2 := mrslRed_mono_const t R hR hall hne
  rw [mrslRed_sum_map_blkSigma t x p q R _ hall hb]
  apply mul_ne_zero
  · exact_mod_cast (fun h => hne (List.length_eq_zero_iff.mp h))
  · cases (R.head hne).2 <;> simp [hp]

/-! ### Consecutive output letters never cancel -/

/-- Two consecutive decorated output letters, coming from two non-`t` letters `c`, `v` of `L` with
an intervening `t`-run `Mid`, never cancel. -/
theorem mrslRed_output_pair_nocancel (t x : β) (p q : ℤ) {c v : β × Bool} {Mid Q : List (β × Bool)}
    (acc : ℤ) (hc : c.1 ≠ t) (hv : v.1 ≠ t)
    (hR : FreeGroup.IsReduced (c :: (Mid ++ v :: Q)))
    (hS : Mid ≠ [] → (Mid.map (blkSigma t x p q)).sum ≠ 0)
    (hgen : c.1 = v.1)
    (hdec : acc + blkPre t x p q c =
      (acc + blkSigma t x p q c + (Mid.map (blkSigma t x p q)).sum) + blkPre t x p q v) :
    c.2 = v.2 := by
  by_contra hne
  -- from `hgen` and `hne`, the two letter contributions `blkPost c` and `blkPre v` cancel
  have hpostpre : blkPost t x p q c + blkPre t x p q v = 0 := by
    rw [blkPost, blkPre, ← hgen, if_neg hc, if_neg hc]
    by_cases hx : c.1 = x
    · rw [if_pos hx, if_pos hx]
      cases h1 : c.2 <;> cases h2 : v.2 <;> simp_all
    · rw [if_neg hx, if_neg hx]
      ring
  -- hence the intervening run has vanishing exponent sum
  have hSzero : (Mid.map (blkSigma t x p q)).sum = 0 := by
    have h := hdec
    rw [blkSigma_eq_pre_add_post hc] at h
    linarith
  by_cases hMid : Mid = []
  · -- the two letters are adjacent in the reduced word `L`
    rw [hMid, List.nil_append] at hR
    exact hne (((FreeGroup.isReduced_cons_cons (L := Q)).1 hR).1 hgen)
  · exact hS hMid hSzero

/-! ### The rewriting of a substituted reduced word -/

/-- The Magnus rewriting of the substituted word `substList t x p q L` of a reduced word `L` is
reduced, for any starting value of the exponent sum. -/
theorem mrslRed_rewriteAux_substList_isReduced_aux (t x : β) (p q : ℤ) (hp : p ≠ 0) :
    ∀ (L : List (β × Bool)) (acc : ℤ), FreeGroup.IsReduced L →
      FreeGroup.IsReduced (rewriteAux t acc (substList t x p q L)) := by
  intro L
  induction L with
  | nil => intro acc _; rw [substList_nil, rewriteAux.eq_1]; exact FreeGroup.IsReduced.nil
  | cons c L ih =>
      intro acc hL
      have hL' : FreeGroup.IsReduced L := List.IsChain.of_cons hL
      by_cases hc : c.1 = t
      · -- the block of a `t`-letter disappears from the rewriting
        rw [rewriteAux_substList_cons, rewriteAux_blkLetter_of_eq hc, List.nil_append]
        exact ih (acc + blkSigma t x p q c) hL'
      · -- the block of `c` contributes exactly one decorated letter
        rw [rewriteAux_substList_cons, rewriteAux_blkLetter_of_ne hc, List.singleton_append]
        have htail : FreeGroup.IsReduced
            (rewriteAux t (acc + blkSigma t x p q c) (substList t x p q L)) :=
          ih (acc + blkSigma t x p q c) hL'
        rcases mrslRed_exists_decomp t L with hall | ⟨Mid, v, Q, heq, hMid, hv⟩
        · rw [rewriteAux_substList_of_all_t (L := L) hall]
          exact FreeGroup.IsReduced.singleton
        · rw [heq] at hL htail ⊢
          rw [head_rewriteAux_substList (Mid := Mid) (v := v) hMid hv (acc + blkSigma t x p q c) Q]
            at htail ⊢
          rw [FreeGroup.isReduced_cons_cons]
          refine ⟨?_, htail⟩
          intro hhead
          have hgen : c.1 = v.1 := by
            have h := congrArg (fun z : ({a : β // a ≠ t} × ℤ) => (z.1 : β)) hhead
            simpa using h
          have hdec : acc + blkPre t x p q c =
              (acc + blkSigma t x p q c + (Mid.map (blkSigma t x p q)).sum) +
                blkPre t x p q v := by
            have h := congrArg (fun z : ({a : β // a ≠ t} × ℤ) => z.2) hhead
            rw [accSum_eq] at h
            simpa using h
          refine mrslRed_output_pair_nocancel t x p q (c := c) (v := v) (Mid := Mid) (Q := Q)
            acc hc hv hL ?_ hgen hdec
          intro hneMid
          have h1 : FreeGroup.IsReduced (Mid ++ v :: Q) := List.IsChain.of_cons hL
          have h2 : FreeGroup.IsReduced Mid := List.IsChain.left_of_append h1
          exact mrslRed_blkSigma_sum_run_ne_zero t x p q hp h2 hneMid hMid

theorem mrsl_rewrite_substList_isReduced {β : Type u} (t x : β) (p q : ℤ) (hp : p ≠ 0) (hq : q ≠ 0)
    {L : List (β × Bool)} (hL : FreeGroup.IsReduced L) :
    FreeGroup.IsReduced (Work.OROneRel.rewrite t (Work.OROneRel.substList t x p q L)) := by
  show FreeGroup.IsReduced (Work.OROneRel.rewriteAux t 0 (Work.OROneRel.substList t x p q L))
  exact mrslRed_rewriteAux_substList_isReduced_aux t x p q hp L 0 hL

end Work.OROneRel
