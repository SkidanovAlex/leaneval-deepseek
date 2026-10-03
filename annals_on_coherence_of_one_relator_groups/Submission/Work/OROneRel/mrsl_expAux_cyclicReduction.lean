import Mathlib
import Submission.Work.OROneRel.mrslExp
import Submission.Work.OROneRel.substDefs
import Submission.Work.OROneRel.mrsl_expAux_isReduced
import Submission.Work.OROneRel.mrsl_runLetters_sandwich

/-!
# The cyclic reduction of the expansion of a cyclically reduced decorated word

For a letter `t` of the free group `F β` and a decorated word
`D : List (({x : β // x ≠ t} × ℤ) × Bool)` the expansion `expAux t 0 D`
(`Submission.Work.OROneRel.mrslExp`) writes out `t ^ (i₁) · x₁ ^ (b₁) · t ^ (i₂ - i₁) · …`: the
`t`-letters of the `i`-frame interleaved with the non-`t` letters of `D`.

If `D` is reduced and *cyclically* reduced, then `expAux t 0 D` is a `t^m`-conjugate of a cyclically
reduced word: the leading run `t ^ (i₁)` and the trailing run `t ^ (i_n)` (recall
`expAux_eq_expMid : expAux t a D = expMid t a D ++ runLetters t (-(lastDec t a D))`) can cancel at
the two ends as long as the exposed letters are `t`-letters of opposite sign, and the two ends of the
middle piece `Y = x₁ ^ (b₁) · t ^ (i₂ - i₁) · … · x_n ^ (b_n)` both have generator `≠ t`; the only
case in which *both* ends of the conjugating word (after peeling) are `Y`'s ends is `i₁ = i_n`, and
there the cyclic reducedness of `D` says that `x₁ ^ (b₁)` and `x_n ^ (b_n)` do not cancel.

The sandwiching list lemma is `Work.OROneRel.mrsl_runLetters_sandwich`.
-/

namespace Work.OROneRel

universe u

variable {β : Type u}

/-- The last letter of `a :: l` is the last letter of `l` as soon as `l` is nonempty. -/
private theorem getLast?_cons_of_ne_nil {α : Type*} {a : α} {l : List α} (h : l ≠ []) :
    (a :: l).getLast? = l.getLast? := by
  rcases l with _ | ⟨y, ys⟩
  · exact absurd rfl h
  · rw [List.getLast?_cons_cons]

/-- The middle part `expMid t a D` of the expansion never ends with a `t`-run: its last letter is the
last letter of `D` with the `t`-frame removed. -/
private theorem expMid_getLast? (t : β) (a : ℤ)
    (D : List (({x : β // x ≠ t} × ℤ) × Bool)) :
    (expMid t a D).getLast? = D.getLast?.map (fun p => (p.1.1.1, p.2)) := by
  induction D generalizing a with
  | nil => simp
  | cons p rest ih =>
    obtain ⟨⟨c, i⟩, b⟩ := p
    rw [expMid_cons]
    rcases rest with _ | ⟨h, tl⟩
    · rw [expMid_nil, List.getLast?_append_cons, List.getLast?_singleton,
        List.getLast?_singleton]
      rfl
    · obtain ⟨⟨c', i'⟩, b'⟩ := h
      rw [List.getLast?_append_of_ne_nil _ (by simp),
        getLast?_cons_of_ne_nil (by simp [expMid_cons]), ih i,
        List.getLast?_cons_cons]

/-- The last decoration `lastDec t a D` of `D` is the decoration of the last letter of `D`. -/
private theorem lastDec_eq_of_getLast? (t : β) (a : ℤ)
    {D : List (({x : β // x ≠ t} × ℤ) × Bool)}
    {p : ({x : β // x ≠ t} × ℤ) × Bool} (h : D.getLast? = some p) :
    lastDec t a D = p.1.2 := by
  induction D generalizing a with
  | nil => simp at h
  | cons q rest ih =>
    rcases rest with _ | ⟨r, rs⟩
    · rw [List.getLast?_singleton] at h
      obtain rfl := Option.some.inj h
      rfl
    · rw [List.getLast?_cons_cons] at h
      rw [lastDec_cons]
      exact ih _ h

theorem mrsl_expAux_cyclicReduction {β : Type u} (t : β) {D : List (({x : β // x ≠ t} × ℤ) × Bool)}
    (hred : FreeGroup.IsReduced D) (hcyc : FreeGroup.IsCyclicallyReduced D) :
    ∃ (m : ℤ) (V : List (β × Bool)),
      Work.OROneRel.expAux t 0 D = runLetters t m ++ V ++ runLetters t (-m) ∧
      FreeGroup.IsCyclicallyReduced V := by
  classical
  cases D with
  | nil => exact ⟨0, [], by simp [expAux], FreeGroup.IsCyclicallyReduced.nil⟩
  | cons p rest =>
    obtain ⟨⟨c, i⟩, b⟩ := p
    set Y : List (β × Bool) := (c.1, b) :: expMid t i rest with hYdef
    have hYne : Y ≠ [] := by rw [hYdef]; simp
    -- the expansion splits as `runLetters t i ++ Y ++ runLetters t (-(lastDec t i rest))`
    have hW : expAux t 0 (((c, i), b) :: rest)
        = runLetters t i ++ Y ++ runLetters t (-(lastDec t i rest)) := by
      rw [expAux_eq_expMid, expMid_cons, lastDec_cons, hYdef]
      simp [List.append_assoc]
    -- the head of `Y` is the first letter of `D`
    have hhead : ∀ a ∈ Y.head?, a.1 ≠ t := by
      intro a ha
      rw [hYdef, List.head?_cons] at ha
      simp only [Option.mem_some_iff] at ha
      subst ha
      exact c.2
    -- the last letter of `Y` is the last letter of `D`
    have hlast : ∀ a ∈ Y.getLast?, a.1 ≠ t := by
      intro a ha
      rw [hYdef] at ha
      rcases hZ : expMid t i rest with _ | ⟨z, Z⟩
      · rw [hZ, List.getLast?_singleton] at ha
        simp only [Option.mem_some_iff] at ha
        subst ha
        exact c.2
      · rw [getLast?_cons_of_ne_nil (by rw [hZ]; simp), expMid_getLast?] at ha
        rcases hq : rest.getLast? with _ | ⟨⟨c', i'⟩, b'⟩
        · rw [hq, Option.map_none] at ha
          simp at ha
        · rw [hq, Option.map_some] at ha
          simp only [Option.mem_some_iff] at ha
          subst ha
          exact c'.2
    -- when `i = lastDec t i rest` (i.e. `p = -q`) the two ends of `Y` are the two ends of `D`,
    -- and the cyclic reducedness of `D` applies
    have hcyc' : i = -(-(lastDec t i rest)) →
        ∀ a ∈ Y.getLast?, ∀ b ∈ Y.head?, a.1 = b.1 → a.2 = b.2 := by
      intro hg a ha b hb hab
      rw [hYdef, List.head?_cons] at hb
      simp only [Option.mem_some_iff] at hb
      subst hb
      rw [hYdef] at ha
      rcases hZ : expMid t i rest with _ | ⟨z, Z⟩
      · rw [hZ, List.getLast?_singleton] at ha
        simp only [Option.mem_some_iff] at ha
        subst ha
        rfl
      · rw [getLast?_cons_of_ne_nil (by rw [hZ]; simp), expMid_getLast?] at ha
        have hrest : rest ≠ [] := by rintro rfl; simp at hZ
        rcases hq : rest.getLast? with _ | ⟨⟨c', i'⟩, b'⟩
        · rw [hq, Option.map_none] at ha
          simp at ha
        · rw [hq, Option.map_some] at ha
          simp only [Option.mem_some_iff] at ha
          subst ha
          have hc : c' = c := Subtype.ext hab
          have hi : i' = i := by
            have h1 : lastDec t i rest = i' := lastDec_eq_of_getLast? t i hq
            simp only [neg_neg] at hg
            rw [hg, h1]
          have hmem : ((c', i'), b') ∈ (((c, i), b) :: rest).getLast? := by
            rw [getLast?_cons_of_ne_nil hrest, hq]; simp
          have hmem' : ((c, i), b) ∈ (((c, i), b) :: rest).head? := by simp
          have hD := hcyc.2 _ hmem _ hmem'
          rw [hc, hi] at hD
          exact hD rfl
    obtain ⟨m, V, hV, hcycV⟩ := mrsl_runLetters_sandwich t hW hYne
      (mrsl_expAux_isReduced t 0 hred) hhead hlast hcyc'
    exact ⟨m, V, hV, hcycV⟩

end Work.OROneRel
