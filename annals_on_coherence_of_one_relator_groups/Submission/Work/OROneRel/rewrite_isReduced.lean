/-
Copyright: subproject `OROneRel` -- one-relator combinatorics.

The Magnus rewriting `rewrite t` of a *reduced* word is again reduced.

The rewriting drops the `t`-letters and records every other letter together with the running
exponent sum in `t` before it.  Two adjacent letters of the output can only cancel if they
come from two consecutive non-`t` letters of the input carrying the *same* running exponent;
reducedness of the input forces the block of `t`-letters between them to be of constant sign,
hence to have nonzero exponent sum unless it is empty, and this leaves the two non-`t`
letters adjacent, where the input's reducedness forbids the cancellation.
-/
import Mathlib
import Submission.Work.OROneRel.FreiheitssatzDefs

namespace Work.OROneRel

universe u

/-- Sum of the signs of the maximal initial block of letters equal to `t`.  Equivalently, the
exponent sum in `t` accumulated by the input word before the first letter different from `t`. -/
noncomputable def leadSum {α : Type u} (t : α) (L : List (α × Bool)) : ℤ := by
  classical
  exact match L with
    | [] => 0
    | p :: L => if p.1 = t then letterSign t p + leadSum t L else 0

lemma letterSign_eq_of_eq_head {α : Type u} {t : α} {p : α × Bool} (hp : p.1 = t) :
    letterSign t p = (if p.2 then (1 : ℤ) else -1) := by
  rw [letterSign]; simp [hp]

lemma letterSign_ne_zero {α : Type u} {t : α} {p : α × Bool} (hp : p.1 = t) :
    letterSign t p ≠ 0 := by
  rw [letterSign_eq_of_eq_head hp]; cases p.2 <;> simp

lemma leadSum_cons_of_ne {α : Type u} (t : α) {p : α × Bool} (L : List (α × Bool))
    (hp : p.1 ≠ t) : leadSum t (p :: L) = 0 := by
  rw [leadSum]; simp [hp]

lemma leadSum_cons_of_eq {α : Type u} (t : α) {p : α × Bool} (L : List (α × Bool))
    (hp : p.1 = t) : leadSum t (p :: L) = letterSign t p + leadSum t L := by
  rw [leadSum]; simp [hp]

/-- In a reduced word whose first letter is `t`, the exponent sum of the initial `t`-block is a
nonzero multiple of the sign of the first letter. -/
lemma leadSum_cons_eq_mul {α : Type u} (t : α) (L : List (α × Bool)) (p : α × Bool)
    (hL : FreeGroup.IsReduced (p :: L)) (hp : p.1 = t) :
    ∃ m : ℕ, leadSum t (p :: L) = ((m + 1 : ℕ) : ℤ) * letterSign t p := by
  induction L generalizing p with
  | nil =>
    refine ⟨0, ?_⟩
    rw [leadSum_cons_of_eq t [] hp]
    simp [leadSum]
  | cons p2 L2 ih =>
    rw [leadSum_cons_of_eq t (p2 :: L2) hp]
    have hcons := (FreeGroup.isReduced_cons_cons (L := L2)).1 hL
    by_cases h2 : p2.1 = t
    · have hp22 : p.2 = p2.2 := hcons.1 (by rw [hp, h2])
      have hs : letterSign t p2 = letterSign t p := by
        rw [letterSign_eq_of_eq_head h2, letterSign_eq_of_eq_head hp, hp22]
      obtain ⟨m, hm⟩ := ih p2 hcons.2 h2
      refine ⟨m + 1, ?_⟩
      rw [hm, hs]
      push_cast
      ring
    · rw [leadSum_cons_of_ne t L2 h2]
      refine ⟨0, ?_⟩
      push_cast
      ring

/-- In a reduced word starting with `t`, the initial `t`-block has nonzero exponent sum. -/
lemma leadSum_cons_ne_zero {α : Type u} (t : α) (L : List (α × Bool)) (p : α × Bool)
    (hL : FreeGroup.IsReduced (p :: L)) (hp : p.1 = t) : leadSum t (p :: L) ≠ 0 := by
  obtain ⟨m, hm⟩ := leadSum_cons_eq_mul t L p hL hp
  rw [hm]
  exact mul_ne_zero (by exact_mod_cast Nat.succ_ne_zero m) (letterSign_ne_zero hp)

lemma rewriteAux_nil {α : Type u} (t : α) (i : ℤ) :
    rewriteAux t i ([] : List (α × Bool)) = [] := by
  simp [rewriteAux]

lemma rewriteAux_cons_of_ne {α : Type u} (t : α) (i : ℤ) {p : α × Bool} (L : List (α × Bool))
    (hp : p.1 ≠ t) :
    rewriteAux t i (p :: L) = ((⟨p.1, hp⟩, i), p.2) :: rewriteAux t i L := by
  simp [rewriteAux, hp]

lemma rewriteAux_cons_of_eq {α : Type u} (t : α) (i : ℤ) {p : α × Bool} (L : List (α × Bool))
    (hp : p.1 = t) :
    rewriteAux t i (p :: L) = rewriteAux t (i + (if p.2 then 1 else -1)) L := by
  simp [rewriteAux, hp]

/-- The first letter of the rewriting carries the exponent sum accumulated by the whole initial
`t`-block of the input. -/
lemma rewriteAux_head_fst {α : Type u} (t : α) (i : ℤ) (L : List (α × Bool))
    (e : ({a : α // a ≠ t} × ℤ) × Bool) (rest : List (({a : α // a ≠ t} × ℤ) × Bool))
    (h : rewriteAux t i L = e :: rest) : e.1.2 = i + leadSum t L := by
  induction L generalizing i e rest with
  | nil => simp [rewriteAux] at h
  | cons p L' ih =>
    by_cases hp : p.1 = t
    · rw [rewriteAux_cons_of_eq t i L' hp] at h
      have hh := ih (i + (if p.2 then 1 else -1)) e rest h
      rw [hh, leadSum_cons_of_eq t L' hp, letterSign_eq_of_eq_head hp]
      ring
    · rw [rewriteAux_cons_of_ne t i L' hp] at h
      injection h with h1 _
      rw [← h1, leadSum_cons_of_ne t L' hp]
      simp

/-- If a reduced, nonempty word starts with a `t`-free letter or a non-`t` letter, it has
`leadSum 0`. -/
lemma exists_cons_of_leadSum_eq_zero {α : Type u} (t : α) {L : List (α × Bool)}
    (hL : FreeGroup.IsReduced L) (h : leadSum t L = 0) (hne : L ≠ []) :
    ∃ (p : α × Bool) (L' : List (α × Bool)), L = p :: L' ∧ p.1 ≠ t := by
  match L, hne with
  | [], hne => exact absurd rfl hne
  | p :: L', _ =>
    refine ⟨p, L', rfl, ?_⟩
    by_cases hp : p.1 = t
    · exact absurd h (leadSum_cons_ne_zero t L' p hL hp)
    · exact hp

/-- The Magnus rewriting of a reduced word is reduced, for any starting exponent sum. -/
theorem rewriteAux_isReduced {α : Type u} (t : α) (L : List (α × Bool))
    (hL : FreeGroup.IsReduced L) : ∀ i : ℤ, FreeGroup.IsReduced (rewriteAux t i L) := by
  induction L with
  | nil => intro i; rw [rewriteAux_nil]; exact FreeGroup.IsReduced.nil
  | cons p L' ih =>
    intro i
    have hL' : FreeGroup.IsReduced L' := List.IsChain.of_cons hL
    by_cases hp : p.1 = t
    · rw [rewriteAux_cons_of_eq t i L' hp]
      exact ih hL' (i + (if p.2 then 1 else -1))
    · rw [rewriteAux_cons_of_ne t i L' hp]
      have htail : FreeGroup.IsReduced (rewriteAux t i L') := ih hL' i
      by_cases hnil : rewriteAux t i L' = []
      · rw [hnil]; exact FreeGroup.IsReduced.singleton
      · obtain ⟨e2, rest, heq⟩ := List.exists_cons_of_ne_nil hnil
        have htail' : FreeGroup.IsReduced (e2 :: rest) := heq ▸ htail
        rw [heq, FreeGroup.isReduced_cons_cons]
        refine ⟨?_, htail'⟩
        · intro h1
          have hhead := rewriteAux_head_fst t i L' e2 rest heq
          have hL'ne : L' ≠ [] := by
            intro h0; rw [h0, rewriteAux_nil] at hnil; exact hnil rfl
          have hzero : leadSum t L' = 0 := by
            have h12 : i = e2.1.2 := by
              have := congrArg Prod.snd h1
              simpa using this
            rw [hhead] at h12
            linarith
          obtain ⟨p2, L2, rfl, h2⟩ := exists_cons_of_leadSum_eq_zero t hL' hzero hL'ne
          rw [rewriteAux_cons_of_ne t i L2 h2] at heq
          injection heq with heq1 _
          rw [← heq1] at h1 ⊢
          have hp2 : p.1 = p2.1 := by
            have hsub : (⟨p.1, hp⟩ : {a : α // a ≠ t}) = ⟨p2.1, h2⟩ := by
              have := congrArg (fun x : ({a : α // a ≠ t} × ℤ) => x.1) h1
              simpa using this
            simpa using congrArg Subtype.val hsub
          have hchain : p.2 = p2.2 := ((FreeGroup.isReduced_cons_cons (L := L2)).1 hL).1 hp2
          simpa using hchain

theorem rewrite_isReduced {α : Type u} (t : α) {L : List (α × Bool)}
    (hL : FreeGroup.IsReduced L) : FreeGroup.IsReduced (Work.OROneRel.rewrite t L) := by
  show FreeGroup.IsReduced (rewriteAux t 0 L)
  exact rewriteAux_isReduced t L hL 0

end Work.OROneRel
