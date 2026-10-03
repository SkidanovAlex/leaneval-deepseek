import Mathlib
import Submission.Work.ORLyndon.annAtDefs
import Submission.Work.ORLyndon.annAt_of_epsZero
import Submission.Work.ORLyndon.annAt_of_epsZero_strong
import Submission.Work.ORLyndon.mmTopSym_mem_relatorLetters
import Submission.Work.ORLyndon.isCyclicallyReducedRelator_rootW
import Submission.Work.ORLyndon.lyndonIndependence_conj
import Submission.Work.OROneRel.magnus_step_root

/-!
# The Cohen--Lyndon descent on `relatorNorm`, in the set-indexed `annAt` form

This file assembles the Cohen--Lyndon induction of this area in the formulation of
`Work.ORLyndon.annAt` (see `annAtDefs.lean`): instead of an invariant with an *exempted set* of
letters (`Work.ORLyndon.CLInvariantWith`, `CLStepA.lean`), the induction carries a *nonempty set of
letters* `S` and proves

`Work.ORLyndon.annAt K (u ^ l) u S`  -- "every `b` annihilating `(∂u/∂x)_x` for all `x ∈ S` is `0`",

simultaneously with the Karrass--Magnus--Solitar **order** statement
`orderOf (presentRho (u ^ l) u) = l` (which the endgame needs and which the exponent-sum-zero Magnus
step propagates for free, `Work.ORLyndon.orderOf_of_mmBaseHom`).

Because `annAt` is *monotone* in `S` (`annAt_mono`: a statement about fewer letters implies one about
more), a descent through the Magnus steps may simply **drop** a letter it cannot reach, and the
induction only has to keep the set nonempty; enlarging it is free.  This replaces the exempted-set
bookkeeping of the earlier design.

## The descent

`Work.ORLyndon.Case2Descent` is the **single residual hypothesis** of the whole reduction: the
descent step in the case where *no usable framing letter is available*.  Recall that the
exponent-sum-zero Magnus step at the framing letter `t` (`σ_t u = 0`) transfers the statement for
the set `E` of letters `≠ t`:

`annAt (u ^ l) u E  ⟸  annAt (base) (rootW …) (top '' E)`

(`Work.ORLyndon.annAt_of_epsZero_strong`, with `E = Subtype.val '' Em`), and propagates the order
statement (`orderOf_of_mmBaseHom`).  So the step is available whenever `u` has a letter `t` with
`σ_t u = 0` which is either

* outside `S` (use `E = S`), or
* inside `S` together with a *second* letter of `S` (use `E = S ∖ {t}`; note
  `annAt (…) (S ∖ {t})` implies `annAt (…) S` by monotonicity).

The residual is therefore the case in which **every letter `t ∈ relatorLetters u` with `σ_t u = 0`
is the unique element of `S`** (`S = {t}`): this is node N2's Case 2 (no letter of `u` has vanishing
exponent sum, `S` arbitrary) together with the degenerate case of the framing-letter component for a
single-letter set.  In this case the descent must come from outside this directory (node N2's
magnus/Masters--Linton step, `Submission/Work/OROneRel/`), and it must supply both the shorter root
`v` with the nonempty set `S'`, and the order statement for `u`.

The base root `v = rootW t u l …` is shorter (`relatorNorm_rootW_lt`), not a proper power
(`not_isProperPower_rootW`) and cyclically reduced (`isCyclicallyReducedRelator_rootW`), and the top
decorated symbols of the letters of the set form a nonempty set of letters of `v`
(`Work.ORLyndon.mmTopSym_mem_relatorLetters`), so the strong induction applies to it.

## Main results

* `Work.ORLyndon.Case2Descent` -- the residual hypothesis;
* `Work.ORLyndon.descent_bundle` -- the strong induction on `relatorNorm` (order and `annAt` at once);
* `Work.ORLyndon.annAt_of_descent`, `Work.ORLyndon.annAt_letters_of_descent`,
  `Work.ORLyndon.regular_rootVec_of_descent` -- the `annAt` statements;
* `Work.ORLyndon.lyndon_independence_of_pow_of_case2` -- **the Cohen--Lyndon theorem from the
  descent hypothesis** (no further input).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

universe u v

namespace Work.ORLyndon

open MonoidAlgebra

variable {X : Type u} [DecidableEq X] {K : Type v} [Field K]

/-- The letters of a nontrivial free-group element are nonempty. -/
theorem relatorLetters_nonempty_of_ne_one {α : Type u} {u : FreeGroup α} (hu : u ≠ 1) :
    (Work.OROneRel.relatorLetters u).Nonempty := by
  classical
  rw [Set.nonempty_iff_ne_empty]
  intro h
  have hnil : FreeGroup.toWord u = [] := by
    by_contra hne
    obtain ⟨g, hg⟩ := List.exists_mem_of_ne_nil _ hne
    have h1 : g.1 ∈ (∅ : Set α) := h ▸ ⟨g.2, hg⟩
    exact h1
  exact hu (FreeGroup.toWord_eq_nil_iff.mp hnil)

/-- **The descent data** attached to a root `u`, an exponent `l` and a set `S` of letters of `u`: a
*strictly shorter* one-relator presentation `⟨β | r' = v ^ l⟩` (`v` cyclically reduced and not a
proper power, `relatorNorm v < relatorNorm u`) together with a nonempty set `S'` of letters of `v`
such that `annAt` at `S'` implies `annAt` at `S`. -/
def MagnusDescent (K : Type v) [Field K] {α : Type u} [DecidableEq α] (u : FreeGroup α) (l : ℕ)
    (S : Set α) : Prop :=
  ∃ (β : Type u) (v r' : FreeGroup β) (S' : Set β),
    ¬ Work.OROneRel.IsProperPower v ∧ r' = v ^ l ∧
    Work.OROneRel.IsCyclicallyReducedRelator v ∧
    Work.OROneRel.relatorNorm v < Work.OROneRel.relatorNorm u ∧
    S'.Nonempty ∧ S' ⊆ Work.OROneRel.relatorLetters v ∧
    (@annAt K _ β (Classical.decEq β) r' v S' → annAt K (u ^ l) u S)

/-- **The residual hypothesis, first part: node N2's Case 2.**  The descent data when *no* letter of
`u` has vanishing exponent sum, together with the order statement for `u`.  This is the case in which
the exponent-sum-zero Magnus step does not apply at all, and which node N2 attacks with the
cyclic-cover / Masters--Linton construction (`Submission/Work/OROneRel/`). -/
def EpsNeZeroDescent (K : Type v) [Field K] : Prop :=
  ∀ {α : Type u} [DecidableEq α] (u : FreeGroup α) (l : ℕ) (hl : 1 ≤ l),
    ¬ Work.OROneRel.IsProperPower u → Work.OROneRel.IsCyclicallyReducedRelator u →
    2 ≤ Work.OROneRel.relatorNorm u →
    (∀ x ∈ Work.OROneRel.relatorLetters u, Work.OROneRel.eps x u ≠ 0) →
    ∀ S : Set α, S.Nonempty → S ⊆ Work.OROneRel.relatorLetters u →
    MagnusDescent K u l S ∧ orderOf (presentRho (u ^ l) u) = l

/-- **The residual hypothesis, second part: the framing-letter component.**  The descent data for the
single-letter set `S = {t}` at the *unique* vanishing-exponent-sum letter `t` of `u`.  Here the
exponent-sum-zero Magnus step cannot deliver `annAt` (the set of letters to which its transfer would
apply is empty), so this needs an argument of its own; the transfer provably cannot deliver it
(notes §27).  The *order* statement is **not** demanded here: in this case it follows from the Magnus
step at `t` (`Work.ORLyndon.orderOf_of_mmBaseHom`), see `Work.ORLyndon.descent_bundle`. -/
def SingletonFramingDescent (K : Type v) [Field K] : Prop :=
  ∀ {α : Type u} [DecidableEq α] (u : FreeGroup α) (l : ℕ) (hl : 1 ≤ l),
    ¬ Work.OROneRel.IsProperPower u → Work.OROneRel.IsCyclicallyReducedRelator u →
    2 ≤ Work.OROneRel.relatorNorm u →
    (t : α) → t ∈ Work.OROneRel.relatorLetters u → Work.OROneRel.eps t u = 0 →
    (∀ x ∈ Work.OROneRel.relatorLetters u, Work.OROneRel.eps x u = 0 → x = t) →
    MagnusDescent K u l {t}

/-- **The residual hypothesis of the descent.**  The descent step in the two cases in which no
*usable* framing letter is available: `Work.ORLyndon.EpsNeZeroDescent` (node N2's Case 2, where no
letter of `u` has vanishing exponent sum) and `Work.ORLyndon.SingletonFramingDescent` (the
single-letter framing component `S = {t}` at the unique vanishing-exponent-sum letter `t`).

This is exactly the complement of the exponent-sum-zero Magnus step (`annAt_of_epsZero_strong`,
`orderOf_of_mmBaseHom`).  Note that the *order* statement is demanded only of the first part: in the
framing case it is proved here, from the Magnus step at `t` together with the induction hypothesis at
the base `rootW t u l …` (see `Work.ORLyndon.descent_bundle`). -/
structure Case2Descent (K : Type v) [Field K] : Prop where
  /-- node N2's Case 2: no letter of `u` has vanishing exponent sum -/
  part1 : EpsNeZeroDescent.{u, v} K
  /-- the single-letter framing component -/
  part2 : SingletonFramingDescent.{u, v} K

/-- **The order statement in the base case of the descent**, `relatorNorm u ≤ 1`: `u` is a single
letter up to sign, and the order of its class in `⟨X | u ^ l⟩` is `l`
(`Work.OROneRel.kmsRoot_of_letterPow`, which is `sorry`-free). -/
theorem orderOf_of_relatorNorm_le_one {r u : FreeGroup X} {l : ℕ} (hl : 1 ≤ l)
    (hpow : r = u ^ l) (hpp : ¬ Work.OROneRel.IsProperPower u)
    (hn : Work.OROneRel.relatorNorm u ≤ 1) :
    orderOf (presentRho r u) = l := by
  classical
  rcases Work.OROneRel.eq_one_or_exists_letterPow_of_relatorNorm_le_one hn with h1 | ⟨a, s, hle⟩
  · exact absurd (h1.symm ▸ Work.OROneRel.isProperPower_one) hpp
  · subst hle
    subst hpow
    simpa using (Work.OROneRel.kmsRoot_of_letterPow a s l hl).1

/-- **The base case of the descent**, for an arbitrary nonempty set of letters of a root of relator
norm `≤ 1`. -/
theorem annAt_of_relatorNorm_le_one_set {r u : FreeGroup X} {l : ℕ} (hl : 1 ≤ l)
    (hpow : r = u ^ l) (hpp : ¬ Work.OROneRel.IsProperPower u)
    (hn : Work.OROneRel.relatorNorm u ≤ 1) {S : Set X} (hSne : S.Nonempty)
    (hSsub : S ⊆ Work.OROneRel.relatorLetters u) :
    annAt K r u S := by
  classical
  rcases Work.OROneRel.eq_one_or_exists_letterPow_of_relatorNorm_le_one hn with h1 | ⟨a, s, hle⟩
  · exact absurd (h1.symm ▸ Work.OROneRel.isProperPower_one) hpp
  · subst hle
    subst hpow
    have hL : Work.OROneRel.relatorLetters (Work.OROneRel.letterPow a s) = {a} :=
      Work.OROneRel.relatorLetters_letterPow a s
    have ha : a ∈ S := by
      obtain ⟨x, hx⟩ := hSne
      have hxa : x = a := by simpa [hL] using hSsub hx
      rwa [hxa] at hx
    exact annAt_of_unit ha (isUnit_rootVec_letterPow _ a s)

/-- **The descent: the strong induction on `relatorNorm`.**  Assuming the residual hypothesis, both
the order statement and the `annAt` statement (for *every* nonempty set of letters) hold for every
cyclically reduced root which is not a proper power. -/
theorem descent_bundle (h2 : Case2Descent.{u, v} K) :
    ∀ n {α : Type u} [DecidableEq α] (u : FreeGroup α) (l : ℕ), 1 ≤ l →
      ¬ Work.OROneRel.IsProperPower u → Work.OROneRel.IsCyclicallyReducedRelator u →
      Work.OROneRel.relatorNorm u ≤ n →
      ∀ S : Set α, S.Nonempty → S ⊆ Work.OROneRel.relatorLetters u →
        (orderOf (presentRho (u ^ l) u) = l) ∧ annAt K (u ^ l) u S := by
  intro n
  induction n with
  | zero =>
      intro α _ u l hl hpp hcyc hn S hSne hSsub
      exact ⟨orderOf_of_relatorNorm_le_one hl rfl hpp (by omega),
        annAt_of_relatorNorm_le_one_set hl rfl hpp (by omega) hSne hSsub⟩
  | succ n ih =>
      intro α _ u l hl hpp hcyc hn S hSne hSsub
      classical
      by_cases hsmall : Work.OROneRel.relatorNorm u ≤ 1
      · exact ⟨orderOf_of_relatorNorm_le_one hl rfl hpp hsmall,
          annAt_of_relatorNorm_le_one_set hl rfl hpp hsmall hSne hSsub⟩
      · push_neg at hsmall
        -- the descent step through the Magnus base at the framing letter `t`
        have hstep : ∀ (t : α) (htL : t ∈ Work.OROneRel.relatorLetters u)
            (htσ : Work.OROneRel.eps t u = 0) (Em : Set {y : α // y ≠ t}),
            Em.Nonempty →
            ((fun y : {y : α // y ≠ t} => mmTopSym t u l y.1 y.2) '' Em) ⊆
              Work.OROneRel.relatorLetters (Work.OROneRel.rootW t u l hcyc htσ hl) →
            annAt K (u ^ l) u (Subtype.val '' Em) ∧ orderOf (presentRho (u ^ l) u) = l := by
          intro t htL htσ Em hEmne hsub
          have htop_ne : ((fun y : {y : α // y ≠ t} =>
              mmTopSym t u l y.1 y.2) '' Em).Nonempty := hEmne.image _
          have hIH := ih (Work.OROneRel.rootW t u l hcyc htσ hl) l hl
              (Work.OROneRel.not_isProperPower_rootW t u l hpp hcyc htσ hl)
              (isCyclicallyReducedRelator_rootW t u l hcyc htσ hl)
              (by have := Work.OROneRel.relatorNorm_rootW_lt t u l hcyc htσ hl htL; omega)
              ((fun y : {y : α // y ≠ t} => mmTopSym t u l y.1 y.2) '' Em) htop_ne hsub
          have hannIH : annAt K ((Work.OROneRel.rootW t u l hcyc htσ hl) ^ l)
              (Work.OROneRel.rootW t u l hcyc htσ hl)
              ((fun y : {y : α // y ≠ t} => mmTopSym t u l y.1 y.2) '' Em) :=
            hIH.2
          rw [Work.OROneRel.rootW_pow t u l hcyc htσ hl] at hannIH
          have hordIH : orderOf (presentRho (Work.OROneRel.mmW t (u ^ l))
              (Work.OROneRel.rootW t u l hcyc htσ hl)) = l := by
            rw [← Work.OROneRel.rootW_pow t u l hcyc htσ hl]
            exact hIH.1
          exact ⟨annAt_of_epsZero_strong t u l hl hpp hcyc htL htσ Em hEmne hannIH,
            orderOf_of_mmBaseHom t u l hl hpp hcyc htL htσ hordIH⟩
        by_cases hα : ∃ t ∈ Work.OROneRel.relatorLetters u, Work.OROneRel.eps t u = 0 ∧ t ∉ S
        · -- the framing letter lies *outside* `S`: use the strong form of the transfer
          obtain ⟨t, htL, htσ, htS⟩ := hα
          set Em : Set {y : α // y ≠ t} := {y | y.1 ∈ S} with hEm
          have hEmne : Em.Nonempty := by
            obtain ⟨z, hz⟩ := hSne
            exact ⟨⟨z, fun h => htS (h ▸ hz)⟩, hz⟩
          have hsub : ((fun y : {y : α // y ≠ t} => mmTopSym t u l y.1 y.2) '' Em) ⊆
              Work.OROneRel.relatorLetters (Work.OROneRel.rootW t u l hcyc htσ hl) := by
            rintro q ⟨y, hy, rfl⟩
            exact mmTopSym_mem_relatorLetters t u l hcyc htσ hl y.1 y.2 (hSsub hy)
          obtain ⟨hann, hord⟩ := hstep t htL htσ Em hEmne hsub
          exact ⟨hord, annAt_mono (by rintro z ⟨y, hy, rfl⟩; exact hy) hann⟩
        · by_cases hβ : ∃ t ∈ S, Work.OROneRel.eps t u = 0 ∧ ∃ x ∈ S, x ≠ t
          · -- the framing letter lies *inside* `S`, together with a second letter
            obtain ⟨t, htS, htσ, x, hxS, hxt⟩ := hβ
            have htL : t ∈ Work.OROneRel.relatorLetters u := hSsub htS
            set Em : Set {y : α // y ≠ t} := {y | y.1 ∈ S} with hEm
            have hEmne : Em.Nonempty := ⟨⟨x, hxt⟩, hxS⟩
            have hsub : ((fun y : {y : α // y ≠ t} => mmTopSym t u l y.1 y.2) '' Em) ⊆
                Work.OROneRel.relatorLetters (Work.OROneRel.rootW t u l hcyc htσ hl) := by
              rintro q ⟨y, hy, rfl⟩
              exact mmTopSym_mem_relatorLetters t u l hcyc htσ hl y.1 y.2 (hSsub hy)
            obtain ⟨hann, hord⟩ := hstep t htL htσ Em hEmne hsub
            exact ⟨hord, annAt_mono (by rintro z ⟨y, hy, rfl⟩; exact hy) hann⟩
          · -- the residual case: split it into its two parts
            push_neg at hβ
            have hcond : ∀ t ∈ Work.OROneRel.relatorLetters u, Work.OROneRel.eps t u = 0 →
                S = {t} := by
              intro t htL htσ
              have htS : t ∈ S := by
                by_contra ht
                exact hα ⟨t, htL, htσ, ht⟩
              refine Set.Subset.antisymm (fun x hx => hβ t htS htσ x hx) ?_
              intro x hx
              rw [Set.mem_singleton_iff] at hx
              rwa [hx]
            by_cases hσ : ∃ t ∈ Work.OROneRel.relatorLetters u, Work.OROneRel.eps t u = 0
            · -- exactly one vanishing-exponent-sum letter, and `S` is the singleton it spans
              obtain ⟨t, htL, htσ⟩ := hσ
              have hSt : S = {t} := hcond t htL htσ
              have huniq : ∀ x ∈ Work.OROneRel.relatorLetters u, Work.OROneRel.eps x u = 0 →
                  x = t := by
                intro x hxL hxσ
                have h1 : (t : α) ∈ S := by rw [hSt]; exact Set.mem_singleton t
                have h2 : (t : α) ∈ ({x} : Set α) := by rw [← hcond x hxL hxσ]; exact h1
                exact (Set.mem_singleton_iff.mp h2).symm
              -- the order statement: from the Magnus step at `t` and the induction hypothesis
              have hord : orderOf (presentRho (u ^ l) u) = l := by
                refine orderOf_of_mmBaseHom t u l hl hpp hcyc htL htσ ?_
                rw [← Work.OROneRel.rootW_pow t u l hcyc htσ hl]
                exact (ih (Work.OROneRel.rootW t u l hcyc htσ hl) l hl
                  (Work.OROneRel.not_isProperPower_rootW t u l hpp hcyc htσ hl)
                  (isCyclicallyReducedRelator_rootW t u l hcyc htσ hl)
                  (by have := Work.OROneRel.relatorNorm_rootW_lt t u l hcyc htσ hl htL; omega)
                  (Work.OROneRel.relatorLetters (Work.OROneRel.rootW t u l hcyc htσ hl))
                  (relatorLetters_nonempty_of_ne_one
                    (Work.OROneRel.ne_one_of_not_isProperPower
                      (Work.OROneRel.not_isProperPower_rootW t u l hpp hcyc htσ hl)))
                  (Set.Subset.refl _)).1
              refine ⟨hord, ?_⟩
              rw [hSt]
              obtain ⟨β, v, r', S', hpp', hr', hcyc', hlt', hS'ne, hS'sub, htrans⟩ :=
                h2.part2 u l hl hpp hcyc hsmall t htL htσ huniq
              refine htrans ?_
              rw [hr']
              exact (ih v l hl hpp' hcyc' (by omega) S' hS'ne hS'sub).2
            · -- no letter of `u` has vanishing exponent sum: node N2's Case 2
              push_neg at hσ
              obtain ⟨hdes, hord⟩ := h2.part1 u l hl hpp hcyc hsmall hσ S hSne hSsub
              obtain ⟨β, v, r', S', hpp', hr', hcyc', hlt', hS'ne, hS'sub, htrans⟩ := hdes
              refine ⟨hord, htrans ?_⟩
              rw [hr']
              exact (ih v l hl hpp' hcyc' (by omega) S' hS'ne hS'sub).2

/-- **The descent**, `annAt` part: the strong induction on `relatorNorm`.  Assuming the residual
hypothesis, the `annAt` statement holds for *every* nonempty set of letters of every cyclically
reduced root which is not a proper power. -/
theorem annAt_of_descent (h2 : Case2Descent.{u, v} K) :
    ∀ n {α : Type u} [DecidableEq α] (u : FreeGroup α) (l : ℕ), 1 ≤ l →
      ¬ Work.OROneRel.IsProperPower u → Work.OROneRel.IsCyclicallyReducedRelator u →
      Work.OROneRel.relatorNorm u ≤ n →
      ∀ S : Set α, S.Nonempty → S ⊆ Work.OROneRel.relatorLetters u → annAt K (u ^ l) u S := by
  intro n α _ u l hl hpp hcyc hn S hSne hSsub
  exact (descent_bundle h2 n u l hl hpp hcyc hn S hSne hSsub).2

/-- **`annAt` at the letters of the root**, from the descent hypothesis. -/
theorem annAt_letters_of_descent (h2 : Case2Descent.{u, v} K) {α : Type u} [DecidableEq α]
    (u : FreeGroup α) (l : ℕ) (hl : 1 ≤ l) (hpp : ¬ Work.OROneRel.IsProperPower u)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator u) :
    annAt K (u ^ l) u (Work.OROneRel.relatorLetters u) :=
  annAt_of_descent h2 (Work.OROneRel.relatorNorm u) u l hl hpp hcyc le_rfl _
    (relatorLetters_nonempty_of_ne_one (Work.OROneRel.ne_one_of_not_isProperPower hpp))
    (Set.Subset.refl _)

/-- **Componentwise right regularity of the root Fox vector at every letter of the root.**  The
descent in fact proves the *strongest* form of the induction hypothesis: `annAt` for every nonempty
set of letters, hence in particular for the singletons.  This is what the exempted-set formulation
(`CLInvariantWith`, `CLStepA.lean`) could *not* deliver: there, regularity had to be exempted at
least at the framing letters. -/
theorem regular_rootVec_of_descent (h2 : Case2Descent.{u, v} K) {α : Type u} [DecidableEq α]
    {u : FreeGroup α} {l : ℕ} (hl : 1 ≤ l) (hpp : ¬ Work.OROneRel.IsProperPower u)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator u) {x : α}
    (hx : x ∈ Work.OROneRel.relatorLetters u) :
    ∀ b : MonoidAlgebra K (OneRelatorGroup (u ^ l)), b * rootVec K (u ^ l) u x = 0 → b = 0 := by
  have h := annAt_of_descent h2 (Work.OROneRel.relatorNorm u) u l hl hpp hcyc le_rfl {x}
    ⟨x, rfl⟩ (by rintro y rfl; exact hx)
  intro b hb
  exact h b fun y hy => by rw [Set.mem_singleton_iff.mp hy]; exact hb

/-- **The Cohen--Lyndon theorem for a cyclically reduced root**, from the descent hypothesis.  The
descent gives both the order statement and `annAt` at the letters of `s`, hence the triviality of
the annihilator of the root Fox vector, and `Work.ORLyndon.lyndon_independence_of_rootVec_inj`
concludes. -/
theorem lyndon_independence_of_pow_of_case2_cyclic (h2 : Case2Descent.{u, v} K)
    {X : Type u} [DecidableEq X] {s : FreeGroup X} (l : ℕ) (hl : 1 ≤ l)
    (hpp : ¬ Work.OROneRel.IsProperPower s)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator s) :
    LyndonIndependence K (s ^ l) s := by
  classical
  have hb := descent_bundle h2 (Work.OROneRel.relatorNorm s) s l hl hpp hcyc le_rfl
    (Work.OROneRel.relatorLetters s)
    (relatorLetters_nonempty_of_ne_one (Work.OROneRel.ne_one_of_not_isProperPower hpp))
    (Set.Subset.refl _)
  have hann : annAt K (s ^ l) s (Work.OROneRel.relatorLetters s) := hb.2
  have hI : ∀ b : MonoidAlgebra K (OneRelatorGroup (s ^ l)),
      b • rootVec K (s ^ l) s = 0 → b = 0 := vector_zero_of_annAt_letters hann
  exact lyndon_independence_of_rootVec_inj (s ^ l) s l hl rfl hb.1 hI

/-- **The Cohen--Lyndon theorem, from the descent hypothesis.**  Any root is replaced by its cyclic
reduction `s`, where the descent gives both the order statement and `annAt` at the letters of `s`,
and `Work.ORLyndon.lyndonIndependence_conj` transports the conclusion for `(s ^ l, s)` back to
`(r, u)`.  No further input (in particular, no Karrass--Magnus--Solitar torsion theorem) is needed. -/
theorem lyndon_independence_of_pow_of_case2 (h2 : Case2Descent.{u, v} K)
    {X : Type u} [DecidableEq X] (r u : FreeGroup X) (l : ℕ) (hl : 1 ≤ l) (hpow : r = u ^ l)
    (hpp : ¬ Work.OROneRel.IsProperPower u) :
    LyndonIndependence K r u := by
  classical
  set s : FreeGroup X := Work.OROneRel.cyclicReduction u with hs
  set c : FreeGroup X := Work.OROneRel.cyclicConjugator u with hc
  have hcs : c * s * c⁻¹ = u := Work.OROneRel.cyclicConjugator_mul_cyclicReduction_mul_inv u
  have hconj : c * s ^ l * c⁻¹ = (c * s * c⁻¹) ^ l := by
    rw [← MulAut.conj_apply c (s ^ l), map_pow, MulAut.conj_apply c s]
  have hspow : (c * s * c⁻¹) ^ l = r := by rw [hcs, hpow]
  have hspp : ¬ Work.OROneRel.IsProperPower s := by
    rw [hs]; exact Work.OROneRel.not_isProperPower_cyclicReduction hpp
  have hscyc : Work.OROneRel.IsCyclicallyReducedRelator s := by
    rw [hs]; exact Work.OROneRel.isCyclicallyReducedRelator_cyclicReduction u
  have hLI : LyndonIndependence K (s ^ l) s :=
    lyndon_independence_of_pow_of_case2_cyclic h2 l hl hspp hscyc
  have hconjLI := lyndonIndependence_conj (s ^ l) s c hLI
  rw [hpow]
  simpa only [hconj, hcs] using hconjLI

/-- The same statement as `Work.ORLyndon.lyndon_independence_of_pow_of_case2`, kept under the name
used in the first draft of this reduction.  The Karrass--Magnus--Solitar order input is now
*provided by* `Work.ORLyndon.Case2Descent` (which demands it, as node N2's Magnus step does), so
unlike the first draft this declaration no longer consumes `Work.ORLyndon.orderOf_presentRho` (node
N2's `kms_torsion_at`) and carries no `sorryAx`. -/
theorem lyndon_independence_of_pow_of_case2_unconditional (h2 : Case2Descent.{u, v} K)
    {X : Type u} [DecidableEq X] (r u : FreeGroup X) (l : ℕ) (hl : 1 ≤ l) (hpow : r = u ^ l)
    (hpp : ¬ Work.OROneRel.IsProperPower u) : LyndonIndependence K r u :=
  lyndon_independence_of_pow_of_case2 h2 r u l hl hpow hpp

end Work.ORLyndon
