/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# The `Z`-cover root is not a proper power when a decorated letter occurs once

`coverRoot W c u` is the word over the symbols `β = coverBeta W c u` spelled by the decorated
letters of `u` of non-trivial loop class (`coverRootDefs.lean`).  This file proves that if some
symbol `x : β` occurs **exactly once** in the list `coverRootList W c u` then `coverRoot W c u` is
not a proper power.

The argument is the exponent-sum obstruction.  `sigma x : FreeGroup β →* Multiplicative ℤ` is the
homomorphism sending `x` to `1` and every other generator to `0`, and `eps x r` is its additive
shadow (`epsc_eq_toAdd_sigma`).  On a `k`-th power the exponent sum is multiplied by `k`
(`epsc_zpow`), so a relator whose exponent sum in some generator is `±1` cannot be a proper power.
Since `coverRootList` emits every symbol with the constant exponent `true`, the exponent sum of `x`
in `coverRoot W c u` is exactly the number of occurrences of `(x, true)` in `coverRootList W c u`
(`sigmaList_eq_count_of_forall_snd`), which is `1` by hypothesis.
-/
import Mathlib
import Submission.Work.OROneRel.coverRootDefs
import Submission.Work.OROneRel.exists_cover_root_data
import Submission.Work.OROneRel.eps_rightPow
import Submission.Work.OROneRel.sigma_mk
import Submission.Work.OROneRel.FreiheitssatzDefs

namespace Work.OROneRel

universe u

/-! ## Exponent sums on lists -/

/-- The exponent sum over a cons. -/
lemma sigmaList_cons {β : Type u} (x : β) (a : β × Bool) (M : List (β × Bool)) :
    sigmaList x (a :: M) = letterSign x a + sigmaList x M := by
  rw [sigmaList, sigmaList, List.map_cons, List.sum_cons]

/-- A letter `(x, true)` contributes `1` to the exponent sum of `x`. -/
lemma letterSign_eq_one_of_eq {β : Type u} {x : β} {a : β × Bool} (h : a = (x, true)) :
    letterSign x a = 1 := by
  subst h; simp [letterSign]

/-- A letter with second component `true` different from `(x, true)` contributes `0` to the exponent
sum of `x`. -/
lemma letterSign_eq_zero_of_snd_true_of_ne {β : Type u} {x : β} {a : β × Bool}
    (ha : a.2 = true) (h : a ≠ (x, true)) : letterSign x a = 0 := by
  obtain ⟨a1, a2⟩ := a
  simp only at ha h
  have hax : a1 ≠ x := by
    intro hc
    exact h (by simp [hc, ha])
  simp [letterSign, hax]

/-- **The exponent sum counts the positive occurrences.**  If every entry of `M` has second
component `true`, then the exponent sum in `x` is the number of occurrences of `(x, true)`. -/
lemma sigmaList_eq_count_of_forall_snd {β : Type u} [DecidableEq β] (x : β) (M : List (β × Bool))
    (hM : ∀ p ∈ M, p.2 = true) :
    sigmaList x M = (M.count (x, true) : ℤ) := by
  induction M with
  | nil => simp [sigmaList]
  | cons a M ih =>
    have ha : a.2 = true := hM a (List.mem_cons_self ..)
    have hM' : ∀ p ∈ M, p.2 = true := fun p hp => hM p (List.mem_cons_of_mem _ hp)
    rw [sigmaList_cons, ih hM']
    by_cases h : a = (x, true)
    · subst h
      rw [List.count_cons_self, letterSign_eq_one_of_eq rfl]
      push_cast
      ring
    · rw [List.count_cons_of_ne h, letterSign_eq_zero_of_snd_true_of_ne ha h]
      ring

/-! ## The proper-power obstruction -/

/-- **An element with an exponent sum `1` is not a proper power.**  If `r = w ^ k` with `k ≥ 2` then
`eps x r = k * eps x w`, which cannot be `1`. -/
lemma not_isProperPower_of_eps_eq_one {β : Type u} (x : β) {r : FreeGroup β}
    (h : eps x r = 1) : ¬ IsProperPower r := by
  rintro ⟨w, k, hk, rfl⟩
  have hkz : eps x (w ^ k) = (k : ℤ) * eps x w := by
    rw [← zpow_natCast w k, epsc_zpow]
  rw [hkz] at h
  have h1 : (k : ℤ) = 1 ∨ (k : ℤ) = -1 := Int.eq_one_or_neg_one_of_mul_eq_one h
  have hk2 : (2 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  omega

/-! ## The list `coverRootList` emits only positive powers -/

/-- `coverRootList` spells every symbol with the constant exponent `true`. -/
lemma coverRootList_snd_eq_true {α : Type u} (W : ℤ → FreeGroup α) (c : α → ℤ)
    (u : FreeGroup α) : ∀ p ∈ coverRootList W c u, p.2 = true := by
  intro p hp
  simp only [coverRootList] at hp
  rw [List.mem_filterMap] at hp
  obtain ⟨a, -, hfa⟩ := hp
  by_cases hc : coverClass W c a.1 ≠ 1
  · rw [dif_pos hc] at hfa
    have hthis := Option.some.inj hfa
    rw [← hthis]
  · rw [dif_neg hc] at hfa
    exact absurd hfa (by simp)

/-! ## The requested lemma -/

theorem not_isProperPower_coverRoot_of_count_one {α : Type u}
    (W : ℤ → FreeGroup α) (c : α → ℤ) (u : FreeGroup α) (x : Work.OROneRel.coverBeta W c u)
    (h : (Work.OROneRel.coverRootList W c u).count (x, true) = 1) :
    ¬ Work.OROneRel.IsProperPower (Work.OROneRel.coverRoot W c u) := by
  classical
  -- the exponent sum of `x` in `coverRoot` is the number of occurrences of `(x, true)`
  have hsig : sigmaList x (coverRootList W c u) = 1 := by
    rw [sigmaList_eq_count_of_forall_snd x _ (coverRootList_snd_eq_true W c u), h]
    norm_num
  have hsigma : sigma x (coverRoot W c u) = Multiplicative.ofAdd (1 : ℤ) := by
    rw [coverRoot, sigma_mk, hsig]
  have heps : eps x (coverRoot W c u) = 1 := by
    rw [epsc_eq_toAdd_sigma, hsigma]
    rfl
  exact not_isProperPower_of_eps_eq_one x heps

end Work.OROneRel
