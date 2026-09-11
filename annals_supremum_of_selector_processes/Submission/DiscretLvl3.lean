import Mathlib.Probability.Distributions.SetBernoulli
import ChallengeDeps
import Submission.Multi
import Submission.MultiMass
import Submission.MultiW2
import Submission.DiscretLvl
import Submission.DiscretLvl2

/-!
# TASK (child): prove ALL lemmas in this file (no gaps).  Statements FIXED; helpers allowed.
# namespace Submission.DiscretLvl3.  Uses `DiscretLvl.lvl`, `DiscretLvl.lvl_le`, `DiscretLvl.lvl_of_unique`,
# `DiscretLvl.lvl_interval`, `DiscretLvl.lvl_top_zero`, `DiscretLvl.lvl_neg_zero` (all PROVEN in
# Submission/DiscretLvl.lean and Submission/DiscretLvl2.lean -- import them).
# The task: exact descriptions of the fibers {x | lvl ε L (g x) = k} for measurable g : α → ℝ, and
# measurability of the level maps.
# HINTS:
#  * fiber k (1 ≤ k ≤ L): {x | lvl(g x) = k} = {x | kε ≤ g x ∧ g x < (k+1)ε}: use
#    `DiscretLvl.lvl_interval` (both directions; note its hypotheses (hε : 0 < ε) (L) (v) {k} (hk0 : 1 ≤ k)
#    (hk : k ≤ L) give `lvl ε L v = k ↔ kε ≤ v ∧ v < ((k+1:ℕ):ℝ)*ε`).
#  * fiber 0: complement of the union of fibers 1..L (set-identity below).
#  * measurability of `fun x => lvl ε L (g x)` (into ℕ, discrete): use
#    `MeasurableSpace.measurableSet_setOf`-style or the general lemma for measurable functions into ℕ:
#    prove by fibers: for every k, `MeasurableSet {x | lvl ε L (g x) = k}`; case k = 0 and k ≥ 1 with
#    the fiber identities + `measurableSet_lt`/`measurableSet_ge`-style interval preimages of the
#    measurable function g (ℝ has measurable intervals: `measurableSet_Ico` etc.).
#  * measurability into Fin (L+1) of `fun x => (⟨lvl ε L (g x), hlt x⟩ : Fin (L+1))` where
#    `hlt x : lvl ε L (g x) < L+1` (from lvl_le): prove using the fibers {x | lvl = k} (k < L+1)
#    directly (the preimage of {k} under the Fin-valued map is {x | lvl (g x) = k.val}, measurable
#    by the previous lemma + Fin.val injectivity; note the Fin-measurable-space fibers: {c} for
#    c : Fin (L+1): preimage {x | ⟨lvl...,hlt x⟩ = c} = {x | lvl ... = c.val}: since equality of Fin
#    elements reduces to equality of .val (Fin.ext)).
#  * Use `funext`, `Set.ext`, `simp [lvl]` sparingly; beware cast shapes ((k:ℝ)*ε vs ↑k*ε) -- use
#    `norm_num`/`exact_mod_cast`.
# Keep it in namespace Submission.DiscretLvl3; do not rename the fixed lemmas; no new imports.
-/


set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
open Classical
open scoped NNReal ENNReal BigOperators

namespace Submission

namespace DiscretLvl3

/-- the fiber of a positive level is the corresponding half-open interval (pulled back) -/
lemma fiber_pos {α : Type*} (ε : ℝ) (hε : 0 < ε) (L : ℕ) (g : α → ℝ) (k : ℕ)
    (hk0 : 1 ≤ k) (hk : k ≤ L) :
    {x | DiscretLvl.lvl ε L (g x) = k}
      = {x | (k : ℝ) * ε ≤ g x ∧ g x < ((k + 1 : ℕ) : ℝ) * ε} := by
  ext x
  exact DiscretLvl.lvl_interval hε L (g x) hk0 hk

/-- the fiber of level 0 is the complement of the union of the positive fibers -/
lemma fiber_zero {α : Type*} (ε : ℝ) (hε : 0 < ε) (L : ℕ) (g : α → ℝ) :
    {x | DiscretLvl.lvl ε L (g x) = 0}
      = {x | ¬ ∃ k : ℕ, 1 ≤ k ∧ k ≤ L ∧ (k : ℝ) * ε ≤ g x ∧ g x < ((k + 1 : ℕ) : ℝ) * ε} := by
  ext x
  constructor
  · intro hl hk
    rcases hk with ⟨k, hk1, hkL, hf⟩
    have hz : DiscretLvl.lvl ε L (g x) = k := (DiscretLvl.lvl_interval hε L (g x) hk1 hkL).2 hf
    have hk0 : k = 0 := by rw [← hz, hl]
    omega
  · intro hnot
    by_contra h
    have hlpos : 1 ≤ DiscretLvl.lvl ε L (g x) :=
      Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero h)
    have hleL : DiscretLvl.lvl ε L (g x) ≤ L := DiscretLvl.lvl_le hε L (g x)
    have hf : (DiscretLvl.lvl ε L (g x) : ℝ) * ε ≤ g x ∧
        g x < ((DiscretLvl.lvl ε L (g x) + 1 : ℕ) : ℝ) * ε :=
      (DiscretLvl.lvl_interval hε L (g x) hlpos hleL).1 rfl
    exact hnot ⟨DiscretLvl.lvl ε L (g x), hlpos, hleL, hf⟩

variable {α : Type*} [MeasurableSpace α]

/-- helper: the pullback of a half-open interval by a measurable g is measurable -/
private lemma interval_fiber_meas (ε : ℝ) (L : ℕ) (g : α → ℝ) (hg : Measurable g) (k : ℕ) :
    MeasurableSet {x : α | (k : ℝ) * ε ≤ g x ∧ g x < ((k + 1 : ℕ) : ℝ) * ε} := by
  have hk : MeasurableSet (Set.Ico ((k : ℝ) * ε) (((k + 1 : ℕ) : ℝ) * ε)) := measurableSet_Ico
  simpa [Set.preimage, Set.mem_Ico] using (hg hk)

/-- helper: every level fiber of the composed level map is measurable -/
private lemma level_fiber_meas (ε : ℝ) (hε : 0 < ε) (L : ℕ) (g : α → ℝ) (hg : Measurable g)
    (n : ℕ) : MeasurableSet {x : α | DiscretLvl.lvl ε L (g x) = n} := by
  by_cases hn0 : n = 0
  · subst n
    rw [fiber_zero ε hε L g]
    let P : ℕ → Set α := fun k => {x : α | (k : ℝ) * ε ≤ g x ∧ g x < ((k + 1 : ℕ) : ℝ) * ε}
    let B : ℕ → Set α := fun k => {x : α | 1 ≤ k ∧ k ≤ L} ∩ P k
    have hC : ∀ k : ℕ, MeasurableSet {x : α | 1 ≤ k ∧ k ≤ L} := by
      intro k
      by_cases hk : 1 ≤ k ∧ k ≤ L
      · simp [hk]
      · simp [hk]
    have hB : ∀ k : ℕ, MeasurableSet (B k) := by
      intro k
      unfold B
      exact (hC k).inter (interval_fiber_meas ε L g hg k)
    have hU : MeasurableSet (⋃ k : ℕ, B k) := MeasurableSet.iUnion fun k => hB k
    have hset : {x : α | ¬ ∃ k : ℕ, 1 ≤ k ∧ k ≤ L ∧ (k : ℝ) * ε ≤ g x ∧
        g x < ((k + 1 : ℕ) : ℝ) * ε} = (⋃ k : ℕ, B k)ᶜ := by
      ext x
      simp [B, P]
    rw [hset]
    exact hU.compl
  · have hnpos : 1 ≤ n := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hn0)
    by_cases hnL : n ≤ L
    · rw [fiber_pos ε hε L g n hnpos hnL]
      exact interval_fiber_meas ε L g hg n
    · have he : {x : α | DiscretLvl.lvl ε L (g x) = n} = (∅ : Set α) := by
        ext x
        constructor
        · intro hx
          have hle : DiscretLvl.lvl ε L (g x) ≤ L := DiscretLvl.lvl_le hε L (g x)
          have : n ≤ L := by rw [← hx]; exact hle
          omega
        · intro hx
          simp at hx
      rw [he]
      exact MeasurableSet.empty

/-- the level of a measurable real function is measurable (into ℕ) -/
lemma measurable_level {α : Type*} [MeasurableSpace α] (ε : ℝ) (hε : 0 < ε) (L : ℕ)
    (g : α → ℝ) (hg : Measurable g) : Measurable (fun x => DiscretLvl.lvl ε L (g x)) := by
  apply measurable_to_countable'
  intro n
  change MeasurableSet {x : α | DiscretLvl.lvl ε L (g x) = n}
  exact level_fiber_meas ε hε L g hg n

/-- the level of a measurable real function is measurable into Fin (L+1) -/
lemma measurable_level_fin {α : Type*} [MeasurableSpace α] (ε : ℝ) (hε : 0 < ε) (L : ℕ)
    (g : α → ℝ) (hg : Measurable g) (hge : ∀ x, 0 ≤ g x) :
    Measurable (fun x : α => (⟨DiscretLvl.lvl ε L (g x), Nat.lt_succ_of_le (DiscretLvl.lvl_le hε L (g x))⟩ : Fin (L + 1))) := by
  apply measurable_to_countable'
  intro c
  change MeasurableSet {x : α |
    (fun x : α => (⟨DiscretLvl.lvl ε L (g x), Nat.lt_succ_of_le (DiscretLvl.lvl_le hε L (g x))⟩ : Fin (L + 1))) x = c}
  have hset : {x : α | (⟨DiscretLvl.lvl ε L (g x), Nat.lt_succ_of_le (DiscretLvl.lvl_le hε L (g x))⟩ : Fin (L + 1)) = c}
      = {x | DiscretLvl.lvl ε L (g x) = c.val} := by
    ext x
    constructor
    · intro h
      exact congrArg Fin.val h
    · intro h
      apply Fin.ext
      simpa using h
  rw [hset]
  exact level_fiber_meas ε hε L g hg c.val

end DiscretLvl3
end Submission
