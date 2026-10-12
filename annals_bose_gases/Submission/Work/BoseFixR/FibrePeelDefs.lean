import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Data.Finsupp.Single
import Submission.Work.BoseFixR.FibreCount
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.FibrePeelDefs` — vocabulary for the fibre-peeling bijection

The **fibre count** of a labelling `σ : Fin m → ι` at a value `i` is the number of
coordinates of `σ` carrying the value `i`,

`fibCount σ i = #{d | σ d = i}`.

The companion module `Work.BoseFixR.fibre_peel` proves the peeling identity

`#{σ : Fin (n+1) → ι | fibCount σ = α}
   = ∑_{k : α k ≠ 0} #{τ : Fin n → ι | fibCount τ = α.update k (α k - 1)}`

by removing the last particle: the last value `σ (Fin.last n) = k` has `α k ≠ 0`, the initial
segment `Fin.init σ` has fibre counts `α.update k (α k - 1)`, and conversely `Fin.snoc τ k`
glues back.

This module fixes the vocabulary (`fibCount`) and records the elementary counting facts used
by that argument:

* `fibCount_snoc'` — peeling/gluing a particle at the end (restatement of
  `Work.BoseFixR.card_fibre_snoc` from `FibreCount`, with the `if` on the fibre value `i`);
* `fibCount_init_add` — the same read along `Fin.init`;
* `fibCount_ne_zero_last` — the last value of a labelling realising `α` is in the support;
* `fibCount_update` — the pointwise value of `α.update k (α k - 1)`.
-/

open Finset

namespace Work.BoseFixR

/-- The number of coordinates `d : Fin m` such that `σ d = i`. -/
def fibCount {ι : Type*} [DecidableEq ι] {m : ℕ} (σ : Fin m → ι) (i : ι) : ℕ :=
  (Finset.univ.filter fun d => σ d = i).card

lemma fibCount_apply {ι : Type*} [DecidableEq ι] {m : ℕ} (σ : Fin m → ι) (i : ι) :
    fibCount σ i = (Finset.univ.filter fun d => σ d = i).card := rfl

/-- The pointwise value of `α.update k (α k - 1)`. -/
lemma fibCount_update {ι : Type*} [DecidableEq ι] (α : ι →₀ ℕ) (k i : ι) :
    (α.update k (α k - 1)) i = if i = k then α k - 1 else α i :=
  Finsupp.update_apply α k (α k - 1) i

/-- Peeling/gluing a particle at the end, in the `fibCount` vocabulary. -/
lemma fibCount_snoc' {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (τ : Fin n → ι) (k i : ι) :
    fibCount (Fin.snoc τ k) i = fibCount τ i + (if i = k then 1 else 0) := by
  rw [fibCount_apply, fibCount_apply, card_fibre_snoc]
  by_cases h : i = k
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

/-- Reading the fibre count of `σ : Fin (n+1) → ι` through its initial segment. -/
lemma fibCount_init_add {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (σ : Fin (n+1) → ι)
    (i : ι) : fibCount σ i = fibCount (Fin.init σ) i + (if i = σ (Fin.last n) then 1 else 0) := by
  conv_lhs => rw [← Fin.snoc_init_self σ]
  exact fibCount_snoc' (Fin.init σ) (σ (Fin.last n)) i

/-- The last value of a labelling realising `α` lies in the support of `α`. -/
lemma fibCount_ne_zero_last {ι : Type*} [DecidableEq ι] {m : ℕ} (α : ι →₀ ℕ)
    (σ : Fin (m+1) → ι) (hσ : ∀ i, fibCount σ i = α i) : α (σ (Fin.last m)) ≠ 0 := by
  have hpos : 0 < fibCount σ (σ (Fin.last m)) := by
    rw [fibCount_apply]
    exact Finset.card_pos.mpr ⟨Fin.last m, by simp⟩
  have := hσ (σ (Fin.last m))
  omega

end Work.BoseFixR
