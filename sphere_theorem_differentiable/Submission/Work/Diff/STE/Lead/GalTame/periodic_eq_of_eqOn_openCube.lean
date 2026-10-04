import Mathlib
import Submission.Work.Diff.STE.Torus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead.GalTame

open Filter

/-! ## Translation by integer vectors

`Periodic1 f` says `f (x + eᵢ) = f x` for the standard basis vectors `eᵢ`.  We record the
consequence that `f` is invariant under translation by an arbitrary integer vector. -/

/-- `1`-periodicity in the coordinate `i` gives invariance under integer multiples of `eᵢ`. -/
lemma periodic1_zsmul {ι : Type*} [DecidableEq ι] {β : Type*} {f : (ι → ℝ) → β}
    (hf : Work.Diff.STE.Periodic1 f) (i : ι) (k : ℤ) (x : ι → ℝ) :
    f (x + (k : ℝ) • Pi.single i (1 : ℝ)) = f x := by
  have h : Function.Periodic f (Pi.single i (1 : ℝ)) := hf i
  rw [Int.cast_smul_eq_zsmul]
  exact h.zsmul k x

/-- Invariance of a `1`-periodic function under translation by an integer vector. -/
lemma periodic1_add_sum {ι : Type*} [Fintype ι] [DecidableEq ι] {β : Type*}
    {f : (ι → ℝ) → β} (hf : Work.Diff.STE.Periodic1 f) (c : ι → ℤ) (y : ι → ℝ) :
    f (y + ∑ i, (c i : ℝ) • Pi.single i (1 : ℝ)) = f y := by
  classical
  have aux : ∀ s : Finset ι, f (y + ∑ i ∈ s, (c i : ℝ) • Pi.single i (1 : ℝ)) = f y := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | insert a s ha ih =>
        rw [Finset.sum_insert ha]
        have hv : y + ((c a : ℝ) • Pi.single a 1 + ∑ i ∈ s, (c i : ℝ) • Pi.single i 1)
            = (y + ∑ i ∈ s, (c i : ℝ) • Pi.single i 1) + (c a : ℝ) • Pi.single a 1 := by
          abel
        rw [hv, periodic1_zsmul hf a (c a), ih]
  simpa using aux Finset.univ

/-- Invariance of a `1`-periodic function under translation by an integer vector, in the form in
which the translate is displayed as the function `i ↦ (c i : ℝ)`. -/
lemma periodic1_add_intVec {ι : Type*} [Fintype ι] [DecidableEq ι] {β : Type*}
    {f : (ι → ℝ) → β} (hf : Work.Diff.STE.Periodic1 f) (c : ι → ℤ) (y : ι → ℝ) :
    f (y + fun i => (c i : ℝ)) = f y := by
  have h1 : (∑ i, (c i : ℝ) • Pi.single i (1 : ℝ) : ι → ℝ) = fun i => (c i : ℝ) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq, Finset.mem_univ]
  rw [← h1]
  exact periodic1_add_sum hf c y

/-- **A `1`-periodic continuous function is determined by its values on the fundamental cube.**

Two `1`-periodic (in every coordinate) continuous functions `ι → ℝ → ℂ` that agree on the open
fundamental cube `(-1/2, 1/2)^ι` agree everywhere.

Proof: the translates of the open cube by integer vectors cover `ℝ^ι` up to the null set
`{z | ∃ i, z i ∈ 1/2 + ℤ}`.  For a point `z` in a translate `(-1/2,1/2)^ι + m` one uses the
periodicity (`f (z - m) = f z` because `z - m` differs from `z` by the integer vector `-m`) to
reduce to the open cube; for the remaining points one takes the limit along a sequence lying in the
open cube together with the continuity of `f` and `g`.  (A convenient choice: `m i = ⌊z i + 1/2⌋`,
so that `z - m ∈ [-1/2,1/2)^ι`, and then approximate `z - m` from above by
`(z - m) + (1/(k+1)) • (1,…,1)`.) -/
theorem periodic_eq_of_eqOn_openCube
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f g : (ι → ℝ) → ℂ} (hf : Work.Diff.STE.Periodic1 f) (hg : Work.Diff.STE.Periodic1 g)
    (hfc : Continuous f) (hgc : Continuous g)
    (h : ∀ z : ι → ℝ, (∀ i, z i ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) → f z = g z) :
    f = g := by
  classical
  funext z
  -- The integer vector and the representative `y = z - m` with `y i ∈ [-1/2, 1/2)`.
  set m : ι → ℤ := fun i => ⌊z i + 1 / 2⌋ with hm
  set y : ι → ℝ := fun i => z i - (m i : ℝ) with hy
  have hy_low : ∀ i, -(1 / 2 : ℝ) ≤ y i := by
    intro i
    rw [hy]
    simp only [hm]
    have := Int.floor_le (z i + 1 / 2)
    linarith
  have hy_up : ∀ i, y i < 1 / 2 := by
    intro i
    rw [hy]
    simp only [hm]
    have := Int.lt_floor_add_one (z i + 1 / 2)
    linarith
  -- The set of coordinates in which the representative sits on the lower wall `-1/2`.
  set W : Finset ι := Finset.univ.filter (fun i => y i = -(1 / 2 : ℝ)) with hW
  -- The direction in which we perturb: `+1` along the walls, `0` elsewhere.
  set v : ι → ℝ := fun i => if i ∈ W then 1 else 0 with hv
  -- The perturbing sequence `w k = z + (1/(k+2)) • v`.
  set w : ℕ → ι → ℝ := fun k => z + (1 / ((k : ℝ) + 2)) • v with hw
  have hεpos : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 2) := by intro k; positivity
  have hεlt : ∀ k : ℕ, (1 : ℝ) / ((k : ℝ) + 2) < 1 := by
    intro k
    rw [div_lt_one (by positivity)]
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hwtend : Tendsto w atTop (nhds z) := by
    have h1 : Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 2)) atTop (nhds 0) := by
      have hh := (Filter.tendsto_add_atTop_iff_nat
        (f := fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) 1).mpr
        tendsto_one_div_add_atTop_nhds_zero_nat
      convert hh using 1
      ext k
      push_cast
      ring
    have h3 : Tendsto (fun k : ℕ => z + (1 / ((k : ℝ) + 2)) • v) atTop
        (nhds (z + (0 : ℝ) • v)) := (h1.smul_const v).const_add z
    simpa [hw, zero_smul, add_zero] using h3
  -- Every `w k` reduces to a point of the open cube by translation with the integer vector `m`.
  have hmem : ∀ k : ℕ, ∀ i, (w k - fun i => (m i : ℝ)) i ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) := by
    intro k i
    have hcoord : (w k - fun i => (m i : ℝ)) i = y i + (1 / ((k : ℝ) + 2)) * v i := by
      simp only [hw, hy, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hcoord]
    by_cases hi : i ∈ W
    · -- On a wall coordinate the perturbation moves the point into the open interval.
      have hyi : y i = -(1 / 2 : ℝ) := (Finset.mem_filter.mp hi).2
      have hvi : v i = 1 := by simp [hv, hi]
      rw [hyi, hvi, mul_one]
      exact ⟨by linarith [hεpos k], by linarith [hεlt k]⟩
    · -- Elsewhere the coordinate is untouched and already lies in the open interval.
      have hvi : v i = 0 := by simp [hv, hi]
      have hyi : y i ≠ -(1 / 2 : ℝ) :=
        fun hh => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hh⟩)
      rw [hvi, mul_zero, add_zero]
      exact ⟨lt_of_le_of_ne (hy_low i) (Ne.symm hyi), hy_up i⟩
  have hpoint : ∀ k : ℕ, f (w k) = g (w k) := by
    intro k
    have hfm : f (w k) = f (w k - fun i => (m i : ℝ)) := by
      have hh := periodic1_add_intVec hf m (w k - fun i => (m i : ℝ))
      rw [sub_add_cancel] at hh
      exact hh
    have hgm : g (w k) = g (w k - fun i => (m i : ℝ)) := by
      have hh := periodic1_add_intVec hg m (w k - fun i => (m i : ℝ))
      rw [sub_add_cancel] at hh
      exact hh
    rw [hfm, hgm, h _ (hmem k)]
  have hft : Tendsto (fun k => f (w k)) atTop (nhds (f z)) :=
    hfc.continuousAt.tendsto.comp hwtend
  have hgt : Tendsto (fun k => g (w k)) atTop (nhds (g z)) :=
    hgc.continuousAt.tendsto.comp hwtend
  have hgt' : Tendsto (fun k => f (w k)) atTop (nhds (g z)) :=
    Filter.Tendsto.congr' (Eventually.of_forall (fun k => (hpoint k).symm)) hgt
  exact tendsto_nhds_unique hft hgt'

end Work.Diff.STE.Lead.GalTame
