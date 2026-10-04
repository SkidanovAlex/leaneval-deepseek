import Mathlib
import Submission.Work.Diff.STE.FlatPDE

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.flat

open Filter

/-- `box n N` is the set of lattice points of `ℤ^n` whose every coordinate lies in `[-N, N]`, i.e.
monomials with all exponents bounded by `N`.  A point all of whose coordinates have `natAbs` at most
`N` (equivalently, whose total `natAbs` is at most `N`) lies in `box n N`. -/
lemma mem_box_of_bd_le {n : ℕ} {k : Fin n → ℤ} {N : ℕ} (h : (∑ i, (k i).natAbs) ≤ N) :
    k ∈ Work.Diff.STE.Flat.box n N := by
  rw [Work.Diff.STE.Flat.box, Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_Icc]
  have hi : (k i).natAbs ≤ N := by
    have hle := Finset.single_le_sum (f := fun j : Fin n => (k j).natAbs)
      (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    simpa using le_trans hle h
  have h1 : -(((k i).natAbs : ℕ) : ℤ) ≤ k i := by
    have := Int.le_natAbs (a := -k i)
    simpa [Int.natAbs_neg] using neg_le_neg this
  have h2 : k i ≤ (((k i).natAbs : ℕ) : ℤ) := Int.le_natAbs
  have h3 : (((k i).natAbs : ℕ) : ℤ) ≤ (N : ℤ) := by exact_mod_cast hi
  constructor <;> omega

/-- The boxes `box n N` exhaust `ℤ^n`: as `N → ∞` they tend to `atTop` in the lattice of finite
subsets (i.e. every finite set of frequencies is eventually contained in `box n N`). -/
lemma tendsto_box_atTop {n : ℕ} :
    Tendsto (fun N : ℕ => Work.Diff.STE.Flat.box n N) atTop atTop := by
  rw [Filter.tendsto_atTop]
  intro s
  rw [Filter.eventually_atTop]
  refine ⟨s.sup (fun k : Fin n → ℤ => ∑ i, (k i).natAbs), fun N hN => ?_⟩
  intro k hk
  refine mem_box_of_bd_le (le_trans ?_ hN)
  exact Finset.le_sup (s := s) (f := fun k : Fin n → ℤ => ∑ i, (k i).natAbs) hk

/-- The tail of a summable family over the complement of `box n N` vanishes as `N → ∞`. -/
theorem tail_tsum_box_tendsto_zero {n : ℕ} (f : (Fin n → ℤ) → ℝ) :
    Filter.Tendsto
      (fun N : ℕ => ∑' k : {k : Fin n → ℤ // k ∉ Work.Diff.STE.Flat.box n N}, f k.1)
      Filter.atTop (nhds 0) := by
  by_cases hf : Summable f
  · -- Summable case: the tail is the full sum minus the partial sum over `box n N`.
    have hsum : Tendsto (fun s : Finset (Fin n → ℤ) => ∑ k ∈ s, f k) atTop
        (nhds (∑' k, f k)) := hf.hasSum
    have hN : Tendsto (fun N : ℕ => ∑ k ∈ Work.Diff.STE.Flat.box n N, f k) atTop
        (nhds (∑' k, f k)) := hsum.comp tendsto_box_atTop
    have heq : ∀ N, (∑' k : {k : Fin n → ℤ // k ∉ Work.Diff.STE.Flat.box n N}, f k.1)
        = (∑' k, f k) - ∑ k ∈ Work.Diff.STE.Flat.box n N, f k := by
      intro N
      have h := hf.sum_add_tsum_compl (s := Work.Diff.STE.Flat.box n N)
      rw [eq_sub_iff_add_eq, add_comm]
      exact h
    simp only [heq]
    have hfin : Tendsto (fun N : ℕ => (∑' k, f k) - ∑ k ∈ Work.Diff.STE.Flat.box n N, f k) atTop
        (nhds ((∑' k, f k) - (∑' k, f k))) :=
      (tendsto_const_nhds (x := ∑' k, f k)).sub hN
    simpa using hfin
  · -- Non-summable case: every tail is non-summable, hence definitionally `0`.
    have hzero : ∀ N, (∑' k : {k : Fin n → ℤ // k ∉ Work.Diff.STE.Flat.box n N}, f k.1) = 0 := by
      intro N
      rw [tsum_eq_zero_of_not_summable]
      intro h
      exact hf ((Finset.summable_compl_iff (s := Work.Diff.STE.Flat.box n N) (f := f)).mp h)
    simp only [hzero]
    exact tendsto_const_nhds

end Work.Diff.STE.flat
