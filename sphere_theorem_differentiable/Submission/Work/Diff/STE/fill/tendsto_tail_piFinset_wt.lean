import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.summable_wt_zpow

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The tail of the weight `⟨k⟩^{-2s}` outside a box vanishes

For a finite index type `ι` and `s` with `card ι < 2 s`, the weight family
`k ↦ ⟨k⟩^{-2s} = (Work.Diff.STE.wt k ^ s)⁻¹` is summable on `ℤ^ι`
(`Work.Diff.STE.summable_wt_zpow`), hence its sum over the complement of the box
`[-N,N]^ι` tends to `0` as `N → ∞`.

The proof is the standard one: the finite sums over the boxes exhaust the full `tsum`
(the boxes `piFinset (i ↦ Icc (-N) N)` are cofinal among finite subsets, since every
finite set of lattice vectors has bounded `ℓ¹`-norm), and the tail over the complement
is the difference between the full sum and the sum over the box.
-/

noncomputable section

namespace Work.Diff.STE.fill

open Filter
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The frequency box `[-N,N]^ι` of the lattice `ℤ^ι`. -/
def box (ι : Type*) [Fintype ι] [DecidableEq ι] (N : ℕ) : Finset (ι → ℤ) :=
  Fintype.piFinset (fun _ : ι => Finset.Icc (-(N : ℤ)) (N : ℤ))

/-- A lattice point whose `ℓ¹`-norm is at most `N` lies in the box `[-N,N]^ι`. -/
lemma mem_box_of_bd_le {k : ι → ℤ} {N : ℕ} (h : (∑ i, (k i).natAbs) ≤ N) :
    k ∈ box ι N := by
  simp only [box, Fintype.mem_piFinset, Finset.mem_Icc]
  intro i
  have hi : (k i).natAbs ≤ N :=
    le_trans (Finset.single_le_sum (f := fun j : ι => (k j).natAbs)
      (fun j _ => Nat.zero_le _) (Finset.mem_univ i)) h
  have h1 : -(((k i).natAbs : ℕ) : ℤ) ≤ k i := by
    have := Int.le_natAbs (a := -k i)
    simpa [Int.natAbs_neg] using neg_le_neg this
  have h2 : k i ≤ (((k i).natAbs : ℕ) : ℤ) := Int.le_natAbs
  have h3 : (((k i).natAbs : ℕ) : ℤ) ≤ (N : ℤ) := by exact_mod_cast hi
  omega

/-- The boxes `[-N,N]^ι` are cofinal among the finite subsets of `ℤ^ι`: every finite set of
lattice vectors is contained in `box ι N` for `N` large. -/
lemma tendsto_box_atTop : Tendsto (fun N : ℕ => box ι N) atTop atTop := by
  rw [Filter.tendsto_atTop]
  intro s
  rw [Filter.eventually_atTop]
  refine ⟨s.sup (fun k : ι → ℤ => ∑ i, (k i).natAbs), fun N hN k hk => ?_⟩
  exact mem_box_of_bd_le
    (le_trans (Finset.le_sup (f := fun k : ι → ℤ => ∑ i, (k i).natAbs) hk) hN)

theorem tendsto_tail_piFinset_wt {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ℕ)
    (hs : Fintype.card ι < 2 * s) :
    Filter.Tendsto
      (fun N : ℕ => ∑' k : {k : ι → ℤ // k ∉ Fintype.piFinset (fun _ : ι => Finset.Icc (-(N : ℤ)) (N : ℤ))},
        ((Work.Diff.STE.wt k.1) ^ s)⁻¹)
      Filter.atTop (nhds 0) := by
  classical
  let f : (ι → ℤ) → ℝ := fun k => ((Work.Diff.STE.wt k) ^ s)⁻¹
  have hsumm : Summable f := by
    refine (Work.Diff.STE.summable_wt_zpow (ι := ι) s hs).congr (fun k => ?_)
    rw [zpow_neg, zpow_natCast]
  have hsum : Tendsto (fun t : Finset (ι → ℤ) => ∑ k ∈ t, f k)
      atTop (nhds (∑' k, f k)) := hsumm.hasSum
  have hN : Tendsto (fun N : ℕ => ∑ k ∈ box ι N, f k)
      atTop (nhds (∑' k, f k)) := hsum.comp tendsto_box_atTop
  have heq : ∀ (N : ℕ),
      (∑' k : {k : ι → ℤ // k ∉ Fintype.piFinset (fun _ : ι => Finset.Icc (-(N : ℤ)) (N : ℤ))},
        f k.1) = (∑' k, f k) - ∑ k ∈ box ι N, f k := by
    intro N
    have h := hsumm.sum_add_tsum_compl (s := box ι N)
    rw [eq_sub_iff_add_eq, add_comm]
    exact h
  have hlim : Tendsto (fun N : ℕ => (∑' k, f k) - ∑ k ∈ box ι N, f k) atTop
      (nhds ((∑' k, f k) - (∑' k, f k))) :=
    tendsto_const_nhds.sub hN
  show Filter.Tendsto
      (fun N : ℕ => ∑' k : {k : ι → ℤ // k ∉ Fintype.piFinset (fun _ : ι => Finset.Icc (-(N : ℤ)) (N : ℤ))},
        f k.1) Filter.atTop (nhds 0)
  simp only [heq]
  simpa using hlim

end Work.Diff.STE.fill
