import Mathlib
import Submission.Work.EKLRelCross.Instances

/-!
# A cofinal sequence of open sets on `SL₃(ℝ)`

`SL₃(ℝ)` is second countable (`Work.EKLRelCross.instSecondCountableSL3`), so it has a countable
topological basis `b : ℕ → Set SL₃(ℝ)` (`TopologicalSpace.exists_seq_basis`).  Taking `W = b`
gives the "cofinal open cover" property used in the EKL argument: for every compact `K` and open
`U` with `K ⊆ U` there is a finite subfamily of `W` whose union lies between `K` and `U`.

Indeed, for each `x ∈ K` the basis property produces `n(x)` with `x ∈ b n(x) ⊆ U`; the family of
those `b n(x)` is an open cover of the compact set `K`, so finitely many of them already cover
`K`, and every one of them is contained in `U`.
-/

namespace Work.EKLCompLeaf

open Work.EKLContract

theorem cofinal_open_cover :
    ∃ W : ℕ → Set Work.EKLContract.SL3,
      (∀ n, IsOpen (W n)) ∧
      ∀ (K U : Set Work.EKLContract.SL3), IsCompact K → IsOpen U → K ⊆ U →
        ∃ s : Finset ℕ, K ⊆ (⋃ n ∈ s, W n) ∧ (⋃ n ∈ s, W n) ⊆ U := by
  obtain ⟨b, hb⟩ := TopologicalSpace.exists_seq_basis SL3
  refine ⟨b, fun n => hb.isOpen (Set.mem_range_self n), ?_⟩
  intro K U hK hU hKU
  -- The basis elements contained in `U` cover `K`.
  have hcover : K ⊆ ⋃ i : {n : ℕ // b n ⊆ U}, b i.1 := by
    intro x hx
    obtain ⟨v, hv, hxv, hvU⟩ := hb.exists_subset_of_mem_open (hKU hx) hU
    obtain ⟨n, rfl⟩ := hv
    exact Set.mem_iUnion.2 ⟨⟨n, hvU⟩, hxv⟩
  obtain ⟨t, ht⟩ :=
    hK.elim_finite_subcover (fun i : {n : ℕ // b n ⊆ U} => b i.1)
      (fun i => hb.isOpen (Set.mem_range_self i.1)) hcover
  refine ⟨t.image Subtype.val, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hit, hxi⟩ := by simpa only [Set.mem_iUnion] using ht hx
    simp only [Set.mem_iUnion]
    exact ⟨i.1, Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨i, hit, rfl⟩), hxi⟩
  · intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨n, hn, hxn⟩ := hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hn)
    exact i.2 hxn

end Work.EKLCompLeaf
