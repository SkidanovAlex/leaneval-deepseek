import Mathlib
import Submission.Work.Peluse.Basic

open scoped BigOperators

namespace Work.Peluse.PET

/-- Membership in the symmetric interval `[-N, N]` of integers is the condition `|x| ≤ N`. -/
lemma natAbs_le_iff_mem_symIcc {N : ℕ} {x : ℤ} :
    x ∈ Work.Peluse.symIcc N ↔ x.natAbs ≤ N := by
  rw [Work.Peluse.symIcc, Finset.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    have h : |x| ≤ (N : ℤ) := abs_le.mpr ⟨h1, h2⟩
    rw [← Int.natCast_natAbs] at h
    exact_mod_cast h
  · intro hx
    have h : (x.natAbs : ℤ) ≤ (N : ℤ) := by exact_mod_cast hx
    rw [Int.natCast_natAbs] at h
    exact abs_le.mp h

/-- Shifting the summation index in `∑_{x ∈ [-N,N]} ‖G (x + dy)‖` can only lose terms, when `G`
is supported in `[-N,N]`: the shifted index `x + dy` either stays in the interval (and then it
contributes the term `‖G (x + dy)‖` of the right-hand sum) or leaves it (and then `G` vanishes
there). -/
theorem sum_symIcc_shift_le {N : ℕ} {G : ℤ → ℂ} (hG : Work.Peluse.SupportIn G N) (d y : ℤ) :
    ∑ x ∈ Work.Peluse.symIcc N, ‖G (x + d * y)‖ ≤ ∑ z ∈ Work.Peluse.symIcc N, ‖G z‖ := by
  classical
  set c : ℤ := d * y with hc
  set t : Finset ℤ :=
    (Work.Peluse.symIcc N).filter (fun x => x + c ∈ Work.Peluse.symIcc N) with ht
  have ht_sub : t ⊆ Work.Peluse.symIcc N := Finset.filter_subset _ _
  -- terms with `x + c` outside the interval vanish
  have h1 : ∑ x ∈ Work.Peluse.symIcc N, ‖G (x + c)‖ = ∑ x ∈ t, ‖G (x + c)‖ := by
    refine (Finset.sum_subset ht_sub ?_).symm
    intro x hx hxt
    have hxnot : x + c ∉ Work.Peluse.symIcc N := fun h => hxt (Finset.mem_filter.mpr ⟨hx, h⟩)
    have hgt : N < (x + c).natAbs :=
      lt_of_not_ge fun h => hxnot (natAbs_le_iff_mem_symIcc.mpr h)
    rw [hG _ hgt, norm_zero]
  -- re-index by the injective shift
  have hinj : Set.InjOn (fun x : ℤ => x + c) (↑t : Set ℤ) := by
    intro x _ y _ h
    exact add_right_cancel h
  have h2 : ∑ x ∈ t, ‖G (x + c)‖ = ∑ z ∈ t.image (fun x => x + c), ‖G z‖ :=
    (Finset.sum_image (s := t) (g := fun x : ℤ => x + c) (f := fun z => ‖G z‖) hinj).symm
  have h2sub : t.image (fun x => x + c) ⊆ Work.Peluse.symIcc N := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact (Finset.mem_filter.mp hx).2
  have h3 : ∑ z ∈ t.image (fun x => x + c), ‖G z‖ ≤ ∑ z ∈ Work.Peluse.symIcc N, ‖G z‖ :=
    Finset.sum_le_sum_of_subset_of_nonneg h2sub (fun z _ _ => norm_nonneg _)
  calc ∑ x ∈ Work.Peluse.symIcc N, ‖G (x + d * y)‖
      = ∑ x ∈ Work.Peluse.symIcc N, ‖G (x + c)‖ := by rw [hc]
    _ = ∑ x ∈ t, ‖G (x + c)‖ := h1
    _ = ∑ z ∈ t.image (fun x => x + c), ‖G z‖ := h2
    _ ≤ ∑ z ∈ Work.Peluse.symIcc N, ‖G z‖ := h3

end Work.Peluse.PET
