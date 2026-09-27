import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.PL.Shell.Basic
import Submission.Work.PL.Shell.sd_iter_prelim
import Submission.Work.PL.Shell.flagEnum_mem
import Submission.Work.PL.Shell.exists_min_vertex_decomp
import Submission.Work.PL.Shell.eq_bary_of_min_weight
import Submission.Work.PL.Shell.perm_append_of_perm_erase

/-!
# The barycentric subdivision of a simplex covers it (flag-enumeration form)

`Work.PL.Shell.sd_iter_covering_flagEnum`: the union of the subdivision simplices
`PL.simp ((prefixes l).image bary)`, over the flags `l` enumerated by `Work.PL.Shell.flagEnum vs`
for `vs` a duplicate-free listing of `Δ`, is `PL.simp Δ`.

This is the covering half of the general `r = 1` shelling statement, in the form needed by
`Work.PL.Sd1.Shell1`.  The proof is self-contained (it does not import
`Submission.Work.PL.Shell.cover_bary`, which declares some of the same names as
`Submission.Work.PL.Shell.face_trace`).
-/

open Set Metric Finset
open scoped BigOperators

namespace Work.PL.Shell

noncomputable section

variable {N : ℕ}

/-- A nonempty list is its own last prefix. -/
theorem sd_iter_top_mem_prefixes (l : List (PL.E N)) (hl : l ≠ []) :
    l.toFinset ∈ prefixes l := by
  have hpos : 0 < l.length := by
    cases l with
    | nil => exact absurd rfl hl
    | cons a t => simp
  simp only [prefixes, Finset.mem_image, Finset.mem_range]
  refine ⟨l.length - 1, by omega, ?_⟩
  simp only [prefAt]
  rw [Nat.sub_add_cancel (by omega), List.take_length]

/-- Appending an element to a list only adds prefix sets. -/
theorem sd_iter_prefixes_append_subset (l : List (PL.E N)) (v : PL.E N) :
    prefixes l ⊆ prefixes (l ++ [v]) := by
  intro A hA
  obtain ⟨k, hk, rfl⟩ := sd_iter_mem_prefixes_iff.mp hA
  simp only [prefixes, Finset.mem_image, Finset.mem_range]
  refine ⟨k, by simpa using Nat.lt_succ_of_lt hk, ?_⟩
  simp only [prefAt]
  rw [List.take_append_of_le_length (Nat.succ_le_of_lt hk)]

/-- The subdivision simplex of a flag of `σ` is contained in `simp σ`. -/
theorem sd_iter_simp_prefixes_subset {σ : Finset (PL.E N)} {l : List (PL.E N)}
    (hl : l.Perm σ.toList) : PL.simp ((prefixes l).image bary) ⊆ PL.simp σ := by
  have hto : l.toFinset = σ := by
    rw [List.toFinset_eq_of_perm _ _ hl, Finset.toList_toFinset]
  rw [PL.simp, PL.simp]
  refine convexHull_min ?_ (convex_convexHull ℝ _)
  intro z hz
  rw [Finset.mem_coe] at hz
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hz
  exact convexHull_mono (fun x hx => by
      have h := sd_iter_prefixes_subset_toFinset hS hx
      rwa [hto] at h) (sd_iter_bary_mem_simp (sd_iter_prefixes_nonempty hS))

/-- Every point of `PL.simp τ` lies in the subdivision simplex of some flag of `τ`. -/
theorem sd_iter_exists_perm_cover (τ : Finset (PL.E N)) (x : PL.E N) (hx : x ∈ PL.simp τ) :
    ∃ l : List (PL.E N), l.Perm τ.toList ∧ x ∈ PL.simp ((prefixes l).image bary) := by
  classical
  suffices H : ∀ k, ∀ τ : Finset (PL.E N), τ.card = k → ∀ x : PL.E N, x ∈ PL.simp τ →
      ∃ l : List (PL.E N), l.Perm τ.toList ∧ x ∈ PL.simp ((prefixes l).image bary) by
    exact H τ.card τ rfl x hx
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro τ hcard x hx
    rcases Finset.eq_empty_or_nonempty τ with hτ | hτ
    · rw [hτ, PL.simp] at hx
      simp at hx
    · obtain ⟨w, hw0, hw1, hwx⟩ := Finset.mem_convexHull.mp hx
      have hxw : x = ∑ y ∈ τ, w y • y := by
        rw [← hwx, Finset.centerMass_eq_of_sum_1 _ _ hw1]
        simp
      obtain ⟨v, hvτ, hvmin⟩ := Finset.exists_min_image τ w hτ
      have ht_le : (τ.card : ℝ) * w v ≤ 1 := by
        have hle : ∑ _y ∈ τ, w v ≤ ∑ y ∈ τ, w y := Finset.sum_le_sum (fun y hy => hvmin y hy)
        rw [Finset.sum_const, hw1, nsmul_eq_mul] at hle
        exact hle
      have ht_nonneg : 0 ≤ (τ.card : ℝ) * w v :=
        mul_nonneg (Nat.cast_nonneg τ.card) (hw0 v hvτ)
      by_cases ht1 : (τ.card : ℝ) * w v = 1
      · have hb : x = bary τ := eq_bary_of_min_weight hvτ hw0 hvmin hw1 hxw ht1
        rw [hb]
        refine ⟨τ.toList, List.Perm.refl _, ?_⟩
        rw [PL.simp]
        refine subset_convexHull ℝ _ ?_
        rw [Finset.mem_coe]
        refine Finset.mem_image.mpr ⟨τ, ?_, rfl⟩
        have hne : τ.toList ≠ [] := by
          simpa [Finset.toList_eq_nil] using (Finset.nonempty_iff_ne_empty.mp hτ)
        have h := sd_iter_top_mem_prefixes τ.toList hne
        rwa [Finset.toList_toFinset] at h
      · have ht_lt : (τ.card : ℝ) * w v < 1 := lt_of_le_of_ne ht_le ht1
        obtain ⟨z, hz_conv, hzx⟩ :=
          exists_min_vertex_decomp (τ := τ) (v := v) (x := x) hvτ hw0 hvmin hw1 hxw ht_lt
        have hcard_lt : (τ.erase v).card < k := by
          have h1 : 0 < τ.card := Finset.card_pos.mpr ⟨v, hvτ⟩
          have h2 := Finset.card_erase_of_mem hvτ
          omega
        obtain ⟨l', hl'perm, hl'z⟩ := ih (τ.erase v).card hcard_lt (τ.erase v) rfl z hz_conv
        have hperm : (l' ++ [v]).Perm τ.toList :=
          perm_append_of_perm_erase (τ := τ) (v := v) hvτ hl'perm
        refine ⟨l' ++ [v], hperm, ?_⟩
        have hto' : (l' ++ [v]).toFinset = τ := by
          rw [List.toFinset_eq_of_perm _ _ hperm, Finset.toList_toFinset]
        have htop : τ ∈ prefixes (l' ++ [v]) := by
          rw [← hto']
          exact sd_iter_top_mem_prefixes (l' ++ [v]) (by simp)
        have hb_mem : bary τ ∈ PL.simp ((prefixes (l' ++ [v])).image bary) := by
          rw [PL.simp]
          refine subset_convexHull ℝ _ ?_
          rw [Finset.mem_coe]
          exact Finset.mem_image.mpr ⟨τ, htop, rfl⟩
        have hz_mem : z ∈ PL.simp ((prefixes (l' ++ [v])).image bary) :=
          convexHull_mono (Finset.image_subset_image (sd_iter_prefixes_append_subset l' v)) hl'z
        have hpair : x ∈ (convexHull ℝ) ({(bary τ), z} : Set (PL.E N)) := by
          rw [convexHull_pair]
          exact ⟨(τ.card : ℝ) * w v, 1 - (τ.card : ℝ) * w v, ht_nonneg, by linarith,
            by ring, hzx.symm⟩
        rw [PL.simp]
        exact convexHull_min (by intro u hu; rcases hu with rfl | rfl; exact hb_mem; exact hz_mem)
          (convex_convexHull ℝ _) hpair

/-- **The barycentric subdivision of a simplex covers it** (permutation form). -/
theorem sd_iter_cover_bary {σ : Finset (PL.E N)}
    (hσ : AffineIndependent ℝ ((↑) : σ → PL.E N)) :
    (⋃ l ∈ σ.toList.permutations.toFinset, PL.simp ((prefixes l).image bary)) = PL.simp σ := by
  apply Set.Subset.antisymm
  · rintro x hx
    rw [Set.mem_iUnion₂] at hx
    obtain ⟨l, hl, hxl⟩ := hx
    exact sd_iter_simp_prefixes_subset (List.mem_permutations.mp (List.mem_toFinset.mp hl)) hxl
  · rintro x hx
    obtain ⟨l, hlperm, hxl⟩ := sd_iter_exists_perm_cover σ x hx
    rw [Set.mem_iUnion₂]
    exact ⟨l, List.mem_toFinset.mpr (List.mem_permutations.mpr hlperm), hxl⟩

/-- **The barycentric subdivision of a simplex covers it**, with the flags indexed by
`flagEnum vs` for an enumeration `vs` of `Δ`. -/
theorem sd_iter_covering_flagEnum {Δ : Finset (PL.E N)}
    (hΔ : AffineIndependent ℝ ((↑) : Δ → PL.E N)) (vs : List (PL.E N))
    (hvs : vs.toFinset = Δ) (hvs' : vs.Nodup) :
    (⋃ l ∈ (flagEnum vs).toFinset, PL.simp ((prefixes l).image bary)) = PL.simp Δ := by
  have hperm : vs.Perm Δ.toList :=
    List.perm_of_nodup_nodup_toFinset_eq hvs' (Finset.nodup_toList Δ)
      (by rw [hvs, Finset.toList_toFinset])
  rw [← sd_iter_cover_bary hΔ]
  apply Set.Subset.antisymm
  · rintro x hx
    rw [Set.mem_iUnion₂] at hx ⊢
    obtain ⟨l, hl, hxl⟩ := hx
    have hlperm : l.Perm vs := flagEnum_mem.mp (List.mem_toFinset.mp hl)
    exact ⟨l, List.mem_toFinset.mpr (List.mem_permutations.mpr (hlperm.trans hperm)), hxl⟩
  · rintro x hx
    rw [Set.mem_iUnion₂] at hx ⊢
    obtain ⟨l, hl, hxl⟩ := hx
    have hlperm : l.Perm Δ.toList := List.mem_permutations.mp (List.mem_toFinset.mp hl)
    exact ⟨l, List.mem_toFinset.mpr (flagEnum_mem.mpr (hlperm.trans hperm.symm)), hxl⟩

end

end Work.PL.Shell
