import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.PL.Shell.Basic
import Submission.Work.PL.Shell.exists_min_vertex_decomp
import Submission.Work.PL.Shell.eq_bary_of_min_weight
import Submission.Work.PL.Shell.perm_append_of_perm_erase

/-!
# The barycentric subdivision of a simplex covers it (A4 `PL/Shell`)

`Work.PL.Shell.cover_bary`: the union of the top-dimensional simplices of the barycentric
subdivision of the simplex `simp σ` is `simp σ` again.  The subdivision simplices are the
`PL.simp ((prefixes l).image bary)` for `l` running over the flags of `σ` (the permutations
of `σ.toList`), where `prefixes l` is the chain of prefix sets of `l` and `bary` is the
centroid.

The two inclusions are proved separately:

* `simp_prefixes_subset`: each subdivision simplex is contained in `simp σ`, since each of
  its vertices `bary S` is a convex combination of the points of `S ⊆ σ` (`bary_mem_simp`)
  and `simp σ` is convex.
* `exists_perm_cover`: conversely every `x ∈ simp σ` lies in one of them.  Writing `x` as a
  convex combination `x = ∑ w y • y` of the points of `σ` (`Finset.mem_convexHull`) and
  choosing a vertex `v` of minimal weight `w v`, either `x` is the centroid
  (`eq_bary_of_min_weight`, and then any flag works), or `x` splits as an explicit convex
  combination of `bary σ` and of a point `z` of the smaller simplex `simp (σ.erase v)`
  (`exists_min_vertex_decomp`), to which the induction hypothesis applies.  Appending `v`
  to the flag of `σ.erase v` (`perm_append_of_perm_erase`) gives the required flag, and
  `bary σ ∈ simp ((prefixes (l ++ [v])).image bary)` because the full set `σ` is the top
  prefix of `l ++ [v]`.

No use is made of affine independence of `σ`.
-/

open Set Metric Finset
open scoped BigOperators

namespace Work.PL.Shell

/-! ### Elementary properties of the prefix chain `prefixes` -/

/-- Membership in `prefixes l`: the prefix sets are the `prefAt l k`, `k < l.length`. -/
theorem mem_prefixes_iff {N : ℕ} {A : Finset (PL.E N)} {l : List (PL.E N)} :
    A ∈ prefixes l ↔ ∃ k < l.length, prefAt l k = A := by
  simp [prefixes, Finset.mem_image, Finset.mem_range, eq_comm]

/-- Every prefix set of a list consists of elements of that list. -/
theorem prefixes_subset_toFinset {N : ℕ} {A : Finset (PL.E N)} {l : List (PL.E N)}
    (hA : A ∈ prefixes l) : A ⊆ l.toFinset := by
  obtain ⟨k, _, rfl⟩ := mem_prefixes_iff.mp hA
  exact fun x hx => by
    simp only [prefAt, List.mem_toFinset] at hx ⊢
    exact List.Sublist.subset (List.take_sublist (k+1) l) hx

/-- Every prefix set of a list is nonempty. -/
theorem prefixes_nonempty {N : ℕ} {A : Finset (PL.E N)} {l : List (PL.E N)}
    (hA : A ∈ prefixes l) : A.Nonempty := by
  obtain ⟨k, hk, hAk⟩ := mem_prefixes_iff.mp hA
  have hne : l.take (k+1) ≠ [] := by
    intro h
    have hlen := congrArg List.length h
    rw [List.length_take, min_eq_left (Nat.succ_le_of_lt hk), List.length_nil] at hlen
    exact Nat.succ_ne_zero k hlen
  rw [← hAk, prefAt, Finset.nonempty_iff_ne_empty]
  simpa [List.toFinset_eq_empty_iff] using hne

/-- The whole list is its last prefix set. -/
theorem top_mem_prefixes {N : ℕ} (l : List (PL.E N)) (hl : l ≠ []) : l.toFinset ∈ prefixes l := by
  have hpos : 0 < l.length := by cases l with
    | nil => exact absurd rfl hl
    | cons a t => simp
  simp only [prefixes, Finset.mem_image, Finset.mem_range]
  refine ⟨l.length - 1, by omega, ?_⟩
  simp only [prefAt]
  rw [Nat.sub_add_cancel (by omega), List.take_length]

/-- Appending an element to a list only adds prefix sets. -/
theorem prefixes_append_subset {N : ℕ} (l : List (PL.E N)) (v : PL.E N) :
    prefixes l ⊆ prefixes (l ++ [v]) := by
  intro A hA
  obtain ⟨k, hk, rfl⟩ := mem_prefixes_iff.mp hA
  simp only [prefixes, Finset.mem_image, Finset.mem_range]
  refine ⟨k, by simpa using Nat.lt_succ_of_lt hk, ?_⟩
  simp only [prefAt]
  rw [List.take_append_of_le_length (Nat.succ_le_of_lt hk)]

/-! ### The subdivision simplices lie in the simplex -/

/-- The centroid of a nonempty `S ⊆ σ` is a point of the simplex on `σ`. -/
theorem bary_mem_simp {N : ℕ} {S σ : Finset (PL.E N)} (hS : S.Nonempty) (h : S ⊆ σ) :
    bary S ∈ PL.simp σ := by
  have hcard : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.card_ne_zero
  have hsum : ∑ y ∈ S, (S.card : ℝ)⁻¹ = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_inv_cancel₀ hcard
  have hcm : S.centerMass (fun _ => (S.card : ℝ)⁻¹) id = bary S := by
    rw [Finset.centerMass_eq_of_sum_1 _ _ hsum, bary]
    simp only [id_eq]
    rw [Finset.smul_sum]
  have hmem : bary S ∈ (convexHull ℝ) ((S : Finset (PL.E N)) : Set (PL.E N)) := by
    rw [Finset.mem_convexHull]
    exact ⟨fun _ => (S.card : ℝ)⁻¹, fun y hy => inv_nonneg.mpr (Nat.cast_nonneg _), hsum, hcm⟩
  rw [PL.simp]
  exact convexHull_mono (fun x hx => h hx) hmem

/-- Every subdivision simplex of a flag `l` of `σ` is contained in `simp σ`. -/
theorem simp_prefixes_subset {N : ℕ} {σ : Finset (PL.E N)} {l : List (PL.E N)}
    (hl : l.Perm σ.toList) : PL.simp ((prefixes l).image bary) ⊆ PL.simp σ := by
  have hto : l.toFinset = σ := by
    rw [List.toFinset_eq_of_perm _ _ hl, Finset.toList_toFinset]
  rw [PL.simp, PL.simp]
  refine convexHull_min ?_ (convex_convexHull ℝ _)
  intro z hz
  rw [Finset.mem_coe] at hz
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hz
  exact bary_mem_simp (prefixes_nonempty hS) (fun x hx => by
    have h := prefixes_subset_toFinset hS hx
    rwa [hto] at h)

/-! ### The subdivision simplices cover the simplex -/

/-- Every point of `simp τ` lies in the subdivision simplex of some flag of `τ`. -/
theorem exists_perm_cover {N : ℕ} (τ : Finset (PL.E N)) (x : PL.E N) (hx : x ∈ PL.simp τ) :
    ∃ l : List (PL.E N), l.Perm τ.toList ∧ x ∈ PL.simp ((prefixes l).image bary) := by
  classical
  suffices H : ∀ k, ∀ τ : Finset (PL.E N), τ.card = k → ∀ x, x ∈ PL.simp τ →
      ∃ l, l.Perm τ.toList ∧ x ∈ PL.simp ((prefixes l).image bary) by
    exact H τ.card τ rfl x hx
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro τ hcard x hx
    rcases Finset.eq_empty_or_nonempty τ with hτ | hτ
    · rw [hτ, PL.simp] at hx
      simp at hx
    · -- `x` is a convex combination of the points of `τ`
      obtain ⟨w, hw0, hw1, hwx⟩ := Finset.mem_convexHull.mp hx
      have hxw : x = ∑ y ∈ τ, w y • y := by
        rw [← hwx, Finset.centerMass_eq_of_sum_1 _ _ hw1]
        simp
      -- a vertex `v` of minimal weight
      obtain ⟨v, hvτ, hvmin⟩ := Finset.exists_min_image τ w hτ
      have ht_le : (τ.card : ℝ) * w v ≤ 1 := by
        have hle : ∑ _y ∈ τ, w v ≤ ∑ y ∈ τ, w y := Finset.sum_le_sum (fun y hy => hvmin y hy)
        rw [Finset.sum_const, hw1, nsmul_eq_mul] at hle
        exact hle
      have ht_nonneg : 0 ≤ (τ.card : ℝ) * w v :=
        mul_nonneg (Nat.cast_nonneg τ.card) (hw0 v hvτ)
      by_cases ht1 : (τ.card : ℝ) * w v = 1
      · -- all weights are equal: `x` is the centroid, so any flag works
        have hb : x = bary τ := eq_bary_of_min_weight hvτ hw0 hvmin hw1 hxw ht1
        rw [hb]
        refine ⟨τ.toList, List.Perm.refl _, ?_⟩
        rw [PL.simp]
        refine subset_convexHull ℝ _ ?_
        rw [Finset.mem_coe]
        refine Finset.mem_image.mpr ⟨τ, ?_, rfl⟩
        have hne : τ.toList ≠ [] := by
          simpa [Finset.toList_eq_nil] using (Finset.nonempty_iff_ne_empty.mp hτ)
        have h := top_mem_prefixes τ.toList hne
        rwa [Finset.toList_toFinset] at h
      · -- otherwise `x` splits off the minimal vertex `v`
        have ht_lt : (τ.card : ℝ) * w v < 1 := lt_of_le_of_ne ht_le ht1
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
          exact top_mem_prefixes (l' ++ [v]) (by simp)
        have hb_mem : bary τ ∈ PL.simp ((prefixes (l' ++ [v])).image bary) := by
          rw [PL.simp]
          refine subset_convexHull ℝ _ ?_
          rw [Finset.mem_coe]
          exact Finset.mem_image.mpr ⟨τ, htop, rfl⟩
        have hz_mem : z ∈ PL.simp ((prefixes (l' ++ [v])).image bary) :=
          convexHull_mono (Finset.image_subset_image (prefixes_append_subset l' v)) hl'z
        have hpair : x ∈ (convexHull ℝ) ({(bary τ), z} : Set (PL.E N)) := by
          rw [convexHull_pair]
          exact ⟨(τ.card : ℝ) * w v, 1 - (τ.card : ℝ) * w v, ht_nonneg, by linarith,
            by ring, hzx.symm⟩
        rw [PL.simp]
        exact convexHull_min (by intro u hu; rcases hu with rfl | rfl; exact hb_mem; exact hz_mem)
          (convex_convexHull ℝ _) hpair

/-- **The barycentric subdivision of a simplex covers it**: the union, over the flags `l`
of `σ` (the permutations of `σ.toList`), of the subdivision simplices
`PL.simp ((prefixes l).image bary)`, is `PL.simp σ`. -/
theorem cover_bary {N : ℕ} {σ : Finset (PL.E N)}
    (hσ : AffineIndependent ℝ ((↑) : σ → PL.E N)) :
    (⋃ l ∈ σ.toList.permutations.toFinset,
        PL.simp ((Work.PL.Shell.prefixes l).image Work.PL.Shell.bary)) = PL.simp σ := by
  apply Set.Subset.antisymm
  · rintro x hx
    rw [Set.mem_iUnion₂] at hx
    obtain ⟨l, hl, hxl⟩ := hx
    exact simp_prefixes_subset (List.mem_permutations.mp (List.mem_toFinset.mp hl)) hxl
  · rintro x hx
    obtain ⟨l, hlperm, hxl⟩ := exists_perm_cover σ x hx
    rw [Set.mem_iUnion₂]
    exact ⟨l, List.mem_toFinset.mpr (List.mem_permutations.mpr hlperm), hxl⟩

end Work.PL.Shell
