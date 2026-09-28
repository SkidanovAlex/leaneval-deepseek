import Mathlib
import Submission.Work.Q44Geom.Basic
import Submission.Work.HP.Q44Child.basis_ext
import Submission.Work.HP.Q44Child.superlattice_basis

/-!
# Auxiliaries for `Work.Q44Geom.bad_fiber_count`

Two self-contained tools, copied into namespace `Work.Q44Geom.BF` so that the fiber count does
not have to depend on the (concurrently edited) module `Work.Q44Geom.BadDefs`:

* `BF.gen_of_le` : a rank-`3` lattice `L` containing a saturated rank-`2` lattice `N` is
  generated over `N` by a single vector, `L = N + ℤ z`;
* `BF.ncard_mul_le_of_disjoint` : counting over a disjoint family of subsets of a finite set.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.Q44Geom.BF

open MvPolynomial

/-! ## A generator of `L` over a primitive rank-`2` sublattice -/

/-- If `N ≤ L` are sublattices of `ℤ^5` with `N` saturated of rank `2` and `L` of rank `3`,
then `L = N + ℤ z` for a single vector `z ∈ L`. -/
theorem gen_of_le (N L : Submodule ℤ (Fin 5 → ℤ)) (hNL : N ≤ L) (hN : Work.HP.IsPrimLat N)
    (hrkN : Work.HP.rk N = 2) (hrkL : Work.HP.rk L = 3) :
    ∃ z : Fin 5 → ℤ, z ∈ L ∧ ∀ w ∈ L, ∃ k : ℤ, ∃ n ∈ N, w = k • z + n := by
  classical
  obtain ⟨b, hb, -, -⟩ := Work.HP.Q44Child.basis_ext N hrkN hN
  have hbase : Work.HP.Q44Child.baseLam b ≤ L := by
    rw [Work.HP.Q44Child.baseLam, ← hb]
    exact hNL
  obtain ⟨v, hvL, hLv⟩ := Work.HP.Q44Child.superlattice_basis b L hbase hrkL
  refine ⟨v, hvL, ?_⟩
  intro w hw
  rw [hLv] at hw
  set A : Fin 5 → ℤ := b (Fin.castLE (by norm_num : 2 ≤ 5) (0 : Fin 2)) with hA
  set B : Fin 5 → ℤ := b (Fin.castLE (by norm_num : 2 ≤ 5) (1 : Fin 2)) with hB
  have hA_mem : A ∈ N := by
    rw [hb]
    exact Submodule.subset_span ⟨(0 : Fin 2), rfl⟩
  have hB_mem : B ∈ N := by
    rw [hb]
    exact Submodule.subset_span ⟨(1 : Fin 2), rfl⟩
  have hsup : Submodule.span ℤ ({A, B, v} : Set (Fin 5 → ℤ)) ≤ N ⊔ Submodule.span ℤ {v} := by
    rw [Submodule.span_le]
    rintro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx | hx
    · rw [hx]; exact Submodule.mem_sup_left hA_mem
    · rw [hx]; exact Submodule.mem_sup_left hB_mem
    · rw [hx]
      exact Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton_iff.mpr rfl))
  obtain ⟨n, hn, u, hu, hnu⟩ := Submodule.mem_sup.mp (hsup hw)
  rw [Submodule.mem_span_singleton] at hu
  obtain ⟨k, rfl⟩ := hu
  exact ⟨k, n, hn, by rw [← hnu]; abel⟩

/-! ## Counting over a disjoint family of subsets -/

/-- If `(t i)_{i ∈ s}` is a family of nonempty pairwise disjoint subsets of a finite set `S`,
each with at least `k` elements, then `#s * k ≤ #S`. -/
theorem ncard_mul_le_of_disjoint {ι α : Type*} (s : Set ι) (t : ι → Set α) (S : Set α) (k : ℝ)
    (hS : S.Finite) (hne : ∀ i ∈ s, (t i).Nonempty) (hsub : ∀ i ∈ s, t i ⊆ S)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (t i) (t j))
    (hk : ∀ i ∈ s, k ≤ ((t i).ncard : ℝ)) :
    (s.ncard : ℝ) * k ≤ (S.ncard : ℝ) := by
  classical
  haveI hSft : Fintype S := hS.fintype
  have hsf : s.Finite := by
    choose g hg using hne
    have hinj : Function.Injective (fun i : s => (⟨g i.1 i.2, hsub i.1 i.2 (hg i.1 i.2)⟩ : S)) := by
      intro i j hij
      have h2 : g i.1 i.2 = g j.1 j.2 := congrArg Subtype.val hij
      by_contra hne'
      have hne2 : i.1 ≠ j.1 := fun h => hne' (Subtype.ext h)
      have hd := Set.disjoint_left.mp (hdisj i.1 i.2 j.1 j.2 hne2)
      exact hd (hg i.1 i.2) (h2 ▸ hg j.1 j.2)
    haveI : Fintype s := Fintype.ofInjective _ hinj
    exact Set.toFinite s
  have hpd : s.PairwiseDisjoint t := fun i hi j hj hij => hdisj i hi j hj hij
  have hEq : (⋃ i ∈ s, t i).ncard = ∑ i ∈ hsf.toFinset, (t i).ncard := by
    rw [hsf.ncard_biUnion (fun i hi => hS.subset (hsub i hi)) hpd,
      finsum_mem_eq_finite_toFinset_sum _ hsf]
  have hle : (⋃ i ∈ s, t i).ncard ≤ S.ncard := by
    refine Set.ncard_le_ncard ?_ hS
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨i, hi, hxi⟩ := hx
    exact hsub i hi hxi
  have hsum : (∑ i ∈ hsf.toFinset, (t i).ncard) ≤ S.ncard := by
    rw [← hEq]; exact hle
  have hmul : (hsf.toFinset.card : ℝ) * k ≤ ∑ i ∈ hsf.toFinset, ((t i).ncard : ℝ) := by
    calc (hsf.toFinset.card : ℝ) * k = ∑ _i ∈ hsf.toFinset, k := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ hsf.toFinset, ((t i).ncard : ℝ) :=
          Finset.sum_le_sum fun i hi => hk i (hsf.mem_toFinset.mp hi)
  have hcast : ((∑ i ∈ hsf.toFinset, (t i).ncard : ℕ) : ℝ)
      = ∑ i ∈ hsf.toFinset, ((t i).ncard : ℝ) := by
    push_cast
    rfl
  calc (s.ncard : ℝ) * k = (hsf.toFinset.card : ℝ) * k := by
        rw [Set.ncard_eq_toFinset_card s hsf]
    _ ≤ ∑ i ∈ hsf.toFinset, ((t i).ncard : ℝ) := hmul
    _ = ((∑ i ∈ hsf.toFinset, (t i).ncard : ℕ) : ℝ) := hcast.symm
    _ ≤ (S.ncard : ℝ) := by exact_mod_cast hsum

end Work.Q44Geom.BF
