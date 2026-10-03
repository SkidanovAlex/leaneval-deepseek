import Mathlib
import Submission.Work.ORReductions.SubgroupAlg
import Submission.Work.ORReductions.SubgroupAlg.subgroupAlgMap_injective
import Submission.Work.ORReductions.Coherent.AssembleSemiring
import Submission.Work.ORReductions.Coherent.assembleS_injective
import Submission.Work.ORReductions.Coherent.assembleS_surjective

set_option maxHeartbeats 2000000

namespace Work.ORReductions.Coherent

open MonoidAlgebra

variable {G : Type*} [Group G]

section Helpers

variable (H : Subgroup G) (K : Type*) [Semiring K]

private lemma assembleS_mapRange_mul_aux (c : (G ⧸ H) →₀ MonoidAlgebra K H) (y : MonoidAlgebra K H)
    (hf : (fun r : MonoidAlgebra K H => r * y) 0 = 0) :
    assembleS H K (c.mapRange (fun r => r * y) hf) =
      assembleS H K c * Work.ORReductions.subgroupAlgMap H K y := by
  classical
  rw [assembleS, assembleS, Finsupp.sum_mapRange_index]
  · rw [Finsupp.sum_mul]
    exact Finsupp.sum_congr fun x _ => by rw [map_mul, mul_assoc]
  · intro q
    simp

end Helpers

theorem ker_le_span_mapRange_alt {G : Type*} [Group G] (H : Subgroup G) (K : Type*) [Semiring K]
    {ι : Type*} {κ : Type*} (y : ι → MonoidAlgebra K H) (k : κ → (ι →₀ MonoidAlgebra K H))
    (hk : Submodule.span (MonoidAlgebra K H) (Set.range k) =
      LinearMap.ker (Finsupp.linearCombination (MonoidAlgebra K H) y)) :
    LinearMap.ker (Finsupp.linearCombination (MonoidAlgebra K G)
        (fun j => Work.ORReductions.subgroupAlgMap H K (y j))) ≤
      Submodule.span (MonoidAlgebra K G)
        (Set.range (fun l : κ => Finsupp.mapRange (Work.ORReductions.subgroupAlgMap H K)
          (map_zero _) (k l))) := by
  classical
  intro e he
  rw [LinearMap.mem_ker] at he
  -- Step 1: lift every `e j` through the assembly map.
  choose r hr using fun j : ι => assembleS_surjective H K (e j)
  have hr0 : ∀ j : ι, j ∉ e.support → r j = 0 := by
    intro j hj
    refine assembleS_injective H K (r j) ?_
    rw [hr j]
    exact Finsupp.notMem_support_iff.mp hj
  have hr0' : ∀ (q : G ⧸ H) (j : ι), j ∉ e.support → (r j) q = 0 := by
    intro q j hj
    rw [hr0 j hj]
    simp
  -- the finite set of cosets that can occur
  set Q : Finset (G ⧸ H) := e.support.biUnion (fun j => (r j).support) with hQ
  -- Step 2: the "difference" element `w` and its vanishing.
  set w : (G ⧸ H) →₀ MonoidAlgebra K H :=
    ∑ j ∈ e.support, (r j).mapRange (fun a => a * y j) (zero_mul (y j)) with hwdef
  have hw_apply : ∀ q : G ⧸ H, w q = ∑ j ∈ e.support, (r j) q * y j := by
    intro q
    rw [hwdef, Finsupp.finsetSum_apply]
    simp only [Finsupp.mapRange_apply]
  have hw : assembleS H K w = 0 := by
    have h1 : assembleS H K w =
        ∑ j ∈ e.support, e j * Work.ORReductions.subgroupAlgMap H K (y j) := by
      rw [hwdef, assembleS_finset_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [assembleS_mapRange_mul_aux, hr j]
    have h2 : ∑ j ∈ e.support, e j * Work.ORReductions.subgroupAlgMap H K (y j) = 0 := by
      have h3 : e.sum (fun i a => a • Work.ORReductions.subgroupAlgMap H K (y i)) = 0 := by
        rw [← Finsupp.linearCombination_apply]
        exact he
      simpa only [Finsupp.sum, smul_eq_mul] using h3
    rw [h1, h2]
  have hw0 : w = 0 := assembleS_injective H K w hw
  -- Step 3: the coset coordinates of `e` lie in the kernel over `K[H]`.
  let c : (G ⧸ H) → (ι →₀ MonoidAlgebra K H) := fun q =>
    Finsupp.onFinset e.support (fun j => (r j) q) (fun j hj => by
      by_contra hjs
      exact hj (hr0' q j hjs))
  have hcq : ∀ (q : G ⧸ H) (j : ι), (c q) j = (r j) q := by
    intro q j
    simp only [c, Finsupp.onFinset_apply]
  have hc : ∀ q : G ⧸ H,
      c q ∈ LinearMap.ker (Finsupp.linearCombination (MonoidAlgebra K H) y) := by
    intro q
    rw [LinearMap.mem_ker, Finsupp.linearCombination_apply]
    have hsub : (c q).support ⊆ e.support := by
      intro j hj
      by_contra hjs
      exact (Finsupp.mem_support_iff.mp hj) (by
        rw [hcq q j]
        exact hr0' q j hjs)
    have hsum : (c q).sum (fun i a => a • y i) = w q := by
      rw [Finsupp.sum, hw_apply q]
      trans ∑ a ∈ e.support, (c q) a • y a
      · exact Finset.sum_subset hsub fun a _ ha => by
          rw [Finsupp.notMem_support_iff.mp ha, zero_smul]
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [hcq q j, smul_eq_mul]
    rw [hsum, hw0]
    simp
  -- Step 4: represent each coordinate in terms of `k`.
  have hcoeff : ∀ q : G ⧸ H, ∃ a : κ →₀ MonoidAlgebra K H,
      a.sum (fun l b => b • k l) = c q := by
    intro q
    rw [← Finsupp.mem_span_range_iff_exists_finsupp]
    rw [hk]
    exact hc q
  choose a ha using hcoeff
  -- the finite set of `k`-indices that can occur
  set L : Finset κ := Q.biUnion (fun q => (a q).support) with hL
  let sval : κ → MonoidAlgebra K G := fun l =>
    ∑ q ∈ Q, MonoidAlgebra.single (Quotient.out q) (1 : K) *
      Work.ORReductions.subgroupAlgMap H K (a q l)
  -- Step 5: assemble the representation of `e`.
  have hRHS : ∀ j : ι, (∑ l ∈ L, sval l • Finsupp.mapRange
        (Work.ORReductions.subgroupAlgMap H K)
        (map_zero (Work.ORReductions.subgroupAlgMap H K)) (k l)) j
      = ∑ l ∈ L, sval l * Work.ORReductions.subgroupAlgMap H K ((k l) j) := by
    intro j
    rw [Finsupp.finsetSum_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]
  have key : ∀ j : ι, e j = ∑ l ∈ L, sval l *
      Work.ORReductions.subgroupAlgMap H K ((k l) j) := by
    intro j
    have hE : e j = ∑ q ∈ Q, MonoidAlgebra.single (Quotient.out q) (1 : K) *
        Work.ORReductions.subgroupAlgMap H K ((r j) q) := by
      have hsub : (r j).support ⊆ Q := by
        by_cases hj : j ∈ e.support
        · exact Finset.subset_biUnion_of_mem (fun j => (r j).support) hj
        · rw [hr0 j hj]
          simp
      rw [← hr j, assembleS, Finsupp.sum]
      exact Finsupp.sum_of_support_subset (r j) hsub
        (fun x r' => MonoidAlgebra.single (Quotient.out x) (1 : K) *
          Work.ORReductions.subgroupAlgMap H K r') (fun x _ => by simp)
    have hφ : ∀ q : G ⧸ H, q ∈ Q → Work.ORReductions.subgroupAlgMap H K ((r j) q) =
        ∑ l ∈ L, Work.ORReductions.subgroupAlgMap H K (a q l) *
          Work.ORReductions.subgroupAlgMap H K ((k l) j) := by
      intro q hq
      have hsubL : (a q).support ⊆ L := by
        rw [hL]
        exact Finset.subset_biUnion_of_mem (fun q' => (a q').support) hq
      have h1 : (r j) q = ∑ l ∈ L, a q l * (k l) j := by
        have h2 : (c q) j = ∑ l ∈ (a q).support, (a q) l * (k l) j := by
          rw [← ha q, Finsupp.sum, Finsupp.finsetSum_apply]
          exact Finset.sum_congr rfl fun l _ => by rw [Finsupp.smul_apply, smul_eq_mul]
        rw [← hcq q j, h2]
        exact Finset.sum_subset hsubL fun l _ hl => by
          rw [Finsupp.notMem_support_iff.mp hl]
          simp
      rw [h1, map_sum]
      exact Finset.sum_congr rfl fun l _ => map_mul _ _ _
    have hcomb : e j = ∑ q ∈ Q, ∑ l ∈ L, (MonoidAlgebra.single (Quotient.out q) (1 : K) *
        Work.ORReductions.subgroupAlgMap H K (a q l)) *
        Work.ORReductions.subgroupAlgMap H K ((k l) j) := by
      rw [hE]
      refine Finset.sum_congr rfl fun q hq => ?_
      rw [hφ q hq, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [mul_assoc]
    have hcomm : (∑ q ∈ Q, ∑ l ∈ L, (MonoidAlgebra.single (Quotient.out q) (1 : K) *
        Work.ORReductions.subgroupAlgMap H K (a q l)) *
        Work.ORReductions.subgroupAlgMap H K ((k l) j)) =
        ∑ l ∈ L, ∑ q ∈ Q, (MonoidAlgebra.single (Quotient.out q) (1 : K) *
        Work.ORReductions.subgroupAlgMap H K (a q l)) *
        Work.ORReductions.subgroupAlgMap H K ((k l) j) := Finset.sum_comm
    have hcomb2 : ∑ l ∈ L, sval l * Work.ORReductions.subgroupAlgMap H K ((k l) j) =
        ∑ l ∈ L, ∑ q ∈ Q, (MonoidAlgebra.single (Quotient.out q) (1 : K) *
        Work.ORReductions.subgroupAlgMap H K (a q l)) *
        Work.ORReductions.subgroupAlgMap H K ((k l) j) := by
      refine Finset.sum_congr rfl fun l _ => ?_
      have hsval : sval l = ∑ q ∈ Q, MonoidAlgebra.single (Quotient.out q) (1 : K) *
          Work.ORReductions.subgroupAlgMap H K (a q l) := rfl
      rw [hsval, Finset.sum_mul]
    exact hcomb.trans (hcomm.trans hcomb2.symm)
  have hmain : e = ∑ l ∈ L, sval l • Finsupp.mapRange
      (Work.ORReductions.subgroupAlgMap H K)
      (map_zero (Work.ORReductions.subgroupAlgMap H K)) (k l) := by
    refine Finsupp.ext fun j => ?_
    rw [hRHS j]
    exact key j
  -- Step 6: conclude.
  have hmem : (∑ l ∈ L, sval l • Finsupp.mapRange (Work.ORReductions.subgroupAlgMap H K)
      (map_zero (Work.ORReductions.subgroupAlgMap H K)) (k l)) ∈
      Submodule.span (MonoidAlgebra K G)
        (Set.range (fun l : κ => Finsupp.mapRange (Work.ORReductions.subgroupAlgMap H K)
          (map_zero _) (k l))) := by
    refine Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact ⟨l, rfl⟩
  rwa [← hmain] at hmem

end Work.ORReductions.Coherent
