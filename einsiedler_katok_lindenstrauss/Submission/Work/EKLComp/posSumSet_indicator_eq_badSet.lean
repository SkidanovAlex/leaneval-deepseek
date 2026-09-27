import Mathlib
import Submission.Work.EKLComp.BirkhoffDefs
import Submission.Work.EKLComp.HopfDefs
import Submission.Work.EKLComp.mem_iterate_iff_of_preimage_eq
import Submission.Work.EKLComp.birkhoffSum_indicator_eq_of_forall_mem

namespace Work.EKLComp

open scoped BigOperators

/-- If `U = badSet T g ε` is `T`-invariant (`hinv`), then the set occurring in the conclusion of
Hopf's maximal inequality for `g̃ := U.indicator (g - ε)` is exactly `U`.  Indeed, on `U` the
`T`-orbit stays in `U` and `birkhoffSum T g̃ n x = n * (birkA T g n x - ε)`, which is `> 0` for
frequently many `n` by definition of `badSet`; off `U` the orbit stays off `U` (contrapositive
of the invariance), so `birkhoffSum T g̃ n x = 0` for all `n`. -/
theorem posSumSet_indicator_eq_badSet {X : Type*} (T : X → X) (g : X → ℝ) (ε : ℝ)
    (hinv : T ⁻¹' Work.EKLComp.Birkhoff.badSet T g ε = Work.EKLComp.Birkhoff.badSet T g ε) :
    {x | ∃ n : ℕ, 0 < birkhoffSum T
        ((Work.EKLComp.Birkhoff.badSet T g ε).indicator (fun y => g y - ε)) n x}
      = Work.EKLComp.Birkhoff.badSet T g ε := by
  ext x
  constructor
  · -- A point with a positive Birkhoff sum of `g̃` must lie in `U`: off `U` the whole orbit
    -- stays off `U`, hence every term of the sum is `0`.
    rintro ⟨n, hn⟩
    by_contra hx
    have hoff : ∀ k, T^[k] x ∉ Work.EKLComp.Birkhoff.badSet T g ε := fun k => by
      rw [mem_iterate_iff_of_preimage_eq T (Work.EKLComp.Birkhoff.badSet T g ε) hinv k x]
      exact hx
    have hzero : birkhoffSum T
        ((Work.EKLComp.Birkhoff.badSet T g ε).indicator (fun y => g y - ε)) n x = 0 := by
      simp only [birkhoffSum]
      exact Finset.sum_eq_zero fun k _ => Set.indicator_of_notMem (hoff k) _
    rw [hzero] at hn
    exact absurd hn (lt_irrefl 0)
  · -- A point of `U` has a positive Birkhoff sum of `g̃`: pick a frequency index `n` where the
    -- average of `g` exceeds `q > ε`; on `U` the orbit stays in `U`, so the indicator drops out
    -- and the sum equals `n * (birkA T g n x - ε) > 0`.
    intro hxU
    have hxUmem : x ∈ Work.EKLComp.Birkhoff.badSet T g ε := hxU
    rcases hxU with ⟨q, hεq, hfreq⟩
    obtain ⟨n, hn1, hnq⟩ :
        ∃ n, 1 ≤ n ∧ (q : ℝ) < Work.EKLComp.Birkhoff.birkA T g n x :=
      (Filter.frequently_atTop.mp hfreq) 1
    refine ⟨n, ?_⟩
    have hmem : ∀ k, k < n → T^[k] x ∈ Work.EKLComp.Birkhoff.badSet T g ε := fun k _ => by
      rw [mem_iterate_iff_of_preimage_eq T (Work.EKLComp.Birkhoff.badSet T g ε) hinv k x]
      exact hxUmem
    rw [birkhoffSum_indicator_eq_of_forall_mem T (Work.EKLComp.Birkhoff.badSet T g ε)
      (fun y => g y - ε) n x hmem, Work.EKLComp.birkhoffSum_sub_const]
    have hnne : n ≠ 0 := by omega
    have hmul : (n : ℝ) * Work.EKLComp.Birkhoff.birkA T g n x = birkhoffSum T g n x := by
      rw [Work.EKLComp.Birkhoff.birkA_def]
      have hcast : (n : ℝ) ≠ 0 := by exact_mod_cast hnne
      simp only [birkhoffSum]
      rw [← mul_assoc, mul_inv_cancel₀ hcast, one_mul]
    rw [← hmul, ← mul_sub]
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hbirk : (0 : ℝ) < Work.EKLComp.Birkhoff.birkA T g n x - ε := by linarith
    exact mul_pos hnpos hbirk

end Work.EKLComp
