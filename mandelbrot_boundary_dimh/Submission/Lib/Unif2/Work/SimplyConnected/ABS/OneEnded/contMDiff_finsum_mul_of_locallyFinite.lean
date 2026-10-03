import Mathlib

/-!
# Smoothness of a locally finite sum with constant coefficients

The assembly step of the ABS exhaustion function
(`Work.SimplyConnected.ABS.OneEnded.exists_contMDiff_sublevel_compact`, see
`NOTES_frontierConnected_superset_ROUTE_ANALYSIS.md` §50): with `χ` a smooth partition of unity
subordinate to a locally finite open cover `U` and `lvl : ℕ → ℕ` a level function with
`closure (U n) ⊆ V (lvl n)`, the function `g x := ∑ᶠ n, χ n x * (lvl n + 1)` — whose sublevel sets are
compact because `x ∉ V N` forces `lvl n > N` for every `n` with `χ n x ≠ 0` — is smooth.

That is the general fact proved here: a *locally finite* sum of smooth real functions with constant
coefficients is smooth.  The proof is pointwise: local finiteness of the supports gives a
neighbourhood on which the finitary sum is the finite sum over a fixed `Finset`, and a finite sum of
smooth functions is smooth (`ContMDiffAt.sum`).

Mathlib has neither `ContMDiffAt.const_mul`, `ContMDiffAt.const_smul` nor `ContMDiff.finsum`, so
this brick has to be built; the coefficient is multiplied through `ContMDiffAt.mul` against the
constant function, which is why the summand is written `f i x * c i` (that is the orientation
`ContMDiffAt.mul` produces).
-/

open scoped ContDiff Topology

open Set Filter

namespace Work.SimplyConnected.ABS.OneEnded

set_option maxHeartbeats 1000000

variable {ι : Type*} {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

/-- **A locally finite sum with constant coefficients of smooth real functions is smooth.** -/
theorem contMDiff_finsum_mul_of_locallyFinite {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {f : ι → M → ℝ} (c : ι → ℝ) (hlf : LocallyFinite fun i => Function.support (f i))
    (hf : ∀ i, ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ (f i)) :
    ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ fun x => ∑ᶠ i, f i x * c i := by
  intro x
  obtain ⟨t, ht, hfin⟩ := hlf x
  obtain ⟨s, hs⟩ := hfin.exists_finset
  have hev : (fun y => ∑ᶠ i, f i y * c i) =ᶠ[𝓝 x] fun y => ∑ i ∈ s, f i y * c i := by
    filter_upwards [ht] with y hy
    refine finsum_eq_sum_of_support_subset (fun i => f i y * c i) ?_
    intro i hi
    have hne : f i y ≠ 0 := fun h0 => hi (by simp [h0])
    simpa using (hs i).mpr ⟨y, hne, hy⟩
  exact ContMDiffAt.congr_of_eventuallyEq
    (ContMDiffAt.sum (t := s) (f := fun i y => f i y * c i)
      (fun i _ => (hf i).contMDiffAt.mul contMDiffAt_const)) hev

/-- **The weighted-sum comparison for a locally finite partition-type family.**

If `f` is a family with locally finite supports, nonnegative at `x`, with `∑ᶠ i, f i x = 1`, and every
summand that does not vanish at `x` has coefficient at least `C`, then `∑ᶠ i, f i x * c i ≥ C`.

This is the comparison step of the ABS exhaustion function (§50 of the route notes): with `f := χ`
the partition of unity and `c := fun n => (lvl n : ℝ) + 1`, the hypothesis `C ≤ c i` on the support is
exactly "`lvl n > N` whenever `χ n x ≠ 0`", which is what `x ∉ V N` gives.  Both finitary sums are
reduced to the same `Finset`, supplied by local finiteness at `x` — the trick of
`contMDiff_finsum_mul_of_locallyFinite` above. -/
theorem le_finsum_mul_of_locallyFinite {M : Type*} [TopologicalSpace M] {ι : Type*}
    {f : ι → M → ℝ} {c : ι → ℝ} {x : M} (hlf : LocallyFinite fun i => Function.support (f i))
    (hnonneg : ∀ i, 0 ≤ f i x) (hsum : ∑ᶠ i, f i x = 1) {C : ℝ}
    (hcoef : ∀ i, f i x ≠ 0 → C ≤ c i) :
    C ≤ ∑ᶠ i, f i x * c i := by
  obtain ⟨t, ht, hfin⟩ := hlf x
  have hxt : x ∈ t := mem_of_mem_nhds ht
  obtain ⟨s, hs⟩ := hfin.exists_finset
  have hsub : Function.support (fun i => f i x) ⊆ ↑s := by
    intro i hi
    have hne : f i x ≠ 0 := hi
    simpa using (hs i).mpr ⟨x, hne, hxt⟩
  have hsub' : Function.support (fun i => f i x * c i) ⊆ ↑s := by
    intro i hi
    have hne : f i x ≠ 0 := fun h0 => hi (by simp [h0])
    simpa using (hs i).mpr ⟨x, hne, hxt⟩
  rw [finsum_eq_sum_of_support_subset (fun i => f i x * c i) hsub']
  have h2 : ∑ i ∈ s, f i x = 1 := by
    rw [← finsum_eq_sum_of_support_subset (fun i => f i x) hsub]; exact hsum
  calc C = (∑ i ∈ s, f i x) * C := by rw [h2, one_mul]
    _ = ∑ i ∈ s, f i x * C := Finset.sum_mul s (fun i => f i x) C
    _ ≤ ∑ i ∈ s, f i x * c i :=
      Finset.sum_le_sum fun i _ => by
        by_cases h0 : f i x = 0
        · simp [h0]
        · exact mul_le_mul_of_nonneg_left (hcoef i h0) (hnonneg i)

end Work.SimplyConnected.ABS.OneEnded
