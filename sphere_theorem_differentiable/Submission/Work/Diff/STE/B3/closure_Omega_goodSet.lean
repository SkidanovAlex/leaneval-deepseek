import Mathlib
import Submission.Work.Diff.STE.D.R_Rstar_expansion2
import Submission.Work.Diff.STE.D.flatToE_mem_interior_target
import Submission.Work.Diff.STE.B3.BPairDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `closure Omega ⊆ goodSet`, with `T2Space M` derived from the Layer B3 data

The statement of `closure_Omega_goodSet` is *not* equipped with a Hausdorffness hypothesis on `M`,
while the corresponding lemma of Layer D, `Work.Diff.STE.D.closure_Omega_subset_goodSet`, is stated
under `[T2Space M]`.  The reason is that its proof has to pass through

`tsupport (ζ i) ⊆ (extChartAt I (x₀ i)).source`  (`Work.Diff.STE.D.tsupport_zeta_subset`),

for which the `pt i`-image of the compact flat `σ i`-ball must be *closed* in `M`.

It turns out that this is not a real loss of generality: the Layer B3 data **forces `M` to be
Hausdorff**.  This is the content of `t2Space_of_B3Data` below, and it is why the Hausdorff-free
statement above is true.

## Why the data forces Hausdorffness

Let `p ≠ q` be two points of `M` that *no* pair of disjoint open sets can separate, i.e. every open
neighbourhood of `p` meets every open neighbourhood of `q`.  Then every continuous function
`f : M → ℝ` has `f p = f q`: if `f p ≠ f q`, pick disjoint open neighbourhoods `U ∋ f p`,
`V ∋ f q` in `ℝ`; then `f ⁻¹' U ∋ p` and `f ⁻¹' V ∋ q` are disjoint open sets, contradiction.

So `ζ i p = ζ i q` for every `i`.  By `hζsq` at `p`, `∑ i, (ζ i p)^2 = 1`, so some `i` has
`ζ i p ≠ 0`; hence, by `hζsupp`, `p ∈ (extChartAt I (x₀ i)).source`.  Also
`ζ i q = ζ i p ≠ 0`, so `hζsupp` gives `q ∈ (extChartAt I (x₀ i)).source` as well: a *single* chart
contains both points.

But a chart separates distinct points: `extChartAt I (x₀ i)` is injective on its open source, so its
two values `e p ≠ e q` in the Hausdorff model space `E` can be separated by disjoint open sets
`A`, `B`; the sets `e.source ∩ e ⁻¹' A` and `e.source ∩ e ⁻¹' B` are then disjoint open
neighbourhoods of `p` and `q` (openness from `ContinuousOn.isOpen_inter_preimage`, using
`continuousOn_extChartAt` and `isOpen_extChartAt_source`), contradicting the choice of `p`, `q`.
-/

namespace Work.Diff.STE.B3

-- `T2Space M` is a proposition; we install it as a local *instance* so that the Layer D lemma
-- (which is stated under `[T2Space M]`) can be applied, hence `haveI` rather than `have`.
set_option linter.style.haveILetI false

/-- **The Layer B3 data forces the underlying space to be Hausdorff.**  See the module docstring for
the (short) argument: two points that no disjoint open sets separate carry the same value under
every continuous function, in particular under all the weights `ζ i`; but `∑ i (ζ i p)^2 = 1` and
`hζsupp` then put both of them into the source of one single chart, and a chart separates distinct
points. -/
theorem t2Space_of_B3Data
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) : T2Space M := by
  rw [t2Space_iff M]
  intro p q hpq
  by_contra hcon
  -- Every continuous function takes the same value at `p` and at `q`.
  have hzeta : ∀ i : ι₀, D.ζ i p = D.ζ i q := by
    intro i
    by_contra hne
    obtain ⟨U, V, hU, hV, hpU, hqV, hdisj⟩ :=
      (t2Space_iff ℝ).mp inferInstance (i := D.ζ i p) (j := D.ζ i q) hne
    exact hcon ⟨(D.ζ i) ⁻¹' U, (D.ζ i) ⁻¹' V,
      hU.preimage (D.hζsm i).continuous, hV.preimage (D.hζsm i).continuous,
      hpU, hqV, hdisj.preimage (D.ζ i)⟩
  -- So some weight at `p` is nonzero, and both `p` and `q` lie in one single chart source.
  obtain ⟨i, hi⟩ : ∃ i : ι₀, D.ζ i p ≠ 0 := by
    have hsum : ∑ i : ι₀, (D.ζ i p) ^ 2 ≠ 0 := by rw [D.hζsq p]; norm_num
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
    exact ⟨i, (pow_ne_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hi⟩
  have hpsrc : p ∈ (extChartAt I (D.x₀ i)).source := (D.hζsupp i p hi).1
  have hqnz : D.ζ i q ≠ 0 := by rw [← hzeta i]; exact hi
  have hqsrc : q ∈ (extChartAt I (D.x₀ i)).source := (D.hζsupp i q hqnz).1
  -- A chart separates distinct points, since the model space is Hausdorff.
  obtain ⟨A, B, hA, hB, hpA, hqB, hdisjAB⟩ :=
    (t2Space_iff E).mp inferInstance (i := (extChartAt I (D.x₀ i)) p)
      (j := (extChartAt I (D.x₀ i)) q) (by
        intro hEq
        have h1 := (extChartAt I (D.x₀ i)).left_inv hpsrc
        have h2 := (extChartAt I (D.x₀ i)).left_inv hqsrc
        exact hpq (by rw [← h1, ← h2, hEq]))
  refine hcon ⟨(extChartAt I (D.x₀ i)).source ∩ (extChartAt I (D.x₀ i)) ⁻¹' A,
    (extChartAt I (D.x₀ i)).source ∩ (extChartAt I (D.x₀ i)) ⁻¹' B,
    ?_, ?_, ⟨hpsrc, hpA⟩, ⟨hqsrc, hqB⟩, ?_⟩
  · exact (continuousOn_extChartAt (I := I) (D.x₀ i)).isOpen_inter_preimage
      (isOpen_extChartAt_source (I := I) (D.x₀ i)) hA
  · exact (continuousOn_extChartAt (I := I) (D.x₀ i)).isOpen_inter_preimage
      (isOpen_extChartAt_source (I := I) (D.x₀ i)) hB
  · exact (hdisjAB.preimage (extChartAt I (D.x₀ i))).mono
      Set.inter_subset_right Set.inter_subset_right

theorem closure_Omega_goodSet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀) :
    closure (Work.Diff.STE.D.Omega (I := I) (M := M) D i j) ⊆
      Work.Diff.STE.D.goodSet (I := I) (M := M) D i j := by
  have hT2 : T2Space M := t2Space_of_B3Data (I := I) (M := M) D
  haveI := hT2
  exact Work.Diff.STE.D.closure_Omega_subset_goodSet (I := I) (M := M) D i j

end Work.Diff.STE.B3
