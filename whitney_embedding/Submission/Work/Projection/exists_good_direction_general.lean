import Mathlib
import Submission.Work.Projection.GeneralDefs
import Submission.Work.Projection.Basic
import Submission.Work.Projection.dimH_badImmCharts_general
import Submission.Work.Projection.dimH_badInjCharts_general
import Submission.Work.Projection.mfderiv_extChartAt_decomp

/-!
# Existence of a good projection direction for a general model with corners

Given a smooth injective immersion `f : M → ℝ^{k+1}` of a manifold modelled on a
finite-dimensional boundaryless model with corners `I : ModelWithCorners ℝ E H`, with
`2 * finrank ℝ E + 1 ≤ k`, there is a direction `u : ℝ^k` such that the linear projection
`projVec u : ℝ^{k+1} → ℝ^k` (with kernel spanned by `(u,1)`) keeps `f` injective and immersive.

This is the generalisation of `Work.Projection.exists_good_direction` (the case
`E = EuclideanSpace ℝ (Fin n)`, `H = EuclideanSpace ℝ (Fin n)`, `I = 𝓡 n`) to an arbitrary
model with corners, using the extended charts `extChartAt I p : M → E` together with
`chartRepI`, `badImmChartsI` and `badInjChartsI` from
`Submission/Work/Projection/GeneralDefs.lean`.

As in the Euclidean case, the set of *bad* directions is the union of the immersion-bad and the
injectivity-bad sets, each of which has Hausdorff dimension `≤ 2 * finrank ℝ E`
(`dimH_badImmCharts_general`, `dimH_badInjCharts_general`).  Since this is strictly less than
`k`, there is a direction outside it, and such a direction is good.
-/

namespace Work.Projection

open scoped Manifold ContDiff
open Topology MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- A linear map which is injective and sends `0` to `0` has trivial kernel. -/
lemma eq_zero_of_map_eq_zero_gen {X Y : Type*} [Zero X] [Zero Y] {g : X → Y}
    (hg : Function.Injective g) (h0 : g 0 = 0) {z : X} (hz : g z = 0) : z = 0 :=
  hg (hz.trans h0.symm)

/-- Applied form of the decomposition of `mfderiv` along the extended chart at `p`: the
derivative of `f` at `x` factors through the derivative of the extended chart, the remaining
factor being the Fréchet derivative of the chart representation of `f`. -/
lemma mfderiv_extChartAt_decomp_apply_gen {k : ℕ} (f : M → EuclideanSpace ℝ (Fin (k+1)))
    (hf : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin (k+1))) ∞ f) (p x : M)
    (hx : x ∈ (extChartAt I p).source) (z : TangentSpace I x) :
    mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (k+1))) f x z =
      fderiv ℝ (Work.Projection.chartRepI (I := I) f p) ((extChartAt I p) x)
        (mfderiv I 𝓘(ℝ, E) (extChartAt I p) x z) := by
  rw [mfderiv_extChartAt_decomp f hf p x hx]
  rfl

/-- If `u` is not an immersion-bad direction, then `projVec u` composed with the derivative of
`f` is injective at every point, provided `f` is an immersion. -/
theorem injective_projVec_comp_mfderiv_general {k : ℕ}
    (f : M → EuclideanSpace ℝ (Fin (k+1)))
    (hf : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin (k+1))) ∞ f)
    (himm : ∀ x, Function.Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (k+1))) f x))
    {p : ℕ → M}
    (hcov : (Set.univ : Set M) ⊆ ⋃ i, (chartAt H (p i)).source)
    {u : EuclideanSpace ℝ (Fin k)} (hu : u ∉ badImmChartsI (I := I) f p) (x : M) :
    Function.Injective (projVec u ∘L mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (k+1))) f x) := by
  intro w w' hww
  refine sub_eq_zero.mp ?_
  have hM : (projVec u ∘L mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (k+1))) f x) (w - w') = 0 := by
    rw [map_sub, hww]; simp
  set z : TangentSpace I x := w - w' with hz
  have hMz : projVec u (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (k+1))) f x z) = 0 := hM
  obtain ⟨c, hc⟩ :=
    (projVec_eq_zero_iff u (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (k+1))) f x z)).1 hMz
  have hxall : x ∈ ⋃ i, (chartAt H (p i)).source := hcov (Set.mem_univ x)
  rw [Set.mem_iUnion] at hxall
  obtain ⟨i, hi⟩ := hxall
  have hxsrc : x ∈ (extChartAt I (p i)).source := by
    rw [extChartAt_source]; exact hi
  have hDgood : ∀ z' : E,
      fderiv ℝ (chartRepI (I := I) f (p i)) ((extChartAt I (p i)) x) z' ≠ vVec u := by
    intro z' hz'
    exact hu ⟨i, (extChartAt I (p i)) x, (extChartAt I (p i)).map_source hxsrc, z', by
      rw [fderivWithin_range_I]; exact hz'⟩
  by_cases hc0 : c = 0
  · have hz0 : mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (k+1))) f x z
        = (0 : EuclideanSpace ℝ (Fin (k+1))) :=
      hc.trans (by rw [hc0]; exact zero_smul ℝ (vVec u))
    have hz' : z = 0 :=
      eq_zero_of_map_eq_zero_gen (himm x)
        (map_zero (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (k+1))) f x)) hz0
    simpa [hz] using hz'
  · exfalso
    have hca := mfderiv_extChartAt_decomp_apply_gen f hf (p i) x hxsrc z
    rw [hca] at hc
    refine hDgood ((1/c) • mfderiv I 𝓘(ℝ, E) (extChartAt I (p i)) x z) ?_
    calc (fderiv ℝ (chartRepI (I := I) f (p i)) ((extChartAt I (p i)) x))
            ((1/c) • mfderiv I 𝓘(ℝ, E) (extChartAt I (p i)) x z)
        = (1/c) • (fderiv ℝ (chartRepI (I := I) f (p i)) ((extChartAt I (p i)) x))
            (mfderiv I 𝓘(ℝ, E) (extChartAt I (p i)) x z) := map_smul _ _ _
      _ = (1/c) • (c • vVec u) := by rw [hc]
      _ = ((1/c) * c) • vVec u := by rw [smul_smul]
      _ = vVec u := by rw [one_div, inv_mul_cancel₀ hc0, one_smul]

/-- If `u` is not an injectivity-bad direction, then `projVec u ∘ f` is injective, provided `f`
is injective. -/
theorem injective_projVec_comp_general {k : ℕ} (f : M → EuclideanSpace ℝ (Fin (k+1)))
    (hinj : Function.Injective f) {p : ℕ → M}
    (hcov : (Set.univ : Set M) ⊆ ⋃ i, (chartAt H (p i)).source)
    {u : EuclideanSpace ℝ (Fin k)} (hu : u ∉ badInjChartsI (I := I) f p) :
    Function.Injective (fun x => projVec u (f x)) := by
  intro x y hxy
  have hxy' : projVec u (f x) = projVec u (f y) := hxy
  by_contra hne
  have h1 : projVec u (f x - f y) = 0 := by
    rw [map_sub, hxy']; simp
  obtain ⟨c, hc⟩ := (projVec_eq_zero_iff u (f x - f y)).1 h1
  have hsub : f x - f y ≠ 0 := sub_ne_zero_of_ne fun h => hne (hinj h)
  have hc0 : c ≠ 0 := by
    intro h0
    exact hsub (by rw [hc, h0, zero_smul])
  have hlast : (f x - f y) (Fin.last k) ≠ 0 := by
    rw [hc, last_smul_vVec]; exact hc0
  have hext : extract (f x - f y) = u := extract_of_eq_smul_vVec u hc0 hc
  have hx : x ∈ ⋃ i, (chartAt H (p i)).source := hcov (Set.mem_univ x)
  have hy : y ∈ ⋃ i, (chartAt H (p i)).source := hcov (Set.mem_univ y)
  rw [Set.mem_iUnion] at hx hy
  obtain ⟨i, hi⟩ := hx
  obtain ⟨j, hj⟩ := hy
  have hxi : x ∈ (extChartAt I (p i)).source := by rw [extChartAt_source]; exact hi
  have hyj : y ∈ (extChartAt I (p j)).source := by rw [extChartAt_source]; exact hj
  refine hu ⟨i, j, (extChartAt I (p i)) x,
    (extChartAt I (p i)).map_source hxi,
    (extChartAt I (p j)) y,
    (extChartAt I (p j)).map_source hyj, ?_, ?_⟩
  · rw [chartRepI_extChartAt (I := I) f (p i) x hxi,
      chartRepI_extChartAt (I := I) f (p j) y hyj]
    exact hlast
  · rw [chartRepI_extChartAt (I := I) f (p i) x hxi,
      chartRepI_extChartAt (I := I) f (p j) y hyj]
    exact hext

/-- **Existence of a good projection direction.**  Given an injective immersion
`f : M → ℝ^{k+1}` of a manifold modelled on a finite dimensional `E`, with
`2 * finrank ℝ E + 1 ≤ k`, there is a direction `u : ℝ^k` such that
`projVec u ∘ f : M → ℝ^k` is again injective with injective derivative. -/
theorem exists_good_direction_general {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {k : ℕ} (hk : 2 * Module.finrank ℝ E + 1 ≤ k)
    (f : M → EuclideanSpace ℝ (Fin (k+1)))
    (hf : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin (k+1))) ∞ f)
    (hinj : Function.Injective f)
    (himm : ∀ x, Function.Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (k+1))) f x))
    (p : ℕ → M)
    (hcov : (Set.univ : Set M) ⊆ ⋃ i, (chartAt H (p i)).source) :
    ∃ u : EuclideanSpace ℝ (Fin k),
      Function.Injective (fun x => Work.Projection.projVec u (f x)) ∧
      ∀ x, Function.Injective
        (Work.Projection.projVec u ∘L
          mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (k+1))) f x) := by
  set bad := badImmChartsI (I := I) f p ∪ badInjChartsI (I := I) f p with hbad
  have hbound : dimH bad ≤ (2 * Module.finrank ℝ E : ℕ) := by
    rw [hbad, dimH_union]
    exact max_le (dimH_badImmCharts_general f hf p) (dimH_badInjCharts_general f hf p)
  have hlt : dimH bad < dimH (Set.univ : Set (EuclideanSpace ℝ (Fin k))) := by
    rw [Real.dimH_univ_eq_finrank, finrank_euclideanSpace_fin]
    refine lt_of_le_of_lt hbound ?_
    have h2 : 2 * Module.finrank ℝ E < k := by omega
    exact_mod_cast h2
  obtain ⟨u, hu⟩ : ∃ u, u ∉ bad := by
    by_contra h
    rw [not_exists] at h
    simp only [not_not] at h
    have : bad = (Set.univ : Set (EuclideanSpace ℝ (Fin k))) := Set.eq_univ_iff_forall.2 h
    rw [this] at hlt
    exact lt_irrefl _ hlt
  rw [hbad, Set.mem_union, not_or] at hu
  exact ⟨u, injective_projVec_comp_general f hinj hcov hu.2,
    injective_projVec_comp_mfderiv_general f hf himm hcov hu.1⟩

end Work.Projection
