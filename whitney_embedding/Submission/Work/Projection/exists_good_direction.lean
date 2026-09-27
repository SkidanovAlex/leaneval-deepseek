import Mathlib
import Submission.Work.Projection.Basic
import Submission.Work.Projection.Defs
import Submission.Work.Projection.mfderiv_chartAt_decomp
import Submission.Work.Projection.dimH_badImmCharts
import Submission.Work.Projection.dimH_badInjCharts

/-!
# Existence of a good projection direction

Given a smooth embedding `f : M → ℝ^{k+1}` of a smooth `n`-manifold, with `2n < k`, there is a
direction `u : ℝ^k` such that the linear projection `projVec u : ℝ^{k+1} → ℝ^k`
(with kernel spanned by `(u,1)`) keeps `f` injective and immersive.

The proof is the classical projection argument: the set of *bad* directions is, in each chart, the
image of a `C¹` map defined on an open subset of `ℝ^{2n}`, hence has Hausdorff dimension `≤ 2n`,
which is strictly less than `k`; so a good direction exists.
-/

open scoped Manifold ContDiff
open Topology MeasureTheory

namespace Work.Projection

variable {n k : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]


/-- A linear map which is injective and sends `0` to `0` has trivial kernel. -/
lemma eq_zero_of_map_eq_zero {E F : Type*} [Zero E] [Zero F] {g : E → F}
    (hg : Function.Injective g) (h0 : g 0 = 0) {z : E} (hz : g z = 0) : z = 0 :=
  hg (hz.trans h0.symm)

/-- Applied form of the chart decomposition of `mfderiv`. -/
lemma mfderiv_chartAt_decomp_apply (f : M → EuclideanSpace ℝ (Fin (k+1)))
    (hf : ContMDiff (𝓡 n) (𝓡 (k+1)) ∞ f) (p x : M)
    (hx : x ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source)
    (z : TangentSpace (𝓡 n) x) :
    mfderiv (𝓡 n) (𝓡 (k+1)) f x z =
      fderiv ℝ (chartRep f p) ((chartAt (EuclideanSpace ℝ (Fin n)) p) x)
        (mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) p) x z) := by
  rw [mfderiv_chartAt_decomp f hf p x hx]
  rfl

/-- If `u` is not an immersion-bad direction, then `projVec u` composed with the derivative of `f`
is injective at every point, provided `f` is an immersion. -/
theorem injective_projVec_comp_mfderiv (f : M → EuclideanSpace ℝ (Fin (k+1)))
    (hf : ContMDiff (𝓡 n) (𝓡 (k+1)) ∞ f)
    (himm : ∀ x, Function.Injective (mfderiv (𝓡 n) (𝓡 (k+1)) f x))
    {p : ℕ → M}
    (hcov : (Set.univ : Set M) ⊆ ⋃ i, (chartAt (EuclideanSpace ℝ (Fin n)) (p i)).source)
    {u : EuclideanSpace ℝ (Fin k)} (hu : u ∉ badImmCharts (n := n) (k := k) f p) (x : M) :
    Function.Injective (projVec u ∘L mfderiv (𝓡 n) (𝓡 (k+1)) f x) := by
  intro w w' hww
  refine sub_eq_zero.mp ?_
  have hM : (projVec u ∘L mfderiv (𝓡 n) (𝓡 (k+1)) f x) (w - w') = 0 := by
    rw [map_sub, hww]
    simp
  set z : TangentSpace (𝓡 n) x := w - w' with hz
  have hMz : projVec u (mfderiv (𝓡 n) (𝓡 (k+1)) f x z) = 0 := hM
  obtain ⟨c, hc⟩ := (projVec_eq_zero_iff u (mfderiv (𝓡 n) (𝓡 (k+1)) f x z)).1 hMz
  have hxall : x ∈ ⋃ i, (chartAt (EuclideanSpace ℝ (Fin n)) (p i)).source :=
    hcov (Set.mem_univ x)
  rw [Set.mem_iUnion] at hxall
  obtain ⟨i, hi⟩ := hxall
  have hDgood : ∀ z' : EuclideanSpace ℝ (Fin n),
      fderiv ℝ (chartRep f (p i)) ((chartAt (EuclideanSpace ℝ (Fin n)) (p i)) x) z' ≠ vVec u := by
    intro z' hz'
    exact hu ⟨i, (chartAt (EuclideanSpace ℝ (Fin n)) (p i)) x,
      (chartAt (EuclideanSpace ℝ (Fin n)) (p i)).map_source hi, z', hz'⟩
  by_cases hc0 : c = 0
  · have hz0 : mfderiv (𝓡 n) (𝓡 (k+1)) f x z = (0 : TangentSpace (𝓡 (k+1)) (f x)) :=
      hc.trans (by rw [hc0]; exact zero_smul ℝ (vVec u))
    have hz' : z = 0 :=
      eq_zero_of_map_eq_zero (himm x) (map_zero (mfderiv (𝓡 n) (𝓡 (k+1)) f x)) hz0
    simpa [hz] using hz'
  · exfalso
    have hca := mfderiv_chartAt_decomp_apply f hf (p i) x hi z
    rw [hca] at hc
    refine hDgood ((1/c) • mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) (p i)) x z) ?_
    calc (fderiv ℝ (chartRep f (p i)) ((chartAt (EuclideanSpace ℝ (Fin n)) (p i)) x))
            ((1/c) • mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) (p i)) x z)
        = (1/c) • (fderiv ℝ (chartRep f (p i)) ((chartAt (EuclideanSpace ℝ (Fin n)) (p i)) x))
            (mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) (p i)) x z) :=
          map_smul _ _ _
      _ = (1/c) • (c • vVec u) := by rw [hc]
      _ = ((1/c) * c) • vVec u := by rw [smul_smul]
      _ = vVec u := by rw [one_div, inv_mul_cancel₀ hc0, one_smul]

/-- If `u` is not an injectivity-bad direction, then `projVec u ∘ f` is injective, provided `f`
is injective. -/
theorem injective_projVec_comp (f : M → EuclideanSpace ℝ (Fin (k+1)))
    (hinj : Function.Injective f) {p : ℕ → M}
    (hcov : (Set.univ : Set M) ⊆ ⋃ i, (chartAt (EuclideanSpace ℝ (Fin n)) (p i)).source)
    {u : EuclideanSpace ℝ (Fin k)} (hu : u ∉ badInjCharts (n := n) (k := k) f p) :
    Function.Injective (fun x => projVec u (f x)) := by
  intro x y hxy
  have hxy' : projVec u (f x) = projVec u (f y) := hxy
  by_contra hne
  have h1 : projVec u (f x - f y) = 0 := by
    rw [map_sub, hxy']
    simp
  obtain ⟨c, hc⟩ := (projVec_eq_zero_iff u (f x - f y)).1 h1
  have hsub : f x - f y ≠ 0 := sub_ne_zero_of_ne fun h => hne (hinj h)
  have hc0 : c ≠ 0 := by
    intro h0
    exact hsub (by rw [hc, h0, zero_smul])
  have hlast : (f x - f y) (Fin.last k) ≠ 0 := by
    rw [hc, last_smul_vVec]
    exact hc0
  have hext : extract (f x - f y) = u := extract_of_eq_smul_vVec u hc0 hc
  have hx : x ∈ ⋃ i, (chartAt (EuclideanSpace ℝ (Fin n)) (p i)).source := hcov (Set.mem_univ x)
  have hy : y ∈ ⋃ i, (chartAt (EuclideanSpace ℝ (Fin n)) (p i)).source := hcov (Set.mem_univ y)
  rw [Set.mem_iUnion] at hx hy
  obtain ⟨i, hi⟩ := hx
  obtain ⟨j, hj⟩ := hy
  refine hu ⟨i, j, (chartAt (EuclideanSpace ℝ (Fin n)) (p i)) x,
    (chartAt (EuclideanSpace ℝ (Fin n)) (p i)).map_source hi,
    (chartAt (EuclideanSpace ℝ (Fin n)) (p j)) y,
    (chartAt (EuclideanSpace ℝ (Fin n)) (p j)).map_source hj, ?_, ?_⟩
  · rw [chartRep_chart f (p i) x hi, chartRep_chart f (p j) y hj]
    exact hlast
  · rw [chartRep_chart f (p i) x hi, chartRep_chart f (p j) y hj]
    exact hext

/-- **Existence of a good projection direction.**  Given an injective immersion `f : M → ℝ^{k+1}`
with `2n < k`, there is a direction `u : ℝ^k` such that
`projVec u ∘ f : M → ℝ^k` is again injective with injective derivative. -/
theorem exists_good_direction (hk : 2 * n + 1 ≤ k)
    (f : M → EuclideanSpace ℝ (Fin (k+1))) (hf : ContMDiff (𝓡 n) (𝓡 (k+1)) ∞ f)
    (hinj : Function.Injective f)
    (himm : ∀ x, Function.Injective (mfderiv (𝓡 n) (𝓡 (k+1)) f x))
    (p : ℕ → M)
    (hcov : (Set.univ : Set M) ⊆ ⋃ i, (chartAt (EuclideanSpace ℝ (Fin n)) (p i)).source) :
    ∃ u : EuclideanSpace ℝ (Fin k),
      Function.Injective (fun x => projVec u (f x)) ∧
      ∀ x, Function.Injective (projVec u ∘L mfderiv (𝓡 n) (𝓡 (k+1)) f x) := by
  set bad := badImmCharts (n := n) (k := k) f p ∪ badInjCharts (n := n) (k := k) f p with hbad
  have hbound : dimH bad ≤ 2 * n := by
    rw [hbad, dimH_union]
    exact max_le (dimH_badImmCharts f hf p) (dimH_badInjCharts f hf p)
  have hlt : dimH bad < dimH (Set.univ : Set (EuclideanSpace ℝ (Fin k))) := by
    rw [Real.dimH_univ_eq_finrank, finrank_euclideanSpace_fin]
    refine lt_of_le_of_lt hbound ?_
    have h2 : 2 * n < k := by omega
    exact_mod_cast h2
  obtain ⟨u, hu⟩ : ∃ u, u ∉ bad := by
    by_contra h
    rw [not_exists] at h
    simp only [not_not] at h
    have : bad = (Set.univ : Set (EuclideanSpace ℝ (Fin k))) := Set.eq_univ_iff_forall.2 h
    rw [this] at hlt
    exact lt_irrefl _ hlt
  rw [hbad, Set.mem_union, not_or] at hu
  exact ⟨u, injective_projVec_comp f hinj hcov hu.2,
    injective_projVec_comp_mfderiv f hf himm hcov hu.1⟩

end Work.Projection
