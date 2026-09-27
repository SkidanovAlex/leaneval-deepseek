import Mathlib
import Submission.Work.Projection.exists_good_direction
import Submission.Work.Projection.exists_countable_chart_cover
import Submission.Work.Projection.compact_embedding

namespace Work.Projection

open scoped Manifold ContDiff
open Topology MeasureTheory

/-- Pointwise form of `injective_projVec_comp_mfderiv`: if `u` is not an immersion-bad direction
and `f` is immersive at the single point `x`, then `projVec u ∘ mfderiv f x` is injective. -/
theorem injective_projVec_comp_mfderiv_of {n k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (f : M → EuclideanSpace ℝ (Fin (k+1)))
    (hf : ContMDiff (𝓡 n) (𝓡 (k+1)) ∞ f)
    {p : ℕ → M}
    (hcov : (Set.univ : Set M) ⊆ ⋃ i, (chartAt (EuclideanSpace ℝ (Fin n)) (p i)).source)
    {u : EuclideanSpace ℝ (Fin k)} (hu : u ∉ badImmCharts (n := n) (k := k) f p) {x : M}
    (hx : Function.Injective (mfderiv (𝓡 n) (𝓡 (k+1)) f x)) :
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
      eq_zero_of_map_eq_zero hx (map_zero (mfderiv (𝓡 n) (𝓡 (k+1)) f x)) hz0
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

/-- Set-restricted form of `injective_projVec_comp`: if `u` is not an injectivity-bad direction
and `f` is injective on `K`, then `projVec u ∘ f` is injective on `K`. -/
theorem injective_projVec_comp_on {n k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (f : M → EuclideanSpace ℝ (Fin (k+1))) (K : Set M) (hinj : Set.InjOn f K)
    {p : ℕ → M}
    (hcov : (Set.univ : Set M) ⊆ ⋃ i, (chartAt (EuclideanSpace ℝ (Fin n)) (p i)).source)
    {u : EuclideanSpace ℝ (Fin k)} (hu : u ∉ badInjCharts (n := n) (k := k) f p) :
    Set.InjOn (fun x => projVec u (f x)) K := by
  intro x hxK y hyK hxy
  by_contra hne
  have hxy' : projVec u (f x) = projVec u (f y) := hxy
  have h1 : projVec u (f x - f y) = 0 := by
    rw [map_sub, hxy']
    simp
  obtain ⟨c, hc⟩ := (projVec_eq_zero_iff u (f x - f y)).1 h1
  have hsub : f x - f y ≠ 0 := sub_ne_zero_of_ne fun h => hne (hinj hxK hyK h)
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

/-- **Existence of a good projection direction, localised to a set `K`.**  Given a smooth map
`f : M → ℝ^{k+1}` with `2n < k` which is injective on `K` and immersive at every point of `K`,
there is a direction `u : ℝ^k` such that `projVec u ∘ f` is again injective on `K` and immersive
at every point of `K`. -/
theorem exists_good_direction_on {n k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (hk : 2 * n + 1 ≤ k)
    (f : M → EuclideanSpace ℝ (Fin (k+1))) (hf : ContMDiff (𝓡 n) (𝓡 (k+1)) ∞ f)
    (K : Set M) (hinj : Set.InjOn f K)
    (himm : ∀ x ∈ K, Function.Injective (mfderiv (𝓡 n) (𝓡 (k+1)) f x))
    (p : ℕ → M)
    (hcov : (Set.univ : Set M) ⊆ ⋃ i, (chartAt (EuclideanSpace ℝ (Fin n)) (p i)).source) :
    ∃ u : EuclideanSpace ℝ (Fin k),
      Set.InjOn (fun x => projVec u (f x)) K ∧
      ∀ x ∈ K, Function.Injective (projVec u ∘L mfderiv (𝓡 n) (𝓡 (k+1)) f x) := by
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
  exact ⟨u, injective_projVec_comp_on f K hinj hcov hu.2,
    fun x hx => injective_projVec_comp_mfderiv_of f hf hcov hu.1 (himm x hx)⟩

end Work.Projection

namespace Work.Noncompact

open scoped Manifold ContDiff
open Topology

/-- Iterated projection, localised to a set `K`: if a smooth map `e : M → ℝ^{2n+1+m}` of a smooth
`n`-manifold is injective on `K` and has injective `mfderiv` at every point of `K`, then so is some
smooth map `M → ℝ^{2n+1}`. -/
theorem reduce_steps_on {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] [T2Space M]
    [SecondCountableTopology M] [Nonempty M] (m : ℕ) (K : Set M)
    (e : M → EuclideanSpace ℝ (Fin (2 * n + 1 + m)))
    (hsm : ContMDiff (𝓡 n) (𝓡 (2 * n + 1 + m)) ∞ e)
    (hinj : Set.InjOn e K)
    (himm : ∀ x ∈ K, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n + 1 + m)) e x)) :
    ∃ e' : M → EuclideanSpace ℝ (Fin (2 * n + 1)),
      ContMDiff (𝓡 n) (𝓡 (2 * n + 1)) ∞ e' ∧ Set.InjOn e' K ∧
      ∀ x ∈ K, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n + 1)) e' x) := by
  induction m with
  | zero => exact ⟨e, hsm, hinj, himm⟩
  | succ m ih =>
      obtain ⟨p, hcov⟩ := Work.Projection.exists_countable_chart_cover n M
      obtain ⟨u, hu1, hu2⟩ :=
        Work.Projection.exists_good_direction_on (n := n) (k := 2 * n + 1 + m) (by omega)
          e hsm K hinj himm p hcov
      refine ih (⇑(Work.Projection.projVec u) ∘ e)
        (Work.Projection.contMDiff_comp_clm (Work.Projection.projVec u) e hsm) hu1 ?_
      intro x hx
      rw [Work.Projection.mfderiv_comp_clm (Work.Projection.projVec u) e hsm x]
      exact hu2 x hx

end Work.Noncompact
