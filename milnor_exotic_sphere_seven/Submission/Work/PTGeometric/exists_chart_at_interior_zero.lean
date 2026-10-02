import Mathlib
import Submission.Work.PTGeometric.linearCoordEquiv

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.PTGeometric

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter

noncomputable section

variable {n : ℕ} [NeZero n]

/-- **A chart of `ℝ` is strictly monotone on a small interval around `0`.**

For any chart `ψ` of `ℝ` whose source contains `0` there is `r > 0` such that `Ioo (-r) r` lies in
the source of `ψ` and `ψ` is either strictly increasing or strictly decreasing there. -/
lemma exists_strictMonoOn_chart_zero (ψ : OpenPartialHomeomorph ℝ ℝ) (h0 : (0 : ℝ) ∈ ψ.source) :
    ∃ r : ℝ, 0 < r ∧ Ioo (-r) r ⊆ ψ.source ∧
      (StrictMonoOn (ψ : ℝ → ℝ) (Ioo (-r) r) ∨ StrictAntiOn (ψ : ℝ → ℝ) (Ioo (-r) r)) := by
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp (ψ.open_source.mem_nhds h0)
  have hIc : Ioo (-r) r ⊆ ψ.source := by
    intro t ht
    refine hrsub ?_
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  exact ⟨r, hr, hIc, ContinuousOn.strictMonoOn_of_injOn_Ioo (a := -r) (b := r) (by linarith)
    (ψ.continuousOn_toFun.mono hIc) (ψ.injOn.mono hIc)⟩

/-- **The straightened (affine) chart at an interior zero.**

`A` a smooth `n`-manifold with boundary, `Φ : A → ℝ`, `x` an *interior* point of `A` with
`Φ x = 0` at which `Φ` is a Mathlib submersion (`IsSubmersionAt`, the local normal form
`ψ (Φ y) = (Λ ((φ.extend) y)).1` with `Λ : E ≃L (ℝ × F)`, `ψ` a chart of `ℝ`).
Then the region `{Φ ≤ 0}` is, near `x`, the image of the half-space `{u | 0 ≤ u 0}` under an
*affine* map of a maximal-atlas chart: there are a chart `e` of the maximal atlas at `x` (source
inside the interior of `A`) and a linear isomorphism `T` of the model space `E` with

`Φ y ≤ 0 ↔ 0 ≤ (T ((e.extend 𝓡∂) y - (e.extend 𝓡∂) x)) 0`  and
`Φ y = 0 ↔ (T ((e.extend 𝓡∂) y - (e.extend 𝓡∂) x)) 0 = 0`

for all `y ∈ e.source`.  (The *affine* correction is essential: the affine hyperplane
`{Λ = Λ (φ.extend x)}` carrying the fibre need not pass through the origin, so a linear functional
of `(e.extend) y` alone cannot cut it out; e.g. `A = ℝ²₊`, `Φ y = y 0 - 1`, `x = (1,0)`.)

Route: normal form of `hsub` (`domChart φ`, `codChart ψ`, `Λ : E ≃L (ℝ × F)`; the first
coordinate of `Λ` is a nonzero functional `ℓ`), so `(ψ.extend) (Φ y) = ℓ ((φ.extend) y)` for
`y ∈ φ.source`.  Then `Φ y = 0 ↔ ℓ ((φ.extend) y) = (ψ.extend) 0 = ℓ ((φ.extend) x)`, and
`{Φ ≤ 0}` is one of the two half-spaces `{ℓ ∘ (φ.extend) ≤/≥ ℓ ((φ.extend) x)}` according to the
monotonicity direction of the injective continuous `ψ.extend` near `0`.  Take `T` with
`(T ·) 0 = ± ℓ` completed to a linear isomorphism (translate the direction to position `0`), which
gives `(T((e.extend) y - (e.extend) x)) 0 = ±(ℓ((φ.extend) y) - ℓ((φ.extend) x))` for `e = φ`.
Shrink the source to a small neighbourhood of `x` inside the interior of `A` (restrictions of
maximal-atlas charts to open sets stay in the maximal atlas). -/
theorem exists_chart_at_interior_zero {n : ℕ} [NeZero n] (A : Type*) [TopologicalSpace A]
    [ChartedSpace (EuclideanHalfSpace n) A] [IsManifold (𝓡∂ n) ∞ A] (Φ : A → ℝ) {x : A}
    (hxint : x ∈ (𝓡∂ n).interior A) (hx0 : Φ x = 0)
    (hsub : IsSubmersionAt (𝓡∂ n) (𝓘(ℝ, ℝ)) ∞ Φ x) :
    ∃ (e : OpenPartialHomeomorph A (EuclideanHalfSpace n))
      (T : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)),
      e ∈ IsManifold.maximalAtlas (𝓡∂ n) ∞ A ∧ x ∈ e.source ∧
      e.source ⊆ (𝓡∂ n).interior A ∧
      (∀ y ∈ e.source, Φ y ≤ 0 ↔ 0 ≤ (T ((e.extend (𝓡∂ n)) y - (e.extend (𝓡∂ n)) x)) 0) ∧
      (∀ y ∈ e.source, Φ y = 0 ↔ (T ((e.extend (𝓡∂ n)) y - (e.extend (𝓡∂ n)) x)) 0 = 0) := by
  classical
  let φ := hsub.domChart
  let ψ := hsub.codChart
  have hxφ : x ∈ φ.source := hsub.mem_domChart_source
  have hxψ : Φ x ∈ ψ.source := hsub.mem_codChart_source
  -- the first coordinate functional of the local normal form
  set ℓ : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ hsub.complement).comp
      (hsub.equiv : EuclideanSpace ℝ (Fin n) →L[ℝ] (ℝ × hsub.complement)) with hℓdef
  have hℓapply : ∀ z, ℓ z = (hsub.equiv z).1 := fun z => rfl
  have hℓne : ℓ ≠ 0 := by
    intro hzero
    have h1 : ℓ (hsub.equiv.symm ((1 : ℝ), 0)) = 1 := by
      rw [hℓapply, ContinuousLinearEquiv.apply_symm_apply]
    rw [hzero] at h1
    norm_num at h1
  -- the normal form of `Φ` in the two charts
  have hwritten : ∀ y ∈ φ.source, ψ (Φ y) = ℓ ((φ.extend (𝓡∂ n)) y) := by
    intro y hy
    have hz : (φ.extend (𝓡∂ n)) y ∈ (φ.extend (𝓡∂ n)).target :=
      PartialEquiv.map_source _ (by simpa using hy)
    have h := hsub.writtenInCharts hz
    have hinv : (φ.extend (𝓡∂ n)).symm ((φ.extend (𝓡∂ n)) y) = y :=
      PartialEquiv.left_inv _ (by simpa [OpenPartialHomeomorph.extend_source] using hy)
    rw [Function.comp_apply, Function.comp_apply, hinv] at h
    have h2 : (ψ.extend (𝓘(ℝ, ℝ))) (Φ y) = ψ (Φ y) := by
      rw [OpenPartialHomeomorph.extend_coe]; rfl
    rw [h2] at h
    have h3 : (Prod.fst ∘ ⇑hsub.equiv) ((φ.extend (𝓡∂ n)) y) = ℓ ((φ.extend (𝓡∂ n)) y) := by
      rw [hℓapply]; rfl
    rw [h3] at h
    exact h
  -- a small interval around `0` on which `ψ` is strictly monotone
  obtain ⟨r, hrpos, hrsub, hmono⟩ :=
    exists_strictMonoOn_chart_zero ψ (by rw [← hx0]; exact hxψ)
  -- a neighbourhood of `x` on which everything is in force
  have hcontΦ : ContinuousAt Φ x := hsub.contMDiffAt.continuousAt
  have hIntOpen : IsOpen ((𝓡∂ n).interior A) :=
    ModelWithCorners.isOpen_interior (I := 𝓡∂ n) (M := A) (n := ∞) (by simp)
  have hmemΦ : Ioo (-r) r ∈ 𝓝 (Φ x) :=
    Ioo_mem_nhds (by rw [hx0]; linarith) (by rw [hx0]; linarith)
  obtain ⟨W, hWsub, hWopen, hxW⟩ := mem_nhds_iff.mp (hcontΦ.preimage_mem_nhds hmemΦ)
  set U : Set A := φ.source ∩ (𝓡∂ n).interior A ∩ W with hUdef
  have hUopen : IsOpen U := by
    rw [hUdef]; exact (φ.open_source.inter hIntOpen).inter hWopen
  have hxU : x ∈ U := by
    rw [hUdef]; exact ⟨⟨hxφ, hxint⟩, hxW⟩
  have hUsubΦ : U ⊆ Φ ⁻¹' Ioo (-r) r := by
    rw [hUdef]; intro y hy; exact hWsub hy.2
  have hUsubInt : U ⊆ (𝓡∂ n).interior A := by
    rw [hUdef]; intro y hy; exact hy.1.2
  -- the straightened chart and its properties
  have hEmem : φ.restr U ∈ IsManifold.maximalAtlas (𝓡∂ n) ∞ A :=
    IsManifold.mem_maximalAtlas_iff.mpr
      (restr_mem_maximalAtlas (contDiffGroupoid ∞ (𝓡∂ n)) hsub.domChart_mem_maximalAtlas hUopen)
  have hEsource : (φ.restr U).source = φ.source ∩ U := φ.restr_source' U hUopen
  have hxE : x ∈ (φ.restr U).source := by rw [hEsource]; exact ⟨hxφ, hxU⟩
  have hEsubInt : (φ.restr U).source ⊆ (𝓡∂ n).interior A := by
    rw [hEsource]; intro y hy; exact hUsubInt hy.2
  have heext : ∀ y, (φ.restr U).extend (𝓡∂ n) y = (φ.extend (𝓡∂ n)) y := fun y => rfl
  have hxI : Φ x ∈ Ioo (-r) r := hWsub hxW
  rcases hmono with hmono | hanti
  · -- `ψ` is strictly increasing on the interval
    obtain ⟨T, hT⟩ := linearCoordEquiv (-ℓ) (neg_ne_zero.mpr hℓne)
    refine ⟨φ.restr U, T, hEmem, hxE, hEsubInt, ?_, ?_⟩
    · intro y hy
      have hy' : y ∈ φ.source ∩ U := hEsource ▸ hy
      have hyle : Φ y ∈ Ioo (-r) r := hUsubΦ hy'.2
      have hA : Φ y ≤ Φ x ↔ ψ (Φ y) ≤ ψ (Φ x) :=
        (StrictMonoOn.le_iff_le hmono hyle hxI).symm
      have hB : ψ (Φ y) ≤ ψ (Φ x) ↔
          ℓ ((φ.extend (𝓡∂ n)) y) ≤ ℓ ((φ.extend (𝓡∂ n)) x) := by
        rw [hwritten y hy'.1, hwritten x hxφ]
      have hC : ℓ ((φ.extend (𝓡∂ n)) y) ≤ ℓ ((φ.extend (𝓡∂ n)) x) ↔
          0 ≤ (-ℓ) ((φ.extend (𝓡∂ n)) y - (φ.extend (𝓡∂ n)) x) := by
        rw [ContinuousLinearMap.neg_apply, map_sub]
        constructor <;> intro hh <;> linarith
      have hgoal : Φ y ≤ Φ x ↔
          0 ≤ (T ((φ.restr U).extend (𝓡∂ n) y - (φ.restr U).extend (𝓡∂ n) x)) 0 := by
        rw [hT, heext y, heext x]
        exact hA.trans (hB.trans hC)
      simpa only [hx0] using hgoal
    · intro y hy
      have hy' : y ∈ φ.source ∩ U := hEsource ▸ hy
      have hA : Φ y = Φ x ↔ ψ (Φ y) = ψ (Φ x) :=
        (InjOn.eq_iff ψ.injOn (hsub.source_subset_preimage_source hy'.1) hxψ).symm
      have hB : ψ (Φ y) = ψ (Φ x) ↔
          ℓ ((φ.extend (𝓡∂ n)) y) = ℓ ((φ.extend (𝓡∂ n)) x) := by
        rw [hwritten y hy'.1, hwritten x hxφ]
      have hC : ℓ ((φ.extend (𝓡∂ n)) y) = ℓ ((φ.extend (𝓡∂ n)) x) ↔
          (-ℓ) ((φ.extend (𝓡∂ n)) y - (φ.extend (𝓡∂ n)) x) = 0 := by
        rw [ContinuousLinearMap.neg_apply, map_sub]
        constructor <;> intro hh <;> linarith
      have hgoal : Φ y = Φ x ↔
          (T ((φ.restr U).extend (𝓡∂ n) y - (φ.restr U).extend (𝓡∂ n) x)) 0 = 0 := by
        rw [hT, heext y, heext x]
        exact hA.trans (hB.trans hC)
      simpa only [hx0] using hgoal
  · -- `ψ` is strictly decreasing on the interval
    obtain ⟨T, hT⟩ := linearCoordEquiv ℓ hℓne
    refine ⟨φ.restr U, T, hEmem, hxE, hEsubInt, ?_, ?_⟩
    · intro y hy
      have hy' : y ∈ φ.source ∩ U := hEsource ▸ hy
      have hyle : Φ y ∈ Ioo (-r) r := hUsubΦ hy'.2
      have hA : Φ y ≤ Φ x ↔ ψ (Φ x) ≤ ψ (Φ y) :=
        (StrictAntiOn.le_iff_ge hanti hxI hyle).symm
      have hB : ψ (Φ x) ≤ ψ (Φ y) ↔
          ℓ ((φ.extend (𝓡∂ n)) x) ≤ ℓ ((φ.extend (𝓡∂ n)) y) := by
        rw [hwritten x hxφ, hwritten y hy'.1]
      have hC : ℓ ((φ.extend (𝓡∂ n)) x) ≤ ℓ ((φ.extend (𝓡∂ n)) y) ↔
          0 ≤ ℓ ((φ.extend (𝓡∂ n)) y - (φ.extend (𝓡∂ n)) x) := by
        rw [map_sub]
        constructor <;> intro hh <;> linarith
      have hgoal : Φ y ≤ Φ x ↔
          0 ≤ (T ((φ.restr U).extend (𝓡∂ n) y - (φ.restr U).extend (𝓡∂ n) x)) 0 := by
        rw [hT, heext y, heext x]
        exact hA.trans (hB.trans hC)
      simpa only [hx0] using hgoal
    · intro y hy
      have hy' : y ∈ φ.source ∩ U := hEsource ▸ hy
      have hA : Φ y = Φ x ↔ ψ (Φ y) = ψ (Φ x) :=
        (InjOn.eq_iff ψ.injOn (hsub.source_subset_preimage_source hy'.1) hxψ).symm
      have hB : ψ (Φ y) = ψ (Φ x) ↔
          ℓ ((φ.extend (𝓡∂ n)) y) = ℓ ((φ.extend (𝓡∂ n)) x) := by
        rw [hwritten y hy'.1, hwritten x hxφ]
      have hC : ℓ ((φ.extend (𝓡∂ n)) y) = ℓ ((φ.extend (𝓡∂ n)) x) ↔
          ℓ ((φ.extend (𝓡∂ n)) y - (φ.extend (𝓡∂ n)) x) = 0 := by
        rw [map_sub]
        constructor <;> intro hh <;> linarith
      have hgoal : Φ y = Φ x ↔
          (T ((φ.restr U).extend (𝓡∂ n) y - (φ.restr U).extend (𝓡∂ n) x)) 0 = 0 := by
        rw [hT, heext y, heext x]
        exact hA.trans (hB.trans hC)
      simpa only [hx0] using hgoal

end

end Work.PTGeometric
