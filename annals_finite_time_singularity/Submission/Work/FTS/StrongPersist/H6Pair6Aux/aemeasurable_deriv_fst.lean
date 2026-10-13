import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Filter MeasureTheory
open scoped MeasureTheory Topology

namespace Work.FTS.StrongPersist.H6Pair6Aux

/-- Auxiliary lemma: translating the first coordinate by a *positive* amount preserves
`AEMeasurable` with respect to `(volume.restrict (Ioi 0)).prod ν`.

The push-forward of `Λ := (volume.restrict (Ioi 0)).prod ν` under `T p = (p.1 + h, p.2)` is
`Λ.map T = (volume.restrict (Ioi h)).prod ν ≤ Λ` (`Measure.map_prod_map`, `Measure.restrict_map`,
`map_add_right_eq_self`, `Measure.prod_mono`, `Measure.restrict_mono`); hence
`AEMeasurable Φ (Λ.map T)` (`AEMeasurable.mono_measure`) and `AEMeasurable (Φ ∘ T) Λ`
(`AEMeasurable.comp_measurable`). -/
theorem aemeasurable_comp_add_fst' {ν : MeasureTheory.Measure ℝ} [MeasureTheory.SFinite ν]
    {h : ℝ} (hh : 0 < h) {Φ : ℝ × ℝ → ℝ}
    (hΦ : AEMeasurable Φ ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod ν)) :
    AEMeasurable (fun p : ℝ × ℝ => Φ (p.1 + h, p.2))
      ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod ν) := by
  set μ : MeasureTheory.Measure (ℝ × ℝ) :=
    (MeasureTheory.volume.restrict (Set.Ioi 0)).prod ν with hμ
  have hΦμ : AEMeasurable Φ μ := hΦ
  have hTmeas : Measurable (fun p : ℝ × ℝ => (p.1 + h, p.2)) :=
    (measurable_fst.add_const h).prodMk measurable_snd
  have hvol : MeasureTheory.Measure.map (fun z : ℝ => z + h)
        (MeasureTheory.volume.restrict (Set.Ioi 0))
      = MeasureTheory.volume.restrict (Set.Ioi h) := by
    have hpre : (fun z : ℝ => z + h) ⁻¹' (Set.Ioi h) = Set.Ioi 0 := by
      ext z
      simp only [Set.mem_preimage, Set.mem_Ioi]
      constructor <;> intro hz <;> linarith
    have hf : Measurable (fun z : ℝ => z + h) := measurable_id.add_const h
    rw [← hpre,
      ← MeasureTheory.Measure.restrict_map (f := fun z : ℝ => z + h) hf measurableSet_Ioi,
      MeasureTheory.map_add_right_eq_self MeasureTheory.volume h]
  have hmap : MeasureTheory.Measure.map (fun p : ℝ × ℝ => (p.1 + h, p.2)) μ
      = (MeasureTheory.volume.restrict (Set.Ioi h)).prod ν := by
    have h1 := MeasureTheory.Measure.map_prod_map (MeasureTheory.volume.restrict (Set.Ioi 0)) ν
      (f := fun z : ℝ => z + h) (g := id) (measurable_id.add_const h) measurable_id
    have h2 : MeasureTheory.Measure.map (Prod.map (fun z : ℝ => z + h) id)
          ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod ν)
        = MeasureTheory.Measure.map (fun p : ℝ × ℝ => (p.1 + h, p.2))
          ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod ν) := rfl
    rw [hμ, ← h2, ← h1, hvol, MeasureTheory.Measure.map_id]
  have hle : MeasureTheory.Measure.map (fun p : ℝ × ℝ => (p.1 + h, p.2)) μ ≤ μ := by
    rw [hmap, hμ]
    exact MeasureTheory.Measure.prod_mono
      (MeasureTheory.Measure.restrict_mono (Set.Ioi_subset_Ioi hh.le) le_rfl) le_rfl
  have hfin := (hΦμ.mono_measure hle).comp_measurable hTmeas
  rw [show (Φ ∘ fun p : ℝ × ℝ => (p.1 + h, p.2)) = (fun p : ℝ × ℝ => Φ (p.1 + h, p.2))
      from rfl] at hfin
  exact hfin

/-- If `Φ : ℝ × ℝ → ℝ` is a.e.-measurable w.r.t. `(volume.restrict (Ioi 0)).prod ν` and each
`z`-slice `z ↦ Φ (z, θ)` is differentiable on `(0,∞)`, then the derivative `∂_z Φ` is again
a.e.-measurable w.r.t. the same measure.

Route: for `n ≥ 1` the difference quotients
`p ↦ n * (Φ (p.1 + 1/n, p.2) - Φ (p.1, p.2))`
are a.e.-measurable (translate the a.e.-measurability by the positive shift `1/n`: the
push-forward of the measure under `(z,θ) ↦ (z+1/n,θ)` is
`(volume.restrict (Ioi (1/n))).prod ν ≤ (volume.restrict (Ioi 0)).prod ν`, via
`Measure.map_prod_map`, `Measure.restrict_map`, `map_add_right_eq_self`, `Measure.prod_mono`,
`Measure.restrict_mono`; then `AEMeasurable.mono_measure` + `AEMeasurable.comp_measurable`),
and they converge a.e. (for `z > 0`) to `∂_zΦ` by `DifferentiableOn.hasDerivAt` +
`HasDerivAt.tendsto_slope` (+ `tendsto_one_div_atTop_nhds_zero_nat`).  An a.e. limit of
a.e.-measurable functions is a.e.-measurable (`AEMeasurable.limsup` + `Tendsto.limsup_eq`). -/
theorem aemeasurable_deriv_fst {ν : MeasureTheory.Measure ℝ} [MeasureTheory.SFinite ν]
    {Φ : ℝ × ℝ → ℝ}
    (hΦ : AEMeasurable Φ ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod ν))
    (hdiff : ∀ θ : ℝ, DifferentiableOn ℝ (fun z => Φ (z, θ)) (Set.Ioi 0)) :
    AEMeasurable (fun p : ℝ × ℝ => deriv (fun z => Φ (z, p.2)) p.1)
      ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod ν) := by
  set μ : MeasureTheory.Measure (ℝ × ℝ) :=
    (MeasureTheory.volume.restrict (Set.Ioi 0)).prod ν with hμ
  have hΦμ : AEMeasurable Φ μ := hΦ
  set F : ℕ → ℝ × ℝ → ℝ :=
    fun n p => (n : ℝ) * (Φ (p.1 + (n : ℝ)⁻¹, p.2) - Φ (p.1, p.2)) with hF
  -- the difference quotients are a.e.-measurable
  have hshift : ∀ n : ℕ, 0 < (n : ℝ)⁻¹ →
      AEMeasurable (fun p : ℝ × ℝ => Φ (p.1 + (n : ℝ)⁻¹, p.2)) μ :=
    fun n hn => aemeasurable_comp_add_fst' hn hΦμ
  have hFmeas : ∀ n : ℕ, AEMeasurable (F n) μ := by
    intro n
    cases n with
    | zero =>
      have hzero : F 0 = fun _ : ℝ × ℝ => (0 : ℝ) := by
        funext p
        simp only [hF, Nat.cast_zero, inv_zero, add_zero, zero_mul]
      rw [hzero]
      exact aemeasurable_const
    | succ k =>
      have hpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ)⁻¹ :=
        inv_pos.mpr (Nat.cast_pos.mpr (Nat.succ_pos k))
      have h1 : AEMeasurable (fun p : ℝ × ℝ => Φ (p.1 + ((k + 1 : ℕ) : ℝ)⁻¹, p.2)) μ :=
        hshift (k + 1) hpos
      have h2 : AEMeasurable (fun p : ℝ × ℝ => Φ (p.1, p.2)) μ := by simpa using hΦμ
      have h3 := h1.sub h2
      have h4 := h3.const_mul ((k + 1 : ℕ) : ℝ)
      simpa [hF] using h4
  -- the first coordinate is positive almost everywhere
  have hμ_eq : μ = ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod ν).restrict
      (Set.prod (Set.Ioi 0) Set.univ) := by
    have h := MeasureTheory.Measure.prod_restrict
      (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ)) (ν := ν) (Set.Ioi 0) Set.univ
    rw [MeasureTheory.Measure.restrict_univ] at h
    rw [hμ]
    exact h
  have hae_mem : ∀ᵐ p ∂μ, p ∈ Set.prod (Set.Ioi 0) Set.univ := by
    rw [hμ_eq]
    exact MeasureTheory.ae_restrict_mem (measurableSet_Ioi.prod MeasurableSet.univ)
  have hpos : ∀ᵐ p ∂μ, 0 < p.1 := hae_mem.mono (fun p hp => hp.1)
  -- pointwise (a.e.) convergence of the difference quotients to the derivative
  have hconv : ∀ᵐ p ∂μ, Filter.Tendsto (fun n : ℕ => F n p) Filter.atTop
      (nhds (deriv (fun z : ℝ => Φ (z, p.2)) p.1)) := by
    filter_upwards [hpos] with p hp
    have hH : HasDerivAt (fun z : ℝ => Φ (z, p.2))
        (deriv (fun z : ℝ => Φ (z, p.2)) p.1) p.1 :=
      DifferentiableOn.hasDerivAt (hdiff p.2) (isOpen_Ioi.mem_nhds hp)
    have hbase : Filter.Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) Filter.atTop (nhds (0 : ℝ)) := by
      simpa only [one_div] using tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
    have hseq : Filter.Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) Filter.atTop
        (nhdsWithin (0 : ℝ) ({(0 : ℝ)}ᶜ)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨hbase, ?_⟩
      filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
      exact inv_ne_zero (Nat.cast_ne_zero.mpr (by omega))
    have hcomp := (hH.tendsto_slope_zero).comp hseq
    refine Filter.Tendsto.congr' ?_ hcomp
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
    simp only [Function.comp_apply, hF, inv_inv, smul_eq_mul]
  -- an a.e. limit of a.e.-measurable functions is a.e.-measurable
  have hlimmeas : AEMeasurable
      (fun p : ℝ × ℝ => Filter.limsup (fun n : ℕ => F n p) Filter.atTop) μ :=
    AEMeasurable.limsup hFmeas
  refine hlimmeas.congr ?_
  filter_upwards [hconv] with p hp
  exact hp.limsup_eq

end Work.FTS.StrongPersist.H6Pair6Aux
