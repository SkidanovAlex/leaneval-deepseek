import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixR.FarLatDefs
import Submission.Work.BoseFixR.SamplingSqSumLeChiR0
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.farLatFoldCell`

**The lattice folding identity for the `far`-region Coulomb denominator.**  If `A ≥ 0` is
integrable with `tsupport A ⊆ closedBall 0 ℓ`, then

    ∫ z, A z / dist(z, ℓℤ³) = ∫_{cell ℓ} (Σ_{m ∈ ℤ³} A (z + ℓ m)) / ‖z‖.

The proof is the standard "fold the integral onto the fundamental domain":

* on the fundamental cell `cell ℓ = [-ℓ/2,ℓ/2]³` the nearest lattice point is the origin, so
  `dist(x, ℓℤ³) = ‖x‖` (`FarFold.infDist_lat_eq_norm_cell`, `x ∈ cell`);
* `dist(·, ℓℤ³)` is `ℓℤ³`-periodic;
* the `ℝ≥0∞` lattice-tiling identity `FarFold.tileLatticeLintegralAdd` (fundamental-domain identity
  for `cellI ℓ` at the level of `lintegral`, transferred to the closed cell through the null
  boundary) turns the whole-space integral into the sum over the lattice of the integrals over
  `cell ℓ`;
* pushing `1/‖x‖` and `ENNReal.ofReal` through the (pointwise finite) lattice sum
  (`FarFold.ofReal_tsum_div_norm_cell`) plus Tonelli for `tsum` (`MeasureTheory.lintegral_tsum`)
  converts the cell integral of the periodisation into the same lattice sum;
* both Bochner integrals are reduced to `ENNReal.toReal` of the corresponding `lintegral` via
  `MeasureTheory.integral_eq_lintegral_of_nonneg_ae`, so no integrability of `A/dist` is needed
  (both sides are `0` when it fails).

-/

noncomputable section

open scoped Real Topology BigOperators Pointwise
open MeasureTheory Metric Filter

namespace Work.BoseFixR.FarFold

/-- The closed box `cell ℓ` is measurable. -/
lemma measurableSet_cell_lat (ℓ : ℝ) : MeasurableSet (Work.BoseFixR.cell ℓ) := by
  rw [Work.BoseFixR.cell_eq_boxL ℓ]
  exact Work.BoseFixR.measurableSet_boxL ℓ

/-- **The lattice tiling identity, `+`-form, closed cell.**  Integrating an `ℝ≥0∞`-valued function
over `ℝ³` is the same as summing, over the lattice `ℓℤ³`, the integrals of its translates against
the closed period cell `cell ℓ`. -/
theorem tileLatticeLintegralAdd {ℓ : ℝ} (hℓ : 0 < ℓ)
    (g : EuclideanSpace ℝ (Fin 3) → ENNReal) :
    ∫⁻ u, g u
      = ∑' n : Fin 3 → ℤ,
          ∫⁻ x in cell ℓ, g (x + lat ℓ n) := by
  haveI : Countable (Work.BoseFixR.latHom ℓ).range := Work.BoseFixR.countable_range_latHom (ne_of_gt hℓ)
  have hplus : ∫⁻ u, g u
      = ∑' n : Fin 3 → ℤ, ∫⁻ x in cellI ℓ, g (x + lat ℓ n) := by
    rw [(Work.BoseFixR.isAddFundamentalDomain_cellI hℓ).lintegral_eq_tsum'' g,
      ← (Work.BoseFixR.latEquiv (ne_of_gt hℓ)).tsum_eq
        (fun v : (Work.BoseFixR.latHom ℓ).range => ∫⁻ x in cellI ℓ, g (v +ᵥ x))]
    refine tsum_congr fun n => ?_
    congr 1 with x
    simp [Work.BoseFixR.latEquiv, add_comm]
  rw [hplus]
  exact tsum_congr fun n => setLIntegral_congr (Work.BoseFixR.cellI_ae_eq_cell ℓ)

/-- Coordinatewise domination of squares on the cell: the `i`-th coordinate of `z` is no larger in
absolute value than the corresponding coordinate of `z - lat ℓ m`. -/
private lemma sq_le_sq_sub_lat {ℓ : ℝ} (hℓ : 0 < ℓ) {z : EuclideanSpace ℝ (Fin 3)}
    (hz : ∀ i, |z i| ≤ ℓ / 2) (m : Fin 3 → ℤ) (i : Fin 3) :
    (z i) ^ 2 ≤ (z i - ℓ * (m i : ℝ)) ^ 2 := by
  have hkey : (z i - ℓ * (m i : ℝ)) ^ 2 - (z i) ^ 2
      = (ℓ * (m i : ℝ)) * (ℓ * (m i : ℝ) - 2 * z i) := by ring
  have hb := abs_le.mp (hz i)
  have hnn : 0 ≤ (ℓ * (m i : ℝ)) * (ℓ * (m i : ℝ) - 2 * z i) := by
    rcases lt_trichotomy (m i) 0 with h | h | h
    · have h1 : ((m i : ℤ) : ℝ) ≤ -1 := by
        have : m i ≤ -1 := by omega
        exact_mod_cast this
      have h2 : ℓ * ((m i : ℤ) : ℝ) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hℓ.le (by linarith)
      have h3 : ℓ * ((m i : ℤ) : ℝ) - 2 * z i ≤ 0 := by nlinarith [hℓ, h1, hb.1]
      exact mul_nonneg_of_nonpos_of_nonpos h2 h3
    · rw [h]; simp
    · have h1 : (1 : ℝ) ≤ ((m i : ℤ) : ℝ) := by
        have : (1 : ℤ) ≤ m i := by omega
        exact_mod_cast this
      have h2 : 0 ≤ ℓ * ((m i : ℤ) : ℝ) := mul_nonneg hℓ.le (by linarith)
      have h3 : 0 ≤ ℓ * ((m i : ℤ) : ℝ) - 2 * z i := by nlinarith [hℓ, h1, hb.2]
      exact mul_nonneg h2 h3
  linarith [hkey, hnn]

/-- The distance from a point of the cell to the lattice `ℓℤ³` is its norm. -/
theorem infDist_lat_eq_norm_cell {ℓ : ℝ} (hℓ : 0 < ℓ) {z : EuclideanSpace ℝ (Fin 3)}
    (hz : ∀ i, |z i| ≤ ℓ / 2) :
    Metric.infDist z (Set.range (fun n : Fin 3 → ℤ => Work.BoseFixR.lat ℓ n)) = ‖z‖ := by
  have hmem : (0 : EuclideanSpace ℝ (Fin 3)) ∈ Set.range (fun n : Fin 3 → ℤ => lat ℓ n) :=
    ⟨0, by simp [lat_zero]⟩
  refine le_antisymm ?_ ?_
  · simpa using Metric.infDist_le_dist_of_mem (x := z) hmem
  · refine (Metric.le_infDist (s := Set.range (fun n : Fin 3 → ℤ => lat ℓ n))
      ⟨0, hmem⟩).mpr ?_
    rintro y ⟨m, rfl⟩
    rw [dist_eq_norm]
    have hsq : ‖z‖ ^ 2 ≤ ‖z - lat ℓ m‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
      refine Finset.sum_le_sum fun i _ => ?_
      have hcoord : (z - lat ℓ m) i = z i - ℓ * (m i : ℝ) := by simp [lat]
      rw [hcoord]
      exact sq_le_sq_sub_lat hℓ hz m i
    nlinarith [hsq, norm_nonneg z, norm_nonneg (z - lat ℓ m)]

/-- Pushing `ENNReal.ofReal` and the factor `1/‖x‖` through the (pointwise finite) lattice sum. -/
theorem ofReal_tsum_div_norm_cell {A : EuclideanSpace ℝ (Fin 3) → ℝ} (hA : ∀ z, 0 ≤ A z)
    {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hsupp : tsupport A ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) ℓ)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ Work.BoseFixR.cell ℓ) :
    ENNReal.ofReal ((∑' m : Fin 3 → ℤ, A (x + Work.BoseFixR.lat ℓ m)) / ‖x‖)
      = ∑' m : Fin 3 → ℤ, ENNReal.ofReal (A (x + Work.BoseFixR.lat ℓ m) / ‖x‖) := by
  classical
  -- the lattice sum is supported on the `27` labels `{-1,0,1}³`
  have hsupport : ∀ m : Fin 3 → ℤ, m ∉ Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-1) 1) →
      A (x + Work.BoseFixR.lat ℓ m) = 0 := by
    intro m hm
    by_contra hne
    have hmem' : x + Work.BoseFixR.lat ℓ m ∈ tsupport A :=
      subset_closure (Function.mem_support.mpr hne)
    have hnorm : ‖x + Work.BoseFixR.lat ℓ m‖ ≤ ℓ := by
      have h := hsupp hmem'
      rw [Metric.mem_closedBall] at h
      simpa [dist_eq_norm] using h
    obtain ⟨i, hi⟩ : ∃ i : Fin 3, ¬ (m i ∈ Finset.Icc (-1) 1) := by
      by_contra hcon
      exact hm (by
        rw [Fintype.mem_piFinset]
        intro i
        by_contra hi
        exact hcon ⟨i, hi⟩)
    have hilt : m i < -1 ∨ 1 < m i := by
      have hi' : ¬(-1 ≤ m i ∧ m i ≤ 1) := by
        simpa [Finset.mem_Icc] using hi
      rcases lt_or_ge (m i) (-1) with h | h
      · exact Or.inl h
      · exact Or.inr (by
          by_contra hc
          exact hi' ⟨h, by omega⟩)
    have h2 : (2 : ℝ) ≤ |((m i : ℤ) : ℝ)| := by
      rcases hilt with h | h
      · have h' : (m i : ℤ) ≤ -2 := by omega
        have h'' : ((m i : ℤ) : ℝ) ≤ -2 := by exact_mod_cast h'
        rw [abs_of_nonpos (by linarith)]; linarith
      · have h' : (2 : ℤ) ≤ m i := by omega
        have h'' : (2 : ℝ) ≤ ((m i : ℤ) : ℝ) := by exact_mod_cast h'
        rw [abs_of_nonneg (by linarith)]; linarith
    have hcoord : |(x + Work.BoseFixR.lat ℓ m) i| ≤ ‖x + Work.BoseFixR.lat ℓ m‖ := by
      simpa using PiLp.norm_apply_le (x + Work.BoseFixR.lat ℓ m) i
    have hcoord' : (x + Work.BoseFixR.lat ℓ m) i = x i + ℓ * ((m i : ℤ) : ℝ) := by
      simp [Work.BoseFixR.lat]
    have hxle : |x i| ≤ ℓ / 2 := mem_cell.mp hx i
    have htri : |ℓ * ((m i : ℤ) : ℝ)| ≤ |(x + Work.BoseFixR.lat ℓ m) i| + |x i| := by
      have h1 : |(x + Work.BoseFixR.lat ℓ m) i - x i|
          ≤ |(x + Work.BoseFixR.lat ℓ m) i| + |x i| := by
        rw [abs_sub_le_iff]
        exact ⟨by linarith [le_abs_self ((x + Work.BoseFixR.lat ℓ m) i), neg_le_abs (x i)],
          by linarith [le_abs_self (x i), neg_le_abs ((x + Work.BoseFixR.lat ℓ m) i)]⟩
      have h2 : ℓ * ((m i : ℤ) : ℝ) = (x + Work.BoseFixR.lat ℓ m) i - x i := by
        rw [hcoord']; ring
      rwa [h2]
    have hbig : ℓ * 2 ≤ |ℓ * ((m i : ℤ) : ℝ)| := by
      rw [abs_mul, abs_of_pos hℓ]
      exact mul_le_mul_of_nonneg_left h2 hℓ.le
    nlinarith [htri, hbig, hcoord, hnorm, hxle, hℓ]
  have h1 : (∑' m : Fin 3 → ℤ, A (x + Work.BoseFixR.lat ℓ m))
      = ∑ m ∈ Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-1) 1),
          A (x + Work.BoseFixR.lat ℓ m) := tsum_eq_sum hsupport
  have h2 : (∑' m : Fin 3 → ℤ, ENNReal.ofReal (A (x + Work.BoseFixR.lat ℓ m) / ‖x‖))
      = ∑ m ∈ Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-1) 1),
          ENNReal.ofReal (A (x + Work.BoseFixR.lat ℓ m) / ‖x‖) := by
    refine tsum_eq_sum fun m hm => ?_
    rw [hsupport m hm, zero_div, ENNReal.ofReal_zero]
  rw [h1, h2]
  by_cases hx0 : ‖x‖ = 0
  · simp [hx0]
  · have hpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm hx0)
    have key : ∀ m ∈ Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-1) 1),
        0 ≤ A (x + Work.BoseFixR.lat ℓ m) := fun m _ => hA _
    calc ENNReal.ofReal
            ((∑ m ∈ Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-1) 1),
              A (x + Work.BoseFixR.lat ℓ m)) / ‖x‖)
        = ENNReal.ofReal (∑ m ∈ Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-1) 1),
              A (x + Work.BoseFixR.lat ℓ m)) / ENNReal.ofReal ‖x‖ :=
          ENNReal.ofReal_div_of_pos hpos
      _ = (∑ m ∈ Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-1) 1),
              ENNReal.ofReal (A (x + Work.BoseFixR.lat ℓ m))) / ENNReal.ofReal ‖x‖ := by
          rw [ENNReal.ofReal_sum_of_nonneg key]
      _ = ∑ m ∈ Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-1) 1),
              ENNReal.ofReal (A (x + Work.BoseFixR.lat ℓ m)) / ENNReal.ofReal ‖x‖ :=
          ENNReal.sum_div _
      _ = ∑ m ∈ Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-1) 1),
              ENNReal.ofReal (A (x + Work.BoseFixR.lat ℓ m) / ‖x‖) := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [ENNReal.ofReal_div_of_pos hpos]

/-- A.e. strong measurability of the periodisation (times `1/‖x‖`) on the cell. -/
theorem aestronglyMeasurable_period_div_cell {A : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hAint : MeasureTheory.Integrable A) (ℓ : ℝ) :
    MeasureTheory.AEStronglyMeasurable
      (fun x : EuclideanSpace ℝ (Fin 3) =>
        (∑' m : Fin 3 → ℤ, A (x + Work.BoseFixR.lat ℓ m)) / ‖x‖)
      (MeasureTheory.volume.restrict (Work.BoseFixR.cell ℓ)) := by
  have hAae : AEMeasurable A volume :=
    aestronglyMeasurable_iff_aemeasurable.mp hAint.aestronglyMeasurable
  have hterm : ∀ m : Fin 3 → ℤ, AEMeasurable (fun x : EuclideanSpace ℝ (Fin 3) =>
      A (x + Work.BoseFixR.lat ℓ m)) volume := fun m =>
    hAae.comp_quasiMeasurePreserving
      (measurePreserving_add_right volume (Work.BoseFixR.lat ℓ m)).quasiMeasurePreserving
  have htsum : AEMeasurable (fun x : EuclideanSpace ℝ (Fin 3) =>
      ∑' m : Fin 3 → ℤ, A (x + Work.BoseFixR.lat ℓ m)) volume :=
    AEMeasurable.tsum hterm
  exact ((htsum.div continuous_norm.aemeasurable).aestronglyMeasurable).mono_measure
    Measure.restrict_le_self

end Work.BoseFixR.FarFold

namespace Work.BoseFixR

/-- **The lattice folding identity.**  The whole-space integral of `A` against the reciprocal
distance to the lattice `ℓℤ³` equals the integral over one period cell of the periodisation of `A`
against `1/‖·‖`. -/
theorem farLatFoldCell {A : EuclideanSpace ℝ (Fin 3) → ℝ} (hA : ∀ z, 0 ≤ A z)
    (hAint : MeasureTheory.Integrable A) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hsupp : tsupport A ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) ℓ) :
    (∫ z, A z / Metric.infDist z (Set.range (fun n : Fin 3 → ℤ => Work.BoseFixR.lat ℓ n)))
      = ∫ z in Work.BoseFixR.cell ℓ,
          (∑' m : Fin 3 → ℤ, A (z + Work.BoseFixR.lat ℓ m)) / ‖z‖ := by
  have hAae : AEMeasurable A volume :=
    aestronglyMeasurable_iff_aemeasurable.mp hAint.aestronglyMeasurable
  -- 1. the left-hand side, as `toReal` of its `lintegral`
  have hL : (∫ z, A z / Metric.infDist z (Set.range (fun n : Fin 3 → ℤ => lat ℓ n)))
      = (∫⁻ z, ENNReal.ofReal (A z / latDistL ℓ z)).toReal := by
    change (∫ z, A z / latDistL ℓ z)
      = (∫⁻ z, ENNReal.ofReal (A z / latDistL ℓ z)).toReal
    refine integral_eq_lintegral_of_nonneg_ae ?_ ?_
    · exact Filter.Eventually.of_forall fun z => div_nonneg (hA z) Metric.infDist_nonneg
    · exact (hAae.div (Metric.continuous_infDist_pt _).aemeasurable).aestronglyMeasurable
  -- 2. the right-hand side, as `toReal` of its `lintegral`
  have hR : (∫ z in cell ℓ, (∑' m : Fin 3 → ℤ, A (z + lat ℓ m)) / ‖z‖)
      = (∫⁻ z in cell ℓ,
          ENNReal.ofReal ((∑' m : Fin 3 → ℤ, A (z + lat ℓ m)) / ‖z‖)).toReal := by
    refine integral_eq_lintegral_of_nonneg_ae (μ := volume.restrict (cell ℓ)) ?_ ?_
    · exact Filter.Eventually.of_forall fun z =>
        div_nonneg (tsum_nonneg fun m => hA _) (norm_nonneg z)
    · exact FarFold.aestronglyMeasurable_period_div_cell hAint ℓ
  -- 3. the `ℝ≥0∞` identity between the two `lintegral`s
  have hmain : (∫⁻ z, ENNReal.ofReal (A z / latDistL ℓ z))
      = ∫⁻ z in cell ℓ,
          ENNReal.ofReal ((∑' m : Fin 3 → ℤ, A (z + lat ℓ m)) / ‖z‖) := by
    have hB := FarFold.tileLatticeLintegralAdd hℓ
      (fun u : EuclideanSpace ℝ (Fin 3) => ENNReal.ofReal (A u / latDistL ℓ u))
    rw [hB]
    -- on the cell, `latDistL` is the norm, and `latDistL` is lattice-periodic
    have h1 : (∑' n : Fin 3 → ℤ, ∫⁻ x in cell ℓ,
          ENNReal.ofReal (A (x + lat ℓ n) / latDistL ℓ (x + lat ℓ n)))
        = ∑' n : Fin 3 → ℤ, ∫⁻ x in cell ℓ,
            ENNReal.ofReal (A (x + lat ℓ n) / ‖x‖) := by
      refine tsum_congr fun n => ?_
      refine setLIntegral_congr_fun (FarFold.measurableSet_cell_lat ℓ) fun x hx => ?_
      have hxnorm : latDistL ℓ x = ‖x‖ :=
        FarFold.infDist_lat_eq_norm_cell hℓ (mem_cell.mp hx)
      rw [latDistL_period ℓ x n, hxnorm]
    -- Tonelli for the (pointwise finite) lattice sum over the cell
    have h2 : (∫⁻ x in cell ℓ,
          ENNReal.ofReal ((∑' m : Fin 3 → ℤ, A (x + lat ℓ m)) / ‖x‖))
        = ∑' m : Fin 3 → ℤ, ∫⁻ x in cell ℓ,
            ENNReal.ofReal (A (x + lat ℓ m) / ‖x‖) := by
      have hswap := lintegral_tsum (μ := volume.restrict (cell ℓ))
        (f := fun m : Fin 3 → ℤ => fun x : EuclideanSpace ℝ (Fin 3) =>
          ENNReal.ofReal (A (x + lat ℓ m) / ‖x‖)) ?_
      · rw [← hswap]
        exact setLIntegral_congr_fun (FarFold.measurableSet_cell_lat ℓ) fun x hx =>
          FarFold.ofReal_tsum_div_norm_cell hA hℓ hsupp hx
      · intro m
        have hshift : AEMeasurable (fun x : EuclideanSpace ℝ (Fin 3) =>
            A (x + lat ℓ m)) volume :=
          hAae.comp_quasiMeasurePreserving
            (measurePreserving_add_right volume (lat ℓ m)).quasiMeasurePreserving
        exact ((hshift.div continuous_norm.aemeasurable).ennreal_ofReal).restrict
    rw [h1, h2]
  rw [hL, hR, hmain]

end Work.BoseFixR
