import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Submission.Work.BoseFixR.LatGreen.madelung_smooth_nonpos
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.LatGreen.latGreen_le_inv_fourpi_infDist`

The **sharp nearest-image bound** for the `ℤ³` lattice Green's function with neutralising
background — the pointwise input (K1) of `FINDING_farLatRow_sharp.md`:

`latGreen u ≤ 1 / (4 π d(u, ℤ³))`   for every `u ≠ 0`,

where `d(u, ℤ³) = Metric.infDist u (Set.range latVec)` is the distance from `u` to the lattice.

The proof has three ingredients.

* The Madelung sign `latGreenSmooth u ≤ 0`, valid on the Voronoi cell `{u | ∀ i, |u i| ≤ 1/2}`
  (`madelung_smooth_nonpos`), gives `latGreen u ≤ 1/(4π‖u‖)` there.
* `latGreen` is `ℤ³`-periodic (`latGreen_periodic`) and the distance to the lattice is invariant
  under lattice translations, so an arbitrary `u` may be reduced to its representative in the
  cell; on the cell the nearest lattice point is the origin, i.e. `d(u,ℤ³) = ‖u‖`.
* On the lattice itself `d = 0`, so the right-hand side is `1/(4π·0) = 0` (Lean's division
  convention) and the statement reads `latGreen (latVec n) ≤ 0`.  In fact
  `latGreen (latVec n) = 0`: the defining integral `∫_0^∞ (heatPeriod t 0 − 1) dt` is *not*
  integrable (its integrand dominates `t ↦ (4πt)^{-3/2}/2` near `0`), so
  `MeasureTheory.integral_undef` assigns it the value `0`.
-/

noncomputable section

open scoped Real BigOperators
open MeasureTheory Set

namespace Work.BoseFixR.LatGreen

local notation "ℝ3" => EuclideanSpace ℝ (Fin 3)

/-- `0` is the lattice vector of the origin. -/
@[simp] lemma latVec_zero : latVec (0 : Fin 3 → ℤ) = (0 : ℝ3) := by
  ext i
  simp [latVec]

/-- **Rounding to the fundamental cell** `[-1/2,1/2]³`: every point of `ℝ3` differs from a
lattice vector by a vector whose coordinates are bounded by `1/2`. -/
lemma exists_cell_rep (u : ℝ3) : ∃ n : Fin 3 → ℤ, ∀ i, |u i - (n i : ℝ)| ≤ 1 / 2 := by
  refine ⟨fun i => ⌊u i + 1 / 2⌋, fun i => ?_⟩
  have h1 : ((⌊u i + 1 / 2⌋ : ℤ) : ℝ) ≤ u i + 1 / 2 := Int.floor_le _
  have h2 : u i + 1 / 2 < ((⌊u i + 1 / 2⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  rw [abs_le]
  constructor <;> linarith

/-- **The distance to the lattice is invariant under lattice translations.** -/
lemma infDist_sub_latVec (u : ℝ3) (n : Fin 3 → ℤ) :
    Metric.infDist (u - latVec n) (Set.range (latVec : (Fin 3 → ℤ) → ℝ3))
      = Metric.infDist u (Set.range (latVec : (Fin 3 → ℤ) → ℝ3)) := by
  have hset : (fun x : ℝ3 => x + latVec n) '' Set.range (latVec : (Fin 3 → ℤ) → ℝ3)
      = Set.range (latVec : (Fin 3 → ℤ) → ℝ3) := by
    ext y
    constructor
    · rintro ⟨x, ⟨m, rfl⟩, rfl⟩
      exact ⟨m + n, by rw [latVec_add]⟩
    · rintro ⟨k, rfl⟩
      exact ⟨latVec (k - n), ⟨k - n, rfl⟩, by rw [latVec_sub]; abel⟩
  have h := Metric.infDist_image (isometry_add_right (latVec n)) (x := u - latVec n)
    (t := Set.range (latVec : (Fin 3 → ℤ) → ℝ3))
  rw [hset] at h
  have hsub : u - latVec n + latVec n = u := by abel
  rw [hsub] at h
  exact h.symm

/-- **On the fundamental cell the nearest lattice point is the origin**, so the distance to the
lattice is the Euclidean norm. -/
lemma infDist_eq_norm_of_cell {u : ℝ3} (hcell : ∀ i, |u i| ≤ 1 / 2) :
    Metric.infDist u (Set.range (latVec : (Fin 3 → ℤ) → ℝ3)) = ‖u‖ := by
  refine le_antisymm ?_ ?_
  · calc Metric.infDist u (Set.range (latVec : (Fin 3 → ℤ) → ℝ3)) ≤ dist u 0 :=
        Metric.infDist_le_dist_of_mem ⟨0, latVec_zero⟩
      _ = ‖u‖ := by rw [dist_eq_norm, sub_zero]
  · refine (Metric.le_infDist (s := Set.range (latVec : (Fin 3 → ℤ) → ℝ3))
      ⟨(0 : ℝ3), ⟨(0 : Fin 3 → ℤ), latVec_zero⟩⟩).mpr ?_
    rintro y ⟨m, hm⟩
    rw [← hm, dist_eq_norm]
    have hsq : ‖u‖ ^ 2 ≤ ‖u - latVec m‖ ^ 2 := norm_sub_latVec_sq_ge hcell m
    calc ‖u‖ = Real.sqrt (‖u‖ ^ 2) := (Real.sqrt_sq (norm_nonneg u)).symm
      _ ≤ Real.sqrt (‖u - latVec m‖ ^ 2) := Real.sqrt_le_sqrt hsq
      _ = ‖u - latVec m‖ := Real.sqrt_sq (norm_nonneg _)

/-- The Green's function bound **on the fundamental cell**: the free propagator plus the
(nonpositive) Madelung correction. -/
lemma latGreen_le_inv_fourpi_norm_of_cell {u : ℝ3} (hu : u ≠ 0)
    (hcell : ∀ i, |u i| ≤ 1 / 2) :
    latGreen u ≤ 1 / (4 * Real.pi * ‖u‖) := by
  have h := madelung_smooth_nonpos hu hcell
  unfold latGreenSmooth at h
  linarith

/-- At `u = 0` the periodised heat kernel dominates the free heat kernel. -/
lemma heatK3_le_heatPeriod_zero {t : ℝ} (ht : 0 < t) : heatK3 t 0 ≤ heatPeriod t 0 := by
  have hgs : Summable (fun n : Fin 3 → ℤ => Real.exp (-‖(0 : ℝ3) - latVec n‖ ^ 2 / (4 * t))) :=
    GaussSummable ht 0
  have hsum : Summable (fun n : Fin 3 → ℤ => heatK3 t (0 - latVec n)) := by
    refine (hgs.mul_left ((4 * Real.pi * t) ^ (-(3 / 2 : ℝ)))).congr (fun n => ?_)
    rw [heatK3]
  have hle := hsum.le_tsum (0 : Fin 3 → ℤ) (fun n _ => heatK3_nonneg ht (0 - latVec n))
  simpa [heatPeriod, latVec_zero] using hle

/-- The defining integrand of `latGreen` at a lattice point is **not integrable** on `(0,∞)`:
near `t = 0` it dominates `c · t^{-3/2}`. -/
lemma not_integrable_heatPeriod_zero :
    ¬ Integrable (fun t : ℝ => heatPeriod t 0 - 1) (volume.restrict (Ioi (0 : ℝ))) := by
  intro hint
  set c : ℝ := (1 / 2) * (4 * Real.pi) ^ (-(3 / 2 : ℝ)) with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  have h1 : IntegrableOn (fun t : ℝ => heatPeriod t 0 - 1) (Ioo 0 (1 / 100)) :=
    IntegrableOn.mono_set hint Ioo_subset_Ioi_self
  have h2 : IntegrableOn (fun t : ℝ => c * t ^ (-(3 / 2 : ℝ))) (Ioo 0 (1 / 100)) := by
    refine Integrable.mono' h1 ?_ ?_
    · have hcont : ContinuousOn (fun t : ℝ => c * t ^ (-(3 / 2 : ℝ))) (Ioo 0 (1 / 100)) :=
        continuousOn_const.mul
          (continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt ht.1)))
      exact hcont.aestronglyMeasurable measurableSet_Ioo
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      have ht0 : 0 < t := ht.1
      have htle : t ≤ 1 / 100 := ht.2.le
      rw [Real.norm_of_nonneg (by positivity)]
      have hw : 0 < 4 * Real.pi * t := by positivity
      have hwle : 4 * Real.pi * t ≤ 1 / 2 := by
        have h4pi : 4 * Real.pi ≤ 16 := by linarith [Real.pi_lt_d20]
        calc 4 * Real.pi * t ≤ 16 * t := mul_le_mul_of_nonneg_right h4pi ht0.le
          _ ≤ 16 * (1 / 100) := mul_le_mul_of_nonneg_left htle (by norm_num)
          _ ≤ 1 / 2 := by norm_num
      have hhalf : (1 / 2 : ℝ) ^ (3 / 2 : ℝ) ≤ 1 / 2 := by
        rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
          Real.rpow_add (by norm_num : (0 : ℝ) < 1 / 2), Real.rpow_one, ← Real.sqrt_eq_rpow]
        have hone : Real.sqrt (1 / 2) ≤ 1 := by
          have := Real.sqrt_le_sqrt (show (1 / 2 : ℝ) ≤ 1 by norm_num)
          rwa [Real.sqrt_one] at this
        nlinarith [hone]
      have hA : (2 : ℝ) ≤ (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) := by
        have hpos : 0 < (4 * Real.pi * t) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hw _
        have hfin : (4 * Real.pi * t) ^ (3 / 2 : ℝ) ≤ 1 / 2 :=
          le_trans (Real.rpow_le_rpow hw.le hwle (by norm_num)) hhalf
        rw [Real.rpow_neg hw.le]
        have := (inv_le_inv₀ (show (0 : ℝ) < 1 / 2 by norm_num) hpos).mpr hfin
        norm_num at this
        exact this
      have hK : heatK3 t 0 = (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) := by simp [heatK3]
      have hmul : (4 * Real.pi * t) ^ (-(3 / 2 : ℝ))
          = (4 * Real.pi) ^ (-(3 / 2 : ℝ)) * t ^ (-(3 / 2 : ℝ)) := by
        rw [show 4 * Real.pi * t = (4 * Real.pi) * t by ring]
        exact Real.mul_rpow (by positivity) ht0.le
      have hKP := heatK3_le_heatPeriod_zero ht0
      calc c * t ^ (-(3 / 2 : ℝ))
          = (1 / 2) * (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) := by rw [hc, hmul]; ring
        _ ≤ (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) - 1 := by linarith
        _ ≤ heatPeriod t 0 - 1 := by rw [← hK]; linarith
  have h3 : IntegrableOn (fun t : ℝ => t ^ (-(3 / 2 : ℝ))) (Ioo 0 (1 / 100)) := by
    refine (h2.const_mul c⁻¹).congr (Filter.Eventually.of_forall fun t => ?_)
    show c⁻¹ * (c * t ^ (-(3 / 2 : ℝ))) = t ^ (-(3 / 2 : ℝ))
    rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hcpos), one_mul]
  have h4 := (intervalIntegral.integrableOn_Ioo_rpow_iff (s := -(3 / 2 : ℝ))
    (show (0 : ℝ) < 1 / 100 by norm_num)).mp h3
  norm_num at h4

/-- At a lattice point the lattice Green's function is `0` (Lean's convention: the defining
integral is that of a non-integrable function). -/
lemma latGreen_latVec_eq_zero (n : Fin 3 → ℤ) : latGreen (latVec n) = 0 := by
  have hper : latGreen (latVec n) = latGreen (0 : ℝ3) := by
    have h := latGreen_periodic (0 : ℝ3) n
    rwa [zero_add] at h
  rw [hper]
  unfold latGreen
  exact integral_undef not_integrable_heatPeriod_zero

theorem latGreen_le_inv_fourpi_infDist {u : EuclideanSpace ℝ (Fin 3)} (hu : u ≠ 0) :
    latGreen u ≤ 1 / (4 * Real.pi * Metric.infDist u
      (Set.range (latVec : (Fin 3 → ℤ) → EuclideanSpace ℝ (Fin 3)))) := by
  by_cases hmem : u ∈ Set.range (latVec : (Fin 3 → ℤ) → EuclideanSpace ℝ (Fin 3))
  · obtain ⟨n, rfl⟩ := hmem
    have hz : Metric.infDist (latVec n)
        (Set.range (latVec : (Fin 3 → ℤ) → EuclideanSpace ℝ (Fin 3))) = 0 :=
      Metric.infDist_zero_of_mem ⟨n, rfl⟩
    rw [latGreen_latVec_eq_zero n, hz]
    norm_num
  · obtain ⟨n, hn⟩ := exists_cell_rep u
    have hw : u - latVec n ≠ 0 := by
      intro h
      exact hmem ⟨n, (sub_eq_zero.mp h).symm⟩
    have hcell : ∀ i, |(u - latVec n) i| ≤ 1 / 2 := fun i => by
      simpa only [WithLp.ofLp_sub, Pi.sub_apply, latVec_apply] using hn i
    have hlat : latGreen u = latGreen (u - latVec n) := by
      conv_lhs => rw [show u = (u - latVec n) + latVec n by abel]
      rw [latGreen_periodic]
    have hdist : ‖u - latVec n‖
        = Metric.infDist u (Set.range (latVec : (Fin 3 → ℤ) → EuclideanSpace ℝ (Fin 3))) := by
      rw [← infDist_eq_norm_of_cell hcell, infDist_sub_latVec u n]
    rw [hlat, ← hdist]
    exact latGreen_le_inv_fourpi_norm_of_cell hw hcell

end Work.BoseFixR.LatGreen
