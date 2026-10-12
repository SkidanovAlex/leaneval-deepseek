import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.RadialTest
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Radial profile a.e. equality transfers from `(R, ∞)` to the 3D exterior

Assigned sub-lemma (Layer 3, `exterior_harmonic_classification`):

    ae_eq_div_norm_of_radial_profile_ae {w : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R)
      (hrad : IsRadial w) {c : ℝ}
      (hprof : ∀ᵐ r : ℝ, R < r → radialProfile w r = c / r) :
      ∀ᵐ x : ℝ³, R ≤ ‖x‖ → w x = c / ‖x‖

If the radial profile of a radial `w` equals `c/r` almost everywhere on
`(R, ∞)`, then `w x = c / ‖x‖` almost everywhere on the exterior
`{x | R ≤ ‖x‖}`.

## Proof route (for the implementer)

Let `N : Set ℝ := {r | R < r ∧ radialProfile w r ≠ c / r}` (the 1D bad
set).  From `hprof` (via `MeasureTheory.ae_iff` and monotonicity of measure)
`(volume : Measure ℝ) N = 0`.

Because `w` is radial (`radial_eq_profile`), for `x` with `R < ‖x‖` we have
`w x = radialProfile w ‖x‖` and `‖x‖ ∈ (0, ∞)`, so the 3D bad set

    bad := {x : ℝ³ | R ≤ ‖x‖ ∧ w x ≠ c / ‖x‖}

is contained in `{x | ‖x‖ ∈ N} ∪ {x | ‖x‖ = R}`.  The sphere
`{x | ‖x‖ = R} = Metric.sphere (0 : ℝ³) R` has zero volume
(`Submission.BoseGases.volume_sphere_r3`, imported via
`Submission.RadialIntegral` through `Submission.RadialTest`).

It remains to show `(volume : Measure ℝ³) {x : ℝ³ | ‖x‖ ∈ N} = 0` for a null
`N ⊆ (0, ∞)`.  Recommended chain:

1. Replace `N` by its measurable hull `N̂ := MeasureTheory.toMeasurable
   (volume : Measure ℝ) N`: `N ⊆ N̂`, `MeasurableSet N̂` and
   `(volume) N̂ = (volume) N = 0` (`subset_toMeasurable`,
   `measurableSet_toMeasurable`, `measure_toMeasurable`).

2. Cover `{x | ‖x‖ ∈ N̂}` by the countable family over `k : ℕ` of bounded
   pieces `{x : ℝ³ | ‖x‖ ∈ N̂ ∧ ‖x‖ < (k : ℝ)}`; every element is covered
   (e.g. `exists_nat_gt`), and a countable union of null sets is null
   (`MeasureTheory.measure_iUnion_null`, monotonicity).

3. **Bounded core.**  For `a ≥ 0`, a *measurable* null `S ⊆ Set.Iio a`
   (bounded above), `(volume : Measure ℝ³) {x | ‖x‖ ∈ S} = 0`:
   - let `T := {x : ℝ³ | ‖x‖ ∈ S}` (measurable: preimage of a measurable
     set under the measurable/continuous norm; `T ⊆ closedBall 0 a` so its
     volume is `< ⊤`);
   - compute `∫ x : ℝ³, T.indicator (fun _ => (1 : ℝ)) x` in two ways:
     by `MeasureTheory.integral_indicator` it is `(volume T).toReal`
     (`MeasureTheory.setIntegral_const`, `MeasureTheory.measureReal_def`);
     and pointwise `T.indicator (fun _ => (1 : ℝ)) x =
       g ‖x‖` with `g : ℝ → ℝ := S.indicator (fun _ => (1 : ℝ))`, so by
     `Submission.BoseGases.integral_fun_norm_r3`
     (`(∫ x : ℝ³, g ‖x‖) = 4 * π * (∫ r in Set.Ioi (0 : ℝ), r ^ 2 * g r)`)
     it equals `4 * π * 0 = 0` because `S` is null makes the integrand
     a.e. zero (`MeasureTheory.integral_eq_zero_of_ae`);
   - conclude with `ENNReal.toReal_eq_zero_iff` plus finiteness, or by
     showing the indicator is a.e. zero.
-/

noncomputable section

open _root_.BoseGases
set_option autoImplicit false

namespace Submission.BoseGases

open Filter Metric MeasureTheory Laplacian
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **Bounded core.** If `S ⊆ Iio a` (with `0 ≤ a`) is a *measurable* null
set of radii, then its preimage under the norm has zero volume in `ℝ³`. -/
lemma volume_preimage_norm_bounded_null_r3 {a : ℝ} (ha : 0 ≤ a) {S : Set ℝ}
    (hSmeas : MeasurableSet S) (hSb : S ⊆ Set.Iio a)
    (hSvol : (volume : Measure ℝ) S = 0) :
    (volume : Measure ℝ³) {x : ℝ³ | ‖x‖ ∈ S} = 0 := by
  let U : Set ℝ³ := {x : ℝ³ | ‖x‖ ∈ S}
  let g : ℝ → ℝ := S.indicator (fun _ : ℝ => (1 : ℝ))
  have hUmeas : MeasurableSet U := by
    dsimp [U]
    exact hSmeas.preimage continuous_norm.measurable
  have hUsub : U ⊆ Metric.closedBall (0 : ℝ³) a := by
    intro x hx
    have hxa : ‖x‖ < a := hSb hx
    have hle : ‖x‖ ≤ a := le_of_lt hxa
    simpa [Metric.mem_closedBall, dist_zero_right] using hle
  have hUfinite : (volume : Measure ℝ³) U ≠ ⊤ := by
    have hvolball : (volume : Measure ℝ³) (Metric.closedBall (0 : ℝ³) a) =
        ENNReal.ofReal ((4 / 3) * π * a ^ 3) := volume_ball_r3 a ha
    have hfin : (volume : Measure ℝ³) (Metric.closedBall (0 : ℝ³) a) ≠ ⊤ := by
      rw [hvolball]
      exact ENNReal.ofReal_ne_top
    exact ne_top_of_le_ne_top hfin (measure_mono hUsub)
  -- integral of the indicator of U equals measureReal U ...
  have hLHS : (∫ x : ℝ³, U.indicator (fun _ : ℝ³ => (1 : ℝ)) x) =
      (volume : Measure ℝ³).real U := by
    rw [integral_indicator (s := U) (f := fun _ : ℝ³ => (1 : ℝ))
      (μ := (volume : Measure ℝ³)) hUmeas]
    rw [setIntegral_const (c := (1 : ℝ)) (s := U) (μ := (volume : Measure ℝ³))]
    simp
  -- ... and equals the radial integral of g = indicator of S
  have hpoint : (fun x : ℝ³ => U.indicator (fun _ : ℝ³ => (1 : ℝ)) x) =
      (fun x : ℝ³ => g ‖x‖) := by
    funext x
    by_cases hx : x ∈ U
    · have hnx : ‖x‖ ∈ S := by simpa [U] using hx
      simp [hx, hnx, g]
    · have hnx : ‖x‖ ∉ S := by
        intro hs
        exact hx (by simpa [U] using hs)
      simp [hx, hnx, g]
  have hg0 : g =ᵐ[(volume : Measure ℝ)] (fun _ : ℝ => (0 : ℝ)) := by
    change ∀ᵐ (r : ℝ) ∂(volume : Measure ℝ), g r = (0 : ℝ)
    rw [MeasureTheory.ae_iff]
    have hset : {r : ℝ | g r ≠ 0} = S := by
      ext r
      by_cases hr : r ∈ S
      · simp [g, hr]
      · simp [g, hr]
    rw [hset]
    exact hSvol
  have hI0 : (∫ r in Set.Ioi (0 : ℝ), r ^ 2 * g r) = 0 := by
    calc
      (∫ r in Set.Ioi (0 : ℝ), r ^ 2 * g r)
          = ∫ r in Set.Ioi (0 : ℝ), (0 : ℝ) := by
            refine MeasureTheory.setIntegral_congr_ae (s := Set.Ioi (0 : ℝ))
              (f := fun r : ℝ => r ^ 2 * g r) (g := fun _ : ℝ => (0 : ℝ))
              (μ := (volume : Measure ℝ)) ?_ ?_
            · measurability
            · filter_upwards [hg0] with r hr
              intro _
              simp [hr]
      _ = 0 := by simp
  have hRHS : (∫ x : ℝ³, g ‖x‖) = 4 * π * (∫ r in Set.Ioi (0 : ℝ), r ^ 2 * g r) :=
    integral_fun_norm_r3 (g := g)
  have hMain : (∫ x : ℝ³, U.indicator (fun _ : ℝ³ => (1 : ℝ)) x) = 0 := by
    calc
      (∫ x : ℝ³, U.indicator (fun _ : ℝ³ => (1 : ℝ)) x) = ∫ x : ℝ³, g ‖x‖ := by
        rw [hpoint]
      _ = 4 * π * (∫ r in Set.Ioi (0 : ℝ), r ^ 2 * g r) := hRHS
      _ = 4 * π * 0 := by rw [hI0]
      _ = 0 := by norm_num
  have htoReal0 : (volume : Measure ℝ³).real U = 0 := by
    rw [← hLHS]
    exact hMain
  rw [measureReal_def] at htoReal0
  rw [ENNReal.toReal_eq_zero_iff] at htoReal0
  exact htoReal0.resolve_right hUfinite

/-- If a measurable set of radii is null, then its preimage under the norm
has zero volume in `ℝ³` (no boundedness needed: split into the countably many
bounded pieces `{‖x‖ < k}`, each handled by
`volume_preimage_norm_bounded_null_r3`). -/
lemma volume_preimage_norm_null_r3 {S : Set ℝ} (hSmeas : MeasurableSet S)
    (hSvol : (volume : Measure ℝ) S = 0) :
    (volume : Measure ℝ³) {x : ℝ³ | ‖x‖ ∈ S} = 0 := by
  let piece : ℕ → Set ℝ³ := fun k => {x : ℝ³ | ‖x‖ ∈ S ∧ ‖x‖ < (k : ℝ)}
  have hcover : {x : ℝ³ | ‖x‖ ∈ S} ⊆ ⋃ k : ℕ, piece k := by
    intro x hx
    rcases exists_nat_gt ‖x‖ with ⟨k, hk⟩
    exact Set.mem_iUnion.mpr ⟨k, ⟨hx, hk⟩⟩
  have hpiece_null : ∀ k : ℕ, (volume : Measure ℝ³) (piece k) = 0 := by
    intro k
    let Sₖ : Set ℝ := S ∩ Set.Iio (k : ℝ)
    have hSₖmeas : MeasurableSet Sₖ := hSmeas.inter measurableSet_Iio
    have hSₖvol : (volume : Measure ℝ) Sₖ = 0 :=
      measure_mono_null (Set.inter_subset_left) hSvol
    have hpiece_eq : piece k = {x : ℝ³ | ‖x‖ ∈ Sₖ} := by
      ext x
      simp [piece, Sₖ]
    rw [hpiece_eq]
    exact volume_preimage_norm_bounded_null_r3 (a := (k : ℝ))
      (by exact_mod_cast Nat.zero_le k) hSₖmeas (Set.inter_subset_right) hSₖvol
  have hunion_null : (volume : Measure ℝ³) (⋃ k : ℕ, piece k) = 0 :=
    measure_iUnion_null hpiece_null
  exact measure_mono_null hcover hunion_null

/-- If a radial function's profile is `c/r` a.e. on `(R, ∞)` with `R > 0`,
then the function itself is `c/‖x‖` a.e. on the exterior `{x | R ≤ ‖x‖}`. -/
theorem ae_eq_div_norm_of_radial_profile_ae {w : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R)
    (hrad : IsRadial w) {c : ℝ}
    (hprof : ∀ᵐ r : ℝ, R < r → radialProfile w r = c / r) :
    ∀ᵐ x : ℝ³, R ≤ ‖x‖ → w x = c / ‖x‖ := by
  -- keep the positivity hypothesis in scope (interface compatibility)
  have _hRpos : 0 < R := hR
  -- the 1D bad set
  let N : Set ℝ := {r : ℝ | R < r ∧ radialProfile w r ≠ c / r}
  have hNvol0 : (volume : Measure ℝ) N = 0 := by
    have hgood : (volume : Measure ℝ) {r : ℝ | ¬(R < r → radialProfile w r = c / r)} = 0 :=
      MeasureTheory.ae_iff.mp hprof
    refine measure_mono_null (s := N)
      (t := {r : ℝ | ¬(R < r → radialProfile w r = c / r)}) ?_ hgood
    intro r hr
    rcases hr with ⟨hrR, hrne⟩
    intro hf
    exact hrne (hf hrR)
  -- replace N by its measurable hull S
  let S : Set ℝ := MeasureTheory.toMeasurable (volume : Measure ℝ) N
  have hSmeas : MeasurableSet S := MeasureTheory.measurableSet_toMeasurable (volume : Measure ℝ) N
  have hNS : N ⊆ S := MeasureTheory.subset_toMeasurable (volume : Measure ℝ) N
  have hSvol0 : (volume : Measure ℝ) S = 0 := by
    rw [MeasureTheory.measure_toMeasurable]
    exact hNvol0
  -- preimage of S under the norm is null in ℝ³
  let T : Set ℝ³ := {x : ℝ³ | ‖x‖ ∈ S}
  have hTvol0 : (volume : Measure ℝ³) T = 0 := by
    dsimp [T]
    exact volume_preimage_norm_null_r3 hSmeas hSvol0
  -- 3D bad set ⊆ T ∪ sphere
  let bad : Set ℝ³ := {x : ℝ³ | R ≤ ‖x‖ ∧ w x ≠ c / ‖x‖}
  have hbad_sub : bad ⊆ T ∪ Metric.sphere (0 : ℝ³) R := by
    intro x hx
    rcases hx with ⟨hRle, hw⟩
    by_cases hxR : ‖x‖ = R
    · right
      simpa [Metric.mem_sphere, dist_zero_right] using hxR
    · left
      have hxRgt : R < ‖x‖ := lt_of_le_of_ne hRle (Ne.symm hxR)
      have hwprof : w x = radialProfile w ‖x‖ := radial_eq_profile hrad x
      have hNmem : ‖x‖ ∈ N := by
        refine ⟨hxRgt, ?_⟩
        intro h
        rw [← hwprof] at h
        exact hw h
      dsimp [T]
      exact hNS hNmem
  have hbadvol : (volume : Measure ℝ³) bad = 0 := by
    have hspTvol : (volume : Measure ℝ³) (T ∪ Metric.sphere (0 : ℝ³) R) = 0 := by
      exact measure_union_null hTvol0 (volume_sphere_r3 R)
    exact measure_mono_null hbad_sub hspTvol
  -- conclusion via ae_iff
  rw [MeasureTheory.ae_iff]
  have hseteq : {x : ℝ³ | ¬(R ≤ ‖x‖ → w x = c / ‖x‖)} = bad := by
    ext x
    constructor
    · intro h
      constructor
      · by_contra hRle
        exact h (fun hRle' => False.elim (hRle hRle'))
      · intro hEq
        exact h (fun _ => hEq)
    · intro h hEq
      exact h.2 (hEq h.1)
  rw [hseteq]
  exact hbadvol

end Submission.BoseGases
