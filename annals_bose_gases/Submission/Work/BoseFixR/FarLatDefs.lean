import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixR.LatGreen.CellDefs
import Submission.Work.BoseFixR.LatGreen.LatGreenAutocorrAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.FarLatDefs` — the `ℓ`-lattice distance and the finite window of lattice points

Vocabulary shared by `Work.BoseFixR.farLatParseval` (the target) and its delegated pieces:

* `latDistL ℓ z = dist(z, ℓℤ³)` — the distance to the `ℓ`-lattice, i.e. exactly the
  `Metric.infDist z (Set.range (fun n => lat ℓ n))` of the target's right-hand side;
* its elementary properties: nonnegativity, vanishing on the lattice, `ℓℤ³`-**periodicity**
  (this is what makes the periodisation/Fubini step work), and the scaling identity
  `latDistL ℓ z = ℓ * latDist (ℓ⁻¹ • z)` relating it to the unit-lattice distance
  `Work.BoseFixR.LatGreen.latDist`;
* `latFin9` — the fixed finite window `{p : ℤ³ | |p i| ≤ 4}` of lattice labels.  On the double
  cell `cell (2ℓ)` the *nearest* `ℓ`-lattice point has its label in `latFin9` (the reciprocal
  distance is the *maximum* of the reciprocals `1/‖z - lat ℓ p‖`, so the finite window turns the
  singular periodic kernel `1/latDistL` into a finite sum of *translation-invariant* Coulomb
  kernels — each of which is then paid by the a.e. bound on the Coulomb potential of
  `wScaled ℓ (g0 v h)`).
-/

noncomputable section

open scoped Real BigOperators Pointwise
open MeasureTheory Set

namespace Work.BoseFixR

/-- The distance to the `ℓ`-lattice `ℓℤ³`.  This is *verbatim* the expression
`Metric.infDist z (Set.range (fun n : Fin 3 → ℤ => lat ℓ n))` occurring in the target
`Work.BoseFixR.farLatParseval`. -/
noncomputable def latDistL (ℓ : ℝ) (z : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  Metric.infDist z (Set.range (fun n : Fin 3 → ℤ => Work.BoseFixR.lat ℓ n))

lemma latDistL_nonneg (ℓ : ℝ) (z : EuclideanSpace ℝ (Fin 3)) : 0 ≤ latDistL ℓ z :=
  Metric.infDist_nonneg

lemma latDistL_zero (ℓ : ℝ) : latDistL ℓ (0 : EuclideanSpace ℝ (Fin 3)) = 0 :=
  Metric.infDist_zero_of_mem ⟨0, by simp [Work.BoseFixR.lat_zero]⟩

lemma latDistL_lat (ℓ : ℝ) (n : Fin 3 → ℤ) : latDistL ℓ (Work.BoseFixR.lat ℓ n) = 0 :=
  Metric.infDist_zero_of_mem ⟨n, rfl⟩

/-- **The distance to the `ℓ`-lattice is `ℓℤ³`-periodic.** -/
lemma latDistL_period (ℓ : ℝ) (z : EuclideanSpace ℝ (Fin 3)) (n : Fin 3 → ℤ) :
    latDistL ℓ (z + Work.BoseFixR.lat ℓ n) = latDistL ℓ z := by
  have hset : (fun x : EuclideanSpace ℝ (Fin 3) => x + Work.BoseFixR.lat ℓ n) ''
      Set.range (fun m : Fin 3 → ℤ => Work.BoseFixR.lat ℓ m)
      = Set.range (fun m : Fin 3 → ℤ => Work.BoseFixR.lat ℓ m) := by
    ext y
    constructor
    · rintro ⟨x, ⟨m, rfl⟩, rfl⟩
      exact ⟨m + n, Work.BoseFixR.lat_add ℓ m n⟩
    · rintro ⟨m, rfl⟩
      exact ⟨Work.BoseFixR.lat ℓ (m - n), ⟨m - n, rfl⟩, by
        rw [show Work.BoseFixR.lat ℓ (m - n) = Work.BoseFixR.lat ℓ m - Work.BoseFixR.lat ℓ n
          from map_sub (Work.BoseFixR.latHom ℓ) m n]
        abel⟩
  have h := Metric.infDist_image (isometry_add_right (Work.BoseFixR.lat ℓ n))
    (x := z) (t := Set.range (fun m : Fin 3 → ℤ => Work.BoseFixR.lat ℓ m))
  rw [hset] at h
  show Metric.infDist (z + Work.BoseFixR.lat ℓ n) _ = Metric.infDist z _
  rw [← h]

/-- The unit lattice vector `latVec` of `LatGreen` is `lat 1`. -/
lemma latVec_eq_lat_one (n : Fin 3 → ℤ) : LatGreen.latVec n = Work.BoseFixR.lat 1 n := by
  ext i
  simp [LatGreen.latVec, Work.BoseFixR.lat]

/-- **Scaling of the lattice distance**: `dist(ℓz, ℓℤ³) = ℓ · dist(z, ℤ³)`. -/
lemma latDistL_eq_mul_latDist {ℓ : ℝ} (hℓ : 0 < ℓ) (z : EuclideanSpace ℝ (Fin 3)) :
    latDistL ℓ z = ℓ * LatGreen.latDist (ℓ⁻¹ • z) := by
  have hset : ℓ • Set.range (fun n : Fin 3 → ℤ => LatGreen.latVec n)
      = Set.range (fun n : Fin 3 → ℤ => Work.BoseFixR.lat ℓ n) := by
    rw [Set.smul_set_range]
    refine congrArg Set.range (funext (fun n => ?_))
    ext i
    simp [LatGreen.latVec, Work.BoseFixR.lat]
  have h := infDist_smul₀ (x := ℓ⁻¹ • z)
    (s := Set.range (fun n : Fin 3 → ℤ => LatGreen.latVec n)) hℓ.ne'
  rw [hset, smul_inv_smul₀ hℓ.ne', Real.norm_of_nonneg hℓ.le] at h
  show Metric.infDist z (Set.range (fun n : Fin 3 → ℤ => lat ℓ n))
    = ℓ * Metric.infDist (ℓ⁻¹ • z) (Set.range (fun n : Fin 3 → ℤ => LatGreen.latVec n))
  rw [← h]

/-- The fixed finite window `{p : ℤ³ | |p i| ≤ 4}` of lattice labels. -/
def latFin9 : Finset (Fin 3 → ℤ) := Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-4) 4)

/-! ## 3. The scaled Madelung bound and the a.e. positivity of the periodisation -/

/-- **The scaled sharp nearest-image bound**: `ℓ²·latGreen(ℓ⁻¹z) ≤ (ℓ³/4π)·dist(z, ℓℤ³)⁻¹`. -/
lemma latGreen_scaled_le {ℓ : ℝ} (hℓ : 0 < ℓ) (z : EuclideanSpace ℝ (Fin 3)) :
    ℓ ^ 2 * LatGreen.latGreen (ℓ⁻¹ • z)
      ≤ (ℓ ^ 3 / (4 * Real.pi)) * (latDistL ℓ z)⁻¹ := by
  have h := LatGreen.latGreen_le_inv_latDist (ℓ⁻¹ • z)
  have hscale : LatGreen.latDist (ℓ⁻¹ • z)
      = ℓ⁻¹ * latDistL ℓ z := by
    rw [latDistL_eq_mul_latDist hℓ z]
    field_simp
  rw [hscale] at h
  calc ℓ ^ 2 * LatGreen.latGreen (ℓ⁻¹ • z)
      ≤ ℓ ^ 2 * (4 * Real.pi * (ℓ⁻¹ * latDistL ℓ z))⁻¹ :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = (ℓ ^ 3 / (4 * Real.pi)) * (latDistL ℓ z)⁻¹ := by
        rw [mul_inv, show (ℓ⁻¹ * latDistL ℓ z)⁻¹
            = ℓ * (latDistL ℓ z)⁻¹ by rw [mul_inv, inv_inv]]
        ring

/-- **The periodisation of an a.e. nonnegative charge is a.e. nonnegative.** -/
lemma period_nonneg_ae {ℓ : ℝ} {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hWnn : 0 ≤ᵐ[MeasureTheory.volume] W) :
    0 ≤ᵐ[MeasureTheory.volume] LatGreen.period W ℓ := by
  have h1 : ∀ᵐ x : EuclideanSpace ℝ (Fin 3),
      ∀ n : Fin 3 → ℤ, 0 ≤ W (x - lat ℓ n) := by
    rw [MeasureTheory.ae_all_iff]
    intro n
    exact (MeasureTheory.measurePreserving_sub_right MeasureTheory.volume
      (lat ℓ n)).quasiMeasurePreserving.ae hWnn
  filter_upwards [h1] with x hx
  exact tsum_nonneg hx

end Work.BoseFixR
