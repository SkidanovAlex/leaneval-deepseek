import Mathlib
import Submission.Finish
import Submission.Commons.Lattice.Packing.exists_ellipsoid_of_lattice
import Submission.Commons.Lattice.MinkowskiHlawka.minkowski_hlawka

/-!
# Klartag's construction of lattice sphere packings: the assembly layer

This file contains the elementary ("assembly") part of the proof of Klartag's theorem on
lattice sphere packings, together with a precise statement of the deep input.

* `omega d` : the volume of the open unit ball of `ℝ^d`.
* `LatticeFree φ` : the image of the open unit ball under `φ` contains no nonzero integer point.
* `latticeFree_smul` : lattice-freeness is preserved by contracting `φ` (shrinking the ellipsoid).
* `volume_image` : the volume of `φ '' ball 0 1` equals `|det φ| * omega d`.
* `exists_exact` : an ellipsoid of volume `≥ c (d-1)^2` can be contracted to one of volume
  exactly `c (d-1)^2`, remaining lattice-free.
* `exists_latticeFree_volume_quarter` : rung 1 (Minkowski–Hlawka) in ellipsoid form, proved
  from the commons: a lattice-free ellipsoid of volume `≥ 1/4` in every dimension `d ≥ 2`.
* `klartag_lattice_large` : **the deep input**, in the lattice ("density") form, for large
  dimensions: for every `d ≥ D` there is a lattice of minimum norm `≥ 1` and covolume
  `≤ ω_d / (c (d-1)^2)`.  This is Klartag's theorem (2025); by the duality between lattice
  packings and lattice-free ellipsoids it is equivalent to the statement below.
* `klartag_density_large` : the same input in ellipsoid/linear-map form, derived from
  `klartag_lattice_large` via `Commons.Lattice.Packing.exists_ellipsoid_of_lattice`.
* `klartag_density` : the input in ellipsoid form for all `d ≥ 2`, obtained by combining
  `klartag_density_large` with rung 1 for the finitely many small dimensions.
* `klartag_of_density` : the target theorem, assembled from the deep input.

**This file is now complete** (no `sorry`): the deep input `klartag_lattice_large` is obtained
from `Submission.Finish.klartag_lattice_large_om`, the completion of Klartag's construction
(the exploration process of `Submission.PLAN_V4.md`, the sharp contact estimate of
`Submission.PLAN_V10/V11.md`, and the final rescaling).  In particular `klartag_density`
combines the large-dimensional input with rung 1 (Minkowski–Hlawka) for the finitely many small
dimensions.
-/

namespace Submission.Helpers

open MeasureTheory Metric

noncomputable section

/-- Volume of the open unit ball of `ℝ^d`. -/
def omega (d : ℕ) : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal

lemma omega_pos {d : ℕ} (hd : 0 < d) : 0 < omega d := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  rw [omega]
  refine ENNReal.toReal_pos ?_ ?_
  · exact (Metric.measure_ball_pos (μ := volume) _ (by norm_num)).ne'
  · rw [EuclideanSpace.volume_ball]
    simp

lemma volume_ball_unit {d : ℕ} (hd : 0 < d) :
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) = ENNReal.ofReal (omega d) := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  rw [omega, ENNReal.ofReal_toReal]
  rw [EuclideanSpace.volume_ball]
  simp

/-- A linear endomorphism of `ℝ^d` is *lattice-free* if the image of the open unit ball
contains no nonzero integer point. -/
def LatticeFree {d : ℕ} (φ : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ y, ‖y‖ < 1 → (∀ i, (φ y) i ∈ Set.range ((↑) : ℤ → ℝ)) → φ y = 0

/-- The set form and the pointwise form of lattice-freeness agree. -/
lemma latticeFree_iff {d : ℕ}
    (φ : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) :
    LatticeFree φ ↔ {v ∈ φ '' Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1 |
        ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0} := by
  constructor
  · intro h
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_image, Set.mem_singleton_iff, Metric.mem_ball, dist_zero_right]
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hint⟩
      exact h y hy hint
    · rintro rfl
      exact ⟨⟨0, by simp, by simp⟩, fun i => ⟨0, by simp⟩⟩
  · intro h y hy hint
    have : φ y ∈ {v ∈ φ '' Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1 |
        ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} :=
      ⟨⟨y, by simpa [Metric.mem_ball, dist_zero_right] using hy, rfl⟩, hint⟩
    rw [h] at this
    simpa using this

/-- Contracting a lattice-free map keeps it lattice-free. -/
lemma latticeFree_smul {d : ℕ} {φ : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)}
    (h : LatticeFree φ) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) : LatticeFree (t • φ) := by
  intro y hy hint
  have hty : ‖t • y‖ < 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
    nlinarith [norm_nonneg y]
  have heq : φ (t • y) = (t • φ) y := by simp [map_smul]
  have key : φ (t • y) = 0 := by
    refine h (t • y) hty ?_
    intro i
    rw [heq]
    exact hint i
  have : t • φ y = 0 := by simpa [map_smul] using key
  have hzero : φ y = 0 := (smul_eq_zero.mp this).resolve_left (ne_of_gt ht0)
  simpa [map_smul, hzero]

/-- The volume of the ellipsoid `φ '' ball 0 1`. -/
lemma volume_image {d : ℕ} (hd : 0 < d)
    (φ : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) :
    volume (φ '' Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)
      = ENNReal.ofReal (|LinearMap.det φ| * omega d) := by
  rw [MeasureTheory.Measure.addHaar_image_linearMap (μ := volume) φ,
    volume_ball_unit hd, ← ENNReal.ofReal_mul (abs_nonneg _)]

/-- **Scaling to an exact volume.** Given a lattice-free ellipsoid of volume at least
`c (d-1)^2` one obtains a lattice-free ellipsoid of volume exactly `c (d-1)^2`,
by contracting it (which keeps it free of nonzero lattice points). -/
lemma exists_exact {d : ℕ} (hd : 2 ≤ d) {c : ℝ} (hc : 0 < c)
    (φ₀ : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))
    (hLF : LatticeFree φ₀) (hdet : c * ((d : ℝ) - 1) ^ 2 ≤ |LinearMap.det φ₀| * omega d) :
    ∃ ψ : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d),
      LatticeFree ψ ∧ |LinearMap.det ψ| * omega d = c * ((d : ℝ) - 1) ^ 2 := by
  have hd0 : 0 < d := by omega
  have hω : 0 < omega d := omega_pos hd0
  have hd1 : (1 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 1 < d)
  have hnum : 0 < c * ((d : ℝ) - 1) ^ 2 := mul_pos hc (pow_pos (by linarith) 2)
  have hMpos : 0 < |LinearMap.det φ₀| * omega d := lt_of_lt_of_le hnum hdet
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := by simp
  set t : ℝ := (c * ((d : ℝ) - 1) ^ 2 / (|LinearMap.det φ₀| * omega d)) ^ (1 / (d : ℝ)) with ht
  have ht0 : 0 < t := by
    rw [ht]
    exact Real.rpow_pos_of_pos (div_pos hnum hMpos) _
  have ht1 : t ≤ 1 := by
    rw [ht]
    have hle : c * ((d : ℝ) - 1) ^ 2 / (|LinearMap.det φ₀| * omega d) ≤ 1 := by
      rw [div_le_one hMpos]; exact hdet
    calc (c * ((d : ℝ) - 1) ^ 2 / (|LinearMap.det φ₀| * omega d)) ^ (1 / (d : ℝ))
        ≤ 1 ^ (1 / (d : ℝ)) :=
          Real.rpow_le_rpow (le_of_lt (div_pos hnum hMpos)) hle (by positivity)
      _ = 1 := by simp
  have htd : t ^ d = c * ((d : ℝ) - 1) ^ 2 / (|LinearMap.det φ₀| * omega d) := by
    have hdne : (d : ℝ) ≠ 0 := by positivity
    rw [← Real.rpow_natCast t d, ht, ← Real.rpow_mul (le_of_lt (div_pos hnum hMpos)),
      one_div, inv_mul_cancel₀ hdne, Real.rpow_one]
  refine ⟨t • φ₀, latticeFree_smul hLF ht0 ht1, ?_⟩
  have hdetne : |LinearMap.det φ₀| ≠ 0 := by
    have : |LinearMap.det φ₀| * omega d ≠ 0 := ne_of_gt hMpos
    intro h
    exact this (by rw [h, zero_mul])
  rw [LinearMap.det_smul, hfr, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ t ^ d), htd]
  field_simp

/-- **Rung 1** (Minkowski–Hlawka) in ellipsoid form, proved from the commons: in every
dimension `d ≥ 2` there is a lattice-free ellipsoid of volume at least `1/4`. -/
theorem exists_latticeFree_volume_quarter {d : ℕ} (hd : 2 ≤ d) :
    ∃ φ : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d),
      LatticeFree φ ∧ (1 / 4 : ℝ) ≤ |LinearMap.det φ| * omega d := by
  obtain ⟨Λ, h₁, h₂, hmin, hcov⟩ := Commons.Lattice.MinkowskiHlawka.minkowski_hlawka d hd
  haveI := h₁
  haveI := h₂
  obtain ⟨φ, hset, hdet⟩ :=
    Commons.Lattice.Packing.exists_ellipsoid_of_lattice (by omega : 0 < d) Λ hmin
  refine ⟨φ, (latticeFree_iff φ).mpr hset, ?_⟩
  have hDpos : 0 < ZLattice.covolume Λ := ZLattice.covolume_pos (L := Λ) (μ := volume)
  have hkey : |LinearMap.det φ| * omega d * ZLattice.covolume Λ = omega d := by
    calc |LinearMap.det φ| * omega d * ZLattice.covolume Λ
        = omega d * (|LinearMap.det φ| * ZLattice.covolume Λ) := by ring
      _ = omega d := by rw [hdet, mul_one]
  have hgoal : (1 / 4 : ℝ) * ZLattice.covolume Λ
      ≤ |LinearMap.det φ| * omega d * ZLattice.covolume Λ := by
    rw [hkey]
    show (1 / 4 : ℝ) * ZLattice.covolume Λ ≤ omega d
    rw [omega]
    linarith [hcov]
  exact le_of_mul_le_mul_right hgoal hDpos

/-- **The deep input** (Klartag, 2025), lattice ("density") form, in large dimensions:
there are a constant `c > 0` and a dimension `D` such that for every `d ≥ D` there is a
lattice of minimum norm at least `1` and covolume at most `ω_d / (c (d-1)^2)`.
Equivalently, in every large dimension there is a lattice-free ellipsoid of volume at least
`c (d-1)^2`. -/
theorem klartag_lattice_large : ∃ c : ℝ, 0 < c ∧ ∃ D : ℕ, 2 ≤ D ∧ ∀ d : ℕ, D ≤ d →
    ∃ (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) (h₁ : DiscreteTopology Λ) (h₂ : IsZLattice ℝ Λ),
      (∀ v : Λ, v ≠ 0 → 1 ≤ ‖(v : EuclideanSpace ℝ (Fin d))‖) ∧
      ZLattice.covolume Λ ≤ omega d / (c * ((d : ℝ) - 1) ^ 2) := by
  obtain ⟨c, hc, D, hD, H⟩ := Submission.Finish.klartag_lattice_large_om
  exact ⟨c, hc, D, hD, fun d hd => H d hd⟩

/-- The deep input in ellipsoid/linear-map form, derived from the lattice form through the
duality between lattice packings and lattice-free ellipsoids
(`Commons.Lattice.Packing.exists_ellipsoid_of_lattice`). -/
theorem klartag_density_large : ∃ c : ℝ, 0 < c ∧ ∃ D : ℕ, 2 ≤ D ∧ ∀ d : ℕ, D ≤ d →
    ∃ φ : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d),
      LatticeFree φ ∧ c * ((d : ℝ) - 1) ^ 2 ≤ |LinearMap.det φ| * omega d := by
  obtain ⟨c, hc, D, hD, H⟩ := klartag_lattice_large
  refine ⟨c, hc, D, hD, fun d hd => ?_⟩
  obtain ⟨Λ, h₁, h₂, hmin, hcov⟩ := H d hd
  haveI := h₁
  haveI := h₂
  obtain ⟨φ, hset, hdet⟩ :=
    Commons.Lattice.Packing.exists_ellipsoid_of_lattice (by omega : 0 < d) Λ hmin
  refine ⟨φ, (latticeFree_iff φ).mpr hset, ?_⟩
  have hd0 : 0 < d := by omega
  have hcpos : 0 < c * ((d : ℝ) - 1) ^ 2 := by
    have h1d : (1 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 1 < d)
    exact mul_pos hc (pow_pos (by linarith) 2)
  have hDpos : 0 < ZLattice.covolume Λ := ZLattice.covolume_pos (L := Λ) (μ := volume)
  have hcov' : c * ((d : ℝ) - 1) ^ 2 * ZLattice.covolume Λ ≤ omega d := by
    have h := (le_div_iff₀ hcpos).mp hcov
    calc c * ((d : ℝ) - 1) ^ 2 * ZLattice.covolume Λ
        = ZLattice.covolume Λ * (c * ((d : ℝ) - 1) ^ 2) := by ring
      _ ≤ omega d := h
  have hkey : |LinearMap.det φ| * omega d * ZLattice.covolume Λ = omega d := by
    calc |LinearMap.det φ| * omega d * ZLattice.covolume Λ
        = omega d * (|LinearMap.det φ| * ZLattice.covolume Λ) := by ring
      _ = omega d := by rw [hdet, mul_one]
  have hgoal : c * ((d : ℝ) - 1) ^ 2 * ZLattice.covolume Λ
      ≤ |LinearMap.det φ| * omega d * ZLattice.covolume Λ := by
    rw [hkey]
    exact hcov'
  exact le_of_mul_le_mul_right hgoal hDpos

/-- The deep input in ellipsoid form for **all** dimensions `d ≥ 2`: the large-dimensional
statement `klartag_density_large` combined with rung 1 (Minkowski–Hlawka, which supplies the
finitely many small dimensions). -/
theorem klartag_density : ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, 2 ≤ d →
    ∃ φ : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d),
      LatticeFree φ ∧ c * ((d : ℝ) - 1) ^ 2 ≤ |LinearMap.det φ| * omega d := by
  obtain ⟨c₁, hc₁, D, hD, H⟩ := klartag_density_large
  refine ⟨min c₁ (1 / (4 * ((D : ℝ) - 1) ^ 2)), ?_, fun d hd => ?_⟩
  · have hD1 : (1 : ℝ) < (D : ℝ) := by exact_mod_cast (by omega : 1 < D)
    have hpos : 0 < 1 / (4 * ((D : ℝ) - 1) ^ 2) := by positivity
    exact lt_min hc₁ hpos
  · by_cases hDd : D ≤ d
    · obtain ⟨φ, hφ, hvol⟩ := H d hDd
      refine ⟨φ, hφ, le_trans ?_ hvol⟩
      have hc₁le : min c₁ (1 / (4 * ((D : ℝ) - 1) ^ 2)) ≤ c₁ := min_le_left _ _
      have hnn : (0 : ℝ) ≤ ((d : ℝ) - 1) ^ 2 := sq_nonneg _
      exact mul_le_mul_of_nonneg_right hc₁le hnn
    · obtain ⟨φ, hφ, hvol⟩ := exists_latticeFree_volume_quarter (d := d) hd
      refine ⟨φ, hφ, le_trans ?_ hvol⟩
      have hDsq : ((d : ℝ) - 1) ^ 2 ≤ ((D : ℝ) - 1) ^ 2 := by
        have h1 : (d : ℝ) ≤ (D : ℝ) := by
          have h2 : d ≤ D := le_of_lt (lt_of_not_ge hDd)
          exact_mod_cast h2
        have hd1 : (0 : ℝ) ≤ (d : ℝ) - 1 := by
          have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (by omega : 1 ≤ d)
          linarith
        exact pow_le_pow_left₀ hd1 (by linarith) 2
      have hcm : min c₁ (1 / (4 * ((D : ℝ) - 1) ^ 2)) ≤ 1 / (4 * ((D : ℝ) - 1) ^ 2) :=
        min_le_right _ _
      calc min c₁ (1 / (4 * ((D : ℝ) - 1) ^ 2)) * ((d : ℝ) - 1) ^ 2
          ≤ (1 / (4 * ((D : ℝ) - 1) ^ 2)) * ((d : ℝ) - 1) ^ 2 :=
            mul_le_mul_of_nonneg_right hcm (sq_nonneg _)
        _ ≤ (1 / (4 * ((D : ℝ) - 1) ^ 2)) * ((D : ℝ) - 1) ^ 2 :=
            mul_le_mul_of_nonneg_left hDsq (by positivity)
        _ = 1 / 4 := by
          have hD1 : (1 : ℝ) < (D : ℝ) := by exact_mod_cast (by omega : 1 < D)
          have hne : ((D : ℝ) - 1) ≠ 0 := by linarith
          field_simp [hne]

/-- **Klartag's theorem**, in the form required by the challenge: for every `n` there is a
linear map on `ℝ^{n+1}` whose image of the unit ball has volume exactly `c n^2` and contains
no nonzero integer point. -/
theorem klartag_of_density : ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
    let V := EuclideanSpace ℝ (Fin (n + 1))
    ∃ φ : V →ₗ[ℝ] V, let E := φ '' Metric.ball (0 : V) 1
      (MeasureTheory.volume E : EReal) = c * n ^ 2 ∧
      {v ∈ E | ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0} := by
  obtain ⟨c, hc, H⟩ := klartag_density
  refine ⟨c, hc, fun n => ?_⟩
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    refine ⟨0, ?_, ?_⟩
    · have hE : ((0 : EuclideanSpace ℝ (Fin 1) →ₗ[ℝ] EuclideanSpace ℝ (Fin 1)) ''
          Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) 1) = {0} := by
        ext x
        simp only [Set.mem_image, Set.mem_singleton_iff]
        constructor
        · rintro ⟨y, -, rfl⟩; simp
        · rintro rfl; exact ⟨0, by simp [Metric.mem_ball], by simp⟩
      rw [hE]
      have hvol : ((volume ({0} : Set (EuclideanSpace ℝ (Fin 1))) : ENNReal) : EReal) = 0 := by
        rw [measure_singleton]
        simp
      rw [hvol]
      norm_num
    · ext v
      simp only [Set.mem_ofPred_eq, Set.mem_image, Set.mem_singleton_iff]
      constructor
      · rintro ⟨⟨y, -, hy⟩, -⟩
        exact hy ▸ (by simp : ((0 : EuclideanSpace ℝ (Fin 1) →ₗ[ℝ] EuclideanSpace ℝ (Fin 1)) y) = 0)
      · rintro rfl
        exact ⟨⟨0, by simp [Metric.mem_ball], by simp⟩, fun i => ⟨0, by simp⟩⟩
  · have hd : 2 ≤ n + 1 := by omega
    obtain ⟨φ, hLF, hdet⟩ := H (n + 1) hd
    obtain ⟨ψ, hψLF, hψdet⟩ := exists_exact hd hc φ hLF hdet
    refine ⟨ψ, ?_, ?_⟩
    · have hvol : volume (ψ '' Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
          = ENNReal.ofReal (c * (n : ℝ) ^ 2) := by
        rw [volume_image (by omega) ψ, hψdet]
        have hcast : ((n + 1 : ℕ) : ℝ) - 1 = (n : ℝ) := by push_cast; ring
        rw [hcast]
      rw [hvol, EReal.coe_ennreal_ofReal, max_eq_left (by positivity)]
      push_cast
      ring
    · ext v
      simp only [Set.mem_ofPred_eq, Set.mem_image, Set.mem_singleton_iff]
      constructor
      · rintro ⟨⟨y, hy, rfl⟩, hint⟩
        have hy1 : ‖y‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hy
        have h0 : ψ y = 0 := hψLF y hy1 hint
        rw [h0]
      · rintro rfl
        exact ⟨⟨0, by simp [Metric.mem_ball], by simp⟩, fun i => ⟨0, by simp⟩⟩

end

end Submission.Helpers
