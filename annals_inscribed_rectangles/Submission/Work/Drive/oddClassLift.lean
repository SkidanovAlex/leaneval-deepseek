import Mathlib
import Submission.Work.Drive.diskLiftHomotopy
import Submission.Work.Drive.exists_odd_renormalization

/-!
# The (B) half of the ends clause with *checkable* inputs

`Work.Drive.exists_diskClassHomotopy` (`Submission/Work/Drive/diskLiftHomotopy.lean`) produces the
homotopy of the ends clause from two lifts that are **odd on the boundary circle**.  The oddness of the
lift of the chart's class map is the *essentiality* of that class map; the checkable form of it is

> the parallelism factor `V (-z) = c · V z` is **negative at one boundary point**

(`Work.Drive.exists_odd_renormalization` turns that into an odd lift: the sign is constant on the circle
because the comparison factor is a continuous nonvanishing function on it, and the sign is the only
invariant of the lift under rescaling by a positive function).

This file packages the passage:

* `Work.Drive.exists_interp_eq_zero_iff` — the characterisation `(1-s) • A + s • B = 0` for some
  `s ∈ [0,1]` iff `A` and `B` are **negatively parallel**; this is what makes the non-collision
  hypothesis `hgood` invariant under rescaling the lift by a positive function, so that it can be taken
  for the *given* lift;
* `Work.Drive.exists_odd_classLift` — from the chart's lift `V` (parallel to `V (-·)` on the circle and
  with negative factor at one point) produce a lift `W = μ • V` of the **same** class map, smooth,
  nonvanishing, with `μ > 0`, and odd on the circle;
* `Work.Drive.exists_diskClassHomotopy_linear_of_neg` — the end-to-end (B) half for the design's two ends
  (the chart's plane and the disk model of a linear plane), with the checkable inputs only.
-/

namespace Work.Drive

open Manifold Set
open scoped Manifold ContDiff Topology

noncomputable section

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

/-- **A negative-parallelism pair is exactly a pair whose interpolation vanishes.**  For nonzero `A`,
`B` there is `s ∈ [0,1]` with `(1-s) • A + s • B = 0` if and only if `B = lam • A` with `lam < 0`. -/
theorem exists_interp_eq_zero_iff {A B : Eucl 3} (hA : A ≠ 0) (hB : B ≠ 0) :
    (∃ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 ∧ (1 - s) • A + s • B = 0) ↔
      ∃ lam : ℝ, B = lam • A ∧ lam < 0 := by
  constructor
  · rintro ⟨s, hs, hzero⟩
    have hs0 : s ≠ 0 := by
      rintro rfl
      rw [sub_zero, one_smul, zero_smul, add_zero] at hzero
      exact hA hzero
    have hs1 : s ≠ 1 := by
      rintro rfl
      rw [sub_self, zero_smul, one_smul, zero_add] at hzero
      exact hB hzero
    have hslo : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
    have hshi : s < 1 := lt_of_le_of_ne hs.2 hs1
    refine ⟨-((1 - s) / s), ?_, ?_⟩
    · have h1 : s • B = -((1 - s) • A) := by
        rw [eq_neg_iff_add_eq_zero, add_comm]
        exact hzero
      calc B = (s⁻¹) • (s • B) := by rw [smul_smul, inv_mul_cancel₀ hs0, one_smul]
        _ = s⁻¹ • (-((1 - s) • A)) := by rw [h1]
        _ = -((1 - s) / s) • A := by
              rw [smul_neg, smul_smul, neg_smul]
              congr 2
              field_simp
    · have hpos : 0 < (1 - s) / s := div_pos (by linarith) hslo
      linarith
  · rintro ⟨lam, rfl, hlam⟩
    have hpos : 0 < 1 - lam := by linarith
    refine ⟨1 / (1 - lam), ⟨div_nonneg zero_le_one (le_of_lt hpos), ?_⟩, ?_⟩
    · rw [div_le_one hpos]; linarith
    · rw [smul_smul]
      have hsum : (1 - 1 / (1 - lam)) + (1 / (1 - lam)) * lam = 0 := by
        field_simp
        ring
      rw [← add_smul, hsum, zero_smul]

/-- **Replacing the chart's lift by an odd one.**  If the given smooth nonvanishing lift `V` of a disk
chart's class map is parallel to its value at the antipode on the boundary circle, with **negative**
factor at one boundary point (the essentiality of the class map), then the same class map has a smooth
nonvanishing lift `W` that is exactly odd on the circle, obtained as `W = μ • V` with `μ > 0`. -/
theorem exists_odd_classLift {D : ℂ → CappingSpace} {V : ℂ → Eucl 3}
    (hVne : ∀ z, V z ≠ 0) (hVsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hcls : IsClassLift D V hVne)
    (hpar : ∀ z : ℂ, ‖z‖ = 1 → ∃ c : ℝ, V (-z) = c • V z)
    {z₀ : ℂ} (hz₀ : ‖z₀‖ = 1)
    (hneg : ∃ c : ℝ, V (-z₀) = c • V z₀ ∧ c < 0) :
    ∃ (W : ℂ → Eucl 3) (μ : ℂ → ℝ) (hW : ∀ z, W z ≠ 0),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W ∧ (∀ z, 0 < μ z) ∧
      (∀ z, W z = μ z • V z) ∧ IsClassLift D W hW ∧
      (∀ z : ℂ, ‖z‖ = 1 → W (-z) = - W z) := by
  obtain ⟨W, μ, hWsmooth, hWne, hμpos, hWeq, hWodd⟩ :=
    exists_odd_renormalization V hVsmooth hVne hpar hz₀ hneg
  have hWcls : IsClassLift D W hWne := by
    intro z
    rw [hcls z]
    refine (Projectivization.mk_eq_mk_iff ℝ (V z) (W z) _ _).mpr
      ⟨(Units.mk0 (μ z) (ne_of_gt (hμpos z)))⁻¹, ?_⟩
    rw [hWeq z, Units.smul_def, Units.val_inv_eq_inv_val, Units.val_mk0, smul_smul,
      inv_mul_cancel₀ (ne_of_gt (hμpos z)), one_smul]
  exact ⟨W, μ, hWne, hWsmooth, hμpos, hWeq, hWcls, hWodd⟩

/-- **The (B) half of the ends clause for the design's two ends, with checkable inputs.**  The chart
contributes a smooth nonvanishing lift `V` of its class map, parallel to its antipodal value on the
boundary circle, with **negative** factor at one boundary point (the essentiality of the class map), and
the non-collision condition `hgood` — in its rescaling-invariant form, "at the zeros of `χ` the linear
plane's class at `z` is not `lam • V z` with `lam < 0`" — for the weight `χ`; the linear plane
contributes the proved odd lift `Work.Drive.linVecC`.  The conclusion is a single `C^∞` homotopy of class
maps of the square, from the chart's plane to the disk model of the linear plane, with the endpoints as
functions on all of `ℝ²` and the seam invariance on the whole seam — the homotopy clauses of
`Work.Drive.HasClassLinearization`. -/
theorem exists_diskClassHomotopy_linear_of_neg (D : ℂ → CappingSpace) (V : ℂ → Eucl 3)
    (hVne : ∀ z, V z ≠ 0) (hVsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hcls : IsClassLift D V hVne)
    (hpar : ∀ z : ℂ, ‖z‖ = 1 → ∃ c : ℝ, V (-z) = c • V z)
    {z₀ : ℂ} (hz₀ : ‖z₀‖ = 1)
    (hneg : ∃ c : ℝ, V (-z₀) = c • V z₀ ∧ c < 0)
    (φ : Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ) (hc : 0 < c) (χ : ℂ → ℝ)
    (hχsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hχodd : ∀ z : ℂ, ‖z‖ = 1 → χ (-z) = - χ z)
    (hgood : ∀ z : ℂ, ‖z‖ ≤ 1 → χ z = 0 →
      ¬ ∃ lam : ℝ, (φ (linVecC z)) = lam • V z ∧ lam < 0) :
    ∃ (p : Eucl 3) (H : ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3)),
      (∀ y, H (0, y) = planeClassMap (diskPlane D) y) ∧
      (∀ y, H (1, y) = planeClassMap (diskPlane (linPlaneChart φ c hc)) y) ∧
      (∀ (t : ℝ) (y : EuclideanSpace ℝ (Fin 2)), onSeam2 y → H (t, seamInv2 y) = H (t, y)) ∧
      Continuous H ∧
      ContMDiff (𝓡 3) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
        ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : EuclideanSpace ℝ (Fin 3) => H (x 2, mk2 (x 0) (x 1))) := by
  obtain ⟨W, μ, hWne, hWsmooth, hμpos, hWeq, hWcls, hWodd⟩ :=
    exists_odd_classLift hVne hVsmooth hcls hpar hz₀ hneg
  have hBne : ∀ z : ℂ, (φ (linVecC z)) ≠ 0 := fun z => phi_linVecC_ne_zero φ z
  have hgood' : ∀ z : ℂ, ‖z‖ ≤ 1 → χ z = 0 → ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      (1 - s) • W z + s • (φ (linVecC z)) ≠ 0 := by
    intro z hz hz0 s hs hzero
    have hWz : W z ≠ 0 := hWne z
    have hpar' : ∃ lam : ℝ, (φ (linVecC z)) = lam • W z ∧ lam < 0 :=
      (exists_interp_eq_zero_iff hWz (hBne z)).mp ⟨s, hs, hzero⟩
    obtain ⟨lam, hlam, hlamneg⟩ := hpar'
    refine hgood z hz hz0 ⟨lam * μ z, ?_, ?_⟩
    · rw [hlam, hWeq z, smul_smul]
    · exact mul_neg_of_neg_of_pos hlamneg (hμpos z)
  exact exists_diskClassHomotopy_linear D W χ φ c hc hWne hWsmooth hχsmooth hWcls hWodd hχodd hgood'

end

end Work.Drive
