import Mathlib
import Submission.Work.Drive.linearPlaneChart

/-!
# The fibres of the linear plane chart

`Work.Drive.linPlaneChart φ c hc : ℂ → CappingSpace` (`linearPlaneChart.lean`) presents the *linear*
projective plane `φ (linStd)` of the level `c` of the capping space as a disk whose boundary circle is
identified antipodally.  This file settles the fibre relation for that presentation: on the closed disk
the chart is injective exactly up to the antipodal identification of the boundary circle,

`linPlaneChart φ c hc z = linPlaneChart φ c hc z' ↔ z = z' ∨ (‖z‖ = 1 ∧ ‖z'‖ = 1 ∧ z' = -z)`,

which pins the multiplicity of the presentation to `1` in the end-contribution count
`#(Z_0 ⋔ Z_1 ⋔ Z_2) = 1` (`ENDS_AND_SEAMS_NOTES.md` §2, `CONCRETE_CHAINS_STATUS.md`).

The algebraic core is `exists_smul_linVecC_eq_iff_aux` below: for two points of the closed unit disk the
sphere lifts `linVecC z = (z, 1 - ‖z‖²)` of `ℂ² ≅ ℝ⁴` are *positive* multiples of one another only when
the points are equal, or are antipodal *boundary* points.  (In the *positive* scaling `a • linVecC z' =
linVecC z` with `a < 0` the equality `z = -z'` is forced by the two scalar equations
`a z' = z`, `a (1 - ‖z'‖²) = 1 - ‖z‖²`, whose subtraction gives `(a - 1)(1 + a ‖z'‖²) = 0`: with
`a ≠ 1` one gets `a = -1` from the disk bounds.)

The statement of `linPlaneChart_eq_iff` here carries the redundant conjunct `‖z'‖ = 1` (it follows from
`z' = -z` and `‖z‖ = 1`); it is the form requested by the counting lane.

**Note for the counting lane.**  The module `Submission/Work/Drive/linPlaneChartInjective.lean` proves
the same mathematics (its `Work.Drive.exists_smul_linVecC_eq_iff` and its variant
`Work.Drive.linPlaneChart_eq_iff`, whose right hand side omits the redundant conjunct `‖z'‖ = 1`).
Because it declares the *same* name `Work.Drive.linPlaneChart_eq_iff`, no module may import both it and
this file (`import ... failed, environment already contains 'Work.Drive.linPlaneChart_eq_iff'`); the
counting lane should import this file (the requested statement) and not that one.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

noncomputable section

/-! ## 1. The two complex coordinate functions along a real multiple

`c₁ v = v 0 + v 1 · i` and `c₂ v = v 2 + v 3 · i` are `ℂ`-linear (over real scalars).  The helper
names all carry the suffix `lin` so that they never collide with the identically stated helpers of
`Submission/Work/Drive/linPlaneChartInjective.lean`, which is a separate module that must not be
imported here (it declares the same `linPlaneChart_eq_iff` name). -/

lemma c₁_smul_lin (t : ℝ) (v : Eucl 3) : c₁ (t • v) = (t : ℂ) * c₁ v := by
  simp [c₁]; ring

lemma c₂_smul_lin (t : ℝ) (v : Eucl 3) : c₂ (t • v) = (t : ℂ) * c₂ v := by
  simp [c₂]; ring

@[simp] lemma c₁_linVecC_lin (z : ℂ) : c₁ (linVecC z) = z := c₁_ofComplex z _

@[simp] lemma c₂_linVecC_lin (z : ℂ) : c₂ (linVecC z) = ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) :=
  c₂_ofComplex z _

/-! ## 2. The algebraic core: positive multiples of the sphere lift on the closed disk -/

/-- **The sphere lifts of two points of the closed unit disk agree only for equal points or antipodal
boundary points.**  This is the algebraic content of the fibre relation of the linear plane chart. -/
theorem exists_smul_linVecC_eq_iff_aux {z z' : ℂ} (hz : ‖z‖ ≤ 1) (hz' : ‖z'‖ ≤ 1) :
    (∃ a : ℝ, a • linVecC z' = linVecC z) ↔ z = z' ∨ (‖z‖ = 1 ∧ z' = -z) := by
  constructor
  · rintro ⟨a, ha⟩
    -- the two complex coordinate equations
    have h1 : (a : ℂ) * z' = z := by
      have h := congrArg c₁ ha
      rwa [c₁_smul_lin, c₁_linVecC_lin, c₁_linVecC_lin] at h
    have h2 : a * (1 - ‖z'‖ ^ 2) = 1 - ‖z‖ ^ 2 := by
      have h := congrArg c₂ ha
      rw [c₂_smul_lin, c₂_linVecC_lin, c₂_linVecC_lin] at h
      have h' := congrArg Complex.re h
      simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] using h'
    -- and the norm equation, from the first one
    have hsq : ‖z‖ ^ 2 = a ^ 2 * ‖z'‖ ^ 2 := by
      rw [← h1, norm_mul, mul_pow]
      simp [sq_abs]
    rcases eq_or_ne a 1 with ha1 | ha1
    · exact Or.inl (by rw [← h1, ha1]; simp)
    · -- the two scalar equations give `(a - 1) * (1 + a ‖z'‖²) = 0`
      have hprod : a * ‖z'‖ ^ 2 = -1 := by
        have hzero : (a - 1) * (1 + a * ‖z'‖ ^ 2) = 0 := by nlinarith [h2, hsq]
        rcases mul_eq_zero.mp hzero with h | h
        · exact absurd (by linarith) ha1
        · linarith
      -- hence `a < 0`, and the disk bounds force `a = -1`
      have hlt : a < 0 := by nlinarith [hprod, sq_nonneg ‖z'‖]
      have hz2 : ‖z‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg z) hz
      have hz2' : ‖z'‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg z') hz'
      have hge : -1 ≤ a := by
        have h3 : ‖z‖ ^ 2 = -a := by nlinarith [hsq, hprod]
        nlinarith [h3, hz2]
      have hle : a ≤ -1 := by
        have h := mul_le_mul_of_nonpos_left hz2' hlt.le
        rw [mul_one, hprod] at h
        exact h
      have haeq : a = -1 := le_antisymm hle hge
      refine Or.inr ⟨?_, ?_⟩
      · have h3 : ‖z‖ ^ 2 = 1 := by nlinarith [hsq, hprod, haeq]
        nlinarith [norm_nonneg z]
      · have hthis : -z' = z := by rw [haeq] at h1; simpa using h1
        exact neg_inj.mp (by simpa using hthis)
  · rintro (rfl | ⟨h1, rfl⟩)
    · exact ⟨1, one_smul ℝ _⟩
    · refine ⟨-1, ?_⟩
      rw [linVecC_neg h1]
      simp

/-! ## 3. The fibre relation of the linear plane chart -/

/-- **The fibres of the linear plane chart**: two points of the closed disk give the same point of the
linear plane exactly when they are equal, or are antipodal points of the boundary circle.  This is the
`ℝP² = D̄/∼` identification in the coordinates of the capping space, and it is the
parameter-uniqueness input of the end contribution's count `#(Z_0 ⋔ Z_1 ⋔ Z_2) = 1`.  (`linPlaneChart`
is `Work.Drive.linPlaneChart` of `Submission/Work/Drive/linearPlaneChart.lean`: the disk model
`z ↦ [φ (z, 1 - ‖z‖²)]` of the projective plane `φ(linStd)` on the level `c` of the capping space.) -/
theorem linPlaneChart_eq_iff (φ : Work.Drive.Eucl 3 ≃L[ℝ] Work.Drive.Eucl 3) (c : ℝ) (hc : 0 < c)
    {z z' : ℂ} (hz : ‖z‖ ≤ 1) (hz' : ‖z'‖ ≤ 1) :
    Work.Drive.linPlaneChart φ c hc z = Work.Drive.linPlaneChart φ c hc z' ↔
      z = z' ∨ (‖z‖ = 1 ∧ ‖z'‖ = 1 ∧ z' = -z) := by
  constructor
  · intro h
    -- reduce to the equality of the projective classes of the two lifts
    have h' := congrArg cappingSpaceHomeoProj h
    rw [cappingSpaceHomeoProj_linPlaneChart, cappingSpaceHomeoProj_linPlaneChart] at h'
    have hcl : Projectivization.mk ℝ (φ (linVecC z)) (phi_linVecC_ne_zero φ z)
        = Projectivization.mk ℝ (φ (linVecC z')) (phi_linVecC_ne_zero φ z') :=
      (Prod.ext_iff.mp h').2
    -- a projective equality is a *unit* multiple
    rw [Projectivization.mk_eq_mk_iff] at hcl
    obtain ⟨a, ha⟩ := hcl
    have hsm : (a : ℝ) • linVecC z' = linVecC z := by
      apply φ.injective
      rw [map_smul, ← Units.smul_def]
      exact ha
    rcases (exists_smul_linVecC_eq_iff_aux hz hz').mp ⟨(a : ℝ), hsm⟩ with hzz | ⟨h1, h2⟩
    · exact Or.inl hzz
    · exact Or.inr ⟨h1, by rw [h2, norm_neg, h1], h2⟩
  · rintro (rfl | ⟨h1, _, h3⟩)
    · rfl
    · rw [h3]
      exact (linPlaneChart_neg φ c hc h1).symm

end

end Work.Drive
