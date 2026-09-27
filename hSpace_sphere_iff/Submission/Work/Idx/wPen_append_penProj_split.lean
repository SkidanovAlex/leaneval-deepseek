import Mathlib
import Submission.Work.Idx.WPenAppendDefs
import Submission.Work.Idx.circleIntegral_const
import Submission.Work.Idx.wPen_append_block_ids
import Submission.Work.Idx.pResA_split_gen

set_option linter.style.haveILetI false

namespace Work.Idx

open Matrix MeasureTheory intervalIntegral
open scoped Topology Interval

noncomputable section

/-! ## The abstract pencil identities

Everything in this section is stated for an arbitrary complex Banach algebra `R`, so that it
applies to `Matrix (WIdx n d ⊕ Fin n) (WIdx n d ⊕ Fin n) C(X, ℂ)` with the `L∞` operator norm.
-/

section Gen

variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R]

/-- **Continuity of the pencil integrand on the unit circle.**  If the pencil `z ↦ z • A + B` is a
unit for every `z` on the unit circle, then `z ↦ (zA+B)⁻¹ A` is continuous there: the map
`z ↦ z • A + B` is continuous, `Ring.inverse` is continuous at units
(`NormedRing.inverse_continuousAt`, whose `HasSummableGeomSeries` hypothesis is supplied by
completeness), and `IsUnit.unit_spec` identifies the two. -/
theorem continuousOn_pResA_one (A B : R)
    (h : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (z • A + B)) :
    ContinuousOn (fun z : ℂ => Work.KT.Idx.pResA A B z) (Metric.sphere (0:ℂ) 1) := by
  have hunits : ContinuousOn Ring.inverse {x : R | IsUnit x} := fun x hx => by
    simpa only [IsUnit.unit_spec hx] using
      (NormedRing.inverse_continuousAt hx.unit).continuousWithinAt
  have hlin : Continuous fun z : ℂ => z • A + B :=
    (continuous_id.smul continuous_const).add continuous_const
  have h1 : ContinuousOn (fun z : ℂ => Ring.inverse (z • A + B)) (Metric.sphere (0:ℂ) 1) :=
    hunits.comp hlin.continuousOn (fun z hz => h z (by
      simpa [Metric.mem_sphere, dist_eq_norm, sub_zero] using hz))
  have h2 : ContinuousOn (fun z : ℂ => Ring.inverse (z • A + B) * A)
      (Metric.sphere (0:ℂ) 1) :=
    h1.mul continuousOn_const
  exact h2.congr (fun z _ => rfl)

/-- **Splitting the pole of the perturbed pencil.**  If `a₁`/`b₁` differ from `a₂`/`b₂` by the
shear `σ` and the square-zero `ρ` in the sense of the identities `σ a₁ = a₂ - b₂ ρ`,
`σ b₁ = b₂`, `a₂ ρ = 0`, `ρ ρ = 0`, `σ σ = 1`, then the two pole integrands differ by a
*polynomial* of degree one in `z` on the unit circle:
`(z a₁+b₁)⁻¹ a₁ = (z a₂+b₂)⁻¹ a₂ - ρ + z • (ρ * (z a₂+b₂)⁻¹ a₂)`.

The hypothesis `IsUnit (z • a₂ + b₂)` makes `z • a₁ + b₁ = σ (z • a₂ + b₂) (1 - z • ρ)` a product
of units (with `(1 - zρ)⁻¹ = 1 + zρ` since `ρ² = 0`), whose inverse is
`(1 + zρ) (z a₂+b₂)⁻¹ σ`; the computation then uses `(z a₂+b₂)⁻¹ b₂ = 1 - z • (z a₂+b₂)⁻¹ a₂` and
`a₂ ρ = 0`. -/
theorem pResA_split_pointwise (σ ρ a₁ b₁ a₂ b₂ : R)
    (hσa : σ * a₁ = a₂ - b₂ * ρ) (hσb : σ * b₁ = b₂)
    (haρ : a₂ * ρ = 0) (hρρ : ρ * ρ = 0) (hσσ : σ * σ = 1)
    (z : ℂ) (hz : IsUnit (z • a₂ + b₂)) :
    Work.KT.Idx.pResA a₁ b₁ z
      = Work.KT.Idx.pResA a₂ b₂ z - ρ + z • (ρ * Work.KT.Idx.pResA a₂ b₂ z) :=
  pResA_split_gen σ ρ a₁ b₁ a₂ b₂ hσa hσb haρ hρρ hσσ z hz

/-- **Integrating the split pole.**  If the pole integrands of two pencils agree on the unit circle
up to the polynomial perturbation `- ρ + z • (ρ * ·)`, then the Riesz projections satisfy
`penProj a₁ b₁ = penProj a₂ b₂ + ρ * Z` with `Z = (2πi)⁻¹ • ∮_{|z|=1} z • (z a₂+b₂)⁻¹ a₂ dz`.

The integral decomposition uses `circleIntegral.integral_add`, `circleIntegral.integral_sub` and
`∮ 1 = 0` (`Work.Idx.circleIntegral_const`) for the constant term, and the pull-out rule
`Work.KT.Fund.circleIntegral_const_mul` for the `z`-linear term; continuity of the integrand on
the circle is supplied by the caller (it is what makes all the functions circle integrable). -/
theorem penProj_eq_add_zmat (ρ a₁ b₁ a₂ b₂ : R)
    (hsplit : ∀ z : ℂ, ‖z‖ = 1 → Work.KT.Idx.pResA a₁ b₁ z
        = Work.KT.Idx.pResA a₂ b₂ z - ρ + z • (ρ * Work.KT.Idx.pResA a₂ b₂ z))
    (hcont : ContinuousOn (fun z : ℂ => Work.KT.Idx.pResA a₂ b₂ z) (Metric.sphere (0:ℂ) 1)) :
    Work.KT.Idx.penProj a₁ b₁
      = Work.KT.Idx.penProj a₂ b₂
        + ρ * ((2 * Real.pi * Complex.I)⁻¹ •
            (∮ z in C(0,1), z • Work.KT.Idx.pResA a₂ b₂ z)) := by
  have hF2 : CircleIntegrable (fun z : ℂ => Work.KT.Idx.pResA a₂ b₂ z) 0 1 :=
    hcont.circleIntegrable (by norm_num)
  have hcρ : CircleIntegrable (fun _ : ℂ => ρ) 0 1 := circleIntegrable_const ρ 0 1
  have hH : CircleIntegrable (fun z : ℂ => z • Work.KT.Idx.pResA a₂ b₂ z) 0 1 :=
    (continuous_id.continuousOn.smul hcont).circleIntegrable (by norm_num)
  have hG : CircleIntegrable (fun z : ℂ => z • (ρ * Work.KT.Idx.pResA a₂ b₂ z)) 0 1 :=
    (continuous_id.continuousOn.smul (continuousOn_const.mul hcont)).circleIntegrable (by norm_num)
  have hFr : CircleIntegrable (fun z : ℂ => Work.KT.Idx.pResA a₂ b₂ z - ρ) 0 1 :=
    hF2.sub hcρ
  have hcongr : (∮ z in C(0,1), Work.KT.Idx.pResA a₁ b₁ z)
      = ∮ z in C(0,1), (Work.KT.Idx.pResA a₂ b₂ z - ρ
          + z • (ρ * Work.KT.Idx.pResA a₂ b₂ z)) :=
    circleIntegral.integral_congr (by norm_num) (fun z hz => hsplit z (by
      simpa [Metric.mem_sphere, dist_eq_norm, sub_zero] using hz))
  have step1 : (∮ z in C(0,1), (Work.KT.Idx.pResA a₂ b₂ z - ρ
        + z • (ρ * Work.KT.Idx.pResA a₂ b₂ z)))
      = (∮ z in C(0,1), Work.KT.Idx.pResA a₂ b₂ z - ρ)
        + (∮ z in C(0,1), z • (ρ * Work.KT.Idx.pResA a₂ b₂ z)) :=
    circleIntegral.integral_add hFr hG
  have step2 : (∮ z in C(0,1), Work.KT.Idx.pResA a₂ b₂ z - ρ)
      = (∮ z in C(0,1), Work.KT.Idx.pResA a₂ b₂ z) - (∮ z in C(0,1), ρ) :=
    circleIntegral.integral_sub hF2 hcρ
  have hfun : (fun z : ℂ => z • (ρ * Work.KT.Idx.pResA a₂ b₂ z))
      = (fun z : ℂ => ρ * (z • Work.KT.Idx.pResA a₂ b₂ z)) := by
    funext z
    exact (mul_smul_comm z ρ (Work.KT.Idx.pResA a₂ b₂ z)).symm
  have step3 : (∮ z in C(0,1), z • (ρ * Work.KT.Idx.pResA a₂ b₂ z))
      = ρ * (∮ z in C(0,1), z • Work.KT.Idx.pResA a₂ b₂ z) := by
    rw [hfun]
    exact Work.KT.Fund.circleIntegral_const_mul ρ
      (fun z : ℂ => z • Work.KT.Idx.pResA a₂ b₂ z) 0 1 hH
  have hsub : (∮ z in C(0,1), (Work.KT.Idx.pResA a₂ b₂ z - ρ
        + z • (ρ * Work.KT.Idx.pResA a₂ b₂ z)))
      = (∮ z in C(0,1), Work.KT.Idx.pResA a₂ b₂ z)
        + ρ * (∮ z in C(0,1), z • Work.KT.Idx.pResA a₂ b₂ z) := by
    rw [step1, step2, Work.Idx.circleIntegral_const ρ 0 1, sub_zero, step3]
  rw [Work.KT.Idx.penProj, Work.KT.Idx.penProj]
  simp only [Work.KT.Idx.pCirc]
  rw [hcongr, hsub, smul_add]
  rw [← Algebra.mul_smul_comm ((2 * Real.pi * Complex.I)⁻¹) ρ
    (∮ z in C(0,1), z • Work.KT.Idx.pResA a₂ b₂ z)]

/-- **The correction term kills `ρ` on the right.**  Since `a₂ ρ = 0`, the integrand
`z • (z a₂ + b₂)⁻¹ a₂` of the correction term satisfies `(z • (za₂+b₂)⁻¹ a₂) ρ = 0`; integrating
and pulling the constant `ρ` out (`Work.KT.Fund.circleIntegral_mul_const`) makes the correction
`Z = (2πi)⁻¹ • ∮ z • (za₂+b₂)⁻¹ a₂` satisfy `Z ρ = 0`. -/
theorem zmat_mul_eq_zero (ρ a₂ b₂ : R) (haρ : a₂ * ρ = 0)
    (hcont : ContinuousOn (fun z : ℂ => Work.KT.Idx.pResA a₂ b₂ z) (Metric.sphere (0:ℂ) 1)) :
    ((2 * Real.pi * Complex.I)⁻¹ •
        (∮ z in C(0,1), z • Work.KT.Idx.pResA a₂ b₂ z)) * ρ = 0 := by
  have hH : CircleIntegrable (fun z : ℂ => z • Work.KT.Idx.pResA a₂ b₂ z) 0 1 :=
    (continuous_id.continuousOn.smul hcont).circleIntegrable (by norm_num)
  have hp : ∀ z : ℂ, Work.KT.Idx.pResA a₂ b₂ z * ρ = 0 := by
    intro z
    rw [Work.KT.Idx.pResA, Work.KT.Idx.pRes, mul_assoc, haρ, mul_zero]
  have hz : ∀ z ∈ Metric.sphere (0:ℂ) 1,
      (z • Work.KT.Idx.pResA a₂ b₂ z) * ρ = (0 : R) := by
    intro z _
    rw [Algebra.smul_mul_assoc, hp z, smul_zero]
  have hzero : (∮ z in C(0,1), (z • Work.KT.Idx.pResA a₂ b₂ z) * ρ) = 0 := by
    have h1 : (∮ z in C(0,1), (z • Work.KT.Idx.pResA a₂ b₂ z) * ρ)
        = ∮ z in C(0,1), (0 : R) :=
      circleIntegral.integral_congr (by norm_num) hz
    rw [h1, Work.Idx.circleIntegral_const (0 : R) 0 1]
  have hWρ : (∮ z in C(0,1), z • Work.KT.Idx.pResA a₂ b₂ z) * ρ = 0 := by
    rw [← Work.KT.Fund.circleIntegral_mul_const ρ
      (fun z : ℂ => z • Work.KT.Idx.pResA a₂ b₂ z) 0 1 hH]
    exact hzero
  rw [Algebra.smul_mul_assoc, hWρ, smul_zero]

end Gen

/-- **Splitting the append projection.**  With `S = Smat`, `R = Rmat` and the block identities
`S · Ablk = Adiag - Bdiag · R`, `S · Bblk = Bdiag`, `Adiag · R = 0`, `R · R = 0`, `S · S = 1`, the
resolvent of the `(d+2)`-block pencil is `(z • Ablk + Bblk)⁻¹ = (1 + zR)(z • Adiag + Bdiag)⁻¹S`
(note `(1 - zR)(1 + zR) = 1` since `R² = 0`), whence
`pResA Ablk Bblk z = pResA Adiag Bdiag z - R + z • (R * pResA Adiag Bdiag z)` on the unit circle
(the two ingredients are `Ablk = S(Adiag - Bdiag R)` and
`(zAdiag+Bdiag)⁻¹ Bdiag = 1 - z • pResA Adiag Bdiag z`).  Integrating over the circle
(`circleIntegral.integral_add/sub`, `Work.KT.Fund.circleIntegral_const_mul`,
`Work.KT.Fund.circleIntegral_mul_const` and `∮ 1 = 0` from `Work.Idx.circleIntegral_const`, plus
continuity of `z ↦ pResA Adiag Bdiag z` on the unit circle, from the unit hypothesis and
`NormedRing.inverse_continuousAt`) gives the first conjunct; the second conjunct uses
`(pResA Adiag Bdiag z) * R = 0`, which follows from `Adiag * R = 0`. -/
theorem wPen_append_penProj_split (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n d : ℕ) (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ))
    (h : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (z • Work.Idx.Adiag X n d + Work.Idx.Bdiag X n d b)) :
    (Work.Idx.penProjMat X (Work.Idx.Ablk X n d) (Work.Idx.Bblk X n d b)
        = Work.Idx.penProjMat X (Work.Idx.Adiag X n d) (Work.Idx.Bdiag X n d b)
          + Work.Idx.Rmat X n d * Work.Idx.Zmat X n d b) ∧
    (Work.Idx.Zmat X n d b * Work.Idx.Rmat X n d = 0) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := wPen_append_block_ids X n d b
  letI : NormedRing (Matrix (WIdx n d ⊕ Fin n) (WIdx n d ⊕ Fin n) C(X, ℂ)) :=
    Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (WIdx n d ⊕ Fin n) (WIdx n d ⊕ Fin n) C(X, ℂ)) :=
    Matrix.linftyOpNormedAlgebra
  letI : CompleteSpace (Matrix (WIdx n d ⊕ Fin n) (WIdx n d ⊕ Fin n) C(X, ℂ)) :=
    Matrix.instCompleteSpace _ _ _
  have hsplit : ∀ z : ℂ, ‖z‖ = 1 →
      Work.KT.Idx.pResA (Ablk X n d) (Bblk X n d b) z
        = Work.KT.Idx.pResA (Adiag X n d) (Bdiag X n d b) z - Rmat X n d
          + z • (Rmat X n d * Work.KT.Idx.pResA (Adiag X n d) (Bdiag X n d b) z) :=
    fun z hz => @pResA_split_gen (Matrix (WIdx n d ⊕ Fin n) (WIdx n d ⊕ Fin n) C(X, ℂ))
      Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
      (Smat X n d) (Rmat X n d) (Ablk X n d) (Bblk X n d b) (Adiag X n d) (Bdiag X n d b)
      h1 h2 h3 h4 h5 z (h z hz)
  have hcont : ContinuousOn (fun z : ℂ =>
      Work.KT.Idx.pResA (Adiag X n d) (Bdiag X n d b) z) (Metric.sphere (0:ℂ) 1) :=
    @continuousOn_pResA_one (Matrix (WIdx n d ⊕ Fin n) (WIdx n d ⊕ Fin n) C(X, ℂ))
      Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
      (Matrix.instCompleteSpace _ _ _) (Adiag X n d) (Bdiag X n d b) (fun z hz => h z hz)
  refine ⟨?_, ?_⟩
  · have k := @penProj_eq_add_zmat (Matrix (WIdx n d ⊕ Fin n) (WIdx n d ⊕ Fin n) C(X, ℂ))
      Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
      (Matrix.instCompleteSpace _ _ _) (Rmat X n d) (Ablk X n d) (Bblk X n d b)
      (Adiag X n d) (Bdiag X n d b) hsplit hcont
    simpa only [penProjMat, Zmat] using k
  · have k := @zmat_mul_eq_zero (Matrix (WIdx n d ⊕ Fin n) (WIdx n d ⊕ Fin n) C(X, ℂ))
      Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
      (Matrix.instCompleteSpace _ _ _) (Rmat X n d) (Adiag X n d) (Bdiag X n d b) h3 hcont
    simpa only [Zmat] using k

end

end Work.Idx
