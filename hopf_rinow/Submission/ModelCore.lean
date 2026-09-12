import Submission.Model

/-!
Prove `Submission.Model.odeField_contDiffAt`: the geodesic first-order vector
field (built from a smooth positive-definite metric family `g` and its
derivative) is `C¹` at every point.  You may add helper lemmas above the final
theorem, importing whatever Mathlib modules you need.  The final theorem
statement must remain as given (fill in its proof).
-/

namespace Submission.Model

open scoped ContDiff
open ContinuousLinearMap

/-!
# Infrastructure

The Mathlib instance chain for *nested* spaces of continuous linear maps stops
at depth three when the nested space occurs on the *left* of `→L` (it only
recurses through codomains).  The smoothness proof below needs `ContDiffAt` of
maps whose values live in `Bilin E →L ℝ` and in `Bilin E →L (E →L ℝ)` (the
spaces of the evaluation maps built with `ContinuousLinearMap.apply`), so we
supply those instances explicitly, following the same `letI` pattern used in
`Submission.CLMInstances`.
-/

section ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable section

instance instNormedAddCommGroupBilinToLReal :
    NormedAddCommGroup (Bilin E →L[ℝ] ℝ) := by
  letI : NormedAddCommGroup (Bilin E) := inferInstance
  letI : NormedSpace ℝ (Bilin E) := inferInstance
  infer_instance

instance instNormedSpaceBilinToLReal : NormedSpace ℝ (Bilin E →L[ℝ] ℝ) := by
  letI : NormedAddCommGroup (Bilin E) := inferInstance
  letI : NormedSpace ℝ (Bilin E) := inferInstance
  infer_instance

instance instNormedAddCommGroupBilinToLCovec :
    NormedAddCommGroup (Bilin E →L[ℝ] (E →L[ℝ] ℝ)) := by
  letI : NormedAddCommGroup (Bilin E) := inferInstance
  letI : NormedSpace ℝ (Bilin E) := inferInstance
  infer_instance

instance instNormedSpaceBilinToLCovec : NormedSpace ℝ (Bilin E →L[ℝ] (E →L[ℝ] ℝ)) := by
  letI : NormedAddCommGroup (Bilin E) := inferInstance
  letI : NormedSpace ℝ (Bilin E) := inferInstance
  infer_instance

/-- The map `v ↦ evalAtV v` (evaluation of a bilinear form at the pair `(v, v)`)
is `C¹`.  It is the composition of the two `ContinuousLinearMap.apply` maps at `v`. -/
lemma contDiff_evalAtV : ContDiff ℝ 1 (fun v : E => evalAtV v) := by
  have h1 : ContDiff ℝ 1 (fun v : E =>
      ContinuousLinearMap.apply (𝕜 := ℝ) (E := E) (Fₗ := E →L[ℝ] ℝ) v) := by
    exact ContinuousLinearMap.contDiff
      (𝕜 := ℝ) (E := E) (F := (Bilin E →L[ℝ] (E →L[ℝ] ℝ)))
      (f := ContinuousLinearMap.apply (𝕜 := ℝ) (E := E) (Fₗ := E →L[ℝ] ℝ))
  have h2 : ContDiff ℝ 1 (fun v : E =>
      ContinuousLinearMap.apply (𝕜 := ℝ) (E := E) (Fₗ := ℝ) v) := by
    exact ContinuousLinearMap.contDiff
      (𝕜 := ℝ) (E := E) (F := ((E →L[ℝ] ℝ) →L[ℝ] ℝ))
      (f := ContinuousLinearMap.apply (𝕜 := ℝ) (E := E) (Fₗ := ℝ))
  have hcomp : ContDiff ℝ 1 (fun v : E => ((ContinuousLinearMap.apply (𝕜 := ℝ) (E := E) (Fₗ := ℝ) v).comp
      (ContinuousLinearMap.apply (𝕜 := ℝ) (E := E) (Fₗ := E →L[ℝ] ℝ) v))) := by
    exact ContDiff.clm_comp
      (𝕜 := ℝ) (X := E) (E := Bilin E) (F := E →L[ℝ] ℝ) (G := ℝ) (n := 1)
      h2 h1
  convert hcomp using 1
  funext v
  simp [evalAtV]

/-- The Euler–Lagrange right-hand covector `(T, v) ↦ rhsCovector T v` is `C¹`. -/
lemma contDiff_rhsCovector : ContDiff ℝ 1
    (fun p : (E →L[ℝ] Bilin E) × E => rhsCovector p.1 p.2) := by
  let X := (E →L[ℝ] Bilin E) × E
  have hEvalAt : ContDiff ℝ 1 (fun p : X => evalAtV p.2) := by
    exact contDiff_evalAtV.comp (contDiff_snd : ContDiff ℝ 1 (fun p : X => p.2))
  have hT : ContDiff ℝ 1 (fun p : X => p.1) := by
    exact contDiff_fst
  have hcv1 : ContDiff ℝ 1 (fun p : X => (evalAtV p.2).comp p.1) := by
    exact ContDiff.clm_comp (𝕜 := ℝ) (X := X) (E := E) (F := Bilin E) (G := ℝ) (n := 1) hEvalAt hT
  have hTv : ContDiff ℝ 1 (fun p : X => p.1 p.2) := by
    exact ContDiff.clm_apply (𝕜 := ℝ) (E := X) (F := E) (G := Bilin E) (n := 1) hT
      (contDiff_snd : ContDiff ℝ 1 (fun p : X => p.2))
  have hcv2 : ContDiff ℝ 1 (fun p : X => (p.1 p.2) p.2) := by
    exact ContDiff.clm_apply (𝕜 := ℝ) (E := X) (F := E) (G := E →L[ℝ] ℝ) (n := 1) hTv
      (contDiff_snd : ContDiff ℝ 1 (fun p : X => p.2))
  have hres : ContDiff ℝ 1 (fun p : X => ((1 / 2 : ℝ) • (evalAtV p.2).comp p.1) - (p.1 p.2) p.2) := by
    exact (hcv1.const_smul (1 / 2 : ℝ)).sub hcv2
  convert hres using 1
  funext p
  simp [rhsCovector]

end

/-- The acceleration map `(x, v) ↦ accel (g x) (fderiv ℝ g x) v` is `C¹` at `(x₀, v₀)`
whenever the metric family `g` is `C³` and invertible at every point. -/
lemma accel_contDiffAt (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (x₀ v₀ : E) :
    ContDiffAt ℝ 1 (fun z : E × E => accel (g z.1) (fderiv ℝ g z.1) z.2) (x₀, v₀) := by
  let p : E × E := (x₀, v₀)
  -- derivative of g is C^1
  have hdf1 : ContDiff ℝ 1 (fderiv ℝ g) := by
    exact hg.fderiv_right (m := 1) (by norm_num : (1 : ℕ∞ω) + 1 ≤ 3)
  -- inversion of the metric at x₀ is smooth there (x ↦ (g x).inverse)
  have hinvAt : ContDiffAt ℝ 1 (fun gx : Bilin E =>
      (ContinuousLinearMap.inverse gx : (E →L[ℝ] ℝ) →L[ℝ] E)) (g x₀) := by
    exact ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse
      (𝕜 := ℝ) (E := E) (F := E →L[ℝ] ℝ) (n := 1) (hinv x₀)
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num : (1 : ℕ∞ω) ≤ 3)
  have hgAtZ : ContDiffAt ℝ 1 (fun z : E × E => g z.1) p :=
    hg1.contDiffAt.comp p contDiffAt_fst
  have hinvAtZ : ContDiffAt ℝ 1 (fun z : E × E =>
      (ContinuousLinearMap.inverse (g z.1) : (E →L[ℝ] ℝ) →L[ℝ] E)) p := by
    exact hinvAt.comp p hgAtZ
  -- covector part (x, v) ↦ rhsCovector (Dg x) v
  have hdfAtZ : ContDiffAt ℝ 1 (fun z : E × E => fderiv ℝ g z.1) p :=
    hdf1.contDiffAt.comp p contDiffAt_fst
  have hQ : ContDiffAt ℝ 1 (fun q : (E →L[ℝ] Bilin E) × E => rhsCovector q.1 q.2)
      ((fderiv ℝ g) x₀, v₀) :=
    contDiff_rhsCovector.contDiffAt
  have hRC : ContDiffAt ℝ 1 (fun z : E × E => rhsCovector (fderiv ℝ g z.1) z.2) p := by
    have hpair : ContDiffAt ℝ 1 (fun z : E × E => ((fderiv ℝ g z.1), z.2)) p :=
      hdfAtZ.prodMk contDiffAt_snd
    exact hQ.comp p hpair
  -- apply the inverse metric to the covector (definition of `accel`)
  have happ : ContDiffAt ℝ 1 (fun z : E × E =>
      (ContinuousLinearMap.inverse (g z.1) : (E →L[ℝ] ℝ) →L[ℝ] E) (rhsCovector (fderiv ℝ g z.1) z.2)) p := by
    exact ContDiffAt.clm_apply (𝕜 := ℝ) (E := E × E) (F := E →L[ℝ] ℝ) (G := E) (n := 1)
      hinvAtZ hRC
  exact happ

/-- The geodesic vector field is `C¹` at every point of the domain. -/
lemma odeField_contDiffAt (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (x₀ v₀ : E) :
    ContDiffAt ℝ 1 (odeField g) (x₀, v₀) := by
  let p : E × E := (x₀, v₀)
  have hAcc := accel_contDiffAt g hg hinv x₀ v₀
  have hSecond : ContDiffAt ℝ 1 (fun z : E × E => (odeField g z).2) p := by
    simpa [odeField, accel] using hAcc
  have hFirst : ContDiffAt ℝ 1 (fun z : E × E => (odeField g z).1) p := by
    simpa [odeField] using (contDiffAt_snd (p := p) : ContDiffAt ℝ 1 (fun z : E × E => z.2) p)
  have hPair : ContDiffAt ℝ 1 (fun z : E × E => ((odeField g z).1, (odeField g z).2)) p :=
    hFirst.prodMk hSecond
  simpa using hPair

end ODE

end Submission.Model
