import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import ChallengeDeps
import Submission.Work.SmallBoxSuperadd
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END


/-!
# Quadratic homogeneity of the small-box energy under pointwise scaling

The hinge that lets the `eB`-infimum over all `CSBox` states collapse to the
normalised one: `sboxE(c•Φ) = c²·sboxE(Φ)` (smooth states), with the two
halves `kinWord` (fderiv-linear spine) and `qLHSword` (state-independent
weight).  The counts `cS1`/`cS2`/`cnPlus` follow from the same aP/aQ
linearity spine (added below as they compile).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
set_option maxHeartbeats 800000

/-- Quadratic homogeneity of `qLHSword` under pointwise scaling: the weight
`−μ·Σw₁-fibre + ½·Σw` is independent of the state, so
`qLHSword(c•Φ) = c²·qLHSword(Φ)`. -/
lemma qLHSword_smul {N : ℕ} {s μ : ℝ} (w w1 : ℝ³ → ℝ³ → ℝ) {Φ : X N → ℝ} (c : ℝ) :
    qLHSword (N := N) s μ w w1 (c • Φ) = (c ^ 2) * qLHSword (N := N) s μ w w1 Φ := by
  unfold qLHSword
  let body : X N → ℝ := fun x => - μ * (∑ i : Fin N, w1Fibre s w1 (x i))
      + (1 / 2) * (∑ p ∈ pairSet N, w (x p.1) (x p.2))
  have hle : ∀ x : X N, ((c • Φ) x) ^ 2 * body x = (c ^ 2) * ((Φ x) ^ 2 * body x) := by
    intro x
    simp [Pi.smul_apply, smul_eq_mul]
    ring
  calc
    (∫ x in abox N s, ((c • Φ) x) ^ 2 * body x)
        = (∫ x in abox N s, (c ^ 2) * ((Φ x) ^ 2 * body x)) := by
            apply integral_congr_ae
            exact ae_of_all _ hle
    _ = (c ^ 2) * (∫ x in abox N s, (Φ x) ^ 2 * body x) := by
            simpa using (MeasureTheory.integral_const_mul (μ := (volume : Measure (X N)).restrict (abox N s))
              (r := c ^ 2) (f := fun x : X N => (Φ x) ^ 2 * body x))

/-- Quadratic homogeneity of `kinWord` under pointwise scaling: the kinetic
word is a sum of squares of `fderiv`, and `fderiv (c•Φ) = c • fderiv Φ`. -/
lemma kinWord_smul {N : ℕ} {ℓ : ℝ} {Φ : X N → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (c : ℝ) :
    kinWord N ℓ (c • Φ) = (c ^ 2) * kinWord N ℓ Φ := by
  unfold kinWord
  have hpk : ∀ i : Fin N, ∀ k : Fin 3,
      (∫ x in abox N ℓ, (fderiv ℝ (c • Φ) x (kcDir N i k)) ^ 2)
        = (c ^ 2) * (∫ x in abox N ℓ, (fderiv ℝ Φ x (kcDir N i k)) ^ 2) := by
    intro i k
    have hle : ∀ x : X N, (fderiv ℝ (c • Φ) x (kcDir N i k)) ^ 2
        = (c ^ 2) * (fderiv ℝ Φ x (kcDir N i k)) ^ 2 := by
      intro x
      have hd : DifferentiableAt ℝ Φ x :=
        (hΦ.differentiable (by norm_num : (∞ : WithTop ℕ∞) ≠ 0)).differentiableAt (x := x)
      have hf := fderiv_const_smul hd c
      rw [hf]
      simp [smul_eq_mul]
      ring
    calc
      (∫ x in abox N ℓ, (fderiv ℝ (c • Φ) x (kcDir N i k)) ^ 2)
          = (∫ x in abox N ℓ, (c ^ 2) * (fderiv ℝ Φ x (kcDir N i k)) ^ 2) := by
              apply integral_congr_ae
              exact ae_of_all _ hle
      _ = (c ^ 2) * (∫ x in abox N ℓ, (fderiv ℝ Φ x (kcDir N i k)) ^ 2) := by
              simpa using (MeasureTheory.integral_const_mul (μ := (volume : Measure (X N)).restrict (abox N ℓ))
                (r := c ^ 2) (f := fun x : X N => (fderiv ℝ Φ x (kcDir N i k)) ^ 2))
  calc
    (∑ i : Fin N, ∑ k : Fin 3, ∫ x in abox N ℓ, (fderiv ℝ (c • Φ) x (kcDir N i k)) ^ 2)
        = (∑ i : Fin N, ∑ k : Fin 3, (c ^ 2) * (∫ x in abox N ℓ, (fderiv ℝ Φ x (kcDir N i k)) ^ 2)) := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro k hk
            exact hpk i k
    _ = (c ^ 2) * (∑ i : Fin N, ∑ k : Fin 3, ∫ x in abox N ℓ, (fderiv ℝ Φ x (kcDir N i k)) ^ 2) := by
            have h1 : (∑ i : Fin N, ∑ k : Fin 3, (c ^ 2) * (∫ x in abox N ℓ, (fderiv ℝ Φ x (kcDir N i k)) ^ 2))
                = (∑ i : Fin N, (c ^ 2) * (∑ k : Fin 3, ∫ x in abox N ℓ, (fderiv ℝ Φ x (kcDir N i k)) ^ 2)) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [← Finset.mul_sum]
            rw [h1]
            rw [← Finset.mul_sum]

/-- **Quadratic homogeneity of the small-box energy** under pointwise
scaling: `sboxE(c•Φ) = c²·sboxE(Φ)` (smooth states).  This is the hinge that
lets the `eB`-infimum over all `CSBox` states collapse to the normalised
one (`sboxE(Φ)/∫Φ² = sboxE(Φ/√∫Φ²)`). -/
lemma sboxE_smul {N : ℕ} {s μ : ℝ} (w w1 : ℝ³ → ℝ³ → ℝ) {Φ : X N → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) (c : ℝ) :
    sboxE N s μ w w1 (c • Φ) = (c ^ 2) * sboxE N s μ w w1 Φ := by
  unfold sboxE
  rw [kinWord_smul hΦ c, qLHSword_smul w w1 c]
  ring

lemma aP_const_smul (ℓ : ℝ) {N : ℕ} (i : Fin N) (Φ : X N → ℝ) (c : ℝ) (x : X N) :
    aP ℓ i (c • Φ) x = c * aP ℓ i Φ x := by
  unfold aP
  have h : (∫ y in acube ℓ, (c • Φ) (Function.update x i y))
      = c * (∫ y in acube ℓ, Φ (Function.update x i y)) := by
    simpa [Pi.smul_apply, smul_eq_mul] using
      (MeasureTheory.integral_const_mul (μ := (volume : Measure ℝ³).restrict (acube ℓ)) (r := c)
        (f := fun y : ℝ³ => Φ (Function.update x i y)))
  rw [h]
  ring

lemma aQ_const_smul (ℓ : ℝ) {N : ℕ} (i : Fin N) (Φ : X N → ℝ) (c : ℝ) (x : X N) :
    aQ ℓ i (c • Φ) x = c * aQ ℓ i Φ x := by
  simp [aQ, aP_const_smul, Pi.smul_apply, smul_eq_mul]
  ring

lemma cS1_smul {N : ℕ} (ℓ : ℝ) (Φ : X N → ℝ) (c : ℝ) :
    cS1 ℓ (c • Φ) = (c ^ 2) * cS1 ℓ Φ := by
  unfold cS1
  have hper : ∀ i : Fin N,
      (∫ x in abox N ℓ, (aP ℓ i (c • Φ) x) ^ 2) = (c ^ 2) * (∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2) := by
    intro i
    have hpt : ∀ x : X N, (aP ℓ i (c • Φ) x) ^ 2 = (c ^ 2) * (aP ℓ i Φ x) ^ 2 := by
      intro x
      rw [aP_const_smul]
      ring
    calc
      (∫ x in abox N ℓ, (aP ℓ i (c • Φ) x) ^ 2)
          = (∫ x in abox N ℓ, (c ^ 2) * (aP ℓ i Φ x) ^ 2) := by
              apply integral_congr_ae
              exact ae_of_all _ hpt
      _ = (c ^ 2) * (∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2) := by
              simpa using (MeasureTheory.integral_const_mul (μ := (volume : Measure (X N)).restrict (abox N ℓ))
                (r := c ^ 2) (f := fun x : X N => (aP ℓ i Φ x) ^ 2))
  calc
    (∑ i : Fin N, ∫ x in abox N ℓ, (aP ℓ i (c • Φ) x) ^ 2)
        = (∑ i : Fin N, (c ^ 2) * (∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2)) := by
            exact Finset.sum_congr rfl (fun i hi => hper i)
    _ = (c ^ 2) * (∑ i : Fin N, ∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2) := by
            rw [← Finset.mul_sum]

lemma cnPlus_smul {N : ℕ} (ℓ : ℝ) (Φ : X N → ℝ) (c : ℝ) :
    cnPlus ℓ (c • Φ) = (c ^ 2) * cnPlus ℓ Φ := by
  unfold cnPlus
  have hper : ∀ i : Fin N,
      (∫ x in abox N ℓ, (aQ ℓ i (c • Φ) x) ^ 2) = (c ^ 2) * (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2) := by
    intro i
    have hpt : ∀ x : X N, (aQ ℓ i (c • Φ) x) ^ 2 = (c ^ 2) * (aQ ℓ i Φ x) ^ 2 := by
      intro x
      rw [aQ_const_smul]
      ring
    calc
      (∫ x in abox N ℓ, (aQ ℓ i (c • Φ) x) ^ 2)
          = (∫ x in abox N ℓ, (c ^ 2) * (aQ ℓ i Φ x) ^ 2) := by
              apply integral_congr_ae
              exact ae_of_all _ hpt
      _ = (c ^ 2) * (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2) := by
              simpa using (MeasureTheory.integral_const_mul (μ := (volume : Measure (X N)).restrict (abox N ℓ))
                (r := c ^ 2) (f := fun x : X N => (aQ ℓ i Φ x) ^ 2))
  calc
    (∑ i : Fin N, ∫ x in abox N ℓ, (aQ ℓ i (c • Φ) x) ^ 2)
        = (∑ i : Fin N, (c ^ 2) * (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2)) := by
            exact Finset.sum_congr rfl (fun i hi => hper i)
    _ = (c ^ 2) * (∑ i : Fin N, ∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2) := by
            rw [← Finset.mul_sum]

lemma cS2_smul {N : ℕ} (ℓ : ℝ) (Φ : X N → ℝ) (c : ℝ) :
    cS2 ℓ (c • Φ) = (c ^ 2) * cS2 ℓ Φ := by
  unfold cS2
  have hper : ∀ p : Fin N × Fin N, p ∈ pairSet N →
      (∫ x in abox N ℓ, (aP ℓ p.1 (aP ℓ p.2 (c • Φ)) x) ^ 2)
        = (c ^ 2) * (∫ x in abox N ℓ, (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2) := by
    intro p hp
    have hpp : ∀ x : X N, aP ℓ p.1 (aP ℓ p.2 (c • Φ)) x = c * aP ℓ p.1 (aP ℓ p.2 Φ) x := by
      intro x
      have h₂ := aP_const_smul ℓ p.1 (aP ℓ p.2 Φ) c x
      -- aP p.1 (c • (aP p.2 Φ)) x = c * aP p.1 (aP p.2 Φ) x ;  and
      -- aP p.2 (c•Φ) = c • (aP p.2 Φ) pointwise
      have h₁ : aP ℓ p.2 (c • Φ) = c • (aP ℓ p.2 Φ) := by
        funext y
        simpa [smul_eq_mul] using (aP_const_smul ℓ p.2 Φ c y)
      calc
        aP ℓ p.1 (aP ℓ p.2 (c • Φ)) x = aP ℓ p.1 (c • (aP ℓ p.2 Φ)) x := by rw [h₁]
        _ = c * aP ℓ p.1 (aP ℓ p.2 Φ) x := by simpa [smul_eq_mul, Pi.smul_apply] using h₂
    have hpt : ∀ x : X N, (aP ℓ p.1 (aP ℓ p.2 (c • Φ)) x) ^ 2
        = (c ^ 2) * (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 := by
      intro x
      rw [hpp]
      ring
    calc
      (∫ x in abox N ℓ, (aP ℓ p.1 (aP ℓ p.2 (c • Φ)) x) ^ 2)
          = (∫ x in abox N ℓ, (c ^ 2) * (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2) := by
              apply integral_congr_ae
              exact ae_of_all _ hpt
      _ = (c ^ 2) * (∫ x in abox N ℓ, (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2) := by
              simpa using (MeasureTheory.integral_const_mul (μ := (volume : Measure (X N)).restrict (abox N ℓ))
                (r := c ^ 2) (f := fun x : X N => (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2))
  calc
    (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aP ℓ p.1 (aP ℓ p.2 (c • Φ)) x) ^ 2)
        = (∑ p ∈ pairSet N, (c ^ 2) * (∫ x in abox N ℓ, (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2)) := by
            exact Finset.sum_congr rfl hper
    _ = (c ^ 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2) := by
            rw [← Finset.mul_sum]

end BoseGases

end Submission
