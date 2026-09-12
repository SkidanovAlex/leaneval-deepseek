import Mathlib
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Submission.Commons.Analysis.MeasureTheory.integral_even_mul_odd
import Submission.Commons.Analysis.MeasureTheory.integral_sq_add_le_two_mul
import Submission.Commons.Analysis.MeasureTheory.evenContinuous_l2_approx
import Submission.Commons.Analysis.MeasureTheory.evenPolynomial_l2_of_continuous

noncomputable section
open Set Function MeasureTheory Metric
open scoped Classical Topology ENNReal

namespace Commons.Analysis.MeasureTheory

private abbrev Eu (n : ℕ) := EuclideanSpace ℝ (Fin n)
private abbrev Sph (n : ℕ) := Metric.sphere (0 : Eu n) 1

/-- The antipodal point of a sphere point, as in the uniform-dense statement, coincides
with `antipodalSphere`. -/
private lemma sphere_neg_eq_antipodal {n : ℕ} (θ : Sph n) :
    (⟨-θ.1, by simpa [mem_sphere_zero_iff_norm, norm_neg] using (mem_sphere_zero_iff_norm.mp θ.2)⟩ : Sph n)
      = antipodalSphere (Eu n) θ := by
  ext
  rfl

theorem sphere_even_polynomial_L2_dense
    {n : ℕ} (f : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 → ℝ)
    (hfmeas : MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume.toSphere)
    (hfeven : ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      f (⟨-θ.1, by simpa [mem_sphere_zero_iff_norm, norm_neg] using (mem_sphere_zero_iff_norm.mp θ.2)⟩ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) = f θ)
    (hfin : MeasureTheory.Integrable (fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 => (f θ)^2) MeasureTheory.volume.toSphere)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ P : MvPolynomial (Fin n) ℝ,
      (∀ x : EuclideanSpace ℝ (Fin n), (MvPolynomial.eval (fun i : Fin n => x i) P) =
        MvPolynomial.eval (fun i : Fin n => (-x) i) P) ∧
      (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          (f θ - (MvPolynomial.eval (fun i : Fin n => (θ : EuclideanSpace ℝ (Fin n)) i) P))^2
        ∂MeasureTheory.volume.toSphere) ≤ ε := by
  cases n with
  | zero =>
      refine ⟨0, ?_, ?_⟩
      · intro x
        simp
      · have hμ0 : (MeasureTheory.volume.toSphere : Measure (Sph 0)) = 0 := by
          rw [Measure.toSphere_eq_zero_iff]
          infer_instance
        simp [hμ0]
        linarith
  | succ m =>
      have hmem : MemLp f 2 (MeasureTheory.volume.toSphere : Measure (Sph (Nat.succ m))) := by
        rw [memLp_two_iff_integrable_sq hfmeas]
        exact hfin
      have hfeven' : ∀ θ : Sph (Nat.succ m), f (antipodalSphere (Eu (Nat.succ m)) θ) = f θ := by
        intro θ
        rw [← sphere_neg_eq_antipodal θ]
        exact hfeven θ
      have hδ : 0 < ε / 4 := by linarith
      obtain ⟨g, hgEven, hgMem, hgB⟩ := evenContinuous_l2_approx (V := Eu (Nat.succ m))
        (f := f) hfmeas hmem hfeven' hδ
      let h : Sph (Nat.succ m) → ℝ := fun θ => (g : Sph (Nat.succ m) → ℝ) θ
      have hhcont : Continuous h := by
        dsimp [h]
        exact (BoundedContinuousFunction.continuous g)
      have hheven : ∀ θ : Sph (Nat.succ m),
          h (⟨-θ.1, by simpa [mem_sphere_zero_iff_norm, norm_neg] using (mem_sphere_zero_iff_norm.mp θ.2)⟩ : Sph (Nat.succ m)) = h θ := by
        intro θ
        dsimp [h]
        have hgθ : g (antipodalSphere (Eu (Nat.succ m)) θ) = g θ := hgEven θ
        have hgθ' : g (⟨-θ.1, by simpa [mem_sphere_zero_iff_norm, norm_neg] using (mem_sphere_zero_iff_norm.mp θ.2)⟩ : Sph (Nat.succ m)) = g θ := by
          simpa [sphere_neg_eq_antipodal θ] using hgθ
        simpa using hgθ'
      have hhfin : MemLp h 2 (MeasureTheory.volume.toSphere : Measure (Sph (Nat.succ m))) := by
        dsimp [h]
        exact hgMem
      obtain ⟨P, hPeven, hPmem, hPB⟩ := evenPolynomial_l2_of_continuous (n := Nat.succ m) h hhcont hheven hhfin hδ
      let a : Sph (Nat.succ m) → ℝ := fun θ => f θ - (g : Sph (Nat.succ m) → ℝ) θ
      let b : Sph (Nat.succ m) → ℝ := fun θ => (g : Sph (Nat.succ m) → ℝ) θ -
        (MvPolynomial.eval (fun i : Fin (Nat.succ m) => (θ : Eu (Nat.succ m)) i) P)
      have haMem : MemLp a 2 (MeasureTheory.volume.toSphere : Measure (Sph (Nat.succ m))) := by
        dsimp [a]
        exact hmem.sub hgMem
      have hbMem : MemLp b 2 (MeasureTheory.volume.toSphere : Measure (Sph (Nat.succ m))) := by
        dsimp [b]
        exact hgMem.sub hPmem
      have hcomb := integral_sq_add_le_two_mul (μ := (MeasureTheory.volume.toSphere : Measure (Sph (Nat.succ m)))) haMem hbMem
      have hpoint : (fun θ : Sph (Nat.succ m) => (a θ + b θ)^2) =
          fun θ : Sph (Nat.succ m) => (f θ - (MvPolynomial.eval (fun i : Fin (Nat.succ m) => (θ : Eu (Nat.succ m)) i) P))^2 := by
        funext θ
        congr 1
        dsimp [a, b]
        ring
      refine ⟨P, hPeven, ?_⟩
      have hfinal : (∫ θ : Sph (Nat.succ m),
          (f θ - (MvPolynomial.eval (fun i : Fin (Nat.succ m) => (θ : Eu (Nat.succ m)) i) P))^2
        ∂MeasureTheory.volume.toSphere) ≤ ε := by
        calc
          (∫ θ : Sph (Nat.succ m),
              (f θ - (MvPolynomial.eval (fun i : Fin (Nat.succ m) => (θ : Eu (Nat.succ m)) i) P))^2
            ∂MeasureTheory.volume.toSphere)
              = (∫ θ : Sph (Nat.succ m), (a θ + b θ)^2 ∂MeasureTheory.volume.toSphere) := by
                  rw [← hpoint]
          _ ≤ 2 * (∫ θ : Sph (Nat.succ m), (a θ)^2 ∂MeasureTheory.volume.toSphere) +
                2 * (∫ θ : Sph (Nat.succ m), (b θ)^2 ∂MeasureTheory.volume.toSphere) := hcomb
          _ ≤ ε := by
              have hb1 : (∫ θ : Sph (Nat.succ m), (a θ)^2 ∂MeasureTheory.volume.toSphere) ≤ ε / 4 := by
                simpa [a] using hgB
              have hb2 : (∫ θ : Sph (Nat.succ m), (b θ)^2 ∂MeasureTheory.volume.toSphere) ≤ ε / 4 := by
                simpa [b, h] using hPB
              nlinarith
      exact hfinal

end Commons.Analysis.MeasureTheory
