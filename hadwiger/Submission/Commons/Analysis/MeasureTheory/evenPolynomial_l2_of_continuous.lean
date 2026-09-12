import Mathlib
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Submission.Commons.Analysis.MeasureTheory.sphere_even_polynomial_uniform_dense
import Submission.Commons.Analysis.MeasureTheory.sphere_polynomial_uniform_dense

open Set Function MeasureTheory Metric Filter
open scoped Classical ENNReal NNReal Topology

noncomputable section

namespace Commons.Analysis.MeasureTheory

private abbrev Eu (n : ℕ) := EuclideanSpace ℝ (Fin n)
private abbrev Sph (n : ℕ) := Metric.sphere (0 : Eu n) 1

/-- For a nonnegative `c` and positive `ε`, there is a positive `δ` with `δ^2 * c ≤ ε`. -/
private lemma exists_pos_sq_mul_le {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ^2 * c ≤ ε := by
  by_cases hc0 : c = 0
  · refine ⟨1, by norm_num, ?_⟩
    rw [hc0]
    simp
    exact le_of_lt hε
  · have hcpos : 0 < c := lt_of_le_of_ne hc (by intro h; exact hc0 h.symm)
    refine ⟨Real.sqrt (ε / c), Real.sqrt_pos.2 (div_pos hε hcpos), ?_⟩
    have hsq : (Real.sqrt (ε / c))^2 = ε / c := Real.sq_sqrt (le_of_lt (div_pos hε hcpos))
    rw [hsq]
    have hmul : ε / c * c = ε := by field_simp [hc0]
    rw [hmul]

/-- Continuous functions on the unit sphere are in `L²` for the sphere measure. -/
private lemma continuous_memLp_toSphere {n : ℕ} (f : Sph n → ℝ) (hf : Continuous f) :
    MeasureTheory.MemLp f 2 (MeasureTheory.volume.toSphere : Measure (Sph n)) := by
  by_cases hnon : Nonempty (Sph n)
  · have hlim : Tendsto (fun θ : Sph n => ‖f θ‖) (cocompact (Sph n)) atBot := by
      simp
    obtain ⟨a, ha⟩ := hf.norm.exists_forall_ge hlim
    exact MemLp.of_bound hf.measurable.aestronglyMeasurable ‖f a‖ (Eventually.of_forall ha)
  · refine MemLp.of_bound hf.measurable.aestronglyMeasurable 0 ?_
    exact Eventually.of_forall (by intro θ; exact False.elim (hnon ⟨θ⟩))

/-- Restriction of a polynomial to the unit sphere is continuous. -/
private lemma continuous_eval_sphere {n : ℕ} (P : MvPolynomial (Fin n) ℝ) :
    Continuous (fun θ : Sph n => MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i) P) := by
  have hcont : Continuous (fun θ : Sph n => (spherePolyToCont n P : Sph n → ℝ) θ) :=
    (spherePolyToCont n P).continuous
  convert hcont using 1
  funext θ
  exact (spherePoly_apply_eval P θ).symm

theorem evenPolynomial_l2_of_continuous
    {n : ℕ} (h : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 → ℝ)
    (hhcont : Continuous h)
    (hheven : ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      h (⟨-θ.1, by simpa [mem_sphere_zero_iff_norm, norm_neg] using (mem_sphere_zero_iff_norm.mp θ.2)⟩ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) = h θ)
    (hhfin : MeasureTheory.MemLp h 2 MeasureTheory.volume.toSphere)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ P : MvPolynomial (Fin n) ℝ,
      (∀ x : EuclideanSpace ℝ (Fin n), (MvPolynomial.eval (fun i : Fin n => x i) P) =
        MvPolynomial.eval (fun i : Fin n => (-x) i) P) ∧
      MeasureTheory.MemLp (fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
        MvPolynomial.eval (fun i : Fin n => (θ : EuclideanSpace ℝ (Fin n)) i) P)
        2 MeasureTheory.volume.toSphere ∧
      (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          (h θ - (MvPolynomial.eval (fun i : Fin n => (θ : EuclideanSpace ℝ (Fin n)) i) P))^2
        ∂MeasureTheory.volume.toSphere) ≤ ε := by
  let μ : Measure (Sph n) := MeasureTheory.volume.toSphere
  have hc : 0 ≤ μ.real univ := by
    dsimp [μ]
    exact measureReal_nonneg
  obtain ⟨δ0, hδ0pos, hδ0le⟩ := exists_pos_sq_mul_le hc hε
  obtain ⟨P, hPeven, hPbound⟩ := sphere_even_polynomial_uniform_dense (n := n) h hhcont hheven hδ0pos
  have hPcont : Continuous
      (fun θ : Sph n => MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i) P) :=
    continuous_eval_sphere P
  have hPmem : MeasureTheory.MemLp
      (fun θ : Sph n => MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i) P) 2 μ := by
    simpa [μ] using continuous_memLp_toSphere
      (fun θ : Sph n => MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i) P) hPcont
  refine ⟨P, ?_, ?_, ?_⟩
  · exact hPeven
  · simpa [μ] using hPmem
  · change (∫ θ : Sph n,
        (h θ - MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i) P)^2 ∂μ) ≤ ε
    let g : Sph n → ℝ := fun θ =>
      (h θ - MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i) P)^2
    have hg_le : ∀ θ : Sph n, g θ ≤ δ0^2 := by
      intro θ
      dsimp [g]
      have hbθ := hPbound θ
      have hsq : |h θ - MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i) P| ≤ |δ0| := by
        simpa [abs_of_nonneg (le_of_lt hδ0pos)] using hbθ
      exact sq_le_sq.mpr hsq
    have hg_meas : MeasureTheory.AEStronglyMeasurable g μ := by
      have hcg : Continuous g := by
        dsimp [g]
        fun_prop
      exact hcg.measurable.aestronglyMeasurable
    have hg_mem : MeasureTheory.MemLp g 1 μ := MemLp.of_bound hg_meas (δ0^2) (by
      refine Eventually.of_forall ?_
      intro θ
      have hg0 : 0 ≤ g θ := by dsimp [g]; positivity
      have hg1 : g θ ≤ δ0^2 := hg_le θ
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith, hg1⟩)
    have hg_int : MeasureTheory.Integrable g μ :=
      (memLp_one_iff_integrable (f := g)).1 hg_mem
    have hconst_int : MeasureTheory.Integrable (fun _ : Sph n => δ0^2) μ :=
      integrable_const (δ0^2)
    have hmain : (∫ θ : Sph n, g θ ∂μ) ≤ (∫ θ : Sph n, δ0^2 ∂μ) :=
      integral_mono_ae hg_int hconst_int (Eventually.of_forall hg_le)
    calc
      (∫ θ : Sph n,
          (h θ - MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i) P)^2 ∂μ)
          = (∫ θ : Sph n, g θ ∂μ) := by simp [g]
      _ ≤ (∫ θ : Sph n, δ0^2 ∂μ) := hmain
      _ = δ0^2 * μ.real univ := by
        rw [integral_const]
        ring
      _ ≤ ε := by
        simpa [μ] using hδ0le

end Commons.Analysis.MeasureTheory

