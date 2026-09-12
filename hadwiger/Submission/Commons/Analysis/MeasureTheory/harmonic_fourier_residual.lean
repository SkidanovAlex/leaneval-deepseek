import Mathlib
import Submission.Commons.Analysis.MeasureTheory.harmonic_projection_orthogonal
import Submission.Commons.Analysis.MeasureTheory.harmonic_basis_pairwise_orthogonal
import Submission.Commons.Analysis.MeasureTheory.harmonic_polynomial_L2_dense_even
import Submission.Commons.Analysis.MeasureTheory.orthonormal_projection_decomp

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Commons.Analysis.MeasureTheory

theorem harmonic_fourier_residual
    {n : ℕ} [Nonempty (Fin n)]
    (d : ℕ → ℕ) (Y : ∀ k : ℕ, Fin (d k) → MvPolynomial (Fin n) ℝ)
    (hY : ∀ k : ℕ,
      (∀ j : Fin (d k), Y k j ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k ∧
        (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i (Y k j))) = 0) ∧
      (∀ i j : Fin (d k),
        (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
            MvPolynomial.eval (fun l : Fin n => (θ : EuclideanSpace ℝ (Fin n)) l) (Y k i) *
            MvPolynomial.eval (fun l : Fin n => (θ : EuclideanSpace ℝ (Fin n)) l) (Y k j)
          ∂MeasureTheory.volume.toSphere) = if i = j then 1 else 0) ∧
      (∀ H : MvPolynomial (Fin n) ℝ,
        H ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k →
        (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i H)) = 0 →
        ∃ c : Fin (d k) → ℝ, ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          MvPolynomial.eval (fun l : Fin n => (θ : EuclideanSpace ℝ (Fin n)) l) H =
            ∑ j : Fin (d k), c j * MvPolynomial.eval (fun l : Fin n => (θ : EuclideanSpace ℝ (Fin n)) l) (Y k j)))
    (a : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 → ℝ)
    (hameas : MeasureTheory.AEStronglyMeasurable a MeasureTheory.volume.toSphere)
    (haeven : ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      a (⟨-θ.1, by simpa [mem_sphere_zero_iff_norm, norm_neg] using (mem_sphere_zero_iff_norm.mp θ.2)⟩ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) = a θ)
    (hint2 : MeasureTheory.Integrable (fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 => (a θ)^2) MeasureTheory.volume.toSphere)
    (hintY : ∀ k : ℕ, ∀ j : Fin (d k), MeasureTheory.Integrable
      (fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 => a θ *
        MvPolynomial.eval (fun l : Fin n => (θ : EuclideanSpace ℝ (Fin n)) l) (Y k j))
      MeasureTheory.volume.toSphere)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ,
      (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          (a θ - ∑ k ∈ Finset.range (N + 1), ∑ j : Fin (d k),
              (∫ φ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
                  a φ * MvPolynomial.eval (fun l : Fin n => (φ : EuclideanSpace ℝ (Fin n)) l) (Y k j)
                ∂MeasureTheory.volume.toSphere) *
              MvPolynomial.eval (fun l : Fin n => (θ : EuclideanSpace ℝ (Fin n)) l) (Y k j))^2
        ∂MeasureTheory.volume.toSphere) ≤ ε := by
  classical
  obtain ⟨m, H, hHcond, hHbound⟩ := harmonic_polynomial_L2_dense_even a hameas haeven hint2 hε
  choose kdeg hkdeg using hHcond
  let N : ℕ := Finset.univ.sup kdeg
  have hN : ∀ j : Fin m, kdeg j ≤ N := fun j => Finset.le_sup (Finset.mem_univ j)
  choose cj hcj using fun j => (hY (kdeg j)).2.2 (H j) (hkdeg j).1 (hkdeg j).2
  let Sph := Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1
  let ι := Σ k : Fin (N + 1), Fin (d k)
  let y : ι → Sph → ℝ := fun u θ => MvPolynomial.eval (fun l : Fin n => (θ : EuclideanSpace ℝ (Fin n)) l) (Y ↑u.1 u.2)
  let g : Sph → ℝ := fun θ => ∑ j : Fin m, MvPolynomial.eval (fun l : Fin n => (θ : EuclideanSpace ℝ (Fin n)) l) (H j)
  let W : (Σ j : Fin m, Fin (d (kdeg j))) → ι := fun x => ⟨⟨kdeg x.1, Nat.lt_succ_of_le (hN x.1)⟩, x.2⟩
  let β : ι → ℝ := fun u => ∑ x ∈ (Finset.univ : Finset (Σ j : Fin m, Fin (d (kdeg j)))).filter (fun x => W x = u), cj x.1 x.2
  have hg : ∀ θ : Sph, g θ = ∑ u : ι, β u * y u θ := by
    intro θ
    have h1 : g θ = ∑ j : Fin m, ∑ i : Fin (d (kdeg j)), cj j i * y (W ⟨j, i⟩) θ := by
      simp only [g]
      apply Finset.sum_congr rfl
      intro j _
      rw [hcj j θ]
    rw [h1]
    rw [Finset.sum_sigma', Finset.univ_sigma_univ]
    rw [← Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset (Σ j : Fin m, Fin (d (kdeg j))))) (t := (Finset.univ : Finset ι)) (g := W) (f := fun x => cj x.1 x.2 * y (W x) θ) (fun x _ => Finset.mem_univ _)]
    apply Finset.sum_congr rfl
    intro u _
    simp only [β]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [hx.2]
  have hYint : ∀ u v : ι, MeasureTheory.Integrable (fun θ : Sph => y u θ * y v θ) MeasureTheory.volume.toSphere :=
    fun u v => Commons.Algebra.MvPolynomial.integrable_eval_mul (Y ↑u.1 u.2) (Y ↑v.1 v.2)
  have horth : ∀ u v : ι, (∫ θ : Sph, y u θ * y v θ ∂MeasureTheory.volume.toSphere) = if u = v then 1 else 0 := by
    rintro ⟨k1, i1⟩ ⟨k2, i2⟩
    by_cases hk : k1 = k2
    · subst hk
      simp only [y, Sph]
      rw [(hY (k1 : ℕ)).2.1 i1 i2]
      by_cases h : i1 = i2
      · subst h; simp
      · have hne : (⟨k1, i1⟩ : ι) ≠ ⟨k1, i2⟩ := by
          intro he
          exact h (eq_of_heq (Sigma.mk.inj_iff.mp he).2)
        simp [h, hne]
    · have hkl : (k1 : ℕ) ≠ (k2 : ℕ) := by
        intro he; exact hk (Fin.ext he)
      simp only [y, Sph]
      rw [harmonic_basis_pairwise_orthogonal d Y (fun k => ⟨(hY k).1, (hY k).2.1⟩) (k1:ℕ) (k2:ℕ) hkl i1 i2]
      have hne : (⟨k1, i1⟩ : ι) ≠ ⟨k2, i2⟩ := by
        intro he; exact hk (congrArg Sigma.fst he)
      simp [hne]
  have haint : ∀ u : ι, MeasureTheory.Integrable (fun θ : Sph => a θ * y u θ) MeasureTheory.volume.toSphere :=
    fun u => hintY ↑u.1 u.2
  let p : Sph → ℝ := fun θ => ∑ u : ι, (∫ φ : Sph, a φ * y u φ ∂MeasureTheory.volume.toSphere) * y u θ
  have hdecomp := orthonormal_projection_decomp y a g β hYint horth haint hint2 hg
  have hdecomp' : (∫ θ : Sph, (a θ - g θ)^2 ∂MeasureTheory.volume.toSphere)
      = (∫ θ : Sph, (a θ - p θ)^2 ∂MeasureTheory.volume.toSphere)
        + (∫ θ : Sph, (g θ - p θ)^2 ∂MeasureTheory.volume.toSphere) := hdecomp
  have hCp : 0 ≤ ∫ θ : Sph, (g θ - p θ)^2 ∂MeasureTheory.volume.toSphere :=
    MeasureTheory.integral_nonneg (fun θ => sq_nonneg _)
  have hBle : (∫ θ : Sph, (a θ - p θ)^2 ∂MeasureTheory.volume.toSphere)
      ≤ (∫ θ : Sph, (a θ - g θ)^2 ∂MeasureTheory.volume.toSphere) := by
    linarith [hdecomp', hCp]
  have hgle : (∫ θ : Sph, (a θ - g θ)^2 ∂MeasureTheory.volume.toSphere) ≤ ε := by
    simpa only [g] using hHbound
  refine ⟨N, ?_⟩
  have hpfun : ∀ θ : Sph, p θ = ∑ k ∈ Finset.range (N + 1), ∑ j : Fin (d k),
        (∫ φ : Sph, a φ * MvPolynomial.eval (fun l : Fin n => (φ : EuclideanSpace ℝ (Fin n)) l) (Y k j) ∂MeasureTheory.volume.toSphere) *
        MvPolynomial.eval (fun l : Fin n => (θ : EuclideanSpace ℝ (Fin n)) l) (Y k j) := by
    intro θ
    simp only [p, y]
    conv_lhs => rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
    exact Fin.sum_univ_eq_sum_range (fun k => ∑ j : Fin (d k),
        (∫ φ : Sph, a φ * MvPolynomial.eval (fun l : Fin n => (φ : EuclideanSpace ℝ (Fin n)) l) (Y k j) ∂MeasureTheory.volume.toSphere) *
        MvPolynomial.eval (fun l : Fin n => (θ : EuclideanSpace ℝ (Fin n)) l) (Y k j)) (N + 1)
  rw [show (∫ θ : Sph, (a θ - ∑ k ∈ Finset.range (N + 1), ∑ j : Fin (d k),
              (∫ φ : Sph, a φ * MvPolynomial.eval (fun l : Fin n => (φ : EuclideanSpace ℝ (Fin n)) l) (Y k j) ∂MeasureTheory.volume.toSphere) *
              MvPolynomial.eval (fun l : Fin n => (θ : EuclideanSpace ℝ (Fin n)) l) (Y k j))^2 ∂MeasureTheory.volume.toSphere)
        = (∫ θ : Sph, (a θ - p θ)^2 ∂MeasureTheory.volume.toSphere) from by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with θ
      rw [hpfun θ]]
  exact le_trans hBle hgle

end Commons.Analysis.MeasureTheory
