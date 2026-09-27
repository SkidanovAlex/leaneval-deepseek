import Mathlib
import Submission.Work.Drive.ManifoldParity.InterSetDefs
import Submission.Work.Drive.ManifoldParity.exists_local_graph
import Submission.Work.Drive.ChartBridge
import Submission.Work.Drive.ManifoldParity.FlowSetupPairing
import Submission.Work.Drive.ManifoldParity.InterSetCover
import Submission.Work.Drive.ManifoldParity.boxMapsTo_flowV_interSet
import Submission.Work.Drive.ManifoldParity.face_data_interSet
import Submission.Work.Drive.ManifoldParity.finite_bInterSet

namespace Work.Drive.ManifoldParity

open scoped Manifold ContDiff in
theorem even_ncard_bInterSet_of_tangential_field {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (D : EuclideanSpace ℝ (Fin 2) → M) (N : EuclideanSpace ℝ (Fin 3) → M)
    (hD : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) D)
    (hN : ContMDiff (𝓡 3) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) N)
    (htrans : ∀ x : Work.Drive.Amb 4, x ∈ Submission.Drive.unitBox 4 →
      D (Work.Drive.sqPart x) = N (Work.Drive.cbPart x) →
      LinearMap.range (mfderiv (𝓡 2) (𝓡 4) D (Work.Drive.sqPart x)).toLinearMap ⊔
        LinearMap.range (mfderiv (𝓡 3) (𝓡 4) N (Work.Drive.cbPart x)).toLinearMap = ⊤)
    (hface : ∀ x : Work.Drive.Amb 4, x ∈ Submission.Drive.unitBox 4 →
      D (Work.Drive.sqPart x) = N (Work.Drive.cbPart x) → x ∈ Submission.Drive.unitBoxBdry 4 →
      (∃ i : Fin 2, (Work.Drive.sqPart x i = 0 ∨ Work.Drive.sqPart x i = 1) ∧
          (∀ j : Fin 2, j ≠ i → Work.Drive.sqPart x j ∈ Set.Ioo (0 : ℝ) 1) ∧
          (∀ j : Fin 3, Work.Drive.cbPart x j ∈ Set.Ioo (0 : ℝ) 1) ∧
          ∃ (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)),
            mfderiv (𝓡 2) (𝓡 4) D (Work.Drive.sqPart x) σ =
              mfderiv (𝓡 3) (𝓡 4) N (Work.Drive.cbPart x) τ ∧ σ i ≠ 0)
      ∨ (∃ j : Fin 3, (Work.Drive.cbPart x j = 0 ∨ Work.Drive.cbPart x j = 1) ∧
          (∀ k : Fin 3, k ≠ j → Work.Drive.cbPart x k ∈ Set.Ioo (0 : ℝ) 1) ∧
          (∀ i : Fin 2, Work.Drive.sqPart x i ∈ Set.Ioo (0 : ℝ) 1) ∧
          ∃ (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)),
            mfderiv (𝓡 2) (𝓡 4) D (Work.Drive.sqPart x) σ =
              mfderiv (𝓡 3) (𝓡 4) N (Work.Drive.cbPart x) τ ∧ τ j ≠ 0))
    (V : Work.Drive.Amb 4 → Work.Drive.Amb 4) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hVsupp : HasCompactSupport V)
    (hVne : ∀ x : Work.Drive.Amb 4, x ∈ Submission.Drive.unitBox 4 →
      D (Work.Drive.sqPart x) = N (Work.Drive.cbPart x) → V x ≠ 0)
    (hVtan : ∀ x : Work.Drive.Amb 4, x ∈ Submission.Drive.unitBox 4 →
      D (Work.Drive.sqPart x) = N (Work.Drive.cbPart x) → ∀ p : M,
      x ∈ Work.Drive.chartRegion p D N →
      fderiv ℝ (Work.Drive.chartDiff p D N) x (V x) = 0) :
    (Work.Drive.bInterSet D N).Finite ∧ Even (Work.Drive.bInterSet D N).ncard := by
  classical
  -- The face condition in the form used by the flow argument (Section `Interfaces`).
  have hface' : ∀ b : Work.Drive.Amb 4, b ∈ Work.Drive.interSet D N →
      b ∈ Submission.Drive.unitBoxBdry 4 →
      ∃ i : Fin 5, (b i = 0 ∨ b i = 1) ∧ (∀ j : Fin 5, j ≠ i → b j ∈ Set.Ioo (0 : ℝ) 1) ∧
        V b i ≠ 0 :=
    fun b hbK hbB => face_data_interSet D N hD hN htrans hface V hVtan hVne b hbK hbB
  -- The intersection set is preserved by the flow while the flow line stays in the box.
  have hmapsTo : ∀ x ∈ Work.Drive.interSet D N, ∀ t : ℝ,
      (∀ u ∈ Set.uIcc (0 : ℝ) t, Work.Drive.flowV V hV hVsupp u x ∈ Submission.Drive.unitBox 4) →
      Work.Drive.flowV V hV hVsupp t x ∈ Work.Drive.interSet D N :=
    fun x hx t hbox =>
      boxMapsTo_flowV_interSet D N hD hN htrans V hV hVsupp hVtan hface' x hx t hbox
  -- A finite cover by chart regions of the intersection set.
  obtain ⟨Cov⟩ := Work.Drive.exists_flowCover D N hD hN htrans V hV hVsupp hVtan hVne hmapsTo
  have hS : (Work.Drive.interSetSetup D N V hV hVsupp hmapsTo).K = Work.Drive.interSet D N := rfl
  have hset : Work.Drive.bInterSet D N =
      Work.Drive.interSet D N ∩ Submission.Drive.unitBoxBdry 4 := by
    ext x
    simp only [Work.Drive.mem_bInterSet, Work.Drive.mem_interSet, Set.mem_inter_iff, and_assoc]
  refine ⟨finite_bInterSet D N hD hN htrans hface, ?_⟩
  have heven : Even ((Work.Drive.interSet D N) ∩ Submission.Drive.unitBoxBdry 4).ncard := by
    have h := Work.Drive.even_ncard_boundary (Work.Drive.interSetSetup D N V hV hVsupp hmapsTo) Cov
      (fun b hb => hface' b hb.1 hb.2)
    rwa [hS] at h
  rw [hset]
  exact heven

end Work.Drive.ManifoldParity
