import Mathlib

namespace Work.WilCrux

lemma exists_osc_fderiv_single {b : ℕ} (f : (Fin b → ℝ) → ℝ) (j : Fin b) {ε : ℝ} (hε : 0 < ε)
    (hcd : ContDiffAt ℝ 1 f 0) :
    ∃ η : ℝ, 0 < η ∧ ∀ z z' : Fin b → ℝ, ‖z‖ < η → ‖z'‖ < η →
      |fderiv ℝ f z (Pi.single j 1) - fderiv ℝ f z' (Pi.single j 1)| < ε := by
  -- `f` is `C¹` at `0`, so its derivative is continuous there.
  have hcont : ContinuousAt (fderiv ℝ f) 0 := hcd.continuousAt_fderiv (by norm_num)
  -- evaluation of a continuous linear map at a fixed vector is continuous.
  have hEv : Continuous (fun L : (Fin b → ℝ) →L[ℝ] ℝ => L (Pi.single j (1:ℝ))) :=
    (ContinuousLinearMap.apply (𝕜 := ℝ) (E := Fin b → ℝ) (Fₗ := ℝ)
      (Pi.single j (1:ℝ))).continuous
  have hg : ContinuousAt (fun z : Fin b → ℝ => fderiv ℝ f z (Pi.single j (1:ℝ))) 0 :=
    hEv.continuousAt.comp hcont
  rw [Metric.continuousAt_iff] at hg
  obtain ⟨δ, hδpos, hδ⟩ := hg (ε / 2) (by linarith)
  refine ⟨δ, hδpos, ?_⟩
  intro z z' hz hz'
  have h1 : dist (fderiv ℝ f z (Pi.single j (1:ℝ))) (fderiv ℝ f 0 (Pi.single j (1:ℝ)))
      < ε / 2 :=
    hδ (by simpa [dist_eq_norm] using hz)
  have h2 : dist (fderiv ℝ f z' (Pi.single j (1:ℝ))) (fderiv ℝ f 0 (Pi.single j (1:ℝ)))
      < ε / 2 :=
    hδ (by simpa [dist_eq_norm] using hz')
  rw [Real.dist_eq] at h1 h2
  rw [abs_sub_comm] at h2
  calc |fderiv ℝ f z (Pi.single j (1:ℝ)) - fderiv ℝ f z' (Pi.single j (1:ℝ))|
      ≤ |fderiv ℝ f z (Pi.single j (1:ℝ)) - fderiv ℝ f 0 (Pi.single j (1:ℝ))|
        + |fderiv ℝ f 0 (Pi.single j (1:ℝ)) - fderiv ℝ f z' (Pi.single j (1:ℝ))| :=
        abs_sub_le _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add h1 h2
    _ = ε := by ring

end Work.WilCrux
