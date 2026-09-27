import Mathlib

namespace Work.Drive.Whitney

/-- Uniform closeness of the family `Q` on the shell swept by `(a + s) • ψ u` for
`s ∈ [-2,2]`: the joint `C^∞`-smoothness of the evaluation of `Q` makes the
family `q ↦ Q q` norm-continuous, hence uniformly continuous on the compact set
`[-2,2] × closedBall 0 2`; the shell is the image of that set under the
continuous map `(s,x) ↦ (a+s) • x` and `ψ` takes its values in `closedBall 0 2`. -/
theorem uniformCloseness_clampedShell {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q : (ℝ × ℝ) → E →L[ℝ] E)
    (hQ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ((ℝ × ℝ) × E) => Q p.1 p.2))
    (a : ℝ) (ψ : (ℝ × ℝ) → (ℝ × ℝ))
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (hψb : ∀ u : ℝ × ℝ, ‖ψ u‖ ≤ 2) :
    ∃ δ > 0, ∀ s ∈ Set.Icc (-2 : ℝ) 2, ∀ t ∈ Set.Icc (-2 : ℝ) 2, ∀ u : ℝ × ℝ,
      |s - t| < δ → ‖Q ((a + s) • ψ u) - Q ((a + t) • ψ u)‖ < 1 := by
  -- The joint smoothness of the evaluation upgrades to smoothness of the family itself,
  -- because `Q q` is the derivative at `0` of `v ↦ Q q v`.
  have hQcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℝ => Q q) := by
    have h := ContDiff.fderiv (𝕜 := ℝ) (m := ((⊤ : ℕ∞) : WithTop ℕ∞))
      (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
      (f := fun q : ℝ × ℝ => fun v : E => Q q v)
      (g := fun _ : ℝ × ℝ => (0 : E)) (by exact hQ)
      contDiff_const (by simp)
    simpa only [ContinuousLinearMap.fderiv] using h
  have hQcont : Continuous fun q : ℝ × ℝ => Q q := hQcd.continuous
  -- The shell map is continuous on `ℝ × (ℝ × ℝ)`.
  have hGcont : Continuous fun p : ℝ × (ℝ × ℝ) => Q ((a + p.1) • p.2) :=
    hQcont.comp ((continuous_const.add continuous_fst).smul continuous_snd)
  -- Heine–Cantor on the compact parameter set `[-2,2] × closedBall 0 2`.
  have hK : IsCompact (Set.Icc (-2 : ℝ) 2 ×ˢ Metric.closedBall (0 : ℝ × ℝ) 2) :=
    isCompact_Icc.prod (isCompact_closedBall 0 2)
  have huc := hK.uniformContinuousOn_of_continuous hGcont.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδpos, hδ⟩ := huc 1 one_pos
  refine ⟨δ, hδpos, ?_⟩
  intro s hs t ht u hst
  have hmem : ψ u ∈ Metric.closedBall (0 : ℝ × ℝ) 2 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hψb u
  have hd : dist ((s, ψ u) : ℝ × (ℝ × ℝ)) (t, ψ u) < δ := by
    rw [dist_prod_same_right, Real.dist_eq]; exact hst
  have hres := hδ (s, ψ u) ⟨hs, hmem⟩ (t, ψ u) ⟨ht, hmem⟩ hd
  simpa [dist_eq_norm] using hres

end Work.Drive.Whitney
