import Mathlib

namespace Work.Transfer

/-- A nonidentically-zero analytic function on a ball is bounded below by a positive constant on
some circle of radius `< R` centred at an interior point `c_s` (whose `R`-ball is still inside). -/
theorem exists_sphere_le_norm {f : ℂ → ℂ} {c₀ c_s : ℂ} {ρ R : ℝ}
    (hR : 0 < R) (hcs : c_s ∈ Metric.ball c₀ ρ)
    (hsub : Metric.ball c_s R ⊆ Metric.ball c₀ ρ)
    (hf : AnalyticOnNhd ℂ f (Metric.ball c₀ ρ))
    (hne : ∃ z ∈ Metric.ball c₀ ρ, f z ≠ 0) :
    ∃ r ∈ Set.Ioo (0 : ℝ) R, ∃ δ : ℝ, 0 < δ ∧
      ∀ z ∈ Metric.sphere c_s r, δ ≤ ‖f z‖ := by
  have hR2 : (0 : ℝ) < R / 2 := by linarith
  have hKsub : Metric.closedBall c_s (R / 2) ⊆ Metric.ball c₀ ρ :=
    (Metric.closedBall_subset_ball (by linarith : R / 2 < R)).trans hsub
  -- The zero set of `f` is finite inside the compact disk `closedBall c_s (R/2)`.
  have hfin : (Metric.closedBall c_s (R / 2) ∩ {z | f z = 0}).Finite := by
    by_contra hinf
    rw [Set.not_finite] at hinf
    obtain ⟨x, hxK, hacc⟩ :=
      hinf.exists_accPt_of_subset_isCompact (isCompact_closedBall c_s (R / 2))
        Set.inter_subset_left
    have hxU : x ∈ Metric.ball c₀ ρ := hKsub hxK
    have hfreq : ∃ᶠ y in nhdsWithin x ({x}ᶜ : Set ℂ), f y = 0 := by
      rw [accPt_iff_frequently_nhdsNE] at hacc
      exact hacc.mono fun y hy => hy.2
    have hzero : Set.EqOn f 0 (Metric.ball c₀ ρ) :=
      hf.eqOn_zero_of_preconnected_of_frequently_eq_zero Metric.isPreconnected_ball hxU hfreq
    obtain ⟨z, hz, hfz⟩ := hne
    exact hfz (hzero hz)
  set M : Set ℝ := (fun z => dist z c_s) '' (Metric.closedBall c_s (R / 2) ∩ {z | f z = 0})
    with hMdef
  have hMfin : M.Finite := hfin.image (fun z => dist z c_s)
  obtain ⟨r, hrIoo, hrM⟩ := (Set.Ioo_infinite hR2).exists_notMem_finite hMfin
  have hrR : r ∈ Set.Ioo (0 : ℝ) R := ⟨hrIoo.1, lt_trans hrIoo.2 (by linarith)⟩
  have hsphere_ne : ∀ z ∈ Metric.sphere c_s r, f z ≠ 0 := by
    intro z hz hfz
    have hzd : dist z c_s = r := by rwa [Metric.mem_sphere] at hz
    have hzK : z ∈ Metric.closedBall c_s (R / 2) := by
      rw [Metric.mem_closedBall, hzd]
      linarith [hrIoo.2]
    have hmem : dist z c_s ∈ M := ⟨z, ⟨hzK, hfz⟩, rfl⟩
    rw [hzd] at hmem
    exact hrM hmem
  have hspheresub : Metric.sphere c_s r ⊆ Metric.ball c₀ ρ :=
    (Metric.sphere_subset_closedBall.trans
      (Metric.closedBall_subset_closedBall (le_of_lt hrIoo.2))).trans hKsub
  have hcont : ContinuousOn (fun z => ‖f z‖) (Metric.sphere c_s r) :=
    (hf.continuousOn.mono hspheresub).norm
  obtain ⟨δ, hδpos, hδle⟩ :=
    (isCompact_sphere c_s r).exists_forall_le' hcont (a := 0)
      (fun z hz => norm_pos_iff.mpr (hsphere_ne z hz))
  exact ⟨r, hrR, δ, hδpos, hδle⟩

end Work.Transfer
