import Mathlib

namespace Work.Drive

/-- A continuous `T`-periodic function on `ℝ` is uniformly continuous, quantitatively: for every
`ε > 0` there is `δ > 0` such that `|x - y| ≤ δ` implies `‖f x - f y‖ ≤ ε`. -/
lemma nmf_uniform_modulus_periodic {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} {T : ℝ}
    (hT : 0 < T) (hper : Function.Periodic f T) (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x y : ℝ, |x - y| ≤ δ → ‖f x - f y‖ ≤ ε := by
  -- `f` is uniformly continuous on the compact window `[-T, T]` (Heine–Cantor).
  have huc : UniformContinuousOn f (Set.Icc (-T) T) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hf.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := huc ε hε
  refine ⟨δ₀ / 2, by linarith, ?_⟩
  intro x y hxy
  -- Any point of `ℝ` has a translate within `T / 2` of any prescribed base point, and if that
  -- translate is already farther than `T / 2` from the base point one may use the point itself.
  have hclaim : ∀ a b : ℝ, ∃ b' : ℝ, f b' = f b ∧ |a - b'| ≤ T / 2 ∧ |a - b'| ≤ |a - b| := by
    intro a b
    rcases le_or_gt |a - b| (T / 2) with hab | hab
    · exact ⟨b, rfl, hab, le_rfl⟩
    · obtain ⟨b', hb'mem, hval⟩ := hper.exists_mem_Ico hT b (a - T / 2)
      rw [Set.mem_Ico] at hb'mem
      have hb'T : |a - b'| ≤ T / 2 := by
        rw [abs_le]
        constructor <;> linarith [hb'mem.1, hb'mem.2]
      exact ⟨b', hval.symm, hb'T, le_trans hb'T hab.le⟩
  obtain ⟨y₁, hy₁val, hy₁leT, hy₁le⟩ := hclaim x y
  -- Shift the pair `(x, y₁)` by a common multiple of the period so that it lands in `[-T, T]²`.
  obtain ⟨k, hk, _⟩ := existsUnique_add_zsmul_mem_Ico hT x (-(T / 2))
  rw [Set.mem_Ico] at hk
  have hyb := abs_le.mp hy₁leT
  have hx'mem : x + k • T ∈ Set.Icc (-T) T := by
    rw [Set.mem_Icc]
    exact ⟨by linarith [hk.1], by linarith [hk.2]⟩
  have hy'mem : y₁ + k • T ∈ Set.Icc (-T) T := by
    rw [Set.mem_Icc]
    constructor <;> linarith [hk.1, hk.2, hyb.1, hyb.2]
  have hx'val : f (x + k • T) = f x := hper.zsmul k x
  have hy'val : f (y₁ + k • T) = f y := (hper.zsmul k y₁).trans hy₁val
  have hdist : |(x + k • T) - (y₁ + k • T)| ≤ |x - y| := by
    have h1 : (x + k • T) - (y₁ + k • T) = x - y₁ := by ring
    rw [h1]
    exact hy₁le
  have hlt : dist (x + k • T) (y₁ + k • T) < δ₀ := by
    rw [Real.dist_eq]
    linarith
  have hfin := hδ₀ (x + k • T) hx'mem (y₁ + k • T) hy'mem hlt
  rw [dist_eq_norm, hx'val, hy'val] at hfin
  linarith

end Work.Drive
