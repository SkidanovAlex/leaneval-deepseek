import Mathlib.Analysis.Calculus.FDeriv.Extend

namespace Commons.Analysis.Calculus

theorem tendsto_inv_smul_of_tendsto_deriv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} {a : F} {T : ℝ} (hT : 0 < T)
    (hf : ∀ t ∈ Set.Ioc 0 T, HasDerivAt f (deriv f t) t)
    (hf0 : f 0 = 0)
    (hcont : Filter.Tendsto f (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hfd : Filter.Tendsto (deriv f) (nhdsWithin 0 (Set.Ioi 0)) (nhds a)) :
    Filter.Tendsto (fun t => t⁻¹ • f t) (nhdsWithin 0 (Set.Ioi 0)) (nhds a) := by
  have hdiff : DifferentiableOn ℝ f (Set.Ioc 0 T) := fun t ht =>
    (hf t ht).differentiableAt.differentiableWithinAt
  have hcont' : ContinuousWithinAt f (Set.Ioc 0 T) 0 := by
    have : ContinuousWithinAt f (Set.Ioi (0 : ℝ)) 0 := by
      simpa [ContinuousWithinAt, hf0] using hcont
    exact this.mono Set.Ioc_subset_Ioi_self
  have hs : Set.Ioc (0 : ℝ) T ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
    rw [mem_nhdsGT_iff_exists_Ioo_subset]
    exact ⟨T, hT, fun x hx => ⟨hx.1, hx.2.le⟩⟩
  have hd := hasDerivWithinAt_Ici_of_tendsto_deriv hdiff hcont' hs hfd
  rw [hasDerivWithinAt_iff_tendsto_slope] at hd
  have hset : (Set.Ici (0 : ℝ) \ {0}) = Set.Ioi 0 := by
    ext t
    simp only [Set.mem_sdiff, Set.mem_Ici, Set.mem_singleton_iff, Set.mem_Ioi]
    exact ⟨fun h => lt_of_le_of_ne h.1 (Ne.symm h.2), fun h => ⟨le_of_lt h, ne_of_gt h⟩⟩
  rw [hset] at hd
  have hfun : slope f 0 = fun t : ℝ => t⁻¹ • f t := by
    funext t
    simp [slope_def_module, hf0]
  rw [hfun] at hd
  exact hd

end Commons.Analysis.Calculus