import Mathlib

open scoped ContDiff

namespace Work.Drive

theorem eventually_norm_eq_one_of_contMDiffAt_dense
    {Z : EuclideanSpace ℝ (Fin 2) → ℂ} {q : EuclideanSpace ℝ (Fin 2)}
    {T : Set (EuclideanSpace ℝ (Fin 2))} (hT : Dense T)
    (hZs : ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) Z q)
    (hne : Filter.Eventually (fun p => T p → ‖Z p‖ = 1) (nhds q)) :
    Filter.Eventually (fun p => ‖Z p‖ = 1) (nhds q) := by
  -- `ContMDiffAt ∞` means `C^n` at the point for every finite `n`; in particular it is
  -- `C^1` at `q`, which by locality is `C^1` (hence continuous) on a whole neighbourhood.
  rw [Filter.eventually_iff_exists_mem] at hne ⊢
  obtain ⟨U, hU, hU'⟩ := hne
  obtain ⟨u, hu, hu_smooth⟩ :=
    (contMDiffAt_iff_contMDiffOn_nhds (n := ((1 : ℕ) : WithTop ℕ∞)) (by simp)).mp
      ((contMDiffAt_infty.mp hZs) 1)
  have hg : ContinuousOn (fun p => ‖Z p‖) u := hu_smooth.continuousOn.norm
  -- an open neighbourhood `V` of `q` contained in `u ∩ U`
  obtain ⟨V, hVsub, hVopen, hqV⟩ := mem_nhds_iff.mp (Filter.inter_mem hu hU)
  refine ⟨V, hVopen.mem_nhds hqV, ?_⟩
  intro p hp
  -- `V ∩ T` is dense in `V`, and `‖Z·‖ = 1` on `V ∩ T`, so continuity on `V` gives `= 1` at `p`.
  have hcl : p ∈ closure (V ∩ T) := (hT.open_subset_closure_inter hVopen) hp
  have hcont : ContinuousWithinAt (fun p => ‖Z p‖) (V ∩ T) p :=
    ((hg.mono (hVsub.trans Set.inter_subset_left)) p hp).mono Set.inter_subset_left
  have hmap : Set.MapsTo (fun p => ‖Z p‖) (V ∩ T) {1} := by
    intro y hy
    exact hU' y ((hVsub hy.1).2) hy.2
  have := hcont.mem_closure hcl hmap
  simpa using this

end Work.Drive
