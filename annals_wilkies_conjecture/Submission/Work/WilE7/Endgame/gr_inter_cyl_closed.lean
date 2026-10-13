/-
  Area E7, Endgame: the graph `gr C g` of a function continuous on `C`, restricted
  to the cylinder `cyl C`, is the trace on the cylinder of a closed set.

  Indeed `g` is continuous on `C` exactly when its graph is closed *relative to*
  `C × ℝ`; explicitly the closed set

    `F = closure (gr C g) ∩ {z | |z (Fin.last p)| ≤ 1}`

  satisfies `F ∩ cyl C = gr C g ∩ cyl C`: any point of `closure (gr C g)` that
  projects into `C` and lies at height at most `1` is already on the graph.
-/
import Mathlib
import Submission.Work.WilE7.DecompDefs

open scoped Topology
open Filter

namespace Work.WilE7.Endgame

/-- If `g` is continuous on `C`, then a point of `closure (gr C g)` whose first
`p` coordinates lie in `C` already lies on the graph `gr C g`. -/
theorem closure_gr_inter_init_mem {p : ℕ} {C : Set (Fin p → ℝ)} {g : (Fin p → ℝ) → ℝ}
    (hg : ContinuousOn g C) :
    closure (Work.WilE7.gr C g) ∩ {z : Fin (p+1) → ℝ | Fin.init z ∈ C} ⊆
      Work.WilE7.gr C g := by
  intro z hz
  obtain ⟨hzcl, hzC⟩ := hz
  obtain ⟨u, hu_mem, hu_tend⟩ := mem_closure_iff_seq_limit.mp hzcl
  simp only [Work.WilE7.gr, Set.mem_ofPred_eq] at hu_mem ⊢
  refine ⟨hzC, ?_⟩
  have huinit_mem : ∀ n, Fin.init (u n) ∈ C := fun n => (hu_mem n).1
  have hueq : ∀ n, u n (Fin.last p) = g (Fin.init (u n)) := fun n => (hu_mem n).2
  have hinit_tend : Tendsto (fun n => Fin.init (u n)) atTop (𝓝 (Fin.init z)) := by
    rw [tendsto_pi_nhds]
    intro i
    exact tendsto_pi_nhds.mp hu_tend (Fin.castSucc i)
  have hCwm : Tendsto (fun n => Fin.init (u n)) atTop (𝓝[C] (Fin.init z)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hinit_tend, Filter.Eventually.of_forall huinit_mem⟩
  have hg_tend : Tendsto (fun n => g (Fin.init (u n))) atTop (𝓝 (g (Fin.init z))) :=
    (hg.continuousWithinAt hzC).tendsto.comp hCwm
  have hlast_tend : Tendsto (fun n => u n (Fin.last p)) atTop (𝓝 (z (Fin.last p))) :=
    tendsto_pi_nhds.mp hu_tend (Fin.last p)
  rw [show (fun n => u n (Fin.last p)) = (fun n => g (Fin.init (u n))) from
    funext hueq] at hlast_tend
  exact tendsto_nhds_unique hlast_tend hg_tend

theorem gr_inter_cyl_closed {p : ℕ} {C : Set (Fin p → ℝ)}
    {g : (Fin p → ℝ) → ℝ} (hg : ContinuousOn g C) :
    ∃ F : Set (Fin (p + 1) → ℝ), IsClosed F ∧
      F ∩ Work.WilE7.cyl C = Work.WilE7.gr C g ∩ Work.WilE7.cyl C := by
  refine ⟨closure (Work.WilE7.gr C g) ∩ {z | |z (Fin.last p)| ≤ 1}, ?_, ?_⟩
  · exact isClosed_closure.inter
      (isClosed_le (continuous_apply (Fin.last p)).abs continuous_const)
  · apply Set.Subset.antisymm
    · intro z hz
      obtain ⟨hzF, hzcyl⟩ := hz
      obtain ⟨hzcl, _⟩ := hzF
      simp only [Work.WilE7.cyl, Set.mem_ofPred_eq] at hzcyl
      exact ⟨closure_gr_inter_init_mem hg ⟨hzcl, hzcyl.1⟩, hzcyl⟩
    · intro z hz
      obtain ⟨hzgr, hzcyl⟩ := hz
      have hzgr' := hzgr
      rw [Work.WilE7.gr] at hzgr'
      simp only [Work.WilE7.cyl, Set.mem_ofPred_eq] at hzcyl
      exact ⟨⟨subset_closure hzgr, hzcyl.2⟩, hzcyl⟩

end Work.WilE7.Endgame
