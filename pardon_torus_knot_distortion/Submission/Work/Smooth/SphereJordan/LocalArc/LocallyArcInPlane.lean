import Mathlib
import Submission.Work.Smooth.SphereJordan.LocalArc.Basic
import Submission.Work.Smooth.SphereJordan.LocalArc.IsLocallyArcOfIsOpen

/-!
# Locally-arc subsets of the plane

If every point `x` of a subset `L ⊆ ℂ` has a neighbourhood in `L` parametrised injectively and
continuously by the open interval `(-1,1)`, then `L` is locally an arc in the sense of
`IsLocallyArc`.
-/

namespace Work.Smooth.SphereJordan.LocalArc

open Set Function

open scoped Topology

noncomputable section

/-- **Locally-arc sets in the plane.** -/
theorem isLocallyArc_of_locallyArcInPlane {L : Set ℂ}
    (hloc : ∀ x ∈ L, ∃ (ε : ℝ) (γ : ℝ → ℂ), 0 < ε ∧ Continuous γ ∧ Function.Injective γ ∧
      γ 0 = x ∧ γ '' Set.Ioo (-1) 1 = L ∩ Metric.ball x ε) :
    Work.Smooth.SphereJordan.IsLocallyArc ↥L := by
  classical
  intro x
  obtain ⟨ε, γ, hε, hγc, hγi, hγ0, hγim⟩ := hloc x.1 x.2
  set V : Set ↥L := {y : ↥L | y.1 ∈ Metric.ball x.1 ε} with hVdef
  have hVopen : IsOpen V := Metric.isOpen_ball.preimage continuous_subtype_val
  have hxV : x ∈ V := by
    show x.1 ∈ Metric.ball x.1 ε
    rw [Metric.mem_ball, dist_self]
    exact hε
  have hex : ∀ y : ↥V, ∃ u : ℝ, u ∈ Set.Ioo (-1) 1 ∧ γ u = y.1.1 := by
    intro y
    have hy : y.1.1 ∈ L ∩ Metric.ball x.1 ε := ⟨y.1.2, y.2⟩
    rw [← hγim] at hy
    obtain ⟨u, hu, hue⟩ := hy
    exact ⟨u, hu, hue⟩
  choose u hu_mem hu_val using hex
  have hu_cont : Continuous fun y : ↥V => u y := by
    rw [continuous_iff_seqContinuous]
    intro ys y hy
    apply Filter.tendsto_of_subseq_tendsto
    intro ns hns
    have hmem : ∀ n : ℕ, u (ys (ns n)) ∈ Set.Icc (-1:ℝ) 1 :=
      fun n => ⟨(hu_mem (ys (ns n))).1.le, (hu_mem (ys (ns n))).2.le⟩
    obtain ⟨a, ha, φ, hφ, hlim⟩ := IsCompact.tendsto_subseq isCompact_Icc hmem
    refine ⟨φ, ?_⟩
    have h1 : Filter.Tendsto (fun n => γ (u (ys (ns (φ n))))) Filter.atTop (𝓝 (γ a)) :=
      hγc.continuousAt.tendsto.comp hlim
    have h2 : Filter.Tendsto (fun n => ((ys (ns (φ n)) : ↥V).1.1)) Filter.atTop
        (𝓝 (y.1.1)) := by
      have h3 : Filter.Tendsto (fun n => ys (ns (φ n))) Filter.atTop (𝓝 y) :=
        hy.comp (hns.comp hφ.tendsto_atTop)
      exact continuous_subtype_val.continuousAt.tendsto.comp
        (continuous_subtype_val.continuousAt.tendsto.comp h3)
    have heq : (fun n => γ (u (ys (ns (φ n))))) =
        fun n => ((ys (ns (φ n)) : ↥V).1.1) :=
      funext fun n => hu_val (ys (ns (φ n)))
    rw [heq] at h1
    have h4 : γ a = y.1.1 := tendsto_nhds_unique h1 h2
    have h5 : a = u y := hγi (by rw [h4, hu_val y])
    rw [h5] at hlim
    exact hlim
  have hmem : ∀ t : ℝ, γ ((homeomorphIoo (1:ℝ) one_pos t : ↥(Set.Ioo (-(1:ℝ)) (1:ℝ))) : ℝ) ∈
      L ∩ Metric.ball x.1 ε := by
    intro t
    rw [← hγim]
    exact ⟨_, (homeomorphIoo (1:ℝ) one_pos t).2, rfl⟩
  let F : ℝ → ↥V := fun t =>
    ⟨⟨γ ((homeomorphIoo (1:ℝ) one_pos t : ↥(Set.Ioo (-(1:ℝ)) (1:ℝ))) : ℝ), (hmem t).1⟩,
      (hmem t).2⟩
  let G : ↥V → ℝ := fun y => (homeomorphIoo (1:ℝ) one_pos).symm ⟨u y, hu_mem y⟩
  have hleft : ∀ t : ℝ, G (F t) = t := by
    intro t
    have h1 : u (F t) = ((homeomorphIoo (1:ℝ) one_pos t : ↥(Set.Ioo (-(1:ℝ)) (1:ℝ))) : ℝ) := by
      refine hγi ?_
      show γ (u (F t)) = γ ((homeomorphIoo (1:ℝ) one_pos t : ↥(Set.Ioo (-(1:ℝ)) (1:ℝ))) : ℝ)
      rw [hu_val]
    show (homeomorphIoo (1:ℝ) one_pos).symm ⟨u (F t), hu_mem (F t)⟩ = t
    have h2 : (⟨u (F t), hu_mem (F t)⟩ : ↥(Set.Ioo (-(1:ℝ)) (1:ℝ))) =
        (homeomorphIoo (1:ℝ) one_pos) t := Subtype.ext h1
    rw [h2, Homeomorph.symm_apply_apply]
  have hright : ∀ y : ↥V, F (G y) = y := by
    intro y
    apply Subtype.ext
    apply Subtype.ext
    show γ ((homeomorphIoo (1:ℝ) one_pos (G y) : ↥(Set.Ioo (-(1:ℝ)) (1:ℝ))) : ℝ) = y.1.1
    rw [Homeomorph.apply_symm_apply]
    exact hu_val y
  have hcontF : Continuous F := Continuous.subtype_mk (Continuous.subtype_mk
    (hγc.comp (continuous_subtype_val.comp (homeomorphIoo (1:ℝ) one_pos).continuous))
    (fun t => (hmem t).1)) (fun t => (hmem t).2)
  have hcontG : Continuous G := (homeomorphIoo (1:ℝ) one_pos).symm.continuous.comp
    (Continuous.subtype_mk hu_cont (fun y => hu_mem y))
  refine ⟨{ V := V, isOpen_V := hVopen, mem_V := hxV, homeo := ?_, homeo_zero := ?_ }⟩
  · exact { toFun := F, invFun := G, left_inv := hleft, right_inv := hright, continuous_toFun := hcontF, continuous_invFun := hcontG }
  · show F 0 = ⟨x, hxV⟩
    apply Subtype.ext
    apply Subtype.ext
    show γ ((homeomorphIoo (1:ℝ) one_pos 0 : ↥(Set.Ioo (-(1:ℝ)) (1:ℝ))) : ℝ) = x.1
    rw [homeomorphIoo_zero]
    exact hγ0

end

end Work.Smooth.SphereJordan.LocalArc
