import Mathlib
import Submission.Work.Drive.Mono.TiltedTraceData
import Submission.Work.Topology.SphereSlicing.All
import Submission.Work.JordanBrouwer3.sphereSides_boxSphere
import Submission.Work.Smooth.BoxGeneric.Bridge
import Submission.Work.Drive.Mono.isPreconnected_of_isCompact_ordConnected_fibers
import Submission.Work.Drive.Mono.exists_frontier_mem_inter_hyperplane_inter_halfspace
import Submission.Work.Drive.Mono.frontier_inter_hyperplane_inter_halfspace_assembly

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion Set

noncomputable section

/-- **The intersection of the box sphere with a tilted slab and a wall is connected or empty.**

`K := closure (PBox s c σ)` is a compact convex body with nonempty interior whose frontier is the
box sphere `{y | boxNorm c σ y = s}` (`Work.JordanBrouwer3.frontier_closure_PBox`).  The slab
`{|⟪v,·⟫ - a| ≤ h}` is convex and the wall `{ℓ ≤ lam}` is a halfspace, so

`X = frontier K ∩ {|⟪v,·⟫ - a| ≤ h} ∩ {ℓ ≤ lam}`.

Sweeping `X` by the functional `f = ⟪v,·⟫`: its image `T = f '' X` is the image of the convex set
`K ∩ slab ∩ wall` under a linear functional (hence an interval), and the fibre of the sweep over
`t ∈ T` is `frontier K ∩ {f = t} ∩ {ℓ ≤ lam}` — the frontier of a compact convex body of `ℝ³` cut
by a plane and a halfspace, preconnected by
`Work.Drive.Mono.isPreconnected_frontier_inter_hyperplane_inter_halfspace`.  Hence `X` is
preconnected by `Work.Drive.Mono.isPreconnected_of_isCompact_ordConnected_fibers`. -/
theorem boxSphere_inter_slab_halfspace_connected (s : ℝ) (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) (v : LeanEval.KnotTheory.PardonDistortion.R3) (h : ℝ)
    (ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ) (lam : ℝ) (hv : ‖v‖ = 1) (hh : 0 < h)
    (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0) :
    IsConnected ({y : LeanEval.KnotTheory.PardonDistortion.R3 | Submission.boxNorm c σ y = s}
        ∩ {y : LeanEval.KnotTheory.PardonDistortion.R3 | |inner ℝ v y - (inner ℝ v c + u)| ≤ h}
        ∩ {y : LeanEval.KnotTheory.PardonDistortion.R3 | ℓ y ≤ lam})
      ∨ ({y : LeanEval.KnotTheory.PardonDistortion.R3 | Submission.boxNorm c σ y = s}
        ∩ {y : LeanEval.KnotTheory.PardonDistortion.R3 | |inner ℝ v y - (inner ℝ v c + u)| ≤ h}
        ∩ {y : LeanEval.KnotTheory.PardonDistortion.R3 | ℓ y ≤ lam} = ∅) := by
  rcases lt_trichotomy s 0 with hlt | heq | hgt
  · -- the box sphere is empty for negative levels
    right
    have hA : {y : R3 | Submission.boxNorm c σ y = s} = ∅ := by
      ext y
      simp only [Set.mem_ofPred_eq, mem_empty_iff_false, iff_false]
      intro hy
      have hnn := Submission.boxNorm_nonneg c σ y
      linarith
    rw [hA]
    simp
  · -- level zero: the box sphere is the centre
    subst heq
    have hbox : {y : R3 | Submission.boxNorm c σ y = 0} = {c} :=
      Work.Smooth.BoxGeneric.BoxSphere_zero_eq_singleton c σ
    set S : Set R3 := {y : R3 | |inner ℝ v y - (inner ℝ v c + u)| ≤ h} with hS
    set H : Set R3 := {y : R3 | ℓ y ≤ lam} with hH
    by_cases hc : c ∈ S ∩ H
    · left
      have hset : {y : R3 | Submission.boxNorm c σ y = 0} ∩ S ∩ H = {c} := by
        rw [hbox]
        refine Subset.antisymm ?_ ?_
        · rintro y ⟨⟨hy, -⟩, -⟩
          simpa using hy
        · intro y hy
          rw [mem_singleton_iff] at hy
          subst hy
          exact ⟨⟨rfl, hc.1⟩, hc.2⟩
      rw [hset]
      exact isConnected_singleton
    · right
      have hset : {y : R3 | Submission.boxNorm c σ y = 0} ∩ S ∩ H = ∅ := by
        rw [hbox]
        ext y
        simp only [mem_inter_iff, mem_singleton_iff, mem_empty_iff_false, iff_false]
        rintro ⟨⟨rfl, hyS⟩, hyH⟩
        exact hc ⟨hyS, hyH⟩
      rw [hset]
  · -- the main case `s > 0`
    set S : Set R3 := {y : R3 | |inner ℝ v y - (inner ℝ v c + u)| ≤ h} with hS
    set H : Set R3 := {y : R3 | ℓ y ≤ lam} with hH
    set K : Set R3 := closure (Submission.PBox s c σ) with hK
    have hfr : frontier K = {y : R3 | Submission.boxNorm c σ y = s} := by
      rw [hK]
      exact Work.JordanBrouwer3.frontier_closure_PBox hgt c σ
    set X : Set R3 := {y : R3 | Submission.boxNorm c σ y = s} ∩ S ∩ H with hX
    have hXfr : X = frontier K ∩ S ∩ H := by rw [hX, hfr]
    -- the compact convex body `K`
    have hPBox_open : IsOpen (Submission.PBox s c σ) :=
      Work.Topology.SphereSlicing.isOpen_PBox s c σ
    have hc_mem : c ∈ Submission.PBox s c σ := by
      rw [Submission.mem_PBox]
      intro i
      rw [sub_self, abs_zero]
      exact mul_pos (Submission.boxSide_pos i) hgt
    have hKcomp : IsCompact K := by
      rw [hK]
      refine IsCompact.of_isClosed_subset (isCompact_closedBall c ((5 / 2) * s)) isClosed_closure ?_
      refine closure_minimal ?_ Metric.isClosed_closedBall
      exact (Submission.PBox_subset_ball s (le_of_lt hgt) c σ).trans Metric.ball_subset_closedBall
    have hKc : Convex ℝ K := by
      rw [hK]
      exact (Work.Topology.SphereSlicing.convex_PBox s c σ).closure
    have hKint : (interior K).Nonempty := by
      rw [hK]
      exact ⟨c, hPBox_open.subset_interior_closure hc_mem⟩
    -- convexity and closedness of the slab and the wall
    have hSc : Convex ℝ S := by
      rw [hS]
      have h1 : {y : R3 | |inner ℝ v y - (inner ℝ v c + u)| ≤ h}
          = (fun y : R3 => inner ℝ v y) ⁻¹'
              Set.Icc (inner ℝ v c + u - h) (inner ℝ v c + u + h) := by
        ext y
        simp only [Set.mem_ofPred_eq, mem_preimage, mem_Icc, abs_le]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨by linarith, by linarith⟩
        · rintro ⟨h1, h2⟩
          exact ⟨by linarith, by linarith⟩
      rw [h1]
      exact (convex_Icc _ _).linear_preimage (innerSL ℝ v).toLinearMap
    have hHc : Convex ℝ H := by
      rw [hH]
      exact convex_halfSpace_le ℓ.toLinearMap.isLinear lam
    have hSclosed : IsClosed S := by
      rw [hS]
      exact isClosed_le (by fun_prop : Continuous fun y : R3 => |inner ℝ v y - (inner ℝ v c + u)|)
        continuous_const
    have hHclosed : IsClosed H := by
      rw [hH]
      exact isClosed_le ℓ.continuous continuous_const
    -- the sweep functional
    set f : R3 →L[ℝ] ℝ := innerSL ℝ v with hf
    have hfapply : ∀ y : R3, f y = inner ℝ v y := fun y => innerSL_apply_apply ℝ v y
    have hfne : f ≠ 0 := by
      intro h0
      have h1 : f v = 0 := by rw [h0]; rfl
      rw [hfapply] at h1
      have hvne : v ≠ 0 := by
        intro hv0
        rw [hv0] at hv
        simp at hv
      exact (ne_of_gt (real_inner_self_pos.mpr hvne)) h1
    -- the base of the sweep
    set T : Set ℝ := f '' (K ∩ S ∩ H) with hT
    have hKCc : Convex ℝ (K ∩ S ∩ H) := (hKc.inter hSc).inter hHc
    have hTord : T.OrdConnected := by
      rw [hT]
      exact (hKCc.linear_image f.toLinearMap).ordConnected
    -- the sweep of `X` hits exactly `T`
    have hfX : f '' X = T := by
      rw [hT]
      refine Subset.antisymm ?_ ?_
      · refine Set.image_mono ?_
        rw [hXfr]
        rintro y ⟨⟨hyfr, hyS⟩, hyH⟩
        exact ⟨⟨hKcomp.isClosed.frontier_subset hyfr, hyS⟩, hyH⟩
      · rintro t ⟨y, ⟨⟨hyK, hyS⟩, hyH⟩, rfl⟩
        -- a frontier point of `K` in the same hyperplane, below the wall
        obtain ⟨z, hzfr, hzf, hzH⟩ :=
          exists_frontier_mem_inter_hyperplane_inter_halfspace hKc hKcomp hKint hyK rfl hyH
        have hzBox : z ∈ {y : R3 | Submission.boxNorm c σ y = s} := by
          rw [← hfr]
          exact hzfr
        rw [hS] at hyS
        rw [Set.mem_ofPred_eq] at hyS
        rw [← hfapply y] at hyS
        have hzS : z ∈ S := by
          rw [hS]
          simp only [Set.mem_ofPred_eq]
          rw [← hfapply z, hzf]
          exact hyS
        exact ⟨z, ⟨⟨hzBox, hzS⟩, hzH⟩, hzf⟩
    -- the fibres of the sweep
    have hfib : ∀ t ∈ f '' X, IsPreconnected (X ∩ f ⁻¹' {t}) := by
      intro t ht
      obtain ⟨z₀, hz₀, hz₀f⟩ := ht
      have ht_slab : |f z₀ - (inner ℝ v c + u)| ≤ h := by
        rw [hXfr, hS] at hz₀
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq] at hz₀
        rw [← hfapply z₀] at hz₀
        exact hz₀.1.2
      rw [hz₀f] at ht_slab
      have hset : X ∩ f ⁻¹' {t}
          = frontier K ∩ {y : R3 | f y = t} ∩ {y : R3 | ℓ y ≤ lam} := by
        ext y
        rw [hXfr]
        simp only [mem_inter_iff, Set.mem_ofPred_eq, mem_preimage, mem_singleton_iff]
        constructor
        · rintro ⟨⟨⟨hfy, hyS⟩, hyH⟩, hyf⟩
          exact ⟨⟨hfy, hyf⟩, hyH⟩
        · rintro ⟨⟨hfy, hyf⟩, hyH⟩
          refine ⟨⟨⟨hfy, ?_⟩, hyH⟩, hyf⟩
          rw [hS]
          simp only [Set.mem_ofPred_eq]
          rw [← hfapply y, hyf]
          exact ht_slab
      rw [hset]
      exact isPreconnected_frontier_inter_hyperplane_inter_halfspace_assembly
        hKc hKcomp hKint hfne t lam
    -- `X` is compact
    have hXcomp : IsCompact X := by
      have hsub : X ⊆ Work.Topology.SphereSlicing.BoxSphere s c σ := by
        rw [hXfr]
        intro y hy
        have : y ∈ {y : R3 | Submission.boxNorm c σ y = s} := by
          rw [← hfr]
          exact hy.1.1
        exact this
      have hcl : IsClosed X := by
        rw [hXfr]
        exact (isClosed_frontier.inter hSclosed).inter hHclosed
      exact (Work.Topology.SphereSlicing.isCompact_BoxSphere hgt c σ).of_isClosed_subset hcl hsub
    have hpre : IsPreconnected X :=
      isPreconnected_of_isCompact_ordConnected_fibers hXcomp f.continuous (hfX.symm ▸ hTord) hfib
    rcases eq_empty_or_nonempty X with hXe | hXne
    · exact Or.inr hXe
    · exact Or.inl ⟨hXne, hpre⟩

end

end Work.Drive.Mono
