import Mathlib
import Submission.Work.Drive.exists_linPlaneCharts_hgen
import Submission.Work.Drive.linPlaneReparamCount
import Submission.Work.Drive.linCommonPoint

/-!
# `hrank` and `hgen` for the *glued* chart family `A ∘ (coordinate permutation)`

`Work.Drive.exists_linPlaneCharts_hgen` proves that the three linear plane charts
`linPlaneChart (coordPermCLM (coordPerms k)) c hc` are in general position (`hrank`) and that their
common point is never attained on the boundary circle (`hgen`).  The ends clause of the counting route
(`Work.Drive.glueDesignData`) needs the *same* two properties for the family

> `φ k := (coordPermCLM (coordPerms k)).trans A = A ∘ (the k-th coordinate permutation)`,

where `A : Eucl 3 ≃L[ℝ] Eucl 3` is a linear isomorphism chosen generically near the identity.  This file
transports `hrank`/`hgen` from the coordinate-permutation witness along an arbitrary invertible `A` —
no genericity of `A` is needed for these two clauses.

The mechanism is that `linSub` is `linStd.map`, so it commutes with composition
(`Work.Drive.linSub_trans`), and that the infimum of a family of planes is transported to the infimum of
the transported family by an invertible map (`Submodule.map_iInf`).  Hence the triple intersection of the
glued family is `A (ℝ ∙ single 0 1)`, still a line; and on the boundary circle the `k`-th chart's class
is that of `A (P k (linVecC z))`, whose `0`-th coordinate vanishes, so it is never the class of the
common point `A (single 0 1)`.

* `Work.Drive.linSub_trans` — `linSub (e.trans f) = (linSub e).map f`;
* `Work.Drive.iInf_linSub_trans` — the triple intersection of the glued family is `A (ℝ ∙ single 0 1)`;
* `Work.Drive.finrank_iInf_linSub_trans` — `hrank` for the glued family;
* `Work.Drive.exists_hrank_hgen_trans` — `hrank` and `hgen` for the glued family, for every `A`.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

noncomputable section

/-! ## 1. `linSub` is natural in the linear equivalence -/

/-- **`linSub` of a composite**: the plane of `e.trans f` is the image of the plane of `e` under `f`.
This is the definitional identity `linSub φ = linStd.map φ` together with `Submodule.map_comp`. -/
lemma linSub_trans (e f : Eucl 3 ≃L[ℝ] Eucl 3) :
    linSub (e.trans f) = (linSub e).map f.toLinearEquiv.toLinearMap := by
  rw [linSub, linSub, ← Submodule.map_comp]
  rfl

/-! ## 2. The triple intersection of the glued family -/

/-- **The triple intersection of the glued coordinate-permutation family is the image of the
coordinate line under `A`.**  The key point is that `⨅ k (S k).map A = (⨅ k, S k).map A` for an
*injective* linear map (`Submodule.map_iInf`), so that `Work.Drive.iInf_linSub_coordPerms_eq` can be
applied under `A`. -/
theorem iInf_linSub_trans (A : Eucl 3 ≃L[ℝ] Eucl 3) :
    (⨅ k : Fin 3, linSub ((coordPermCLM (coordPerms k)).trans A))
      = ℝ ∙ A (EuclideanSpace.single 0 (1:ℝ)) := by
  have h : ∀ k, linSub ((coordPermCLM (coordPerms k)).trans A)
      = (linSub (coordPermCLM (coordPerms k))).map A.toLinearEquiv.toLinearMap :=
    fun k => linSub_trans _ _
  simp only [h]
  rw [← Submodule.map_iInf A.toLinearEquiv.toLinearMap A.injective,
    iInf_linSub_coordPerms_eq, Submodule.map_span]
  simp

/-- **`hrank` for the glued family**: for every linear isomorphism `A`, the three planes
`linSub ((coordPermCLM (coordPerms k)).trans A)` meet in a line. -/
theorem finrank_iInf_linSub_trans (A : Eucl 3 ≃L[ℝ] Eucl 3) :
    Module.finrank ℝ ↥(⨅ k : Fin 3,
      linSub ((coordPermCLM (coordPerms k)).trans A)) = 1 := by
  rw [iInf_linSub_trans A]
  exact finrank_span_singleton
    (fun hh => hgenSingle_ne_zero (A.injective (by rw [hh, map_zero])))

/-! ## 3. The generator of the intersection lies in every plane -/

/-- `A (single 0 1)` lies in each of the three glued planes. -/
lemma mem_linSub_trans_hgenSingle (A : Eucl 3 ≃L[ℝ] Eucl 3) (k : Fin 3) :
    A (EuclideanSpace.single 0 (1:ℝ)) ∈ linSub ((coordPermCLM (coordPerms k)).trans A) := by
  rw [linSub_trans]
  exact Submodule.mem_map.mpr ⟨EuclideanSpace.single 0 (1:ℝ), mem_linSub_hgenSingle k, rfl⟩

/-- `A (single 0 1)` is non-zero for an invertible `A`. -/
lemma trans_hgenSingle_ne_zero (A : Eucl 3 ≃L[ℝ] Eucl 3) :
    A (EuclideanSpace.single 0 (1:ℝ)) ≠ 0 :=
  fun hh => hgenSingle_ne_zero (A.injective (by rw [hh, map_zero]))

/-! ## 4. The boundary circle avoids the common point -/

/-- **`hrank` and `hgen` for the glued family `A ∘ (coordinate permutation)`.**  The general-position
witness is `Work.Drive.finrank_iInf_linSub_trans`; the common point is the class of `A (single 0 1)` at
the level `c` (`Work.Drive.eq_linCommonPt` applied to the memberships
`Work.Drive.mem_linSub_trans_hgenSingle`), while on the boundary circle the `k`-th chart's class is that
of `A (P k (linVecC z))`; the two differ because `P k (linVecC z)` has vanishing `0`-th coordinate while
`single 0 1` has `0`-th coordinate `1`. -/
theorem exists_hrank_hgen_trans (A : Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ) (hc : 0 < c) :
    ∃ h : Module.finrank ℝ ↥(⨅ k : Fin 3, linSub ((coordPermCLM (coordPerms k)).trans A)) = 1,
      ∀ (k : Fin 3) (z : ℂ), ‖z‖ = 1 →
        linPlaneChart ((coordPermCLM (coordPerms k)).trans A) c hc z
          ≠ linCommonPt (fun k => (coordPermCLM (coordPerms k)).trans A) c hc h := by
  refine ⟨finrank_iInf_linSub_trans A, ?_⟩
  intro k z hz heq
  have hA : A (EuclideanSpace.single 0 (1:ℝ)) ≠ 0 := trans_hgenSingle_ne_zero A
  -- The common point of the glued planes is the class of `A (single 0 1)` at the level `c`.
  have hpt : cappingVecPoint c hc (A (EuclideanSpace.single 0 (1:ℝ))) hA
      = linCommonPt (fun k => (coordPermCLM (coordPerms k)).trans A) c hc
          (finrank_iInf_linSub_trans A) := by
    refine eq_linCommonPt (fun k => (coordPermCLM (coordPerms k)).trans A) c hc _ ?_ ?_
    · rw [cappingSpaceHomeoProj_cappingVecPoint]
    · intro j
      rw [cappingSpaceHomeoProj_cappingVecPoint]
      exact ⟨_, hA, mem_linSub_trans_hgenSingle A j, rfl⟩
  -- Equality of the chart value with the common point is an equality of projective classes.
  have hcls := congrArg (fun p => (cappingSpaceHomeoProj p).2) (heq.trans hpt.symm)
  rw [cappingSpaceHomeoProj_linPlaneChart, cappingSpaceHomeoProj_cappingVecPoint] at hcls
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff ℝ
    (A (coordPermCLM (coordPerms k) (linVecC z)))
    (A (EuclideanSpace.single 0 (1:ℝ))) _ _).mp hcls
  -- `a • A (single 0 1) = A (P k (linVecC z))`; apply `A.symm`.
  have ha' : a • (EuclideanSpace.single 0 (1:ℝ) : Eucl 3)
      = coordPermCLM (coordPerms k) (linVecC z) := by
    have h2 := congrArg (fun v : Eucl 3 => A.symm v) ha
    simpa [Units.smul_def, map_smul] using h2
  -- The `0`-th coordinate of `P k (linVecC z)` vanishes on the boundary circle.
  have hzero : (coordPermCLM (coordPerms k) (linVecC z)) 0 = 0 := by
    rw [coordPermCLM_apply, coordPerms_symm_zero k, linVecC_apply_two, hz]
    norm_num
  have hkey : ((a : ℝ)) = 0 := by
    have h := congrArg (fun v : Eucl 3 => v 0) ha'
    rw [hzero] at h
    rw [Units.smul_def, PiLp.smul_apply, PiLp.single_eq_same, smul_eq_mul, mul_one] at h
    exact h
  exact Units.ne_zero a hkey

end

end Work.Drive
