import Mathlib
import Submission.Work.Drive.linearPlaneChart

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

noncomputable section

/-! ## Line-membership bookkeeping for `projLine`

These two recopy the `private` helpers of `projective_planes_meet_oddly.lean` in the direction needed
here: membership in `projLine U` is equivalent to the *associated projective line* `x.submodule` being
contained in `U`. -/

/-- A projective point whose associated line lies in `U` lies on `projLine U`. -/
lemma mem_projLine_of_submodule_le {x : Projectivization ℝ (Eucl 3)} {U : Submodule ℝ (Eucl 3)}
    (h : x.submodule ≤ U) : x ∈ projLine U :=
  ⟨x.rep, x.rep_nonzero,
    h (by rw [Projectivization.submodule_eq]; exact Submodule.mem_span_singleton_self x.rep),
    (Projectivization.mk_rep x).symm⟩

/-- A point of `projLine U` has its associated line inside `U`. -/
lemma submodule_le_of_mem_projLine {x : Projectivization ℝ (Eucl 3)} {U : Submodule ℝ (Eucl 3)}
    (h : x ∈ projLine U) : x.submodule ≤ U := by
  obtain ⟨w, hw, hwU, rfl⟩ := h
  rw [Projectivization.submodule_mk]
  exact (Submodule.span_singleton_le_iff_mem w U).mpr hwU

/-- **Two points of `ℝP³` lying on a one-dimensional projective line coincide.**  A one-dimensional
subspace has a single point of the projective space on it. -/
lemma eq_of_mem_projLine_of_finrank_eq_one {U : Submodule ℝ (Eucl 3)}
    (hU : Module.finrank ℝ ↥U = 1) {x y : Projectivization ℝ (Eucl 3)}
    (hx : x ∈ projLine U) (hy : y ∈ projLine U) : x = y := by
  haveI : Module.Free ℝ ↥U := Module.Free.of_divisionRing ℝ ↥U
  obtain ⟨v, hv0, hvall⟩ := (finrank_eq_one_iff' (K := ℝ) (V := ↥U)).1 hU
  have hv0' : (v : Eucl 3) ≠ 0 := fun hc => hv0 (Subtype.ext (by simpa using hc))
  have key : ∀ {z : Projectivization ℝ (Eucl 3)}, z ∈ projLine U →
      z = Projectivization.mk ℝ (v : Eucl 3) hv0' := by
    intro z hz
    obtain ⟨w, hw, hwU, hwz⟩ := hz
    obtain ⟨a, ha⟩ := hvall ⟨w, hwU⟩
    rw [hwz]
    exact (Projectivization.mk_eq_mk_iff' ℝ w (v : Eucl 3) hw hv0').mpr
      ⟨a, congrArg Subtype.val ha⟩
  rw [key hx, key hy]

/-- **The end contribution, set level: three linear planes of one level in general position meet in
exactly one point.**  For three linear plane charts on the level `c` whose planes have a
one-dimensional triple intersection (the general position of `Work.Drive.projective_planes_meet_oddly`)
there is exactly one point of the capping space that lies on all three.  This is the geometric content
of the bottom face computation `Σ_k bottom_k ≡ 1` of `ENDS_AND_SEAMS_NOTES.md` §2; what is *not* in
this statement is the passage from this set-level uniqueness to the engine's count over *parameter
triples*, which needs `Work.Drive.linPlaneChart_eq_iff` (the fibres are singletons off the projective
lines).  (The helpers `projLine U = U.projectivization` and "a `1`-dimensional `U` has a one-point
projectivisation" are `private` in `projective_planes_meet_oddly.lean`; only
`Work.Drive.projective_planes_meet_oddly` is public, so the intersection step may have to be redone.) -/
theorem linPlanes_meet_unique (φ : Fin 3 → Work.Drive.Eucl 3 ≃L[ℝ] Work.Drive.Eucl 3)
    (c : ℝ) (hc : 0 < c)
    (h : Module.finrank ℝ ↥(⨅ k : Fin 3, Work.Drive.linSub (φ k)) = 1) :
    ∃! p : Work.Drive.CappingSpace, ((Work.Drive.cappingSpaceHomeoProj p).1 : ℝ) = c ∧
      (Work.Drive.cappingSpaceHomeoProj p).2 ∈ Work.Drive.projLine (Work.Drive.linSub (φ 0)) ∧
      (Work.Drive.cappingSpaceHomeoProj p).2 ∈ Work.Drive.projLine (Work.Drive.linSub (φ 1)) ∧
      (Work.Drive.cappingSpaceHomeoProj p).2 ∈ Work.Drive.projLine (Work.Drive.linSub (φ 2)) := by
  haveI : Module.Free ℝ ↥(⨅ k : Fin 3, linSub (φ k)) :=
    Module.Free.of_divisionRing ℝ ↥(⨅ k : Fin 3, linSub (φ k))
  obtain ⟨v, hv0, _hvall⟩ :=
    (finrank_eq_one_iff' (K := ℝ) (V := ↥(⨅ k : Fin 3, linSub (φ k)))).1 h
  have hv0' : (v : Eucl 3) ≠ 0 := fun hc0 => hv0 (Subtype.ext (by simpa using hc0))
  have hvU : (v : Eucl 3) ∈ ⨅ k : Fin 3, linSub (φ k) := v.2
  have hvk : ∀ k : Fin 3, (v : Eucl 3) ∈ linSub (φ k) :=
    fun k => iInf_le (fun k : Fin 3 => linSub (φ k)) k hvU
  have hplevel :
      ((cappingSpaceHomeoProj (cappingVecPoint c hc (v : Eucl 3) hv0')).1 : ℝ) = c := by
    rw [cappingSpaceHomeoProj_cappingVecPoint]
  have hpcls : (cappingSpaceHomeoProj (cappingVecPoint c hc (v : Eucl 3) hv0')).2
      = Projectivization.mk ℝ (v : Eucl 3) hv0' := by
    rw [cappingSpaceHomeoProj_cappingVecPoint]
  refine ⟨cappingVecPoint c hc (v : Eucl 3) hv0', ⟨hplevel, ?_, ?_, ?_⟩, ?_⟩
  · exact ⟨(v : Eucl 3), hv0', hvk 0, hpcls⟩
  · exact ⟨(v : Eucl 3), hv0', hvk 1, hpcls⟩
  · exact ⟨(v : Eucl 3), hv0', hvk 2, hpcls⟩
  · intro q hq
    obtain ⟨hql, hq0, hq1, hq2⟩ := hq
    have hpU : (cappingSpaceHomeoProj (cappingVecPoint c hc (v : Eucl 3) hv0')).2
        ∈ projLine (⨅ k : Fin 3, linSub (φ k)) :=
      ⟨(v : Eucl 3), hv0', hvU, hpcls⟩
    have hqU : (cappingSpaceHomeoProj q).2 ∈ projLine (⨅ k : Fin 3, linSub (φ k)) := by
      refine mem_projLine_of_submodule_le (le_iInf ?_)
      intro k
      refine submodule_le_of_mem_projLine ?_
      fin_cases k
      · exact hq0
      · exact hq1
      · exact hq2
    apply cappingSpaceHomeoProj.injective
    refine Prod.ext ?_ ?_
    · exact Subtype.ext (by rw [hql, hplevel])
    · exact eq_of_mem_projLine_of_finrank_eq_one h hqU hpU

end

end Work.Drive
