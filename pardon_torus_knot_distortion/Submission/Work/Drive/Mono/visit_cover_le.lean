import Mathlib
import Submission.Work.Drive.Mono.LevelCountLeDefs
import Submission.Work.Drive.Mono.visit_cover

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

variable {K : Knot} {s u : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {v : R3} {h : ℝ}
variable {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ}

/-! ## Every in-box trace parameter of the level lies in the closure of a visit through a crossing

The statement `Work.Drive.Mono.visit_cover` proves this for the *strictly* below-level face
parameters (`facePts`, `wallW < lam`).  Replacing the strict inequality by `wallW ≤ lam` adds the
corner parameters `{|cutG| = h ∧ wallW = lam}`; the proof goes through verbatim because

* on the face branch only `boxA < 0` and `|cutG| = h` are used: the one-sided neighbourhood in
  `slabVisit` produced by `exists_Ioo_side_slabVisit` needs the transversality `hface` at a face
  parameter, nothing about the level `lam`;
* on the wall branch the point already lies in the open slab, hence in `slabVisit`. -/

/-- **The cover of the level's in-box trace parameters by the closures of the crossings.**  Every
face parameter at or below the level (`facePtsLe`) and every wall parameter of the level lies in
the closure of the visit of a crossing parameter. -/
theorem visit_cover_le
    {K : LeanEval.KnotTheory.PardonDistortion.Knot} {s u : ℝ}
    {c : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)}
    {v : LeanEval.KnotTheory.PardonDistortion.R3} {h : ℝ}
    {ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ} {lam : ℝ}
    (hh : 0 < h)
    (hcross : ∀ t ∈ Work.Drive.Mono.slabVisit K s c σ u v h,
      ∃ w : ℝ, w ∈ Work.Drive.Mono.visit (Work.Drive.Mono.slabVisit K s c σ u v h) t ∧
        Work.Drive.Mono.cutG K c u v w = 0)
    (hface : ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
        |Work.Drive.Mono.cutG K c u v t| = h →
        deriv (fun r : ℝ => inner ℝ v (K.curve r)) t ≠ 0) :
    ∀ p ∈ Work.Drive.Mono.facePtsLe K s c σ u v h ℓ lam ∪
        Work.Drive.Mono.wallPts K s c σ u v h ℓ lam,
      ∃ z ∈ Work.Drive.Mono.cutCross K s c σ u v,
        p ∈ closure (Work.Drive.Mono.visit (Work.Drive.Mono.slabVisit K s c σ u v h) z) := by
  intro p hp
  rcases hp with hp | hp
  · -- `p` is a face parameter of the level: one side of `p` lies in the slab visit set
    rw [facePtsLe, Set.mem_ofPred_eq] at hp
    obtain ⟨hboxp, hcutp, -⟩ := hp
    obtain ⟨δ, hδ, hside⟩ := exists_Ioo_side_slabVisit (K := K) (s := s) (c := c) (σ := σ)
      (u := u) (v := v) (h := h) hh hface hboxp hcutp
    rcases hside with hleft | hright
    · have ht0 : p - δ / 2 ∈ Ioo (p - δ) p := ⟨by linarith, by linarith⟩
      have hslab : p - δ / 2 ∈ slabVisit K s c σ u v h := hleft _ ht0
      obtain ⟨z, hz, hz0⟩ := hcross _ hslab
      refine ⟨z, ?_, ?_⟩
      · rw [cutCross, Set.mem_ofPred_eq]
        exact ⟨(connectedComponentIn_subset _ _ hz).1, hz0⟩
      · have hsub : Ioo (p - δ) p ⊆ connectedComponentIn (slabVisit K s c σ u v h) (p - δ / 2) :=
          IsPreconnected.subset_connectedComponentIn isPreconnected_Ioo ht0 hleft
        have hpcl : p ∈ closure (Ioo (p - δ) p) := by
          rw [closure_Ioo (by linarith : p - δ ≠ p)]
          exact ⟨by linarith, le_rfl⟩
        have hmem := closure_mono hsub hpcl
        have hcomp := connectedComponentIn_eq hz
        show p ∈ closure (visit (slabVisit K s c σ u v h) z)
        unfold visit
        rw [← hcomp]
        exact hmem
    · have ht0 : p + δ / 2 ∈ Ioo p (p + δ) := ⟨by linarith, by linarith⟩
      have hslab : p + δ / 2 ∈ slabVisit K s c σ u v h := hright _ ht0
      obtain ⟨z, hz, hz0⟩ := hcross _ hslab
      refine ⟨z, ?_, ?_⟩
      · rw [cutCross, Set.mem_ofPred_eq]
        exact ⟨(connectedComponentIn_subset _ _ hz).1, hz0⟩
      · have hsub : Ioo p (p + δ) ⊆ connectedComponentIn (slabVisit K s c σ u v h) (p + δ / 2) :=
          IsPreconnected.subset_connectedComponentIn isPreconnected_Ioo ht0 hright
        have hpcl : p ∈ closure (Ioo p (p + δ)) := by
          rw [closure_Ioo (by linarith : p ≠ p + δ)]
          exact ⟨le_rfl, by linarith⟩
        have hmem := closure_mono hsub hpcl
        have hcomp := connectedComponentIn_eq hz
        show p ∈ closure (visit (slabVisit K s c σ u v h) z)
        unfold visit
        rw [← hcomp]
        exact hmem
  · -- `p` is a wall parameter: it already lies in the slab visit set
    rw [wallPts, Set.mem_ofPred_eq] at hp
    obtain ⟨hboxp, hcutp, -⟩ := hp
    have hslab : p ∈ slabVisit K s c σ u v h := ⟨hboxp, hcutp⟩
    obtain ⟨z, hz, hz0⟩ := hcross p hslab
    refine ⟨z, ?_, ?_⟩
    · rw [cutCross, Set.mem_ofPred_eq]
      exact ⟨(connectedComponentIn_subset _ _ hz).1, hz0⟩
    · have hcomp := connectedComponentIn_eq hz
      show p ∈ closure (visit (slabVisit K s c σ u v h) z)
      unfold visit
      rw [← hcomp]
      exact subset_closure (mem_connectedComponentIn hslab)

end

end Work.Drive.Mono
