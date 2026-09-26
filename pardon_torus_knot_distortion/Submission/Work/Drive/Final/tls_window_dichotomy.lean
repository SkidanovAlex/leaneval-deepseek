import Mathlib
import Submission.Work.Drive.Final.tls_window_aux
import Submission.Work.Drive.Final.tls_seam_caseAlpha
import Submission.Work.Drive.Final.tls_window_beta_contra

/-!
# The window dichotomy for one level of the tilted sweep

`Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam` is Pardon's open box with the closed
tilted slab `{|⟪v,·⟫ - (⟪v,c⟫+u)| ≤ h}` cut away on the side `{ℓ < lam}`.  Its frontier is the
union of the outer piece (part of the box sphere) and the trough (part of the boundary of the
chunk `closure (PBox) ∩ slab ∩ {ℓ ≤ lam}`), glued along the seam

`tlsSeam = BoxSphere ∩ chunk ∩ (slabBdry ∪ {ℓ = lam})`.

This module proves the *dichotomy* which separates the two regimes of the one-sphere window: for
every configuration in which the box pokes out of the slab on both sides strictly above the wall,
either

* the frontier of the removed set **is** the whole box sphere (the degenerate case: the chunk
  misses the open box), or
* the chunk has nonempty interior and the seam is a nonempty circle — the genuine window in which
  the frontier is the union of two discs glued along the seam
  (`Work.Drive.Final.tls_twoDiscs_crux`).

The two ingredients are

* `Work.Drive.Final.interior_tlsChunk_nonempty_of_point`: a point of the open box in the closed
  slab below the wall can be moved into the interior of the chunk;
* the dichotomy on the wall plane: either the wall meets the open box inside the slab
  (`Work.Drive.Final.tls_seam_caseAlpha`: the seam is nonempty) or the wall meets the open box
  only outside the slab, which is impossible in the presence of a point of the chunk
  (`Work.Drive.Final.tls_window_beta_contra`).
-/

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set

namespace Work.Drive.Final

noncomputable section

theorem tls_window_dichotomy (s : ℝ) (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3)) (u h lam : ℝ) (v : LeanEval.KnotTheory.PardonDistortion.R3)
    (ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ) (hs : 0 < s) (hh : 0 < h) (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0)
    (hvertex : ∀ ε : Fin 3 → Bool,
      lam ≠ ℓ (WithLp.toLp 2 (fun j : Fin 3 => c j +
        (if ε (σ.symm j) then 1 else -1) * Submission.boxSide (σ.symm j) * s)))
    (hwallP : ∃ y ∈ Submission.PBox s c σ,
      inner ℝ v c + u + h < inner ℝ v y ∧ lam < ℓ y)
    (hwallM : ∃ y ∈ Submission.PBox s c σ,
      inner ℝ v y < inner ℝ v c + u - h ∧ lam < ℓ y)
    (hwinP : ∃ y ∈ Submission.PBox s c σ, inner ℝ v c + u + h < inner ℝ v y)
    (hwinM : ∃ y ∈ Submission.PBox s c σ, inner ℝ v y < inner ℝ v c + u - h) :
    frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam) =
        Work.Topology.SphereSlicing.BoxSphere s c σ ∨
      ((interior (Work.Drive.Final.tlsChunk s c σ u h lam v ℓ)).Nonempty ∧
        (Work.Drive.Final.tlsSeam s c σ u h lam v ℓ).Nonempty) := by
  have hv : v ≠ 0 := tls_v_ne_zero (s := s) (c := c) (σ := σ) (u := u) (h := h) hh hwinP hwinM
  -- the wall plane cuts the open box
  by_cases hcut : ∃ y ∈ Submission.PBox s c σ, ℓ y = lam ∧
      |inner ℝ v y - (inner ℝ v c + u)| ≤ h
  · have hseam : (tlsSeam s c σ u h lam v ℓ).Nonempty :=
      tls_seam_caseAlpha s c σ u h lam v ℓ hs hℓne hcut
    obtain ⟨y, hy, hyl, hys⟩ := hcut
    exact Or.inr ⟨interior_tlsChunk_nonempty_of_point hs hh hv hℓv hℓne hy hys (le_of_eq hyl), hseam⟩
  · -- the wall meets the open box only strictly outside the slab
    have hβ : ∀ y ∈ Submission.PBox s c σ, ℓ y = lam →
        h < |inner ℝ v y - (inner ℝ v c + u)| := by
      intro y hy hyl
      by_contra hcon
      exact hcut ⟨y, hy, hyl, not_lt.mp hcon⟩
    by_cases hbox : (Submission.PBox s c σ ∩ tlsChunk s c σ u h lam v ℓ).Nonempty
    · have hcontra : False := tls_window_beta_contra s c σ u h lam v ℓ hbox hwallP hwallM hβ
      obtain ⟨z, hzbox, hzchunk⟩ := hbox
      have hpz : |inner ℝ v z - (inner ℝ v c + u)| ≤ h := hzchunk.1.2
      have hℓz : ℓ z ≤ lam := hzchunk.2
      exact Or.inr ⟨interior_tlsChunk_nonempty_of_point hs hh hv hℓv hℓne hzbox hpz hℓz, hcontra.elim⟩
    · -- the chunk misses the open box: nothing is removed
      refine Or.inl ?_
      have hR : Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam = Submission.PBox s c σ := by
        simp only [Work.Drive.Mono.tiltedLevelRemoved]
        rw [sdiff_eq_left, Set.disjoint_left]
        rintro y hy ⟨hyslab, hywall⟩
        have hywall' : ℓ y < lam := by simpa using hywall
        exact hbox ⟨y, hy, ⟨subset_closure hy, hyslab⟩, le_of_lt hywall'⟩
      rw [hR]
      exact Work.Topology.SphereSlicing.frontier_PBox hs c σ

end

end Work.Drive.Final
