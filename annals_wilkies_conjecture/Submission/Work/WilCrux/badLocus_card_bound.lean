/-
  `Work.WilCrux.badLocus_card_bound`

  A one-variable function whose graph is `Ω F D 2` for a sharply o-minimal structure `S`
  with sharp cell decomposition is `C¹` off a *uniformly bounded* number of points.

  The proof combines three ingredients:

  * `Work.WilG4c.jointBad_mem` — the non-`C¹` locus `{z : Fin 1 → ℝ | ¬ ContDiffAt ℝ 1 g z}`
    of `g = fun x => h (x 0)` is `Ω`-definable with a format `a` depending only on `S` and `F`,
    and a degree bounded by a fixed polynomial in `D` (this is the first-order ε-δ encoding of
    `C¹`, so no `SharpDeriv` hypothesis is needed);
  * `WilkiesDesign.CG.G1_generic_smooth_proved` — that locus has empty interior;
  * `Work.WilCrux.Omega_thin_card_bound` (`SOMin.comps` in dimension one) — an `Ω`-set in `ℝ¹`
    with empty interior is contained in a `Finset` of at most `p.eval D` points.

  Transporting along the linear homeomorphism `Fin 1 → ℝ ≃ ℝ`
  (`Work.WilG4a.CD.contDiffAt_fin1_comp`) turns the bounding `Finset` of `ℝ¹` into the
  exceptional `Finset ℝ` of the statement; the projection `z ↦ z 0` does not increase cardinality.
-/
import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.WilG4c.C1BadLocusMemPB2
import Submission.Work.WilG1.Main
import Submission.Work.WilCrux.Omega_thin_card_bound
import Submission.Work.WilG4a.CD.oneDim_Cj_locus_mem

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Classical
open scoped Topology

namespace Work.WilCrux

open WilkiesDesign

/-- **A one-variable function with `Ω`-definable graph is `C¹` off a uniformly bounded set.**

For fixed `S`, `hcd`, `F`, `D` there is a bound `Kb` such that for every `h : ℝ → ℝ` whose
graph, read as a subset of `ℝ² = Fin 2 → ℝ`, lies in `S.Ω F D 2`, the set of points at which
`h` fails to be `C¹` is contained in a `Finset ℝ` of at most `Kb` points.

The exceptional set is the non-`C¹` locus
`{z : Fin 1 → ℝ | ¬ ContDiffAt ℝ 1 (fun x => h (x 0)) z}`.  It is `Ω`-definable with a format
`a` depending only on `S`, `F` and degree `b.eval D` (`Work.WilG4c.jointBad_mem`), and it has
empty interior (`WilkiesDesign.CG.G1_generic_smooth_proved`).  A one-dimensional `Ω`-set with
empty interior is a finite union of preconnected pieces of empty interior, each a subsingleton
by `SOMin.comps`, hence it has at most `p.eval (b.eval D)` points
(`Work.WilCrux.Omega_thin_card_bound`).

The *uniformity* in `h` — the point of the statement — comes from `a`, `b` and `p` depending only
on `S`, `F` (and `D` in the degree of `b`), never on `h` itself. -/
theorem badLocus_card_bound (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (F D : ℕ) :
    ∃ Kb : ℕ, ∀ h : ℝ → ℝ,
      WilkiesDesign.graphOf (fun x : Fin 1 → ℝ => h (x 0)) ∈ S.Ω F D 2 →
        ∃ Bb : Finset ℝ, Bb.card ≤ Kb ∧ ∀ x : ℝ, x ∉ Bb → ContDiffAt ℝ 1 h x := by
  classical
  -- the non-`C¹` locus of `h` read on `ℝ¹ = Fin 1 → ℝ` is `Ω`-definable, uniformly in `h`
  obtain ⟨a, b, hmemb⟩ := Work.WilG4c.jointBad_mem S 1 F
  -- a thin `Ω`-set of `ℝ¹` is contained in a `Finset` with at most `p.eval D` points
  obtain ⟨p, hp⟩ := Omega_thin_card_bound S a
  refine ⟨p.eval (b.eval D), ?_⟩
  intro h hgh
  let g : (Fin 1 → ℝ) → ℝ := fun z => h (z 0)
  let A : Set (Fin 1 → ℝ) := {z | ¬ ContDiffAt ℝ 1 g z}
  have hA : A ∈ S.Ω a (b.eval D) 1 := hmemb D g hgh
  have hint : interior A = ∅ := WilkiesDesign.CG.G1_generic_smooth_proved S hcd g hgh 1
  obtain ⟨B, hBcard, hBmem⟩ := hp (b.eval D) A hA hint
  -- project the bounding `Finset` of `ℝ¹` down to `ℝ`; this does not increase the cardinality
  refine ⟨B.image (fun z : Fin 1 → ℝ => z 0), ?_, ?_⟩
  · calc (B.image (fun z : Fin 1 → ℝ => z 0)).card ≤ B.card := Finset.card_image_le
      _ ≤ p.eval (b.eval D) := hBcard
  · intro x hx
    -- `x` is not a bad point: otherwise `(fun _ => x) ∈ B`, hence `x ∈ B.image (· 0)`
    have hz : ContDiffAt ℝ 1 g (fun _ : Fin 1 => x) := by
      by_contra hcon
      have hmemB : (fun _ : Fin 1 => x) ∈ B := by
        by_contra hzB
        exact hBmem (fun _ : Fin 1 => x) hzB hcon
      exact hx (Finset.mem_image.mpr ⟨fun _ : Fin 1 => x, hmemB, rfl⟩)
    exact (Work.WilG4a.CD.contDiffAt_fin1_comp h 1 (fun _ : Fin 1 => x)).mp hz

end Work.WilCrux
