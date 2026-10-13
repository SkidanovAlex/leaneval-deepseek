/-
  `nondiff_finite_side`: the one-dimensional finiteness of the non-`C¹` locus of an
  `Ω`-definable function, proved from the *multi-dimensional* generic-smoothness theorem
  `Work.WilG1.Cell.smooth_k_cover` (`interior {¬C^k} = ∅` in every arity), together with the
  one-dimensional fact `Work.WilG1.Calc.finite_of_interior_empty` that an `Ω`-subset of `ℝ¹`
  of empty interior is finite.

  This is the same statement as `Work.WilG4b.nondiff_finite` (and `Work.WilG4bF.nondiff_finite`),
  but it lives on the `Work.WilG1.OneDim.bad_covered` side of the workspace's
  `Work.WilG1.OneDim.mem_oscL_iff` name clash, and it uses none of the modules there.
-/
import Mathlib
import Submission.Work.WilG1.Cell.smooth_k_cover
import Submission.Work.WilG1.Calc.finite_of_interior_empty
import Submission.Work.WilG1.Thin.oneDim_fin

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-- `G : ℝ → ℝ` read as a function of `Fin 1 → ℝ`. -/
abbrev fin1Hat (G : ℝ → ℝ) : (Fin 1 → ℝ) → ℝ := fun x => G (x 0)

/-- Transport of the `C¹` condition between `ℝ` and `Fin 1 → ℝ`. -/
theorem contDiffAt_fin1Hat_iff {G : ℝ → ℝ} {t : ℝ} :
    ContDiffAt ℝ 1 G t ↔ ContDiffAt ℝ 1 (fin1Hat G) (fun _ : Fin 1 => t) := by
  constructor
  · intro h
    have hproj : ContDiffAt ℝ 1 (fun x : Fin 1 → ℝ => x 0) (fun _ : Fin 1 => t) :=
      ((ContinuousLinearMap.proj (0 : Fin 1) : (Fin 1 → ℝ) →L[ℝ] ℝ).contDiff.contDiffAt)
    have h' : ContDiffAt ℝ 1 G ((fun x : Fin 1 → ℝ => x 0) (fun _ : Fin 1 => t)) := h
    have hcomp := ContDiffAt.comp (fun _ : Fin 1 => t) h' hproj
    simpa [fin1Hat, Function.comp_def] using hcomp
  · intro h
    have hphi : ContDiffAt ℝ 1 (fun s : ℝ => (fun _ : Fin 1 => s)) t :=
      contDiffAt_pi' (fun _ => contDiffAt_id)
    have hcomp := ContDiffAt.comp t h hphi
    simpa [fin1Hat, Function.comp_def] using hcomp

/-- One-dimensional finiteness of the non-`C¹` locus of a definable function. -/
theorem nondiff_finite_side (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv)
    {F D : ℕ} (G : ℝ → ℝ)
    (hG : WilkiesDesign.graphOf (fun x : Fin 1 → ℝ => G (x 0)) ∈ S.Ω F D 2) :
    ({t : ℝ | ¬ ContDiffAt ℝ 1 G t}).Finite := by
  obtain ⟨m, a, b, A, hA, hint, hsub⟩ :=
    Work.WilG1.Cell.smooth_k_cover (S := S) hcd (k := 1)
      (fun x : Fin 1 → ℝ => G (x 0)) hG
  have hfinA : ∀ i : Fin m, (A i).Finite := fun i =>
    Work.WilG1.Calc.finite_of_interior_empty (hA i) (hint i)
  have hU : (⋃ i : Fin m, A i).Finite := by
    simpa using ((Finset.univ : Finset (Fin m)).finite_toSet).biUnion (fun i _ => hfinA i)
  have hfin1 : ({x : Fin 1 → ℝ | ¬ ContDiffAt ℝ 1 (fun x : Fin 1 → ℝ => G (x 0)) x}).Finite :=
    Set.Finite.subset hU hsub
  have hiff : ∀ z : Fin 1 → ℝ,
      (¬ ContDiffAt ℝ 1 G (z 0)) ↔
        (¬ ContDiffAt ℝ 1 (fun x : Fin 1 → ℝ => G (x 0)) z) := by
    intro z
    have hpt : (fun _ : Fin 1 => z 0) = z := by
      funext i
      exact (congrArg z (Subsingleton.elim i 0)).symm
    have h := not_congr (contDiffAt_fin1Hat_iff (G := G) (t := z 0))
    have h' : (¬ ContDiffAt ℝ 1 G (z 0)) ↔ (¬ ContDiffAt ℝ 1 (fin1Hat G) z) := by
      rwa [hpt] at h
    simpa [fin1Hat] using h'
  have hset : Work.WilG1.liftR {t : ℝ | ¬ ContDiffAt ℝ 1 G t}
      = {z : Fin 1 → ℝ | ¬ ContDiffAt ℝ 1 (fun x : Fin 1 → ℝ => G (x 0)) z} := by
    ext z
    rw [Work.WilG1.liftR, Set.mem_ofPred_eq]
    exact hiff z
  rw [← hset] at hfin1
  exact (Work.WilG1.Thin.finite_liftR_iff {t : ℝ | ¬ ContDiffAt ℝ 1 G t}).mp hfin1

end Work.WilkG4c
