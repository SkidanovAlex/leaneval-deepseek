import Mathlib
import Submission.Fold
import Submission.E2bCore

/-!
# E2b telescope (s = 1): cell-zero algebra for the deformation identity

The E2b deformation (Plan.md DESIGN NOTE 25/27) parts the region between
the big circle `C(0, e^B)` and the ε-contour `Γ` hugging the hedgehog into
*above-the-tip window cells* `[u_j, B] × (x_j−δ, x_j+δ)` (boundary integral
zero by `Submission.TipCell`) and *gap cells* `[A, B] × (x_j+δ, x_{j+1}−δ)`
(zero by `Submission.SpineGaps` + `Submission.Fold.gap_cell_zero`).  This
module proves the pure interval-integral bookkeeping converting those cell
zeros into the deformation identity.  The s = 1 case (`circle_eq_cap_sum_s1`,
PROVED here): for a single spike direction `x`, tip radius `e^u`, base
radius `e^A`, outer radius `e^B`,

    ∮_{C(0,e^B)} h  =  I • arcInt(pull h) u (x−δ) (x+δ)     (tip cap)
                    + I • arcInt(pull h) A (x+δ) (x−δ+2π)   (base gap arc)
                    + radInt(pull h) A u (x−δ)              (side down)
                    - radInt(pull h) A u (x+δ)              (side up)

whenever the window and gap cell boundary integrals vanish (hypotheses
`hwc`, `hgc`) and the interval-additivity gluing facts hold (hypotheses
`hbwin`, `hbgap`, `hradu`, `hrub`, `hradu'`, `hrub'`: all automatic for
continuous integrands, in particular for `pull h` with `h` holomorphic off
the hedgehog and the pieces star-free).  The algebra: expand both cell
identities (`cellExpr`), glue the two B-arcs and telescope the radial sides
via the wrap-periodicity `radInt_add_two_pi`, and rearrange by `ring`.

The general-s statement is the same identity summed over `j` with cyclic
indices (`x_s := x_0 + 2π`), to be assembled in later sessions.
-/
noncomputable section
open scoped Complex Real Interval
open Complex
open MeasureTheory
open Submission.Fold

namespace Submission.E2bT

/-- s=1 deformation identity (algebra). -/
theorem circle_eq_cap_sum_s1 (h : ℂ → ℂ) (A u B x δ : ℝ)
    (hbwin : IntervalIntegrable (fun y : ℝ => Submission.E2bCore.pull h (B + y * Complex.I)) volume (x - δ) (x + δ))
    (hbgap : IntervalIntegrable (fun y : ℝ => Submission.E2bCore.pull h (B + y * Complex.I)) volume (x + δ) (x - δ + 2 * Real.pi))
    (hradu : IntervalIntegrable (fun t : ℝ => Submission.E2bCore.pull h (t + (x - δ) * Complex.I)) volume A u)
    (hrub : IntervalIntegrable (fun t : ℝ => Submission.E2bCore.pull h (t + (x - δ) * Complex.I)) volume u B)
    (hradu' : IntervalIntegrable (fun t : ℝ => Submission.E2bCore.pull h (t + (x + δ) * Complex.I)) volume A u)
    (hrub' : IntervalIntegrable (fun t : ℝ => Submission.E2bCore.pull h (t + (x + δ) * Complex.I)) volume u B)
    (hwc : cellExpr (Submission.E2bCore.pull h) u B (x - δ) (x + δ) = 0)
    (hgc : cellExpr (Submission.E2bCore.pull h) A B (x + δ) (x - δ + 2 * Real.pi) = 0) :
    (∮ z in C((0 : ℂ), Real.exp B), h z) =
      Complex.I • arcInt (Submission.E2bCore.pull h) u (x - δ) (x + δ)
        + Complex.I • arcInt (Submission.E2bCore.pull h) A (x + δ) (x - δ + 2 * Real.pi)
        + radInt (Submission.E2bCore.pull h) A u (x - δ)
        - radInt (Submission.E2bCore.pull h) A u (x + δ) := by
  classical
  let F : ℂ → ℂ := Submission.E2bCore.pull h
  -- rad periodic identity at the wrap (via the E2bCore lemma; all radInt/arcInt
  -- definitions are definitionally equal between the namespaces)
  have hperwrap : radInt F A B (x - δ + 2 * Real.pi) = radInt F A B (x - δ) := by
    simpa [F, radInt, Submission.E2bCore.radInt] using
      (Submission.E2bCore.radInt_add_two_pi h A B (x - δ))
  -- rad glue at angle x - δ : rad A u + rad u B = rad A B
  have hglue_rad_l : radInt F A u (x - δ) + radInt F u B (x - δ) = radInt F A B (x - δ) := by
    unfold radInt
    simpa [F] using (intervalIntegral.integral_add_adjacent_intervals hradu hrub)
  have hglue_rad_r : radInt F A u (x + δ) + radInt F u B (x + δ) = radInt F A B (x + δ) := by
    unfold radInt
    simpa [F] using (intervalIntegral.integral_add_adjacent_intervals hradu' hrub')
  -- arc glue at radius B
  have hglue_arcB : arcInt F B (x - δ) (x + δ) + arcInt F B (x + δ) (x - δ + 2 * Real.pi)
      = arcInt F B (x - δ) (x - δ + 2 * Real.pi) := by
    unfold arcInt
    simpa [F] using (intervalIntegral.integral_add_adjacent_intervals hbwin hbgap)
  have hB : Complex.I • arcInt F B (x - δ) (x + δ) + Complex.I • arcInt F B (x + δ) (x - δ + 2 * Real.pi)
        = Complex.I • arcInt F B (x - δ) (x - δ + 2 * Real.pi) := by
      rw [← smul_add]
      exact congrArg (fun t : ℂ => Complex.I • t) hglue_arcB
  -- the sum of the two cell expressions is zero
  have hsum : cellExpr F u B (x - δ) (x + δ) + cellExpr F A B (x + δ) (x - δ + 2 * Real.pi) = 0 := by
    subst F
    rw [hwc, hgc]
    ring
  have hmain : Complex.I • arcInt F B (x - δ) (x - δ + 2 * Real.pi)
      = Complex.I • arcInt F u (x - δ) (x + δ)
        + Complex.I • arcInt F A (x + δ) (x - δ + 2 * Real.pi)
        + radInt F A u (x - δ) - radInt F A u (x + δ) := by
    have hs0 := hsum
    unfold cellExpr at hs0
    simp only [smul_eq_mul] at hs0
    -- zero relations (in ring form):
    -- (z1) the two B arcs combine into the full-window B arc
    have hz1 : Complex.I * arcInt F B (x - δ) (x + δ) + Complex.I * arcInt F B (x + δ) (x - δ + 2 * Real.pi)
          - Complex.I * arcInt F B (x - δ) (x - δ + 2 * Real.pi) = 0 := by
      have hBsm : Complex.I • arcInt F B (x - δ) (x + δ) + Complex.I • arcInt F B (x + δ) (x - δ + 2 * Real.pi)
            = Complex.I • arcInt F B (x - δ) (x - δ + 2 * Real.pi) := by
        rw [← smul_add]
        exact congrArg (fun t : ℂ => Complex.I • t) hglue_arcB
      exact sub_eq_zero.mpr (by simpa [smul_eq_mul] using hBsm)
    -- (z2) the radial-side combination telescopes to the side segments
    have hz2 : (radInt F u B (x - δ) - radInt F u B (x + δ) + radInt F A B (x + δ)
          - radInt F A B (x - δ + 2 * Real.pi))
          - (- radInt F A u (x - δ) + radInt F A u (x + δ)) = 0 := by
      have hL : radInt F u B (x - δ) - radInt F A B (x - δ + 2 * Real.pi) = - radInt F A u (x - δ) := by
        rw [hperwrap]
        rw [← hglue_rad_l]
        ring
      have hR : radInt F A B (x + δ) - radInt F u B (x + δ) = radInt F A u (x + δ) := by
        rw [← hglue_rad_r]
        ring
      calc
        (radInt F u B (x - δ) - radInt F u B (x + δ) + radInt F A B (x + δ)
            - radInt F A B (x - δ + 2 * Real.pi))
            - (- radInt F A u (x - δ) + radInt F A u (x + δ))
            = (radInt F u B (x - δ) - radInt F A B (x - δ + 2 * Real.pi))
                + (radInt F A B (x + δ) - radInt F u B (x + δ))
                + radInt F A u (x - δ) - radInt F A u (x + δ) := by ring
        _ = (- radInt F A u (x - δ)) + radInt F A u (x + δ)
              + radInt F A u (x - δ) - radInt F A u (x + δ) := by rw [hL, hR]
        _ = 0 := by ring
    have hE : Complex.I * arcInt F B (x - δ) (x - δ + 2 * Real.pi)
          - (Complex.I * arcInt F u (x - δ) (x + δ)
              + Complex.I * arcInt F A (x + δ) (x - δ + 2 * Real.pi)
              + radInt F A u (x - δ) - radInt F A u (x + δ)) = 0 := by
      linear_combination hs0 - hz1 - hz2
    -- back to the smul form of the statement
    rw [← sub_eq_zero]
    simp only [smul_eq_mul]
    ring_nf at hE ⊢
    exact hE
  calc
    (∮ z in C((0 : ℂ), Real.exp B), h z)
        = Complex.I • arcInt F B (x - δ) (x - δ + 2 * Real.pi) := by
          dsimp [F]
          simpa [arcInt, Submission.E2bCore.arcInt] using
            (Submission.E2bCore.circle_eq_arc_window h B (x - δ))
    _ = Complex.I • arcInt F u (x - δ) (x + δ)
          + Complex.I • arcInt F A (x + δ) (x - δ + 2 * Real.pi)
          + radInt F A u (x - δ) - radInt F A u (x + δ) := hmain


/-- **Split-glue zero.**  If the two sub-cells over `(c,m)` and `(m,d)` of
an angular range split at `m` both have zero boundary integrals, then the
cell over `(c,d)` does too (the shared radial side at angle `m` cancels;
`Submission.Fold.cellExpr_add_adjacent`).  This is the algebraic glue for
splitting a seam-crossing window at `±π`. -/
lemma cellExpr_split_zero (h : ℂ → ℂ) (u B c m d : ℝ)
    (hz_l : cellExpr (Submission.E2bCore.pull h) u B c m = 0)
    (hz_r : cellExpr (Submission.E2bCore.pull h) u B m d = 0)
    (hbmc : IntervalIntegrable (fun y : ℝ =>
        Submission.E2bCore.pull h (B + y * Complex.I)) MeasureTheory.volume c m)
    (hbmd : IntervalIntegrable (fun y : ℝ =>
        Submission.E2bCore.pull h (B + y * Complex.I)) MeasureTheory.volume m d)
    (hamc : IntervalIntegrable (fun y : ℝ =>
        Submission.E2bCore.pull h (u + y * Complex.I)) MeasureTheory.volume c m)
    (hamd : IntervalIntegrable (fun y : ℝ =>
        Submission.E2bCore.pull h (u + y * Complex.I)) MeasureTheory.volume m d) :
    cellExpr (Submission.E2bCore.pull h) u B c d = 0 := by
  rw [← cellExpr_add_adjacent (Submission.E2bCore.pull h) u B c m d hbmc hbmd hamc hamd]
  rw [hz_l, hz_r]
  ring


/-- Cell expressions of the exp-pullback are invariant under shifting both
angular bounds by `2π` (each side is, by periodicity of the pullback). -/
lemma cellExpr_add_two_pi (h : ℂ → ℂ) (a b c d : ℝ) :
    cellExpr (Submission.E2bCore.pull h) a b (c + 2 * Real.pi) (d + 2 * Real.pi) =
      cellExpr (Submission.E2bCore.pull h) a b c d := by
  unfold cellExpr
  have hR : ∀ (a b c : ℝ),
      radInt (Submission.E2bCore.pull h) a b (c + 2 * Real.pi) =
        radInt (Submission.E2bCore.pull h) a b c := by
    intro a b c
    simpa [radInt, Submission.E2bCore.radInt] using
      (Submission.E2bCore.radInt_add_two_pi h a b c)
  have hA : ∀ (u c d : ℝ),
      arcInt (Submission.E2bCore.pull h) u (c + 2 * Real.pi) (d + 2 * Real.pi) =
        arcInt (Submission.E2bCore.pull h) u c d := by
    intro u c d
    simpa [arcInt, Submission.E2bCore.arcInt] using
      (Submission.E2bCore.arcInt_add_two_pi h u c d)
  rw [hR a b c, hR a b d, hA b c d, hA a c d]

/-- Cell expressions are invariant under shifting both bounds by `−2π`
(useful to move a cell back into `(−π, π]`). -/
lemma cellExpr_sub_two_pi (h : ℂ → ℂ) (a b c d : ℝ) :
    cellExpr (Submission.E2bCore.pull h) a b (c - 2 * Real.pi) (d - 2 * Real.pi) =
      cellExpr (Submission.E2bCore.pull h) a b c d := by
  have hs := cellExpr_add_two_pi h a b (c - 2 * Real.pi) (d - 2 * Real.pi)
  have hc : (c - 2 * Real.pi) + 2 * Real.pi = c := by ring
  have hd : (d - 2 * Real.pi) + 2 * Real.pi = d := by ring
  simpa [hc, hd] using hs.symm

end Submission.E2bT
