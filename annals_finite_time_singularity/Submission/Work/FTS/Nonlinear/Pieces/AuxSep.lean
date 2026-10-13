/-
# N4 — `T1`-free copies of three elementary `LocData` lemmas

`Submission/Work/FTS/LocData/hLoc_hk.lean` ends by defining `Work.FTS.LocData.T1`, and so does
`Submission/Work/FTS/LocData/FstarAux.lean`; the two modules therefore **cannot be imported
together** (a known wart of the shared library, recorded in
`Submission/Work/FTS/LocDataExt/FMJet5.lean`).  `Pieces/rowsAux.lean` needs three *elementary*
lemmas of the `hLoc_hk` file — `sep_sq1`, `sep_sq2`, `Gam_sq_rpow_le_angMaj_gam` — and nothing
else from it, while the row files of `Pieces/RNP` need the `FstarAux` chain.  This module
re-proves the three lemmas (with the same statements, under local names), so that `rowsAux` can
drop its `hLoc_hk` import and the clash disappears.

The proofs are verbatim adaptations of the originals.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.LocData.angMaj_mem
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology

namespace Work.FTS.Nonlinear.Pieces

/-- `(b / s^e)² = b²·s^{-2e}`, valid for `s ≥ 0` (both sides vanish at `s = 0`). -/
theorem div_rpow_sq_loc (b s e : ℝ) (hs : 0 ≤ s) : (b / s ^ e) ^ 2 = b ^ 2 * s ^ (-(2 * e)) := by
  rw [div_pow, div_eq_mul_inv]
  have h : (s ^ e) ^ 2 = s ^ (2 * e) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs]
    ring_nf
  rw [h, ← Real.rpow_neg hs]

/-- The square of a `D_z`-summand factorises into its radial and angular blocks. -/
theorem sep_sq1_loc (B G w s e : ℝ) (hs : 0 ≤ s) :
    (B * G * (w / s ^ (e / 2))) ^ 2 = (B * w) ^ 2 * (G ^ 2 * s ^ (-e)) := by
  rw [show B * G * (w / s ^ (e / 2)) = B * G * w / s ^ (e / 2) by ring, div_rpow_sq_loc _ _ _ hs]
  rw [show -(2 * (e / 2)) = -e by ring]
  ring

/-- The square of a mixed-summand factorises into its radial and angular blocks. -/
theorem sep_sq2_loc (B G w s g : ℝ) (hs : 0 ≤ s) :
    (B * G * (w * s ^ (-(g / 2)))) ^ 2 = (B * w) ^ 2 * (G ^ 2 * s ^ (-g)) := by
  rw [show B * G * (w * s ^ (-(g / 2))) = (B * G * w) * s ^ (-(g / 2)) by ring, mul_pow]
  rw [show (s ^ (-(g / 2))) ^ 2 = s ^ (-g) from by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs]; congr 1; ring]
  ring

/-- `sin(2θ) ≥ 0` on `Iθ`. -/
theorem sin_two_nonneg_loc {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) := by
  apply Real.sin_nonneg_of_mem_Icc
  exact ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- The `γ`-summand of `angMaj`. -/
theorem Gam_sq_rpow_le_angMaj_gam_loc (α : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ Work.FTS.LocData.angMaj α θ := by
  have hs0 := sin_two_nonneg_loc hθ
  rw [Work.FTS.LocData.angMaj_apply]
  have h1 : 0 ≤ Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _)
  linarith

end Work.FTS.Nonlinear.Pieces
