import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBoxFock.tauGapDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.tauSplitBricks` — the pointwise algebra of the sharp/excess split

This module collects the *elementary, pointwise* identities that turn the four weights of
`tauGapDefs` (`tauPsi`, `tauRho`, `tauSharp`, `tauTheta`) into each other.  They are the input of
the two aggregate identities

* `Work.BoseBoxFock.tauPsi_tsum_decomp` — the convexity defect decomposes as
  `Ψ_c = δ_c + Θ_c − c·r + (5/4+c₀)c²` (`δ_c = F_c − τ_c`);
* `Work.BoseBoxFock.tauSharp_tsum_cont` — the sharp weight satisfies
  `F_c = r² + c² − 2c·r − Θ_c` (`2c·r + Θ_c = r² + c² − F_c`),

and they are also what makes the corresponding bounds (`F_c ≤ r²`, `0 ≤ δ_c ≤ r²`) immediate.

The two moment identities `L(1) = C(1)`, `L(‖·‖²) = C(‖·‖²)` (proved in
`Work.BoseBoxFock.deficit_inputs`) then upgrade these pointwise statements to the *state-level*
identities `hψ` and `hF` of `FINDING_tauPhi_row_lattice.md` §8.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseBoxFock

/-- **The two cap pieces add up to the full square**: `F_c(r) + Θ_c(r) = (r−c)²`.
Indeed one of `max 0 (r−c)`, `max 0 (c−r)` is `0` and the other is `|r−c|`. -/
lemma tauSharp_add_tauTheta (c r : ℝ) : tauSharp c r + tauTheta c r = (r - c) ^ 2 := by
  rw [tauSharp, tauTheta]
  rcases le_or_gt r c with h | h
  · rw [max_eq_left (by linarith : r - c ≤ 0), max_eq_right (by linarith : (0 : ℝ) ≤ c - r)]
    ring
  · rw [max_eq_right (by linarith : (0 : ℝ) ≤ r - c), max_eq_left (by linarith : c - r ≤ 0)]
    ring

/-- **The polynomial splitting of the sharp weight**: `F_c = r² + c² − 2c·r − Θ_c`, i.e.
`2c·r + Θ_c = r² + c² − F_c` (`tauShiftW_eq_sq_add_sub_sharp` of `tauPhi_row_lattice`). -/
lemma tauSharp_eq_sq_add_sub (c r : ℝ) : tauSharp c r = r ^ 2 + c ^ 2 - 2 * c * r - tauTheta c r := by
  have h := tauSharp_add_tauTheta c r
  have : tauSharp c r = (r - c) ^ 2 - tauTheta c r := by linarith
  rw [this]; ring

/-- **The quadratic tail in terms of the two cap pieces**:
`ρ_c(r) = F_c(r) + Θ_c(r) − c·r + (5/4+c₀)c²`. -/
lemma tauRho_eq_sharp_add_theta (c r : ℝ) :
    tauRho c r = tauSharp c r + tauTheta c r - c * r + (5 / 4 + tauC0phi) * c ^ 2 := by
  rw [tauRho, tauSharp_add_tauTheta]
  ring

/-- **The pointwise split of the convexity defect**:
`Ψ_c = (F_c − τ_c) + Θ_c − c·r + (5/4+c₀)c²`, where `τ_c(r) = c²·tauPhi (r/c)`. -/
lemma tauPsi_eq_sharp_split (c r : ℝ) :
    tauPsi c r = (tauSharp c r - c ^ 2 * tauPhi (r / c)) + tauTheta c r - c * r
      + (5 / 4 + tauC0phi) * c ^ 2 := by
  rw [tauPsi, tauRho_eq_sharp_add_theta]
  ring

/-- The sharp weight is nonnegative. -/
lemma tauSharp_nonneg (c r : ℝ) : 0 ≤ tauSharp c r := by
  rw [tauSharp]; positivity

/-- **The sharp weight is dominated by the square**: for `c > 0` and `r ≥ 0`,
`F_c(r) = (r−c)₊² ≤ r²` (because `0 ≤ max 0 (r−c) ≤ r`). -/
lemma tauSharp_le_sq {c r : ℝ} (hc : 0 < c) (hr : 0 ≤ r) : tauSharp c r ≤ r ^ 2 := by
  rw [tauSharp]
  have h1 : max 0 (r - c) ≤ r := max_le hr (by linarith)
  have h2 : 0 ≤ max 0 (r - c) := le_max_left _ _
  nlinarith

/-- The smoothing gap `δ_c = F_c − τ_c` is nonnegative. -/
lemma tauSharp_sub_phi_nonneg {c r : ℝ} (hc : 0 < c) :
    0 ≤ tauSharp c r - c ^ 2 * tauPhi (r / c) :=
  sub_nonneg.mpr (tauPhiWeight_le_tauSharp hc)

/-- The smoothing gap is dominated by the square: `δ_c(r) ≤ r²` for `r ≥ 0`. -/
lemma tauSharp_sub_phi_le_sq {c r : ℝ} (hc : 0 < c) (hr : 0 ≤ r) :
    tauSharp c r - c ^ 2 * tauPhi (r / c) ≤ r ^ 2 := by
  have := tauSharp_le_sq hc hr
  have h2 : 0 ≤ c ^ 2 * tauPhi (r / c) := mul_nonneg (sq_nonneg c) (tauPhi_nonneg _)
  linarith

end Work.BoseBoxFock
