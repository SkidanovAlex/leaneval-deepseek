/-
# `Submission.Work.FIArea6Hecke.R.CompletionStrictDefs`

The explicit entire completion of the Hecke `L`-function of `ℚ(i)` at weight `m = 0`, for a
*strict* (not necessarily primitive) character `χ` mod `4d`, obtained by splitting the Mellin
integral of `thetaHol χ 0` at the point `c₀ = 1/(4d)²` (well below the involution fixed point
`1/(4d)`), exactly as in `Work.FIArea6Hecke.R.hci_completion_of_nat_strict` (the case `k = 0`).

`completionL0 d psi s = (4d)^s · (∫₀^{c₀} u^{s-1} θ(u) du + ∫_{c₀}^∞ u^{s-1} θ(u) du)`
where `θ = thetaHol psi 0`.  The two cut Mellin transforms are entire
(`hci_lowCut_facts`, `hci_highCut_facts`) and on `re s > 1` their sum is `mellin θ s`, whence
`completionL0 d psi s = heckeArch d 0 s · heckeLSeries psi 0 s`.
-/
import Mathlib
import Submission.Work.FIArea6Hecke.R.heckeCompletionImprimitive

set_option autoImplicit false

namespace Work.FIArea6Hecke.R

open MeasureTheory Set
open scoped Topology

noncomputable section

/-- The split point `c₀ = 1/(4d)²` of the Mellin integral of `thetaHol`.  It lies strictly below
the involution fixed point `1/(4d) = thetaC d`. -/
def completionCut (d : ℕ) : ℝ := 1 / (4 * (d : ℝ)) ^ 2

/-- The low cut `u ↦ (if u < c₀ then thetaHol psi 0 u else 0)` of the theta series. -/
def completionLowCut (d : ℕ) (psi : GaussianInt → ℂ) : ℝ → ℂ :=
  fun u => if u < completionCut d then Work.FIArea5.S16Hecke.thetaHol psi 0 u else 0

/-- The high cut `u ↦ (if c₀ ≤ u then thetaHol psi 0 u else 0)` of the theta series. -/
def completionHighCut (d : ℕ) (psi : GaussianInt → ℂ) : ℝ → ℂ :=
  fun u => if completionCut d ≤ u then Work.FIArea5.S16Hecke.thetaHol psi 0 u else 0

/-- The explicit completion `(4d)^s (mellin lowCut + mellin highCut)`. -/
def completionL0 (d : ℕ) (psi : GaussianInt → ℂ) (s : ℂ) : ℂ :=
  (((4 * d : ℕ)) : ℂ) ^ s *
    (mellin (completionLowCut d psi) s + mellin (completionHighCut d psi) s)

lemma completionCut_pos {d : ℕ} (hd : 1 ≤ d) : 0 < completionCut d := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  rw [completionCut]
  positivity

lemma completionCut_le_one {d : ℕ} (hd : 1 ≤ d) : completionCut d ≤ 1 := by
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  rw [completionCut, div_le_one (by positivity)]
  nlinarith

lemma completionCut_lt_thetaC {d : ℕ} (hd : 1 ≤ d) :
    completionCut d < Work.FIArea5.S16Hecke.thetaC d := by
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hpos : 0 < 4 * (d : ℝ) := by linarith
  have hgt : (1 : ℝ) < 4 * (d : ℝ) := by linarith
  have hlt : 4 * (d : ℝ) < (4 * (d : ℝ)) ^ 2 := by
    have h := mul_lt_mul_of_pos_left hgt hpos
    simpa [mul_one, sq] using h
  rw [completionCut, Work.FIArea5.S16Hecke.thetaC, one_div, one_div]
  exact (inv_lt_inv₀ (by positivity : (0:ℝ) < (4 * (d:ℝ))^2) hpos).mpr hlt

end

end Work.FIArea6Hecke.R
