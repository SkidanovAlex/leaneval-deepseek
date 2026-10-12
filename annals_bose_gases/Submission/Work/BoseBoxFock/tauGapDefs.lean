import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.tauC0Facts
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.tauGapDefs` — the exact split of the smoothed kinetic weight

This module records, for the **explicit** profile `tauPhi` of `TauProf.lean`, the split of the
weight of the target `Work.BoseBoxFock.tauPhi_row_lattice` that turns that row into a statement
about the first-moment deficit and the low-frequency mass.

With `c > 0`, `c₀ = ∫t² tauKer t` (so `0 ≤ c₀ ≤ 1/16`) and the weight

    τ_c(r) = c²·tauPhi (r/c)  =  ∫ t, tauH (r - c(3/2+t)) tauKer t ,

we define

* `tauRho c r = (r - 3c/2)² + c₀c²` — the *quadratic tail* (`τ_c ≤ tauRho` pointwise),
* `tauPsi c r = tauRho c r - τ_c(r)` — the convexity defect (`≥ 0`),
* `tauTheta c r = (c - r)₊²`, `tauSharp c r = (r - c)₊²` — the two cap/parabola pieces.

The content of this file (all proved):

* `tauPsi_nonneg` : `0 ≤ tauPsi c r` (the explicit profile lies below its quadratic tail);
* `tauPhi_eq_zero_of_le_five_quarters` : `τ_c(r) = 0` for `r ≤ 5c/4`
  (because `supp tauKer ⊆ [-1/4,1/4]`), so `tauPsi c r = tauRho c r` there;
* `tauTheta_le_tauPsi` : **`(c-r)₊² ≤ tauPsi c r`** — the low-frequency cap is dominated by the
  convexity defect; this is what lets the low-frequency part of the lattice sum `L(Ψ_c)` pay the
  continuum cap term `C(Θ_c)` in the row;
* `tauSharp_sub_tauPhi_ge` : `(r-c)₊² - τ_c(r) ≥ max 0 (c·r - (5/4+c₀)c²)` — the *quantitative*
  pointwise gap: the difference of the two weights of the row grows at least linearly in `r`
  above the threshold `(5/4+c₀)c`, while it is `0` below `c` and `≥ 0` everywhere.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

/-- The second moment of the smoothing kernel: `c₀ = ∫ t² tauKer t`, with `0 ≤ c₀ ≤ 1/16`. -/
noncomputable def tauC0phi : ℝ := ∫ t, t ^ 2 * tauKer t

lemma tauC0phi_def : tauC0phi = ∫ t, t ^ 2 * tauKer t := rfl

lemma tauC0phi_nonneg : 0 ≤ tauC0phi := tauKer_moment2_nonneg

lemma tauC0phi_le : tauC0phi ≤ 1 / 16 := tauKer_moment2_le

/-- The quadratic tail `ρ_c(r) = (r - 3c/2)² + c₀c²`. -/
noncomputable def tauRho (c r : ℝ) : ℝ := (r - 3 * c / 2) ^ 2 + tauC0phi * c ^ 2

/-- The convexity defect `Ψ_c = ρ_c - τ_c`. -/
noncomputable def tauPsi (c r : ℝ) : ℝ := tauRho c r - c ^ 2 * tauPhi (r / c)

/-- The cap `Θ_c(r) = (c - r)₊²`. -/
noncomputable def tauTheta (c r : ℝ) : ℝ := (max 0 (c - r)) ^ 2

/-- The sharp parabola `F_c(r) = (r - c)₊²`. -/
noncomputable def tauSharp (c r : ℝ) : ℝ := (max 0 (r - c)) ^ 2

lemma tauRho_eq (c r : ℝ) :
    tauRho c r = (r - 3 * c / 2) ^ 2 + tauC0phi * c ^ 2 := rfl

lemma tauPsi_eq (c r : ℝ) :
    tauPsi c r = tauRho c r - c ^ 2 * tauPhi (r / c) := rfl

/-- `τ_c(r) = c²·tauPhi (r/c)` is the (smoothed) weight of the left-hand side of the row. -/
lemma tauRho_sub_tauPsi (c r : ℝ) :
    c ^ 2 * tauPhi (r / c) = tauRho c r - tauPsi c r := by
  rw [tauPsi]; ring

/-- **The explicit profile lies below its quadratic tail**: `τ_c ≤ ρ_c`, i.e. `Ψ_c ≥ 0`. -/
lemma tauPsi_nonneg {c r : ℝ} (hc : 0 < c) : 0 ≤ tauPsi c r := by
  have h := tauDelta_phi_nonneg (c := c) (r := r) hc
  have hsq : r ^ 2 - 3 * c * r + (9 / 4 + ∫ t, t ^ 2 * tauKer t) * c ^ 2
      = (r - 3 * c / 2) ^ 2 + (∫ t, t ^ 2 * tauKer t) * c ^ 2 := by ring
  rw [hsq] at h
  simp only [tauPsi, tauRho, tauC0phi_def]
  linarith [h]

/-- **`τ_c` vanishes below `5c/4`**: for `c > 0` and `r ≤ 5c/4`, `c²·tauPhi (r/c) = 0`.
The smoother `tauKer` is supported in `[-1/4,1/4]`, so a nonzero contribution needs
`r - c(3/2+t) > 0` with `|t| < 1/4`, i.e. `r > 5c/4`. -/
lemma tauPhi_eq_zero_of_le_five_quarters {c r : ℝ} (hc : 0 < c) (hr : r ≤ 5 * c / 4) :
    c ^ 2 * tauPhi (r / c) = 0 := by
  have hratio : r / c ≤ 5 / 4 := by
    rw [div_le_iff₀ hc]; linarith
  have hzero : tauPhi (r / c) = 0 := by
    rw [tauPhi_eq_integral]
    have hpt : ∀ t, tauH (r / c - 3 / 2 - t) * tauKer t = 0 := by
      intro t
      rcases eq_or_ne (tauKer t) 0 with h0 | h0
      · rw [h0, mul_zero]
      · have hlt := abs_lt.1 (tauKer_abs_lt t h0)
        rw [tauH_eq_zero_of_nonpos (by linarith [hlt.1, hlt.2]), zero_mul]
    simp only [hpt]
    simp
  rw [hzero, mul_zero]

/-- Below `5c/4` the convexity defect is the whole quadratic tail: `Ψ_c = ρ_c`. -/
lemma tauPsi_eq_rho_of_le {c r : ℝ} (hc : 0 < c) (hr : r ≤ 5 * c / 4) :
    tauPsi c r = tauRho c r := by
  rw [tauPsi, tauPhi_eq_zero_of_le_five_quarters hc hr, sub_zero]

lemma tauRho_nonneg (c r : ℝ) : 0 ≤ tauRho c r := by
  rw [tauRho, tauC0phi_def]
  have := tauKer_moment2_nonneg
  nlinarith [sq_nonneg (r - 3 * c / 2), sq_nonneg c]

/-- **The cap is dominated by the convexity defect**: `(c-r)₊² ≤ Ψ_c(r)`.

For `r ≥ c` the cap vanishes; for `r ≤ c` the profile vanishes in a whole neighbourhood of the
origin (in particular `c²tauPhi (r/c) = 0` since `r ≤ c ≤ 5c/4`) and the difference is
`ρ_c(r) - (c-r)² = -c·r + (5/4+c₀)c² ≥ (1/4+c₀)c² ≥ 0`. -/
lemma tauTheta_le_tauPsi {c r : ℝ} (hc : 0 < c) : tauTheta c r ≤ tauPsi c r := by
  rcases le_or_gt r c with hr | hr
  · have h0 : tauTheta c r = (c - r) ^ 2 := by
      rw [tauTheta, max_eq_right (by linarith : (0:ℝ) ≤ c - r)]
    have h5 : r ≤ 5 * c / 4 := by linarith
    rw [tauPsi_eq_rho_of_le hc h5, tauRho, tauC0phi_def, h0]
    have hc0 := tauKer_moment2_nonneg
    have hc2 : (0:ℝ) < c ^ 2 := by positivity
    nlinarith [hr, hc0, sq_nonneg c, sq_nonneg (r - 3 * c / 2), sq_nonneg (c - r)]
  · have h0 : tauTheta c r = 0 := by
      rw [tauTheta, max_eq_left (by linarith : (c - r) ≤ 0)]; ring
    rw [h0]; exact tauPsi_nonneg hc

/-- `τ_c` is nonnegative (it is `c²` times the nonnegative profile). -/
lemma tauPhiWeight_nonneg (c r : ℝ) : 0 ≤ c ^ 2 * tauPhi (r / c) :=
  mul_nonneg (sq_nonneg c) (tauPhi_nonneg _)

/-- The pointwise domination of the row's two weights: `τ_c ≤ F_c` (`tauPhi_le`). -/
lemma tauPhiWeight_le_tauSharp {c r : ℝ} (hc : 0 < c) :
    c ^ 2 * tauPhi (r / c) ≤ tauSharp c r := by
  have h := tauPhi_le (r / c)
  have hm : c ^ 2 * tauPhi (r / c) ≤ c ^ 2 * (max 0 (r / c - 1)) ^ 2 :=
    mul_le_mul_of_nonneg_left h (sq_nonneg c)
  have hsq : c ^ 2 * (max 0 (r / c - 1)) ^ 2 = tauSharp c r := by
    rw [tauSharp]
    rcases le_or_gt r c with hrc | hrc
    · have h1 : r / c - 1 ≤ 0 := by
        have h2 : r / c ≤ 1 := by rw [div_le_one hc]; linarith
        linarith
      rw [max_eq_left h1, max_eq_left (by linarith : r - c ≤ 0)]
      ring
    · have h1 : (0:ℝ) < r / c - 1 := by
        have : (1:ℝ) < r / c := (lt_div_iff₀ hc).mpr (by linarith)
        linarith
      rw [max_eq_right h1.le, max_eq_right (by linarith : (0:ℝ) ≤ r - c)]
      field_simp
  rw [hsq] at hm
  exact hm

/-- **The quantitative pointwise gap of the row**: for `c > 0` and `r ≥ 0`,

    (r-c)₊² - τ_c(r)  ≥  max 0 (c·r - (5/4+c₀)c²) .

The gap is the difference between the sharp parabola `tauSharp c` (the right-hand weight of the
row) and the smoothed weight `τ_c`; the linear lower bound is the difference of the two quadratic
tails, and it is `≥ 0` precisely from `r ≥ (5/4+c₀)c`. -/
lemma tauSharp_sub_tauPhi_ge {c r : ℝ} (hc : 0 < c) :
    max 0 (c * r - (5 / 4 + tauC0phi) * c ^ 2) ≤ tauSharp c r - c ^ 2 * tauPhi (r / c) := by
  have hgap0 : 0 ≤ tauSharp c r - c ^ 2 * tauPhi (r / c) :=
    sub_nonneg.mpr (tauPhiWeight_le_tauSharp hc)
  have hquad : c ^ 2 * tauPhi (r / c) ≤ (r - 3 * c / 2) ^ 2 + tauC0phi * c ^ 2 := by
    have hq := tauPhi_le_quad (r / c)
    rw [tauC0phi_def]
    have hm := mul_le_mul_of_nonneg_left hq (sq_nonneg c)
    have hexp : c ^ 2 * ((r / c - 3 / 2) ^ 2 + ∫ t, t ^ 2 * tauKer t)
        = (r - 3 * c / 2) ^ 2 + (∫ t, t ^ 2 * tauKer t) * c ^ 2 := by
      field_simp
    rwa [hexp] at hm
  rcases le_or_gt r c with hrc | hrc
  · -- below c the max vanishes and the gap is 0
    have h0 : tauSharp c r = 0 := by
      rw [tauSharp, max_eq_left (by linarith : r - c ≤ 0)]; ring
    have hz : c ^ 2 * tauPhi (r / c) = 0 := by
      have h1 : r / c ≤ 1 := by rw [div_le_one hc]; linarith
      rw [tauPhi_zero_of_le_one (r / c) h1, mul_zero]
    have hmax : c * r - (5 / 4 + tauC0phi) * c ^ 2 ≤ 0 := by
      have hc0 := tauC0phi_nonneg
      nlinarith [hrc, sq_nonneg c, hc0]
    rw [max_eq_left hmax, h0, hz]
    simpa using hgap0
  · have h1 : tauSharp c r = (r - c) ^ 2 := by
      rw [tauSharp, max_eq_right (by linarith : (0:ℝ) ≤ r - c)]
    rw [h1]
    rcases le_or_gt r ((5 / 4 + tauC0phi) * c) with hsmall | hbig
    · have hneg : c * r - (5 / 4 + tauC0phi) * c ^ 2 ≤ 0 := by nlinarith
      rw [max_eq_left hneg]
      linarith [hquad, hgap0, hneg]
    · have hpos : 0 ≤ c * r - (5 / 4 + tauC0phi) * c ^ 2 := by nlinarith
      rw [max_eq_right hpos]
      have h2 : (r - 3 * c / 2) ^ 2 + tauC0phi * c ^ 2
          = (r - c) ^ 2 - (c * r - (5 / 4 + tauC0phi) * c ^ 2) := by ring
      linarith [hquad, h2]

end Work.BoseBoxFock
