import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.BoseB6.Scaled
import Submission.Work.BoseBoxFock.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.tauSm_le_fsTau` — the smoothed symbol dominates FS's kink

The view pins the kinetic symbol to the *smoothed* profile
`τ̃ = (1-eT)c²φ(‖k‖/c) + eT c'²φ(‖k‖/c')` with `c = (2sℓ)⁻¹`, `c' = (2dsℓ)⁻¹` and
`φ ≤ (max 0 (·-1))²` (`Work.BoseBoxFock.tauProf`), while FS's model symbol in the scaled
variables is the two kinked parabolas
`fsTau εT c1 c2 t = (1-εT)(max (|t|-c1) 0)² + εT (max (|t|-c2) 0)²`
(`Work.BoseB6.fsTau`) with the *pinned* thresholds `c1 = (2sℓ)⁻¹/√P`,
`c2 = (2dsℓ)⁻¹/√P` at `P = ρ_z a`, `t = ‖k‖/√(ρ_z a)`.

Because `√P·c1 = (2sℓ)⁻¹` and `√P·c2 = (2dsℓ)⁻¹`, rescaling the kinks by `√P` converts
each of FS's terms into `(max 0 (‖k‖ - c))²` respectively `(max 0 (‖k‖ - c'))²`, which by
the upper bound of the profile dominates `c²φ(‖k‖/c)` respectively `c'²φ(‖k‖/c')`.  Hence

  `tauSm εT s d ℓ k ≤ P · fsTau εT c1 c2 (eucNorm3 k / √P)`

— the smoothed symbol is *below* the model's, uniformly in the mode.  (This is the
inequality direction used by `FINDING_tauSm_vs_fsTau.md` §3: the datum's summand is the
larger one, and the excess is absorbed by the error bracket.)

Nothing here uses `0 < d` beyond positivity of the second threshold (in particular no
`d ≥ 1` and no monotonicity of `φ` is needed: the two terms are bounded separately).
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseBogFS

/-- The upper bound of the smoothing profile `τ̃ ≤ (max 0 (·-1))²`
(`Work.BoseBoxFock.exists_tauProf`). -/
lemma tauProf_le_upper (r : ℝ) :
    Work.BoseBoxFock.tauProf r ≤ (max 0 (r - 1)) ^ 2 :=
  Work.BoseBoxFock.tauProf_spec.2.2.2.1 r

/-- **The one-variable core.**  Since `φ(r) ≤ (max 0 (r-1))²`, for `c > 0` the rescaled
smoothed term is dominated by the kink at `c`: `c²·φ(x/c) ≤ (max 0 (x-c))²`. -/
lemma sq_mul_tauProf_le {c x : ℝ} (hc : 0 < c) :
    c ^ 2 * Work.BoseBoxFock.tauProf (x / c) ≤ (max 0 (x - c)) ^ 2 := by
  have h := tauProf_le_upper (x / c)
  have hcm : c * max 0 (x / c - 1) = max 0 (x - c) := by
    rw [mul_max_of_nonneg _ _ hc.le, mul_zero, mul_sub, mul_one,
        mul_div_cancel₀ x (ne_of_gt hc)]
  calc c ^ 2 * Work.BoseBoxFock.tauProf (x / c)
      ≤ c ^ 2 * (max 0 (x / c - 1)) ^ 2 := mul_le_mul_of_nonneg_left h (sq_nonneg c)
    _ = (c * max 0 (x / c - 1)) ^ 2 := by rw [mul_pow]
    _ = (max 0 (x - c)) ^ 2 := by rw [hcm]

/-- **Rescaling FS's kink by `√P`.**  If `√P·c1 = c` then
`P·(max (|x/√P| - c1) 0)² = (max 0 (x - c))²`: multiplying the kink argument by
`√P ≥ 0` moves the threshold from `c1` to `√P·c1 = c` and the prefactor `P` into the
square. -/
lemma sqrtP_mul_fsTau_term {P c c1 x : ℝ} (hP : 0 < P) (hx : 0 ≤ x)
    (hc : Real.sqrt P * c1 = c) :
    P * (max (|x / Real.sqrt P| - c1) 0) ^ 2 = (max 0 (x - c)) ^ 2 := by
  have hS : 0 < Real.sqrt P := Real.sqrt_pos.mpr hP
  have habs : |x / Real.sqrt P| = x / Real.sqrt P := abs_of_nonneg (div_nonneg hx hS.le)
  have hm : Real.sqrt P * max (x / Real.sqrt P - c1) 0 = max 0 (x - c) := by
    rw [mul_max_of_nonneg _ _ hS.le, mul_zero, mul_sub, hc,
        mul_div_cancel₀ x (ne_of_gt hS), max_comm]
  have hsq : Real.sqrt P ^ 2 = P := Real.sq_sqrt hP.le
  calc P * (max (|x / Real.sqrt P| - c1) 0) ^ 2
      = P * (max (x / Real.sqrt P - c1) 0) ^ 2 := by rw [habs]
    _ = Real.sqrt P ^ 2 * (max (x / Real.sqrt P - c1) 0) ^ 2 := by rw [hsq]
    _ = (Real.sqrt P * max (x / Real.sqrt P - c1) 0) ^ 2 := by rw [mul_pow]
    _ = (max 0 (x - c)) ^ 2 := by rw [hm]

/-- The corpus norm `Submission.BoseGases.eucNorm3` on `Fin 3 → ℝ` is the Euclidean
norm of `EuclideanSpace ℝ (Fin 3)`. -/
lemma eucNorm3_eq_norm (k : EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.eucNorm3 k = ‖k‖ := by
  rw [EuclideanSpace.norm_eq, Submission.BoseGases.eucNorm3]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => by rw [Real.norm_eq_abs, sq_abs])

/-- **The smoothed kinetic symbol is dominated by FS's kinked symbol at the pinned
thresholds** (the inequality form of the symbol identification; the reverse inequality
fails and is recorded in `FINDING_tauSm_vs_fsTau.md`). -/
theorem tauSm_le_fsTau {εT s d ℓ P c1 c2 : ℝ} (hε0 : 0 ≤ εT) (hε1 : εT ≤ 1)
    (hs : 0 < s) (hd : 0 < d) (hℓ : 0 < ℓ) (hP : 0 < P)
    (hc1 : c1 = (2 * s * ℓ)⁻¹ / Real.sqrt P) (hc2 : c2 = (2 * d * s * ℓ)⁻¹ / Real.sqrt P)
    (k : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseBoxFock.tauSm εT s d ℓ k
      ≤ P * Work.BoseB6.fsTau εT c1 c2 (Submission.BoseGases.eucNorm3 k / Real.sqrt P) := by
  have hnorm : Submission.BoseGases.eucNorm3 k = ‖k‖ := eucNorm3_eq_norm k
  have hc1' : Real.sqrt P * c1 = (2 * s * ℓ)⁻¹ := by rw [hc1]; field_simp
  have hc2' : Real.sqrt P * c2 = (2 * d * s * ℓ)⁻¹ := by rw [hc2]; field_simp
  -- FS's side, with the two thresholds rescaled back to the physical ones
  have hR : P * Work.BoseB6.fsTau εT c1 c2 (Submission.BoseGases.eucNorm3 k / Real.sqrt P)
      = (1 - εT) * (max 0 (‖k‖ - (2 * s * ℓ)⁻¹)) ^ 2
        + εT * (max 0 (‖k‖ - (2 * d * s * ℓ)⁻¹)) ^ 2 := by
    rw [hnorm]
    unfold Work.BoseB6.fsTau
    have hA := sqrtP_mul_fsTau_term (P := P) (c := (2 * s * ℓ)⁻¹) (c1 := c1)
        (x := ‖k‖) hP (norm_nonneg k) hc1'
    have hB := sqrtP_mul_fsTau_term (P := P) (c := (2 * d * s * ℓ)⁻¹) (c1 := c2)
        (x := ‖k‖) hP (norm_nonneg k) hc2'
    calc P * ((1 - εT) * max (|‖k‖ / Real.sqrt P| - c1) 0 ^ 2
            + εT * max (|‖k‖ / Real.sqrt P| - c2) 0 ^ 2)
        = (1 - εT) * (P * max (|‖k‖ / Real.sqrt P| - c1) 0 ^ 2)
          + εT * (P * max (|‖k‖ / Real.sqrt P| - c2) 0 ^ 2) := by ring
      _ = (1 - εT) * (max 0 (‖k‖ - (2 * s * ℓ)⁻¹)) ^ 2
          + εT * (max 0 (‖k‖ - (2 * d * s * ℓ)⁻¹)) ^ 2 := by rw [hA, hB]
  rw [hR]
  -- the view's side, regrouped for the termwise comparison
  have hnode : Work.BoseBoxFock.tauSm εT s d ℓ k
      = (1 - εT) * (((2 * s * ℓ)⁻¹) ^ 2
            * Work.BoseBoxFock.tauProf (‖k‖ / (2 * s * ℓ)⁻¹))
        + εT * (((2 * d * s * ℓ)⁻¹) ^ 2
            * Work.BoseBoxFock.tauProf (‖k‖ / (2 * d * s * ℓ)⁻¹)) := by
    unfold Work.BoseBoxFock.tauSm
    ring
  rw [hnode]
  have hc₁ : 0 < (2 * s * ℓ)⁻¹ := by positivity
  have hc₂ : 0 < (2 * d * s * ℓ)⁻¹ := by positivity
  have h1 : ((2 * s * ℓ)⁻¹) ^ 2 * Work.BoseBoxFock.tauProf (‖k‖ / (2 * s * ℓ)⁻¹)
      ≤ (max 0 (‖k‖ - (2 * s * ℓ)⁻¹)) ^ 2 := sq_mul_tauProf_le hc₁
  have h2 : ((2 * d * s * ℓ)⁻¹) ^ 2 * Work.BoseBoxFock.tauProf (‖k‖ / (2 * d * s * ℓ)⁻¹)
      ≤ (max 0 (‖k‖ - (2 * d * s * ℓ)⁻¹)) ^ 2 := sq_mul_tauProf_le hc₂
  have hε1' : 0 ≤ 1 - εT := by linarith
  have t1 := mul_le_mul_of_nonneg_left h1 hε1'
  have t2 := mul_le_mul_of_nonneg_left h2 hε0
  linarith

end Work.BoseBogFS
