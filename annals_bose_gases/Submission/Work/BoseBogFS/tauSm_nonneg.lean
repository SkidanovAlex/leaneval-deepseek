import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.BoseBogFS.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

theorem tauSm_nonneg {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode)
    (hpin : Work.BoseBogFS.tauSmPin F E) (hε0 : 0 ≤ E.eT) (hε1 : E.eT ≤ 1)
    (hs : 0 ≤ E.s) (hd : 0 ≤ E.d) (hℓ : 0 ≤ E.ell) (k : Mode) :
    0 ≤ E.tau k := by
  -- Unpack the pin: `E.tau` is a two-term convex combination of `φ` at the two
  -- rescaled momenta, and `φ r ≥ (max 0 (r-2))² ≥ 0`.
  obtain ⟨φ, _, _, hlow, _, _, htau⟩ := hpin
  rw [htau]
  have hφ₀ : 0 ≤ φ (‖F.kmom k‖ / (2 * E.s * E.ell)⁻¹) :=
    le_trans (sq_nonneg _) (hlow _)
  have hφ₁ : 0 ≤ φ (‖F.kmom k‖ / (2 * E.d * E.s * E.ell)⁻¹) :=
    le_trans (sq_nonneg _) (hlow _)
  have h1 : 0 ≤ (1 - E.eT) * ((2 * E.s * E.ell)⁻¹) ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  have h2 : 0 ≤ E.eT * ((2 * E.d * E.s * E.ell)⁻¹) ^ 2 :=
    mul_nonneg hε0 (sq_nonneg _)
  linarith [mul_nonneg h1 hφ₀, mul_nonneg h2 hφ₁]

end Work.BoseBogFS
