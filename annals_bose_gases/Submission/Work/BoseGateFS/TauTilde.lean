import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseGateFS.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseGateFS.TauTilde` — the smoothed kinetic symbol `τ̃`

`BOSE_BOXFOCK_LEAD.md` §2.2: FS's kinetic symbol `def:tau` has kinks at
`|k| = (2sℓ)⁻¹` and `(2dsℓ)⁻¹`, and its periodisation onto the box lattice
differs from the whole-space multiplier by `≈ 1/(sℓ²)` per particle — *not*
absorbable in the §10 gap.  The honest model therefore uses the **smoothed**
symbol

`τ̃(k) = (1-ε_T)c²φ(|k|/c) + ε_T c'²φ(|k|/c')`,  `c = (2sℓ)⁻¹`, `c' = (2dsℓ)⁻¹`,

with `φ` the `C^∞` monotone profile of `Work.BoseBoxFock.exists_tauProf`:

`(max 0 (r-2))² ≤ φ r ≤ (max 0 (r-1))²`,  `φ r = 0` for `r ≤ 1`.

The design's name for this object is `Work.BoseBoxFock.tauSm`; `tauTilde` is the
same formula, written here for the τ̃-rows of the gate.  The identification
`tauTilde Work.BoseBoxFock.tauProf eT s d ℓ = Work.BoseBoxFock.tauSm eT s d ℓ` is
recorded in the bridge module.

## What the gate needs from `τ̃`

* `τ̃ k ≤ ‖k‖²` (`tauTilde_le_sq`) — with `φ ≤ (r-1)₊²`;
* the *deficit bound* `‖k‖² - τ̃ k ≤ 4‖k‖/(dsℓ)` (`tauTilde_deficit`) — with
  `φ ≥ (r-2)₊²` and `d ≤ 1`; this replaces FS's kinked `def:tau` in both
  `A_ge`/`ABq` and the kinetic domination;
* Lipschitz growth `|τ̃ p - τ̃ q| ≤ C(1+‖p‖+‖q‖)‖p-q‖` (`tauTilde_lip`) — with a
  bound `|φ'| ≤ C(1+r)`; this replaces `tauFun_lip_of` in K3 (`alpha_lip`);
* the kinked lower bound `(1-ε_T)(r-2c)₊² + ε_T(r-2c')₊² ≤ τ̃ k`
  (`tauTilde_ge_kink`) — the input of the `P_H^q` domination
  (`arith_tauTilde_ge`).
-/

noncomputable section

open scoped BigOperators Pointwise

namespace Work.BoseGateFS

/-- **The smoothed kinetic symbol** `τ̃ ≤ τ` of `BOSE_BOXFOCK_LEAD.md` §2.2
(the design's `Work.BoseBoxFock.tauSm`, same formula). -/
def tauTilde (φ : ℝ → ℝ) (eT s d ℓ : ℝ) (k : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  (1 - eT) * ((2 * s * ℓ)⁻¹) ^ 2 * φ (‖k‖ / (2 * s * ℓ)⁻¹)
    + eT * ((2 * d * s * ℓ)⁻¹) ^ 2 * φ (‖k‖ / (2 * d * s * ℓ)⁻¹)

/-- `τ̃` is radial, hence even. -/
lemma tauTilde_even (φ : ℝ → ℝ) (eT s d ℓ : ℝ) (k : EuclideanSpace ℝ (Fin 3)) :
    tauTilde φ eT s d ℓ (-k) = tauTilde φ eT s d ℓ k := by
  simp only [tauTilde, norm_neg]

/-- `τ̃` is radial: it only depends on `‖k‖`. -/
lemma tauTilde_eq_of_norm_eq (φ : ℝ → ℝ) (eT s d ℓ : ℝ)
    {k k' : EuclideanSpace ℝ (Fin 3)} (h : ‖k‖ = ‖k'‖) :
    tauTilde φ eT s d ℓ k = tauTilde φ eT s d ℓ k' := by
  simp only [tauTilde, h]

end Work.BoseGateFS
