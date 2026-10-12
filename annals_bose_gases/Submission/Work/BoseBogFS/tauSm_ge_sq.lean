import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.BoseBogFS.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.tauSm_ge_sq` — the kink of the smoothed kinetic symbol

The pin `Work.BoseBogFS.tauSmPin` says

`E.tau k = (1-ε_T)·c²·φ(‖k‖/c) + ε_T·c'²·φ(‖k‖/c')`,  `c = (2sℓ)⁻¹`, `c' = (2dsℓ)⁻¹`,

with the profile `φ` of `BOSE_BOXFOCK_LEAD.md` §2.2, whose only lower bound is
`(max 0 (r-2))² ≤ φ r`.  Since the *first* kink of the smoothed symbol sits at
`‖k‖ = 2c = (sℓ)⁻¹`, and `φ` is nonnegative there, restricting to
`‖k‖ ≥ (sℓ)⁻¹` (the region where `τ̃` has already left its flat bottom) gives the
**kink domination**

`(1-ε_T)·(‖k‖ - (sℓ)⁻¹)² ≤ E.tau k`,

for `0 ≤ ε_T ≤ 1`.  This is the `RHi`-side row that bounds `𝒟_k = ½(𝒜_k + √(𝒜_k²-ℬ_k²))`
from below by its kinetic part on the kept region (cf. `Work.BoseGateFS.tauTilde_ge_kink`,
which states the same domination for the two-term kink *plus* the analogous
`(d s ℓ)⁻¹`-term; here only the first term is needed and no hypothesis on `d` is used,
so the second term is simply discarded as nonnegative).

Main steps:

* one-variable core (`sq_sub_two_mul_le_sq_mul_phi`): for `c > 0` and `x ≥ 2c`,
  `(x - 2c)² ≤ c²·φ(x/c)` — from `φ(x/c) ≥ (max 0 (x/c - 2))² = (x/c - 2)²`;
* apply it at `c = (2sℓ)⁻¹`, `x = ‖F.kmom k‖`, using `2c = (sℓ)⁻¹` and `hk`;
* multiply by `1 - ε_T ≥ 0` and add the nonnegative `ε_T`-weighted second term.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseBogFS

open Work.BoseB7

/-- **One-variable core.**  If `φ r ≥ (max 0 (r-2))²` and `c > 0`, then for every
`x ≥ 2c`, `(x - 2c)² ≤ c²·φ(x/c)`: the argument `x/c` is `≥ 2`, so the `max` in the
lower bound of `φ` is inactive and `c²·(x/c - 2)² = (x - 2c)²`. -/
lemma sq_sub_two_mul_le_sq_mul_phi {φ : ℝ → ℝ}
    (hφ : ∀ r : ℝ, (max 0 (r - 2)) ^ 2 ≤ φ r) {c x : ℝ} (hc : 0 < c) (hx : 2 * c ≤ x) :
    (x - 2 * c) ^ 2 ≤ c ^ 2 * φ (x / c) := by
  have hxc : 2 ≤ x / c := (le_div_iff₀ hc).mpr (by linarith)
  have hm : max 0 (x / c - 2) = x / c - 2 := max_eq_right (sub_nonneg.mpr hxc)
  have h1 : (x / c - 2) ^ 2 ≤ φ (x / c) := by
    have h := hφ (x / c)
    rwa [hm] at h
  have h2 : c ^ 2 * (x / c - 2) ^ 2 = (x - 2 * c) ^ 2 := by field_simp
  calc (x - 2 * c) ^ 2 = c ^ 2 * (x / c - 2) ^ 2 := h2.symm
    _ ≤ c ^ 2 * φ (x / c) := mul_le_mul_of_nonneg_left h1 (sq_nonneg c)

theorem tauSm_ge_sq {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode)
    (hpin : Work.BoseBogFS.tauSmPin F E) (hε0 : 0 ≤ E.eT) (hε1 : E.eT ≤ 1)
    (hs : 0 < E.s) (hℓ : 0 < E.ell) (k : Mode) (hk : (E.s * E.ell)⁻¹ ≤ ‖F.kmom k‖) :
    (1 - E.eT) * (‖F.kmom k‖ - (E.s * E.ell)⁻¹) ^ 2 ≤ E.tau k := by
  -- unpack the pin: `E.tau k` is the two-term convex combination of `φ`
  obtain ⟨φ, _, _, hlow, _, _, htau⟩ := hpin
  have hkey : E.tau k = (1 - E.eT) * ((2 * E.s * E.ell)⁻¹) ^ 2
        * φ (‖F.kmom k‖ / (2 * E.s * E.ell)⁻¹)
      + E.eT * ((2 * E.d * E.s * E.ell)⁻¹) ^ 2
        * φ (‖F.kmom k‖ / (2 * E.d * E.s * E.ell)⁻¹) := congrFun htau k
  rw [hkey]
  -- `2·(2sℓ)⁻¹ = (sℓ)⁻¹`, so `hk` is exactly the hypothesis `x ≥ 2c`
  have h2c : 2 * (2 * E.s * E.ell)⁻¹ = (E.s * E.ell)⁻¹ := by field_simp
  have hleb : 2 * (2 * E.s * E.ell)⁻¹ ≤ ‖F.kmom k‖ := by rw [h2c]; exact hk
  have hkink : (‖F.kmom k‖ - (E.s * E.ell)⁻¹) ^ 2
      ≤ ((2 * E.s * E.ell)⁻¹) ^ 2 * φ (‖F.kmom k‖ / (2 * E.s * E.ell)⁻¹) := by
    have h := sq_sub_two_mul_le_sq_mul_phi hlow (c := (2 * E.s * E.ell)⁻¹)
      (x := ‖F.kmom k‖) (by positivity) hleb
    rwa [h2c] at h
  -- multiply by `1 - ε_T ≥ 0`
  have h1eT : 0 ≤ 1 - E.eT := by linarith
  have hmain : (1 - E.eT) * (‖F.kmom k‖ - (E.s * E.ell)⁻¹) ^ 2
      ≤ (1 - E.eT) * ((2 * E.s * E.ell)⁻¹) ^ 2
          * φ (‖F.kmom k‖ / (2 * E.s * E.ell)⁻¹) := by
    calc (1 - E.eT) * (‖F.kmom k‖ - (E.s * E.ell)⁻¹) ^ 2
        ≤ (1 - E.eT) * (((2 * E.s * E.ell)⁻¹) ^ 2
            * φ (‖F.kmom k‖ / (2 * E.s * E.ell)⁻¹)) :=
          mul_le_mul_of_nonneg_left hkink h1eT
      _ = (1 - E.eT) * ((2 * E.s * E.ell)⁻¹) ^ 2
            * φ (‖F.kmom k‖ / (2 * E.s * E.ell)⁻¹) := by ring
  -- the `ε_T`-weighted second term is nonnegative and is discarded
  have hnn : 0 ≤ E.eT * ((2 * E.d * E.s * E.ell)⁻¹) ^ 2
      * φ (‖F.kmom k‖ / (2 * E.d * E.s * E.ell)⁻¹) :=
    mul_nonneg (mul_nonneg hε0 (sq_nonneg _)) (le_trans (sq_nonneg _) (hlow _))
  exact le_trans hmain (le_add_of_nonneg_right hnn)

end Work.BoseBogFS
