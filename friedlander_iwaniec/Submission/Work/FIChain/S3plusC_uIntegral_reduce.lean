/-
# `Submission.Work.FIChain.S3plusC_uIntegral_reduce` — the `λ⁺` inner sum as a *level* integral
of a `ρ`-window sum, at levels `≤ c/Cm`

`Work.FIChain.S3plusInnerC a N ℓ z sz Cm = Σ_{z<c≤sz, ℓc≤N} μ(c)·λ⁺(c)·a(ℓc)`.

The PROVED identity `Work.FIChain.S3plusC_lamPlus_identity`,
`μ(c)·λ⁺(c) = ∫_1^{c/Cm} ρ(c;u) du/u` (`ρ(c;u) = rhoTrunc c u`), has the crucial feature that its
**level range is `[1, c/Cm]`, not `[1, c]`**: the `μ(c)` of the summand is absorbed by the
divisor-duality step of the identity, and in exchange the truncation level drops from `≈` the
position `c` to `≈ c/Cm` — far below the `(2.12)`-forbidden regime `level ≈ position` (where
`ρ(n;s) = −μ(n)` and the `ρ`-window degenerates into the unsigned double count).

This module records the resulting two-step reduction (both steps are the composite of lemmas
already proved in the workspace — nothing new is asserted here):

* `S3plusInnerC_eq_levelIntegral` — the level-integral form
  `S3plusInnerC atilc N ℓ z sz Cm
     = ∫_1^{sz/Cm} (du/u) Σ_{z<c≤sz, ℓc≤N} (if Cm·u < c then atilc(ℓc)·ρ(c;u) else 0)`;

**The remaining gap (see `NOTES_S3plusC_session9.md`).**  The `u`-integrand is a `ρ`-window sum
for the sequence `atilc = μ²·FIa` *without* any Möbius factor on the position `c`, whereas every
window hypothesis available in this workspace (`Work.FITop.RhoWindowC` / `Work.FIChain.RhoWindowC_param_aux`,
proved from `Prop41Stmt`) is stated for `XrhoC a N m s t u = Σ ρ(c;s)·μ(mc)·a(mc)` — a Möbius
factor on the product `mc`.  Matching the two needs `μ(ℓ)·μ(ℓc) = 1`, i.e. is FALSE in general.
So the level-integral form of `λ⁺` is *not* covered by the proved `ρ`-window as it stands.
-/
import Mathlib
import Submission.Work.FIChain.S3plusC_aux
import Submission.Work.FIChain.s3InnerInt_eq_integral_swap
import Submission.Work.FIChain.s3InnerInt_eq_dsum

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIChain

open Finset MeasureTheory
open scoped BigOperators Interval

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `atilc = μ²·FIa` vanishes off the squarefree integers. -/
lemma atilc_eq_zero_of_not_squarefree (n : ℕ) (h : ¬ Squarefree n) : atilc n = 0 := by
  simp [Work.FITop.atilFIa, Submission.ASP.atil,
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree h]

/-- **The `λ⁺` inner sum as a level integral** (levels `u ∈ [1, sz/Cm]`):
`S3plusInnerC atilc N ℓ z sz Cm = ∫_1^{sz/Cm} (du/u) Σ_{z<c≤sz, ℓc≤N} (if Cm·u < c then
atilc(ℓc)·ρ(c;u) else 0)`.  Composites the PROVED
`S3plusInnerC_eq_s3InnerInt` (`μ(c)λ⁺(c) = ∫_1^{c/Cm}ρ(c;u)du/u`) with the PROVED Fubini swap
`s3InnerInt_eq_integral_swap`. -/
theorem S3plusInnerC_eq_levelIntegral (x ℓ : ℕ) (z sz : ℝ) (Cm : ℕ)
    (hCm : 1 ≤ Cm) (hz2 : 2 ≤ z) (hzCm : ((Cm : ℕ) : ℝ) < z) (hsz : 0 < sz)
    (hT : 1 ≤ sz / (Cm : ℝ)) :
    S3plusInnerC atilc x ℓ z sz (Cm : ℝ)
      = ∫ u in (1 : ℝ)..(sz / (Cm : ℝ)),
          ∑ c ∈ (Finset.Icc 1 x).filter
              (fun c => z < ((c : ℕ) : ℝ) ∧ ((c : ℕ) : ℝ) ≤ sz ∧ ℓ * c ≤ x),
            (if (Cm : ℝ) * u < ((c : ℕ) : ℝ)
              then atilc (ℓ * c) * Submission.ASP.rhoTrunc c u else 0) / u := by
  rw [S3plusInnerC_eq_s3InnerInt atilc x ℓ Cm z sz atilc_eq_zero_of_not_squarefree hCm hz2 hzCm]
  exact s3InnerInt_eq_integral_swap atilc x ℓ Cm z sz hCm (le_of_lt hzCm) hsz hT

end

end Work.FIChain
