import Submission.CDTPlan.Interfaces
import Submission.CDT.ZagierHBC

/-!
# cdt_linearIndependent — Theorem A contracts, wave 1 (orchestrator-owned)

The Theorem-A contour (redesigned 2026-09-26; the paper's printed nesting of the rotation angles
is wrong — see FM3-DRIVE §3): `ψ_A(z) = −R·lune(c, −w₄)`, `w₀ = s·z`,
`w_j = e^{2πi t_j}·Slit(w_{j−1}, r_j)`, with s = 491/500, R = 4/5, c = 36/5,
r = (9/10, 379/625, 673/1250, 7487/10000), t = (2033/25000, 2927/25000, 453/12500, −1971/25000).
`|ψ_A'(0)| = s R (c²−1)/(c²+1) ∏ 4r_j/(1+r_j)² = 0.63141515…`, `log(256|ψ_A'(0)|) = 5.08538…`.
The holonomy bound is used with `l = 2`: maps `φ_A(z/10⁴)`, `φ_A(283 z/500)`, `φ_A(z)` and
`γ = (0, 71/125, 277/100, 14)`; numerically the rearrangement integral is 10.97411 and
the bound is 13.513 < 14.
-/

open Complex Metric

namespace Submission.CDTPlan

/-- The slit map `(𝔻,0) ≅ (𝔻 ∖ (−1,−r], 0)` (paper eq. `(slit)`), principal square root,
value `0` at `z = 0` (removable singularity). -/
noncomputable def slit (r : ℝ) (z : ℂ) : ℂ :=
  if z = 0 then 0 else
    ((1 + (r : ℂ)) ^ 2 - 2 * ((r : ℂ) - 1) ^ 2 * z + (1 + (r : ℂ)) ^ 2 * z ^ 2 +
        (1 + (r : ℂ)) * (z - 1) *
          ((1 + (r : ℂ)) ^ 2 - 2 * (1 - 6 * (r : ℂ) + (r : ℂ) ^ 2) * z + (1 + (r : ℂ)) ^ 2 * z ^ 2)
            ^ (1 / 2 : ℂ)) / (8 * (r : ℂ) * z)

/-- `e^{2πit}`. -/
noncomputable def rot (t : ℝ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))

/-- The four-slit part `w₄(z)` of the Theorem-A contour map. -/
noncomputable def slitsA (z : ℂ) : ℂ :=
  rot (-1971 / 25000) * slit (7487 / 10000)
    (rot (453 / 12500) * slit (673 / 1250)
      (rot (2927 / 25000) * slit (379 / 625)
        (rot (2033 / 25000) * slit (9 / 10) ((491 / 500 : ℂ) * z))))

/-- The Theorem-A contour map `ψ_A(z) = −(4/5)·lune(36/5, −w₄(z))`. -/
noncomputable def psiA (z : ℂ) : ℂ := -(4 / 5) * lune (36 / 5) (-slitsA z)

/-- `φ_A = h ∘ ψ_A`. -/
noncomputable def phiA (z : ℂ) : ℂ := hauptH (psiA z)

/-- The three maps of the `l = 2` holonomy bound for Theorem A. -/
noncomputable def phiAfam : Fin 3 → ℂ → ℂ :=
  ![fun z => phiA (z / 10000), fun z => phiA (283 * z / 500), phiA]

/-- The partition `γ = (0, 71/125, 277/100, 14)`. -/
noncomputable def gammaA : Fin 4 → ℝ := ![0, 71 / 125, 277 / 100, 14]

/-- Certified numerics for Theorem A: the conformal radius, the rearrangement integral of the
`l = 2` family (true value 10.97411), and the absence of preimages of `−1/72` outside the tiny
disc `|z| < 1/1000` (the principal preimage is at `|z| ≈ 8.6e-5`; the nearest excluded
preimages are ≥ 8.6e-4 away from `ψ_A(circle)` in the q-disc; `min_{|z|=1} |φ_A + 1/72| = 3.66e-4`). -/
def ANumerics : Prop :=
  ‖deriv psiA 0‖ = 2383521894760738000000000 / 3774888615849058882987209 ∧
    rearrInt (fun k => (gammaA k.succ - gammaA k.castSucc) / 14) phiAfam ≤ 112 / 10 ∧
    ∀ z : ℂ, 1 / 1000 ≤ ‖z‖ → ‖z‖ ≤ 1 → phiA z ≠ -1 / 72

/-- Analytic facts on `ψ_A` (exact, no numerics). -/
def PsiAFacts : Prop :=
  ContinuousOn psiA (closedBall 0 1) ∧ DifferentiableOn ℂ psiA (ball 0 1) ∧ psiA 0 = 0 ∧
    (∀ z ∈ closedBall (0 : ℂ) 1, ‖psiA z‖ < 1) ∧
    (∀ z ∈ closedBall (0 : ℂ) 1, psiA z = 0 → z = 0)

/-- Integrality of Zagier's `c_n` up to the harmless factor 8:
`8·[1..n]²·c_n ∈ ℤ` (numerically: `[1..n]²c_n ∈ ℤ` for n ≤ 399 and its denominator is odd). -/
def ZagierCIntegrality : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ z : ℤ, (8 * (lcmUpto n : ℚ) ^ 2) * Submission.CDT.HC_coeff n = z

/-- Integrality of Zagier's `b_n` up to a fixed factor: `K·[1..n]²·b_n ∈ ℤ`
(numerically `[1..n]²b_n ∈ ℤ` for n ≤ 399, and 3 never divides the denominator). -/
def ZagierBIntegrality : Prop :=
  ∃ K : ℕ, 0 < K ∧ ∀ n : ℕ, 1 ≤ n →
    ∃ z : ℤ, ((K : ℚ) * (lcmUpto n : ℚ) ^ 2) * Submission.CDT.HB_coeff n = z

end Submission.CDTPlan
