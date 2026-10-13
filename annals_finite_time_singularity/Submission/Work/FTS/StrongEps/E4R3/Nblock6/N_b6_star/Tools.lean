import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.HkSq_const_mul
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.VocabO
import Submission.Work.Spaces.ProductRuleInW

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `N_b6_star.Tools` — the elementary tools of the nine star pieces of the level-`6` `N`-block

The per-piece arithmetic of `Nblock6.N_b6_star`: every star piece is a scalar times a product
`A·P` of a `𝒲^{6,∞}`-coefficient priced by `KA` and an `ℋ⁶`-factor priced by `SP`; the product
rule `RawE6Aux.wlInfMul6` gives `HkSq α 6 (A·P) ≤ Cw α⁻¹ KA² (1 + SP)`, and the three lemmas
`piece_arith_e1`, `piece_arith_e2`, `piece_arith_sl1` reduce the three occurring shapes
(`1 + A·E`, `1 + Z`) to a constant times `B`.
-/

namespace Work.FTS.StrongEps.E4R3.Nblock6

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open MeasureTheory Set Filter
open scoped Real Topology

open Work.FTS.Galerkin (Fn)

/-! ## Elementary tools -/

/-- `HkNorm`-`HkSq` bookkeeping (a local copy; the `RawE6Aux` one sits in a file with development
stubs). -/
theorem hkNorm_sq_loc (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) :
    (Work.Spaces.HkNorm α k f) ^ 2 = Work.Spaces.HkSq α k f := by
  rw [Work.Spaces.HkNorm]
  exact Real.sq_sqrt (Work.Spaces.HkSq_nonneg α k f)

/-- `α^{-1}·(K α)² ≤ K²` for `0 < α ≤ 1`. -/
theorem inv_mul_sq_le {α K : ℝ} (hα1 : α ≤ 1) (hα0 : 0 < α) :
    α ^ (-(1 : ℝ)) * (K * α) ^ 2 ≤ K ^ 2 := by
  have h : α ^ (-(1 : ℝ)) * (K * α) ^ 2 = K ^ 2 * α := by
    rw [Real.rpow_neg_one, mul_pow]; field_simp
  rw [h]; nlinarith [sq_nonneg K]

/-- `α^{-1}·(K α²)² ≤ K²` for `0 < α ≤ 1`. -/
theorem inv_mul_sq_sq_le {α K : ℝ} (hα1 : α ≤ 1) (hα0 : 0 < α) :
    α ^ (-(1 : ℝ)) * (K * α ^ 2) ^ 2 ≤ K ^ 2 := by
  have h : α ^ (-(1 : ℝ)) * (K * α ^ 2) ^ 2 = K ^ 2 * α ^ 3 := by
    rw [Real.rpow_neg_one, mul_pow]; field_simp
  rw [h]
  have h3 : α ^ 3 ≤ 1 := pow_le_one₀ (n := 3) hα0.le hα1
  nlinarith [sq_nonneg K]

/-- `HkSq α k P ≤ Ce²·HkSq α k f` from `HkNorm α k P ≤ Ce·HkNorm α k f` (no sign hypothesis on
`Ce`: the absolute value is taken first). -/
theorem hkSq_le_of_hkNorm_le {α : ℝ} (k : ℕ) {P f : ℝ → ℝ → ℝ} {Ce : ℝ}
    (h : Work.Spaces.HkNorm α k P ≤ Ce * Work.Spaces.HkNorm α k f) :
    Work.Spaces.HkSq α k P ≤ Ce ^ 2 * Work.Spaces.HkSq α k f := by
  have h2 : Work.Spaces.HkNorm α k P ≤ |Ce| * Work.Spaces.HkNorm α k f :=
    le_trans h (mul_le_mul_of_nonneg_right (le_abs_self Ce) (Real.sqrt_nonneg _))
  have h1 : (Work.Spaces.HkNorm α k P) ^ 2 ≤ (|Ce| * Work.Spaces.HkNorm α k f) ^ 2 :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) h2 2
  rw [hkNorm_sq_loc, mul_pow, sq_abs, hkNorm_sq_loc] at h1
  exact h1

/-- `HkSq α k P ≤ K²` from `HkNorm α k P ≤ K`. -/
theorem hkSq_le_sq_of_le {α : ℝ} (k : ℕ) {P : ℝ → ℝ → ℝ} {K : ℝ}
    (h : Work.Spaces.HkNorm α k P ≤ K) : Work.Spaces.HkSq α k P ≤ K ^ 2 := by
  have h1 : (Work.Spaces.HkNorm α k P) ^ 2 ≤ K ^ 2 :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
  rwa [hkNorm_sq_loc] at h1

/-! ## The per-piece arithmetic

Each piece is `c·(A·P)` with `HkSq α 6 (A·P) ≤ Cw α⁻¹ KA² (1 + SP)` and `KA = Ci·α^p`; the
following three lemmas reduce that to the final constant. -/

/-- The `1 + A·E`-shape (fixed and `w`-slots): reduce `c·(Cw α⁻¹(Ciα)^2(1+AE))`. -/
theorem piece_arith_e1 {α Cw Ci A E c2 B : ℝ}
    (hCw : 0 ≤ Cw) (hcore : α ^ (-(1 : ℝ)) * (Ci * α) ^ 2 ≤ Ci ^ 2)
    (hc2 : 0 ≤ c2) (hc2le : c2 ≤ 4) (hA : 0 ≤ A) (hE : 0 ≤ E) (hEB : E ≤ B) (hB1 : 1 ≤ B) :
    c2 * (Cw * α ^ (-(1 : ℝ)) * (Ci * α) ^ 2 * (1 + A * E))
      ≤ 4 * (Cw * Ci ^ 2) * ((1 + A) * B) := by
  have hZ : 0 ≤ 1 + A * E := add_nonneg zero_le_one (mul_nonneg hA hE)
  have h1 : 1 + A * E ≤ (1 + A) * B := by nlinarith
  have hfac : 0 ≤ c2 * Cw * (1 + A * E) := mul_nonneg (mul_nonneg hc2 hCw) hZ
  calc c2 * (Cw * α ^ (-(1 : ℝ)) * (Ci * α) ^ 2 * (1 + A * E))
      = (c2 * Cw * (1 + A * E)) * (α ^ (-(1 : ℝ)) * (Ci * α) ^ 2) := by ring
    _ ≤ (c2 * Cw * (1 + A * E)) * Ci ^ 2 := mul_le_mul_of_nonneg_left hcore hfac
    _ ≤ (4 * Cw * (1 + A * E)) * Ci ^ 2 := by
        have h2 : c2 * Cw * (1 + A * E) ≤ 4 * Cw * (1 + A * E) := by
          have hAE : 0 ≤ Cw * (1 + A * E) := mul_nonneg hCw hZ
          calc c2 * Cw * (1 + A * E) = c2 * (Cw * (1 + A * E)) := by ring
            _ ≤ 4 * (Cw * (1 + A * E)) := mul_le_mul_of_nonneg_right hc2le hAE
            _ = 4 * Cw * (1 + A * E) := by ring
        exact mul_le_mul_of_nonneg_right h2 (sq_nonneg Ci)
    _ ≤ (4 * Cw * ((1 + A) * B)) * Ci ^ 2 := by
        have h3 : 4 * Cw * (1 + A * E) ≤ 4 * Cw * ((1 + A) * B) :=
          mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 4 * Cw)
        exact mul_le_mul_of_nonneg_right h3 (sq_nonneg Ci)
    _ = 4 * (Cw * Ci ^ 2) * ((1 + A) * B) := by ring

/-- The `1 + A·E`-shape with a *quadratic* slot `(Ci·α²)²` (piece `5`). -/
theorem piece_arith_e2 {α Cw Ci A E c2 B : ℝ}
    (hCw : 0 ≤ Cw) (hcore : α ^ (-(1 : ℝ)) * (Ci * α ^ 2) ^ 2 ≤ Ci ^ 2)
    (hc2 : 0 ≤ c2) (hc2le : c2 ≤ 4) (hA : 0 ≤ A) (hE : 0 ≤ E) (hEB : E ≤ B) (hB1 : 1 ≤ B) :
    c2 * (Cw * α ^ (-(1 : ℝ)) * (Ci * α ^ 2) ^ 2 * (1 + A * E))
      ≤ 4 * (Cw * Ci ^ 2) * ((1 + A) * B) := by
  have hZ : 0 ≤ 1 + A * E := add_nonneg zero_le_one (mul_nonneg hA hE)
  have h1 : 1 + A * E ≤ (1 + A) * B := by nlinarith
  have hfac : 0 ≤ c2 * Cw * (1 + A * E) := mul_nonneg (mul_nonneg hc2 hCw) hZ
  calc c2 * (Cw * α ^ (-(1 : ℝ)) * (Ci * α ^ 2) ^ 2 * (1 + A * E))
      = (c2 * Cw * (1 + A * E)) * (α ^ (-(1 : ℝ)) * (Ci * α ^ 2) ^ 2) := by ring
    _ ≤ (c2 * Cw * (1 + A * E)) * Ci ^ 2 := mul_le_mul_of_nonneg_left hcore hfac
    _ ≤ (4 * Cw * (1 + A * E)) * Ci ^ 2 := by
        have h2 : c2 * Cw * (1 + A * E) ≤ 4 * Cw * (1 + A * E) := by
          have hAE : 0 ≤ Cw * (1 + A * E) := mul_nonneg hCw hZ
          calc c2 * Cw * (1 + A * E) = c2 * (Cw * (1 + A * E)) := by ring
            _ ≤ 4 * (Cw * (1 + A * E)) := mul_le_mul_of_nonneg_right hc2le hAE
            _ = 4 * Cw * (1 + A * E) := by ring
        exact mul_le_mul_of_nonneg_right h2 (sq_nonneg Ci)
    _ ≤ (4 * Cw * ((1 + A) * B)) * Ci ^ 2 := by
        have h3 : 4 * Cw * (1 + A * E) ≤ 4 * Cw * ((1 + A) * B) :=
          mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 4 * Cw)
        exact mul_le_mul_of_nonneg_right h3 (sq_nonneg Ci)
    _ = 4 * (Cw * Ci ^ 2) * ((1 + A) * B) := by ring

/-- The `1 + Z`-shape with an arbitrary nonnegative `Z` (the shifted `F_*`-slots). -/
theorem piece_arith_sl1 {α Cw Ci Z c2 B : ℝ}
    (hCw : 0 ≤ Cw) (hcore : α ^ (-(1 : ℝ)) * (Ci * α) ^ 2 ≤ Ci ^ 2)
    (hc2 : 0 ≤ c2) (hc2le : c2 ≤ 4) (hB1 : 1 ≤ B) (hZ : 0 ≤ Z) :
    c2 * (Cw * α ^ (-(1 : ℝ)) * (Ci * α) ^ 2 * (1 + Z))
      ≤ 4 * (Cw * Ci ^ 2) * ((1 + Z) * B) := by
  have hfac : 0 ≤ c2 * Cw * (1 + Z) := mul_nonneg (mul_nonneg hc2 hCw) (by linarith)
  calc c2 * (Cw * α ^ (-(1 : ℝ)) * (Ci * α) ^ 2 * (1 + Z))
      = (c2 * Cw * (1 + Z)) * (α ^ (-(1 : ℝ)) * (Ci * α) ^ 2) := by ring
    _ ≤ (c2 * Cw * (1 + Z)) * Ci ^ 2 := mul_le_mul_of_nonneg_left hcore hfac
    _ ≤ (4 * Cw * (1 + Z)) * Ci ^ 2 := by
        have h2 : c2 * Cw * (1 + Z) ≤ 4 * Cw * (1 + Z) := by
          have hAE : 0 ≤ Cw * (1 + Z) := mul_nonneg hCw (by linarith)
          calc c2 * Cw * (1 + Z) = c2 * (Cw * (1 + Z)) := by ring
            _ ≤ 4 * (Cw * (1 + Z)) := mul_le_mul_of_nonneg_right hc2le hAE
            _ = 4 * Cw * (1 + Z) := by ring
        exact mul_le_mul_of_nonneg_right h2 (sq_nonneg Ci)
    _ = 4 * (Cw * Ci ^ 2) * (1 + Z) := by ring
    _ ≤ 4 * (Cw * Ci ^ 2) * ((1 + Z) * B) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact le_mul_of_one_le_right (by linarith) hB1

/-- **The generic per-piece estimate.**  For a scalar `c`, a `𝒲^{6,∞}`-coefficient `A` priced by
`KA` and an `ℋ⁶`-factor `P` priced by `SP`, the level-`6` energy of `c·(A·P)` is at most
`c²·Cw·α⁻¹·KA²·(1+SP)`. -/
theorem piece_le {α Cw c KA SP : ℝ} {A P : ℝ → ℝ → ℝ}
    (hwl : ∀ (A' P' : ℝ → ℝ → ℝ) (K : ℝ),
      Work.FTS.EllipticEst.SmoothOpen A' → Work.Spaces.WlInfMem α 6 A' → Work.Spaces.WlInf α 6 A' ≤ K →
      Work.FTS.EllipticEst.SmoothOpen P' → Work.Spaces.HkMem α 6 P' →
      Work.Spaces.HkSq α 6 (fun z θ => A' z θ * P' z θ)
        ≤ Cw * α ^ (-(1 : ℝ)) * K ^ 2 * (1 + Work.Spaces.HkSq α 6 P'))
    (hCw : 0 ≤ Cw) (hα0 : 0 < α)
    (hA : Work.FTS.EllipticEst.SmoothOpen A) (hAm : Work.Spaces.WlInfMem α 6 A)
    (hAb : Work.Spaces.WlInf α 6 A ≤ KA)
    (hP : Work.FTS.EllipticEst.SmoothOpen P) (hPm : Work.Spaces.HkMem α 6 P)
    (hPb : Work.Spaces.HkSq α 6 P ≤ SP) :
    Work.Spaces.HkSq α 6 (fun z θ => c * (A z θ * P z θ))
      ≤ c ^ 2 * (Cw * α ^ (-(1 : ℝ)) * KA ^ 2 * (1 + SP)) := by
  rw [Work.FTS.StrongEps.HkSq_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg c)
  have hWnn : 0 ≤ Work.Spaces.WlInf α 6 A := Work.Spaces.WlInf_nonneg α 6 A hAm
  have hKAnn : 0 ≤ KA := le_trans hWnn hAb
  refine le_trans (hwl A P KA hA hAm hAb hP hPm) ?_
  have hbase : 0 ≤ Cw * α ^ (-(1 : ℝ)) * KA ^ 2 :=
    mul_nonneg (mul_nonneg hCw (Real.rpow_nonneg hα0.le _)) (sq_nonneg KA)
  exact mul_le_mul_of_nonneg_left (by linarith) hbase

