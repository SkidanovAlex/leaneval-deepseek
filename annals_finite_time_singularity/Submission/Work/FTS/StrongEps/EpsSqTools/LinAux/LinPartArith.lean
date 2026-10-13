/-
# `LinAux/LinPartArith.lean` — the three stand-alone pieces of `EpsSq_LinPart_le`

Kept out of the target file (which has to stay under the elaboration size limit):

* `smoothOpen_Pz` — the projection `P₀` of a `SmoothOpen` profile is `SmoothOpen`;
* `gam_int_mul_le` — the numerical bound `G · P ≤ 32000 · BB¹²DE/α` for the angular–
  radial product coming from the `Γ`-block;
* `linPart_final_const_le` — the final constant bookkeeping
  `10⁵ · BB¹²DE/α ≤ BigC (BigC/(α²ε))² E` for `BigC = max 1 (10⁵ B¹²)`.

Everything below is `sorry`-free.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.StrongPersist.Vocab
import Submission.Work.FTS.StrongEps.BumpDefs
import Submission.Work.FTS.StrongEps.PZero
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.SmoothOpenAdd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsSqTools.LinAux

set_option autoImplicit false

/-! ## The projection of a smooth profile -/

/-- `P₀ f = f − (L₁₂ f 0 / pzNorm) • bump` is smooth whenever `f` is. -/
theorem smoothOpen_Pz {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.Pz f) := by
  have h2 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm)
        * Work.FTS.StrongEps.bump z θ) :=
    Work.FTS.EllipticEst.SmoothOpen.const_mul'
      (Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm)
      Work.FTS.StrongEps.smoothOpen_bump
  have h3 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => f z θ - (Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm)
        * Work.FTS.StrongEps.bump z θ) :=
    Work.FTS.EllipticEst.smoothOpen_sub hf h2
  refine (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mpr fun n => ?_
  have h4 : ∀ n : ℕ, ContDiffOn ℝ n
      (Function.uncurry (fun z θ => f z θ
        - (Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm)
          * Work.FTS.StrongEps.bump z θ)) Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp h3
  have hun : Function.uncurry (Work.FTS.StrongEps.Pz f)
      = Function.uncurry (fun z θ => f z θ
        - (Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm)
          * Work.FTS.StrongEps.bump z θ) := by
    funext p
    rcases p with ⟨z, θ⟩
    exact Work.FTS.StrongEps.Pz_apply f z θ
  rw [hun]
  exact h4 n

/-! ## The angular–radial product -/

/-- **The `Γ`-block contribution.**  With `A₁ ≤ 4 BB⁹DE`, `A₄ ≤ 36 BB⁹DE`, `CL, C12 ≤ BB`,
`G ≤ BB/α` and `P ≤ 800 (CL A₁ + C12² A₄)`, the product is bounded by `32000 BB¹²DE/α`. -/
theorem gam_int_mul_le {α BB D E G P CL C12 A1 A4 : ℝ}
    (hα0 : 0 < α) (hBB1 : 1 ≤ BB) (hDnn : 0 ≤ D) (hE0 : 0 ≤ E)
    (hA1nn : 0 ≤ A1) (hA1 : A1 ≤ 4 * (BB ^ 9 * D * E))
    (hA40 : 0 ≤ A4) (hA4 : A4 ≤ 36 * (BB ^ 9 * D * E))
    (hP0 : 0 ≤ P) (hP : P ≤ 800 * (CL * A1 + C12 ^ 2 * A4))
    (hCL : CL ≤ BB) (hC12 : C12 ≤ BB) (hCL0 : 0 ≤ CL) (hC120 : 0 ≤ C12)
    (hG : G ≤ BB / α) :
    G * P ≤ 32000 * (BB ^ 12 * D * E / α) := by
  have hBB0 : 0 ≤ BB := le_trans zero_le_one hBB1
  have hde0 : (0 : ℝ) ≤ D * E := mul_nonneg hDnn hE0
  have hP9 : (0 : ℝ) ≤ BB ^ 9 * D * E :=
    mul_nonneg (mul_nonneg (pow_nonneg hBB0 9) hDnn) hE0
  have hP11 : (0 : ℝ) ≤ BB ^ 11 * D * E :=
    mul_nonneg (mul_nonneg (pow_nonneg hBB0 11) hDnn) hE0
  -- the bound on `∫ Ψ`
  have hC1 : CL * A1 ≤ BB * (4 * (BB ^ 9 * D * E)) :=
    mul_le_mul hCL hA1 hA1nn hBB0
  have hC2 : C12 ^ 2 * A4 ≤ BB ^ 2 * (36 * (BB ^ 9 * D * E)) :=
    mul_le_mul (pow_le_pow_left₀ hC120 hC12 2) hA4 hA40 (by positivity)
  have hB10 : BB ^ 10 ≤ BB ^ 11 := pow_le_pow_right₀ hBB1 (by norm_num)
  have hC1' : CL * A1 ≤ 4 * (BB ^ 10 * D * E) := by
    have h : BB * (4 * (BB ^ 9 * D * E)) = 4 * (BB ^ 10 * D * E) := by ring
    linarith [hC1, h]
  have hC2' : C12 ^ 2 * A4 ≤ 36 * (BB ^ 11 * D * E) := by
    have h : BB ^ 2 * (36 * (BB ^ 9 * D * E)) = 36 * (BB ^ 11 * D * E) := by ring
    linarith [hC2, h]
  have h4le : 4 * (BB ^ 10 * D * E) ≤ 4 * (BB ^ 11 * D * E) := by
    have h1 : BB ^ 10 * (D * E) ≤ BB ^ 11 * (D * E) :=
      mul_le_mul_of_nonneg_right hB10 hde0
    have h2 : BB ^ 10 * D * E ≤ BB ^ 11 * D * E := by linarith [h1]
    linarith [h2]
  have hsum : CL * A1 + C12 ^ 2 * A4 ≤ 40 * (BB ^ 11 * D * E) := by
    linarith [hC1', hC2', h4le]
  have hPle : P ≤ 32000 * (BB ^ 11 * D * E) := by
    calc P ≤ 800 * (CL * A1 + C12 ^ 2 * A4) := hP
      _ ≤ 800 * (40 * (BB ^ 11 * D * E)) := mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ = 32000 * (BB ^ 11 * D * E) := by ring
  have h1 : G * P ≤ (BB / α) * (32000 * (BB ^ 11 * D * E)) :=
    mul_le_mul hG hPle hP0 (by positivity)
  calc G * P ≤ (BB / α) * (32000 * (BB ^ 11 * D * E)) := h1
    _ = 32000 * (BB ^ 12 * D * E / α) := by ring

/-! ## The final constant -/

/-- **The final constant bookkeeping.**  For `BB = B ≥ 1`, `D = 1/(α²ε²)` and
`C = max 1 (10⁵ B¹²)`, `10⁵ · BB¹²DE/α ≤ C (C/(α²ε))² E`. -/
theorem linPart_final_const_le {α ε BB D E B : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hε0 : 0 < ε)
    (hBB1 : 1 ≤ BB) (hDnn : 0 ≤ D) (hE0 : 0 ≤ E)
    (hDdef : D = 1 / (α ^ 2 * ε ^ 2)) (hBeq : BB = B) (hB1 : 1 ≤ B) :
    100000 * (BB ^ 12 * D * E / α)
      ≤ max 1 (100000 * B ^ 12) * (max 1 (100000 * B ^ 12) / (α ^ 2 * ε)) ^ 2 * E := by
  have hαne : α ≠ 0 := ne_of_gt hα0
  have hεne : ε ≠ 0 := ne_of_gt hε0
  have hM : 100000 * BB ^ 12 ≤ max 1 (100000 * B ^ 12) := by
    rw [hBeq]
    exact le_max_right _ _
  have hCn : (1 : ℝ) ≤ max 1 (100000 * B ^ 12) := le_max_left _ _
  have hCpos : (0 : ℝ) < max 1 (100000 * B ^ 12) := lt_of_lt_of_le zero_lt_one hCn
  have hCn2 : α ≤ (max 1 (100000 * B ^ 12)) ^ 2 := by
    have h2 : (1 : ℝ) ≤ (max 1 (100000 * B ^ 12)) ^ 2 := by nlinarith [hCn]
    linarith [hα1, h2]
  have hde0 : (0 : ℝ) ≤ D * E := mul_nonneg hDnn hE0
  have harg : 100000 * BB ^ 12 * D * E / α
      ≤ (max 1 (100000 * B ^ 12)) ^ 3 * D * E / α ^ 2 := by
    have hcube : 100000 * BB ^ 12 * α ≤ (max 1 (100000 * B ^ 12)) ^ 3 := by
      have hαM : 100000 * BB ^ 12 * α ≤ max 1 (100000 * B ^ 12) := by
        have h1 : 100000 * BB ^ 12 * α ≤ 100000 * BB ^ 12 * 1 :=
          mul_le_mul_of_nonneg_left hα1 (by positivity)
        linarith [h1, hM]
      have h2 : max 1 (100000 * B ^ 12) ≤ (max 1 (100000 * B ^ 12)) ^ 3 := by
        nlinarith [hCn, hCpos]
      linarith [hαM, h2]
    have h12 : 100000 * BB ^ 12 * D * E * α ≤ (max 1 (100000 * B ^ 12)) ^ 3 * D * E := by
      calc 100000 * BB ^ 12 * D * E * α
          = (100000 * BB ^ 12 * α) * (D * E) := by ring
        _ ≤ (max 1 (100000 * B ^ 12)) ^ 3 * (D * E) :=
            mul_le_mul_of_nonneg_right hcube hde0
        _ = (max 1 (100000 * B ^ 12)) ^ 3 * D * E := by ring
    calc 100000 * BB ^ 12 * D * E / α
        = 100000 * BB ^ 12 * D * E * α / α ^ 2 := by
          field_simp
      _ ≤ (max 1 (100000 * B ^ 12)) ^ 3 * D * E / α ^ 2 :=
          div_le_div_of_nonneg_right h12 (by positivity)
  have hfirst : 100000 * (BB ^ 12 * D * E / α) = 100000 * BB ^ 12 * D * E / α := by ring
  have hlast : (max 1 (100000 * B ^ 12)) ^ 3 * D * E / α ^ 2
      = max 1 (100000 * B ^ 12)
        * (max 1 (100000 * B ^ 12) / (α ^ 2 * ε)) ^ 2 * E := by
    rw [hDdef]
    field_simp
  rw [hfirst]
  rw [← hlast]
  exact harg

end Work.FTS.StrongEps.EpsSqTools.LinAux
