import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.OneBodyKin.ProfHatDecay
import Submission.Work.OneBodyKin.famSym_Ftrunc_bound
import Submission.Work.OneBodyKin.famSym_Ftrunc_tendsto
import Submission.Work.OneBodyKin.integrable_q_pieces
import Submission.Work.OneBodyKin.kinFT_decay_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.OneBodyKin.SymbolIntegralRhsTendsto` — the right-hand side of the symbol identity
converges along the truncations

The FS cut-off symbol `fsKinCoeff c = [· − c]₊²` (`Submission.BoseGases.fsKinCoeff`) is the
pointwise increasing limit of the truncated symbols `Ftrunc c n` (`TruncDefs.lean`).  The
symbol-integral identity `Work.OneBodyKin.SymbolIntegral ℓ (fsKinCoeff c)` is obtained from the
`L¹` case (`bsFamilyForm_eq_symbolIntegral`) by monotone convergence on *both* sides; this file
supplies the entire right-hand half of that passage, namely

    `(2π)⁻³ ∫_q famSym ℓ (Ftrunc c n) q · ‖kinFT ψ q‖² dq
        ⟶ (2π)⁻³ ∫_q famSym ℓ (fsKinCoeff c) q · ‖kinFT ψ q‖² dq`   as `n → ∞`.

## The argument

Everything is a single application of dominated convergence in `q`, with the three inputs

* **pointwise convergence at each `q`** (`Work.OneBodyKin.famSym_Ftrunc_tendsto`): each of the
  three symbol terms `symA`, `symD`, `symC` is an integral in `p` of `Ftrunc c n` against a fixed
  weight, and `Ftrunc c n ↑ fsKinCoeff c` pointwise, so dominated convergence in `p` (with the
  decay `|profHat p| ≤ C(1+‖p‖)⁻⁶`, `ProfHatDecay`) gives convergence term by term;
* **a uniform-in-`n` polynomial bound** (`Work.OneBodyKin.famSym_Ftrunc_bound`): there are
  `A, B ≥ 0` with `|famSym ℓ (Ftrunc c n) q| ≤ A‖q‖² + B` for all `n` and `q`
  (`Ftrunc c n ≤ fsKinCoeff c` makes the bound `n`-independent; the quadratic growth in `q` is
  that of `symA`);
* **Schwartz decay of the test function** (`Work.OneBodyKin.kinFT_decay_le` for `ψ`, `C^∞` with
  compact support): `‖kinFT ψ q‖ ≤ D(1+‖q‖)⁻⁶`, hence
  `(A‖q‖²+B)‖kinFT ψ q‖² ≤ (A+B)D²(1+‖q‖)⁻¹⁰`, which is integrable in dimension three.

Integrability of each member of the sequence (so that the dominated convergence theorem applies
to honest Bochner integrals, and each member is a.e. strongly measurable) is supplied by
`Work.OneBodyKin.integrable_q_pieces`: for each `n` the three `q`-integrands of the symbol
expansion are `L¹`, and `famSym` is their combination.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.OneBodyKin

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

theorem SymbolIntegralRhsTendsto {ℓ c : ℝ} (hℓ : 0 < ℓ) (ψ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    Filter.Tendsto (fun n : ℕ =>
      ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : EuclideanSpace ℝ (Fin 3),
        Work.OneBodyKin.famSym ℓ (Work.OneBodyKin.Ftrunc c n) q *
          ‖Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) => (ψ z : ℂ)) q‖ ^ 2)
      Filter.atTop
      (nhds (((2 * Real.pi) ^ 3)⁻¹ * ∫ q : EuclideanSpace ℝ (Fin 3),
        Work.OneBodyKin.famSym ℓ (Submission.BoseGases.fsKinCoeff c) q *
          ‖Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) => (ψ z : ℂ)) q‖ ^ 2)) := by
  -- ## 0. the two decay inputs: `profHat` (via `ProfHatDecay`) and `kinFT ψ` (Schwartz)
  obtain ⟨CP, hCP0, hd⟩ := Work.OneBodyKin.ProfHatDecay
  have hψc : ContDiff ℝ (⊤ : ENat) (fun z : ℝ³ => (ψ z : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hψ
  have hcsc : HasCompactSupport (fun z : ℝ³ => (ψ z : ℂ)) :=
    hcs.comp_left (by simp : ((0 : ℝ) : ℂ) = 0)
  obtain ⟨D, _hD0, hDdec⟩ := kinFT_decay_le 6 hψc hcsc
  -- ## 1. the uniform-in-`n` polynomial bound on the truncated symbol
  obtain ⟨A, B, hA0, hB0, hbnd⟩ := famSym_Ftrunc_bound (ℓ := ℓ) (c := c) hℓ hCP0 hd
  -- ## 2. the dominating function `(A+B)D²(1+‖q‖)⁻¹⁰`, and its integrability
  have hone : Integrable (fun q : ℝ³ => (1 + ‖q‖) ^ (-((10:ℕ):ℝ))) := by
    refine integrable_one_add_norm (E := ℝ³) (μ := volume) (r := ((10:ℕ):ℝ)) ?_
    rw [finrank_euclideanSpace_fin]
    norm_num
  have hGint : Integrable (fun q : ℝ³ => (A + B) * D ^ 2 * (1 + ‖q‖) ^ (-((10:ℕ):ℝ))) :=
    hone.const_mul _
  -- ## 3. the pointwise domination of the integrands
  have hbound : ∀ n : ℕ, ∀ᵐ q ∂volume,
      ‖famSym ℓ (Ftrunc c n) q * ‖kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2‖
        ≤ (A + B) * D ^ 2 * (1 + ‖q‖) ^ (-((10:ℕ):ℝ)) := by
    intro n
    refine Eventually.of_forall (fun q => ?_)
    have hpos : (0 : ℝ) < 1 + ‖q‖ := by positivity
    -- the symbol grows at most quadratically in `q`
    have h1 : |famSym ℓ (Ftrunc c n) q| ≤ (A + B) * (1 + ‖q‖) ^ 2 := by
      have hsq : ‖q‖ ^ 2 ≤ (1 + ‖q‖) ^ 2 := by nlinarith [norm_nonneg q]
      have hone2 : (1 : ℝ) ≤ (1 + ‖q‖) ^ 2 := by nlinarith [norm_nonneg q]
      have hA' : A * ‖q‖ ^ 2 ≤ A * (1 + ‖q‖) ^ 2 := mul_le_mul_of_nonneg_left hsq hA0
      have hB' : B ≤ B * (1 + ‖q‖) ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_left hone2 hB0, hB0]
      have hsum : A * (1 + ‖q‖) ^ 2 + B * (1 + ‖q‖) ^ 2 = (A + B) * (1 + ‖q‖) ^ 2 := by ring
      linarith [hbnd n q, hA', hB', hsum]
    -- and the test function decays like `(1+‖q‖)⁻⁶`
    have h2 : ‖kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2
        ≤ D ^ 2 * (1 + ‖q‖) ^ (-((12:ℕ):ℝ)) := by
      calc ‖kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2
          ≤ (D / (1 + ‖q‖) ^ 6) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hDdec q) 2
        _ = D ^ 2 * (1 + ‖q‖) ^ (-((12:ℕ):ℝ)) := by
            rw [div_pow, div_eq_mul_inv, show ((1 + ‖q‖) ^ 6) ^ 2 = (1 + ‖q‖) ^ 12 by ring,
              Real.rpow_neg hpos.le, Real.rpow_natCast]
    have hrw : (1 + ‖q‖) ^ (-((10:ℕ):ℝ))
        = (1 + ‖q‖) ^ 2 * (1 + ‖q‖) ^ (-((12:ℕ):ℝ)) := by
      rw [show (-((10:ℕ):ℝ)) = (2:ℝ) + (-((12:ℕ):ℝ)) by norm_num, Real.rpow_add hpos]
      norm_num
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (sq_nonneg ‖kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖), hrw]
    calc |famSym ℓ (Ftrunc c n) q| * ‖kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2
        ≤ ((A + B) * (1 + ‖q‖) ^ 2) * (D ^ 2 * (1 + ‖q‖) ^ (-((12:ℕ):ℝ))) :=
          mul_le_mul h1 h2 (sq_nonneg _) (by positivity)
      _ = (A + B) * D ^ 2 * ((1 + ‖q‖) ^ 2 * (1 + ‖q‖) ^ (-((12:ℕ):ℝ))) := by ring
  -- ## 4. integrability of each member of the sequence, hence a.e. strong measurability
  have hInt : ∀ n : ℕ, Integrable (fun q : ℝ³ =>
      famSym ℓ (Ftrunc c n) q * ‖kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2) := by
    intro n
    obtain ⟨h1, h2, h3⟩ :=
      integrable_q_pieces hℓ (integrable_Ftrunc c n) (Ftrunc_nonneg c n) ψ hψ hcs
    have key : (fun q : ℝ³ =>
          famSym ℓ (Ftrunc c n) q * ‖kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2)
        = fun q : ℝ³ =>
            symA ℓ (Ftrunc c n) q * ‖kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2
          - (2 * ((2 * Real.pi) ^ 3)⁻¹) *
              (boxHat ℓ q * symD ℓ (Ftrunc c n) q *
                ‖kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2)
          + symC ℓ (Ftrunc c n) q * ‖kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2 := by
      funext q
      simp only [famSym]
      ring
    rw [key]
    exact (h1.sub (h2.const_mul _)).add h3
  -- ## 5. pointwise convergence in `n`, and dominated convergence
  have hlim : ∀ᵐ q ∂volume, Filter.Tendsto
      (fun n : ℕ => famSym ℓ (Ftrunc c n) q * ‖kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2)
      Filter.atTop
      (nhds (famSym ℓ (fsKinCoeff c) q * ‖kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2)) :=
    Eventually.of_forall (fun q => (famSym_Ftrunc_tendsto hℓ hCP0 hd q).mul_const _)
  have hmain := tendsto_integral_of_dominated_convergence
      (F := fun (n : ℕ) (q : ℝ³) =>
        famSym ℓ (Ftrunc c n) q * ‖kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2)
      (f := fun q : ℝ³ =>
        famSym ℓ (fsKinCoeff c) q * ‖kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2)
      (fun q : ℝ³ => (A + B) * D ^ 2 * (1 + ‖q‖) ^ (-((10:ℕ):ℝ)))
      (fun n => (hInt n).aestronglyMeasurable) hGint hbound hlim
  simpa only [Pi.smul_apply, smul_eq_mul] using hmain.const_mul (((2 * Real.pi) ^ 3)⁻¹)

end Work.OneBodyKin
