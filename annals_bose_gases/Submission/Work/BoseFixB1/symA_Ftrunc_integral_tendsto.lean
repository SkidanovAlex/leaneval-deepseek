import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1.symA_Ftrunc_pt
import Submission.Work.BoseFixB1.symA_Ftrunc_quad_bound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1

noncomputable section

open MeasureTheory Filter

open Work.OneBodyKin (symA Ftrunc integrable_Ftrunc Ftrunc_nonneg integrable_q_pieces)
open Submission.BoseGases (kinFT fsKinCoeff)
open scoped Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 800000

/-- The `q`-integral of the unprojected family symbol `symA ℓ (Ftrunc c n) q · ‖kinFT ψ q‖²` converges, as the radial truncation `Ftrunc c n ↑ fsKinCoeff c` increases, to the integral at the full FS cut-off `fsKinCoeff c`.  Proved by dominated convergence in `q`: pointwise convergence `symA ℓ (Ftrunc c n) q → symA ℓ (fsKinCoeff c) q` (dominated convergence in `p`, bound from `ProfHatDecay`), a uniform-in-`n` polynomial bound `|symA ℓ (Ftrunc c n) q| ≤ A‖q‖² + B`, and the Schwartz decay `‖kinFT ψ q‖ ≤ D(1+‖q‖)^{-6}`.  Mirrors `Work.OneBodyKin.SymbolIntegralRhsTendsto` (`famSym` → `symA`). -/
theorem symA_Ftrunc_integral_tendsto {ℓ c : ℝ} (hℓ : 0 < ℓ)
    {ψ : EuclideanSpace ℝ (Fin 3) → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    (hcs : HasCompactSupport ψ) :
    Filter.Tendsto (fun n : ℕ => ∫ q : EuclideanSpace ℝ (Fin 3),
        Work.OneBodyKin.symA ℓ (Work.OneBodyKin.Ftrunc c n) q *
          ‖Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) => (ψ z : ℂ)) q‖ ^ 2)
      Filter.atTop
      (nhds (∫ q : EuclideanSpace ℝ (Fin 3),
        Work.OneBodyKin.symA ℓ (Submission.BoseGases.fsKinCoeff c) q *
          ‖Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) => (ψ z : ℂ)) q‖ ^ 2)) := by
  -- ## 0. Schwartz decay of the test function
  obtain ⟨D, _hD0, hDdec⟩ :=
    Work.OneBodyKin.kinFT_decay_le 6 (Complex.ofRealCLM.contDiff.comp hψ)
      (hcs.comp_left (by simp : ((0 : ℝ) : ℂ) = 0))
  -- ## 1. the uniform-in-`n` quadratic bound on the truncated symbol
  obtain ⟨A, B, hA0, hB0, hbnd⟩ := symA_Ftrunc_quad_bound (ℓ := ℓ) (c := c) hℓ
  -- ## 2. the dominating function `(A+B)D²(1+‖q‖)⁻¹⁰`, and its integrability
  have hone : Integrable (fun q : ℝ³ => (1 + ‖q‖) ^ (-((10 : ℕ) : ℝ))) := by
    refine integrable_one_add_norm (E := ℝ³) (μ := volume) (r := ((10 : ℕ) : ℝ)) ?_
    rw [finrank_euclideanSpace_fin]
    norm_num
  have hGint : Integrable (fun q : ℝ³ => (A + B) * D ^ 2 * (1 + ‖q‖) ^ (-((10 : ℕ) : ℝ))) :=
    hone.const_mul _
  -- ## 3. the pointwise domination of the integrands
  have hbound : ∀ n : ℕ, ∀ᵐ q ∂volume,
      ‖symA ℓ (Ftrunc c n) q *
          ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2‖
        ≤ (A + B) * D ^ 2 * (1 + ‖q‖) ^ (-((10 : ℕ) : ℝ)) := by
    intro n
    refine Eventually.of_forall (fun q => ?_)
    have hpos : (0 : ℝ) < 1 + ‖q‖ := by positivity
    -- the symbol grows at most quadratically in `q`
    have h1 : |symA ℓ (Ftrunc c n) q| ≤ (A + B) * (1 + ‖q‖) ^ 2 := by
      have hsq : ‖q‖ ^ 2 ≤ (1 + ‖q‖) ^ 2 := by nlinarith [norm_nonneg q]
      have hone2 : (1 : ℝ) ≤ (1 + ‖q‖) ^ 2 := by nlinarith [norm_nonneg q]
      have hA' : A * ‖q‖ ^ 2 ≤ A * (1 + ‖q‖) ^ 2 := mul_le_mul_of_nonneg_left hsq hA0
      have hB' : B ≤ B * (1 + ‖q‖) ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_left hone2 hB0, hB0]
      have hsum : A * (1 + ‖q‖) ^ 2 + B * (1 + ‖q‖) ^ 2 = (A + B) * (1 + ‖q‖) ^ 2 := by ring
      linarith [hbnd n q, hA', hB', hsum]
    -- and the test function decays like `(1+‖q‖)⁻⁶`
    have h2 : ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2
        ≤ D ^ 2 * (1 + ‖q‖) ^ (-((12 : ℕ) : ℝ)) := by
      calc ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2
          ≤ (D / (1 + ‖q‖) ^ 6) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hDdec q) 2
        _ = D ^ 2 * (1 + ‖q‖) ^ (-((12 : ℕ) : ℝ)) := by
            rw [div_pow, div_eq_mul_inv, show ((1 + ‖q‖) ^ 6) ^ 2 = (1 + ‖q‖) ^ 12 by ring,
              Real.rpow_neg hpos.le, Real.rpow_natCast]
    have hrw : (1 + ‖q‖) ^ (-((10 : ℕ) : ℝ))
        = (1 + ‖q‖) ^ 2 * (1 + ‖q‖) ^ (-((12 : ℕ) : ℝ)) := by
      rw [show (-((10 : ℕ) : ℝ)) = (2 : ℝ) + (-((12 : ℕ) : ℝ)) by norm_num, Real.rpow_add hpos]
      norm_num
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (sq_nonneg ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖), hrw]
    calc |symA ℓ (Ftrunc c n) q| * ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2
        ≤ ((A + B) * (1 + ‖q‖) ^ 2) * (D ^ 2 * (1 + ‖q‖) ^ (-((12 : ℕ) : ℝ))) :=
          mul_le_mul h1 h2 (sq_nonneg _) (by positivity)
      _ = (A + B) * D ^ 2 * ((1 + ‖q‖) ^ 2 * (1 + ‖q‖) ^ (-((12 : ℕ) : ℝ))) := by ring
  -- ## 4. integrability of each member of the sequence, hence a.e. strong measurability
  have hInt : ∀ n : ℕ, Integrable (fun q : ℝ³ =>
      symA ℓ (Ftrunc c n) q *
        ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2) := fun n =>
    (integrable_q_pieces hℓ (integrable_Ftrunc c n) (Ftrunc_nonneg c n) ψ hψ hcs).1
  -- ## 5. pointwise convergence in `n`, and dominated convergence
  have hlim : ∀ᵐ q ∂volume, Filter.Tendsto
      (fun n : ℕ => symA ℓ (Ftrunc c n) q *
        ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2)
      Filter.atTop
      (nhds (symA ℓ (fsKinCoeff c) q *
        ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2)) :=
    Eventually.of_forall (fun q => (symA_Ftrunc_pt hℓ q).mul_const _)
  exact tendsto_integral_of_dominated_convergence _
    (fun n => (hInt n).aestronglyMeasurable) hGint hbound hlim

end

end Work.BoseFixB1
