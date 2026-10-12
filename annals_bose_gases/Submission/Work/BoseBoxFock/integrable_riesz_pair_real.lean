import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.SqrtKin.riesz_pair_integrable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.integrable_riesz_pair_real`

The Riesz pair integrand `(x,y) ↦ ‖x − y‖⁻⁴ (F x − F y)²` of a **real** smooth compactly
supported function `F : ℝ³ → ℝ` is integrable for the product of Lebesgue measures on
`ℝ³ × ℝ³`.

Mathlib (and the corpus) only provide the `ℂ`-valued version
(`Submission.Work.BoseBoxFock.SqrtKin.riesz_pair_integrable`); the real version is what the
Cauchy–Schwarz assembly of `flatnessMass_sq_le_kinFirst` needs (it is the integrability
obligation for `F = √K·(f∘π₁ − f∘π₂)` with real `f`, see
`FINDING_flatnessChain_state.md` §3).  The proof transfers through the `ℂ`-lift
`x ↦ (F x : ℂ)`: this preserves the support (`(r : ℂ) = 0 ↔ r = 0`), and the norm of the lifted
difference is the absolute value of the real difference, so squaring removes the `|·|`.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The norm bookkeeping: the squared norm of the lifted difference is the square of the real
difference (padding by `|·|² = ·²`). -/
lemma norm_sq_ofReal_sub (a b : ℝ) : ‖((a : ℂ) - (b : ℂ))‖ ^ 2 = (a - b) ^ 2 := by
  have h : ((a : ℂ) - (b : ℂ)) = ((a - b : ℝ) : ℂ) := by push_cast; ring
  rw [h, Complex.sq_norm, Complex.normSq_ofReal]; ring

/-- **The Riesz pair integrand of a real smooth compactly supported function is product-measure
integrable.** -/
theorem integrable_riesz_pair_real {F : ℝ³ → ℝ} (hF : ContDiff ℝ (⊤ : ENat) F)
    (hc : HasCompactSupport F) :
    Integrable (fun p : ℝ³ × ℝ³ => ‖p.1 - p.2‖ ^ (-(4 : ℝ)) * (F p.1 - F p.2) ^ 2)
      (volume.prod volume) := by
  have hcC : HasCompactSupport (fun x : ℝ³ => (F x : ℂ)) := by
    refine HasCompactSupport.of_support_subset_isCompact hc.isCompact ?_
    intro x hx
    exact subset_tsupport F (by simpa [Function.mem_support] using hx)
  have h := SqrtKin.riesz_pair_integrable (g := fun x : ℝ³ => (F x : ℂ))
    (Complex.ofRealCLM.contDiff.comp hF) hcC
  have heq : (fun p : ℝ³ × ℝ³ => ‖p.1 - p.2‖ ^ (-(4 : ℝ)) * ‖(F p.1 : ℂ) - (F p.2 : ℂ)‖ ^ 2)
      = fun p : ℝ³ × ℝ³ => ‖p.1 - p.2‖ ^ (-(4 : ℝ)) * (F p.1 - F p.2) ^ 2 := by
    funext p
    rw [norm_sq_ofReal_sub]
  rwa [heq] at h

end Work.BoseBoxFock
