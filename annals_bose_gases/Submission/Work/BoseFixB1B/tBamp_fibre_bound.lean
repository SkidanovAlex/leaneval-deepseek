import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxBridge.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The fibre amplitude bound `‖kinFT (χ·Φ(kcInsN i (·,r))) p‖ ≤ |B|·∫‖χ‖`

The windowed `p`-mode of the `i`-th fibre of a state `Φ` that is bounded by `B` on the
box `abox (n+1) a`: the trivial `L¹`-bound for the `p`-convention Fourier transform
`kinFT u p = ∫_y e^{−i⟪p,y⟫}u(y)dy`, with the state bound supplied by `hB` and the
support of `χ` confined to `acube a` so that the reassembled configuration
`kcInsN n i (y,r)` stays in `abox (n+1) a` whenever `χ y ≠ 0`.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixB1B

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 800000

theorem tBamp_fibre_bound {n : ℕ} {a B : ℝ} (ha : 0 < a) {χ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hχ : Continuous χ) (hχsupp : ∀ z : EuclideanSpace ℝ (Fin 3), z ∉ Submission.BoseGases.acube a → χ z = 0)
    {Φ : Submission.BoseGases.X (n + 1) → ℝ}
    (hB : ∀ x ∈ Submission.BoseGases.abox (n + 1) a, |Φ x| ≤ B) (i : Fin (n + 1)) :
    ∀ r ∈ Submission.BoseGases.abox n a, ∀ p : EuclideanSpace ℝ (Fin 3),
      ‖Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) =>
          (χ z : ℂ) * (Φ (Submission.BoseGases.kcInsN n i (z, r)) : ℂ)) p‖
        ≤ |B| * ∫ z : EuclideanSpace ℝ (Fin 3), ‖χ z‖ := by
  -- χ is continuous with support in the compact cube `acube a`, hence integrable
  have hsupp : Function.support χ ⊆ Submission.BoseGases.acube a := by
    intro z hz
    by_contra hz'
    exact hz (hχsupp z hz')
  have hcs : HasCompactSupport χ :=
    HasCompactSupport.of_support_subset_isCompact (Submission.BoseGases.acube_compact ha) hsupp
  have hint : Integrable χ := hχ.integrable_of_hasCompactSupport hcs
  have hintn : Integrable (fun z : ℝ³ => ‖χ z‖) := hint.norm
  have hintB : Integrable (fun z : ℝ³ => |B| * ‖χ z‖) := hintn.const_mul |B|
  intro r hr p
  -- the reassembled configuration lands in the box
  have hmem : ∀ z : ℝ³, z ∈ Submission.BoseGases.acube a →
      Submission.BoseGases.kcInsN n i (z, r) ∈ Submission.BoseGases.abox (n + 1) a := by
    intro z hz j
    by_cases hj : j = i
    · rw [hj, Submission.BoseGases.kc_insN_apply_same]
      exact hz
    · rcases Fin.exists_succAbove_eq hj with ⟨j', rfl⟩
      rw [Submission.BoseGases.kc_insN_apply_succ]
      exact hr j'
  -- the pointwise bound on the integrand
  have hpt : ∀ z : ℝ³, ‖(χ z : ℂ) * (Φ (Submission.BoseGases.kcInsN n i (z, r)) : ℂ)‖
      ≤ |B| * ‖χ z‖ := by
    intro z
    by_cases hz : z ∈ Submission.BoseGases.acube a
    · have hΦ : |Φ (Submission.BoseGases.kcInsN n i (z, r))| ≤ |B| :=
        le_trans (hB _ (hmem z hz)) (le_abs_self B)
      calc ‖(χ z : ℂ) * (Φ (Submission.BoseGases.kcInsN n i (z, r)) : ℂ)‖
          = |χ z| * |Φ (Submission.BoseGases.kcInsN n i (z, r))| := by
            rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
              Real.norm_eq_abs]
        _ ≤ |χ z| * |B| := mul_le_mul_of_nonneg_left hΦ (abs_nonneg _)
        _ = |B| * ‖χ z‖ := by rw [Real.norm_eq_abs, mul_comm]
    · rw [hχsupp z hz]
      simp
  -- the phase has modulus one
  have hexp : ∀ z : ℝ³, ‖Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))‖ = 1 := by
    intro z
    have hrew : -(Complex.I * ((inner ℝ p z : ℝ) : ℂ))
        = ((-(inner ℝ p z) : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [hrew, Complex.norm_exp_ofReal_mul_I]
  calc ‖Submission.BoseGases.kinFT (fun z : ℝ³ =>
        (χ z : ℂ) * (Φ (Submission.BoseGases.kcInsN n i (z, r)) : ℂ)) p‖
      = ‖∫ z : ℝ³, Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
          ((χ z : ℂ) * (Φ (Submission.BoseGases.kcInsN n i (z, r)) : ℂ))‖ := by
        rw [Submission.BoseGases.kinFT]
    _ ≤ ∫ z : ℝ³, ‖Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
          ((χ z : ℂ) * (Φ (Submission.BoseGases.kcInsN n i (z, r)) : ℂ))‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ z : ℝ³, ‖(χ z : ℂ) * (Φ (Submission.BoseGases.kcInsN n i (z, r)) : ℂ)‖ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only [norm_mul, hexp z, one_mul]
    _ ≤ ∫ z : ℝ³, |B| * ‖χ z‖ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => norm_nonneg _) hintB
          (Filter.Eventually.of_forall hpt)
    _ = |B| * ∫ z : ℝ³, ‖χ z‖ := integral_const_mul _ _

end Work.BoseFixB1B
