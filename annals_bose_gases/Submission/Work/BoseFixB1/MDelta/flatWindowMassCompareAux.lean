import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.MDelta.massUpper
import Submission.Work.BoseFixB1S.boxM2SubBoxM1GeConvChiMass
import Submission.Work.BoseFixB1S.wSmall1Pair_denom_bounds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
-- import Submission.Work.BoseFixB1.MDelta.chiSmallSlabMass
-- import Submission.Work.BoseFixB1.MDelta.chiSmallSlabSetIntegral
-- import Submission.Work.BoseFixB1.MDelta.chiSmallScaledModulus
-- import Submission.Work.BoseFixB1.MDelta.dlBoxEqCube

/-!
# `Work.BoseFixB1.MDelta.flatWindowMassCompareAux` — the shift bound for `chiSmallB`

The target `Work.BoseFixB1.MDelta.flatWindowMassCompare` is *one* input away from the PROVED
`Work.BoseFixB1S.boxM2SubBoxM1GeConvChiMass`, which turns the **autocorrelation shift
hypothesis** `(S) (1 − θ)·chiMass ≤ ∫ x, χ_B(x)·χ_B(x − z) (‖z‖ ≤ R)` into the mass comparison
`(1 − θ)·g₀ω₀-mass·chiMass ≤ boxM2 − boxM1`.  This file proves (S) from the window-comparison
hypotheses (H1), (H2) of the target and the diluteness `R ≤ ℓd/K`, `K (R/(ℓd))² ≤ θ`, following
the plan in the module docstring of the deliverable file.
-/

noncomputable section
open MeasureTheory Metric Filter
open scoped Real Topology BigOperators ENNReal

namespace Work.BoseFixB1.MDelta

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §1. Elementary facts -/

/-- Young's inequality in the `(1+δ)` shape: `(a+b)² ≤ (1+δ)a² + (1+1/δ)b²`. -/
lemma sq_add_le_young {a b δ : ℝ} (hδ : 0 < δ) :
    (a + b) ^ 2 ≤ (1 + δ) * a ^ 2 + (1 + 1 / δ) * b ^ 2 := by
  have hkey : δ * ((1 + δ) * a ^ 2 + (1 + 1 / δ) * b ^ 2 - (a + b) ^ 2)
      = (δ * a - b) ^ 2 := by
    field_simp
    ring
  have hnn : 0 ≤ δ * ((1 + δ) * a ^ 2 + (1 + 1 / δ) * b ^ 2 - (a + b) ^ 2) := by
    rw [hkey]; exact sq_nonneg _
  have h2 : 0 ≤ (1 + δ) * a ^ 2 + (1 + 1 / δ) * b ^ 2 - (a + b) ^ 2 :=
    (mul_nonneg_iff_of_pos_left hδ).mp hnn
  linarith

/-- `χ_B(x) = χ_ℓ(x)·χ_M((ℓd)⁻¹(x − (ℓd)u))` — the two factors. -/
lemma chiSmallB_factor {M : ℕ} {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (u x : E3) :
    Submission.BoseGases.chiSmallB M ℓ d u x
      = Submission.BoseGases.chiScale ℓ x
        * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • (x - (ℓ * d) • u)) := by
  rw [Submission.BoseGases.chiSmallB]
  congr 1
  rw [smul_sub, smul_smul, inv_mul_cancel₀ (ne_of_gt (mul_pos hℓ hd)), one_smul]

/-- **The cube mass of the scaled cosine bump**: `∫_x χ_M((x−w)/c)² dx = c³`. -/
lemma integral_chiSmall_scale_sq {M : ℕ} (hM : 1 ≤ M) {c : ℝ} (hc : 0 < c) (w : E3) :
    (∫ x : E3, (Submission.BoseGases.chiSmall M (c⁻¹ • (x - w))) ^ 2) = c ^ 3 := by
  have hpt : ∀ y : E3, (Submission.BoseGases.chiSmall M (c⁻¹ • (y + w - w))) ^ 2
      = (Submission.BoseGases.chiSmall M (c⁻¹ • y)) ^ 2 := by
    intro y
    rw [add_sub_cancel_right]
  calc (∫ x : E3, (Submission.BoseGases.chiSmall M (c⁻¹ • (x - w))) ^ 2)
      = ∫ y : E3, (Submission.BoseGases.chiSmall M (c⁻¹ • (y + w - w))) ^ 2 :=
        (integral_add_right_eq_self (μ := (volume : Measure E3))
          (f := fun y : E3 => (Submission.BoseGases.chiSmall M (c⁻¹ • (y - w))) ^ 2) w).symm
    _ = ∫ y : E3, (Submission.BoseGases.chiSmall M (c⁻¹ • y)) ^ 2 :=
        integral_congr_ae (ae_of_all _ hpt)
    _ = c ^ 3 * (∫ s : E3, (Submission.BoseGases.chiSmall M (c⁻¹ • (c • s))) ^ 2) :=
        Submission.BoseGases.integral_comp_smul_right
          (g := fun z : E3 => (Submission.BoseGases.chiSmall M (c⁻¹ • z)) ^ 2) hc
    _ = c ^ 3 * (∫ s : E3, (Submission.BoseGases.chiSmall M s) ^ 2) := by
        congr 1
        refine integral_congr_ae (ae_of_all _ (fun s => ?_))
        show (Submission.BoseGases.chiSmall M (c⁻¹ • (c • s))) ^ 2
          = (Submission.BoseGases.chiSmall M s) ^ 2
        rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hc), one_smul]
    _ = c ^ 3 := by rw [Submission.BoseGases.chiSmall_L2 hM, mul_one]

/-- `χ_ℓ(x) > 0` forces `‖x‖ < ℓ/2`. -/
lemma chiScale_pos_imp_norm_lt {ℓ : ℝ} (hℓ : 0 < ℓ) {x : E3}
    (h : 0 < Submission.BoseGases.chiScale ℓ x) : ‖x‖ < ℓ / 2 := by
  by_contra hc
  rw [not_lt] at hc
  have hhalf : (1 / 2 : ℝ) ≤ ‖(ℓ⁻¹ : ℝ) • x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hℓ)]
    calc (1 / 2 : ℝ) = ℓ⁻¹ * (ℓ / 2) := by field_simp
      _ ≤ ℓ⁻¹ * ‖x‖ := mul_le_mul_of_nonneg_left hc (le_of_lt (inv_pos.mpr hℓ))
  have h0 : Submission.BoseGases.chiScale ℓ x = 0 :=
    Submission.BoseGases.chi_eq_zero_of_half_le_norm _ hhalf
  rw [h0] at h
  exact lt_irrefl 0 h

/-- **The dichotomy of (H1)**: on `B(u)`, either the ball window vanishes identically, or it is
strictly positive everywhere. -/
lemma chiScale_dichotomy {ℓ d θ : ℝ} (hθ : 0 ≤ θ) {u : E3}
    (H1 : ∀ x y : E3, x ∈ Submission.BoseGases.dlBox ℓ d u →
      y ∈ Submission.BoseGases.dlBox ℓ d u →
      Submission.BoseGases.chiScale ℓ y ≤ (1 + θ) * Submission.BoseGases.chiScale ℓ x)
    (hne : ∃ x₀ : E3, x₀ ∈ Submission.BoseGases.dlBox ℓ d u
      ∧ Submission.BoseGases.chiScale ℓ x₀ ≠ 0) :
    ∀ x : E3, x ∈ Submission.BoseGases.dlBox ℓ d u →
      0 < Submission.BoseGases.chiScale ℓ x := by
  obtain ⟨x₀, hx₀, hx₀ne⟩ := hne
  have hx₀pos : 0 < Submission.BoseGases.chiScale ℓ x₀ :=
    lt_of_le_of_ne (Submission.BoseGases.chiScale_nonneg ℓ x₀) (Ne.symm hx₀ne)
  intro x hx
  have h1 : Submission.BoseGases.chiScale ℓ x₀
      ≤ (1 + θ) * Submission.BoseGases.chiScale ℓ x := H1 x x₀ hx hx₀
  by_contra hcon
  rw [not_lt] at hcon
  have hprod : (1 + θ) * Submission.BoseGases.chiScale ℓ x ≤ 0 := by
    have := mul_nonneg (by linarith : (0:ℝ) ≤ 1 + θ)
      (by linarith : (0:ℝ) ≤ -Submission.BoseGases.chiScale ℓ x)
    linarith
  linarith [h1, hx₀pos, hprod]

/-- **The sign-free flatness of the ball window**: on `B(u) ∩ (B(u)+z)`, H1/H2 give
`|χ_ℓ x − χ_ℓ (x−z)| ≤ θ·χ_ℓ x` (for `0 ≤ θ ≤ 1`). -/
lemma chiScale_shift_abs_le {ℓ d R θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) {u : E3}
    (H2 : ∀ z : E3, ‖z‖ ≤ R → ∀ x : E3, x ∈ Submission.BoseGases.dlBox ℓ d u →
      Submission.BoseGases.chiScale ℓ (x - z) ≤ (1 + θ) * Submission.BoseGases.chiScale ℓ x)
    {x z : E3} (hz : ‖z‖ ≤ R)
    (hx : x ∈ Submission.BoseGases.dlBox ℓ d u)
    (hxz : x - z ∈ Submission.BoseGases.dlBox ℓ d u) :
    |Submission.BoseGases.chiScale ℓ x - Submission.BoseGases.chiScale ℓ (x - z)|
      ≤ θ * Submission.BoseGases.chiScale ℓ x := by
  have h1 : Submission.BoseGases.chiScale ℓ (x - z)
      ≤ (1 + θ) * Submission.BoseGases.chiScale ℓ x := H2 z hz x hx
  have h2 : Submission.BoseGases.chiScale ℓ x
      ≤ (1 + θ) * Submission.BoseGases.chiScale ℓ (x - z) := by
    have h := H2 (-z) (by simpa using hz) (x - z) hxz
    simpa using h
  have hxnn : 0 ≤ Submission.BoseGases.chiScale ℓ x := Submission.BoseGases.chiScale_nonneg ℓ x
  rw [abs_le]
  constructor
  · linarith
  · have h3 : Submission.BoseGases.chiScale ℓ x / (1 + θ)
        ≤ Submission.BoseGases.chiScale ℓ (x - z) := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 + θ)]
      linarith
    have h4 : (1 - θ) * Submission.BoseGases.chiScale ℓ x
        ≤ Submission.BoseGases.chiScale ℓ x / (1 + θ) := by
      rw [le_div_iff₀ (by linarith : (0 : ℝ) < 1 + θ)]
      nlinarith [hxnn, hθ1, sq_nonneg θ, mul_nonneg (sq_nonneg θ) hxnn]
    linarith

end Work.BoseFixB1.MDelta
