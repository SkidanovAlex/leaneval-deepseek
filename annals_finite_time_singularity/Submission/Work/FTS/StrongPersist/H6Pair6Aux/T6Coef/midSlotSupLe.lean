import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.TransportS.sup_dz_le_hk
import Submission.Work.FTS.TransportS.T2SupB2.mixed_pointwise_le_Xn
import Submission.Work.FTS.StrongPersist.N6.PwOpen6
import Submission.Work.FTS.OpenPkg.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef

/-- **The middle-slot sup bound.**  For a datum `f` which is `C^∞` on the open quadrant and
honestly in `ℋ⁶`, and for indices with `a₁ ≤ a`, `b₁ ≤ b`, `3 ≤ a₁ + b₁`, `a + b ≤ 6`, the
left-over slot `D_z^{b-b₁} D_θ^{a-a₁} f` — of total order `≤ 3` — is bounded pointwise on the
open quadrant by `C α^{-1/2}` times `(1 + M)` when its order is `≤ 2` (with `M` an a-priori
bound for the `ℋ⁴`-norm of `f`) and by `C α^{-1/2}` times the `ℋ⁶`-norm of `f` when its order
is exactly `3`.

The three ingredients are the pointwise bounds available at the two levels:
`Work.FTS.TransportS.T2SupB2.mixed_pointwise_le_Xn` (α-uniform for the genuinely mixed slots of
order `≤ 2`), `Work.FTS.TransportS.sup_dz_le_hk` (the pure `D_z`-slots of order `≤ 2`, with the
`(γ-1)^{-1/2} = √10 · α^{-1/2}` loss) and `Work.FTS.StrongPersist.N6.PwAny6` (all slots of
order `≤ 4` against the `ℋ⁶`-norm, again with the `α^{-1/2}` loss). -/
theorem midSlotSupLe :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ) (a b a₁ b₁ : ℕ) (M : ℝ),
      α ∈ Set.Ioc 0 1 → Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      Work.FTS.Nonlin.Xn α f ≤ M →
      a₁ ≤ a → b₁ ≤ b → 3 ≤ a₁ + b₁ → a + b ≤ 6 →
      (((a - a₁) + (b - b₁) ≤ 2) →
          ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
            |Work.Spaces.mixed (b - b₁) (a - a₁) f z θ|
              ≤ C * α ^ (-(1 / 2 : ℝ)) * (1 + M)) ∧
      (((a - a₁) + (b - b₁) = 3) →
          ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
            |Work.Spaces.mixed (b - b₁) (a - a₁) f z θ|
              ≤ C * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f) := by
  obtain ⟨C1, hC1pos, hC1⟩ := Work.FTS.TransportS.sup_dz_le_hk
  obtain ⟨C2, hC2pos, hC2⟩ := Work.FTS.TransportS.T2SupB2.mixed_pointwise_le_Xn
  obtain ⟨C3, hC3pos, hC3⟩ := Work.FTS.StrongPersist.N6.PwAny6
  refine ⟨100 * (C1 + C2 + C3 + 1), by positivity, ?_⟩
  intro α f a b a₁ b₁ M hα hF hmem6 hbdd ha₁ hb₁ h3 hab
  set p : ℝ := α ^ (-(1 / 2 : ℝ)) with hpdef
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have h4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hF 4 (by norm_num) hmem6
  have hXn0 : 0 ≤ Work.FTS.Nonlin.Xn α f := Work.Spaces.HkNorm_nonneg α 4 f
  -- the two square-root rewrites making the `α^{-1/2}` explicit
  have hp_sqrt : p = (Real.sqrt α)⁻¹ := by
    rw [hpdef, Real.rpow_neg hα0.le, Real.sqrt_eq_rpow]
  have hp1 : 1 ≤ p := by
    rw [hp_sqrt]
    exact (one_le_inv₀ (Real.sqrt_pos.mpr hα0)).mpr (Real.sqrt_le_one.mpr hα1)
  have hp0 : 0 ≤ p := le_trans zero_le_one hp1
  have hgam : Work.Spaces.gam α - 1 = α / 10 := Work.Spaces.gam_sub_one α
  have hroot : Real.sqrt (Work.Spaces.gam α - 1) = Real.sqrt α / Real.sqrt 10 := by
    rw [hgam, Real.sqrt_div hα0.le]
  have hrootinv : (Real.sqrt (Work.Spaces.gam α - 1))⁻¹ = Real.sqrt 10 * p := by
    rw [hroot, inv_div, div_eq_mul_inv, ← hp_sqrt]
  have hroot3 : Real.sqrt (C3 / (Work.Spaces.gam α - 1)) = Real.sqrt (10 * C3) * p := by
    have h10 : C3 / (Work.Spaces.gam α - 1) = (10 * C3) / α := by rw [hgam]; ring
    rw [h10, Real.sqrt_div (mul_nonneg (by norm_num) hC3pos.le), div_eq_mul_inv, ← hp_sqrt]
  -- the size of the constant
  have hC2le : C2 ≤ 100 * (C1 + C2 + C3 + 1) := by nlinarith
  have hC1le : Real.sqrt 10 * C1 ≤ 100 * (C1 + C2 + C3 + 1) := by
    have hs : Real.sqrt 10 ≤ 4 := by rw [Real.sqrt_le_iff]; norm_num
    nlinarith
  have hC3le : Real.sqrt (10 * C3) ≤ 100 * (C1 + C2 + C3 + 1) := by
    have hle : Real.sqrt (10 * C3) ≤ 10 * C3 + 1 := by
      rw [Real.sqrt_le_iff]
      exact ⟨by positivity, by nlinarith [sq_nonneg (10 * C3)]⟩
    nlinarith
  have hK0 : 0 ≤ 100 * (C1 + C2 + C3 + 1) := by positivity
  have hKp0 : 0 ≤ 100 * (C1 + C2 + C3 + 1) * p := mul_nonneg hK0 hp0
  have hX1 : Work.FTS.Nonlin.Xn α f ≤ 1 + M := le_trans hbdd (by linarith)
  constructor
  · -- the order-`≤ 2` slots
    intro hle z θ hz hθ hθ2
    rcases Nat.eq_zero_or_pos (a - a₁) with hi | hi
    · -- the pure radial slot `D_z^{b-b₁}`
      have hb : b - b₁ ≤ 2 := by omega
      have heq : Work.Spaces.mixed (b - b₁) (a - a₁) f = Work.Spaces.DzIter (b - b₁) f := by
        rw [hi, Work.Spaces.mixed_zero_right]
      have h := hC1 α f hα0 hα1 hF h4 (b - b₁) hb z θ hz hθ hθ2
      rw [heq]
      have hfin : C1 / Real.sqrt (Work.Spaces.gam α - 1) ≤ Real.sqrt 10 * C1 * p :=
        le_of_eq (by rw [div_eq_mul_inv, hrootinv]; ring)
      calc |Work.Spaces.DzIter (b - b₁) f z θ|
          ≤ C1 / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α f := h
        _ ≤ Real.sqrt 10 * C1 * p * Work.FTS.Nonlin.Xn α f :=
              mul_le_mul_of_nonneg_right hfin hXn0
        _ ≤ 100 * (C1 + C2 + C3 + 1) * p * (1 + M) := by
              have h1 : Real.sqrt 10 * C1 * p * Work.FTS.Nonlin.Xn α f
                  ≤ 100 * (C1 + C2 + C3 + 1) * p * Work.FTS.Nonlin.Xn α f :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC1le hp0) hXn0
              have h2 : 100 * (C1 + C2 + C3 + 1) * p * Work.FTS.Nonlin.Xn α f
                  ≤ 100 * (C1 + C2 + C3 + 1) * p * (1 + M) :=
                mul_le_mul_of_nonneg_left hX1 hKp0
              linarith
    · -- a genuine mixed slot
      have hi1 : 1 ≤ a - a₁ := by omega
      have h := hC2 α f hα0 hα1 hF h4 (b - b₁) (a - a₁) hi1 hle z θ hz hθ hθ2
      calc |Work.Spaces.mixed (b - b₁) (a - a₁) f z θ|
          ≤ C2 * Work.FTS.Nonlin.Xn α f := h
        _ ≤ 100 * (C1 + C2 + C3 + 1) * p * (1 + M) := by
              have h1 : C2 * Work.FTS.Nonlin.Xn α f
                  ≤ 100 * (C1 + C2 + C3 + 1) * Work.FTS.Nonlin.Xn α f :=
                mul_le_mul_of_nonneg_right hC2le hXn0
              have hstep : Work.FTS.Nonlin.Xn α f ≤ p * (1 + M) := by
                have a1 : Work.FTS.Nonlin.Xn α f ≤ p * Work.FTS.Nonlin.Xn α f := by
                  simpa using mul_le_mul_of_nonneg_right hp1 hXn0
                exact le_trans a1 (mul_le_mul_of_nonneg_left hX1 hp0)
              have h2 : 100 * (C1 + C2 + C3 + 1) * Work.FTS.Nonlin.Xn α f
                  ≤ 100 * (C1 + C2 + C3 + 1) * p * (1 + M) := by
                calc 100 * (C1 + C2 + C3 + 1) * Work.FTS.Nonlin.Xn α f
                    ≤ 100 * (C1 + C2 + C3 + 1) * (p * (1 + M)) :=
                      mul_le_mul_of_nonneg_left hstep hK0
                  _ = 100 * (C1 + C2 + C3 + 1) * p * (1 + M) := by ring
              linarith
  · -- the order-`3` slot
    intro heq3 z θ hz hθ hθ2
    have h := hC3 α f (b - b₁) (a - a₁) hα0 hα1 hF hmem6 (by omega) z hz θ ⟨hθ, hθ2⟩
    have hnorm0 : 0 ≤ Work.Spaces.HkNorm α 6 f := Work.Spaces.HkNorm_nonneg α 6 f
    have hden0 : 0 ≤ Work.Spaces.gam α - 1 := by rw [hgam]; linarith
    have hsq : |Work.Spaces.mixed (b - b₁) (a - a₁) f z θ|
        ≤ Real.sqrt (C3 / (Work.Spaces.gam α - 1)) * Work.Spaces.HkNorm α 6 f := by
      rw [← Real.sqrt_sq_eq_abs, Work.Spaces.HkNorm]
      calc Real.sqrt ((Work.Spaces.mixed (b - b₁) (a - a₁) f z θ) ^ 2)
          ≤ Real.sqrt (C3 / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 6 f) :=
            Real.sqrt_le_sqrt h
        _ = Real.sqrt (C3 / (Work.Spaces.gam α - 1))
              * Real.sqrt (Work.Spaces.HkSq α 6 f) :=
            Real.sqrt_mul (div_nonneg hC3pos.le hden0) (Work.Spaces.HkSq α 6 f)
    have hfin : Real.sqrt (C3 / (Work.Spaces.gam α - 1))
        ≤ 100 * (C1 + C2 + C3 + 1) * p := by
      rw [hroot3]
      exact mul_le_mul_of_nonneg_right hC3le hp0
    calc |Work.Spaces.mixed (b - b₁) (a - a₁) f z θ|
        ≤ Real.sqrt (C3 / (Work.Spaces.gam α - 1)) * Work.Spaces.HkNorm α 6 f := hsq
      _ ≤ 100 * (C1 + C2 + C3 + 1) * p * Work.Spaces.HkNorm α 6 f :=
            mul_le_mul_of_nonneg_right hfin hnorm0

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef
