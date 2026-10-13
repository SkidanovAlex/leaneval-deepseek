import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.PSeries
import Mathlib.Tactic.NormNum.RealSqrt
import Submission.Work.FTS.PhiStar.FlatWAux.Defs
import Submission.Work.FTS.PhiStar.StarDefs
import Submission.Work.FTS.PhiStar.Series.RemSetup
import Submission.Work.FTS.PhiStar.FamDerivDivLinv
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology BigOperators

namespace Work.FTS.PhiStar.FlatWAux

set_option maxHeartbeats 1000000

/-- The majorant `(2m+1)/(λ_m √(2m+1))` is summable: `(2m+1)/(λ_m √(2m+1)) = √(2m+1)/λ_m` is
asymptotic to `(√2/4) m^{-3/2}`, and `Σ m^{-3/2}` converges.  (At `m = 0` the quotient is `0`
because Lean's division by zero is total, so that term causes no difficulty.) -/
lemma summable_lam_sqrt_aux :
    Summable (fun m : ℕ => (2 * (m : ℝ) + 1)
      / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))) := by
  have hbase : Summable (fun m : ℕ => ((m : ℝ) + 1) ^ (-(3 / 2 : ℝ))) := by
    have h : Summable (fun n : ℕ => ((n : ℝ)) ^ (-(3 / 2 : ℝ))) :=
      (Real.summable_nat_rpow (p := (-(3 / 2 : ℝ)))).mpr (by norm_num)
    have h' := (summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ)) ^ (-(3 / 2 : ℝ))) 1).mpr h
    simpa only [Nat.cast_add, Nat.cast_one] using h'
  refine Summable.of_norm_bounded (hbase.mul_left (Real.sqrt 2)) (fun m => ?_)
  rw [Real.norm_eq_abs]
  by_cases hm : m = 0
  · subst hm
    have h0 : (2 * ((0 : ℕ) : ℝ) + 1)
        / (Gegenbauer.lam 0 * Real.sqrt (2 * ((0 : ℕ) : ℝ) + 1)) = 0 := by
      rw [show Gegenbauer.lam 0 = 0 by norm_num [Gegenbauer.lam]]
      norm_num
    rw [h0, abs_zero]
    positivity
  · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
    have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    have hlam_pos : 0 < Gegenbauer.lam m := by
      simp only [Gegenbauer.lam]; nlinarith
    have hA : (0 : ℝ) ≤ (2 * (m : ℝ) + 1)
        / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)) :=
      div_nonneg (by positivity) (mul_nonneg hlam_pos.le (Real.sqrt_nonneg _))
    rw [abs_of_nonneg hA]
    have hsne : Real.sqrt (2 * (m : ℝ) + 1) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr (by positivity))
    have hsq : Real.sqrt (2 * (m : ℝ) + 1) * Real.sqrt (2 * (m : ℝ) + 1)
        = 2 * (m : ℝ) + 1 := Real.mul_self_sqrt (by positivity)
    -- divide numerator and denominator by `√(2m+1)`
    have hstep : (2 * (m : ℝ) + 1) / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
        = Real.sqrt (2 * (m : ℝ) + 1) / Gegenbauer.lam m := by
      rw [div_eq_iff (mul_ne_zero (ne_of_gt hlam_pos) hsne)]
      have h1 : Real.sqrt (2 * (m : ℝ) + 1) / Gegenbauer.lam m
          * (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
          = Real.sqrt (2 * (m : ℝ) + 1) * Real.sqrt (2 * (m : ℝ) + 1) := by
        rw [div_mul_eq_mul_div,
          show Real.sqrt (2 * (m : ℝ) + 1) * (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
            = Gegenbauer.lam m
                * (Real.sqrt (2 * (m : ℝ) + 1) * Real.sqrt (2 * (m : ℝ) + 1)) by ring,
          mul_div_cancel_left₀ _ (ne_of_gt hlam_pos)]
      rw [h1, hsq]
    rw [hstep]
    -- `√(2m+1) ≤ √2·√(m+1)`
    have hsle : Real.sqrt (2 * (m : ℝ) + 1) ≤ Real.sqrt 2 * Real.sqrt ((m : ℝ) + 1) := by
      rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      exact Real.sqrt_le_sqrt (by linarith)
    -- `(m+1)^2 ≤ λ_m`
    have hlam2 : ((m : ℝ) + 1) ^ 2 ≤ Gegenbauer.lam m := by
      simp only [Gegenbauer.lam]; nlinarith
    have hb2pos : (0 : ℝ) < ((m : ℝ) + 1) ^ 2 := by positivity
    have hnum : (0 : ℝ) ≤ Real.sqrt 2 * Real.sqrt ((m : ℝ) + 1) := by positivity
    -- the `rpow` identity `√(m+1)/(m+1)^2 = (m+1)^{-3/2}`
    have hcore : Real.sqrt ((m : ℝ) + 1) / ((m : ℝ) + 1) ^ 2
        = ((m : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
      have hx : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      rw [Real.sqrt_eq_rpow, div_eq_mul_inv, ← Real.rpow_natCast ((m : ℝ) + 1) 2,
        ← Real.rpow_neg hx.le, ← Real.rpow_add hx]
      have hexp : (1 : ℝ) / 2 + -(((2 : ℕ)) : ℝ) = -(3 / 2) := by norm_num
      exact congrArg (fun e : ℝ => ((m : ℝ) + 1) ^ e) hexp
    calc Real.sqrt (2 * (m : ℝ) + 1) / Gegenbauer.lam m
        ≤ (Real.sqrt 2 * Real.sqrt ((m : ℝ) + 1)) / Gegenbauer.lam m :=
          div_le_div_of_nonneg_right hsle hlam_pos.le
      _ = Real.sqrt 2 * (Real.sqrt ((m : ℝ) + 1) / Gegenbauer.lam m) := by ring
      _ ≤ Real.sqrt 2 * (Real.sqrt ((m : ℝ) + 1) / ((m : ℝ) + 1) ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact div_le_div_of_nonneg_left (Real.sqrt_nonneg ((m : ℝ) + 1)) hb2pos hlam2
      _ = Real.sqrt 2 * ((m : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by rw [hcore]

theorem WtDerivTsum (ψ : ℝ → ℝ) (j : ℕ) (hj : 1 ≤ j)
    (hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ|
        ≤ C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hgr : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ C * (2 * (m : ℝ) + 1))
    (hQ0 : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ), 1 ≤ m → ∀ θ : ℝ,
      θ ∈ Set.Ioo 0 (Real.pi / 2) →
        |Work.FTS.PhiStar.FlatWAux.Qm m θ| ≤ C * (2 * (m : ℝ) + 1) ^ 2)
    (hL : ∃ K : ℝ, 0 < K ∧ ∀ (m : ℕ) (y : ℝ), y ∈ Set.Ioo 0 (Real.pi / 2) →
      |Work.FTS.PhiStar.Linv
        (fun θ' => Work.FTS.PhiStar.Gegenbauer.lam m * Work.FTS.PhiStar.Gegenbauer.eFam m θ') y|
        ≤ K * (Work.FTS.PhiStar.Gegenbauer.lam m * (2 * (m : ℝ) + 1))) :
    ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      deriv (Work.FTS.PhiStar.FlatWAux.Wt ψ j) θ
        = ∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
            * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ j
            * Work.FTS.PhiStar.Linv
                (fun θ' => Work.FTS.PhiStar.Gegenbauer.lam m
                  * Work.FTS.PhiStar.Gegenbauer.eFam m θ') θ := by
  obtain ⟨C, hC, hdec⟩ := hdec
  obtain ⟨Cg, hCg, hgr⟩ := hgr
  obtain ⟨K, hK, hL⟩ := hL
  intro θ hθ
  obtain ⟨j', hj'⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  have hj'' : j = j' + 1 := hj'
  rw [hj'']
  -- the summable majorant of the differentiated series
  have hu : Summable (fun m : ℕ => C * K * ((2 * (m : ℝ) + 1)
      / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))) :=
    summable_lam_sqrt_aux.mul_left (C * K)
  -- the `m`-th summand and its derivative
  have hQdiff : ∀ (m : ℕ) (y : ℝ), y ∈ Set.Ioo 0 (Real.pi / 2) →
      HasDerivAt (Qm m)
        (Work.FTS.PhiStar.Linv (fun θ' => Gegenbauer.lam m * Gegenbauer.eFam m θ') y) y := by
    intro m y hy
    have h1 : HasDerivAt (fun z : ℝ => Gegenbauer.eFam m z) (deriv (Gegenbauer.eFam m) y) y :=
      (((contDiff_eFam_fam m).differentiable (by norm_num)).differentiableAt).hasDerivAt
    have h2 : HasDerivAt Work.Construction.s2 (deriv Work.Construction.s2 y) y :=
      (differentiable_s2_fam.differentiableAt).hasDerivAt
    have h3 := h1.div h2 (linv_s2_ne_zero hy)
    have h4 : deriv (fun z : ℝ => Gegenbauer.eFam m z / Work.Construction.s2 z) y
        = (deriv (Gegenbauer.eFam m) y * Work.Construction.s2 y
            - Gegenbauer.eFam m y * deriv Work.Construction.s2 y)
              / Work.Construction.s2 y ^ 2 := h3.deriv
    refine h3.congr_deriv ?_
    rw [← h4]
    exact FamDerivDivLinv m hy
  have hderiv : ∀ (m : ℕ) (y : ℝ), y ∈ Set.Ioo 0 (Real.pi / 2) →
      HasDerivAt (fun z => Work.FTS.PhiStar.Series.bmode m ψ
          * ((Gegenbauer.lam m)⁻¹) ^ (j' + 1) * Qm m z)
        (Work.FTS.PhiStar.Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ (j' + 1)
          * Work.FTS.PhiStar.Linv (fun θ' => Gegenbauer.lam m * Gegenbauer.eFam m θ') y) y :=
    fun m y hy => (hQdiff m y hy).const_mul _
  -- the uniform bound on the derivatives
  have hbdd : ∀ (m : ℕ) (y : ℝ), y ∈ Set.Ioo 0 (Real.pi / 2) →
      ‖Work.FTS.PhiStar.Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ (j' + 1)
        * Work.FTS.PhiStar.Linv (fun θ' => Gegenbauer.lam m * Gegenbauer.eFam m θ') y‖
      ≤ C * K * ((2 * (m : ℝ) + 1)
          / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))) := by
    intro m y hy
    rw [Real.norm_eq_abs]
    by_cases hm : m = 0
    · subst hm
      have hz : ((Gegenbauer.lam 0)⁻¹) ^ (j' + 1) = 0 := by
        rw [show Gegenbauer.lam 0 = 0 by norm_num [Gegenbauer.lam], inv_zero]
        exact zero_pow (Nat.succ_ne_zero j')
      have hzero : Work.FTS.PhiStar.Series.bmode 0 ψ * ((Gegenbauer.lam 0)⁻¹) ^ (j' + 1)
          * Work.FTS.PhiStar.Linv (fun θ' => Gegenbauer.lam 0 * Gegenbauer.eFam 0 θ') y = 0 := by
        rw [hz, mul_zero, zero_mul]
      rw [hzero, abs_zero]
      have hl0 : (0 : ℝ) ≤ Gegenbauer.lam 0 := by norm_num [Gegenbauer.lam]
      exact mul_nonneg (mul_nonneg hC.le hK.le)
        (div_nonneg (by norm_num) (mul_nonneg hl0 (Real.sqrt_nonneg _)))
    · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
      have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
      have hlam_pos : 0 < Gegenbauer.lam m := by
        simp only [Gegenbauer.lam]; nlinarith
      have hlam1 : (1 : ℝ) ≤ Gegenbauer.lam m := by
        simp only [Gegenbauer.lam]; nlinarith
      have hinvnn : (0 : ℝ) ≤ (Gegenbauer.lam m)⁻¹ := inv_nonneg.mpr hlam_pos.le
      have hpownn : (0 : ℝ) ≤ ((Gegenbauer.lam m)⁻¹) ^ (j' + 1) := pow_nonneg hinvnn _
      -- `(λ_m⁻¹)^{j'+1}·λ_m ≤ 1`
      have hcancel : ((Gegenbauer.lam m)⁻¹) ^ (j' + 1) * Gegenbauer.lam m ≤ 1 := by
        calc ((Gegenbauer.lam m)⁻¹) ^ (j' + 1) * Gegenbauer.lam m
            = ((Gegenbauer.lam m)⁻¹) ^ j' * (Gegenbauer.lam m)⁻¹ * Gegenbauer.lam m := by
              rw [pow_succ]
          _ = ((Gegenbauer.lam m)⁻¹) ^ j' := by
              rw [mul_assoc, inv_mul_cancel₀ (ne_of_gt hlam_pos), mul_one]
          _ ≤ 1 := pow_le_one₀ hinvnn ((inv_le_one₀ hlam_pos).mpr hlam1)
      have hK21 : (0 : ℝ) ≤ K * (2 * (m : ℝ) + 1) := by positivity
      rw [abs_mul, abs_mul, abs_of_nonneg hpownn]
      calc |Work.FTS.PhiStar.Series.bmode m ψ| * ((Gegenbauer.lam m)⁻¹) ^ (j' + 1)
            * |Work.FTS.PhiStar.Linv
                (fun θ' => Gegenbauer.lam m * Gegenbauer.eFam m θ') y|
          ≤ |Work.FTS.PhiStar.Series.bmode m ψ| * ((Gegenbauer.lam m)⁻¹) ^ (j' + 1)
              * (K * (Gegenbauer.lam m * (2 * (m : ℝ) + 1))) :=
            mul_le_mul_of_nonneg_left (hL m y hy) (mul_nonneg (abs_nonneg _) hpownn)
        _ = |Work.FTS.PhiStar.Series.bmode m ψ| * ((((Gegenbauer.lam m)⁻¹) ^ (j' + 1)
              * Gegenbauer.lam m) * (K * (2 * (m : ℝ) + 1))) := by ring
        _ ≤ |Work.FTS.PhiStar.Series.bmode m ψ| * (1 * (K * (2 * (m : ℝ) + 1))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcancel hK21) (abs_nonneg _)
        _ ≤ (C / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
              * (K * (2 * (m : ℝ) + 1)) := by
            calc |Work.FTS.PhiStar.Series.bmode m ψ| * (1 * (K * (2 * (m : ℝ) + 1)))
                = |Work.FTS.PhiStar.Series.bmode m ψ| * (K * (2 * (m : ℝ) + 1)) := by ring
              _ ≤ (C / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
                    * (K * (2 * (m : ℝ) + 1)) :=
                  mul_le_mul_of_nonneg_right (hdec m hm1) hK21
        _ = C * K * ((2 * (m : ℝ) + 1)
              / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))) := by ring
  -- summability of the series at the base point `π/4`
  have hsum0 : Summable (fun m : ℕ => Work.FTS.PhiStar.Series.bmode m ψ
      * ((Gegenbauer.lam m)⁻¹) ^ (j' + 1) * Qm m (Real.pi / 4)) := by
    refine Summable.of_norm_bounded (hu.mul_left (Cg / K)) (fun m => ?_)
    rw [Real.norm_eq_abs]
    by_cases hm : m = 0
    · subst hm
      have hz : ((Gegenbauer.lam 0)⁻¹) ^ (j' + 1) = 0 := by
        rw [show Gegenbauer.lam 0 = 0 by norm_num [Gegenbauer.lam], inv_zero]
        exact zero_pow (Nat.succ_ne_zero j')
      have hzero : Work.FTS.PhiStar.Series.bmode 0 ψ * ((Gegenbauer.lam 0)⁻¹) ^ (j' + 1)
          * Qm 0 (Real.pi / 4) = 0 := by
        rw [hz, mul_zero, zero_mul]
      rw [hzero, abs_zero]
      have hl0 : (0 : ℝ) ≤ Gegenbauer.lam 0 := by norm_num [Gegenbauer.lam]
      exact mul_nonneg (div_nonneg hCg.le hK.le)
        (mul_nonneg (mul_nonneg hC.le hK.le)
          (div_nonneg (by norm_num) (mul_nonneg hl0 (Real.sqrt_nonneg _))))
    · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
      have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
      have hlam_pos : 0 < Gegenbauer.lam m := by
        simp only [Gegenbauer.lam]; nlinarith
      have hlam1 : (1 : ℝ) ≤ Gegenbauer.lam m := by
        simp only [Gegenbauer.lam]; nlinarith
      have hinvnn : (0 : ℝ) ≤ (Gegenbauer.lam m)⁻¹ := inv_nonneg.mpr hlam_pos.le
      have hpownn : (0 : ℝ) ≤ ((Gegenbauer.lam m)⁻¹) ^ (j' + 1) := pow_nonneg hinvnn _
      have hpow1 : ((Gegenbauer.lam m)⁻¹) ^ (j' + 1) ≤ 1 :=
        pow_le_one₀ hinvnn ((inv_le_one₀ hlam_pos).mpr hlam1)
      have hQ : Qm m (Real.pi / 4) = Gegenbauer.eFam m (Real.pi / 4) := by
        have hs : Work.Construction.s2 (Real.pi / 4) = 1 := by
          rw [Work.Construction.s2_eq, show 2 * (Real.pi / 4) = Real.pi / 2 by ring,
            Real.sin_pi_div_two]
        simp only [Qm, hs, div_one]
      have he : |Gegenbauer.eFam m (Real.pi / 4)| ≤ Cg * (2 * (m : ℝ) + 1) :=
        hgr m (Real.pi / 4) (by constructor <;> linarith [Real.pi_pos])
      rw [abs_mul, abs_mul, abs_of_nonneg hpownn, hQ]
      calc |Work.FTS.PhiStar.Series.bmode m ψ| * ((Gegenbauer.lam m)⁻¹) ^ (j' + 1)
            * |Gegenbauer.eFam m (Real.pi / 4)|
          = (|Work.FTS.PhiStar.Series.bmode m ψ| * |Gegenbauer.eFam m (Real.pi / 4)|)
              * ((Gegenbauer.lam m)⁻¹) ^ (j' + 1) := by ring
        _ ≤ (C / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
              * (Cg * (2 * (m : ℝ) + 1))) * ((Gegenbauer.lam m)⁻¹) ^ (j' + 1) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul (hdec m hm1) he (abs_nonneg _) (by positivity)) hpownn
        _ = C / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
              * ((Gegenbauer.lam m)⁻¹) ^ (j' + 1) * (Cg * (2 * (m : ℝ) + 1)) := by ring
        _ ≤ C / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)) * 1
              * (Cg * (2 * (m : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow1 (by positivity))
              (by positivity)
        _ = C * Cg * ((2 * (m : ℝ) + 1)
              / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))) := by ring
        _ = (Cg / K) * (C * K * ((2 * (m : ℝ) + 1)
              / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))) := by
            have hnum : Cg * (C * K * ((2 * (m : ℝ) + 1)
                / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))))
                = (C * Cg * ((2 * (m : ℝ) + 1)
                    / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))) * K := by ring
            rw [div_mul_eq_mul_div, hnum, mul_div_cancel_right₀ _ (ne_of_gt hK)]
  have hmain : HasDerivAt
      (fun z : ℝ => ∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
        * ((Gegenbauer.lam m)⁻¹) ^ (j' + 1) * Qm m z)
      (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ (j' + 1)
        * Work.FTS.PhiStar.Linv (fun θ' => Gegenbauer.lam m * Gegenbauer.eFam m θ') θ) θ :=
    hasDerivAt_tsum_of_isPreconnected
      (u := fun m : ℕ => C * K * ((2 * (m : ℝ) + 1)
        / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))))
      (g := fun m z => Work.FTS.PhiStar.Series.bmode m ψ
        * ((Gegenbauer.lam m)⁻¹) ^ (j' + 1) * Qm m z)
      (g' := fun m z => Work.FTS.PhiStar.Series.bmode m ψ
        * ((Gegenbauer.lam m)⁻¹) ^ (j' + 1)
        * Work.FTS.PhiStar.Linv (fun θ' => Gegenbauer.lam m * Gegenbauer.eFam m θ') z)
      hu isOpen_Ioo isPreconnected_Ioo hderiv hbdd
      (show Real.pi / 4 ∈ Set.Ioo 0 (Real.pi / 2) from
        ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩) hsum0 hθ
  simp only [Wt]
  exact hmain.deriv

end Work.FTS.PhiStar.FlatWAux
