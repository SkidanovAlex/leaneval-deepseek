import Submission.NBody.LYZUnif
import Submission.NBody.EnergyLevel
import Submission.NBody.LimitShape
import Mathlib

/-!
# The energy identity for `h`-minimisers and the upper bound on their action

This module supplies the analytic inputs of Section 7 of Liu--Yan--Zhou:

* `actionOn_le_sqrt_mul_psi` — the **upper bound on the action** of an `h`-minimiser joining `x` to
  `x* + T • b`: `A_h(γ).toReal ≤ √(2h) · (T + Ψ(T))`;
* `lagR_eq_weightedNorm_sq_of_minimizer` — on a collision-free `h`-minimiser the Lagrangian equals
  the squared mass norm of the velocity (`minimizer_energy_eq_level` gives `kinetic = U + h`);
* `integral_weightedNorm_sq_eq_actionOn` — hence `∫₀^t ‖γ̇‖²_[m] = (A_h(γ|[0,t])).toReal`.
-/

open ViscositySolutions
open Filter Gradient Real Set Metric
open scoped BigOperators Topology ENNReal
open MeasureTheory

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [Nontrivial E]
variable {N : ℕ}

namespace Submission.NBody

/-! ## The upper bound on the action -/

/-- **Upper bound on the action of an `h`-minimiser** (Liu--Yan--Zhou, Lemma 4.1, second part).
If `γ` is an `h`-minimiser joining `γ 0` to `x* + T • b` (with `‖b‖_[m] = 1` and the ray from `x*`
in the direction `b` collision free), then
`(A_h(γ)).toReal ≤ √(2h) * (T + Ψ(T))`. -/
theorem actionOn_le_sqrt_mul_psi {m : Fin N → ℝ} {h : ℝ} (hh : 0 < h) (hm : ∀ i, 0 ≤ m i)
    {γ : ℝ → EN E N} {xstar b : EN E N} {τ T A B M : ℝ} (hT : 0 < T)
    (hmin : actionOn m h γ 0 τ = actionPot m h (γ 0) (γ τ))
    (hγτ : γ τ = xstar + T • b)
    (hb : ‖b‖_[m] = 1)
    (hncseg : ∀ t ∈ Set.Icc (0:ℝ) T, WithoutCollisions (xstar + t • b))
    (hΦ₁ : actionPot m h (γ 0) xstar < ⊤)
    (hA : (Real.sqrt (2 * h))⁻¹ * (actionPot m h (γ 0) xstar).toReal ≤ A)
    (hpot : ∫ t in (0:ℝ)..T, U m (xstar + t • b) ≤ (2 * h) * B * Real.log (2 * T + 2 * M + 1))
    (hlog : 0 ≤ Real.log (2 * T + 2 * M + 1)) :
    (actionOn m h γ 0 τ).toReal ≤ Real.sqrt (2 * h) * (T + lyzPsi A B M T) := by
  set W : ℝ := ∫ t in (0:ℝ)..T, U m (xstar + t • b) with hW
  have hW' : W ≤ (2 * h) * B * Real.log (2 * T + 2 * M + 1) := hpot
  have hsqrt : 0 < Real.sqrt (2 * h) := Real.sqrt_pos.mpr (by linarith)
  have hsq : (Real.sqrt (2 * h)) ^ 2 = 2 * h := Real.sq_sqrt (by linarith)
  have hW0 : 0 ≤ W := by
    rw [hW]
    exact intervalIntegral.integral_nonneg_of_forall hT.le (fun t => U_nonneg hm _)
  have hstraight : actionPot m h xstar (xstar + T • b)
      ≤ ENNReal.ofReal (Real.sqrt (2 * h) * T)
        + ENNReal.ofReal ((Real.sqrt (2 * h))⁻¹ * W) := by
    rw [hW]; exact actionPot_le_of_straight hh hm hb hT xstar hncseg
  have hΦ₂lt : actionPot m h xstar (xstar + T • b) < ⊤ := by
    refine lt_of_le_of_lt hstraight ?_
    rw [ENNReal.add_lt_top]
    exact ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩
  have htri := actionPot_triangle m h (γ 0) xstar (xstar + T • b)
  have hAB : actionPot m h (γ 0) xstar + actionPot m h xstar (xstar + T • b) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hΦ₁.ne, hΦ₂lt.ne⟩
  have h3 : (actionPot m h (γ 0) (xstar + T • b)).toReal
      ≤ (actionPot m h (γ 0) xstar).toReal + (actionPot m h xstar (xstar + T • b)).toReal :=
    (ENNReal.toReal_mono hAB htri).trans ENNReal.toReal_add_le
  have hΦ₂val : (actionPot m h xstar (xstar + T • b)).toReal
      ≤ Real.sqrt (2 * h) * T + (Real.sqrt (2 * h))⁻¹ * W := by
    have hlt : ENNReal.ofReal (Real.sqrt (2 * h) * T)
        + ENNReal.ofReal ((Real.sqrt (2 * h))⁻¹ * W) ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
    refine (ENNReal.toReal_mono hlt hstraight).trans (le_of_eq ?_)
    rw [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_ofReal (mul_nonneg (inv_nonneg.mpr hsqrt.le) hW0)]
  have hWle : (Real.sqrt (2 * h))⁻¹ * W
      ≤ Real.sqrt (2 * h) * (B * Real.log (2 * T + 2 * M + 1)) := by
    have h2 : (Real.sqrt (2 * h))⁻¹ * ((2 * h) * B * Real.log (2 * T + 2 * M + 1))
        = Real.sqrt (2 * h) * (B * Real.log (2 * T + 2 * M + 1)) := by
      have h3 : (Real.sqrt (2 * h))⁻¹ * (2 * h) = Real.sqrt (2 * h) := by
        have h4 : (Real.sqrt (2 * h))⁻¹ * (Real.sqrt (2 * h)) ^ 2 = Real.sqrt (2 * h) := by
          rw [pow_two, ← mul_assoc, inv_mul_cancel₀ hsqrt.ne', one_mul]
        rwa [hsq] at h4
      rw [show (Real.sqrt (2 * h))⁻¹ * ((2 * h) * B * Real.log (2 * T + 2 * M + 1))
          = ((Real.sqrt (2 * h))⁻¹ * (2 * h)) * (B * Real.log (2 * T + 2 * M + 1)) by ring, h3]
    calc (Real.sqrt (2 * h))⁻¹ * W
        ≤ (Real.sqrt (2 * h))⁻¹ * ((2 * h) * B * Real.log (2 * T + 2 * M + 1)) :=
          mul_le_mul_of_nonneg_left hW' (inv_nonneg.mpr hsqrt.le)
      _ = Real.sqrt (2 * h) * (B * Real.log (2 * T + 2 * M + 1)) := h2
  have hA' : (actionPot m h (γ 0) xstar).toReal ≤ Real.sqrt (2 * h) * A := by
    have h := mul_le_mul_of_nonneg_left hA hsqrt.le
    rwa [← mul_assoc, mul_inv_cancel₀ hsqrt.ne', one_mul] at h
  rw [hmin, hγτ]
  calc (actionPot m h (γ 0) (xstar + T • b)).toReal
      ≤ (actionPot m h (γ 0) xstar).toReal
        + (actionPot m h xstar (xstar + T • b)).toReal := h3
    _ ≤ Real.sqrt (2 * h) * A + (Real.sqrt (2 * h) * T + (Real.sqrt (2 * h))⁻¹ * W) :=
        add_le_add hA' hΦ₂val
    _ ≤ Real.sqrt (2 * h) * A + (Real.sqrt (2 * h) * T
          + Real.sqrt (2 * h) * (B * Real.log (2 * T + 2 * M + 1))) := by
        linarith [hWle]
    _ = Real.sqrt (2 * h) * (T + lyzPsi A B M T) := by rw [lyzPsi]; ring

/-! ## The energy identity -/

/-- The energy is the kinetic energy minus the potential. -/
lemma energy_eq_kinetic_sub_U (m : Fin N → ℝ) (γ : ℝ → EN E N) (s : ℝ) :
    energy m γ s = kinetic m (deriv γ s) - U m (γ s) := rfl

/-- **On a collision-free `h`-minimiser the Lagrangian is the square of the mass norm of the
velocity.**  Indeed the energy is `h`, so `kinetic = U + h` and
`lagR = kinetic + U + h = kinetic + kinetic = ‖γ̇‖²_[m]`. -/
theorem lagR_eq_weightedNorm_sq_of_minimizer {m : Fin N → ℝ} {h T : ℝ} {γ : ℝ → EN E N}
    (hm : ∀ i, 0 < m i) (hh : 0 < h) (hT : 0 < T)
    (hac : AbsolutelyContinuousOnInterval γ 0 T)
    (hnc : ∀ t ∈ Set.Icc 0 T, WithoutCollisions (γ t))
    (hmin : IsHMinimizer m h γ 0 T)
    (hfin : actionPot m h (γ 0) (γ T) < ⊤) :
    ∀ s ∈ Set.Ioo 0 T, lagR m h (γ s) (deriv γ s) = ‖deriv γ s‖_[m] ^ 2 := by
  intro s hs
  have hm0 : ∀ i, 0 ≤ m i := fun i => (hm i).le
  have he := minimizer_energy_eq_level hm hh hT hac hnc hmin hfin s hs
  have hk : (1 / 2) * ∑ i, m i * ‖(deriv γ s) i‖ ^ 2 = (1 / 2) * (‖deriv γ s‖_[m]) ^ 2 :=
    kinetic_eq_half_weightedNorm_sq' hm0 (deriv γ s)
  have hw := weightedNorm_sq hm0 (deriv γ s)
  rw [energy] at he
  rw [lagR, hw]
  linarith [he, hk]

/-- On a collision-free `h`-minimiser with `h > 0` the speed is at least `√(2h)`. -/
theorem sqrt_two_h_le_weightedNorm_of_minimizer {m : Fin N → ℝ} {h T : ℝ} {γ : ℝ → EN E N}
    (hm : ∀ i, 0 < m i) (hh : 0 < h) (hT : 0 < T)
    (hac : AbsolutelyContinuousOnInterval γ 0 T)
    (hnc : ∀ t ∈ Set.Icc 0 T, WithoutCollisions (γ t))
    (hmin : IsHMinimizer m h γ 0 T)
    (hfin : actionPot m h (γ 0) (γ T) < ⊤) :
    ∀ s ∈ Set.Ioo 0 T, Real.sqrt (2 * h) ≤ ‖deriv γ s‖_[m] := by
  intro s hs
  have hm0 : ∀ i, 0 ≤ m i := fun i => (hm i).le
  have he := minimizer_energy_eq_level hm hh hT hac hnc hmin hfin s hs
  have hk : (1 / 2) * ∑ i, m i * ‖(deriv γ s) i‖ ^ 2 = (1 / 2) * (‖deriv γ s‖_[m]) ^ 2 :=
    kinetic_eq_half_weightedNorm_sq' hm0 (deriv γ s)
  have hU := U_nonneg hm0 (γ s)
  have hx : 0 ≤ ‖deriv γ s‖_[m] := weightedNorm_nonneg m _
  rw [energy] at he
  have h2 : (‖deriv γ s‖_[m]) ^ 2 = 2 * (U m (γ s) + h) := by linarith [he, hk]
  have h3 : 2 * h ≤ (‖deriv γ s‖_[m]) ^ 2 := by linarith [h2, hU]
  calc Real.sqrt (2 * h) ≤ Real.sqrt ((‖deriv γ s‖_[m]) ^ 2) := Real.sqrt_le_sqrt h3
    _ = ‖deriv γ s‖_[m] := Real.sqrt_sq hx

/-- **The integral of the squared mass norm of the velocity is the action**, along a collision-free
`h`-minimiser. -/
theorem integral_weightedNorm_sq_eq_actionOn {m : Fin N → ℝ} {h : ℝ} (hh : 0 < h)
    (hm : ∀ i, 0 < m i) (hh0 : 0 ≤ h) {γ : ℝ → EN E N} {t : ℝ} (ht : 0 < t)
    (hac : AbsolutelyContinuousOnInterval γ 0 t)
    (hnc : ∀ s ∈ Set.Icc 0 t, WithoutCollisions (γ s))
    (hmin : IsHMinimizer m h γ 0 t)
    (hfin : actionPot m h (γ 0) (γ t) < ⊤) :
    ∫ s in (0:ℝ)..t, ‖deriv γ s‖_[m] ^ 2 = (actionOn m h γ 0 t).toReal := by
  have hm0 : ∀ i, 0 ≤ m i := fun i => (hm i).le
  have hfin' : actionOn m h γ 0 t < ⊤ := by rw [hmin]; exact hfin
  have h1 : actionOn m h γ 0 t
      = ENNReal.ofReal (∫ s in (0:ℝ)..t, lagR m h (γ s) (deriv γ s)) :=
    actionOn_eq_ofReal_integral_lagR ht.le hm0 hh0 hac hnc hfin'
  have h2 : ∫ s in (0:ℝ)..t, lagR m h (γ s) (deriv γ s)
      = ∫ s in (0:ℝ)..t, ‖deriv γ s‖_[m] ^ 2 := by
    have hnull : volume ({0, t} : Set ℝ) = 0 := (Set.toFinite _).measure_zero volume
    rw [intervalIntegral.integral_congr_ae
      (f := fun s => lagR m h (γ s) (deriv γ s)) (g := fun s => ‖deriv γ s‖_[m] ^ 2) ?_]
    filter_upwards [compl_mem_ae_iff.mpr hnull] with s hs hsI
    rw [Set.uIoc_of_le ht.le] at hsI
    have hst : s < t := by
      rcases lt_or_eq_of_le hsI.2 with h | h
      · exact h
      · exact absurd (by simp [h] : s ∈ ({0, t} : Set ℝ)) hs
    exact lagR_eq_weightedNorm_sq_of_minimizer hm hh ht hac hnc hmin hfin s ⟨hsI.1, hst⟩
  have hnn : 0 ≤ ∫ s in (0:ℝ)..t, ‖deriv γ s‖_[m] ^ 2 :=
    intervalIntegral.integral_nonneg ht.le fun s _ => sq_nonneg _
  rw [h1, h2, ENNReal.toReal_ofReal hnn]

/-- **The action is bounded by `√(2h) · D · (1 + Ψ̄(D)²)`** where `D = |γ t - x*|`: combining
`actionOn_le_sqrt_mul_psi` with Liu--Yan--Zhou's inequality `√(Ψ(D)/D) ≤ Ψ̄(D)`. -/
theorem actionOn_toReal_le_sqrt_mul {m : Fin N → ℝ} {h : ℝ} (hh : 0 < h) (hm : ∀ i, 0 ≤ m i)
    {γ : ℝ → EN E N} {xstar b : EN E N} {τ T A B M : ℝ} (hT : 0 < T)
    (hmin : actionOn m h γ 0 τ = actionPot m h (γ 0) (γ τ))
    (hγτ : γ τ = xstar + T • b)
    (hb : ‖b‖_[m] = 1)
    (hncseg : ∀ t ∈ Set.Icc (0:ℝ) T, WithoutCollisions (xstar + t • b))
    (hΦ₁ : actionPot m h (γ 0) xstar < ⊤)
    (hA : (Real.sqrt (2 * h))⁻¹ * (actionPot m h (γ 0) xstar).toReal ≤ A)
    (hpot : ∫ t in (0:ℝ)..T, U m (xstar + t • b) ≤ (2 * h) * B * Real.log (2 * T + 2 * M + 1))
    (hlog : 0 ≤ Real.log (2 * T + 2 * M + 1))
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hM0 : 0 ≤ M)
    {Ψb : ℝ → ℝ} (hrel : Real.sqrt (lyzPsi A B M T / T) ≤ Ψb T) :
    (actionOn m h γ 0 τ).toReal ≤ Real.sqrt (2 * h) * (T * (1 + Ψb T ^ 2)) := by
  have hbase := actionOn_le_sqrt_mul_psi hh hm hT hmin hγτ hb hncseg hΦ₁ hA hpot hlog
  have hΨnn : 0 ≤ lyzPsi A B M T := lyzPsi_nonneg hA0 hB0 hM0 hT.le
  have hdiv : lyzPsi A B M T / T ≤ Ψb T ^ 2 := by
    have h1 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hrel 2
    rwa [Real.sq_sqrt (div_nonneg hΨnn hT.le)] at h1
  have hmul : lyzPsi A B M T ≤ T * Ψb T ^ 2 := by
    have h2 := mul_le_mul_of_nonneg_right hdiv hT.le
    rw [div_mul_cancel₀ _ hT.ne'] at h2
    simpa [mul_comm] using h2
  have hkey : T + lyzPsi A B M T ≤ T * (1 + Ψb T ^ 2) := by linarith
  exact hbase.trans (mul_le_mul_of_nonneg_left hkey (Real.sqrt_nonneg (2 * h)))

end Submission.NBody
