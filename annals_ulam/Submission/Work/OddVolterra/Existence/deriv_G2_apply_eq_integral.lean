import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Kernel.Diag
import Submission.Work.OddVolterra.Kernel.G2Deriv
import Submission.Work.OddVolterra.Existence.Theta_integrand_intervalIntegrable

/-!
# The first-slot derivative of `G₂`, componentwise

`G₂(u,σ,z) = ∫₀¹ (√(τ(1-τ)))⁻¹ • K(u + τ(σ-u), σ, z) dτ`.  Differentiating under the Abel
integral (`Work.OddVolterra.G2_deriv_eq_integral`) gives the vector-valued identity

`deriv (fun u => G₂(u,σ,z)) s = ∫₀¹ (√(τ(1-τ)))⁻¹ • ((1-τ) • deriv K(s + τ(σ-s), σ, z))`,

and this file reads off the `i`-th component of both sides, in the scalar form used by the
odd-case Volterra argument.

The single analytic input is that the moving point `s + τ(σ-s)` stays inside the region where
`Kvec` is differentiable with bounded derivative (the hypotheses `hpos`, `hbdK`, `hbdD`); the
margin `δ` of the statement is then cut down to `min δ ((σ-s)/2)` so that the whole *symmetric*
interval `(s - δ', s + δ')` used by `hasDerivAt_G2` maps into the region `[s - δ, σ)`.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

set_option maxHeartbeats 2000000

namespace Work.OddVolterra.Existence

noncomputable section

theorem deriv_G2_apply_eq_integral (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) {Z : ℝ → Work.OddVolterra.St}
    (hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z (Set.Ioi (0:ℝ)))
    {s : ℝ} (hs : s ∈ Set.Ioo (0:ℝ) 1) (i : Fin 2)
    {δ Cm : ℝ} (hδ : 0 < δ) (hCm : 0 < Cm)
    (hpos : ∀ σ ∈ Set.Icc s 1, ∀ a ∈ Set.Icc (s - δ) σ,
      0 < Work.OddVolterra.krad h σ (-(Z σ 0)) a ∧
        0 < Work.OddVolterra.krad h σ (Z σ 1) a)
    (hbdK : ∀ σ ∈ Set.Icc s 1, ∀ a ∈ Set.Ico (s - δ) σ,
      ‖Work.OddVolterra.Kvec n h a σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)‖ ≤ Cm)
    (hbdD : ∀ σ ∈ Set.Icc s 1, ∀ a ∈ Set.Ico (s - δ) σ,
      ‖deriv (fun u : ℝ => Work.OddVolterra.Kvec n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) a‖ ≤ Cm)
    {σ : ℝ} (hσ : σ ∈ Set.Ioo s 1) :
    deriv (fun u : ℝ => (Work.OddVolterra.G2 n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) i) s =
      ∫ τ in (0:ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ *
        ((1 - τ) * ((deriv (fun u : ℝ => Work.OddVolterra.Kvec n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) (s + τ * (σ - s))) i)) := by
  have hsσ : s < σ := hσ.1
  have hσIcc : σ ∈ Set.Icc s 1 := ⟨le_of_lt hσ.1, le_of_lt hσ.2⟩
  have hσs : 0 < σ - s := by linarith
  -- cut the margin down so that the symmetric interval used by `hasDerivAt_G2` lies in `[s-δ, σ)`
  set δ' : ℝ := min δ ((σ - s) / 2) with hδ'def
  have hδ'pos : 0 < δ' := lt_min hδ (by linarith)
  have hδ'le : δ' ≤ δ := min_le_left _ _
  have hδ'le₂ : δ' ≤ (σ - s) / 2 := min_le_right _ _
  have hpt : ∀ x ∈ Set.Ioo (s - δ') (s + δ'), ∀ τ ∈ Set.Ico (0:ℝ) 1,
      x + τ * (σ - x) ∈ Set.Ico (s - δ) σ := by
    intro x hx τ hτ
    have hxσ : x < σ := by linarith [hx.2, hδ'le₂]
    refine ⟨?_, ?_⟩
    · have h1 : x ≤ x + τ * (σ - x) := by
        have : 0 ≤ τ * (σ - x) := mul_nonneg hτ.1 (by linarith)
        linarith
      linarith [le_of_lt hx.1, hδ'le]
    · have h1 : τ * (σ - x) < σ - x := by
        exact mul_lt_of_lt_one_left (by linarith) hτ.2
      linarith
  have hbdK' : ∀ x ∈ Set.Ioo (s - δ') (s + δ'), ∀ τ ∈ Set.Ico (0:ℝ) 1,
      ‖Work.OddVolterra.Kvec n h (x + τ * (σ - x)) σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)‖ ≤ Cm :=
    fun x hx τ hτ => hbdK σ hσIcc _ (hpt x hx τ hτ)
  have hdiff' : ∀ x ∈ Set.Ioo (s - δ') (s + δ'), ∀ τ ∈ Set.Ico (0:ℝ) 1,
      DifferentiableAt ℝ (fun u : ℝ =>
        Work.OddVolterra.Kvec n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) (x + τ * (σ - x)) := by
    intro x hx τ hτ
    have ha := hpt x hx τ hτ
    obtain ⟨hk1, hk2⟩ := hpos σ hσIcc _ ⟨ha.1, le_of_lt ha.2⟩
    exact differentiableAt_Kvec n hn hh (Z σ) ha.2 hk1 hk2
  have hbound' : ∀ x ∈ Set.Ioo (s - δ') (s + δ'), ∀ τ ∈ Set.Icc (0:ℝ) 1,
      ‖(1 - τ) • deriv (fun u : ℝ =>
        Work.OddVolterra.Kvec n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) (x + τ * (σ - x))‖ ≤ Cm := by
    intro x hx τ hτ
    rcases eq_or_lt_of_le hτ.2 with h1 | h1
    · subst h1
      simp only [sub_self, zero_smul, norm_zero]
      exact hCm.le
    · have hτIco : τ ∈ Set.Ico (0:ℝ) 1 := ⟨hτ.1, h1⟩
      have hb := hbdD σ hσIcc _ (hpt x hx τ hτIco)
      have hτle : (0:ℝ) ≤ 1 - τ := by linarith
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hτle]
      calc (1 - τ) * ‖deriv (fun u : ℝ =>
              Work.OddVolterra.Kvec n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) (x + τ * (σ - x))‖
            ≤ 1 * ‖deriv (fun u : ℝ =>
              Work.OddVolterra.Kvec n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) (x + τ * (σ - x))‖ := by
              refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
              linarith [hτ.1, h1]
        _ = ‖deriv (fun u : ℝ =>
              Work.OddVolterra.Kvec n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) (x + τ * (σ - x))‖ := one_mul _
        _ ≤ Cm := hb
  have hH := Work.OddVolterra.hasDerivAt_G2 (h := h) n hh hsσ (Z σ) hδ'pos hbdK' hdiff' hbound'
  -- the Abel integrand of the derivative
  have hVint : IntervalIntegrable
      (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹ •
        ((1 - τ) • deriv (fun u : ℝ =>
          Work.OddVolterra.Kvec n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) (s + τ * (σ - s))))
      volume (0:ℝ) 1 := by
    refine (Commons.Geometry.Ulam.intervalIntegrable_abel_weight.mul_const Cm).mono_fun' ?_ ?_
    · have hm : Measurable (fun τ : ℝ => deriv (fun u : ℝ =>
          Work.OddVolterra.Kvec n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) (s + τ * (σ - s))) :=
        (measurable_deriv (𝕜 := ℝ) (fun u : ℝ =>
          Work.OddVolterra.Kvec n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3))).comp
          (by fun_prop : Measurable fun τ : ℝ => s + τ * (σ - s))
      have hw : Measurable (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹) :=
        (Work.OddVolterra.measurable_sqrt_real.comp
          (measurable_id.mul (measurable_const.sub measurable_id))).inv
      exact (hw.smul ((measurable_const.sub measurable_id).smul hm)).aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with τ hτ
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hτ
      rcases eq_or_lt_of_le hτ.2 with h1 | h1
      · subst h1
        simp [Real.sqrt_zero]
      · have hτIco : τ ∈ Set.Ico (0:ℝ) 1 := ⟨le_of_lt hτ.1, h1⟩
        have ha : s + τ * (σ - s) ∈ Set.Ico (s - δ) σ := by
          refine ⟨?_, ?_⟩
          · have : 0 ≤ τ * (σ - s) := mul_nonneg (le_of_lt hτ.1) (le_of_lt hσs)
            linarith
          · have : τ * (σ - s) < σ - s := mul_lt_of_lt_one_left hσs h1
            linarith
        have hb := hbdD σ hσIcc _ ha
        have hw : 0 ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
        have hτle : (0:ℝ) ≤ 1 - τ := by linarith
        have hsm : ‖(1 - τ) • deriv (fun u : ℝ =>
            Work.OddVolterra.Kvec n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) (s + τ * (σ - s))‖ ≤ Cm := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hτle]
          calc (1 - τ) * ‖deriv (fun u : ℝ =>
                  Work.OddVolterra.Kvec n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) (s + τ * (σ - s))‖
                ≤ 1 * ‖deriv (fun u : ℝ =>
                  Work.OddVolterra.Kvec n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) (s + τ * (σ - s))‖ := by
                  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
                  linarith [hτ.1, h1]
            _ = ‖deriv (fun u : ℝ =>
                  Work.OddVolterra.Kvec n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) (s + τ * (σ - s))‖ := one_mul _
            _ ≤ Cm := hb
        calc ‖(Real.sqrt (τ * (1 - τ)))⁻¹ •
              ((1 - τ) • deriv (fun u : ℝ =>
                Work.OddVolterra.Kvec n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) (s + τ * (σ - s)))‖
            = (Real.sqrt (τ * (1 - τ)))⁻¹ * ‖(1 - τ) • deriv (fun u : ℝ =>
                Work.OddVolterra.Kvec n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) (s + τ * (σ - s))‖ := by
              rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hw]
          _ ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ * Cm := mul_le_mul_of_nonneg_left hsm hw
  have hdiffcomp : ∀ j : Fin 2, DifferentiableAt ℝ
      (fun u : ℝ => (Work.OddVolterra.G2 n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) j) s :=
    fun j => (differentiableAt_pi.mp hH.differentiableAt) j
  have hcomp_eq : deriv (fun u : ℝ =>
        (Work.OddVolterra.G2 n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) i) s
      = (deriv (fun u : ℝ =>
        Work.OddVolterra.G2 n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) s) i :=
    (congrFun (deriv_pi (𝕜 := ℝ) (x := s)
      (φ := fun u : ℝ => Work.OddVolterra.G2 n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3))
      (fun j => hdiffcomp j)) i).symm
  have hproj_eq : (∫ τ in (0:ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ •
        ((1 - τ) • deriv (fun u : ℝ =>
          Work.OddVolterra.Kvec n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) (s + τ * (σ - s)))) i
      = ∫ τ in (0:ℝ)..1, ((Real.sqrt (τ * (1 - τ)))⁻¹ •
        ((1 - τ) • deriv (fun u : ℝ =>
          Work.OddVolterra.Kvec n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) (s + τ * (σ - s)))) i := by
    have h := ContinuousLinearMap.intervalIntegral_comp_comm
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i) hVint
    simpa [ContinuousLinearMap.proj_apply] using h.symm
  have key : ∀ τ : ℝ, ((Real.sqrt (τ * (1 - τ)))⁻¹ •
        ((1 - τ) • deriv (fun u : ℝ =>
          Work.OddVolterra.Kvec n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) (s + τ * (σ - s)))) i
      = (Real.sqrt (τ * (1 - τ)))⁻¹ *
        ((1 - τ) * ((deriv (fun u : ℝ =>
          Work.OddVolterra.Kvec n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) (s + τ * (σ - s))) i)) :=
    fun τ => by simp [Pi.smul_apply, smul_eq_mul]
  calc deriv (fun u : ℝ =>
        (Work.OddVolterra.G2 n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) i) s
      = (deriv (fun u : ℝ =>
          Work.OddVolterra.G2 n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) s) i := hcomp_eq
    _ = (∫ τ in (0:ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ •
          ((1 - τ) • deriv (fun u : ℝ =>
            Work.OddVolterra.Kvec n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) (s + τ * (σ - s)))) i := by
          rw [hH.deriv]
    _ = ∫ τ in (0:ℝ)..1, ((Real.sqrt (τ * (1 - τ)))⁻¹ •
          ((1 - τ) • deriv (fun u : ℝ =>
            Work.OddVolterra.Kvec n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) (s + τ * (σ - s)))) i :=
          hproj_eq
    _ = ∫ τ in (0:ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ *
          ((1 - τ) * ((deriv (fun u : ℝ =>
            Work.OddVolterra.Kvec n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) (s + τ * (σ - s))) i)) :=
          intervalIntegral.integral_congr (fun τ _ => key τ)

end

end Work.OddVolterra.Existence
