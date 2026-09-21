import Mathlib
import Submission.Work.OddVolterra.Kernel.Diag
import Submission.Work.Geometry.Ulam.ulam_g2ds

/-!
# Differentiation under the Abel integral for `G₂`

`G₂(u,σ,z) = ∫₀¹ (√(τ(1-τ)))⁻¹ • K(u+τ(σ-u), σ, z) dτ`; this file computes its derivative in
the first slot as the Abel-weighted integral of the derivative of the kernel.  The two analytic
inputs are exactly the ones supplied by `K1_K2_deriv_bound`: the moving point stays in the
smoothness region of the kernel and the derivative of the kernel is bounded there.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddVolterra

noncomputable section

set_option maxHeartbeats 2000000

variable {h : ℝ → ℝ}

lemma measurable_sqrt_real : Measurable Real.sqrt := Real.continuous_sqrt.measurable

/-- Measurability in the first slot of the Abel kernel `K₁`. -/
lemma measurable_K1 (n : ℕ) (hh : ContDiff ℝ (⊤ : ℕ∞) h) (σ t : ℝ) :
    Measurable (fun a : ℝ => K1 n h a σ t) := by
  have hlin : Measurable (fun a : ℝ => line h a t) := by
    unfold line
    exact ((continuous_id.mul continuous_const).add hh.continuous).measurable
  have hquot : Measurable (fun a : ℝ => hquot h a σ) :=
    ((Work.OddVolterra.Existence.hquot_contDiff hh).continuous.comp
      (by fun_prop : Continuous fun a : ℝ => (a, σ))).measurable
  have hpsi : Measurable (fun a : ℝ => psi h (fun t' => line h σ t') a t) := by
    unfold psi
    exact measurable_const.sub (hlin.pow_const 2)
  have hF : Measurable (fun a : ℝ => psi h (fun t' => line h σ t') a t ^ n *
      Real.sqrt (psi h (fun t' => line h σ t') a t)) :=
    (hpsi.pow_const n).mul (measurable_sqrt_real.comp hpsi)
  have hiter : ∀ k : ℕ, Measurable (fun a : ℝ => iteratedDeriv k
      (fun u : ℝ => psi h (fun t' => line h σ t') u t ^ n *
        Real.sqrt (psi h (fun t' => line h σ t') u t)) a) := by
    intro k
    induction k with
    | zero => simpa using hF
    | succ k ih =>
        have heq : (fun a : ℝ => iteratedDeriv (k + 1)
            (fun u : ℝ => psi h (fun t' => line h σ t') u t ^ n *
              Real.sqrt (psi h (fun t' => line h σ t') u t)) a)
            = deriv (iteratedDeriv k
              (fun u : ℝ => psi h (fun t' => line h σ t') u t ^ n *
                Real.sqrt (psi h (fun t' => line h σ t') u t))) := by
          funext a
          rw [iteratedDeriv_succ]
        rw [heq]
        exact measurable_deriv (𝕜 := ℝ) _
  have hJ1 : Measurable (fun a : ℝ => J1 n h a σ t) := by
    have hthen : Measurable (fun a : ℝ =>
        ((Nat.doubleFactorial (2 * n + 1) : ℝ)) *
          (- (line h a t * lineSlope h a t)) ^ (n + 1)) := by
      have hslope : Measurable (fun a : ℝ => lineSlope h a t) := by
        unfold lineSlope
        exact measurable_const.add (measurable_deriv (𝕜 := ℝ) h)
      exact measurable_const.mul (((hlin.mul hslope).neg).pow_const (n + 1))
    have helse : Measurable (fun a : ℝ => iteratedDeriv (n + 1)
        (fun u : ℝ => psi h (fun t' => line h σ t') u t ^ n *
          Real.sqrt (psi h (fun t' => line h σ t') u t)) a *
        Real.sqrt (psi h (fun t' => line h σ t') a t)) :=
      ((hiter (n + 1)).mul (measurable_sqrt_real.comp hpsi))
    have hset : MeasurableSet {a : ℝ | σ = a} :=
      measurableSet_eq_fun measurable_const measurable_id
    unfold J1
    exact Measurable.ite (p := fun a : ℝ => σ = a) hset hthen helse
  have hKden : Measurable (fun a : ℝ => Kden h a σ t) := by
    unfold Kden
    refine measurable_sqrt_real.comp ?_
    exact (measurable_const.add hquot).mul (measurable_const.add hlin)
  unfold K1
  exact hJ1.div hKden

/-- Measurability in the first slot of the Abel kernel `K₂`. -/
lemma measurable_K2 (n : ℕ) (hh : ContDiff ℝ (⊤ : ℕ∞) h) (σ t : ℝ) :
    Measurable (fun a : ℝ => K2 n h a σ t) := by
  have hlin : Measurable (fun a : ℝ => line h a t) := by
    unfold line
    exact ((continuous_id.mul continuous_const).add hh.continuous).measurable
  have hquot : Measurable (fun a : ℝ => hquot h a σ) :=
    ((Work.OddVolterra.Existence.hquot_contDiff hh).continuous.comp
      (by fun_prop : Continuous fun a : ℝ => (a, σ))).measurable
  have hpsi : Measurable (fun a : ℝ => psi h (fun t' => line h σ t') a t) := by
    unfold psi
    exact measurable_const.sub (hlin.pow_const 2)
  have hslope : Measurable (fun a : ℝ => lineSlope h a t) := by
    unfold lineSlope
    exact measurable_const.add (measurable_deriv (𝕜 := ℝ) h)
  have hF : Measurable (fun a : ℝ => psi h (fun t' => line h σ t') a t ^ (n - 1) *
      Real.sqrt (psi h (fun t' => line h σ t') a t) * lineSlope h a t) :=
    (((hpsi.pow_const (n - 1)).mul (measurable_sqrt_real.comp hpsi)).mul hslope)
  have hiter : ∀ k : ℕ, Measurable (fun a : ℝ => iteratedDeriv k
      (fun u : ℝ => psi h (fun t' => line h σ t') u t ^ (n - 1) *
        Real.sqrt (psi h (fun t' => line h σ t') u t) * lineSlope h u t) a) := by
    intro k
    induction k with
    | zero => simpa using hF
    | succ k ih =>
        have heq : (fun a : ℝ => iteratedDeriv (k + 1)
            (fun u : ℝ => psi h (fun t' => line h σ t') u t ^ (n - 1) *
              Real.sqrt (psi h (fun t' => line h σ t') u t) * lineSlope h u t) a)
            = deriv (iteratedDeriv k
              (fun u : ℝ => psi h (fun t' => line h σ t') u t ^ (n - 1) *
                Real.sqrt (psi h (fun t' => line h σ t') u t) * lineSlope h u t)) := by
          funext a
          rw [iteratedDeriv_succ]
        rw [heq]
        exact measurable_deriv (𝕜 := ℝ) _
  have hJ2 : Measurable (fun a : ℝ => J2 n h a σ t) := by
    have hthen : Measurable (fun a : ℝ =>
        ((Nat.doubleFactorial (2 * n - 1) : ℝ)) *
          (- (line h a t * lineSlope h a t)) ^ n * lineSlope h a t) :=
      (measurable_const.mul (((hlin.mul hslope).neg).pow_const n)).mul hslope
    have helse : Measurable (fun a : ℝ => iteratedDeriv n
        (fun u : ℝ => psi h (fun t' => line h σ t') u t ^ (n - 1) *
          Real.sqrt (psi h (fun t' => line h σ t') u t) * lineSlope h u t) a *
        Real.sqrt (psi h (fun t' => line h σ t') a t)) :=
      ((hiter n).mul (measurable_sqrt_real.comp hpsi))
    have hset : MeasurableSet {a : ℝ | σ = a} :=
      measurableSet_eq_fun measurable_const measurable_id
    unfold J2
    exact Measurable.ite (p := fun a : ℝ => σ = a) hset hthen helse
  have hKden : Measurable (fun a : ℝ => Kden h a σ t) := by
    unfold Kden
    refine measurable_sqrt_real.comp ?_
    exact (measurable_const.add hquot).mul (measurable_const.add hlin)
  unfold K2
  exact hJ2.div hKden

/-- Measurability in the first slot of the two-component Abel kernel `Kvec`. -/
lemma measurable_Kvec (n : ℕ) (hh : ContDiff ℝ (⊤ : ℕ∞) h) (σ : ℝ) (z : St) :
    Measurable (fun a : ℝ => Kvec n h a σ (z 0) (z 1) (z 2) (z 3)) := by
  have h1 := measurable_K1 (h := h) n hh σ (-(z 0))
  have h2 := measurable_K1 (h := h) n hh σ (z 1)
  have h3 := measurable_K2 (h := h) n hh σ (-(z 0))
  have h4 := measurable_K2 (h := h) n hh σ (z 1)
  rw [show (fun a : ℝ => Kvec n h a σ (z 0) (z 1) (z 2) (z 3))
      = fun a : ℝ => ![- (K1 n h a σ (-(z 0)) * z 2 + K1 n h a σ (z 1) * z 3),
          - (K2 n h a σ (-(z 0)) * z 2 + K2 n h a σ (z 1) * z 3)] from by
      funext a i
      fin_cases i <;> rfl]
  rw [measurable_pi_iff]
  intro i
  fin_cases i
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons]
    exact ((h1.mul measurable_const).add (h2.mul measurable_const)).neg
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons]
    exact ((h3.mul measurable_const).add (h4.mul measurable_const)).neg

/-- **Differentiation under the Abel integral for `G₂`** (`HasDerivAt` form). -/
theorem hasDerivAt_G2 (n : ℕ) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    {s σ : ℝ} (hsσ : s < σ) (z : St) {δ C : ℝ} (hδ : 0 < δ)
    (hbdK : ∀ x ∈ Set.Ioo (s - δ) (s + δ), ∀ τ ∈ Set.Ico (0:ℝ) 1,
      ‖Kvec n h (x + τ * (σ - x)) σ (z 0) (z 1) (z 2) (z 3)‖ ≤ C)
    (hdiff : ∀ x ∈ Set.Ioo (s - δ) (s + δ), ∀ τ ∈ Set.Ico (0:ℝ) 1,
      DifferentiableAt ℝ (fun u : ℝ => Kvec n h u σ (z 0) (z 1) (z 2) (z 3)) (x + τ * (σ - x)))
    (hbound : ∀ x ∈ Set.Ioo (s - δ) (s + δ), ∀ τ ∈ Set.Icc (0:ℝ) 1,
      ‖(1 - τ) • deriv (fun u : ℝ => Kvec n h u σ (z 0) (z 1) (z 2) (z 3)) (x + τ * (σ - x))‖ ≤ C) :
    HasDerivAt (fun u : ℝ => G2 n h u σ (z 0) (z 1) (z 2) (z 3))
      (∫ τ in (0:ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ •
        ((1 - τ) • deriv (fun u : ℝ => Kvec n h u σ (z 0) (z 1) (z 2) (z 3)) (s + τ * (σ - s)))) s := by
  have hC0 : 0 ≤ C := by
    have h := hbound s ⟨by linarith, by linarith⟩ 1 ⟨zero_le_one, le_rfl⟩
    simpa using h
  have hw_int : IntervalIntegrable
      (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹) volume (0 : ℝ) 1 :=
    Commons.Geometry.Ulam.intervalIntegrable_abel_weight
  have hw_norm : ∀ τ : ℝ, ‖(Real.sqrt (τ * (1 - τ)))⁻¹‖ = (Real.sqrt (τ * (1 - τ)))⁻¹ := by
    intro τ
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  have hw_meas : Measurable (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹) := by
    have h : Measurable (fun τ : ℝ => Real.sqrt (τ * (1 - τ))) :=
      measurable_sqrt_real.comp (measurable_id.mul (measurable_const.sub measurable_id))
    exact h.inv
  have hinner_cont : Continuous (fun τ : ℝ => (fun x : ℝ => x + τ * (σ - x))) := by
    fun_prop
  -- the two integrands
  set F : ℝ → ℝ → (Fin 2 → ℝ) := fun x τ => (Real.sqrt (τ * (1 - τ)))⁻¹ •
      Kvec n h (x + τ * (σ - x)) σ (z 0) (z 1) (z 2) (z 3) with hFdef
  set F' : ℝ → ℝ → (Fin 2 → ℝ) := fun x τ => (Real.sqrt (τ * (1 - τ)))⁻¹ •
      ((1 - τ) • deriv (fun u : ℝ => Kvec n h u σ (z 0) (z 1) (z 2) (z 3))
        (x + τ * (σ - x))) with hF'def
  have hF_meas_all : ∀ x : ℝ,
      AEStronglyMeasurable (F x) (volume.restrict (Set.uIoc (0:ℝ) 1)) := by
    intro x
    have hm : Measurable (fun τ : ℝ => Kvec n h (x + τ * (σ - x)) σ (z 0) (z 1) (z 2) (z 3)) :=
      (measurable_Kvec n hh σ z).comp (by fun_prop : Measurable fun τ : ℝ => x + τ * (σ - x))
    exact (hw_meas.smul hm).aestronglyMeasurable
  have hF_meas : ∀ᶠ x in 𝓝 s, AEStronglyMeasurable (F x) (volume.restrict (Set.uIoc (0:ℝ) 1)) :=
    Filter.Eventually.of_forall hF_meas_all
  have hF'_meas : AEStronglyMeasurable (F' s) (volume.restrict (Set.uIoc (0:ℝ) 1)) := by
    have hm : Measurable (fun τ : ℝ =>
        deriv (fun u : ℝ => Kvec n h u σ (z 0) (z 1) (z 2) (z 3)) (s + τ * (σ - s))) :=
      (measurable_deriv (𝕜 := ℝ)
        (fun u : ℝ => Kvec n h u σ (z 0) (z 1) (z 2) (z 3))).comp
        (by fun_prop : Measurable fun τ : ℝ => s + τ * (σ - s))
    exact (hw_meas.smul ((measurable_const.sub measurable_id).smul hm)).aestronglyMeasurable
  have hF_int : IntervalIntegrable (F s) volume (0:ℝ) 1 := by
    refine (hw_int.mul_const C).mono_fun' ?_ ?_
    · exact (hF_meas.self_of_nhds)
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with τ hτ
      by_cases h1 : τ = 1
      · subst h1
        have hz : F s 1 = 0 := by
          simp only [hFdef]
          have hx1 : s + 1 * (σ - s) = σ := by ring
          rw [hx1]
          norm_num
        rw [hz]
        simp
      have hτIco : τ ∈ Set.Ico (0:ℝ) 1 := by
        rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1), Set.mem_Ioc] at hτ
        exact ⟨le_of_lt hτ.1, lt_of_le_of_ne hτ.2 h1⟩
      have hK := hbdK s ⟨sub_lt_self _ hδ, lt_add_of_pos_right _ hδ⟩ τ hτIco
      have hw : 0 ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
      calc ‖F s τ‖ = ‖(Real.sqrt (τ * (1 - τ)))⁻¹‖ *
            ‖Kvec n h (s + τ * (σ - s)) σ (z 0) (z 1) (z 2) (z 3)‖ := by
              simp only [hFdef, norm_smul]
        _ = (Real.sqrt (τ * (1 - τ)))⁻¹ *
            ‖Kvec n h (s + τ * (σ - s)) σ (z 0) (z 1) (z 2) (z 3)‖ := by
              rw [Real.norm_eq_abs, abs_of_nonneg hw]
        _ ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ * C := mul_le_mul_of_nonneg_left hK hw
  have h_bound : ∀ᵐ τ ∂(volume : Measure ℝ), τ ∈ Set.uIoc (0:ℝ) 1 →
      ∀ x ∈ Set.Ioo (s - δ) (s + δ),
        ‖F' x τ‖ ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ * C := by
    refine Filter.Eventually.of_forall (fun τ hτ x hx => ?_)
    have hτIcc : τ ∈ Set.Icc (0:ℝ) 1 := by
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hτ
      exact ⟨le_of_lt hτ.1, hτ.2⟩
    have hK := hbound x hx τ hτIcc
    have hw : 0 ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
    calc ‖F' x τ‖ = ‖(Real.sqrt (τ * (1 - τ)))⁻¹‖ *
          ‖(1 - τ) • deriv (fun u : ℝ => Kvec n h u σ (z 0) (z 1) (z 2) (z 3))
            (x + τ * (σ - x))‖ := by simp only [hF'def, norm_smul]
      _ = (Real.sqrt (τ * (1 - τ)))⁻¹ *
          ‖(1 - τ) • deriv (fun u : ℝ => Kvec n h u σ (z 0) (z 1) (z 2) (z 3))
            (x + τ * (σ - x))‖ := by rw [Real.norm_eq_abs, abs_of_nonneg hw]
      _ ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ * C := mul_le_mul_of_nonneg_left hK hw
  have hbound_int : IntervalIntegrable
      (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹ * C) volume (0:ℝ) 1 :=
    hw_int.mul_const C
  have h_diff : ∀ᵐ τ ∂(volume : Measure ℝ), τ ∈ Set.uIoc (0:ℝ) 1 →
      ∀ x ∈ Set.Ioo (s - δ) (s + δ),
        HasDerivAt (fun x => F x τ) (F' x τ) x := by
    refine Filter.Eventually.of_forall (fun τ hτ x hx => ?_)
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1), Set.mem_Ioc] at hτ
    have hτIcc : τ ∈ Set.Icc (0:ℝ) 1 := ⟨le_of_lt hτ.1, hτ.2⟩
    by_cases h1 : τ = 1
    · subst h1
      have hzero : (fun x : ℝ => F x 1) = fun _ : ℝ => (0 : Fin 2 → ℝ) := by
        funext y
        simp only [hFdef, mul_one]
        have h1 : y + 1 * (σ - y) = σ := by ring
        rw [h1]
        norm_num
      have hzero' : F' x 1 = 0 := by
        simp only [hF'def, sub_self, zero_smul, smul_zero]
      rw [hzero, hzero']
      exact hasDerivAt_const x 0
    · have hτlt : τ < 1 := lt_of_le_of_ne hτIcc.2 h1
      have hinner : HasDerivAt (fun x : ℝ => x + τ * (σ - x)) (1 - τ) x := by
        have hfun : (fun x : ℝ => x + τ * (σ - x)) = fun x : ℝ => (1 - τ) * x + τ * σ := by
          funext y; ring
        rw [hfun]
        simpa using ((hasDerivAt_id x).const_mul (1 - τ)).add_const (τ * σ)
      have houter : HasDerivAt (fun u : ℝ => Kvec n h u σ (z 0) (z 1) (z 2) (z 3))
          (deriv (fun u : ℝ => Kvec n h u σ (z 0) (z 1) (z 2) (z 3))
            (x + τ * (σ - x))) (x + τ * (σ - x)) :=
        (hdiff x hx τ ⟨hτIcc.1, hτlt⟩).hasDerivAt
      have hcomp := houter.scomp (𝕜 := ℝ) (𝕜' := ℝ) (F := Fin 2 → ℝ) (x := x) hinner
      have hfull := hcomp.const_smul ((Real.sqrt (τ * (1 - τ)))⁻¹)
      refine hfull.congr_deriv ?_
      simp only [hFdef, hF'def]
  have hmain := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (a := (0:ℝ)) (b := 1) (μ := volume)
    (F := F) (F' := F') (x₀ := s) (s := Set.Ioo (s - δ) (s + δ))
    (bound := fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹ * C)
    (isOpen_Ioo.mem_nhds ⟨sub_lt_self _ hδ, lt_add_of_pos_right _ hδ⟩)
    hF_meas hF_int hF'_meas h_bound hbound_int h_diff
  have hG : (fun x => ∫ τ in (0:ℝ)..1, F x τ) =ᶠ[𝓝 s]
      fun u : ℝ => G2 n h u σ (z 0) (z 1) (z 2) (z 3) := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨sub_lt_self _ hδ, lt_add_of_pos_right _ hδ⟩] with x hx
    funext i
    have hint : IntervalIntegrable (F x) volume (0:ℝ) 1 := by
      refine (hw_int.mul_const C).mono_fun' ?_ ?_
      · exact hF_meas_all x
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with τ hτ
        by_cases h1 : τ = 1
        · subst h1
          have hz : F x 1 = 0 := by
            simp only [hFdef]
            have hx1 : x + 1 * (σ - x) = σ := by ring
            rw [hx1]
            norm_num
          rw [hz]
          simp
        have hτIco : τ ∈ Set.Ico (0:ℝ) 1 := by
          rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1), Set.mem_Ioc] at hτ
          exact ⟨le_of_lt hτ.1, lt_of_le_of_ne hτ.2 h1⟩
        have hK := hbdK x hx τ hτIco
        have hw : 0 ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
        calc ‖F x τ‖ = ‖(Real.sqrt (τ * (1 - τ)))⁻¹‖ *
              ‖Kvec n h (x + τ * (σ - x)) σ (z 0) (z 1) (z 2) (z 3)‖ := by
                simp only [hFdef, norm_smul]
          _ = (Real.sqrt (τ * (1 - τ)))⁻¹ *
              ‖Kvec n h (x + τ * (σ - x)) σ (z 0) (z 1) (z 2) (z 3)‖ := by
                rw [Real.norm_eq_abs, abs_of_nonneg hw]
          _ ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ * C := mul_le_mul_of_nonneg_left hK hw
    have hproj : (∫ τ in (0:ℝ)..1, F x τ) i = ∫ τ in (0:ℝ)..1, (F x τ) i := by
      have hcomp := ContinuousLinearMap.intervalIntegral_comp_comm
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i) hint
      simpa only [ContinuousLinearMap.proj_apply] using hcomp.symm
    rw [hproj, G2]
    refine intervalIntegral.integral_congr (fun τ hτ => ?_)
    simp only [hFdef, Pi.smul_apply, smul_eq_mul]
    rw [div_eq_mul_inv, mul_comm]
  rw [hG.hasDerivAt_iff] at hmain
  simpa only [hF'def] using hmain.2

/-- **Differentiation under the Abel integral for `G₂`.**  The derivative in the first slot of
`G₂` is the Abel-weighted integral of the derivative of the kernel. -/
theorem G2_deriv_eq_integral (n : ℕ) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    {s σ : ℝ} (hsσ : s < σ) (z : St) {δ C : ℝ} (hδ : 0 < δ)
    (hbdK : ∀ x ∈ Set.Ioo (s - δ) (s + δ), ∀ τ ∈ Set.Ico (0:ℝ) 1,
      ‖Kvec n h (x + τ * (σ - x)) σ (z 0) (z 1) (z 2) (z 3)‖ ≤ C)
    (hdiff : ∀ x ∈ Set.Ioo (s - δ) (s + δ), ∀ τ ∈ Set.Ico (0:ℝ) 1,
      DifferentiableAt ℝ (fun u : ℝ => Kvec n h u σ (z 0) (z 1) (z 2) (z 3)) (x + τ * (σ - x)))
    (hbound : ∀ x ∈ Set.Ioo (s - δ) (s + δ), ∀ τ ∈ Set.Icc (0:ℝ) 1,
      ‖(1 - τ) • deriv (fun u : ℝ => Kvec n h u σ (z 0) (z 1) (z 2) (z 3)) (x + τ * (σ - x))‖ ≤ C) :
    deriv (fun u : ℝ => G2 n h u σ (z 0) (z 1) (z 2) (z 3)) s =
      ∫ τ in (0:ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ •
        ((1 - τ) • deriv (fun u : ℝ => Kvec n h u σ (z 0) (z 1) (z 2) (z 3)) (s + τ * (σ - s))) :=
  (hasDerivAt_G2 n hh hsσ z hδ hbdK hdiff hbound).deriv

end

end Work.OddVolterra
