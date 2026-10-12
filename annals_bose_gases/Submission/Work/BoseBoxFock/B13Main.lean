import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.lintegral_fibre_one
import Submission.Work.BoseBoxFock.lintegral_fibre_p1
import Submission.Work.BoseBoxFock.lintegral_fibre_two_p
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.B13Main` — the `L²` bound on the one-slot fibre

This module develops the `L²` estimate of the block I/III fibre of the Fournais--Solovej `Q₂` row
(the target `Work.BoseBoxFock.block13_fibre_L2`).

The fibre integral is

`Gfun p Θ A B w y = ∫ x' : Fib1 p, ∫ u, star (Θ (fibreIns p.2 w x')) · A ((fibreIns p.2 w x') p.1)
   · star (B u) · Θ ((fibreIns p.2 w x')[p.1 ↦ y][p.2 ↦ u])`,

and the bound is proved in the following steps.

* the pointwise Cauchy--Schwarz in `x'` and in `u`, giving
  `‖Gfun w y‖² ≤ F1 w · G2 y`;
* the factorisation `∫⁻ w ∫⁻ y F1 w · G2 y = (∫⁻ w F1 w) · (∫⁻ y G2 y)`;
* the one-slot fibre identity `∫⁻ w F1 w = ∫⁻ x ‖Θ x‖²`;
* the two-slot fibre identity `∫⁻ y G2 y = (∫⁻ u ‖B u‖²) · ((∫⁻ a ‖A a‖²) · ∫⁻ x ‖Θ x‖²)`;
* the passage from `∫⁻` back to the Bochner integral.

Everything here is `sorry`-free.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {n : ℕ}

/-! ## 1. The fibre integral and its `ℝ≥0∞` pieces -/

/-- The block I/III fibre integrand, integrated over the free slot `p.2`, the free variable `y`
and the second free variable `u`. -/
def Gfun (p : Fin n × Fin n) (Θ : (Fin n → E3) → ℂ) (A B : E3 → ℂ) (w y : E3) : ℂ :=
  ∫ x' : Fib1 p, ∫ u : E3, star (Θ (fibreIns p.2 w x')) * A ((fibreIns p.2 w x') p.1)
    * star (B u) * Θ (Function.update (Function.update (fibreIns p.2 w x') p.1 y) p.2 u)

/-- `∫⁻ u, ‖B u‖²`, the `L²`-mass of the second factor. -/
def NB (B : E3 → ℂ) : ENNReal := ∫⁻ u : E3, ENNReal.ofReal (‖B u‖ ^ 2)

/-- `∫⁻ a, ‖A a‖²`, the `L²`-mass of the first factor. -/
def NA (A : E3 → ℂ) : ENNReal := ∫⁻ a : E3, ENNReal.ofReal (‖A a‖ ^ 2)

/-- `∫⁻ x, ‖Θ x‖²`, the `L²`-mass of the state. -/
def NE (Θ : (Fin n → E3) → ℂ) : ENNReal :=
  ∫⁻ x : Fin n → E3, ENNReal.ofReal (‖Θ x‖ ^ 2)

/-- The `w`-factor of the Cauchy--Schwarz bound. -/
def F1 (p : Fin n × Fin n) (Θ : (Fin n → E3) → ℂ) (w : E3) : ENNReal :=
  ∫⁻ x' : Fib1 p, ENNReal.ofReal (‖Θ (fibreIns p.2 w x')‖ ^ 2)

/-- The `y`-factor of the Cauchy--Schwarz bound. -/
def G2 (p : Fin n × Fin n) (hp : p.1 ≠ p.2) (A : E3 → ℂ) (Θ : (Fin n → E3) → ℂ)
    (c : ENNReal) (y : E3) : ENNReal :=
  ∫⁻ x' : Fib1 p, ENNReal.ofReal (‖A (x' ⟨p.1, hp⟩)‖ ^ 2)
    * (c * ∫⁻ u : E3, ENNReal.ofReal (‖Θ (upd2 p y u (res p x'))‖ ^ 2))

/-- The `x''`-integral of the `Θ`-insertion. -/
def M2 (p : Fin n × Fin n) (Θ : (Fin n → E3) → ℂ) (y : E3) : ENNReal :=
  ∫⁻ x'' : Fib2 p, ∫⁻ u : E3, ENNReal.ofReal (‖Θ (upd2 p y u x'')‖ ^ 2)

/-! ## 2. Measurability of the two factors -/

/-- Composing a strongly measurable `Θ` with a measurable map keeps a.e.-measurability. -/
theorem aemeasurable_ofReal_normSq_meas {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {Θ : (Fin n → E3) → ℂ} (hΘ : Measurable Θ) {g : α → Fin n → E3} (hg : Measurable g) :
    AEMeasurable (fun a => ENNReal.ofReal (‖Θ (g a)‖ ^ 2)) μ :=
  ((ENNReal.measurable_ofReal.comp ((continuous_norm.measurable.comp hΘ).pow_const 2)).comp
    hg).aemeasurable

theorem F1_aemeasurable (p : Fin n × Fin n) {Θ : (Fin n → E3) → ℂ} (hΘ : Measurable Θ) :
    AEMeasurable (F1 p Θ) volume := by
  have h : AEMeasurable
      (fun z : E3 × Fib1 p => ENNReal.ofReal (‖Θ (fibreIns p.2 z.1 z.2)‖ ^ 2))
      (volume.prod volume) :=
    aemeasurable_ofReal_normSq_meas _ hΘ (measurable_fibreIns_prod p)
  exact h.lintegral_prod_right

theorem G2_aemeasurable (p : Fin n × Fin n) (hp : p.1 ≠ p.2) {A : E3 → ℂ}
    {Θ : (Fin n → E3) → ℂ} (c : ENNReal)
    (hAproj : AEMeasurable (fun x' : Fib1 p => A (x' ⟨p.1, hp⟩)) volume)
    (hΘ : Measurable Θ) : AEMeasurable (G2 p hp A Θ c) volume := by
  have h1 : AEMeasurable
      (fun z : E3 × Fib1 p => ENNReal.ofReal (‖A (z.2 ⟨p.1, hp⟩)‖ ^ 2)) (volume.prod volume) :=
    (ENNReal.measurable_ofReal.comp_aemeasurable (hAproj.norm.pow_const 2)).comp_snd
  have h2 : AEMeasurable
      (fun z : E3 × Fib1 p =>
        ∫⁻ u : E3, ENNReal.ofReal (‖Θ (upd2 p z.1 u (res p z.2))‖ ^ 2)) (volume.prod volume) := by
    have h : AEMeasurable
        (fun q : (E3 × Fib1 p) × E3 =>
          ENNReal.ofReal (‖Θ (upd2 p q.1.1 q.2 (res p q.1.2))‖ ^ 2)) (volume.prod volume) :=
      aemeasurable_ofReal_normSq_meas _ hΘ (measurable_upd2_res' p)
    exact h.lintegral_prod_right
  have h3 : AEMeasurable
      (fun z : E3 × Fib1 p => ENNReal.ofReal (‖A (z.2 ⟨p.1, hp⟩)‖ ^ 2)
        * (c * ∫⁻ u : E3, ENNReal.ofReal (‖Θ (upd2 p z.1 u (res p z.2))‖ ^ 2)))
      (volume.prod volume) :=
    h1.mul (aemeasurable_const.mul h2)
  exact h3.lintegral_prod_right

/-! ## 3. The one-slot fibre identity -/

theorem F1_eq (p : Fin n × Fin n) {Θ : (Fin n → E3) → ℂ} (hΘ : Measurable Θ) :
    ∫⁻ w : E3, F1 p Θ w = NE Θ := by
  have h : AEMeasurable (fun x : Fin n → E3 => ENNReal.ofReal (‖Θ x‖ ^ 2)) volume :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hΘ.aemeasurable.norm.pow_const 2)
  have hmain := lintegral_fibre_one (a := p.2)
    (F := fun x : Fin n → E3 => ENNReal.ofReal (‖Θ x‖ ^ 2)) h
  simp only [F1, NE]
  exact hmain.symm

/-! ## 4. The two-slot fibre identity -/

theorem M2_eq_NE (p : Fin n × Fin n) (hp : p.1 ≠ p.2) {Θ : (Fin n → E3) → ℂ}
    (hΘ : Measurable Θ) :
    ∫⁻ y : E3, M2 p Θ y = NE Θ := by
  have hmeas : AEMeasurable (fun x : Fin n → E3 => ENNReal.ofReal (‖Θ x‖ ^ 2)) volume :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hΘ.aemeasurable.norm.pow_const 2)
  have hmain := lintegral_fibre_two_p p hp
    (F := fun x : Fin n → E3 => ENNReal.ofReal (‖Θ x‖ ^ 2)) hmeas
  -- inner swap `x'' ↔ u` for fixed `y`
  have hinner : ∀ y : E3, (∫⁻ x'' : Fib2 p, ∫⁻ u : E3,
        ENNReal.ofReal (‖Θ (upd2 p y u x'')‖ ^ 2))
      = ∫⁻ u : E3, ∫⁻ x'' : Fib2 p, ENNReal.ofReal (‖Θ (upd2 p y u x'')‖ ^ 2) := by
    intro y
    refine lintegral_lintegral_swap ?_
    refine aemeasurable_ofReal_normSq_meas _ hΘ ?_
    refine measurable_pi_iff.mpr (fun k => ?_)
    by_cases h2 : k = p.2
    · simp only [upd2, dif_pos h2]
      exact measurable_snd
    · by_cases h1 : k = p.1
      · simp only [upd2, dif_neg h2, dif_pos h1]
        exact measurable_const
      · simp only [upd2, dif_neg h2, dif_neg h1]
        show Measurable (fun q : Fib2 p × E3 => q.1 ⟨k, h2, h1⟩)
        exact (measurable_pi_apply (⟨k, h2, h1⟩ : I2 p)).comp measurable_fst
  -- outer swap `y ↔ u`
  have houter : (∫⁻ y : E3, ∫⁻ u : E3, ∫⁻ x'' : Fib2 p,
        ENNReal.ofReal (‖Θ (upd2 p y u x'')‖ ^ 2))
      = ∫⁻ u : E3, ∫⁻ y : E3, ∫⁻ x'' : Fib2 p,
          ENNReal.ofReal (‖Θ (upd2 p y u x'')‖ ^ 2) := by
    refine lintegral_lintegral_swap ?_
    have h'' : AEMeasurable
        (fun q : (E3 × E3) × Fib2 p => ENNReal.ofReal (‖Θ (upd2 p q.1.1 q.1.2 q.2)‖ ^ 2))
        (volume.prod volume) := by
      refine aemeasurable_ofReal_normSq_meas _ hΘ ?_
      refine measurable_pi_iff.mpr (fun k => ?_)
      by_cases h2 : k = p.2
      · simp only [upd2, dif_pos h2]
        exact measurable_fst.snd
      · by_cases h1 : k = p.1
        · simp only [upd2, dif_neg h2, dif_pos h1]
          exact measurable_fst.fst
        · simp only [upd2, dif_neg h2, dif_neg h1]
          show Measurable (fun q : (E3 × E3) × Fib2 p => q.2 ⟨k, h2, h1⟩)
          exact (measurable_pi_apply (⟨k, h2, h1⟩ : I2 p)).comp measurable_snd
    exact h''.lintegral_prod_right
  simp only [M2]
  rw [lintegral_congr hinner, houter]
  exact hmain.symm

/-! ## 5. The pointwise Cauchy--Schwarz bound -/

/-- The pointwise bound `‖Gfun w y‖² ≤ F1 w · G2 y`. -/
theorem pointwise_bound (p : Fin n × Fin n) (hp : p.1 ≠ p.2) {Θ : (Fin n → E3) → ℂ}
    (A B : E3 → ℂ) (hΘm : Measurable Θ)
    (hAproj : AEMeasurable (fun x' : Fib1 p => A (x' ⟨p.1, hp⟩)) volume)
    (hBm : AEMeasurable B volume) (w y : E3) :
    ENNReal.ofReal (‖Gfun p Θ A B w y‖ ^ 2) ≤ F1 p Θ w * G2 p hp A Θ (NB B) y := by
  -- (a) reassociate the `u`-integral
  have hG : Gfun p Θ A B w y = ∫ x' : Fib1 p, star (Θ (fibreIns p.2 w x'))
      * (A (x' ⟨p.1, hp⟩) * ∫ u : E3, star (B u) * Θ (upd2 p y u (res p x'))) := by
    rw [Gfun]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x' => ?_)
    beta_reduce
    have hu : (fun u : E3 => star (Θ (fibreIns p.2 w x')) * A ((fibreIns p.2 w x') p.1)
          * star (B u) * Θ (Function.update (Function.update (fibreIns p.2 w x') p.1 y) p.2 u))
        = fun u : E3 => (star (Θ (fibreIns p.2 w x')) * A (x' ⟨p.1, hp⟩))
            * (star (B u) * Θ (upd2 p y u (res p x'))) := by
      funext u
      rw [fibreIns_apply_p1 (hp := hp), update_update_fibreIns (hp := hp)]
      ring
    rw [hu, MeasureTheory.integral_const_mul]
    ring
  -- (b) Cauchy--Schwarz in `u`
  have hZ : ∀ x' : Fib1 p,
      ENNReal.ofReal (‖∫ u : E3, star (B u) * Θ (upd2 p y u (res p x'))‖ ^ 2)
        ≤ NB B * (∫⁻ u : E3, ENNReal.ofReal (‖Θ (upd2 p y u (res p x'))‖ ^ 2)) := by
    intro x'
    have h1 : AEMeasurable (fun u : E3 => star (B u)) volume :=
      continuous_star.measurable.comp_aemeasurable hBm
    have h2 : AEMeasurable (fun u : E3 => Θ (upd2 p y u (res p x'))) volume := by
      have hmeas : Measurable (fun u : E3 => upd2 p y u (res p x')) := by
        refine measurable_pi_iff.mpr (fun k => ?_)
        by_cases h2 : k = p.2
        · simp only [upd2, dif_pos h2]
          exact measurable_id
        · by_cases h1 : k = p.1
          · simp only [upd2, dif_neg h2, dif_pos h1]
            exact measurable_const
          · simp only [upd2, dif_neg h2, dif_neg h1]
            show Measurable (fun _ : E3 => res p x' ⟨k, h2, h1⟩)
            exact measurable_const
      exact (hΘm.comp hmeas).aemeasurable
    have h := ofReal_norm_integral_mul_sq_le h1 h2
    simpa [NB, norm_star] using h
  -- (c) Cauchy--Schwarz in `x'`
  have hZmeas : AEMeasurable
      (fun x' : Fib1 p => ∫ u : E3, star (B u) * Θ (upd2 p y u (res p x'))) volume := by
    have huncur : AEStronglyMeasurable
        (fun q : Fib1 p × E3 => star (B q.2) * Θ (upd2 p y q.2 (res p q.1)))
        (volume.prod volume) :=
      ((continuous_star.measurable.comp_aemeasurable hBm.comp_snd).aestronglyMeasurable).mul
        ((hΘm.comp (measurable_upd2_res p y)).aestronglyMeasurable)
    exact huncur.integral_prod_right'.aemeasurable
  have hf : AEMeasurable (fun x' : Fib1 p => star (Θ (fibreIns p.2 w x'))) volume :=
    (continuous_star.measurable.comp (hΘm.comp (measurable_fibreIns_fixed p w))).aemeasurable
  have hg : AEMeasurable (fun x' : Fib1 p => A (x' ⟨p.1, hp⟩)
      * ∫ u : E3, star (B u) * Θ (upd2 p y u (res p x'))) volume := hAproj.mul hZmeas
  -- the first factor of the bound
  have hf_eq : (∫⁻ x' : Fib1 p, ENNReal.ofReal (‖star (Θ (fibreIns p.2 w x'))‖ ^ 2))
      = F1 p Θ w := by
    rw [F1]
    refine lintegral_congr fun x' => ?_
    rw [norm_star]
  -- the second factor of the bound
  have hg_le : (∫⁻ x' : Fib1 p, ENNReal.ofReal (‖A (x' ⟨p.1, hp⟩)
        * (∫ u : E3, star (B u) * Θ (upd2 p y u (res p x')))‖ ^ 2))
      ≤ G2 p hp A Θ (NB B) y := by
    rw [G2]
    refine lintegral_mono fun x' => ?_
    calc ENNReal.ofReal (‖A (x' ⟨p.1, hp⟩)
            * (∫ u : E3, star (B u) * Θ (upd2 p y u (res p x')))‖ ^ 2)
        = ENNReal.ofReal (‖A (x' ⟨p.1, hp⟩)‖ ^ 2)
            * ENNReal.ofReal (‖∫ u : E3, star (B u) * Θ (upd2 p y u (res p x'))‖ ^ 2) := by
          rw [norm_mul, mul_pow, ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal (‖A (x' ⟨p.1, hp⟩)‖ ^ 2)
            * (NB B * ∫⁻ u : E3, ENNReal.ofReal (‖Θ (upd2 p y u (res p x'))‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left (hZ x') (by positivity)
  rw [hG]
  refine (ofReal_norm_integral_mul_sq_le hf hg).trans ?_
  rw [hf_eq]
  exact mul_le_mul_of_nonneg_left hg_le (by positivity)

/-! ## 6. The `ℝ≥0∞` assembly -/

theorem ennreal_bound (p : Fin n × Fin n) (hp : p.1 ≠ p.2) {Θ : (Fin n → E3) → ℂ}
    (A B : E3 → ℂ) (hΘm : Measurable Θ)
    (hAproj : AEMeasurable (fun x' : Fib1 p => A (x' ⟨p.1, hp⟩)) volume)
    (hBm : AEMeasurable B volume)
    (hG2 : ∫⁻ y : E3, G2 p hp A Θ (NB B) y = NB B * (NA A * NE Θ)) :
    ∫⁻ w : E3, ∫⁻ y : E3, ENNReal.ofReal (‖Gfun p Θ A B w y‖ ^ 2)
      ≤ NE Θ * (NB B * (NA A * NE Θ)) := by
  have hF1 : AEMeasurable (F1 p Θ) volume := F1_aemeasurable p hΘm
  have hG2m : AEMeasurable (G2 p hp A Θ (NB B)) volume := G2_aemeasurable p hp (NB B) hAproj hΘm
  have h1 : ∫⁻ w : E3, ∫⁻ y : E3, ENNReal.ofReal (‖Gfun p Θ A B w y‖ ^ 2)
      ≤ ∫⁻ w : E3, ∫⁻ y : E3, F1 p Θ w * G2 p hp A Θ (NB B) y :=
    lintegral_mono fun w => lintegral_mono fun y => pointwise_bound p hp A B hΘm hAproj hBm w y
  have h2 : ∫⁻ w : E3, ∫⁻ y : E3, F1 p Θ w * G2 p hp A Θ (NB B) y
      = (∫⁻ w : E3, F1 p Θ w) * (∫⁻ y : E3, G2 p hp A Θ (NB B) y) := by
    have hmeas : AEMeasurable
        (fun z : E3 × E3 => F1 p Θ z.1 * G2 p hp A Θ (NB B) z.2) (volume.prod volume) :=
      hF1.comp_fst.mul hG2m.comp_snd
    rw [← lintegral_prod (fun z : E3 × E3 => F1 p Θ z.1 * G2 p hp A Θ (NB B) z.2) hmeas]
    exact lintegral_prod_mul hF1 hG2m
  calc ∫⁻ w : E3, ∫⁻ y : E3, ENNReal.ofReal (‖Gfun p Θ A B w y‖ ^ 2)
      ≤ (∫⁻ w : E3, F1 p Θ w) * (∫⁻ y : E3, G2 p hp A Θ (NB B) y) := h1.trans h2.le
    _ = NE Θ * (NB B * (NA A * NE Θ)) := by rw [F1_eq p hΘm, hG2]

/-! ## 7. From the `ℝ≥0∞` chain back to the Bochner integral -/

theorem ofReal_integral_le_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : 0 ≤ f) :
    ENNReal.ofReal (∫ a, f a ∂μ) ≤ ∫⁻ a, ENNReal.ofReal (f a) ∂μ := by
  have hnn : 0 ≤ ∫ a, f a ∂μ := integral_nonneg hf
  calc ENNReal.ofReal (∫ a, f a ∂μ) = ENNReal.ofReal ‖∫ a, f a ∂μ‖ := by
        rw [Real.norm_of_nonneg hnn]
    _ ≤ ∫⁻ a, ENNReal.ofReal ‖f a‖ ∂μ :=
        ENNReal.ofReal_le_of_le_toReal (norm_integral_le_lintegral_norm f)
    _ = ∫⁻ a, ENNReal.ofReal (f a) ∂μ := lintegral_congr fun a => by
        rw [Real.norm_of_nonneg (hf a)]

/-! ## 8. The Bochner-integral form of the bound -/

theorem block13_core (p : Fin n × Fin n) (hp : p.1 ≠ p.2) {Θ : (Fin n → E3) → ℂ}
    (A B : E3 → ℂ) (hΘm : Measurable Θ) (hΘL : Integrable (fun x => ‖Θ x‖ ^ 2))
    (hAL : Integrable (fun x => ‖A x‖ ^ 2)) (hBL : Integrable (fun x => ‖B x‖ ^ 2))
    (hAproj : AEMeasurable (fun x' : Fib1 p => A (x' ⟨p.1, hp⟩)) volume)
    (hBm : AEMeasurable B volume)
    (hG2 : ∫⁻ y : E3, G2 p hp A Θ (NB B) y = NB B * (NA A * NE Θ)) :
    ∫ w : E3, ∫ y : E3, ‖Gfun p Θ A B w y‖ ^ 2
      ≤ (∫ x : E3, ‖A x‖ ^ 2) * (∫ x : E3, ‖B x‖ ^ 2)
        * (∫ x : Fin n → E3, ‖Θ x‖ ^ 2) ^ 2 := by
  have hbridge : ENNReal.ofReal (∫ w : E3, ∫ y : E3, ‖Gfun p Θ A B w y‖ ^ 2)
      ≤ ∫⁻ w : E3, ∫⁻ y : E3, ENNReal.ofReal (‖Gfun p Θ A B w y‖ ^ 2) := by
    refine (ofReal_integral_le_lintegral (fun w => ?_)).trans ?_
    · exact integral_nonneg fun y => by positivity
    · exact lintegral_mono fun w => ofReal_integral_le_lintegral (fun y => by positivity)
  have hNE : NE Θ = ENNReal.ofReal (∫ x : Fin n → E3, ‖Θ x‖ ^ 2) :=
    (ofReal_integral_eq_lintegral_ofReal hΘL
      (Filter.Eventually.of_forall fun x => by positivity)).symm
  have hNB : NB B = ENNReal.ofReal (∫ x : E3, ‖B x‖ ^ 2) :=
    (ofReal_integral_eq_lintegral_ofReal hBL
      (Filter.Eventually.of_forall fun x => by positivity)).symm
  have hNA : NA A = ENNReal.ofReal (∫ x : E3, ‖A x‖ ^ 2) :=
    (ofReal_integral_eq_lintegral_ofReal hAL
      (Filter.Eventually.of_forall fun x => by positivity)).symm
  have hmain := hbridge.trans (ennreal_bound p hp A B hΘm hAproj hBm hG2)
  rw [hNE, hNB, hNA] at hmain
  have hprod : ENNReal.ofReal ((∫ x : E3, ‖A x‖ ^ 2) * (∫ x : E3, ‖B x‖ ^ 2)
        * (∫ x : Fin n → E3, ‖Θ x‖ ^ 2) ^ 2)
      = ENNReal.ofReal (∫ x : Fin n → E3, ‖Θ x‖ ^ 2)
        * (ENNReal.ofReal (∫ x : E3, ‖B x‖ ^ 2)
          * (ENNReal.ofReal (∫ x : E3, ‖A x‖ ^ 2)
            * ENNReal.ofReal (∫ x : Fin n → E3, ‖Θ x‖ ^ 2))) := by
    rw [show (∫ x : E3, ‖A x‖ ^ 2) * (∫ x : E3, ‖B x‖ ^ 2)
          * (∫ x : Fin n → E3, ‖Θ x‖ ^ 2) ^ 2
        = (∫ x : Fin n → E3, ‖Θ x‖ ^ 2)
          * ((∫ x : E3, ‖B x‖ ^ 2)
            * ((∫ x : E3, ‖A x‖ ^ 2) * (∫ x : Fin n → E3, ‖Θ x‖ ^ 2))) from by ring]
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by positivity)]
  rw [← hprod] at hmain
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hmain

end Work.BoseBoxFock
