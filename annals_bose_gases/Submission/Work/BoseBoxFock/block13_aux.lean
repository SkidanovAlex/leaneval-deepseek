import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.pairRowS3Defs
import Submission.Work.BoseBoxFock.qmqDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.block13_aux` — the analytic toolbox of the block-I dictionary

Definitions and auxiliary lemmas for `Work.BoseBoxFock.block13_dict`.  The dictionary identity

    ℓ⁻³·re (rowShape13 Θ (c·θ) (c·θ) (qmqKernel ℓ k) p)
      = ∫_{abox n ℓ} (P_{p.1}Q_{p.2}Ψ)·(P_{p.2}Q_{p.1}Ψ)·k(x_{p.1},x_{p.2})

is proved in three steps, the second of which (`block13_main`) is stated here for an **arbitrary**
measurable bounded state `Th` (no support hypothesis is needed):

* the slot means `Pᵢ` (`Submission.BoseGases.aP`) are the box means; their algebra for
  measurable bounded states is `Work.BoseBoxFock.Weak`;
* the kernel `qmqKernel ℓ k = (1−P)M_k(1−P)` (as a kernel) expands, under symmetry of `k`, as
  `k w y − κ w − κ y + kk` with the one-slot mean `κ = kRow ℓ k` and the two-slot mean
  `kk = kAvg ℓ k`;
* the identity then follows by four applications of the self-adjointness `Weak.aP_sym_box`
  (plus the pointwise independence of `C = P_{p.1}P_{p.2}Th` from both slots and of
  `P_{p.1}(κ(·)P_{p.2}Th)` from the `p.2`-slot).

Everything here is complete and axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

local notation "Xn" => Submission.BoseGases.X
local notation "abx" => Submission.BoseGases.abox
local notation "acb" => Submission.BoseGases.acube
local notation "aP" => Submission.BoseGases.aP
local notation "aQ" => Submission.BoseGases.aQ

set_option autoImplicit false

/-! ## 0. Nonnegative uniform bounds -/

lemma exists_bound_nonneg {n : ℕ} {f : Submission.BoseGases.X n → ℝ}
    (h : ∃ C : ℝ, ∀ x, |f x| ≤ C) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |f x| ≤ C := by
  obtain ⟨C, hC⟩ := h
  exact ⟨max C 0, le_max_right _ _, fun x => le_trans (hC x) (le_max_left _ _)⟩

lemma exists_bound_nonneg2 {α β : Type*} {f : α → β → ℝ}
    (h : ∃ C : ℝ, ∀ a b, |f a b| ≤ C) : ∃ C : ℝ, 0 ≤ C ∧ ∀ a b, |f a b| ≤ C := by
  obtain ⟨C, hC⟩ := h
  exact ⟨max C 0, le_max_right _ _, fun a b => le_trans (hC a b) (le_max_left _ _)⟩

/-- A measurable function bounded on the box is integrable on it. -/
lemma integrableOn_of_bound_box {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {F : Submission.BoseGases.X n → ℝ}
    {C : ℝ} (hFm : Measurable F) (hFb : ∀ x, |F x| ≤ C) :
    IntegrableOn F (Submission.BoseGases.abox n ℓ) volume :=
  IntegrableOn.of_bound (Submission.BoseGases.abox_lt_top n ℓ hℓ.le)
    hFm.aestronglyMeasurable C (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hFb x)

/-! ## 1. The real box restriction -/

/-- The real box restriction `Φ·1_{abox n ℓ}` of a state. -/
noncomputable def boxRestrR {n : ℕ} (ℓ : ℝ) (Φ : Submission.BoseGases.X n → ℝ) :
    Submission.BoseGases.X n → ℝ :=
  fun x => Φ x * (Submission.BoseGases.abox n ℓ).indicator (fun _ => (1 : ℝ)) x

lemma boxRestrR_eq_of_mem {n : ℕ} {ℓ : ℝ} {Φ : Submission.BoseGases.X n → ℝ}
    {x : Submission.BoseGases.X n} (hx : x ∈ Submission.BoseGases.abox n ℓ) :
    boxRestrR ℓ Φ x = Φ x := by
  unfold boxRestrR
  rw [Set.indicator_of_mem hx (fun _ => (1 : ℝ)), mul_one]

lemma boxRestrR_eq_zero_of_notMem {n : ℕ} {ℓ : ℝ} {Φ : Submission.BoseGases.X n → ℝ}
    {x : Submission.BoseGases.X n} (hx : x ∉ Submission.BoseGases.abox n ℓ) :
    boxRestrR ℓ Φ x = 0 := by
  unfold boxRestrR
  rw [Set.indicator_of_notMem hx (fun _ => (1 : ℝ)), mul_zero]

lemma boxRestrR_measurable {n : ℕ} {ℓ : ℝ} {Φ : Submission.BoseGases.X n → ℝ}
    (hΦm : Measurable Φ) : Measurable (boxRestrR ℓ Φ) :=
  hΦm.mul (Measurable.indicator measurable_const (Submission.BoseGases.abox_measurable n ℓ))

lemma boxRestrR_support {n : ℕ} (ℓ : ℝ) (Φ : Submission.BoseGases.X n → ℝ) :
    Function.support (boxRestrR ℓ Φ) ⊆ Submission.BoseGases.abox n ℓ := by
  intro x hx
  by_contra h
  exact hx (boxRestrR_eq_zero_of_notMem h)

lemma boxRestrR_support_boxPow {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (Φ : Submission.BoseGases.X n → ℝ) :
    Function.support (boxRestrR ℓ Φ) ⊆ Work.MB.boxPow n ℓ := by
  have hA : Submission.BoseGases.acube ℓ = Work.BoseK15.corpusBox.boxL ℓ :=
    (boxL_eq_acube hℓ).symm
  intro x hx
  have hx' := boxRestrR_support ℓ Φ hx
  rw [Work.MB.boxPow, Set.mem_univ_pi]
  intro i
  exact hA ▸ ((Submission.BoseGases.mem_abox_iff n ℓ x).mp hx' i)

lemma boxRestrR_abs_le {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : Submission.BoseGases.X n → ℝ}
    (hΦc : Continuous Φ) : ∃ C : ℝ, ∀ x, |boxRestrR ℓ Φ x| ≤ C := by
  obtain ⟨C, hC⟩ := (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn
    (f := Φ) hΦc.continuousOn
  refine ⟨max C 0, fun x => ?_⟩
  by_cases hx : x ∈ Submission.BoseGases.abox n ℓ
  · rw [boxRestrR_eq_of_mem hx]
    exact le_trans (by simpa [Real.norm_eq_abs] using hC x hx) (le_max_left C 0)
  · rw [boxRestrR_eq_zero_of_notMem hx, abs_zero]
    exact le_max_right C 0

/-! ## 2. The real `Q M Q` kernel and its means -/

/-- The real kernel whose cast is `qmqKernel ℓ k`. -/
noncomputable def qmqKernelR (ℓ : ℝ) (k : E3 → E3 → ℝ) (w y : E3) : ℝ :=
  k w y
    - (ℓ ^ 3)⁻¹ * (∫ y' in Submission.BoseGases.acube ℓ, k w y')
    - (ℓ ^ 3)⁻¹ * (∫ w' in Submission.BoseGases.acube ℓ, k w' y)
    + ((ℓ ^ 3)⁻¹) ^ 2
        * (∫ w' in Submission.BoseGases.acube ℓ,
            ∫ y' in Submission.BoseGases.acube ℓ, k w' y')

/-- The one-slot mean `κ w = ℓ⁻³∫_{acube} k w ·`. -/
noncomputable def kRow (ℓ : ℝ) (k : E3 → E3 → ℝ) (w : E3) : ℝ :=
  (ℓ ^ 3)⁻¹ * ∫ y in Submission.BoseGases.acube ℓ, k w y

/-- The two-slot mean `kk = ℓ⁻⁶∬ k = ℓ⁻³∫ κ`. -/
noncomputable def kAvg (ℓ : ℝ) (k : E3 → E3 → ℝ) : ℝ :=
  (ℓ ^ 3)⁻¹ * ∫ w in Submission.BoseGases.acube ℓ, kRow ℓ k w

/-- The kernel `qmqKernel ℓ k` is the cast of the real kernel `qmqKernelR ℓ k`. -/
theorem qmqKernel_eq_ofReal (ℓ : ℝ) (k : E3 → E3 → ℝ) (w y : E3) :
    qmqKernel ℓ k w y = ((qmqKernelR ℓ k w y : ℝ) : ℂ) := by
  have hB : (∫ y' in Submission.BoseGases.acube ℓ, ((k w y' : ℝ) : ℂ))
      = ((∫ y' in Submission.BoseGases.acube ℓ, k w y' : ℝ) : ℂ) := integral_ofReal
  have hC : (∫ w' in Submission.BoseGases.acube ℓ, ((k w' y : ℝ) : ℂ))
      = ((∫ w' in Submission.BoseGases.acube ℓ, k w' y : ℝ) : ℂ) := integral_ofReal
  have hD : (∫ w' in Submission.BoseGases.acube ℓ,
        ∫ y' in Submission.BoseGases.acube ℓ, ((k w' y' : ℝ) : ℂ))
      = ((∫ w' in Submission.BoseGases.acube ℓ,
          ∫ y' in Submission.BoseGases.acube ℓ, k w' y' : ℝ) : ℂ) := by
    rw [show (∫ w' in Submission.BoseGases.acube ℓ,
          ∫ y' in Submission.BoseGases.acube ℓ, ((k w' y' : ℝ) : ℂ))
        = ∫ w' in Submission.BoseGases.acube ℓ,
            ((∫ y' in Submission.BoseGases.acube ℓ, k w' y' : ℝ) : ℂ) from by
      refine integral_congr_ae (Filter.Eventually.of_forall fun w' => ?_)
      exact integral_ofReal]
    exact integral_ofReal
  rw [qmqKernel, qmqRowB, qmqRowC, qmqRowD, qmqKernelR, hB, hC, hD]
  push_cast
  ring

theorem kAvg_eq (ℓ : ℝ) (k : E3 → E3 → ℝ) :
    kAvg ℓ k
      = ((ℓ ^ 3)⁻¹) ^ 2
          * (∫ w' in Submission.BoseGases.acube ℓ,
              ∫ y' in Submission.BoseGases.acube ℓ, k w' y') := by
  unfold kAvg kRow
  rw [MeasureTheory.integral_const_mul]
  ring

/-- The expansion of the real kernel under symmetry of `k`. -/
theorem qmqKernelR_eq (ℓ : ℝ) {k : E3 → E3 → ℝ} (hksym : ∀ w y, k w y = k y w)
    (w y : E3) :
    qmqKernelR ℓ k w y = k w y - kRow ℓ k w - kRow ℓ k y + kAvg ℓ k := by
  have hrow : (∫ w' in Submission.BoseGases.acube ℓ, k w' y)
      = ∫ w' in Submission.BoseGases.acube ℓ, k y w' := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun w' => ?_)
    exact hksym w' y
  simp only [qmqKernelR, kRow, kAvg_eq]
  rw [hrow]

/-! ## 3. Slot independence -/

/-- **A function independent of the `i`-th coordinate is its own `i`-th slot mean.** -/
lemma aP_eq_self_of_indep {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin n)
    {F : Submission.BoseGases.X n → ℝ}
    (hF : ∀ x z, F (Function.update x i z) = F x) (x : Submission.BoseGases.X n) :
    Submission.BoseGases.aP ℓ i F x = F x := by
  rw [Submission.BoseGases.aP]
  rw [show (fun y : E3 => F (Function.update x i y)) = fun _ : E3 => F x from
    funext fun y => hF x y]
  rw [Submission.BoseGases.integral_const_acube ℓ hℓ (F x)]
  field_simp

/-- **The `i`-th slot mean of a function independent of the `j`-th coordinate stays
independent of the `j`-th coordinate.** -/
lemma aP_indep_of_indep {n : ℕ} {ℓ : ℝ} {i j : Fin n} (hij : i ≠ j)
    {F : Submission.BoseGases.X n → ℝ} (hF : ∀ x z, F (Function.update x j z) = F x) :
    ∀ x z, Submission.BoseGases.aP ℓ i F (Function.update x j z) = Submission.BoseGases.aP ℓ i F x := by
  intro x z
  unfold Submission.BoseGases.aP
  congr 1
  apply integral_congr_ae
  filter_upwards with y
  rw [Function.update_comm (Ne.symm hij)]
  exact hF (Function.update x i y) z

/-- **Pulling a factor independent of the `i`-th coordinate out of the slot mean.** -/
lemma aP_mul_of_indep {n : ℕ} {ℓ : ℝ} (i : Fin n) {F : Submission.BoseGases.X n → ℝ}
    (hF : ∀ x z, F (Function.update x i z) = F x) (G : Submission.BoseGases.X n → ℝ)
    (x : Submission.BoseGases.X n) :
    Submission.BoseGases.aP ℓ i (fun y => F y * G y) x = F x * Submission.BoseGases.aP ℓ i G x := by
  rw [Submission.BoseGases.aP, Submission.BoseGases.aP]
  have hmain : (∫ y in Submission.BoseGases.acube ℓ,
        F (Function.update x i y) * G (Function.update x i y))
      = F x * ∫ y in Submission.BoseGases.acube ℓ, G (Function.update x i y) := by
    rw [← MeasureTheory.integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    rw [hF x y]
  rw [hmain]
  ring

/-! ## 4. Measurability and bounds for the kernel means -/

lemma kRow_measurable {ℓ : ℝ} {k : E3 → E3 → ℝ} (hkm : Measurable (Function.uncurry k)) :
    Measurable (kRow ℓ k) := by
  unfold kRow
  have h : StronglyMeasurable (fun w : E3 => ∫ y, k w y
      ∂((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))) :=
    hkm.stronglyMeasurable.integral_prod_right
  exact (h.measurable).const_mul _

lemma kRow_abs_le {ℓ : ℝ} (hℓ : 0 < ℓ) {k : E3 → E3 → ℝ} {CK : ℝ} (hCK0 : 0 ≤ CK)
    (hCK : ∀ w y, |k w y| ≤ CK) (w : E3) : |kRow ℓ k w| ≤ CK := by
  have hvol : (volume : Measure E3).real (Submission.BoseGases.acube ℓ) = ℓ ^ 3 := by
    rw [MeasureTheory.Measure.real_def,
      ← ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ ℓ ^ 3),
      ← Submission.BoseGases.acube_volume ℓ hℓ.le]
  have h2 : |∫ y in Submission.BoseGases.acube ℓ, k w y| ≤ CK * ℓ ^ 3 := by
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume)
      (s := Submission.BoseGases.acube ℓ) (f := fun y => k w y) (C := CK)
      (Submission.BoseGases.acube_lt_top ℓ hℓ.le) (fun y _ => by
        simpa [Real.norm_eq_abs] using hCK w y)
    rw [hvol] at h
    simpa [Real.norm_eq_abs] using h
  calc |kRow ℓ k w| = (ℓ ^ 3)⁻¹ * |∫ y in Submission.BoseGases.acube ℓ, k w y| := by
        unfold kRow
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (ℓ ^ 3)⁻¹)]
    _ ≤ (ℓ ^ 3)⁻¹ * (CK * ℓ ^ 3) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = CK := by field_simp

lemma kAvg_abs_le {ℓ : ℝ} (hℓ : 0 < ℓ) {k : E3 → E3 → ℝ} {CK : ℝ} (hCK0 : 0 ≤ CK)
    (hCK : ∀ w y, |k w y| ≤ CK) : |kAvg ℓ k| ≤ CK := by
  have hvol : (volume : Measure E3).real (Submission.BoseGases.acube ℓ) = ℓ ^ 3 := by
    rw [MeasureTheory.Measure.real_def,
      ← ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ ℓ ^ 3),
      ← Submission.BoseGases.acube_volume ℓ hℓ.le]
  have h2 : |∫ w in Submission.BoseGases.acube ℓ, kRow ℓ k w| ≤ CK * ℓ ^ 3 := by
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume)
      (s := Submission.BoseGases.acube ℓ) (f := fun w => kRow ℓ k w) (C := CK)
      (Submission.BoseGases.acube_lt_top ℓ hℓ.le) (fun w _ => by
        simpa [Real.norm_eq_abs] using kRow_abs_le hℓ hCK0 hCK w)
    rw [hvol] at h
    simpa [Real.norm_eq_abs] using h
  calc |kAvg ℓ k| = (ℓ ^ 3)⁻¹ * |∫ w in Submission.BoseGases.acube ℓ, kRow ℓ k w| := by
        unfold kAvg
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (ℓ ^ 3)⁻¹)]
    _ ≤ (ℓ ^ 3)⁻¹ * (CK * ℓ ^ 3) := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = CK := by field_simp

/-- A measurable pair of bounded functions on the cube is integrable on the cube. -/
lemma integrable_acube_of_bound {ℓ : ℝ} (hℓ : 0 < ℓ) {f : E3 → ℝ} {C : ℝ}
    (hfm : Measurable f) (hfb : ∀ y, |f y| ≤ C) :
    Integrable f ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) :=
  Integrable.of_bound hfm.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hfb y)

lemma integrable_acube_mul_of_bound {ℓ : ℝ} (hℓ : 0 < ℓ) {f g : E3 → ℝ} {a b : ℝ}
    (hfm : Measurable f) (hfb : ∀ y, |f y| ≤ a) (hgm : Measurable g) (hgb : ∀ y, |g y| ≤ b) :
    Integrable (fun y => f y * g y)
      ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) :=
  integrable_acube_of_bound hℓ (hfm.mul hgm) (fun y => by
    rw [abs_mul]
    exact mul_le_mul (hfb y) (hgb y) (abs_nonneg _) (le_trans (abs_nonneg _) (hfb y)))

lemma integrableOn_abox_mul_of_bound {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {f g : Xn n → ℝ} {a b : ℝ}
    (hfm : Measurable f) (hfb : ∀ y, |f y| ≤ a) (hgm : Measurable g) (hgb : ∀ y, |g y| ≤ b) :
    IntegrableOn (fun y => f y * g y) (abx n ℓ) volume :=
  integrableOn_of_bound_box hℓ (hfm.mul hgm) (fun y => by
    rw [abs_mul]
    exact mul_le_mul (hfb y) (hgb y) (abs_nonneg _) (le_trans (abs_nonneg _) (hfb y)))

lemma integrableOn_abox_mul3_of_bound {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {f g h : Xn n → ℝ} {a b c : ℝ}
    (hfm : Measurable f) (hfb : ∀ y, |f y| ≤ a) (hgm : Measurable g) (hgb : ∀ y, |g y| ≤ b)
    (hhm : Measurable h) (hhb : ∀ y, |h y| ≤ c) :
    IntegrableOn (fun y => f y * g y * h y) (abx n ℓ) volume :=
  integrableOn_abox_mul_of_bound hℓ (hfm.mul hgm)
    (fun y => by
      rw [abs_mul]
      exact mul_le_mul (hfb y) (hgb y) (abs_nonneg _) (le_trans (abs_nonneg _) (hfb y)))
    hhm hhb

/-! ## 5. The pointwise expansion of `aP` at the `Q M Q` kernel -/

lemma aP_qmqKernelR {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Th : Xn n → ℝ}
    (hThm : Measurable Th) (hThb : ∃ C : ℝ, ∀ x, |Th x| ≤ C)
    {k : E3 → E3 → ℝ} (hkm : Measurable (Function.uncurry k))
    (hkb : ∃ C : ℝ, ∀ w y, |k w y| ≤ C) (hksym : ∀ w y, k w y = k y w)
    {p : Fin n × Fin n} (hp : p.1 ≠ p.2) (x : Xn n) :
    aP ℓ p.1 (fun z => qmqKernelR ℓ k (z p.2) (z p.1) * aP ℓ p.2 Th z) x
      = aP ℓ p.1 (fun z => k (z p.2) (z p.1) * aP ℓ p.2 Th z) x
        - kRow ℓ k (x p.2) * aP ℓ p.1 (aP ℓ p.2 Th) x
        - aP ℓ p.1 (fun z => kRow ℓ k (z p.1) * aP ℓ p.2 Th z) x
        + kAvg ℓ k * aP ℓ p.1 (aP ℓ p.2 Th) x := by
  obtain ⟨CT, hCT0, hCTb⟩ := exists_bound_nonneg hThb
  obtain ⟨CK, hCK0, hCKb⟩ := exists_bound_nonneg2 hkb
  have hBm : Measurable (aP ℓ p.2 Th) := Weak.aP_measurable p.2 hThm
  have hBb : ∀ x, |aP ℓ p.2 Th x| ≤ CT := Weak.aP_abs_le hℓ p.2 hCT0 hCTb
  have hκm : Measurable (kRow ℓ k) := kRow_measurable hkm
  have hκb : ∀ w, |kRow ℓ k w| ≤ CK := kRow_abs_le hℓ hCK0 hCKb
  -- the four summands
  set F1 : Xn n → ℝ := fun z => k (z p.2) (z p.1) * aP ℓ p.2 Th z with hF1
  set F2 : Xn n → ℝ := fun z => kRow ℓ k (z p.2) * aP ℓ p.2 Th z with hF2
  set F3 : Xn n → ℝ := fun z => kRow ℓ k (z p.1) * aP ℓ p.2 Th z with hF3
  set F4 : Xn n → ℝ := fun z => kAvg ℓ k * aP ℓ p.2 Th z with hF4
  have hF1m : Measurable F1 := by
    rw [hF1]
    exact (hkm.comp (Measurable.prodMk (measurable_pi_apply p.2)
      (measurable_pi_apply p.1))).mul hBm
  have hF2m : Measurable F2 := by
    rw [hF2]
    exact (hκm.comp (measurable_pi_apply p.2)).mul hBm
  have hF3m : Measurable F3 := by
    rw [hF3]
    exact (hκm.comp (measurable_pi_apply p.1)).mul hBm
  have hF4m : Measurable F4 := by
    rw [hF4]; exact measurable_const.mul hBm
  have hF1b : ∀ z, |F1 z| ≤ CK * CT := by
    intro z; rw [hF1, abs_mul]
    exact mul_le_mul (hCKb _ _) (hBb z) (abs_nonneg _) hCK0
  have hF2b : ∀ z, |F2 z| ≤ CK * CT := by
    intro z; rw [hF2, abs_mul]
    exact mul_le_mul (hκb _) (hBb z) (abs_nonneg _) hCK0
  have hF3b : ∀ z, |F3 z| ≤ CK * CT := by
    intro z; rw [hF3, abs_mul]
    exact mul_le_mul (hκb _) (hBb z) (abs_nonneg _) hCK0
  have hF4b : ∀ z, |F4 z| ≤ CK * CT := by
    intro z; rw [hF4, abs_mul]
    exact mul_le_mul (kAvg_abs_le hℓ hCK0 hCKb) (hBb z) (abs_nonneg _) hCK0
  -- measurability/boundedness of the partial sums
  have h12m : Measurable (fun z => F1 z - F2 z) := hF1m.sub hF2m
  have h12b : ∀ z, |(fun z => F1 z - F2 z) z| ≤ CK * CT + CK * CT := by
    intro z
    exact le_trans (abs_sub _ _) (by linarith [hF1b z, hF2b z])
  have h123m : Measurable (fun z => (F1 z - F2 z) - F3 z) := h12m.sub hF3m
  have h123b : ∀ z, |(fun z => (F1 z - F2 z) - F3 z) z| ≤ (CK * CT + CK * CT) + CK * CT := by
    intro z
    exact le_trans (abs_sub _ _) (by linarith [h12b z, hF3b z])
  -- the expansion of the kernel, then the linearity of `aP`
  have hfun : (fun z : Xn n => qmqKernelR ℓ k (z p.2) (z p.1) * aP ℓ p.2 Th z)
      = fun z => (F1 z - F2 z - F3 z) + F4 z := by
    funext z
    rw [hF1, hF2, hF3, hF4, qmqKernelR_eq ℓ hksym]
    ring
  rw [hfun,
    show (fun z : Xn n => F1 z - F2 z - F3 z + F4 z)
      = (fun z => F1 z - F2 z - F3 z) + F4 from rfl,
    Weak.aP_add hℓ p.1 (by positivity) (by positivity) h123m h123b hF4m hF4b x,
    show (fun z : Xn n => F1 z - F2 z - F3 z) = (fun z => F1 z - F2 z) - F3 from rfl,
    Weak.aP_sub hℓ p.1 (by positivity) (by positivity) h12m h12b hF3m hF3b x,
    show (fun z : Xn n => F1 z - F2 z) = F1 - F2 from rfl,
    Weak.aP_sub hℓ p.1 (by positivity) (by positivity) hF1m hF1b hF2m hF2b x]
  -- the two collapsed summands
  have hdep2 : ∀ z y, (fun w : Xn n => kRow ℓ k (w p.2)) (Function.update z p.1 y)
      = (fun w : Xn n => kRow ℓ k (w p.2)) z := by
    intro z y; simp only [Function.update_of_ne (Ne.symm hp)]
  have hdep4 : ∀ z y, (fun _ : Xn n => kAvg ℓ k) (Function.update z p.1 y)
      = (fun _ : Xn n => kAvg ℓ k) z := by
    intro z y; rfl
  have h2id : aP ℓ p.1 F2 x = kRow ℓ k (x p.2) * aP ℓ p.1 (aP ℓ p.2 Th) x := by
    rw [hF2, aP_mul_of_indep p.1 hdep2 (aP ℓ p.2 Th) x]
  have h4id : aP ℓ p.1 F4 x = kAvg ℓ k * aP ℓ p.1 (aP ℓ p.2 Th) x := by
    rw [hF4, aP_mul_of_indep p.1 hdep4 (aP ℓ p.2 Th) x]
  rw [h2id, h4id, hF1, hF3]

/-! ## 6. The four terms of the identity -/

lemma int_Th_H1 {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Th : Xn n → ℝ}
    (hThm : Measurable Th) (hThb : ∃ C : ℝ, ∀ x, |Th x| ≤ C)
    {k : E3 → E3 → ℝ} (hkm : Measurable (Function.uncurry k))
    (hkb : ∃ C : ℝ, ∀ w y, |k w y| ≤ C) (hksym : ∀ w y, k w y = k y w)
    {p : Fin n × Fin n} (hp : p.1 ≠ p.2) :
    (∫ x in abx n ℓ,
        Th x * aP ℓ p.1 (fun z => k (z p.2) (z p.1) * aP ℓ p.2 Th z) x)
      = ∫ x in abx n ℓ,
          aP ℓ p.1 Th x * aP ℓ p.2 Th x * k (x p.1) (x p.2) := by
  obtain ⟨CT, hCT0, hCTb⟩ := exists_bound_nonneg hThb
  obtain ⟨CK, hCK0, hCKb⟩ := exists_bound_nonneg2 hkb
  have hBm : Measurable (aP ℓ p.2 Th) := Weak.aP_measurable p.2 hThm
  have hBb : ∀ x, |aP ℓ p.2 Th x| ≤ CT := Weak.aP_abs_le hℓ p.2 hCT0 hCTb
  have hkm' : Measurable (fun x : Xn n => k (x p.1) (x p.2)) :=
    hkm.comp (Measurable.prodMk (measurable_pi_apply p.1) (measurable_pi_apply p.2))
  have hGm : Measurable (fun x : Xn n => aP ℓ p.2 Th x * k (x p.1) (x p.2)) := hBm.mul hkm'
  have hGb : ∀ x : Xn n, |aP ℓ p.2 Th x * k (x p.1) (x p.2)| ≤ CT * CK := by
    intro x
    rw [abs_mul]
    exact mul_le_mul (hBb x) (hCKb _ _) (abs_nonneg _) hCT0
  have hsym := Weak.aP_sym_box hℓ p.1 hCT0 (mul_nonneg hCT0 hCK0) hThm hCTb hGm hGb
  rw [show (∫ x in abx n ℓ,
        aP ℓ p.1 Th x * aP ℓ p.2 Th x * k (x p.1) (x p.2))
      = ∫ x in abx n ℓ,
          aP ℓ p.1 Th x * (aP ℓ p.2 Th x * k (x p.1) (x p.2)) from
      integral_congr_ae (Filter.Eventually.of_forall fun x => by ring), hsym]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  rw [show (fun z => k (z p.2) (z p.1) * aP ℓ p.2 Th z)
      = fun z => aP ℓ p.2 Th z * k (z p.1) (z p.2) from by
    funext z; rw [mul_comm, hksym]]

lemma int_Th_H2 {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Th : Xn n → ℝ}
    (hThm : Measurable Th) (hThb : ∃ C : ℝ, ∀ x, |Th x| ≤ C)
    {k : E3 → E3 → ℝ} (hkm : Measurable (Function.uncurry k))
    (hkb : ∃ C : ℝ, ∀ w y, |k w y| ≤ C) (hksym : ∀ w y, k w y = k y w)
    {p : Fin n × Fin n} (hp : p.1 ≠ p.2) :
    (∫ x in abx n ℓ, Th x * (kRow ℓ k (x p.2) * aP ℓ p.1 (aP ℓ p.2 Th) x))
      = ∫ x in abx n ℓ,
          aP ℓ p.1 Th x * aP ℓ p.1 (aP ℓ p.2 Th) x * k (x p.1) (x p.2) := by
  obtain ⟨CT, hCT0, hCTb⟩ := exists_bound_nonneg hThb
  obtain ⟨CK, hCK0, hCKb⟩ := exists_bound_nonneg2 hkb
  have hBm : Measurable (aP ℓ p.2 Th) := Weak.aP_measurable p.2 hThm
  have hBb : ∀ x, |aP ℓ p.2 Th x| ≤ CT := Weak.aP_abs_le hℓ p.2 hCT0 hCTb
  have hPm : Measurable (aP ℓ p.1 (aP ℓ p.2 Th)) := Weak.aP_measurable p.1 hBm
  have hPb : ∀ x, |aP ℓ p.1 (aP ℓ p.2 Th) x| ≤ CT := Weak.aP_abs_le hℓ p.1 hCT0 hBb
  have hkm' : Measurable (fun x : Xn n => k (x p.1) (x p.2)) :=
    hkm.comp (Measurable.prodMk (measurable_pi_apply p.1) (measurable_pi_apply p.2))
  have hGm : Measurable (fun x : Xn n => aP ℓ p.1 (aP ℓ p.2 Th) x * k (x p.1) (x p.2)) :=
    hPm.mul hkm'
  have hGb : ∀ x : Xn n, |aP ℓ p.1 (aP ℓ p.2 Th) x * k (x p.1) (x p.2)| ≤ CT * CK := by
    intro x
    rw [abs_mul]
    exact mul_le_mul (hPb x) (hCKb _ _) (abs_nonneg _) hCT0
  rw [show (∫ x in abx n ℓ,
        aP ℓ p.1 Th x * aP ℓ p.1 (aP ℓ p.2 Th) x * k (x p.1) (x p.2))
      = ∫ x in abx n ℓ,
          aP ℓ p.1 Th x * (aP ℓ p.1 (aP ℓ p.2 Th) x * k (x p.1) (x p.2)) from
      integral_congr_ae (Filter.Eventually.of_forall fun x => by ring),
    Weak.aP_sym_box hℓ p.1 hCT0 (mul_nonneg hCT0 hCK0) hThm hCTb hGm hGb]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hdep : ∀ z y, (fun w : Xn n => aP ℓ p.1 (aP ℓ p.2 Th) w) (Function.update z p.1 y)
      = (fun w : Xn n => aP ℓ p.1 (aP ℓ p.2 Th) w) z :=
    fun z y => Weak.aP_const_in_coord p.1 (aP ℓ p.2 Th) z y
  have hpt : aP ℓ p.1 (fun z : Xn n => k (z p.1) (z p.2)) x = kRow ℓ k (x p.2) := by
    rw [Submission.BoseGases.aP, kRow, one_div]
    congr 1
    apply integral_congr_ae
    filter_upwards with y
    simp only [Function.update_self, Function.update_of_ne (Ne.symm hp)]
    exact hksym y (x p.2)
  show Th x * (kRow ℓ k (x p.2) * aP ℓ p.1 (aP ℓ p.2 Th) x)
      = Th x * aP ℓ p.1 (fun z : Xn n => aP ℓ p.1 (aP ℓ p.2 Th) z * k (z p.1) (z p.2)) x
  rw [aP_mul_of_indep (ℓ := ℓ) p.1 hdep (fun z : Xn n => k (z p.1) (z p.2)) x, hpt]
  ring

lemma int_Th_H3 {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Th : Xn n → ℝ}
    (hThm : Measurable Th) (hThb : ∃ C : ℝ, ∀ x, |Th x| ≤ C)
    {k : E3 → E3 → ℝ} (hkm : Measurable (Function.uncurry k))
    (hkb : ∃ C : ℝ, ∀ w y, |k w y| ≤ C) (hksym : ∀ w y, k w y = k y w)
    {p : Fin n × Fin n} (hp : p.1 ≠ p.2) :
    (∫ x in abx n ℓ, Th x * aP ℓ p.1 (fun z => kRow ℓ k (z p.1) * aP ℓ p.2 Th z) x)
      = ∫ x in abx n ℓ,
          aP ℓ p.2 Th x * aP ℓ p.1 (aP ℓ p.2 Th) x * k (x p.1) (x p.2) := by
  obtain ⟨CT, hCT0, hCTb⟩ := exists_bound_nonneg hThb
  obtain ⟨CK, hCK0, hCKb⟩ := exists_bound_nonneg2 hkb
  have hκm : Measurable (kRow ℓ k) := kRow_measurable hkm
  have hκb : ∀ w, |kRow ℓ k w| ≤ CK := kRow_abs_le hℓ hCK0 hCKb
  set B : Xn n → ℝ := aP ℓ p.2 Th with hBdef
  set A : Xn n → ℝ := aP ℓ p.1 Th with hAdef
  set Cc : Xn n → ℝ := aP ℓ p.1 B with hCcdef
  set κB : Xn n → ℝ := fun x => kRow ℓ k (x p.1) * aP ℓ p.2 Th x with hκBdef
  have hBm : Measurable B := by rw [hBdef]; exact Weak.aP_measurable p.2 hThm
  have hBb : ∀ x, |B x| ≤ CT := by
    intro x; rw [hBdef]; exact Weak.aP_abs_le hℓ p.2 hCT0 hCTb x
  have hAm : Measurable A := by rw [hAdef]; exact Weak.aP_measurable p.1 hThm
  have hAb : ∀ x, |A x| ≤ CT := by
    intro x; rw [hAdef]; exact Weak.aP_abs_le hℓ p.1 hCT0 hCTb x
  have hCcm : Measurable Cc := by rw [hCcdef]; exact Weak.aP_measurable p.1 hBm
  have hCcb : ∀ x, |Cc x| ≤ CT := by
    intro x; rw [hCcdef]; exact Weak.aP_abs_le hℓ p.1 hCT0 hBb x
  have hκBm : Measurable κB := by
    rw [hκBdef]
    exact (hκm.comp (measurable_pi_apply p.1)).mul hBm
  have hκBb : ∀ x, |κB x| ≤ CK * CT := by
    intro x; rw [hκBdef, abs_mul]
    exact mul_le_mul (hκb _) (hBb x) (abs_nonneg _) hCK0
  have hH3m : Measurable (aP ℓ p.1 κB) := Weak.aP_measurable p.1 hκBm
  have hH3b : ∀ x, |aP ℓ p.1 κB x| ≤ CK * CT :=
    fun x => Weak.aP_abs_le hℓ p.1 (mul_nonneg hCK0 hCT0) hκBb x
  -- the three independence facts
  have hBindep : ∀ x z, B (Function.update x p.2 z) = B x := by
    intro x z; rw [hBdef]; exact Weak.aP_const_in_coord p.2 Th x z
  have hCcdep : ∀ x z, Cc (Function.update x p.2 z) = Cc x := by
    rw [hCcdef]
    exact fun x z => aP_indep_of_indep hp hBindep x z
  have hκBindep : ∀ x z, κB (Function.update x p.2 z) = κB x := by
    intro x z
    rw [hκBdef]
    show kRow ℓ k ((Function.update x p.2 z) p.1) * aP ℓ p.2 Th (Function.update x p.2 z)
      = kRow ℓ k (x p.1) * aP ℓ p.2 Th x
    rw [Function.update_of_ne hp]
    congr 1
    rw [← hBdef]
    exact hBindep x z
  have hH3indep : ∀ x z, aP ℓ p.1 κB (Function.update x p.2 z) = aP ℓ p.1 κB x :=
    fun x z => aP_indep_of_indep hp hκBindep x z
  -- 1. `∫ Th·H3 = ∫ A·κB`
  have h12 : (∫ x in abx n ℓ, Th x * aP ℓ p.1 κB x) = ∫ x in abx n ℓ, A x * κB x :=
    (Weak.aP_sym_box hℓ p.1 hCT0 (mul_nonneg hCK0 hCT0) hThm hCTb hκBm hκBb).symm
  -- 2. `∫ A·κB = ∫ Cc·κB`
  have hA_C : ∀ x, A x - Cc x = aP ℓ p.1 (Th - B) x := by
    intro x
    rw [hAdef, hCcdef, hBdef]
    exact (Weak.aP_sub hℓ p.1 hCT0 hCT0 hThm hCTb hBm hBb x).symm
  have hTBm : Measurable (Th - B) := hThm.sub hBm
  have hTBb : ∀ x : Xn n, |(Th - B) x| ≤ CT + CT := fun x => le_trans (abs_sub _ _) (by
    linarith [hCTb x, hBb x])
  have hzero : (∫ x in abx n ℓ, (A x - Cc x) * κB x) = 0 := by
    rw [show (fun x : Xn n => (A x - Cc x) * κB x)
        = fun x : Xn n => aP ℓ p.1 (Th - B) x * κB x from by
      funext x; rw [hA_C x]]
    rw [Weak.aP_sym_box hℓ p.1 (by positivity) (mul_nonneg hCK0 hCT0) hTBm hTBb hκBm hκBb]
    rw [show (fun x : Xn n => (Th - B) x * aP ℓ p.1 κB x)
        = fun x : Xn n => Th x * aP ℓ p.1 κB x - B x * aP ℓ p.1 κB x from by
      funext x; simp only [Pi.sub_apply]; ring]
    have hstep : (∫ x in abx n ℓ, (Th x * aP ℓ p.1 κB x - B x * aP ℓ p.1 κB x))
        = (∫ x in abx n ℓ, Th x * aP ℓ p.1 κB x)
          - ∫ x in abx n ℓ, B x * aP ℓ p.1 κB x :=
      MeasureTheory.integral_sub
        (integrableOn_abox_mul_of_bound hℓ hThm hCTb hH3m hH3b)
        (integrableOn_abox_mul_of_bound hℓ hBm hBb hH3m hH3b)
    rw [hstep]
    rw [show (∫ x in abx n ℓ, B x * aP ℓ p.1 κB x)
        = ∫ x in abx n ℓ, Th x * aP ℓ p.2 (aP ℓ p.1 κB) x from
      Weak.aP_sym_box hℓ p.2 hCT0 (mul_nonneg hCK0 hCT0) hThm hCTb hH3m hH3b]
    rw [show aP ℓ p.2 (aP ℓ p.1 κB) = aP ℓ p.1 κB from by
      funext x
      exact aP_eq_self_of_indep hℓ p.2 (F := aP ℓ p.1 κB) hH3indep x]
    ring
  have h23 : (∫ x in abx n ℓ, A x * κB x) = ∫ x in abx n ℓ, Cc x * κB x := by
    have hstep : (∫ x in abx n ℓ, (A x * κB x - Cc x * κB x))
        = (∫ x in abx n ℓ, A x * κB x) - ∫ x in abx n ℓ, Cc x * κB x :=
      MeasureTheory.integral_sub
        (integrableOn_abox_mul_of_bound hℓ hAm hAb hκBm hκBb)
        (integrableOn_abox_mul_of_bound hℓ hCcm hCcb hκBm hκBb)
    have hsub : (∫ x in abx n ℓ, (A x - Cc x) * κB x)
        = (∫ x in abx n ℓ, A x * κB x) - ∫ x in abx n ℓ, Cc x * κB x := by
      rw [← hstep]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    have h' : (∫ x in abx n ℓ, A x * κB x) - ∫ x in abx n ℓ, Cc x * κB x = 0 := by
      rw [← hsub]; exact hzero
    exact sub_eq_zero.mp h'
  -- 3. `∫ Cc·κB = ∫ Th·(Cc·kRow(·))`
  have h34 : (∫ x in abx n ℓ, Cc x * κB x)
      = ∫ x in abx n ℓ, Th x * (Cc x * kRow ℓ k (x p.1)) := by
    rw [show (fun x : Xn n => Cc x * κB x)
        = fun x : Xn n => B x * (Cc x * kRow ℓ k (x p.1)) from by
      funext x; rw [hκBdef, hBdef]; ring]
    rw [show (fun x : Xn n => B x * (Cc x * kRow ℓ k (x p.1)))
        = fun x : Xn n => aP ℓ p.2 Th x * (Cc x * kRow ℓ k (x p.1)) from by
      funext x; rw [hBdef]]
    have hGm : Measurable (fun x : Xn n => Cc x * kRow ℓ k (x p.1)) :=
      hCcm.mul (hκm.comp (measurable_pi_apply p.1))
    have hGb : ∀ x : Xn n, |Cc x * kRow ℓ k (x p.1)| ≤ CT * CK := by
      intro x; rw [abs_mul]
      exact mul_le_mul (hCcb x) (hκb _) (abs_nonneg _) hCT0
    rw [Weak.aP_sym_box hℓ p.2 hCT0 (mul_nonneg hCT0 hCK0) hThm hCTb hGm hGb]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have hdepK : ∀ z y, (fun w : Xn n => kRow ℓ k (w p.1)) (Function.update z p.2 y)
        = (fun w : Xn n => kRow ℓ k (w p.1)) z := by
      intro z y; simp only [Function.update_of_ne hp]
    have hself : aP ℓ p.2 (fun w : Xn n => kRow ℓ k (w p.1)) x = kRow ℓ k (x p.1) :=
      aP_eq_self_of_indep hℓ p.2 (F := fun w : Xn n => kRow ℓ k (w p.1)) hdepK x
    show Th x * aP ℓ p.2 (fun z : Xn n => Cc z * kRow ℓ k (z p.1)) x
        = Th x * (Cc x * kRow ℓ k (x p.1))
    rw [aP_mul_of_indep (ℓ := ℓ) p.2 hCcdep (fun w : Xn n => kRow ℓ k (w p.1)) x, hself]
    try ring
  -- 4. `∫ Th·(Cc·kRow(·)) = ∫ B·(Cc·k)`
  have h45 : (∫ x in abx n ℓ, Th x * (Cc x * kRow ℓ k (x p.1)))
      = ∫ x in abx n ℓ, B x * (Cc x * k (x p.1) (x p.2)) := by
    rw [show (∫ x in abx n ℓ, B x * (Cc x * k (x p.1) (x p.2)))
        = ∫ x in abx n ℓ, aP ℓ p.2 Th x * (Cc x * k (x p.1) (x p.2)) from by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_); rw [hBdef]]
    have hGm : Measurable (fun x : Xn n => Cc x * k (x p.1) (x p.2)) :=
      hCcm.mul (hkm.comp (Measurable.prodMk (measurable_pi_apply p.1)
        (measurable_pi_apply p.2)))
    have hGb : ∀ x : Xn n, |Cc x * k (x p.1) (x p.2)| ≤ CT * CK := by
      intro x; rw [abs_mul]
      exact mul_le_mul (hCcb x) (hCKb _ _) (abs_nonneg _) hCT0
    rw [Weak.aP_sym_box hℓ p.2 hCT0 (mul_nonneg hCT0 hCK0) hThm hCTb hGm hGb]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have hpt : aP ℓ p.2 (fun z : Xn n => k (z p.1) (z p.2)) x = kRow ℓ k (x p.1) := by
      rw [Submission.BoseGases.aP, kRow, one_div]
      congr 1
      apply integral_congr_ae
      filter_upwards with y
      simp only [Function.update_of_ne hp, Function.update_self]
    show Th x * (Cc x * kRow ℓ k (x p.1))
        = Th x * aP ℓ p.2 (fun z : Xn n => Cc z * k (z p.1) (z p.2)) x
    rw [aP_mul_of_indep (ℓ := ℓ) p.2 hCcdep (fun w : Xn n => k (w p.1) (w p.2)) x, hpt]
    try ring
  calc (∫ x in abx n ℓ, Th x * aP ℓ p.1 (fun z => kRow ℓ k (z p.1) * aP ℓ p.2 Th z) x)
      = ∫ x in abx n ℓ, Th x * aP ℓ p.1 κB x := rfl
    _ = ∫ x in abx n ℓ, A x * κB x := h12
    _ = ∫ x in abx n ℓ, Cc x * κB x := h23
    _ = ∫ x in abx n ℓ, Th x * (Cc x * kRow ℓ k (x p.1)) := h34
    _ = ∫ x in abx n ℓ, B x * (Cc x * k (x p.1) (x p.2)) := h45
    _ = ∫ x in abx n ℓ, aP ℓ p.2 Th x * aP ℓ p.1 (aP ℓ p.2 Th) x * k (x p.1) (x p.2) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        rw [hBdef, hCcdef]; ring

lemma int_Th_Cc_eq {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Th : Xn n → ℝ}
    (hThm : Measurable Th) (hThb : ∃ C : ℝ, ∀ x, |Th x| ≤ C)
    {p : Fin n × Fin n} (hp : p.1 ≠ p.2) :
    (∫ x in abx n ℓ, Th x * aP ℓ p.1 (aP ℓ p.2 Th) x)
      = ∫ x in abx n ℓ, aP ℓ p.1 (aP ℓ p.2 Th) x * aP ℓ p.1 (aP ℓ p.2 Th) x := by
  obtain ⟨CT, hCT0, hCTb⟩ := exists_bound_nonneg hThb
  have hBm : Measurable (aP ℓ p.2 Th) := Weak.aP_measurable p.2 hThm
  have hBb : ∀ x, |aP ℓ p.2 Th x| ≤ CT := Weak.aP_abs_le hℓ p.2 hCT0 hCTb
  have hCcm : Measurable (aP ℓ p.1 (aP ℓ p.2 Th)) := Weak.aP_measurable p.1 hBm
  have hCcb : ∀ x, |aP ℓ p.1 (aP ℓ p.2 Th) x| ≤ CT := Weak.aP_abs_le hℓ p.1 hCT0 hBb
  have h_e1 : aP ℓ p.1 (aP ℓ p.1 (aP ℓ p.2 Th)) = aP ℓ p.1 (aP ℓ p.2 Th) :=
    Weak.aP_idem_fun hℓ p.1 (aP ℓ p.2 Th)
  have h_e2 : aP ℓ p.2 (aP ℓ p.1 (aP ℓ p.2 Th)) = aP ℓ p.1 (aP ℓ p.2 Th) := by
    funext x
    exact aP_eq_self_of_indep hℓ p.2 (F := aP ℓ p.1 (aP ℓ p.2 Th))
      (fun y z => aP_indep_of_indep hp (fun y z => Weak.aP_const_in_coord p.2 Th y z) y z) x
  have h3 : (∫ x in abx n ℓ, aP ℓ p.1 (aP ℓ p.2 Th) x * aP ℓ p.1 (aP ℓ p.2 Th) x)
      = ∫ x in abx n ℓ, Th x * aP ℓ p.1 (aP ℓ p.2 Th) x := by
    have hsym1 := Weak.aP_sym_box hℓ p.1 hCT0 hCT0 hBm hBb hCcm hCcb
    rw [h_e1] at hsym1
    have hsym2 := Weak.aP_sym_box hℓ p.2 hCT0 hCT0 hThm hCTb hCcm hCcb
    rw [h_e2] at hsym2
    exact hsym1.trans hsym2
  exact h3.symm

lemma int_Th_kk {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Th : Xn n → ℝ}
    (hThm : Measurable Th) (hThb : ∃ C : ℝ, ∀ x, |Th x| ≤ C)
    {k : E3 → E3 → ℝ} {p : Fin n × Fin n} (hp : p.1 ≠ p.2) :
    (∫ x in abx n ℓ, Th x * (kAvg ℓ k * aP ℓ p.1 (aP ℓ p.2 Th) x))
      = kAvg ℓ k * ∫ x in abx n ℓ,
          aP ℓ p.1 (aP ℓ p.2 Th) x * aP ℓ p.1 (aP ℓ p.2 Th) x := by
  rw [show (fun x : Xn n => Th x * (kAvg ℓ k * aP ℓ p.1 (aP ℓ p.2 Th) x))
      = fun x : Xn n => kAvg ℓ k * (Th x * aP ℓ p.1 (aP ℓ p.2 Th) x) from by
    funext x; ring]
  rw [MeasureTheory.integral_const_mul, int_Th_Cc_eq hℓ hThm hThb hp]

lemma int_C2_k {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Th : Xn n → ℝ}
    (hThm : Measurable Th) (hThb : ∃ C : ℝ, ∀ x, |Th x| ≤ C)
    {k : E3 → E3 → ℝ} (hkm : Measurable (Function.uncurry k))
    (hkb : ∃ C : ℝ, ∀ w y, |k w y| ≤ C) (hksym : ∀ w y, k w y = k y w)
    {p : Fin n × Fin n} (hp : p.1 ≠ p.2) :
    (∫ x in abx n ℓ,
        aP ℓ p.1 (aP ℓ p.2 Th) x * aP ℓ p.1 (aP ℓ p.2 Th) x * k (x p.1) (x p.2))
      = kAvg ℓ k * ∫ x in abx n ℓ,
          aP ℓ p.1 (aP ℓ p.2 Th) x * aP ℓ p.1 (aP ℓ p.2 Th) x := by
  obtain ⟨CT, hCT0, hCTb⟩ := exists_bound_nonneg hThb
  obtain ⟨CK, hCK0, hCKb⟩ := exists_bound_nonneg2 hkb
  have hκm : Measurable (kRow ℓ k) := kRow_measurable hkm
  have hκb : ∀ w, |kRow ℓ k w| ≤ CK := kRow_abs_le hℓ hCK0 hCKb
  have hBm : Measurable (aP ℓ p.2 Th) := Weak.aP_measurable p.2 hThm
  have hBb : ∀ x, |aP ℓ p.2 Th x| ≤ CT := Weak.aP_abs_le hℓ p.2 hCT0 hCTb
  have hCcm : Measurable (aP ℓ p.1 (aP ℓ p.2 Th)) := Weak.aP_measurable p.1 hBm
  have hCcb : ∀ x, |aP ℓ p.1 (aP ℓ p.2 Th) x| ≤ CT := Weak.aP_abs_le hℓ p.1 hCT0 hBb
  have hCcdep1 : ∀ x z, aP ℓ p.1 (aP ℓ p.2 Th) (Function.update x p.1 z)
      = aP ℓ p.1 (aP ℓ p.2 Th) x :=
    fun x z => Weak.aP_const_in_coord p.1 (aP ℓ p.2 Th) x z
  have hCcdep2 : ∀ x z, aP ℓ p.1 (aP ℓ p.2 Th) (Function.update x p.2 z)
      = aP ℓ p.1 (aP ℓ p.2 Th) x :=
    fun x z => aP_indep_of_indep hp (fun y z => Weak.aP_const_in_coord p.2 Th y z) x z
  have hpt1 : aP ℓ p.1 (fun y : Xn n => aP ℓ p.1 (aP ℓ p.2 Th) y * k (y p.1) (y p.2))
      = fun y : Xn n => aP ℓ p.1 (aP ℓ p.2 Th) y * kRow ℓ k (y p.2) := by
    funext x
    rw [aP_mul_of_indep (ℓ := ℓ) p.1 hCcdep1 (fun y : Xn n => k (y p.1) (y p.2)) x]
    congr 1
    rw [Submission.BoseGases.aP, kRow, one_div]
    congr 1
    apply integral_congr_ae
    filter_upwards with y
    simp only [Function.update_self, Function.update_of_ne (Ne.symm hp)]
    exact hksym y (x p.2)
  have hpt2 : aP ℓ p.2 (fun y : Xn n => aP ℓ p.1 (aP ℓ p.2 Th) y * kRow ℓ k (y p.2))
      = fun y : Xn n => aP ℓ p.1 (aP ℓ p.2 Th) y * kAvg ℓ k := by
    funext x
    rw [aP_mul_of_indep (ℓ := ℓ) p.2 hCcdep2 (fun y : Xn n => kRow ℓ k (y p.2)) x]
    congr 1
    rw [Submission.BoseGases.aP, kAvg, one_div]
    congr 1
    apply integral_congr_ae
    filter_upwards with y
    simp only [Function.update_self]
  have hGm : Measurable (fun y : Xn n => aP ℓ p.1 (aP ℓ p.2 Th) y * k (y p.1) (y p.2)) :=
    hCcm.mul (hkm.comp (Measurable.prodMk (measurable_pi_apply p.1) (measurable_pi_apply p.2)))
  have hGb : ∀ y : Xn n, |aP ℓ p.1 (aP ℓ p.2 Th) y * k (y p.1) (y p.2)| ≤ CT * CK := by
    intro y; rw [abs_mul]
    exact mul_le_mul (hCcb y) (hCKb _ _) (abs_nonneg _) hCT0
  have hGm2 : Measurable (fun y : Xn n => aP ℓ p.1 (aP ℓ p.2 Th) y * kRow ℓ k (y p.2)) :=
    hCcm.mul (hκm.comp (measurable_pi_apply p.2))
  have hGb2 : ∀ y : Xn n, |aP ℓ p.1 (aP ℓ p.2 Th) y * kRow ℓ k (y p.2)| ≤ CT * CK := by
    intro y; rw [abs_mul]
    exact mul_le_mul (hCcb y) (hκb _) (abs_nonneg _) hCT0
  calc (∫ x in abx n ℓ,
        aP ℓ p.1 (aP ℓ p.2 Th) x * aP ℓ p.1 (aP ℓ p.2 Th) x * k (x p.1) (x p.2))
      = ∫ x in abx n ℓ, aP ℓ p.1 (aP ℓ p.2 Th) x
          * (aP ℓ p.1 (aP ℓ p.2 Th) x * k (x p.1) (x p.2)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    _ = ∫ x in abx n ℓ, aP ℓ p.2 Th x
          * (aP ℓ p.1 (aP ℓ p.2 Th) x * kRow ℓ k (x p.2)) := by
        rw [Weak.aP_sym_box hℓ p.1 hCT0 (mul_nonneg hCT0 hCK0) hBm hBb hGm hGb, hpt1]
    _ = ∫ x in abx n ℓ, Th x * (aP ℓ p.1 (aP ℓ p.2 Th) x * kAvg ℓ k) := by
        rw [Weak.aP_sym_box hℓ p.2 hCT0 (mul_nonneg hCT0 hCK0) hThm hCTb hGm2 hGb2, hpt2]
    _ = kAvg ℓ k * ∫ x in abx n ℓ, Th x * aP ℓ p.1 (aP ℓ p.2 Th) x := by
        rw [show (fun x : Xn n => Th x * (aP ℓ p.1 (aP ℓ p.2 Th) x * kAvg ℓ k))
            = fun x : Xn n => kAvg ℓ k * (Th x * aP ℓ p.1 (aP ℓ p.2 Th) x) from by
          funext x; ring]
        rw [MeasureTheory.integral_const_mul]
    _ = kAvg ℓ k * ∫ x in abx n ℓ,
          aP ℓ p.1 (aP ℓ p.2 Th) x * aP ℓ p.1 (aP ℓ p.2 Th) x := by
        rw [int_Th_Cc_eq hℓ hThm hThb hp]

/-- **Congruence of the slot mean on the box.**  If two states agree on the `n`-particle box, their
slot means agree there. -/
lemma aP_congr_of_eqOn_abox {n : ℕ} {ℓ : ℝ} (i : Fin n) {F G : Xn n → ℝ}
    (h : ∀ y ∈ abx n ℓ, F y = G y) {x : Xn n} (hx : x ∈ abx n ℓ) :
    aP ℓ i F x = aP ℓ i G x := by
  rw [Submission.BoseGases.aP, Submission.BoseGases.aP]
  congr 1
  apply MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ)
  intro y hy
  refine h _ ((Submission.BoseGases.mem_abox_iff n ℓ _).mpr fun j => ?_)
  by_cases hj : j = i
  · subst hj; rwa [Function.update_self]
  · rw [Function.update_of_ne hj]
    exact (Submission.BoseGases.mem_abox_iff n ℓ x).mp hx j

theorem block13_main {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Th : Xn n → ℝ}
    (hThm : Measurable Th) (hThb : ∃ C : ℝ, ∀ x, |Th x| ≤ C)
    {k : E3 → E3 → ℝ} (hkm : Measurable (Function.uncurry k))
    (hkb : ∃ C : ℝ, ∀ w y, |k w y| ≤ C) (hksym : ∀ w y, k w y = k y w)
    {p : Fin n × Fin n} (hp : p.1 ≠ p.2) :
    (∫ x in abx n ℓ, Th x * aP ℓ p.1
        (fun z : Xn n => qmqKernelR ℓ k (z p.2) (z p.1) * aP ℓ p.2 Th z) x)
      = ∫ x in abx n ℓ,
          (aP ℓ p.1 Th x - aP ℓ p.1 (aP ℓ p.2 Th) x)
            * (aP ℓ p.2 Th x - aP ℓ p.1 (aP ℓ p.2 Th) x) * k (x p.1) (x p.2) := by
  obtain ⟨CT, hCT0, hCTb⟩ := exists_bound_nonneg hThb
  obtain ⟨CK, hCK0, hCKb⟩ := exists_bound_nonneg2 hkb
  have hκm : Measurable (kRow ℓ k) := kRow_measurable hkm
  have hκb : ∀ w, |kRow ℓ k w| ≤ CK := kRow_abs_le hℓ hCK0 hCKb
  have hBm : Measurable (aP ℓ p.2 Th) := Weak.aP_measurable p.2 hThm
  have hBb : ∀ x, |aP ℓ p.2 Th x| ≤ CT := Weak.aP_abs_le hℓ p.2 hCT0 hCTb
  have hAm : Measurable (aP ℓ p.1 Th) := Weak.aP_measurable p.1 hThm
  have hAb : ∀ x, |aP ℓ p.1 Th x| ≤ CT := Weak.aP_abs_le hℓ p.1 hCT0 hCTb
  have hCcm : Measurable (aP ℓ p.1 (aP ℓ p.2 Th)) := Weak.aP_measurable p.1 hBm
  have hCcb : ∀ x, |aP ℓ p.1 (aP ℓ p.2 Th) x| ≤ CT := Weak.aP_abs_le hℓ p.1 hCT0 hBb
  have hH1m : Measurable (aP ℓ p.1 (fun z : Xn n => k (z p.2) (z p.1) * aP ℓ p.2 Th z)) :=
    Weak.aP_measurable p.1 ((hkm.comp (Measurable.prodMk (measurable_pi_apply p.2)
      (measurable_pi_apply p.1))).mul hBm)
  have hH1b : ∀ x, |aP ℓ p.1 (fun z : Xn n => k (z p.2) (z p.1) * aP ℓ p.2 Th z) x|
      ≤ CK * CT := fun x => Weak.aP_abs_le hℓ p.1 (mul_nonneg hCK0 hCT0) (fun z => by
        rw [abs_mul]
        exact mul_le_mul (hCKb _ _) (hBb z) (abs_nonneg _) hCK0) x
  have hH3m : Measurable (aP ℓ p.1 (fun z : Xn n => kRow ℓ k (z p.1) * aP ℓ p.2 Th z)) :=
    Weak.aP_measurable p.1 ((hκm.comp (measurable_pi_apply p.1)).mul hBm)
  have hH3b : ∀ x, |aP ℓ p.1 (fun z : Xn n => kRow ℓ k (z p.1) * aP ℓ p.2 Th z) x|
      ≤ CK * CT := fun x => Weak.aP_abs_le hℓ p.1 (mul_nonneg hCK0 hCT0) (fun z => by
        rw [abs_mul]
        exact mul_le_mul (hκb _) (hBb z) (abs_nonneg _) hCK0) x
  -- the four integrability facts of the left-hand split
  have hL1 : IntegrableOn (fun x : Xn n =>
      Th x * aP ℓ p.1 (fun z : Xn n => k (z p.2) (z p.1) * aP ℓ p.2 Th z) x)
      (abx n ℓ) volume := integrableOn_abox_mul_of_bound hℓ hThm hCTb hH1m hH1b
  have hL2 : IntegrableOn (fun x : Xn n =>
      Th x * (kRow ℓ k (x p.2) * aP ℓ p.1 (aP ℓ p.2 Th) x)) (abx n ℓ) volume :=
    integrableOn_abox_mul_of_bound hℓ hThm hCTb
      ((hκm.comp (measurable_pi_apply p.2)).mul hCcm) (fun x => by
        rw [abs_mul]
        exact mul_le_mul (hκb _) (hCcb x) (abs_nonneg _) hCK0)
  have hL3 : IntegrableOn (fun x : Xn n =>
      Th x * aP ℓ p.1 (fun z : Xn n => kRow ℓ k (z p.1) * aP ℓ p.2 Th z) x)
      (abx n ℓ) volume := integrableOn_abox_mul_of_bound hℓ hThm hCTb hH3m hH3b
  have hL4 : IntegrableOn (fun x : Xn n =>
      Th x * (kAvg ℓ k * aP ℓ p.1 (aP ℓ p.2 Th) x)) (abx n ℓ) volume :=
    integrableOn_abox_mul_of_bound hℓ hThm hCTb (measurable_const.mul hCcm) (fun x => by
        rw [abs_mul]
        exact mul_le_mul (kAvg_abs_le hℓ hCK0 hCKb) (hCcb x) (abs_nonneg _)
          (le_trans (abs_nonneg _) (kAvg_abs_le hℓ hCK0 hCKb)))
  -- the pointwise expansion of the left-hand side
  have hpt : ∀ x : Xn n, aP ℓ p.1 (fun z : Xn n => qmqKernelR ℓ k (z p.2) (z p.1)
        * aP ℓ p.2 Th z) x
      = aP ℓ p.1 (fun z : Xn n => k (z p.2) (z p.1) * aP ℓ p.2 Th z) x
        - kRow ℓ k (x p.2) * aP ℓ p.1 (aP ℓ p.2 Th) x
        - aP ℓ p.1 (fun z : Xn n => kRow ℓ k (z p.1) * aP ℓ p.2 Th z) x
        + kAvg ℓ k * aP ℓ p.1 (aP ℓ p.2 Th) x :=
    fun x => aP_qmqKernelR hℓ hThm hThb hkm hkb hksym hp x
  have hsplitL : (∫ x in abx n ℓ, Th x * aP ℓ p.1
        (fun z : Xn n => qmqKernelR ℓ k (z p.2) (z p.1) * aP ℓ p.2 Th z) x)
      = (∫ x in abx n ℓ, Th x * aP ℓ p.1
            (fun z : Xn n => k (z p.2) (z p.1) * aP ℓ p.2 Th z) x)
        - (∫ x in abx n ℓ, Th x * (kRow ℓ k (x p.2) * aP ℓ p.1 (aP ℓ p.2 Th) x))
        - (∫ x in abx n ℓ, Th x * aP ℓ p.1
            (fun z : Xn n => kRow ℓ k (z p.1) * aP ℓ p.2 Th z) x)
        + (∫ x in abx n ℓ, Th x * (kAvg ℓ k * aP ℓ p.1 (aP ℓ p.2 Th) x)) := by
    rw [show (fun x : Xn n => Th x * aP ℓ p.1
          (fun z : Xn n => qmqKernelR ℓ k (z p.2) (z p.1) * aP ℓ p.2 Th z) x)
        = fun x : Xn n => Th x * (aP ℓ p.1
            (fun z : Xn n => k (z p.2) (z p.1) * aP ℓ p.2 Th z) x
          - kRow ℓ k (x p.2) * aP ℓ p.1 (aP ℓ p.2 Th) x
          - aP ℓ p.1 (fun z : Xn n => kRow ℓ k (z p.1) * aP ℓ p.2 Th z) x
          + kAvg ℓ k * aP ℓ p.1 (aP ℓ p.2 Th) x) from by
      funext x; rw [hpt x]]
    rw [show (fun x : Xn n => Th x * (aP ℓ p.1
            (fun z : Xn n => k (z p.2) (z p.1) * aP ℓ p.2 Th z) x
          - kRow ℓ k (x p.2) * aP ℓ p.1 (aP ℓ p.2 Th) x
          - aP ℓ p.1 (fun z : Xn n => kRow ℓ k (z p.1) * aP ℓ p.2 Th z) x
          + kAvg ℓ k * aP ℓ p.1 (aP ℓ p.2 Th) x))
        = fun x : Xn n => ((Th x * aP ℓ p.1
              (fun z : Xn n => k (z p.2) (z p.1) * aP ℓ p.2 Th z) x
            - Th x * (kRow ℓ k (x p.2) * aP ℓ p.1 (aP ℓ p.2 Th) x))
          - Th x * aP ℓ p.1 (fun z : Xn n => kRow ℓ k (z p.1) * aP ℓ p.2 Th z) x)
          + Th x * (kAvg ℓ k * aP ℓ p.1 (aP ℓ p.2 Th) x) from by
      funext x; ring]
    rw [MeasureTheory.integral_add
        (f := fun x : Xn n => (Th x * aP ℓ p.1
              (fun z : Xn n => k (z p.2) (z p.1) * aP ℓ p.2 Th z) x
            - Th x * (kRow ℓ k (x p.2) * aP ℓ p.1 (aP ℓ p.2 Th) x))
          - Th x * aP ℓ p.1 (fun z : Xn n => kRow ℓ k (z p.1) * aP ℓ p.2 Th z) x)
        (g := fun x : Xn n => Th x * (kAvg ℓ k * aP ℓ p.1 (aP ℓ p.2 Th) x))
        ((hL1.sub hL2).sub hL3) hL4,
      MeasureTheory.integral_sub (f := fun x : Xn n => Th x * aP ℓ p.1
              (fun z : Xn n => k (z p.2) (z p.1) * aP ℓ p.2 Th z) x
            - Th x * (kRow ℓ k (x p.2) * aP ℓ p.1 (aP ℓ p.2 Th) x))
        (g := fun x : Xn n => Th x * aP ℓ p.1
              (fun z : Xn n => kRow ℓ k (z p.1) * aP ℓ p.2 Th z) x)
        (hL1.sub hL2) hL3,
      MeasureTheory.integral_sub (f := fun x : Xn n => Th x * aP ℓ p.1
              (fun z : Xn n => k (z p.2) (z p.1) * aP ℓ p.2 Th z) x)
        (g := fun x : Xn n => Th x * (kRow ℓ k (x p.2) * aP ℓ p.1 (aP ℓ p.2 Th) x))
        hL1 hL2]
  rw [hsplitL,
    int_Th_H1 hℓ hThm hThb hkm hkb hksym hp,
    int_Th_H2 hℓ hThm hThb hkm hkb hksym hp,
    int_Th_H3 hℓ hThm hThb hkm hkb hksym hp,
    int_Th_kk hℓ hThm hThb hp]
  have hkm' : Measurable (fun x : Xn n => k (x p.1) (x p.2)) :=
    hkm.comp (Measurable.prodMk (measurable_pi_apply p.1) (measurable_pi_apply p.2))
  have hkb' : ∀ x : Xn n, |k (x p.1) (x p.2)| ≤ CK := fun x => hCKb _ _
  have hR1 : IntegrableOn (fun x : Xn n =>
      aP ℓ p.1 Th x * aP ℓ p.2 Th x * k (x p.1) (x p.2)) (abx n ℓ) volume :=
    integrableOn_abox_mul3_of_bound hℓ hAm hAb hBm hBb hkm' hkb'
  have hR2 : IntegrableOn (fun x : Xn n =>
      aP ℓ p.1 Th x * aP ℓ p.1 (aP ℓ p.2 Th) x * k (x p.1) (x p.2)) (abx n ℓ) volume :=
    integrableOn_abox_mul3_of_bound hℓ hAm hAb hCcm hCcb hkm' hkb'
  have hR3 : IntegrableOn (fun x : Xn n =>
      aP ℓ p.2 Th x * aP ℓ p.1 (aP ℓ p.2 Th) x * k (x p.1) (x p.2)) (abx n ℓ) volume :=
    integrableOn_abox_mul3_of_bound hℓ hBm hBb hCcm hCcb hkm' hkb'
  have hR4 : IntegrableOn (fun x : Xn n =>
      aP ℓ p.1 (aP ℓ p.2 Th) x * aP ℓ p.1 (aP ℓ p.2 Th) x * k (x p.1) (x p.2))
      (abx n ℓ) volume :=
    integrableOn_abox_mul3_of_bound hℓ hCcm hCcb hCcm hCcb hkm' hkb'
  -- the right-hand expansion
  rw [show (∫ x in abx n ℓ,
        (aP ℓ p.1 Th x - aP ℓ p.1 (aP ℓ p.2 Th) x)
          * (aP ℓ p.2 Th x - aP ℓ p.1 (aP ℓ p.2 Th) x) * k (x p.1) (x p.2))
      = ∫ x in abx n ℓ, ((aP ℓ p.1 Th x * aP ℓ p.2 Th x * k (x p.1) (x p.2)
            - aP ℓ p.1 Th x * aP ℓ p.1 (aP ℓ p.2 Th) x * k (x p.1) (x p.2))
          - aP ℓ p.2 Th x * aP ℓ p.1 (aP ℓ p.2 Th) x * k (x p.1) (x p.2))
        + aP ℓ p.1 (aP ℓ p.2 Th) x * aP ℓ p.1 (aP ℓ p.2 Th) x * k (x p.1) (x p.2) from
      integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)]
  rw [MeasureTheory.integral_add
        (f := fun x : Xn n => (aP ℓ p.1 Th x * aP ℓ p.2 Th x * k (x p.1) (x p.2)
            - aP ℓ p.1 Th x * aP ℓ p.1 (aP ℓ p.2 Th) x * k (x p.1) (x p.2))
          - aP ℓ p.2 Th x * aP ℓ p.1 (aP ℓ p.2 Th) x * k (x p.1) (x p.2))
        (g := fun x : Xn n => aP ℓ p.1 (aP ℓ p.2 Th) x * aP ℓ p.1 (aP ℓ p.2 Th) x
          * k (x p.1) (x p.2))
        ((hR1.sub hR2).sub hR3) hR4,
      MeasureTheory.integral_sub
        (f := fun x : Xn n => aP ℓ p.1 Th x * aP ℓ p.2 Th x * k (x p.1) (x p.2)
            - aP ℓ p.1 Th x * aP ℓ p.1 (aP ℓ p.2 Th) x * k (x p.1) (x p.2))
        (g := fun x : Xn n => aP ℓ p.2 Th x * aP ℓ p.1 (aP ℓ p.2 Th) x
            * k (x p.1) (x p.2))
        (hR1.sub hR2) hR3,
      MeasureTheory.integral_sub
        (f := fun x : Xn n => aP ℓ p.1 Th x * aP ℓ p.2 Th x * k (x p.1) (x p.2))
        (g := fun x : Xn n => aP ℓ p.1 Th x * aP ℓ p.1 (aP ℓ p.2 Th) x
            * k (x p.1) (x p.2))
        hR1 hR2]
  rw [int_C2_k hℓ hThm hThb hkm hkb hksym hp]

end Work.BoseBoxFock
