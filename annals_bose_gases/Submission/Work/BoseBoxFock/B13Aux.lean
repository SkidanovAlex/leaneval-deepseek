import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Submission.Work.BoseBoxFock.integral_fibre_two
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.B13Aux` — coordinates of the one-slot fibre of `block13_fibre`

Auxiliary vocabulary for `Work.BoseBoxFock.block13_fibre_L2`.  All objects live on the
`n`-particle configuration space `Fin n → ℝ³` (definitionally `Work.BoseDict.Xn n`), for a pair of
slots `p : Fin n × Fin n` with `p.1 ≠ p.2`:

* `I1 p` — the index type of the coordinates other than `p.2`;
* `I2 p` — the index type of the coordinates other than both `p.2` and `p.1`;
* `upd1 p a x''` — the `Fib1 p`-configuration with the slot `p.1` set to `a`;
* `upd2 p a w x''` — the full configuration with the slots `p.1`, `p.2` set to `a`, `w`;
* `res p x'` — the restriction of a `Fib1 p`-configuration to `Fib2 p`;
* `resFull p y` — the restriction of a full configuration to `Fib2 p`.

The identities `upd2 p a w x'' = fibreIns p.2 w (upd1 p a x'')`, `res p (upd1 p a x'') = x''`,
`upd1 p a x'' ⟨p.1, hp⟩ = a` are the bookkeeping of the two-step fibre decomposition of
`∫_{x : Fin n → ℝ³}` first at the slot `p.2` and then at the slot `p.1`.

Everything here is `sorry`-free.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {n : ℕ}

/-- The coordinates other than the slot `p.2`, as an index type. -/
abbrev I1 (p : Fin n × Fin n) : Type := {k : Fin n // k ≠ p.2}

/-- The coordinates other than both slots `p.2` and `p.1`, as an index type. -/
abbrev I2 (p : Fin n × Fin n) : Type := {k : Fin n // k ≠ p.2 ∧ k ≠ p.1}

/-- The coordinates other than the slot `p.2`. -/
abbrev Fib1 (p : Fin n × Fin n) : Type := I1 p → E3

/-- The coordinates other than both slots `p.2` and `p.1`. -/
abbrev Fib2 (p : Fin n × Fin n) : Type := I2 p → E3

/-- The `Fib1 p`-configuration with the slot `p.1` set to `a`. -/
def upd1 (p : Fin n × Fin n) (a : E3) (x'' : Fib2 p) : Fib1 p :=
  fun k => if h : k.1 = p.1 then a else x'' ⟨k.1, k.2, h⟩

/-- The full configuration with the slots `p.1`, `p.2` set to `a`, `w`. -/
def upd2 (p : Fin n × Fin n) (a w : E3) (x'' : Fib2 p) : Fin n → E3 :=
  fun k => if h : k = p.2 then w else if h' : k = p.1 then a else x'' ⟨k, h, h'⟩

/-- Restriction of a `Fib1 p`-configuration to the remaining coordinates `Fib2 p`. -/
def res (p : Fin n × Fin n) (x' : Fib1 p) : Fib2 p :=
  fun k => x' ⟨k.1, k.2.1⟩

/-- Restriction of a full configuration to the coordinates other than `p.2`, `p.1`. -/
def resFull (p : Fin n × Fin n) (y : Fin n → E3) : Fib2 p :=
  fun k => y k.1

theorem upd1_apply_self {p : Fin n × Fin n} {a : E3} {x'' : Fib2 p} (k : I1 p)
    (h : k.1 = p.1) : upd1 p a x'' k = a := by
  rw [upd1, dif_pos h]

theorem upd1_apply_ne {p : Fin n × Fin n} {a : E3} {x'' : Fib2 p} (k : I1 p)
    (h : ¬ k.1 = p.1) : upd1 p a x'' k = x'' ⟨k.1, k.2, h⟩ := by
  rw [upd1, dif_neg h]

theorem res_upd1 {p : Fin n × Fin n} (a : E3) (x'' : Fib2 p) : res p (upd1 p a x'') = x'' := by
  funext k
  rw [res, upd1_apply_ne ⟨k.1, k.2.1⟩ k.2.2]

/-- The value of `upd1` at the slot `p.1`. -/
@[simp] theorem upd1_apply_p1 {p : Fin n × Fin n} {hp : p.1 ≠ p.2} (a : E3) (x'' : Fib2 p) :
    upd1 p a x'' ⟨p.1, hp⟩ = a :=
  upd1_apply_self _ rfl

theorem upd1_self {p : Fin n × Fin n} {hp : p.1 ≠ p.2} (x' : Fib1 p) :
    upd1 p (x' ⟨p.1, hp⟩) (res p x') = x' := by
  funext k
  by_cases h : k.1 = p.1
  · rw [upd1_apply_self k h]
    have hk : k = (⟨p.1, hp⟩ : I1 p) := Subtype.ext h
    rw [hk]
  · rw [upd1_apply_ne k h]
    simp only [res]

theorem upd2_eq_fibreIns_upd1 {p : Fin n × Fin n} (a w : E3) (x'' : Fib2 p) :
    upd2 p a w x'' = fibreIns p.2 w (upd1 p a x'') := by
  funext k
  by_cases h : k = p.2
  · rw [upd2, dif_pos h, fibreIns, dif_pos h]
  · rw [upd2, dif_neg h, fibreIns, dif_neg h]
    by_cases h' : k = p.1
    · rw [upd1_apply_self ⟨k, h⟩ h', dif_pos h']
    · rw [upd1_apply_ne ⟨k, h⟩ h', dif_neg h']

theorem fibreIns_eq_upd2 {p : Fin n × Fin n} {hp : p.1 ≠ p.2} (w : E3) (x' : Fib1 p) :
    fibreIns p.2 w x' = upd2 p (x' ⟨p.1, hp⟩) w (res p x') := by
  rw [upd2_eq_fibreIns_upd1, upd1_self]

theorem fibreIns_apply_p1 {p : Fin n × Fin n} {hp : p.1 ≠ p.2} (w : E3) (x' : Fib1 p) :
    (fibreIns p.2 w x') p.1 = x' ⟨p.1, hp⟩ := by
  rw [fibreIns, dif_neg hp]

theorem resFull_fibreIns {p : Fin n × Fin n} (w : E3) (x' : Fib1 p) :
    resFull p (fibreIns p.2 w x') = res p x' := by
  funext k
  rw [resFull, res, fibreIns, dif_neg k.2.1]

theorem upd2_apply_p1 {p : Fin n × Fin n} (hp : p.1 ≠ p.2) (a w : E3) (x'' : Fib2 p) :
    upd2 p a w x'' p.1 = a := by
  rw [upd2, dif_neg hp, dif_pos rfl]

theorem upd2_apply_p2 {p : Fin n × Fin n} (a w : E3) (x'' : Fib2 p) :
    upd2 p a w x'' p.2 = w := by
  rw [upd2, dif_pos rfl]

theorem upd2_apply_ne {p : Fin n × Fin n} {a w : E3} {x'' : Fib2 p} {k : Fin n}
    (h : k ≠ p.2) (h' : k ≠ p.1) : upd2 p a w x'' k = x'' ⟨k, h, h'⟩ := by
  rw [upd2, dif_neg h, dif_neg h']

/-- The two-fold update of the fibre configuration is the full configuration with the slots
`p.1`, `p.2` overwritten. -/
theorem update_update_fibreIns {p : Fin n × Fin n} {hp : p.1 ≠ p.2} (w y u : E3) (x' : Fib1 p) :
    Function.update (Function.update (fibreIns p.2 w x') p.1 y) p.2 u
      = upd2 p y u (res p x') := by
  funext k
  by_cases h2 : k = p.2
  · subst h2
    rw [Function.update_self, upd2_apply_p2]
  · rw [Function.update_of_ne h2]
    by_cases h1 : k = p.1
    · subst h1
      rw [Function.update_self, upd2_apply_p1 hp]
    · rw [Function.update_of_ne h1, upd2_apply_ne h2 h1, res, fibreIns, dif_neg h2]

/-! ## Measurability of the coordinate maps -/

theorem measurable_fibreIns_fixed (p : Fin n × Fin n) (w : E3) :
    Measurable (fun x' : Fib1 p => fibreIns p.2 w x') := by
  refine measurable_pi_iff.mpr (fun k => ?_)
  by_cases h : k = p.2
  · simp only [fibreIns, dif_pos h]
    exact measurable_const
  · simp only [fibreIns, dif_neg h]
    exact (measurable_pi_apply (⟨k, h⟩ : I1 p))

theorem measurable_fibreIns_prod (p : Fin n × Fin n) :
    Measurable (fun q : E3 × Fib1 p => fibreIns p.2 q.1 q.2) := by
  refine measurable_pi_iff.mpr (fun k => ?_)
  by_cases h : k = p.2
  · simp only [fibreIns, dif_pos h]
    exact measurable_fst
  · simp only [fibreIns, dif_neg h]
    exact ((measurable_pi_apply (⟨k, h⟩ : I1 p)).comp measurable_snd)

theorem measurable_upd1_prod (p : Fin n × Fin n) :
    Measurable (fun q : E3 × Fib2 p => upd1 p q.1 q.2) := by
  refine measurable_pi_iff.mpr (fun k => ?_)
  by_cases h : k.1 = p.1
  · simp only [upd1, dif_pos h]
    exact measurable_fst
  · simp only [upd1, dif_neg h]
    exact ((measurable_pi_apply (⟨k.1, k.2, h⟩ : I2 p)).comp measurable_snd)

theorem measurable_res (p : Fin n × Fin n) : Measurable (fun x' : Fib1 p => res p x') := by
  refine measurable_pi_iff.mpr (fun k => ?_)
  exact (measurable_pi_apply (⟨k.1, k.2.1⟩ : I1 p))

theorem measurable_upd2_prod (p : Fin n × Fin n) :
    Measurable (fun q : E3 × E3 × Fib2 p => upd2 p q.1 q.2.1 q.2.2) := by
  refine measurable_pi_iff.mpr (fun k => ?_)
  by_cases h2 : k = p.2
  · simp only [upd2, dif_pos h2]
    exact measurable_snd.fst
  · by_cases h1 : k = p.1
    · simp only [upd2, dif_neg h2, dif_pos h1]
      exact measurable_fst
    · simp only [upd2, dif_neg h2, dif_neg h1]
      show Measurable (fun q : E3 × E3 × Fib2 p => q.2.2 ⟨k, h2, h1⟩)
      exact (measurable_pi_apply (⟨k, h2, h1⟩ : I2 p)).comp measurable_snd.snd

theorem measurable_upd2_res (p : Fin n × Fin n) (y : E3) :
    Measurable (fun q : Fib1 p × E3 => upd2 p y q.2 (res p q.1)) := by
  refine measurable_pi_iff.mpr (fun k => ?_)
  by_cases h2 : k = p.2
  · simp only [upd2, dif_pos h2]
    exact measurable_snd
  · by_cases h1 : k = p.1
    · simp only [upd2, dif_neg h2, dif_pos h1]
      exact measurable_const
    · simp only [upd2, dif_neg h2, dif_neg h1]
      show Measurable (fun q : Fib1 p × E3 => res p q.1 ⟨k, h2, h1⟩)
      exact (measurable_pi_apply (⟨k, h2, h1⟩ : I2 p)).comp
        ((measurable_res p).comp measurable_fst)

/-- The `u`-insertion with the `p.1`-slot of the ambient configuration free. -/
theorem measurable_upd2_res' (p : Fin n × Fin n) :
    Measurable (fun q : (E3 × Fib1 p) × E3 => upd2 p q.1.1 q.2 (res p q.1.2)) := by
  refine measurable_pi_iff.mpr (fun k => ?_)
  by_cases h2 : k = p.2
  · simp only [upd2, dif_pos h2]
    exact measurable_snd
  · by_cases h1 : k = p.1
    · simp only [upd2, dif_neg h2, dif_pos h1]
      exact measurable_fst.fst
    · simp only [upd2, dif_neg h2, dif_neg h1]
      show Measurable (fun q : (E3 × Fib1 p) × E3 => res p q.1.2 ⟨k, h2, h1⟩)
      exact (measurable_pi_apply (⟨k, h2, h1⟩ : I2 p)).comp
        ((measurable_res p).comp (measurable_snd.comp measurable_fst))

/-! ## Cauchy–Schwarz for the Bochner integral in `ℝ≥0∞` form -/

/-- Cauchy–Schwarz for the Bochner integral: the square of the norm of `∫ f g` is bounded by
the product of the `L²`-integrals of `‖f‖` and `‖g‖`. -/
theorem ofReal_norm_integral_mul_sq_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℂ} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    ENNReal.ofReal (‖∫ a, f a * g a ∂μ‖ ^ 2) ≤
      (∫⁻ a, ENNReal.ofReal (‖f a‖ ^ 2) ∂μ) * (∫⁻ a, ENNReal.ofReal (‖g a‖ ^ 2) ∂μ) := by
  have h1 : ENNReal.ofReal ‖∫ a, f a * g a ∂μ‖ ≤ ∫⁻ a, ENNReal.ofReal (‖f a * g a‖) ∂μ :=
    ENNReal.ofReal_le_of_le_toReal (norm_integral_le_lintegral_norm (fun a => f a * g a))
  have hf' : AEMeasurable (fun a => ENNReal.ofReal ‖f a‖) μ :=
    ENNReal.measurable_ofReal.comp_aemeasurable hf.norm
  have hg' : AEMeasurable (fun a => ENNReal.ofReal ‖g a‖) μ :=
    ENNReal.measurable_ofReal.comp_aemeasurable hg.norm
  have hc : Real.HolderConjugate (2 : ℝ) 2 := by rw [Real.holderConjugate_iff]; norm_num
  calc ENNReal.ofReal (‖∫ a, f a * g a ∂μ‖ ^ 2)
      = (ENNReal.ofReal ‖∫ a, f a * g a ∂μ‖) ^ 2 := ENNReal.ofReal_pow (norm_nonneg _) 2
    _ ≤ (∫⁻ a, ENNReal.ofReal (‖f a * g a‖) ∂μ) ^ 2 := pow_le_pow_left' h1 2
    _ = (∫⁻ a, ENNReal.ofReal ‖f a‖ * ENNReal.ofReal ‖g a‖ ∂μ) ^ 2 := by
        refine congrArg (fun t => t ^ 2) ?_
        refine lintegral_congr fun a => ?_
        rw [norm_mul, ENNReal.ofReal_mul (norm_nonneg _)]
    _ ≤ ((∫⁻ a, (ENNReal.ofReal ‖f a‖) ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) *
          (∫⁻ a, (ENNReal.ofReal ‖g a‖) ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ)) ^ 2 := by
        refine pow_le_pow_left' ?_ 2
        exact ENNReal.lintegral_mul_le_Lp_mul_Lq μ hc hf' hg'
    _ = (∫⁻ a, (ENNReal.ofReal ‖f a‖) ^ (2 : ℝ) ∂μ) *
          (∫⁻ a, (ENNReal.ofReal ‖g a‖) ^ (2 : ℝ) ∂μ) := by
        simp only [mul_pow]
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, ← ENNReal.rpow_natCast,
          ← ENNReal.rpow_mul]
        norm_num
    _ = (∫⁻ a, ENNReal.ofReal (‖f a‖ ^ 2) ∂μ) * (∫⁻ a, ENNReal.ofReal (‖g a‖ ^ 2) ∂μ) := by
        congr 1 <;> (refine lintegral_congr fun a => ?_)
        · exact (ENNReal.rpow_natCast (ENNReal.ofReal ‖f a‖) 2).trans
            (ENNReal.ofReal_pow (norm_nonneg (f a)) 2).symm
        · exact (ENNReal.rpow_natCast (ENNReal.ofReal ‖g a‖) 2).trans
            (ENNReal.ofReal_pow (norm_nonneg (g a)) 2).symm

end Work.BoseBoxFock
