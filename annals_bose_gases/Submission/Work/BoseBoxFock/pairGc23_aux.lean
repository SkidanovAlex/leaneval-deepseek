import Mathlib
import Submission.Work.BoseBoxFock.PairGc21Aux
import Submission.Work.BoseBoxFock.pairGBounds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
set_option synthInstance.maxSize 1024
set_option synthInstance.maxHeartbeats 400000

/-!
# `Work.BoseBoxFock.pairGc23_aux` — the measure-theoretic core of the `pairGc23_core` estimate

`pairGc23 ℓ p hp Θ₀ A B w₀ w₁` (of `pairGCore`) is the set integral over the *product box*

    K = boxPiSet {k // k ≠ p.1 ∧ k ≠ p.2} ℓ ×ˢ (boxL ℓ ×ˢ boxL ℓ)

of the integrand

    z ↦ star (Θ₀ (insertCoord2 p w₀ w₁ z.1)) * star (A z.2.1) * star (B z.2.2)
           * Θ₀ (insertCoord2 p z.2.1 z.2.2 z.1)  .

This module collects the elementary facts that every estimate for `pairGc23` uses:

* compactness / finiteness of the box `K` (`isCompact_box23`, `measure_box23_lt_top`);
* the *splitting* identity `insertCoord2 p a b x' = splitEquiv hp (x', (a, b))` and the fact that
  the measure-preserving equivalence `splitEquiv hp` carries the box `K` onto the `n`-particle box
  `abox n ℓ` (`splitEquiv_image_box23`);
* the resulting **change of variables** for the *second* state factor,
  `∫_{z ∈ K} ‖Θ₀ (insertCoord2 p z.2.1 z.2.2 z.1)‖² = pinL2 ℓ Θ₀`, which is the `g`-factor of the
  Cauchy–Schwarz estimate;
* a bound for the first state factor on a *slice*
  (`exists_bound_slice`): for fixed `(w₀, w₁)` the map `x ↦ insertCoord2 p w₀ w₁ x` sends the
  compact fibre box to a compact subset of `Xn n`, on which the continuous function `Θ₀` is bounded.
  This is what makes the `w`-dependence of `pairGc23` locally uniformly dominated (and hence, by the
  dominated convergence theorem, continuous and differentiable).

`sorry`-free.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn
local notation "boxL" => Work.BoseK15.corpusBox.boxL

/-- The fibre index type of the block II.2 (two-slot) fibre. -/
abbrev Fib23 (n : ℕ) (p : Fin n × Fin n) : Type := {k : Fin n // k ≠ p.1 ∧ k ≠ p.2}

/-- The box over which `pairGc23` integrates: the free fibre box times the two kernel boxes. -/
def box23 {n : ℕ} (ℓ : ℝ) (p : Fin n × Fin n) :
    Set ((Fib23 n p → E3) × (E3 × E3)) :=
  boxPiSet (Fib23 n p) ℓ ×ˢ (boxL ℓ ×ˢ boxL ℓ)

theorem mem_box23 {n : ℕ} {ℓ : ℝ} {p : Fin n × Fin n} {z : (Fib23 n p → E3) × (E3 × E3)} :
    z ∈ box23 ℓ p ↔ z.1 ∈ boxPiSet (Fib23 n p) ℓ ∧ z.2.1 ∈ boxL ℓ ∧ z.2.2 ∈ boxL ℓ := by
  rw [box23, Set.mem_prod, Set.mem_prod]

theorem isCompact_box23 {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n) :
    IsCompact (box23 ℓ p) := by
  rw [box23]
  exact (isCompact_boxPiSet (ι := Fib23 n p) hℓ).prod
    ((Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ).prod
      (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ))

theorem measure_box23_lt_top {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n) :
    (volume : Measure ((Fib23 n p → E3) × (E3 × E3))) (box23 ℓ p) < ⊤ :=
  lt_top_iff_ne_top.mpr (isCompact_box23 hℓ p).measure_ne_top

theorem measurableSet_box23 {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n) :
    MeasurableSet (box23 ℓ p) :=
  (isCompact_box23 hℓ p).measurableSet

/-- The integrand of `pairGc23`. -/
def gcIntegrand {n : ℕ} (p : Fin n × Fin n) (Θ₀ : Xn n → ℂ) (A B : E3 → ℂ) (w₀ w₁ : E3) :
    (Fib23 n p → E3) × (E3 × E3) → ℂ :=
  fun z => star (Θ₀ (insertCoord2 p w₀ w₁ z.1)) * star (A z.2.1) * star (B z.2.2)
              * Θ₀ (insertCoord2 p z.2.1 z.2.2 z.1)

/-- `pairGc23` is the set integral of `gcIntegrand` over the product box `box23`. -/
theorem pairGc23_eq_setIntegral {n : ℕ} {ℓ : ℝ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    (Θ₀ : Xn n → ℂ) (A B : E3 → ℂ) (w₀ w₁ : E3) :
    pairGc23 ℓ p hp Θ₀ A B w₀ w₁
      = ∫ z in box23 ℓ p, gcIntegrand p Θ₀ A B w₀ w₁ z := rfl

/-- The integrand splits into the `(w, A, B)`-factor times the *free* state factor. -/
theorem gcIntegrand_eq_mul {n : ℕ} (p : Fin n × Fin n) (Θ₀ : Xn n → ℂ) (A B : E3 → ℂ)
    (w₀ w₁ : E3) (z : (Fib23 n p → E3) × (E3 × E3)) :
    gcIntegrand p Θ₀ A B w₀ w₁ z
      = (star (Θ₀ (insertCoord2 p w₀ w₁ z.1)) * star (A z.2.1) * star (B z.2.2))
          * Θ₀ (insertCoord2 p z.2.1 z.2.2 z.1) := rfl

/-- The inserted configuration is the measure-preserving insertion `splitEquiv`. -/
theorem insertCoord2_eq_splitEquiv {n : ℕ} {p : Fin n × Fin n} (hp : p.1 ≠ p.2)
    (z : (Fib23 n p → E3) × (E3 × E3)) :
    insertCoord2 p z.2.1 z.2.2 z.1 = splitEquiv hp z := by
  obtain ⟨x', a, b⟩ := z
  simp only [insertCoord2_eq, splitEquiv_apply]

/-- **The insertion carries the product box onto the `n`-particle box.** -/
theorem splitEquiv_image_box23 {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {p : Fin n × Fin n}
    (hp : p.1 ≠ p.2) :
    splitEquiv hp '' box23 ℓ p = Submission.BoseGases.abox n ℓ := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [← insertCoord2_eq_splitEquiv hp z]
    rw [Submission.BoseGases.mem_abox_iff, ← corpusBox_boxL_eq_acube hℓ]
    have hz1 := mem_boxPiSet.mp hz.1
    have hz2 := Set.mem_prod.mp hz.2
    intro k
    simp only [insertCoord2_eq]
    by_cases h1 : k = p.1
    · rw [dif_pos h1]; exact hz2.1
    · by_cases h2 : k = p.2
      · rw [dif_neg h1, dif_pos h2]; exact hz2.2
      · rw [dif_neg h1, dif_neg h2]; exact hz1 ⟨k, h1, h2⟩
  · intro hx
    have hxab : ∀ i : Fin n, x i ∈ boxL ℓ := fun i => by
      rw [corpusBox_boxL_eq_acube hℓ]
      exact (Submission.BoseGases.mem_abox_iff n ℓ x).mp hx i
    refine ⟨(fun k => x k.1, (x p.1, x p.2)), ?_, ?_⟩
    · rw [mem_box23]
      refine ⟨?_, hxab p.1, hxab p.2⟩
      rw [mem_boxPiSet]
      intro k
      exact hxab k.1
    · rw [splitEquiv_apply]
      funext k
      by_cases h1 : k = p.1
      · rw [dif_pos h1, h1]
      · by_cases h2 : k = p.2
        · rw [dif_neg h1, dif_pos h2, h2]
        · rw [dif_neg h1, dif_neg h2]

/-- **Change of variables for the free state factor**: the box integral of
`‖Θ₀ (insertCoord2 p z.2.1 z.2.2 z.1)‖²` is `pinL2 ℓ Θ₀`. -/
theorem integral_second_eq_pinL2 {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {p : Fin n × Fin n}
    (hp : p.1 ≠ p.2) (Θ₀ : Xn n → ℂ) :
    (∫ z in box23 ℓ p, ‖Θ₀ (insertCoord2 p z.2.1 z.2.2 z.1)‖ ^ 2)
      = pinL2 ℓ Θ₀ := by
  have h := (measurePreserving_splitEquiv hp).setIntegral_image_emb
    (splitEquiv hp).measurableEmbedding (fun x : Xn n => ‖Θ₀ x‖ ^ 2) (box23 ℓ p)
  rw [splitEquiv_image_box23 hℓ hp] at h
  have h2 : (∫ z in box23 ℓ p, ‖Θ₀ (insertCoord2 p z.2.1 z.2.2 z.1)‖ ^ 2)
      = ∫ z in box23 ℓ p, ‖Θ₀ ((splitEquiv hp) z)‖ ^ 2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    refine congrArg (fun w => ‖Θ₀ w‖ ^ 2) ?_
    rw [insertCoord2_eq_splitEquiv hp z]
  rw [h2, pinL2, h]
  rfl

/-- The norm squared of the `(w, A, B)`-factor of `gcIntegrand`. -/
theorem norm_first_factor_sq {n : ℕ} (p : Fin n × Fin n) (Θ₀ : Xn n → ℂ) (A B : E3 → ℂ)
    (w₀ w₁ : E3) (z : (Fib23 n p → E3) × (E3 × E3)) :
    ‖star (Θ₀ (insertCoord2 p w₀ w₁ z.1)) * star (A z.2.1) * star (B z.2.2)‖ ^ 2
      = ‖Θ₀ (insertCoord2 p w₀ w₁ z.1)‖ ^ 2 * (‖A z.2.1‖ ^ 2 * ‖B z.2.2‖ ^ 2) := by
  rw [norm_mul, norm_mul, norm_star, norm_star, norm_star]
  ring

/-- **The `(w, A, B)`-factor of the fibre factorises**: its box integral is the slice mass
`memX23` times the two box `L²`-masses of `A` and `B`.  (The product structure makes this an
instance of `setIntegral_prod_mul`.) -/
theorem setIntegral_first_eq {n : ℕ} {ℓ : ℝ} {p : Fin n × Fin n} (Θ₀ : Xn n → ℂ) (A B : E3 → ℂ)
    (w₀ w₁ : E3) :
    (∫ z in box23 ℓ p, ‖Θ₀ (insertCoord2 p w₀ w₁ z.1)‖ ^ 2
        * (‖A z.2.1‖ ^ 2 * ‖B z.2.2‖ ^ 2))
      = memX23 ℓ p Θ₀ w₀ w₁ * ((∫ a in boxL ℓ, ‖A a‖ ^ 2) * (∫ b in boxL ℓ, ‖B b‖ ^ 2)) := by
  have hy : (∫ y in boxL ℓ ×ˢ boxL ℓ, ‖A y.1‖ ^ 2 * ‖B y.2‖ ^ 2)
      = (∫ a in boxL ℓ, ‖A a‖ ^ 2) * (∫ b in boxL ℓ, ‖B b‖ ^ 2) := by
    show (∫ y in boxL ℓ ×ˢ boxL ℓ, ‖A y.1‖ ^ 2 * ‖B y.2‖ ^ 2
        ∂((volume : Measure E3).prod (volume : Measure E3)))
      = (∫ a in boxL ℓ, ‖A a‖ ^ 2) * (∫ b in boxL ℓ, ‖B b‖ ^ 2)
    rw [MeasureTheory.setIntegral_prod_mul (μ := (volume : Measure E3))
      (ν := (volume : Measure E3)) (f := fun a : E3 => ‖A a‖ ^ 2)
      (g := fun b : E3 => ‖B b‖ ^ 2) (s := boxL ℓ) (t := boxL ℓ)]
  show (∫ z in boxPiSet (Fib23 n p) ℓ ×ˢ (boxL ℓ ×ˢ boxL ℓ),
        ‖Θ₀ (insertCoord2 p w₀ w₁ z.1)‖ ^ 2 * (‖A z.2.1‖ ^ 2 * ‖B z.2.2‖ ^ 2)
      ∂((volume : Measure (Fib23 n p → E3)).prod (volume : Measure (E3 × E3))))
    = memX23 ℓ p Θ₀ w₀ w₁ * ((∫ a in boxL ℓ, ‖A a‖ ^ 2) * (∫ b in boxL ℓ, ‖B b‖ ^ 2))
  rw [MeasureTheory.setIntegral_prod_mul (μ := (volume : Measure (Fib23 n p → E3)))
    (ν := (volume : Measure (E3 × E3)))
    (f := fun x : Fib23 n p → E3 => ‖Θ₀ (insertCoord2 p w₀ w₁ x)‖ ^ 2)
    (g := fun y : E3 × E3 => ‖A y.1‖ ^ 2 * ‖B y.2‖ ^ 2)
    (s := boxPiSet (Fib23 n p) ℓ) (t := boxL ℓ ×ˢ boxL ℓ)]
  rw [hy]
  rfl

/-- A bound for the box `L²`-mass of a bounded function. -/
theorem setIntegral_normSq_le_of_bound {f : E3 → ℂ} {c : ℝ} (hf : Measurable f)
    (hfb : ∀ x, ‖f x‖ ≤ c) (hc : 0 ≤ c) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (∫ a in boxL ℓ, ‖f a‖ ^ 2) ≤ c ^ 2 * ℓ ^ 3 := by
  have hvol : (volume (boxL ℓ)).toReal = ℓ ^ 3 := by
    rw [ofReal_volume_boxL ℓ hℓ, ENNReal.toReal_ofReal (by positivity)]
  have hfin : (volume (boxL ℓ)) < ⊤ :=
    lt_top_iff_ne_top.mpr (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ).measure_ne_top
  have h1 : |∫ a in boxL ℓ, ‖f a‖ ^ 2| ≤ c ^ 2 * (volume (boxL ℓ)).toReal := by
    rw [← Real.norm_eq_abs]
    refine norm_setIntegral_le_of_norm_le_const (f := fun a => ‖f a‖ ^ 2) hfin fun a _ => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hfb a) 2
  rw [hvol] at h1
  exact (abs_le.mp h1).2

/-- **Boundedness of the state on a slice.**  For fixed `(w₀, w₁)` the configuration
`insertCoord2 p w₀ w₁ x` runs over a compact subset of `Xn n` as `x` runs over the fibre box, so
the continuous function `Θ₀` is bounded on it. -/
theorem exists_bound_slice {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {p : Fin n × Fin n} {Θ₀ : Xn n → ℂ}
    (hΘ₀ : Continuous Θ₀) (w₀ w₁ : E3) (hp : p.1 ≠ p.2) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ boxPiSet (Fib23 n p) ℓ, ‖Θ₀ (insertCoord2 p w₀ w₁ x)‖ ≤ M := by
  have hcont : Continuous (fun x : Fib23 n p → E3 => insertCoord2 p w₀ w₁ x) :=
    continuous_insertCoord2_fixed p hp w₀ w₁
  obtain ⟨C, hC⟩ := ((isCompact_boxPiSet (ι := Fib23 n p) hℓ).image hcont).exists_bound_of_continuousOn
    (hΘ₀.continuousOn)
  exact ⟨max C 0, le_max_right _ _, fun x hx =>
    le_trans (hC _ (Set.mem_image_of_mem _ hx)) (le_max_left _ _)⟩

end Work.BoseBoxFock
