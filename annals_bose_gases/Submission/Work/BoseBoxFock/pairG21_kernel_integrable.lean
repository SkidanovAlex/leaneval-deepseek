import Mathlib
import Submission.Work.BoseBoxFock.pairG_supports
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
set_option synthInstance.maxSize 1024
set_option synthInstance.maxHeartbeats 400000

namespace Work.BoseBoxFock

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn

/-! ## Elementary tools -/

/-- **A measurable, everywhere bounded function supported in a set of finite measure is
integrable.**  (The general-measure-space form of `Work.BoseBoxFock.integrable_of_bounded_support`;
the proof is the same: restrict to `s` and use `IntegrableOn.of_bound`.) -/
theorem pairG21_integrable_of_bounded_support {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : Set α} (hs : μ s < ⊤) {f : α → ℂ} (hm : Measurable f)
    (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) (hsup : Function.support f ⊆ s) : Integrable f μ := by
  obtain ⟨C, hC⟩ := hb
  refine (MeasureTheory.integrableOn_iff_integrable_of_support_subset (μ := μ) (s := s)
    (f := f) hsup).mp ?_
  exact MeasureTheory.IntegrableOn.of_bound (s := s) (μ := μ) hs
    hm.aestronglyMeasurable.restrict (max C 0)
    (Filter.Eventually.of_forall fun x => le_trans (hC x) (le_max_left _ _))

/-- The box squared has finite measure. -/
theorem pairG21_volume_prod_boxL_lt_top (ℓ : ℝ) :
    volume (Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ) < (⊤ : ENNReal) :=
  IsCompact.measure_lt_top ((Work.BoseK15.corpusBox.boxL_compact ℓ).prod
    (Work.BoseK15.corpusBox.boxL_compact ℓ))

/-- The `n`-particle box `boxPow n ℓ = (boxL ℓ)^n` has finite measure (it is the product of `n`
copies of the compact one-particle box). -/
theorem pairG21_volume_boxPow_lt_top {n : ℕ} (ℓ : ℝ) :
    volume (Work.MB.boxPow n ℓ) < (⊤ : ENNReal) :=
  IsCompact.measure_lt_top (isCompact_univ_pi (fun _ => Work.BoseK15.corpusBox.boxL_compact ℓ))

/-- The mixed product of the `n`-particle box with the box squared has finite measure. -/
theorem pairG21_volume_prod_boxPow_boxL_lt_top {n : ℕ} (ℓ : ℝ) :
    volume (Work.MB.boxPow n ℓ ×ˢ
      (Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ)) < (⊤ : ENNReal) :=
  IsCompact.measure_lt_top ((isCompact_univ_pi (fun _ => Work.BoseK15.corpusBox.boxL_compact ℓ)).prod
    ((Work.BoseK15.corpusBox.boxL_compact ℓ).prod (Work.BoseK15.corpusBox.boxL_compact ℓ)))

theorem pairG21_kernel_integrable {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2) {ℓ : ℝ}
    {Θ : Work.BoseDict.Xn n → ℂ} {A : EuclideanSpace ℝ (Fin 3) → ℂ}
    {K : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hPm : Measurable (Function.uncurry (pairG21 p Θ A)))
    (hPb : ∃ C : ℝ, ∀ u y, ‖pairG21 p Θ A u y‖ ≤ C)
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘs : Function.support Θ ⊆ Work.MB.boxPow n ℓ)
    (hAm : Measurable A) (hAb : ∃ C : ℝ, ∀ x, ‖A x‖ ≤ C)
    (hKm : Measurable (Function.uncurry K)) (hKb : ∃ C : ℝ, ∀ w y, ‖K w y‖ ≤ C) :
    MeasureTheory.Integrable (Function.uncurry (fun w y : EuclideanSpace ℝ (Fin 3) =>
        K w y * pairG21 p Θ A w y))
        (MeasureTheory.volume : MeasureTheory.Measure
          (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)))
  ∧ (∀ x : Work.BoseDict.Xn n, MeasureTheory.Integrable
      (Function.uncurry (fun y u : EuclideanSpace ℝ (Fin 3) => K u y * (star (Θ x) * A (x p.1)
        * A (x p.2) * Θ (Function.update (Function.update x p.1 y) p.2 u))))
      (MeasureTheory.volume : MeasureTheory.Measure
        (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))))
  ∧ MeasureTheory.Integrable
      (Function.uncurry (fun x : Work.BoseDict.Xn n =>
        fun z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        K z.2 z.1 * (star (Θ x) * A (x p.1) * A (x p.2)
          * Θ (Function.update (Function.update x p.1 z.1) p.2 z.2))))
      (MeasureTheory.volume : MeasureTheory.Measure (Work.BoseDict.Xn n
        × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))))
  ∧ MeasureTheory.Integrable
      (fun z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        ∫ x : Work.BoseDict.Xn n, K z.1 z.2 * (star (Θ x) * A (x p.1)
        * A (x p.2) * Θ (Function.update (Function.update x p.1 z.2) p.2 z.1)))
      (MeasureTheory.volume : MeasureTheory.Measure
        (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))) := by
  obtain ⟨CK, hCK⟩ := hKb
  obtain ⟨CP, hCP⟩ := hPb
  obtain ⟨CT, hCT⟩ := hΘb
  obtain ⟨CA, hCA⟩ := hAb
  have hCT0 : (0 : ℝ) ≤ CT := le_trans (norm_nonneg _) (hCT 0)
  have hCA0 : (0 : ℝ) ≤ CA := le_trans (norm_nonneg _) (hCA 0)
  have hCK0 : (0 : ℝ) ≤ CK := le_trans (norm_nonneg _) (hCK 0 0)
  -- the fibre is supported in the box squared
  have hGsupp : Function.support (Function.uncurry (pairG21 p Θ A)) ⊆
      Set.prod (Work.BoseK15.corpusBox.boxL ℓ) (Work.BoseK15.corpusBox.boxL ℓ) :=
    (pairG_supports p hp (A := A) (B := A) hΘs).2.2
  -- the two-fold update keeps the values inserted
  have hupd_fst : ∀ (z : Xn n) (y u : E3),
      Function.update (Function.update z p.1 y) p.2 u p.1 = y := by
    intro z y u
    rw [Function.update_apply, if_neg hp, Function.update_self]
  have hupd_snd : ∀ (z : Xn n) (y u : E3),
      Function.update (Function.update z p.1 y) p.2 u p.2 = u := by
    intro z y u
    rw [Function.update_apply, if_pos rfl]
  -- the state vanishes when one of the two inserted values leaves the box
  have hΘz_fst : ∀ (x : Xn n) (y u : E3), y ∉ Work.BoseK15.corpusBox.boxL ℓ →
      Θ (Function.update (Function.update x p.1 y) p.2 u) = 0 := fun x y u hy =>
    theta_eq_zero_of_coord_notMem hΘs (j := p.1) (by rw [hupd_fst x y u]; exact hy)
  have hΘz_snd : ∀ (x : Xn n) (y u : E3), u ∉ Work.BoseK15.corpusBox.boxL ℓ →
      Θ (Function.update (Function.update x p.1 y) p.2 u) = 0 := fun x y u hu =>
    theta_eq_zero_of_coord_notMem hΘs (j := p.2) (by rw [hupd_snd x y u]; exact hu)
  -- the norm bound of the four state factors
  have hFac : ∀ (x : Xn n) (y u : E3),
      ‖star (Θ x) * A (x p.1) * A (x p.2)
        * Θ (Function.update (Function.update x p.1 y) p.2 u)‖ ≤ CT * CA * CA * CT := by
    intro x y u
    have h1 : ‖Θ x‖ ≤ CT := hCT x
    have h2 : ‖A (x p.1)‖ ≤ CA := hCA _
    have h3 : ‖A (x p.2)‖ ≤ CA := hCA _
    have h4 : ‖Θ (Function.update (Function.update x p.1 y) p.2 u)‖ ≤ CT := hCT _
    rw [norm_mul, norm_mul, norm_mul, norm_star]
    exact mul_le_mul (mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) hCT0) h3 (norm_nonneg _)
      (mul_nonneg hCT0 hCA0)) h4 (norm_nonneg _) (mul_nonneg (mul_nonneg hCT0 hCA0) hCA0)
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the kernel pairing against the fibre
    have hmeas : Measurable (Function.uncurry (fun w y : E3 =>
        K w y * pairG21 p Θ A w y)) := hKm.mul hPm
    have hbdd : ∃ C : ℝ, ∀ z : E3 × E3,
        ‖Function.uncurry (fun w y : E3 => K w y * pairG21 p Θ A w y) z‖ ≤ C := by
      refine ⟨CK * CP, fun z => ?_⟩
      rw [Function.uncurry_apply_pair, norm_mul]
      exact mul_le_mul (hCK _ _) (hCP _ _) (norm_nonneg _) hCK0
    have hsup : Function.support (Function.uncurry (fun w y : E3 =>
        K w y * pairG21 p Θ A w y)) ⊆
        Set.prod (Work.BoseK15.corpusBox.boxL ℓ) (Work.BoseK15.corpusBox.boxL ℓ) := by
      intro z hz
      refine hGsupp (Function.mem_support.mpr ?_)
      intro h0
      refine hz ?_
      rw [Function.uncurry_apply_pair] at h0
      show K z.1 z.2 * pairG21 p Θ A z.1 z.2 = 0
      rw [h0, mul_zero]
    exact pairG21_integrable_of_bounded_support (pairG21_volume_prod_boxL_lt_top ℓ)
      hmeas hbdd hsup
  · -- the inner pairing at a fixed configuration
    intro x
    have hmeas : Measurable (Function.uncurry (fun y u : E3 => K u y * (star (Θ x) * A (x p.1)
        * A (x p.2) * Θ (Function.update (Function.update x p.1 y) p.2 u)))) := by fun_prop
    have hbdd : ∃ C : ℝ, ∀ z : E3 × E3, ‖Function.uncurry (fun y u : E3 => K u y
        * (star (Θ x) * A (x p.1) * A (x p.2)
          * Θ (Function.update (Function.update x p.1 y) p.2 u))) z‖ ≤ C := by
      refine ⟨CK * (CT * CA * CA * CT), fun z => ?_⟩
      rw [Function.uncurry_apply_pair, norm_mul]
      exact mul_le_mul (hCK _ _) (hFac x z.1 z.2) (norm_nonneg _) hCK0
    have hsup : Function.support (Function.uncurry (fun y u : E3 => K u y
        * (star (Θ x) * A (x p.1) * A (x p.2)
          * Θ (Function.update (Function.update x p.1 y) p.2 u)))) ⊆
        Set.prod (Work.BoseK15.corpusBox.boxL ℓ) (Work.BoseK15.corpusBox.boxL ℓ) := by
      intro z hz
      rw [Function.mem_support] at hz
      refine ⟨?_, ?_⟩
      · by_contra hy
        refine hz ?_
        rw [Function.uncurry_apply_pair]
        simp [hΘz_fst x z.1 z.2 hy]
      · by_contra hu
        refine hz ?_
        rw [Function.uncurry_apply_pair]
        simp [hΘz_snd x z.1 z.2 hu]
    exact pairG21_integrable_of_bounded_support (pairG21_volume_prod_boxL_lt_top ℓ)
      hmeas hbdd hsup
  · -- the joint (configuration, kernel pair) integrand
    have hmeas : Measurable (Function.uncurry (fun x : Xn n => fun z : E3 × E3 => K z.2 z.1
        * (star (Θ x) * A (x p.1) * A (x p.2)
          * Θ (Function.update (Function.update x p.1 z.1) p.2 z.2)))) := by fun_prop
    have hbdd : ∃ C : ℝ, ∀ q : Xn n × (E3 × E3),
        ‖Function.uncurry (fun x : Xn n => fun z : E3 × E3 => K z.2 z.1
          * (star (Θ x) * A (x p.1) * A (x p.2)
            * Θ (Function.update (Function.update x p.1 z.1) p.2 z.2))) q‖ ≤ C := by
      refine ⟨CK * (CT * CA * CA * CT), fun q => ?_⟩
      rw [Function.uncurry_apply_pair, norm_mul]
      exact mul_le_mul (hCK _ _) (hFac q.1 q.2.1 q.2.2) (norm_nonneg _) hCK0
    have hsup : Function.support (Function.uncurry (fun x : Xn n => fun z : E3 × E3 => K z.2 z.1
        * (star (Θ x) * A (x p.1) * A (x p.2)
          * Θ (Function.update (Function.update x p.1 z.1) p.2 z.2)))) ⊆
        Set.prod (Work.MB.boxPow n ℓ)
          (Set.prod (Work.BoseK15.corpusBox.boxL ℓ) (Work.BoseK15.corpusBox.boxL ℓ)) := by
      intro q hq
      rw [Function.mem_support] at hq
      refine ⟨?_, ?_, ?_⟩
      · by_contra hx
        refine hq ?_
        rw [Function.uncurry_apply_pair]
        have h0 : Θ q.1 = 0 := by
          by_contra h
          exact hx (hΘs (Function.mem_support.mpr h))
        simp [h0]
      · by_contra hy
        refine hq ?_
        rw [Function.uncurry_apply_pair]
        simp [hΘz_fst q.1 q.2.1 q.2.2 hy]
      · by_contra hu
        refine hq ?_
        rw [Function.uncurry_apply_pair]
        simp [hΘz_snd q.1 q.2.1 q.2.2 hu]
    exact pairG21_integrable_of_bounded_support (pairG21_volume_prod_boxPow_boxL_lt_top ℓ)
      hmeas hbdd hsup
  · -- the parameter integral
    have hjoint : Measurable (fun q : (E3 × E3) × Xn n => K q.1.1 q.1.2
        * (star (Θ q.2) * A (q.2 p.1) * A (q.2 p.2)
          * Θ (Function.update (Function.update q.2 p.1 q.1.2) p.2 q.1.1))) := by fun_prop
    have hmeas : Measurable (fun z : E3 × E3 => ∫ x : Xn n, K z.1 z.2
        * (star (Θ x) * A (x p.1) * A (x p.2)
          * Θ (Function.update (Function.update x p.1 z.2) p.2 z.1))) :=
      (StronglyMeasurable.integral_prod_right' (α := E3 × E3) (β := Xn n)
        (ν := (volume : Measure (Xn n)))
        (f := fun q : (E3 × E3) × Xn n => K q.1.1 q.1.2
          * (star (Θ q.2) * A (q.2 p.1) * A (q.2 p.2)
            * Θ (Function.update (Function.update q.2 p.1 q.1.2) p.2 q.1.1)))
        hjoint.stronglyMeasurable).measurable
    have hbdd : ∃ C : ℝ, ∀ z : E3 × E3, ‖∫ x : Xn n, K z.1 z.2
        * (star (Θ x) * A (x p.1) * A (x p.2)
          * Θ (Function.update (Function.update x p.1 z.2) p.2 z.1))‖ ≤ C := by
      refine ⟨CK * ((CT * CA * CA * CT) * (volume (Work.MB.boxPow n ℓ)).toReal), fun z => ?_⟩
      rw [MeasureTheory.integral_const_mul, norm_mul]
      refine mul_le_mul (hCK _ _) ?_ (norm_nonneg _) hCK0
      have hg : ∀ x : Xn n, ‖star (Θ x) * A (x p.1) * A (x p.2)
          * Θ (Function.update (Function.update x p.1 z.2) p.2 z.1)‖ ≤ CT * CA * CA * CT :=
        fun x => hFac x z.2 z.1
      have hsupp : ∀ x : Xn n, x ∉ Work.MB.boxPow n ℓ → star (Θ x) * A (x p.1) * A (x p.2)
          * Θ (Function.update (Function.update x p.1 z.2) p.2 z.1) = 0 := by
        intro x hx
        have h0 : Θ x = 0 := by
          by_contra h
          exact hx (hΘs (Function.mem_support.mpr h))
        simp [h0]
      rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hsupp]
      exact MeasureTheory.norm_setIntegral_le_of_norm_le_const
        (pairG21_volume_boxPow_lt_top (n := n) ℓ) (fun x _ => hg x)
    have hsup : Function.support (fun z : E3 × E3 => ∫ x : Xn n, K z.1 z.2
        * (star (Θ x) * A (x p.1) * A (x p.2)
          * Θ (Function.update (Function.update x p.1 z.2) p.2 z.1))) ⊆
        Set.prod (Work.BoseK15.corpusBox.boxL ℓ) (Work.BoseK15.corpusBox.boxL ℓ) := by
      intro z hz
      rw [Function.mem_support] at hz
      refine ⟨?_, ?_⟩
      · by_contra h
        refine hz ?_
        have hzero : (fun x : Xn n => K z.1 z.2 * (star (Θ x) * A (x p.1) * A (x p.2)
            * Θ (Function.update (Function.update x p.1 z.2) p.2 z.1))) = fun _ => 0 := by
          funext x
          have h0 := hΘz_snd x z.2 z.1 h
          simp [h0]
        rw [hzero, integral_zero]
      · by_contra h
        refine hz ?_
        have hzero : (fun x : Xn n => K z.1 z.2 * (star (Θ x) * A (x p.1) * A (x p.2)
            * Θ (Function.update (Function.update x p.1 z.2) p.2 z.1))) = fun _ => 0 := by
          funext x
          have h0 := hΘz_fst x z.2 z.1 h
          simp [h0]
        rw [hzero, integral_zero]
    exact pairG21_integrable_of_bounded_support (pairG21_volume_prod_boxL_lt_top ℓ)
      hmeas hbdd hsup

end Work.BoseBoxFock
