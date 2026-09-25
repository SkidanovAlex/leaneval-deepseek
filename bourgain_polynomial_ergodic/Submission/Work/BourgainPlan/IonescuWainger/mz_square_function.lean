import Mathlib
import Submission.Commons.Analysis.Walsh.exists_khintchine_hilbert
import Submission.Work.BourgainPlan.IonescuWainger.rademacher_one_stage_upper
import Submission.Work.BourgainPlan.IonescuWainger.rademacher_two_stage_lower

open MeasureTheory
open scoped ENNReal BigOperators

set_option maxHeartbeats 1000000

namespace Work.BourgainPlan.IonescuWainger

/-! ## Helper lemmas -/

lemma mzAux_isLinearMap_finset_sum {M M₂ γ : Type*} [AddCommMonoid M] [AddCommMonoid M₂]
    [Module ℂ M] [Module ℂ M₂] (L : M → M₂) (hL : IsLinearMap ℂ L) (s : Finset γ) (c : γ → ℂ)
    (g : γ → M) : L (∑ i ∈ s, c i • g i) = ∑ i ∈ s, c i • L (g i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using IsLinearMap.map_zero hL
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, hL.map_add, hL.map_smul, ih]

lemma mzAux_lintegral_fintype_sum {α ι : Type*} [Fintype ι] [MeasurableSpace α] {μ : Measure α}
    (f : ι → α → ENNReal) (hf : ∀ i, AEMeasurable (f i) μ) :
    ∫⁻ a, ∑ i, f i a ∂μ = ∑ i, ∫⁻ a, f i a ∂μ :=
  lintegral_finsetSum' Finset.univ (fun i _ => hf i)

lemma mzAux_finset_sum_lintegral_le {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    (s : Finset ι) (f : ι → α → ENNReal) :
    ∑ i ∈ s, ∫⁻ a, f i a ∂μ ≤ ∫⁻ a, ∑ i ∈ s, f i a ∂μ := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      have hstep : (∑ i ∈ insert a s, ∫⁻ x, f i x ∂μ)
          = ∫⁻ x, f a x ∂μ + ∑ i ∈ s, ∫⁻ x, f i x ∂μ := by rw [Finset.sum_insert ha]
      have hsum : (∫⁻ x, ∑ i ∈ insert a s, f i x ∂μ)
          = ∫⁻ x, (f a x + ∑ i ∈ s, f i x) ∂μ := by
        apply lintegral_congr
        intro x
        exact Finset.sum_insert ha
      rw [hstep, hsum]
      calc ∫⁻ x, f a x ∂μ + ∑ i ∈ s, ∫⁻ x, f i x ∂μ
          ≤ ∫⁻ x, f a x ∂μ + ∫⁻ x, ∑ i ∈ s, f i x ∂μ := add_le_add le_rfl ih
        _ ≤ ∫⁻ x, (f a x + ∑ i ∈ s, f i x) ∂μ := le_lintegral_add _ _

lemma mzAux_key_ennreal (a b X Z : ENNReal) (h : (a * b)⁻¹ * (a * b) = 1) :
    (a * b)⁻¹ * (X * (a * (b * Z))) = X * Z := by
  rw [show X * (a * (b * Z)) = (a * b) * (X * Z) by ring, ← mul_assoc, h, one_mul]



/-- **Marcinkiewicz–Zygmund / Rademacher square-function lemma** (Tao, arXiv:2008.05066, Theorem `mz`; MST, arXiv:1512.07518, Lemma 2.30).  Let `(T_i)_{i ∈ ι}` be a finite family of **linear** operators on functions and suppose that *every* signed combination `Σ_i ε_i T_i` satisfies the `L^p` bound with constant `A` (a scalar hypothesis only!).  Then the square function over both the operator family and an arbitrary finite family `(f_t)_{t ∈ κ}` obeys `‖(Σ_{i,t}|T_i f_t|²)^{1/2}‖_{L^p} ≤ C A ‖(Σ_t|f_t|²)^{1/2}‖_{L^p}`, with `C` depending only on `p` and the measure spaces — in particular uniformly in the index sets `ι`, `κ` and in the families.  Proof: Khintchine's inequality (the corpus's `Submission.Commons.Analysis.Walsh.exists_khintchine_hilbert` gives it in both directions with constants uniform in the number of terms — import that module) for the Rademacher system indexed by `ι × κ`: `(Σ_{i,t}|T_i f_t(y)|²)^{1/2} ≃_p (avg_{ω,ω'} ‖T^ω(F_{ω'})(y)‖^p)^{1/p}` with `T^ω = Σ_i ω_i T_i` and `F_{ω'} = Σ_t ω'_t f_t`; then the hypothesis and Khintchine again on the `X`-side; the average over `ω'` is essential for the uniformity in `κ`.  Linearity of the `T_i` is what lets `T^ω(F_{ω'}) = Σ_{i,t} ω_i ω'_t T_i f_t`. -/
theorem mz_square_function {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : MeasureTheory.Measure X) (ν : MeasureTheory.Measure Y) {p : ℝ} (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι κ : Type*} [Fintype ι] [Fintype κ]
      (T : ι → (X → ℂ) → (Y → ℂ)) (_hlin : ∀ i, IsLinearMap ℂ (T i))
      (_hmeas : ∀ (i : ι) (f : X → ℂ), AEMeasurable (T i f) ν)
      (A : ℝ) (_hA : 0 ≤ A)
      (_hT : ∀ (ε : ι → Bool) (f : X → ℂ),
        ∫⁻ y, ‖∑ i : ι, (if ε i then (1 : ℂ) else -1) * T i f y‖ₑ ^ p ∂ν
          ≤ ENNReal.ofReal (A ^ p) * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ)
      (f : κ → X → ℂ),
      ∫⁻ y, (∑ i : ι, ∑ t : κ, ‖T i (f t) y‖ₑ ^ (2 : ℝ)) ^ (p / 2) ∂ν
        ≤ ENNReal.ofReal (C * A ^ p) * ∫⁻ x, (∑ t : κ, ‖f t x‖ₑ ^ (2 : ℝ)) ^ (p / 2) ∂μ := by
  obtain ⟨c, hcpos, hc⟩ := rademacher_two_stage_lower p hp
  obtain ⟨Ck, hCkpos, hCk⟩ := rademacher_one_stage_upper p hp
  refine ⟨(1/c) * Ck, by positivity, ?_⟩
  intro ι κ hι hκ T hlin hmeas A hA hT f
  classical
  set F : (κ → Bool) → X → ℂ := fun η => ∑ t : κ, (if η t then (1 : ℂ) else -1) • f t with hF
  set V : (ι → Bool) → (κ → Bool) → Y → ℂ :=
    fun ε η => ∑ i : ι, (if ε i then (1 : ℂ) else -1) • T i (F η) with hV
  set S : Y → ENNReal := fun y => (∑ i : ι, ∑ t : κ, ‖T i (f t) y‖ₑ ^ (2 : ℝ)) ^ (p / 2) with hS
  set G : X → ENNReal := fun x => (∑ t : κ, ‖f t x‖ₑ ^ (2 : ℝ)) ^ (p / 2) with hG
  set P : ENNReal := ∫⁻ y, S y ∂ν
  set Q : ENNReal := ∫⁻ x, G x ∂μ
  change P ≤ ENNReal.ofReal (((1/c) * Ck) * A ^ p) * Q
  have hNa : ((Fintype.card (ι → Bool) : ENNReal) * (Fintype.card (κ → Bool) : ENNReal))⁻¹
      * ((Fintype.card (ι → Bool) : ENNReal) * (Fintype.card (κ → Bool) : ENNReal)) = 1 :=
    ENNReal.inv_mul_cancel (by simp [mul_eq_zero]) (by simp [ENNReal.mul_ne_top])
  have hint1 : ∫⁻ y, ENNReal.ofReal c * S y ∂ν = ENNReal.ofReal c * P :=
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hFapp : ∀ (η : κ → Bool) (x : X),
      F η x = ∑ t : κ, (if η t then (1 : ℂ) else -1) * (f t x) := by
    intro η x
    simp only [hF, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hVapp : ∀ (ε : ι → Bool) (η : κ → Bool) (y : Y),
      V ε η y = ∑ i : ι, (if ε i then (1 : ℂ) else -1) * (T i (F η) y) := by
    intro ε η y
    simp only [hV, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hTsum : ∀ (i : ι) (η : κ → Bool),
      T i (F η) = ∑ t : κ, (if η t then (1 : ℂ) else -1) • T i (f t) := by
    intro i η
    have h1 : F η = ∑ t : κ, (if η t then (1 : ℂ) else -1) • f t := rfl
    rw [h1]
    exact mzAux_isLinearMap_finset_sum (T i) (hlin i) Finset.univ
      (fun t => (if η t then (1 : ℂ) else -1)) f
  have hVexp : ∀ (ε : ι → Bool) (η : κ → Bool) (y : Y),
      V ε η y = ∑ i : ι, ∑ t : κ,
        (if ε i then (1 : ℂ) else -1) * (if η t then (1 : ℂ) else -1) * (T i (f t) y) := by
    intro ε η y
    rw [hVapp ε η y]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hTsum i η, Finset.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hmeasV : ∀ (ε : ι → Bool) (η : κ → Bool), AEMeasurable (fun y => ‖V ε η y‖ₑ ^ p) ν := by
    intro ε η
    have hsum : AEMeasurable (fun y : Y =>
        ∑ i : ι, (if ε i then (1 : ℂ) else -1) * (T i (F η) y)) ν :=
      Finset.aemeasurable_fun_sum Finset.univ (fun i _ => (hmeas i (F η)).const_mul _)
    have hEq : (fun y : Y => ∑ i : ι, (if ε i then (1 : ℂ) else -1) * (T i (F η) y))
        = V ε η := by
      funext y
      rw [hVapp ε η y]
    rw [hEq] at hsum
    exact hsum.enorm.pow aemeasurable_const
  have hpt : ∀ y : Y, ENNReal.ofReal c * S y ≤
      (∑ ε : ι → Bool, ∑ η : κ → Bool, ‖V ε η y‖ₑ ^ p)
        * ((Fintype.card (ι → Bool) : ENNReal) * (Fintype.card (κ → Bool) : ENNReal))⁻¹ := by
    intro y
    have h := hc (fun i t => T i (f t) y)
    have hsum_eq : (∑ ε : ι → Bool, ∑ η : κ → Bool,
          ‖∑ i : ι, ∑ t : κ, (if ε i then (1 : ℂ) else -1) * (if η t then (1 : ℂ) else -1)
              * (T i (f t) y)‖ₑ ^ p)
        = ∑ ε : ι → Bool, ∑ η : κ → Bool, ‖V ε η y‖ₑ ^ p := by
      refine Finset.sum_congr rfl fun ε _ => Finset.sum_congr rfl fun η _ => ?_
      rw [← hVexp ε η y]
    rw [hsum_eq] at h
    exact h
  have hint2 : (∑ ε : ι → Bool, ∑ η : κ → Bool, ∫⁻ y, ‖V ε η y‖ₑ ^ p ∂ν)
      = ∫⁻ y, ∑ ε : ι → Bool, ∑ η : κ → Bool, ‖V ε η y‖ₑ ^ p ∂ν := by
    rw [mzAux_lintegral_fintype_sum (fun ε y => ∑ η : κ → Bool, ‖V ε η y‖ₑ ^ p)
      (fun ε => Finset.aemeasurable_fun_sum Finset.univ (fun η _ => hmeasV ε η))]
    apply Finset.sum_congr rfl
    intro ε _
    rw [mzAux_lintegral_fintype_sum (fun η y => ‖V ε η y‖ₑ ^ p) (fun η => hmeasV ε η)]
  have hInt1 : ENNReal.ofReal c * P ≤
      ((Fintype.card (ι → Bool) : ENNReal) * (Fintype.card (κ → Bool) : ENNReal))⁻¹
        * ∑ ε : ι → Bool, ∑ η : κ → Bool, ∫⁻ y, ‖V ε η y‖ₑ ^ p ∂ν := by
    calc ENNReal.ofReal c * P
        = ∫⁻ y, ENNReal.ofReal c * S y ∂ν := hint1.symm
      _ ≤ ∫⁻ y, (∑ ε : ι → Bool, ∑ η : κ → Bool, ‖V ε η y‖ₑ ^ p)
            * ((Fintype.card (ι → Bool) : ENNReal)
              * (Fintype.card (κ → Bool) : ENNReal))⁻¹ ∂ν := lintegral_mono hpt
      _ = ∫⁻ y, ((Fintype.card (ι → Bool) : ENNReal)
              * (Fintype.card (κ → Bool) : ENNReal))⁻¹
            * (∑ ε : ι → Bool, ∑ η : κ → Bool, ‖V ε η y‖ₑ ^ p) ∂ν := by
            apply lintegral_congr
            intro y
            exact mul_comm _ _
      _ = ((Fintype.card (ι → Bool) : ENNReal)
              * (Fintype.card (κ → Bool) : ENNReal))⁻¹
            * ∫⁻ y, ∑ ε : ι → Bool, ∑ η : κ → Bool, ‖V ε η y‖ₑ ^ p ∂ν := by
            rw [lintegral_const_mul' _ _
              (ENNReal.inv_ne_top.mpr (by simp [mul_eq_zero]))]
      _ = _ := by rw [hint2]
  have hVbound : ∀ (ε : ι → Bool) (η : κ → Bool),
      ∫⁻ y, ‖V ε η y‖ₑ ^ p ∂ν ≤ ENNReal.ofReal (A ^ p) * ∫⁻ x, ‖F η x‖ₑ ^ p ∂μ := by
    intro ε η
    have h := hT ε (F η)
    have hEq : (fun y : Y => ‖∑ i : ι, (if ε i then (1 : ℂ) else -1) * (T i (F η) y)‖ₑ ^ p)
        = fun y : Y => ‖V ε η y‖ₑ ^ p := by
      funext y
      rw [hVapp ε η y]
    rwa [hEq] at h
  have hsum2 : (∑ ε : ι → Bool, ∑ η : κ → Bool, ∫⁻ y, ‖V ε η y‖ₑ ^ p ∂ν)
      ≤ ENNReal.ofReal (A ^ p) * ((Fintype.card (ι → Bool) : ENNReal)
          * (∑ η : κ → Bool, ∫⁻ x, ‖F η x‖ₑ ^ p ∂μ)) := by
    calc ∑ ε : ι → Bool, ∑ η : κ → Bool, ∫⁻ y, ‖V ε η y‖ₑ ^ p ∂ν
        ≤ ∑ ε : ι → Bool, ∑ η : κ → Bool,
            ENNReal.ofReal (A ^ p) * ∫⁻ x, ‖F η x‖ₑ ^ p ∂μ :=
          Finset.sum_le_sum fun ε _ => Finset.sum_le_sum fun η _ => hVbound ε η
      _ = ∑ ε : ι → Bool, ENNReal.ofReal (A ^ p)
            * (∑ η : κ → Bool, ∫⁻ x, ‖F η x‖ₑ ^ p ∂μ) := by
          apply Finset.sum_congr rfl
          intro ε _
          rw [Finset.mul_sum]
      _ = (Fintype.card (ι → Bool) : ENNReal)
            * (ENNReal.ofReal (A ^ p) * (∑ η : κ → Bool, ∫⁻ x, ‖F η x‖ₑ ^ p ∂μ)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = ENNReal.ofReal (A ^ p) * ((Fintype.card (ι → Bool) : ENNReal)
            * (∑ η : κ → Bool, ∫⁻ x, ‖F η x‖ₑ ^ p ∂μ)) := by ring
  have hXpt : ∀ x : X, (∑ η : κ → Bool, ‖F η x‖ₑ ^ p)
      ≤ (Fintype.card (κ → Bool) : ENNReal) * (ENNReal.ofReal Ck * G x) := by
    intro x
    have h := hCk (fun t => f t x)
    have hsum_eq : (∑ η : κ → Bool, ‖∑ t : κ, (if η t then (1 : ℂ) else -1) * (f t x)‖ₑ ^ p)
        = ∑ η : κ → Bool, ‖F η x‖ₑ ^ p := by
      refine Finset.sum_congr rfl fun η _ => ?_
      rw [← hFapp η x]
    rw [hsum_eq] at h
    calc ∑ η : κ → Bool, ‖F η x‖ₑ ^ p
        = 1 * (∑ η : κ → Bool, ‖F η x‖ₑ ^ p) := (one_mul _).symm
      _ = ((Fintype.card (κ → Bool) : ENNReal)⁻¹ * (Fintype.card (κ → Bool) : ENNReal))
            * (∑ η : κ → Bool, ‖F η x‖ₑ ^ p) := by
          rw [ENNReal.inv_mul_cancel (by simp) (ENNReal.natCast_ne_top _)]
      _ = (Fintype.card (κ → Bool) : ENNReal)
            * ((∑ η : κ → Bool, ‖F η x‖ₑ ^ p)
                * (Fintype.card (κ → Bool) : ENNReal)⁻¹) := by ring
      _ ≤ (Fintype.card (κ → Bool) : ENNReal)
            * (ENNReal.ofReal Ck * (∑ t : κ, ‖f t x‖ₑ ^ (2 : ℝ)) ^ (p / 2)) :=
          mul_le_mul_right h _
      _ = (Fintype.card (κ → Bool) : ENNReal) * (ENNReal.ofReal Ck * G x) := rfl
  have hXsum : (∑ η : κ → Bool, ∫⁻ x, ‖F η x‖ₑ ^ p ∂μ)
      ≤ (Fintype.card (κ → Bool) : ENNReal) * (ENNReal.ofReal Ck * Q) := by
    calc ∑ η : κ → Bool, ∫⁻ x, ‖F η x‖ₑ ^ p ∂μ
        ≤ ∫⁻ x, ∑ η : κ → Bool, ‖F η x‖ₑ ^ p ∂μ := mzAux_finset_sum_lintegral_le Finset.univ _
      _ ≤ ∫⁻ x, (Fintype.card (κ → Bool) : ENNReal) * (ENNReal.ofReal Ck * G x) ∂μ :=
          lintegral_mono hXpt
      _ = (Fintype.card (κ → Bool) : ENNReal) * (ENNReal.ofReal Ck * ∫⁻ x, G x ∂μ) := by
          rw [lintegral_const_mul' (Fintype.card (κ → Bool) : ENNReal)
            (fun x => ENNReal.ofReal Ck * G x) (ENNReal.natCast_ne_top _),
            lintegral_const_mul' (ENNReal.ofReal Ck) G ENNReal.ofReal_ne_top]
      _ = (Fintype.card (κ → Bool) : ENNReal) * (ENNReal.ofReal Ck * Q) := rfl
  have hchain : ENNReal.ofReal c * P ≤ ENNReal.ofReal (A ^ p) * ENNReal.ofReal Ck * Q := by
    calc ENNReal.ofReal c * P
        ≤ ((Fintype.card (ι → Bool) : ENNReal) * (Fintype.card (κ → Bool) : ENNReal))⁻¹
            * (∑ ε : ι → Bool, ∑ η : κ → Bool, ∫⁻ y, ‖V ε η y‖ₑ ^ p ∂ν) := hInt1
      _ ≤ ((Fintype.card (ι → Bool) : ENNReal) * (Fintype.card (κ → Bool) : ENNReal))⁻¹
            * (ENNReal.ofReal (A ^ p) * ((Fintype.card (ι → Bool) : ENNReal)
                * (∑ η : κ → Bool, ∫⁻ x, ‖F η x‖ₑ ^ p ∂μ))) :=
          mul_le_mul_right hsum2 _
      _ ≤ ((Fintype.card (ι → Bool) : ENNReal) * (Fintype.card (κ → Bool) : ENNReal))⁻¹
            * (ENNReal.ofReal (A ^ p) * ((Fintype.card (ι → Bool) : ENNReal)
                * ((Fintype.card (κ → Bool) : ENNReal) * (ENNReal.ofReal Ck * Q)))) := by
          refine mul_le_mul_right ?_ _
          refine mul_le_mul_right ?_ _
          exact mul_le_mul_right hXsum _
      _ = ENNReal.ofReal (A ^ p) * (ENNReal.ofReal Ck * Q) :=
          mzAux_key_ennreal _ _ _ _ hNa
      _ = ENNReal.ofReal (A ^ p) * ENNReal.ofReal Ck * Q := by ring
  have hfin : P ≤ ENNReal.ofReal (((1/c) * Ck) * A ^ p) * Q := by
    have hc0 : ENNReal.ofReal c ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hcpos)
    have hct : ENNReal.ofReal c ≠ ⊤ := ENNReal.ofReal_ne_top
    have h1 : P = (ENNReal.ofReal c)⁻¹ * (ENNReal.ofReal c * P) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]
    have h2 : (ENNReal.ofReal c)⁻¹ * (ENNReal.ofReal (A ^ p) * ENNReal.ofReal Ck * Q)
        = ENNReal.ofReal (((1/c) * Ck) * A ^ p) * Q := by
      rw [one_div, ENNReal.ofReal_mul (le_of_lt (mul_pos (inv_pos.mpr hcpos) hCkpos)),
        ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr hcpos)), ENNReal.ofReal_inv_of_pos hcpos]
      ring
    calc P = (ENNReal.ofReal c)⁻¹ * (ENNReal.ofReal c * P) := h1
      _ ≤ (ENNReal.ofReal c)⁻¹ * (ENNReal.ofReal (A ^ p) * ENNReal.ofReal Ck * Q) :=
          mul_le_mul_right hchain _
      _ = ENNReal.ofReal (((1/c) * Ck) * A ^ p) * Q := h2
  exact hfin

end Work.BourgainPlan.IonescuWainger
