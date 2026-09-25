import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.mz_square_function_finsupp

open MeasureTheory
open scoped ENNReal BigOperators

set_option maxHeartbeats 1000000

namespace Work.BourgainPlan.IonescuWainger

/-! ## A domain-general Marcinkiewicz–Zygmund

The proofs of `mz_square_function` and `mz_square_function_finsupp` use the domain of the
operators `T i` in only two ways: it must be a `ℂ`-module (so that the Rademacher combinations
`Σ_t ± f t` live in it and linearity may be applied), and it must come with a linear map `ρ` to
functions (so that the pointwise Rademacher/Khintchine lemmas may be applied to the *values*).
We isolate that abstract statement once, so that any domain — in particular the Hilbert space
`ℓ²(ℤ)` — can be fed in. -/

/-- The coefficients of an `ℓ²(ℤ)`-element as a `ℂ`-linear map. -/
noncomputable def lpCoeFnLM : lp (fun _ : ℤ => ℂ) 2 →ₗ[ℂ] (ℤ → ℂ) where
  toFun v := ⇑v
  map_add' v w := by ext n; rfl
  map_smul' c v := by ext n; rfl

lemma lpCoeFnLM_apply (v : lp (fun _ : ℤ => ℂ) 2) : (lpCoeFnLM v : ℤ → ℂ) = ⇑v := rfl

/-- **Marcinkiewicz–Zygmund for an abstract linear domain.**  Let `M` be a `ℂ`-module together with
a `ℂ`-linear map `ρ : M →ₗ (X → ℂ)` ("the coefficients"), and let `T : ι → M → (Y → ℂ)` be a
finite family of `ℂ`-linear maps.  If every signed combination `Σ_i ε_i T_i` satisfies the `Lᵖ`
bound with constant `A` — on the domain `M`, the right-hand side being the `ρ`-norm of the input —
then the square function of the outputs over an arbitrary finite family `(f t) ⊂ M` obeys the same
bound with a constant depending only on `p`.

This is the proof of `mz_square_function` with the domain `X → ℂ` replaced by the abstract `M`; it
is what makes the statement available for the Hilbert space `ℓ²(ℤ)`, on which the torsion arc
multipliers `Op_{m;𝕋[Q]}` act as honest linear maps (`opMulLM`). -/
theorem mz_square_function_dom {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : MeasureTheory.Measure X) (ν : MeasureTheory.Measure Y) {p : ℝ} (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι κ : Type} [Fintype ι] [Fintype κ]
      {M : Type} [AddCommMonoid M] [Module ℂ M] (ρ : M →ₗ[ℂ] (X → ℂ))
      (T : ι → M → (Y → ℂ))
      (hlin : ∀ i, IsLinearMap ℂ (T i))
      (hmeas : ∀ (i : ι) (f : M), AEMeasurable (T i f) ν)
      (A : ℝ) (hA : 0 ≤ A)
      (hT : ∀ (ε : ι → Bool) (f : M),
        ∫⁻ y, ‖∑ i : ι, (if ε i then (1 : ℂ) else -1) * T i f y‖ₑ ^ p ∂ν
          ≤ ENNReal.ofReal (A ^ p) * ∫⁻ x, ‖ρ f x‖ₑ ^ p ∂μ)
      (f : κ → M),
      ∫⁻ y, (∑ i : ι, ∑ t : κ, ‖T i (f t) y‖ₑ ^ (2 : ℝ)) ^ (p / 2) ∂ν
        ≤ ENNReal.ofReal (C * A ^ p)
          * ∫⁻ x, (∑ t : κ, ‖ρ (f t) x‖ₑ ^ (2 : ℝ)) ^ (p / 2) ∂μ := by
  obtain ⟨c, hcpos, hc⟩ := rademacher_two_stage_lower p hp
  obtain ⟨Ck, hCkpos, hCk⟩ := rademacher_one_stage_upper p hp
  refine ⟨(1/c) * Ck, by positivity, ?_⟩
  intro ι κ hι hκ M hM hMod ρ T hlin hmeas A hA hT f
  classical
  set F : (κ → Bool) → M := fun η => ∑ t : κ, (if η t then (1 : ℂ) else -1) • f t with hF
  set V : (ι → Bool) → (κ → Bool) → (Y → ℂ) :=
    fun ε η => ∑ i : ι, (if ε i then (1 : ℂ) else -1) • T i (F η) with hV
  set S : Y → ENNReal :=
    fun y => (∑ i : ι, ∑ t : κ, ‖T i (f t) y‖ₑ ^ (2 : ℝ)) ^ (p / 2) with hS
  set G : X → ENNReal :=
    fun x => (∑ t : κ, ‖ρ (f t) x‖ₑ ^ (2 : ℝ)) ^ (p / 2) with hG
  set P : ENNReal := ∫⁻ y, S y ∂ν with hP
  set Q : ENNReal := ∫⁻ x, G x ∂μ with hQ
  change P ≤ ENNReal.ofReal (((1/c) * Ck) * A ^ p) * Q
  have hNa : ((Fintype.card (ι → Bool) : ENNReal) * (Fintype.card (κ → Bool) : ENNReal))⁻¹
      * ((Fintype.card (ι → Bool) : ENNReal) * (Fintype.card (κ → Bool) : ENNReal)) = 1 :=
    ENNReal.inv_mul_cancel (by simp [mul_eq_zero]) (by simp [ENNReal.mul_ne_top])
  have hint1 : ∫⁻ y, ENNReal.ofReal c * S y ∂ν = ENNReal.ofReal c * P :=
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hFapp : ∀ (η : κ → Bool) (x : X),
      ρ (F η) x = ∑ t : κ, (if η t then (1 : ℂ) else -1) * (ρ (f t) x) := by
    intro η x
    simp only [hF, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
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
      ∫⁻ y, ‖V ε η y‖ₑ ^ p ∂ν ≤ ENNReal.ofReal (A ^ p) * ∫⁻ x, ‖ρ (F η) x‖ₑ ^ p ∂μ := by
    intro ε η
    have h := hT ε (F η)
    have hEq : (fun y : Y => ‖∑ i : ι, (if ε i then (1 : ℂ) else -1) * (T i (F η) y)‖ₑ ^ p)
        = fun y : Y => ‖V ε η y‖ₑ ^ p := by
      funext y
      rw [hVapp ε η y]
    rwa [hEq] at h
  have hsum2 : (∑ ε : ι → Bool, ∑ η : κ → Bool, ∫⁻ y, ‖V ε η y‖ₑ ^ p ∂ν)
      ≤ ENNReal.ofReal (A ^ p) * ((Fintype.card (ι → Bool) : ENNReal)
          * (∑ η : κ → Bool, ∫⁻ x, ‖ρ (F η) x‖ₑ ^ p ∂μ)) := by
    calc ∑ ε : ι → Bool, ∑ η : κ → Bool, ∫⁻ y, ‖V ε η y‖ₑ ^ p ∂ν
        ≤ ∑ ε : ι → Bool, ∑ η : κ → Bool,
            ENNReal.ofReal (A ^ p) * ∫⁻ x, ‖ρ (F η) x‖ₑ ^ p ∂μ :=
          Finset.sum_le_sum fun ε _ => Finset.sum_le_sum fun η _ => hVbound ε η
      _ = ∑ ε : ι → Bool, ENNReal.ofReal (A ^ p)
            * (∑ η : κ → Bool, ∫⁻ x, ‖ρ (F η) x‖ₑ ^ p ∂μ) := by
          apply Finset.sum_congr rfl
          intro ε _
          rw [Finset.mul_sum]
      _ = (Fintype.card (ι → Bool) : ENNReal)
            * (ENNReal.ofReal (A ^ p) * (∑ η : κ → Bool, ∫⁻ x, ‖ρ (F η) x‖ₑ ^ p ∂μ)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = ENNReal.ofReal (A ^ p) * ((Fintype.card (ι → Bool) : ENNReal)
            * (∑ η : κ → Bool, ∫⁻ x, ‖ρ (F η) x‖ₑ ^ p ∂μ)) := by ring
  have hXpt : ∀ x : X, (∑ η : κ → Bool, ‖ρ (F η) x‖ₑ ^ p)
      ≤ (Fintype.card (κ → Bool) : ENNReal) * (ENNReal.ofReal Ck * G x) := by
    intro x
    have h := hCk (fun t => ρ (f t) x)
    have hsum_eq : (∑ η : κ → Bool,
          ‖∑ t : κ, (if η t then (1 : ℂ) else -1) * (ρ (f t) x)‖ₑ ^ p)
        = ∑ η : κ → Bool, ‖ρ (F η) x‖ₑ ^ p := by
      refine Finset.sum_congr rfl fun η _ => ?_
      rw [← hFapp η x]
    rw [hsum_eq] at h
    calc ∑ η : κ → Bool, ‖ρ (F η) x‖ₑ ^ p
        = 1 * (∑ η : κ → Bool, ‖ρ (F η) x‖ₑ ^ p) := (one_mul _).symm
      _ = ((Fintype.card (κ → Bool) : ENNReal)⁻¹ * (Fintype.card (κ → Bool) : ENNReal))
            * (∑ η : κ → Bool, ‖ρ (F η) x‖ₑ ^ p) := by
          rw [ENNReal.inv_mul_cancel (by simp) (ENNReal.natCast_ne_top _)]
      _ = (Fintype.card (κ → Bool) : ENNReal)
            * ((∑ η : κ → Bool, ‖ρ (F η) x‖ₑ ^ p)
                * (Fintype.card (κ → Bool) : ENNReal)⁻¹) := by ring
      _ ≤ (Fintype.card (κ → Bool) : ENNReal)
            * (ENNReal.ofReal Ck * (∑ t : κ, ‖ρ (f t) x‖ₑ ^ (2 : ℝ)) ^ (p / 2)) :=
          mul_le_mul_right h _
      _ = (Fintype.card (κ → Bool) : ENNReal) * (ENNReal.ofReal Ck * G x) := rfl
  have hXsum : (∑ η : κ → Bool, ∫⁻ x, ‖ρ (F η) x‖ₑ ^ p ∂μ)
      ≤ (Fintype.card (κ → Bool) : ENNReal) * (ENNReal.ofReal Ck * Q) := by
    calc ∑ η : κ → Bool, ∫⁻ x, ‖ρ (F η) x‖ₑ ^ p ∂μ
        ≤ ∫⁻ x, ∑ η : κ → Bool, ‖ρ (F η) x‖ₑ ^ p ∂μ := mzAux_finset_sum_lintegral_le Finset.univ _
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
                * (∑ η : κ → Bool, ∫⁻ x, ‖ρ (F η) x‖ₑ ^ p ∂μ))) :=
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

/-- **Marcinkiewicz–Zygmund with the Hilbert space `ℓ²(ℤ)` as its domain.**  The corpus already has the version with the domain `ℤ →₀ ℂ` (`Work.BourgainPlan.IonescuWainger.mz_square_function_finsupp`) and the full-space version (`mz_square_function`); this is the domain on which the *torsion arc multipliers* `Op_{m;𝕋[Q]}` act as honest linear maps (`Work.BourgainPlan.IonescuWainger.opMulLM`), so that the symbol disposal (`Work.BourgainPlan.IonescuWainger.torsion_family_bound`, Tao's proof of `main` step (iv)) can be applied to the intermediate objects of the Ionescu–Wainger assembly, which are `ℓ²` and not finitely supported.

If every signed combination of a finite family of `ℂ`-linear operators on `ℓ²(ℤ)` satisfies the `ℓᵖ(ℤ)` bound with constant `A`, then the square function of the outputs over a further finite family of `ℓ²` inputs satisfies the same bound, with a constant depending only on `p`. -/
theorem mz_square_function_lp (p : ℝ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι κ : Type} [Fintype ι] [Fintype κ]
      (T : ι → lp (fun _ : ℤ => ℂ) 2 → (ℤ → ℂ))
      (hlin : ∀ i, IsLinearMap ℂ (T i))
      (hmeas : ∀ (i : ι) (f : lp (fun _ : ℤ => ℂ) 2), AEMeasurable (T i f) MeasureTheory.Measure.count)
      (A : ℝ) (hA : 0 ≤ A)
      (hT : ∀ (ε : ι → Bool) (f : lp (fun _ : ℤ => ℂ) 2),
        ∫⁻ y : ℤ, ‖∑ i : ι, (if ε i then (1 : ℂ) else -1) * T i f y‖ₑ ^ p
            ∂MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (A ^ p)
            * ∫⁻ y : ℤ, ‖(⇑f : ℤ → ℂ) y‖ₑ ^ p ∂MeasureTheory.Measure.count)
      (f : κ → lp (fun _ : ℤ => ℂ) 2),
      ∫⁻ y : ℤ, (∑ i : ι, ∑ t : κ, ‖T i (f t) y‖ₑ ^ (2 : ℝ)) ^ (p / 2)
          ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * A ^ p)
          * ∫⁻ y : ℤ, (∑ t : κ, ‖(⇑(f t) : ℤ → ℂ) y‖ₑ ^ (2 : ℝ)) ^ (p / 2)
              ∂MeasureTheory.Measure.count := by
  obtain ⟨C, hC, h⟩ :=
    mz_square_function_dom (X := ℤ) (Y := ℤ) MeasureTheory.Measure.count
      MeasureTheory.Measure.count (p := p) hp
  refine ⟨C, hC, ?_⟩
  intro ι κ _ _ T hlin hmeas A hA hT f
  have h' := h (M := lp (fun _ : ℤ => ℂ) 2) lpCoeFnLM T hlin hmeas A hA hT f
  have hR : ∫⁻ x : ℤ,
        (∑ t : κ, ‖((lpCoeFnLM (f t)) : ℤ → ℂ) x‖ₑ ^ (2 : ℝ)) ^ (p / 2)
        ∂MeasureTheory.Measure.count
      = ∫⁻ x : ℤ, (∑ t : κ, ‖(⇑(f t) : ℤ → ℂ) x‖ₑ ^ (2 : ℝ)) ^ (p / 2)
        ∂MeasureTheory.Measure.count := by
    refine lintegral_congr fun x => ?_
    congr 1
  rw [hR] at h'
  exact h'

end Work.BourgainPlan.IonescuWainger
