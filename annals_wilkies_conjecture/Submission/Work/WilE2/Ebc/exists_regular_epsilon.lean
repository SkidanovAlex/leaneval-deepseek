import Mathlib
import Submission.Work.WilE2.Ebc.Defs
import Submission.Work.WilE2.VcbDefs
import Submission.Vendor.TauCeti.Analysis.Calculus.Sard.VanishingDerivative

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.WilE2.Ebc

open Set Filter MeasureTheory
open scoped Topology ENNReal

variable {k : ℕ}

/-! ## The ratio function `φ / (ρ² - ‖x‖²)`

The tube function `tubeFun φ ρ ε x = φ x + ε (‖x‖² - ρ²)` factorises, inside the ball `‖x‖ < ρ`,
as `(φ x / (ρ² - ‖x‖²) - ε) * (ρ² - ‖x‖²)`.  Hence, for `ε > 0`, a *degenerate* zero of
`tubeFun φ ρ ε` exists exactly when `ε` is a *critical value* of the ratio function
`φ / (ρ² - ‖x‖²)` restricted to the open ball.  The critical values of a real-analytic function of
several variables form a Lebesgue-null set (Morse–Sard in the case of a one-dimensional target,
available as `TauCeti.addHaar_image_eq_zero_of_fderiv_eq_zero`), and a null set cannot contain the
interval `(0, ε₀)`.
-/

/-- The sum of squares `∑ᵢ xᵢ²`. -/
def sqSum (x : Fin k → ℝ) : ℝ := ∑ i, (x i) ^ 2

/-- The denominator `ρ² - ∑ᵢ xᵢ²`. -/
def qrho (ρ : ℝ) (x : Fin k → ℝ) : ℝ := ρ ^ 2 - sqSum x

/-- The ratio `φ / (ρ² - ∑ᵢ xᵢ²)`. -/
noncomputable def ratioFun (φ : (Fin k → ℝ) → ℝ) (ρ : ℝ) (x : Fin k → ℝ) : ℝ := φ x / qrho ρ x

/-- The open Euclidean ball of radius `ρ`. -/
def oball (ρ : ℝ) : Set (Fin k → ℝ) := {x | sqSum x < ρ ^ 2}

@[simp] lemma sqSum_apply (x : Fin k → ℝ) : sqSum x = ∑ i, (x i) ^ 2 := rfl

@[simp] lemma qrho_apply (ρ : ℝ) (x : Fin k → ℝ) : qrho ρ x = ρ ^ 2 - ∑ i, (x i) ^ 2 := rfl

@[simp] lemma ratioFun_apply (φ : (Fin k → ℝ) → ℝ) (ρ : ℝ) (x : Fin k → ℝ) :
    ratioFun φ ρ x = φ x / (ρ ^ 2 - ∑ i, (x i) ^ 2) := rfl

@[simp] lemma mem_oball {ρ : ℝ} {x : Fin k → ℝ} :
    x ∈ oball (k := k) ρ ↔ ∑ i, (x i) ^ 2 < ρ ^ 2 := Iff.rfl

/-! ### Calculus of `∑ᵢ xᵢ²` -/

lemma hasFDerivAt_sqSum (x : Fin k → ℝ) : HasFDerivAt (fun y : Fin k → ℝ => ∑ i, (y i) ^ 2)
    (∑ i : Fin k, (2 * x i) • (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ)) x := by
  have h := HasFDerivAt.sum (𝕜 := ℝ) (u := (Finset.univ : Finset (Fin k)))
    (A := fun i (y : Fin k → ℝ) => (y i) ^ 2)
    (A' := fun i => (2 * x i) • (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ))
    (fun i _ => by
      have h1 : HasFDerivAt (fun y : Fin k → ℝ => y i)
          (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ) x := hasFDerivAt_apply i x
      convert h1.pow 2 using 1 <;> simp)
  have hfun : (∑ i, (fun y : Fin k → ℝ => (y i) ^ 2)) = (fun y : Fin k → ℝ => ∑ i, (y i) ^ 2) := by
    funext y; simp [Finset.sum_apply]
  rw [hfun] at h
  exact h

lemma differentiableAt_sqSum (x : Fin k → ℝ) :
    DifferentiableAt ℝ (fun y : Fin k → ℝ => ∑ i, (y i) ^ 2) x :=
  (hasFDerivAt_sqSum (k := k) x).differentiableAt

lemma fderiv_sqSum_apply (x v : Fin k → ℝ) :
    fderiv ℝ (fun y : Fin k → ℝ => ∑ i, (y i) ^ 2) x v = 2 * ∑ i, (x i) * (v i) := by
  rw [(hasFDerivAt_sqSum (k := k) x).fderiv]
  simp only [sum_apply, smul_apply, ContinuousLinearMap.proj_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-! ### Analyticity -/

lemma analyticAt_sqSum (x : Fin k → ℝ) : AnalyticAt ℝ (fun y : Fin k → ℝ => ∑ i, (y i) ^ 2) x := by
  have h := Finset.analyticAt_sum (𝕜 := ℝ) (E := (Fin k → ℝ)) (F := ℝ)
    (Finset.univ : Finset (Fin k)) (f := fun i (y : Fin k → ℝ) => (y i) ^ 2) (c := x) ?_
  · have hfun : (∑ n : Fin k, (fun y : Fin k → ℝ => (y n) ^ 2))
        = (fun y : Fin k → ℝ => ∑ n, (y n) ^ 2) := by
      funext y; simp [Finset.sum_apply]
    rw [hfun] at h
    exact h
  · intro i _
    exact (((ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ)).analyticAt x).pow 2

lemma analyticAt_qrho (ρ : ℝ) (x : Fin k → ℝ) : AnalyticAt ℝ (qrho ρ) x := by
  have h := AnalyticAt.sub (analyticAt_const (v := ρ ^ 2) (x := x)) (analyticAt_sqSum (k := k) x)
  have hfun : (fun _ : Fin k → ℝ => ρ ^ 2) - (fun y : Fin k → ℝ => ∑ i, (y i) ^ 2) = qrho ρ := rfl
  rwa [hfun] at h

lemma analyticAt_ratioFun {φ : (Fin k → ℝ) → ℝ} {ρ : ℝ} {x : Fin k → ℝ}
    (hφ : AnalyticAt ℝ φ x) (hq : qrho ρ x ≠ 0) : AnalyticAt ℝ (ratioFun φ ρ) x :=
  AnalyticAt.div hφ (analyticAt_qrho (k := k) ρ x) hq

/-! ### The factorisation of the tube function -/

lemma tubeFun_eq_mul {φ : (Fin k → ℝ) → ℝ} {ρ ε : ℝ} {x : Fin k → ℝ} (hq : qrho ρ x ≠ 0) :
    tubeFun φ ρ ε x = (ratioFun φ ρ x - ε) * qrho ρ x := by
  have h : (ratioFun φ ρ x - ε) * qrho ρ x = φ x - ε * qrho ρ x := by
    simp only [ratioFun]
    rw [sub_mul, div_mul_cancel₀ _ hq]
  rw [h]
  simp only [tubeFun, qrho, sqSum]
  ring

/-- The derivative of the tube function, in the "applied to `v`" form. -/
lemma fderiv_tubeFun_apply {φ : (Fin k → ℝ) → ℝ} {ρ ε : ℝ} (x v : Fin k → ℝ)
    (hφ : DifferentiableAt ℝ φ x) :
    fderiv ℝ (tubeFun φ ρ ε) x v = fderiv ℝ φ x v + ε * (2 * ∑ i, (x i) * (v i)) := by
  have ht : tubeFun φ ρ ε = φ + fun y : Fin k → ℝ => ε * (∑ i, (y i) ^ 2 - ρ ^ 2) := by
    funext y; simp [tubeFun]
  have h2 : DifferentiableAt ℝ (fun y : Fin k → ℝ => ε * (∑ i, (y i) ^ 2 - ρ ^ 2)) x :=
    ((differentiableAt_sqSum (k := k) x).sub_const (ρ ^ 2)).const_mul ε
  have h3 : fderiv ℝ (fun y : Fin k → ℝ => ε * (∑ i, (y i) ^ 2 - ρ ^ 2)) x
      = ε • fderiv ℝ (fun y : Fin k → ℝ => ∑ i, (y i) ^ 2) x := by
    rw [fderiv_const_mul ((differentiableAt_sqSum (k := k) x).sub_const (ρ ^ 2)) ε,
      fderiv_sub_const]
  rw [ht, fderiv_add hφ h2, h3]
  simp only [add_apply, smul_apply, smul_eq_mul, fderiv_sqSum_apply]

/-- The derivative of the tube function along `x`, at a point with `qrho ρ x = 0`. -/
lemma fderiv_tubeFun_self {φ : (Fin k → ℝ) → ℝ} {ρ ε : ℝ} {x : Fin k → ℝ}
    (hφ : DifferentiableAt ℝ φ x) (hφ0 : fderiv ℝ φ x x = 0) (h0 : qrho ρ x = 0) :
    fderiv ℝ (tubeFun φ ρ ε) x x = 2 * ε * sqSum x := by
  rw [fderiv_tubeFun_apply (k := k) x x hφ, hφ0, sqSum]
  have hsum : ∑ i, (x i) * (x i) = ∑ i, (x i) ^ 2 := Finset.sum_congr rfl (fun i _ => by ring)
  rw [hsum]
  simp only [qrho, sqSum] at h0
  linarith

/-! ### The derivative of the tube function in the factorised form -/

lemma fderiv_tubeFun_eq_smul {φ : (Fin k → ℝ) → ℝ} {ρ ε : ℝ} {x : Fin k → ℝ}
    (hφ : AnalyticAt ℝ φ x) (hq : qrho ρ x ≠ 0) :
    fderiv ℝ (tubeFun φ ρ ε) x
      = (ratioFun φ ρ x - ε) • fderiv ℝ (qrho ρ) x + qrho ρ x • fderiv ℝ (ratioFun φ ρ) x := by
  have hcont : ContinuousAt (qrho ρ) x := (analyticAt_qrho (k := k) ρ x).continuousAt
  have hev : ∀ᶠ y in 𝓝 x, qrho ρ y ≠ 0 := hcont.eventually_ne hq
  have hfun : tubeFun φ ρ ε =ᶠ[𝓝 x]
      (fun y : Fin k → ℝ => (ratioFun φ ρ y - ε) * qrho ρ y) :=
    hev.mono fun y hy => tubeFun_eq_mul (φ := φ) (ρ := ρ) (ε := ε) hy
  have h1 : DifferentiableAt ℝ (fun y : Fin k → ℝ => ratioFun φ ρ y - ε) x :=
    ((analyticAt_ratioFun (k := k) hφ hq).differentiableAt).sub_const ε
  have h2 : DifferentiableAt ℝ (qrho ρ) x := (analyticAt_qrho (k := k) ρ x).differentiableAt
  have hprod : (fun y : Fin k → ℝ => (ratioFun φ ρ y - ε) * qrho ρ y)
      = (fun y : Fin k → ℝ => ratioFun φ ρ y - ε) * (qrho ρ) := by
    funext y; rfl
  rw [hfun.fderiv_eq, hprod, fderiv_mul h1 h2, fderiv_sub_const]

/-! ### Bad parameters versus critical values -/

/-- **A degenerate zero of the tube function is a critical value of the ratio function.**
If `ε > 0` and `tubeFun φ ρ ε` has a zero at which its derivative vanishes, then that value `ε`
occurs as the value of the ratio function at a *critical point* inside the open ball. -/
lemma bad_imp_critValue {φ : (Fin k → ℝ) → ℝ} (hφ : AnalyticOn ℝ φ Set.univ)
    (hφnn : ∀ x, 0 ≤ φ x) {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) {x : Fin k → ℝ}
    (h1 : tubeFun φ ρ ε x = 0) (h2 : fderiv ℝ (tubeFun φ ρ ε) x = 0) :
    ∃ y ∈ oball (k := k) ρ, ratioFun φ ρ y = ε ∧ fderiv ℝ (ratioFun φ ρ) y = 0 := by
  have hφx : AnalyticAt ℝ φ x := hφ.analyticAt (by simp)
  have hφd : DifferentiableAt ℝ φ x := hφx.differentiableAt
  have hval : φ x = ε * qrho ρ x := by
    have h := h1
    rw [tubeFun] at h
    simp only [qrho, sqSum]
    linarith
  have hqnn : 0 ≤ qrho ρ x := by
    have h : 0 ≤ ε * qrho ρ x := by rw [← hval]; exact hφnn x
    exact (mul_nonneg_iff_of_pos_left hε).mp h
  rcases lt_or_eq_of_le hqnn with hq | hq
  · have hr : ratioFun φ ρ x = ε := by
      have hq' : ρ ^ 2 - ∑ i, (x i) ^ 2 ≠ 0 := by
        simp only [qrho, sqSum] at hq
        linarith
      simp only [ratioFun, qrho, sqSum]
      rw [div_eq_iff hq']
      simpa only [qrho, sqSum] using hval
    refine ⟨x, ?_, hr, ?_⟩
    · simp only [mem_oball, sqSum]
      simp only [qrho, sqSum] at hq
      linarith
    · have hd := fderiv_tubeFun_eq_smul (k := k) (φ := φ) (ρ := ρ) (ε := ε) hφx hq.ne'
      rw [hd, hr, sub_self, zero_smul, zero_add] at h2
      exact (smul_eq_zero.mp h2).resolve_left hq.ne'
  · exfalso
    have hq0 : qrho ρ x = 0 := hq.symm
    have hφ0 : φ x = 0 := by rw [hval, hq0, mul_zero]
    have hmin : IsLocalMin φ x := Eventually.of_forall fun y => by rw [hφ0]; exact hφnn y
    have hdφ : fderiv ℝ φ x = 0 := hmin.fderiv_eq_zero
    have hself := fderiv_tubeFun_self (k := k) (φ := φ) (ρ := ρ) (ε := ε) hφd
      (by rw [hdφ]; rfl) hq0
    have hzero : fderiv ℝ (tubeFun φ ρ ε) x x = 0 := by rw [h2]; rfl
    rw [hzero] at hself
    have hpos : 0 < 2 * ε * sqSum x := by
      have hs : sqSum x = ρ ^ 2 := by
        simp only [qrho, sqSum] at hq0 ⊢
        linarith
      rw [hs]
      have hρ2 : 0 < ρ ^ 2 := pow_pos hρ 2
      nlinarith [hε, hρ2]
    linarith

/-! ### Nullity of the critical values of the ratio function -/

/-- **Morse–Sard for the ratio function.**  The set of critical values of the real-analytic
function `φ / (ρ² - ‖x‖²)` on the open ball is Lebesgue-null. -/
lemma volume_critValues_ratioFun {φ : (Fin k → ℝ) → ℝ} (hφ : AnalyticOn ℝ φ Set.univ) (ρ : ℝ) :
    volume (ratioFun φ ρ '' (oball (k := k) ρ ∩ {x | fderiv ℝ (ratioFun φ ρ) x = 0})) = 0 := by
  refine TauCeti.addHaar_image_eq_zero_of_fderiv_eq_zero (ν := (volume : Measure ℝ))
    (E := Fin k → ℝ) (F := ℝ) (f := ratioFun φ ρ)
    (s := oball (k := k) ρ ∩ {x | fderiv ℝ (ratioFun φ ρ) x = 0})
    (n := ((Module.finrank ℝ (Fin k → ℝ) * Module.finrank ℝ (Fin k → ℝ) + 1 : ℕ) : WithTop ℕ∞))
    le_rfl ?_ ?_
  · rintro x hx
    have hq : qrho ρ x ≠ 0 := by
      have hx' : ∑ i, (x i) ^ 2 < ρ ^ 2 := hx.1
      simp only [qrho, sqSum]
      linarith
    exact (analyticAt_ratioFun (k := k) (hφ.analyticAt (by simp)) hq).contDiffAt
  · exact fun x hx => hx.2

/-! ### The main theorem -/

theorem exists_regular_epsilon {k : ℕ} (φ : (Fin k → ℝ) → ℝ) (hφ : AnalyticOn ℝ φ Set.univ)
    (hφnn : ∀ x, 0 ≤ φ x) (ρ : ℝ) (hρ : 0 < ρ) (hSard : SardDense) {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ ε : ℝ, 0 < ε ∧ ε < ε₀ ∧ ∀ x : Fin k → ℝ, tubeFun φ ρ ε x = 0 →
      fderiv ℝ (tubeFun φ ρ ε) x ≠ 0 := by
  set Bad : Set ℝ :=
    {ε | 0 < ε ∧ ε < ε₀ ∧ ∃ x, tubeFun φ ρ ε x = 0 ∧ fderiv ℝ (tubeFun φ ρ ε) x = 0}
  have hle : volume Bad
      ≤ volume (ratioFun φ ρ '' (oball (k := k) ρ ∩ {x | fderiv ℝ (ratioFun φ ρ) x = 0})) := by
    refine measure_mono ?_
    rintro ε ⟨hε, -, x, h1, h2⟩
    obtain ⟨y, hy, hyε, hyd⟩ := bad_imp_critValue (k := k) hφ hφnn hρ hε h1 h2
    exact ⟨y, ⟨hy, hyd⟩, hyε⟩
  rw [volume_critValues_ratioFun (k := k) hφ ρ] at hle
  have hnull : volume Bad = 0 := le_antisymm hle bot_le
  by_contra hcon
  push Not at hcon
  have hsub : Ioo (0 : ℝ) ε₀ ⊆ Bad := fun ε hε => ⟨hε.1, hε.2, hcon ε hε.1 hε.2⟩
  have hle2 : volume (Ioo (0 : ℝ) ε₀) ≤ volume Bad := measure_mono hsub
  rw [Real.volume_Ioo, hnull, tsub_zero] at hle2
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal ε₀ := ENNReal.ofReal_pos.mpr hε₀
  exact absurd hle2 (not_le.mpr hpos)

end Work.WilE2.Ebc
