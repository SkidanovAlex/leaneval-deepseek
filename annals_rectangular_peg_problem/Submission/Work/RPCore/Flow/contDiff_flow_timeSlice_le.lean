import Mathlib
import Submission.Work.RPCore.Defs
import Submission.Work.RPCore.Flow.Basic

/-!
# Smooth dependence of the flow on the initial condition, finite regularity

The ported development in `Submission/Work/RPCore/Port/ODE/SmoothFlow.lean` proves that the time
slices of the flow of a *smooth* vector field `X` (with a global bound on `‖X‖` and on
`‖fderiv ℝ X‖`) are smooth, for uniformly small times, by applying the implicit function theorem
to the fixed-point equation of the Picard operator in the Banach space of continuous paths on a
small interval `[0, δ]`.

Here we run the *same* argument, but for a vector field which is only `C^n` for a natural number
`n ≥ 1`; the only ingredient that changes is the smoothness of the Picard operator in `(y, u)`,
which needs the finite-`n` Nemytskii lemma `contDiff_compCM`.

Main result: `contDiff_flow_timeSlice_le`.
-/

set_option autoImplicit false

open scoped Topology NNReal ContDiff
open Set Function Pointwise

noncomputable section

namespace Work.RPCore.Flow

open Work.RPCore.Port.ODE

/-- The Picard operator of a `C^n` field `X`, as a function of the pair (initial point, path),
is again `C^n`.  This is the finite-regularity analogue of `Port.ODE.contDiff_pic`, whose proof
uses the finite-`n` composition (Nemytskii) lemma `Port.ODE.contDiff_compCM`. -/
lemma contDiff_pic_fin {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] {n : ℕ} (X : E → E) (hX : ContDiff ℝ n X) (δ : ℝ) (hδ : 0 ≤ δ) :
    ContDiff ℝ n (fun p : E × C(Set.Icc 0 δ, E) => pic X hX.continuous δ hδ p.1 p.2) := by
  have h1 : ContDiff ℝ n (fun p : E × C(Set.Icc 0 δ, E) => constCLM δ p.1) :=
    (contDiff_constCLM δ (n : ℕ∞ω)).comp contDiff_fst
  have h2 : ContDiff ℝ n (fun p : E × C(Set.Icc 0 δ, E) =>
      primCLM δ hδ (compCM X hX.continuous p.2)) :=
    (primCLM δ hδ).contDiff.comp ((contDiff_compCM n X hX).comp contDiff_snd)
  have hfun : (fun p : E × C(Set.Icc 0 δ, E) => pic X hX.continuous δ hδ p.1 p.2)
      = fun p => constCLM δ p.1 + primCLM δ hδ (compCM X hX.continuous p.2) := by
    funext p
    rfl
  rw [hfun]
  exact h1.add h2

/-- **Local smoothness of the flow in the initial condition, finite regularity.**  For a `C^n`
field `X` (`n ≥ 1`) with `‖fderiv ℝ X‖ ≤ K` and `0 ≤ t < min 1 (1/(2(K+1)))`, the time-`t` slice
`y ↦ Φ t y` is `C^n` near any point `y₀`.  This is the finite-`n` analogue of
`Port.ODE.contDiffAt_timeSlice`. -/
lemma contDiffAt_timeSlice_fin {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] {n : ℕ} (hn : 1 ≤ n) (X : E → E)
    (hX : ContDiff ℝ n X) {K : ℝ} (hK : ∀ z, ‖fderiv ℝ X z‖ ≤ K) (Φ : ℝ → E → E)
    (hΦ : ∀ t y, ∃ γ : ℝ → E, γ 0 = y ∧ IsIntegralCurve γ (fun _ z => X z) ∧ γ t = Φ t y)
    (y₀ : E) {t : ℝ} (ht0 : 0 ≤ t) (htδ : t < min 1 (1 / (2 * (K + 1)))) :
    ContDiffAt ℝ n (fun y => Φ t y) y₀ := by
  classical
  have hK0 : 0 ≤ K := (norm_nonneg (fderiv ℝ X 0)).trans (hK 0)
  have hX1 : ContDiff ℝ 1 X := hX.of_le (by exact_mod_cast hn)
  have hXc : Continuous X := hX.continuous
  set δ : ℝ := min 1 (1 / (2 * (K + 1))) with hδdef
  have hδpos : 0 < δ := lt_min zero_lt_one (by positivity)
  have hδle : 0 ≤ δ := hδpos.le
  have hδK : δ * K < 1 := by
    have h1 : δ ≤ 1 / (2 * (K + 1)) := by rw [hδdef]; exact min_le_right _ _
    have h2 : (0:ℝ) < 2 * (K + 1) := by positivity
    calc δ * K ≤ (1 / (2 * (K + 1))) * K := mul_le_mul_of_nonneg_right h1 hK0
      _ = K / (2 * (K + 1)) := by ring
      _ < 1 := by
          rw [div_lt_one h2]
          linarith
  have hδ' : t < δ := htδ
  -- the base point: the restriction of the global curve through `y₀`
  let u₀ : C(Set.Icc 0 δ, E) :=
    ⟨fun s => (Classical.choose (hΦ 0 y₀)) s,
      ((Classical.choose_spec (hΦ 0 y₀)).2.1).continuous.comp continuous_subtype_val⟩
  have hu₀ : pic X hXc δ hδle y₀ u₀ = u₀ :=
    isFixedPt_pic_of_curve X hXc hδle (Classical.choose_spec (hΦ 0 y₀)).1
      (Classical.choose_spec (hΦ 0 y₀)).2.1
  -- smoothness of the equation
  have hGsmooth : ContDiffAt ℝ (n : ℕ∞ω)
      (fun p : E × C(Set.Icc 0 δ, E) => p.2 - pic X hXc δ hδle p.1 p.2) (y₀, u₀) :=
    (contDiff_snd.sub (contDiff_pic_fin X hX δ hδle)).contDiffAt
  -- derivative and invertibility
  have hGderiv : HasFDerivAt (fun p : E × C(Set.Icc 0 δ, E) =>
      p.2 - pic X hXc δ hδle p.1 p.2)
      (ContinuousLinearMap.snd ℝ E C(Set.Icc 0 δ, E) -
        (constCLM δ ∘L ContinuousLinearMap.fst ℝ E C(Set.Icc 0 δ, E) +
          (primCLM δ hδle ∘L derivCLM X hX1 u₀) ∘L
            ContinuousLinearMap.snd ℝ E C(Set.Icc 0 δ, E))) (y₀, u₀) :=
    hasFDerivAt_snd.sub (hasFDerivAt_pic X hX1 hXc δ hδle y₀ u₀)
  have hcomp_inr : (ContinuousLinearMap.snd ℝ E C(Set.Icc 0 δ, E) -
        (constCLM δ ∘L ContinuousLinearMap.fst ℝ E C(Set.Icc 0 δ, E) +
          (primCLM δ hδle ∘L derivCLM X hX1 u₀) ∘L
            ContinuousLinearMap.snd ℝ E C(Set.Icc 0 δ, E)))
        ∘L ContinuousLinearMap.inr ℝ E C(Set.Icc 0 δ, E)
      = 1 - primCLM δ hδle ∘L derivCLM X hX1 u₀ := by
    ext v
    simp [ContinuousLinearMap.comp_apply]
  have hBlt : ‖primCLM δ hδle ∘L derivCLM X hX1 u₀‖ < 1 := by
    refine lt_of_le_of_lt ?_ hδK
    refine (norm_primCLM_comp_le δ hδle _).trans ?_
    exact mul_le_mul_of_nonneg_left (norm_derivCLM_le hX1 hK u₀) hδle
  have hInv : ContinuousLinearMap.IsInvertible (fderiv ℝ (fun p : E × C(Set.Icc 0 δ, E) =>
      p.2 - pic X hXc δ hδle p.1 p.2) (y₀, u₀) ∘L
        ContinuousLinearMap.inr ℝ E C(Set.Icc 0 δ, E)) := by
    rw [hGderiv.fderiv, hcomp_inr]
    exact ⟨ContinuousLinearEquiv.ofUnit (Units.oneSub
        (primCLM δ hδle ∘L derivCLM X hX1 u₀) hBlt), by
      rw [show ((ContinuousLinearEquiv.ofUnit (Units.oneSub
          (primCLM δ hδle ∘L derivCLM X hX1 u₀) hBlt) :
            C(Set.Icc 0 δ, E) →L[ℝ] C(Set.Icc 0 δ, E)))
          = ((Units.oneSub (primCLM δ hδle ∘L derivCLM X hX1 u₀) hBlt :
              (C(Set.Icc 0 δ, E) →L[ℝ] C(Set.Icc 0 δ, E))ˣ) :
              C(Set.Icc 0 δ, E) →L[ℝ] C(Set.Icc 0 δ, E)) from rfl, Units.val_oneSub]⟩
  -- the implicit function
  set ψ : E → C(Set.Icc 0 δ, E) := hGsmooth.implicitFunction
    (by intro h; rw [Nat.cast_eq_zero] at h; omega) hInv with hψdef
  have hψ0 : ψ y₀ = u₀ := hGsmooth.implicitFunction_apply_self _ _
  have hψsm : ContDiffAt ℝ (n : ℕ∞ω) ψ y₀ := hGsmooth.contDiffAt_implicitFunction _ _
  have hψeq : ∀ᶠ y in 𝓝 y₀, pic X hXc δ hδle y (ψ y) = ψ y := by
    filter_upwards [hGsmooth.eventually_apply_implicitFunction
      (by intro h; rw [Nat.cast_eq_zero] at h; omega) hInv] with y hy
    have hy' : ψ y - pic X hXc δ hδle y (ψ y)
        = u₀ - pic X hXc δ hδle y₀ u₀ := hy
    rw [hu₀, sub_self] at hy'
    exact (sub_eq_zero.mp hy').symm
  -- the two fixed points coincide, by uniqueness of the fixed point of the contraction
  have hkey : ∀ᶠ y in 𝓝 y₀, ∀ s : Set.Icc 0 δ, (ψ y) s = Φ s y := by
    filter_upwards [hψeq] with y hy
    intro s
    let uy : C(Set.Icc 0 δ, E) := ⟨fun r => Φ r y,
      (isIntegralCurve_flow (lipschitzWith_lipConst hX1 hK) Φ hΦ y).continuous.comp
        continuous_subtype_val⟩
    have huy : pic X hXc δ hδle y uy = uy :=
      isFixedPt_pic_of_curve X hXc hδle (flow_zero Φ hΦ y)
        (isIntegralCurve_flow (lipschitzWith_lipConst hX1 hK) Φ hΦ y)
    have hdist : dist (ψ y) uy ≤ (δ * K) * dist (ψ y) uy := by
      calc dist (ψ y) uy = dist (pic X hXc δ hδle y (ψ y)) (pic X hXc δ hδle y uy) := by
            rw [hy, huy]
        _ ≤ (δ * K) * dist (ψ y) uy := dist_pic_le hX1 hK hXc hδle y _ _
    have hzero : dist (ψ y) uy = 0 := by
      by_contra hne
      have hpos : 0 < dist (ψ y) uy := lt_of_le_of_ne (dist_nonneg) (Ne.symm hne)
      nlinarith [hdist, hδK]
    have heq : ψ y = uy := dist_eq_zero.mp hzero
    rw [heq]
    rfl
  -- conclusion
  have hsmooth : ContDiffAt ℝ (n : ℕ∞ω) (fun y => (ψ y) ⟨t, ht0, hδ'.le⟩) y₀ := by
    have h1 := ((ContinuousMap.evalCLM ℝ ⟨t, ht0, hδ'.le⟩).contDiff
      (n := (n : ℕ∞ω))).contDiffAt.comp y₀ hψsm
    simpa [ContinuousMap.evalCLM_apply, Function.comp_def] using h1
  refine hsmooth.congr_of_eventuallyEq ?_
  filter_upwards [hkey] with y hy
  exact (hy ⟨t, ht0, hδ'.le⟩).symm

/-- **Smooth dependence on the initial condition, finite regularity.**  The time slices of the
flow of a `C^n` vector field `X` (`n ≥ 1`) with bounded value and bounded derivative are `C^n`,
for uniformly small times. -/
theorem contDiff_flow_timeSlice_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] (n : ℕ) (hn : 1 ≤ n) (X : E → E)
    (hX : ContDiff ℝ n X) (M K : ℝ) (hM : ∀ z, ‖X z‖ ≤ M) (hK : ∀ z, ‖fderiv ℝ X z‖ ≤ K)
    (Φ : ℝ → E → E)
    (hΦ : ∀ t y, ∃ γ : ℝ → E, γ 0 = y ∧ IsIntegralCurve γ (fun _ z => X z) ∧ γ t = Φ t y) :
    ∃ δ > (0 : ℝ), ∀ t, |t| ≤ δ → ContDiff ℝ n (Φ t) := by
  classical
  have hK0 : 0 ≤ K := (norm_nonneg (fderiv ℝ X 0)).trans (hK 0)
  set δ₀ : ℝ := min 1 (1 / (2 * (K + 1))) with hδ₀def
  have hδ₀pos : 0 < δ₀ := lt_min zero_lt_one (by positivity)
  -- the key step, for the field itself and for its negative
  have key : ∀ (Y : E → E), ContDiff ℝ n Y → (∀ z, ‖fderiv ℝ Y z‖ ≤ K) →
      ∀ (Ψ : ℝ → E → E),
      (∀ t y, ∃ γ : ℝ → E, γ 0 = y ∧ IsIntegralCurve γ (fun _ z => Y z) ∧ γ t = Ψ t y) →
      ∀ t : ℝ, 0 ≤ t → t < δ₀ → ContDiff ℝ n (Ψ t) := by
    intro Y hY hKY Ψ hΨ t ht0 htδ
    exact contDiff_iff_contDiffAt.mpr (fun y =>
      contDiffAt_timeSlice_fin hn Y hY hKY Ψ hΨ y ht0 htδ)
  -- the reversed field, for negative times
  have hKneg : ∀ z, ‖fderiv ℝ (fun z : E => -X z) z‖ ≤ K := by
    intro z
    have h : fderiv ℝ (fun z : E => -X z) z = -fderiv ℝ X z := by
      simpa using fderiv_neg (𝕜 := ℝ) (f := X) (x := z)
    rw [h, norm_neg]
    exact hK z
  have hΦneg : ∀ t y, ∃ γ : ℝ → E, γ 0 = y ∧
      IsIntegralCurve γ (fun _ z => -X z) ∧ γ t = (fun r y => Φ (-r) y) t y := by
    intro t y
    obtain ⟨γ, hγ0, hγint, hγval⟩ := hΦ (-t) y
    refine ⟨fun s => γ (-1 * s), ?_, ?_, ?_⟩
    · simpa using hγ0
    · have hfield3 : ((-1 : ℝ) • ((fun (_ : ℝ) (z : E) => X z) ∘ (fun x : ℝ => x * -1)))
          = (fun (_ : ℝ) (z : E) => -X z) := by
        funext r z
        simp [Function.comp_def]
      have h := hγint.comp_mul (-1)
      rw [hfield3] at h
      simpa [Function.comp_def, mul_comm] using h
    · show γ (-1 * t) = Φ (-t) y
      rw [neg_one_mul]
      exact hγval
  refine ⟨δ₀ / 2, by positivity, fun t ht => ?_⟩
  rw [abs_le] at ht
  rcases le_or_gt 0 t with ht0 | ht0
  · exact key X hX hK Φ hΦ t ht0 (by linarith [ht.2])
  · have ht' : -t < δ₀ := by linarith [ht.1]
    have h := key (fun z : E => -X z) (hX.neg) hKneg (fun r y => Φ (-r) y) hΦneg (-t)
      (by linarith) ht'
    simpa [neg_neg] using h

end Work.RPCore.Flow
