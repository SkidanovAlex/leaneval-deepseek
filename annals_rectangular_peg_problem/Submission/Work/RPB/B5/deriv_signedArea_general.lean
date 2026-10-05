import Mathlib
import Submission.Work.RPB.Defs
import Submission.Work.RPA3.deriv_deriv_swap
import Submission.Work.RPA3.hasFDerivAt_param_intervalIntegral
import Submission.Work.RPB.B4.flux_two_point
import Submission.Work.RPB.B5.contDiff_omegaC_fderiv_snd

open MeasureTheory intervalIntegral
open scoped Interval

set_option autoImplicit false

namespace Work.RPB.B5

/-!
# `deriv_signedArea_general`: the derivative of the signed area of a curve family

For a `C²` family `V : ℝ → ℝ → ℂ` whose members are `2π`-periodic, the derivative of the signed
area of the member `t ↦ V s t` with respect to `s` is the integral over one period of the
symplectic pairing of the two partial derivatives:

`d/ds ∮ ω_ℂ(V_s, ∂_t V_s) = 2 ∮ ω_ℂ(∂_s V, ∂_t V)`,

which, after the factor `1/2` in `signedArea`, is exactly the claimed identity.  The proof is the
classical one: differentiate under the integral sign (the joint integrand is `C¹` because `V` is
`C²`), expand the derivative with the product rule for the skew form `ω_ℂ`, and observe that the
`∂_t∂_s` term is the total derivative of `t ↦ ω_ℂ(V(σ,t), ∂_sV(σ,t))`, whose integral over a
period vanishes by periodicity (Schwarz's theorem, i.e. `deriv_deriv_swap`, identifies `∂_t∂_s`
with `∂_s∂_t`).

## Contents

* `deriv_curry_fst`, `deriv_curry_snd` — line partial derivatives as `fderiv` evaluations;
* `deriv_integrand`          — the pointwise product rule for the integrand;
* `deriv_signedArea_uncurried` — the theorem for an uncurried `C²` family `Φ : ℝ × ℝ → ℂ`;
* `deriv_signedArea_general` — the requested statement.
-/

/-- The partial derivative in the first variable of an uncurried family, as a `fderiv`
evaluation. -/
private lemma deriv_curry_fst (Φ : ℝ × ℝ → ℂ) (hΦ : ContDiff ℝ 2 Φ) (s t : ℝ) :
    deriv (fun u => Φ (u, t)) s = (fderiv ℝ Φ (s, t)) (1, 0) :=
  Work.RPA3.deriv_prodMk_left
    ((hΦ.differentiable (by norm_num)).differentiableAt).hasFDerivAt

/-- The partial derivative in the second variable of an uncurried family, as a `fderiv`
evaluation. -/
private lemma deriv_curry_snd (Φ : ℝ × ℝ → ℂ) (hΦ : ContDiff ℝ 2 Φ) (s t : ℝ) :
    deriv (fun u => Φ (s, u)) t = (fderiv ℝ Φ (s, t)) (0, 1) :=
  Work.RPA3.deriv_prodMk_right
    ((hΦ.differentiable (by norm_num)).differentiableAt).hasFDerivAt

/-- The pointwise derivative of the integrand `s ↦ ω_ℂ(Φ(s,t), ∂_tΦ(s,t))`, by the product rule
for the skew form `ω_ℂ` and Schwarz's theorem. -/
private lemma deriv_integrand (Φ : ℝ × ℝ → ℂ) (hΦ : ContDiff ℝ 2 Φ) (σ t : ℝ) :
    deriv (fun s => Work.RPV.ωC (Φ (s, t)) (deriv (fun u => Φ (s, u)) t)) σ =
      Work.RPV.ωC ((fderiv ℝ Φ (σ, t)) (1, 0)) ((fderiv ℝ Φ (σ, t)) (0, 1)) +
        Work.RPV.ωC (Φ (σ, t)) (deriv (fun y => (fderiv ℝ Φ (σ, y)) (1, 0)) t) := by
  have hΦd : ∀ p : ℝ × ℝ, HasFDerivAt Φ (fderiv ℝ Φ p) p :=
    fun p => ((hΦ.differentiable (by norm_num)).differentiableAt).hasFDerivAt
  have hlinA : ContDiff ℝ 2 (fun s : ℝ => Φ (s, t)) := by fun_prop
  have hA : HasDerivAt (fun s => Φ (s, t)) ((fderiv ℝ Φ (σ, t)) (1, 0)) σ := by
    have h1 : HasDerivAt (fun s => Φ (s, t)) (deriv (fun s => Φ (s, t)) σ) σ :=
      ((hlinA.differentiable (by norm_num)).differentiableAt).hasDerivAt
    rwa [deriv_curry_fst Φ hΦ σ t] at h1
  have hElin : ContDiff ℝ 1 (fun s : ℝ => fderiv ℝ Φ (s, t) (0, 1)) := by fun_prop
  have hB : HasDerivAt (fun s => deriv (fun u => Φ (s, u)) t)
      (deriv (fun s => deriv (fun u => Φ (s, u)) t) σ) σ := by
    have h2 : DifferentiableAt ℝ (fun s : ℝ => fderiv ℝ Φ (s, t) (0, 1)) σ :=
      (hElin.differentiable (by norm_num)).differentiableAt
    have heq : (fun s : ℝ => deriv (fun u => Φ (s, u)) t)
        = (fun s : ℝ => fderiv ℝ Φ (s, t) (0, 1)) := by
      funext s
      rw [Work.RPA3.deriv_prodMk_right (hΦd (s, t))]
    rw [← heq] at h2
    exact h2.hasDerivAt
  have h := (Work.RPB.B4.hasDerivAt_ωC hA hB).deriv
  rw [h, Work.RPA3.deriv_prodMk_right (hΦd (σ, t))]
  congr 1
  congr 1
  have hsw := Work.RPA3.deriv_deriv_swap (G := Φ) (a := σ) (b := t) hΦ.contDiffAt
  have heq : (fun y : ℝ => deriv (fun s => Φ (s, y)) σ)
      = (fun y : ℝ => (fderiv ℝ Φ (σ, y)) (1, 0)) := by
    funext y
    rw [deriv_curry_fst Φ hΦ σ y]
  rw [heq] at hsw
  exact hsw.symm

/-- The total-derivative identity: the integral of `ω_ℂ(Φ(σ,·), ∂_t∂_σΦ(σ,·))` over a period
equals the integral of `ω_ℂ(∂_σΦ, ∂_tΦ)` over a period, because the two integrands differ by the
total derivative `d/dt ω_ℂ(Φ(σ,t), ∂_σΦ(σ,t))` and both `Φ(σ,·)` and `∂_σΦ(σ,·)` are `2π`-periodic
in `t`. -/
private lemma integral_omegaC_mixed (Φ : ℝ × ℝ → ℂ) (hΦ : ContDiff ℝ 2 Φ)
    (hper : ∀ s t, Φ (s, t + 2 * Real.pi) = Φ (s, t)) (σ : ℝ) :
    (∫ t in (0 : ℝ)..(2 * Real.pi),
        Work.RPV.ωC (Φ (σ, t)) (deriv (fun y => (fderiv ℝ Φ (σ, y)) (1, 0)) t))
      = ∫ t in (0 : ℝ)..(2 * Real.pi),
          Work.RPV.ωC ((fderiv ℝ Φ (σ, t)) (1, 0)) ((fderiv ℝ Φ (σ, t)) (0, 1)) := by
  have hΦd : ∀ p : ℝ × ℝ, HasFDerivAt Φ (fderiv ℝ Φ p) p :=
    fun p => ((hΦ.differentiable (by norm_num)).differentiableAt).hasFDerivAt
  have hskew : ∀ a b : ℂ, Work.RPV.ωC a b = -Work.RPV.ωC b a := by
    intro a b
    rw [Work.RPB.B4.ωC_eq, Work.RPB.B4.ωC_eq]
    ring
  -- the two `2π`-periodic curves entering the cross-term lemma
  have hE1cd : ContDiff ℝ 1 (fun t : ℝ => (fderiv ℝ Φ (σ, t)) (1, 0)) := by fun_prop
  have hGcd : ContDiff ℝ 1 (fun t : ℝ => Φ (σ, t)) := by
    have hpair : ContDiff ℝ 1 (fun t : ℝ => ((σ, t) : ℝ × ℝ)) := by fun_prop
    exact (hΦ.of_le (by norm_num)).comp hpair
  have hE1per : ∀ t : ℝ,
      (fderiv ℝ Φ (σ, t + 2 * Real.pi)) (1, 0) = (fderiv ℝ Φ (σ, t)) (1, 0) := by
    intro t
    rw [← deriv_curry_fst Φ hΦ σ (t + 2 * Real.pi), ← deriv_curry_fst Φ hΦ σ t]
    congr 1
    funext s
    rw [hper s t]
  have hGper : ∀ t : ℝ, Φ (σ, t + 2 * Real.pi) = Φ (σ, t) := fun t => hper σ t
  have hcz := Work.RPB.B4.integral_omegaC_cross_zero
    (fun t : ℝ => (fderiv ℝ Φ (σ, t)) (1, 0)) (fun t : ℝ => Φ (σ, t))
    hE1cd hGcd hE1per hGper
  have hG' : ∀ t : ℝ, deriv (fun t' : ℝ => Φ (σ, t')) t = (fderiv ℝ Φ (σ, t)) (0, 1) :=
    fun t => Work.RPA3.deriv_prodMk_right (hΦd (σ, t))
  simp only [hG'] at hcz
  -- continuity of the two pieces of the (split) integrand
  have hMcont : Continuous (fun t : ℝ => deriv (fun y => (fderiv ℝ Φ (σ, y)) (1, 0)) t) := by
    have h : ContDiff ℝ 1 (fun y : ℝ => (fderiv ℝ Φ (σ, y)) (1, 0)) := by fun_prop
    exact h.continuous_deriv le_rfl
  have hΦcont : Continuous (fun t : ℝ => Φ (σ, t)) := hGcd.continuous
  have h1cont : Continuous (fun t : ℝ =>
      Work.RPV.ωC (deriv (fun y => (fderiv ℝ Φ (σ, y)) (1, 0)) t) (Φ (σ, t))) := by
    rw [funext (fun t : ℝ => Work.RPB.B4.ωC_eq
      (deriv (fun y => (fderiv ℝ Φ (σ, y)) (1, 0)) t) (Φ (σ, t))) ]
    exact ((Complex.continuous_re.comp hMcont).mul (Complex.continuous_im.comp hΦcont)).sub
      ((Complex.continuous_im.comp hMcont).mul (Complex.continuous_re.comp hΦcont))
  have hE2cont : Continuous (fun t : ℝ => (fderiv ℝ Φ (σ, t)) (0, 1)) := by
    have h : ContDiff ℝ 1 (fun t : ℝ => (fderiv ℝ Φ (σ, t)) (0, 1)) := by fun_prop
    exact h.continuous
  have h2cont : Continuous (fun t : ℝ => Work.RPV.ωC ((fderiv ℝ Φ (σ, t)) (1, 0))
      ((fderiv ℝ Φ (σ, t)) (0, 1))) := by
    rw [funext (fun t : ℝ => Work.RPB.B4.ωC_eq ((fderiv ℝ Φ (σ, t)) (1, 0))
      ((fderiv ℝ Φ (σ, t)) (0, 1))) ]
    exact ((Complex.continuous_re.comp hE1cd.continuous).mul
        (Complex.continuous_im.comp hE2cont)).sub
      ((Complex.continuous_im.comp hE1cd.continuous).mul
        (Complex.continuous_re.comp hE2cont))
  have hsplit : (∫ t in (0 : ℝ)..(2 * Real.pi),
        (Work.RPV.ωC (deriv (fun y => (fderiv ℝ Φ (σ, y)) (1, 0)) t) (Φ (σ, t))
          + Work.RPV.ωC ((fderiv ℝ Φ (σ, t)) (1, 0))
              ((fderiv ℝ Φ (σ, t)) (0, 1))))
      = (∫ t in (0 : ℝ)..(2 * Real.pi),
            Work.RPV.ωC (deriv (fun y => (fderiv ℝ Φ (σ, y)) (1, 0)) t) (Φ (σ, t)))
        + ∫ t in (0 : ℝ)..(2 * Real.pi), Work.RPV.ωC ((fderiv ℝ Φ (σ, t)) (1, 0))
            ((fderiv ℝ Φ (σ, t)) (0, 1)) :=
    intervalIntegral.integral_add (h1cont.intervalIntegrable _ _) (h2cont.intervalIntegrable _ _)
  have hneg : (∫ t in (0 : ℝ)..(2 * Real.pi),
        Work.RPV.ωC (deriv (fun y => (fderiv ℝ Φ (σ, y)) (1, 0)) t) (Φ (σ, t)))
      = -(∫ t in (0 : ℝ)..(2 * Real.pi),
            Work.RPV.ωC (Φ (σ, t)) (deriv (fun y => (fderiv ℝ Φ (σ, y)) (1, 0)) t)) := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    exact hskew _ _
  have hAB : (∫ t in (0 : ℝ)..(2 * Real.pi),
        Work.RPV.ωC (deriv (fun y => (fderiv ℝ Φ (σ, y)) (1, 0)) t) (Φ (σ, t)))
      + (∫ t in (0 : ℝ)..(2 * Real.pi), Work.RPV.ωC ((fderiv ℝ Φ (σ, t)) (1, 0))
            ((fderiv ℝ Φ (σ, t)) (0, 1))) = 0 := by
    rw [← hsplit]
    exact hcz
  linarith [hneg, hAB]

/-- The theorem for an uncurried `C²` family `Φ : ℝ × ℝ → ℂ`. -/
private lemma deriv_signedArea_uncurried (Φ : ℝ × ℝ → ℂ) (hΦ : ContDiff ℝ 2 Φ)
    (hper : ∀ s t, Φ (s, t + 2 * Real.pi) = Φ (s, t)) (σ : ℝ) :
    deriv (fun s => (1 / 2) * ∫ t in (0 : ℝ)..(2 * Real.pi),
        Work.RPV.ωC (Φ (s, t)) (deriv (fun u => Φ (s, u)) t)) σ
      = ∫ t in (0 : ℝ)..(2 * Real.pi),
          Work.RPV.ωC ((fderiv ℝ Φ (σ, t)) (1, 0)) ((fderiv ℝ Φ (σ, t)) (0, 1)) := by
  have hpt : ∀ t : ℝ,
      deriv (fun s => Work.RPV.ωC (Φ (s, t)) (deriv (fun u => Φ (s, u)) t)) σ =
        Work.RPV.ωC ((fderiv ℝ Φ (σ, t)) (1, 0)) ((fderiv ℝ Φ (σ, t)) (0, 1)) +
          Work.RPV.ωC (Φ (σ, t)) (deriv (fun y => (fderiv ℝ Φ (σ, y)) (1, 0)) t) :=
    fun t => deriv_integrand Φ hΦ σ t
  -- the joint integrand is `C¹`
  have hcd : ContDiff ℝ 1
      (fun z : ℝ × ℝ => Work.RPV.ωC (Φ z) (deriv (fun u => Φ (z.1, u)) z.2)) := by
    have heq : (fun z : ℝ × ℝ => Work.RPV.ωC (Φ z) (deriv (fun u => Φ (z.1, u)) z.2))
        = (fun z : ℝ × ℝ => Work.RPV.ωC (Φ z) (fderiv ℝ Φ z (0, 1))) := by
      funext z
      rw [deriv_curry_snd Φ hΦ z.1 z.2]
    rw [heq]
    exact contDiff_omegaC_fderiv_snd hΦ
  -- differentiate under the integral sign
  have hFD := Work.RPA3.hasFDerivAt_param_intervalIntegral (X := ℝ) (F := ℝ)
    (g := fun s t => Work.RPV.ωC (Φ (s, t)) (deriv (fun u => Φ (s, u)) t)) hcd
    0 (2 * Real.pi) σ
  have hCLMcont : Continuous (fun u : ℝ => (fderiv ℝ (fun z : ℝ × ℝ =>
      Work.RPV.ωC (Φ z) (deriv (fun u => Φ (z.1, u)) z.2)) (σ, u)).comp
        (ContinuousLinearMap.inl ℝ ℝ ℝ)) := by
    have h1 : Continuous (fun u : ℝ => fderiv ℝ (fun z : ℝ × ℝ =>
        Work.RPV.ωC (Φ z) (deriv (fun u => Φ (z.1, u)) z.2)) (σ, u)) :=
      (hcd.continuous_fderiv (by norm_num)).comp (continuous_const.prodMk continuous_id)
    have h2 : Continuous fun A : (ℝ × ℝ) →L[ℝ] ℝ => A.comp (ContinuousLinearMap.inl ℝ ℝ ℝ) := by
      have heq : (fun A : (ℝ × ℝ) →L[ℝ] ℝ => A.comp (ContinuousLinearMap.inl ℝ ℝ ℝ))
          = (ContinuousLinearMap.precomp ℝ (ContinuousLinearMap.inl ℝ ℝ ℝ) :
              ((ℝ × ℝ) →L[ℝ] ℝ) → (ℝ →L[ℝ] ℝ)) :=
        funext (fun A => (ContinuousLinearMap.precomp_apply ℝ
          (ContinuousLinearMap.inl ℝ ℝ ℝ) A).symm)
      rw [heq]
      exact (ContinuousLinearMap.precomp ℝ (ContinuousLinearMap.inl ℝ ℝ ℝ)).continuous
    exact h2.comp h1
  have hD : HasDerivAt (fun s : ℝ => ∫ t in (0 : ℝ)..(2 * Real.pi),
        Work.RPV.ωC (Φ (s, t)) (deriv (fun u => Φ (s, u)) t))
      (∫ t in (0 : ℝ)..(2 * Real.pi),
          deriv (fun s => Work.RPV.ωC (Φ (s, t)) (deriv (fun u => Φ (s, u)) t)) σ) σ := by
    refine hFD.hasDerivAt.congr_deriv ?_
    rw [ContinuousLinearMap.intervalIntegral_apply
      (hCLMcont.intervalIntegrable 0 (2 * Real.pi)) 1]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
    exact (Work.RPA3.deriv_prodMk_left
      (((hcd.differentiable (by norm_num)).differentiableAt).hasFDerivAt)).symm
  -- continuity of the two pieces of the split integrand
  have hE1 : Continuous (fun t : ℝ => (fderiv ℝ Φ (σ, t)) (1, 0)) := by
    have h : ContDiff ℝ 1 (fun t : ℝ => (fderiv ℝ Φ (σ, t)) (1, 0)) := by fun_prop
    exact h.continuous
  have hE2 : Continuous (fun t : ℝ => (fderiv ℝ Φ (σ, t)) (0, 1)) := by
    have h : ContDiff ℝ 1 (fun t : ℝ => (fderiv ℝ Φ (σ, t)) (0, 1)) := by fun_prop
    exact h.continuous
  have hM : Continuous (fun t : ℝ => deriv (fun y => (fderiv ℝ Φ (σ, y)) (1, 0)) t) := by
    have h : ContDiff ℝ 1 (fun y : ℝ => (fderiv ℝ Φ (σ, y)) (1, 0)) := by fun_prop
    exact h.continuous_deriv le_rfl
  have hΦlin : Continuous (fun t : ℝ => Φ (σ, t)) := by
    have h : ContDiff ℝ 2 (fun t : ℝ => Φ (σ, t)) := by fun_prop
    exact h.continuous
  have hAcont : Continuous (fun t : ℝ => Work.RPV.ωC ((fderiv ℝ Φ (σ, t)) (1, 0))
      ((fderiv ℝ Φ (σ, t)) (0, 1))) := by
    rw [funext (fun t : ℝ => Work.RPB.B4.ωC_eq ((fderiv ℝ Φ (σ, t)) (1, 0))
      ((fderiv ℝ Φ (σ, t)) (0, 1))) ]
    exact ((Complex.continuous_re.comp hE1).mul (Complex.continuous_im.comp hE2)).sub
      ((Complex.continuous_im.comp hE1).mul (Complex.continuous_re.comp hE2))
  have hBcont : Continuous (fun t : ℝ => Work.RPV.ωC (Φ (σ, t))
      (deriv (fun y => (fderiv ℝ Φ (σ, y)) (1, 0)) t)) := by
    rw [funext (fun t : ℝ => Work.RPB.B4.ωC_eq (Φ (σ, t))
      (deriv (fun y => (fderiv ℝ Φ (σ, y)) (1, 0)) t)) ]
    exact ((Complex.continuous_re.comp hΦlin).mul (Complex.continuous_im.comp hM)).sub
      ((Complex.continuous_im.comp hΦlin).mul (Complex.continuous_re.comp hM))
  have hstep1 : (∫ t in (0 : ℝ)..(2 * Real.pi),
        deriv (fun s => Work.RPV.ωC (Φ (s, t)) (deriv (fun u => Φ (s, u)) t)) σ)
      = ∫ t in (0 : ℝ)..(2 * Real.pi),
          (Work.RPV.ωC ((fderiv ℝ Φ (σ, t)) (1, 0)) ((fderiv ℝ Φ (σ, t)) (0, 1)) +
            Work.RPV.ωC (Φ (σ, t)) (deriv (fun y => (fderiv ℝ Φ (σ, y)) (1, 0)) t)) :=
    intervalIntegral.integral_congr fun t _ => hpt t
  have hstep2 : (∫ t in (0 : ℝ)..(2 * Real.pi),
          (Work.RPV.ωC ((fderiv ℝ Φ (σ, t)) (1, 0)) ((fderiv ℝ Φ (σ, t)) (0, 1)) +
            Work.RPV.ωC (Φ (σ, t)) (deriv (fun y => (fderiv ℝ Φ (σ, y)) (1, 0)) t)))
      = (∫ t in (0 : ℝ)..(2 * Real.pi), Work.RPV.ωC ((fderiv ℝ Φ (σ, t)) (1, 0))
            ((fderiv ℝ Φ (σ, t)) (0, 1)))
        + ∫ t in (0 : ℝ)..(2 * Real.pi), Work.RPV.ωC (Φ (σ, t))
            (deriv (fun y => (fderiv ℝ Φ (σ, y)) (1, 0)) t) :=
    intervalIntegral.integral_add (hAcont.intervalIntegrable _ _) (hBcont.intervalIntegrable _ _)
  have hcross := integral_omegaC_mixed Φ hΦ hper σ
  have hmul : deriv (fun s : ℝ => (1 / 2) * ∫ t in (0 : ℝ)..(2 * Real.pi),
        Work.RPV.ωC (Φ (s, t)) (deriv (fun u => Φ (s, u)) t)) σ
      = (1 / 2) * (∫ t in (0 : ℝ)..(2 * Real.pi),
          deriv (fun s => Work.RPV.ωC (Φ (s, t)) (deriv (fun u => Φ (s, u)) t)) σ) :=
    (hD.const_mul (1 / 2 : ℝ)).deriv
  rw [hmul, hstep1, hstep2, hcross]
  ring

theorem deriv_signedArea_general (V : ℝ → ℝ → ℂ) (σ : ℝ) (hper : ∀ σ t, V σ (t + 2 * Real.pi) = V σ t) (hV : ContDiff ℝ 2 (fun z : ℝ × ℝ => V z.1 z.2)) : deriv (fun s => Work.RPB.signedArea (fun t => V s t)) σ = ∫ t in (0 : ℝ)..(2 * Real.pi), Work.RPV.ωC (deriv (fun s => V s t) σ) (deriv (fun s => V σ s) t) := by
  set Φ : ℝ × ℝ → ℂ := fun z => V z.1 z.2 with hΦdef
  have hΦ : ContDiff ℝ 2 Φ := hV
  have hper' : ∀ s t, Φ (s, t + 2 * Real.pi) = Φ (s, t) := fun s t => hper s t
  have hd1 : ∀ t : ℝ, deriv (fun s => V s t) σ = (fderiv ℝ Φ (σ, t)) (1, 0) :=
    fun t => deriv_curry_fst Φ hΦ σ t
  have hd2 : ∀ t : ℝ, deriv (fun s => V σ s) t = (fderiv ℝ Φ (σ, t)) (0, 1) :=
    fun t => deriv_curry_snd Φ hΦ σ t
  have hL : (fun s => Work.RPB.signedArea (fun t => V s t))
      = (fun s => (1 / 2) * ∫ t in (0 : ℝ)..(2 * Real.pi),
          Work.RPV.ωC (Φ (s, t)) (deriv (fun u => Φ (s, u)) t)) := by
    funext s
    simp only [Work.RPB.signedArea]
    congr 1
  simp only [hd1, hd2]
  rw [hL, deriv_signedArea_uncurried Φ hΦ hper' σ]

end Work.RPB.B5
