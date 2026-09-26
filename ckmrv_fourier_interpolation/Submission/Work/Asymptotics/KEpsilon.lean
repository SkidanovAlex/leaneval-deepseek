/-
# The cusp-`0` neighbourhood `E = S(𝓕)` of the CKMRV fundamental domain

The target lemma `Work.Asymptotics.kernelTransform_seminorm_funnel_khat` bounds the `r`-seminorms
of the contour transform `Work.Kernels.kernelTransform (Khat ℓ d) τ ·` on the *funnel*

  `𝓕 = {τ ∈ 𝒟 : 2 ≤ Im τ}`

(the cusp `∞` of `𝒟`).  By the `S`-transport `K̂ = -K|^τ_{d/2}S` the transform of `K̂` at `τ` is,
up to the moderate factor `τ^{-d/2}`, the transform of `K` at `S • τ`; hence the target is
*equivalent* to the seminorm bound for `K` on the region

  `E := {w ∈ 𝒟 : 2 ≤ Im (S • w)} = S(𝓕)`,

the cusp-`0` neighbourhood of `𝒟` (`E = {w ∈ 𝒟 : ‖w - i/4‖ ≤ 1/4}`, the closed disk of radius
`1/4` about `i/4` intersected with `𝒟`).

This file records the region `E`, the basic geometry of the `S`-transport, and the two analytic
inputs on `E` (flatness at the cusp `0` and the cusp-`i∞` expansion of `z ↦ K(τ,z)`) in the exact
form in which the layer machinery of `Submission/Work/Asymptotics/` consumes them.

## Main definitions

* `Work.Asymptotics.KEpsilon` — the cusp-`0` neighbourhood `E = S(𝓕)`.
* `Work.Asymptotics.TailBoundE` — the two-regime control of `Kaxis (Kfun ℓ d) w t - Aexp G w t`
  for `w ∈ E`, i.e. `Work.Asymptotics.TailBound` with `𝒟` replaced by `E`.
-/
import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.Asymptotics.GcuspDefs

noncomputable section

open UpperHalfPlane ModularGroup Matrix
open scoped MatrixGroups UpperHalfPlane

namespace Work.Asymptotics

/-! ## The region `E` -/

/-- The cusp-`0` neighbourhood `E = S(𝓕)` of `𝒟`: the points `w ∈ 𝒟` whose `S`-image has
imaginary part `≥ 2`.  Equivalently `E = {w ∈ 𝒟 : ‖w - i/4‖ ≤ 1/4}`. -/
def KEpsilon : Set ℍ := {w : ℍ | w ∈ DomainD ∧ 2 ≤ (ModularGroup.S • w).im}

lemma mem_KEpsilon {w : ℍ} :
    w ∈ KEpsilon ↔ w ∈ DomainD ∧ 2 ≤ (ModularGroup.S • w).im := Iff.rfl

lemma KEpsilon_subset_DomainD : KEpsilon ⊆ DomainD := fun _ h => h.1

/-- `S = z ↦ -1/z` maps `𝒟` into itself. -/
lemma S_smul_mem_DomainD {u : ℍ} (hu : u ∈ DomainD) : ModularGroup.S • u ∈ DomainD := by
  rw [mem_DomainD] at hu ⊢
  obtain ⟨hx1, hx2, h3, h4⟩ := hu
  have hne : (u : ℂ) ≠ 0 := u.ne_zero
  have hNpos : 0 < Complex.normSq (u : ℂ) := Complex.normSq_pos.mpr hne
  have hcoe : ((ModularGroup.S • u : ℍ) : ℂ) = -((u : ℂ))⁻¹ := by
    rw [modular_S_smul, UpperHalfPlane.coe_mk, inv_neg]
  have hre : (ModularGroup.S • u).re = -u.re / Complex.normSq (u : ℂ) := by
    rw [← UpperHalfPlane.coe_re, hcoe, Complex.neg_re, Complex.inv_re, UpperHalfPlane.coe_re]
    rw [← neg_div]
  have hsub : -(u : ℂ)⁻¹ - (1 / 2 : ℂ) = -((u : ℂ) + 2) / (2 * (u : ℂ)) := by
    field_simp; ring
  have hadd : -(u : ℂ)⁻¹ + (1 / 2 : ℂ) = ((u : ℂ) - 2) / (2 * (u : ℂ)) := by
    field_simp; ring
  have harcR : u.re - u.re ^ 2 < u.im ^ 2 := by
    have h : (1 / 4 : ℝ) < Complex.normSq ((u : ℂ) - (1 / 2 : ℂ)) := by
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg ((u : ℂ) - (1 / 2 : ℂ))]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, UpperHalfPlane.coe_re,
      UpperHalfPlane.coe_im] at h
    norm_num at h
    nlinarith
  have harcL : -u.re - u.re ^ 2 < u.im ^ 2 := by
    have h : (1 / 4 : ℝ) < Complex.normSq ((u : ℂ) + (1 / 2 : ℂ)) := by
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg ((u : ℂ) + (1 / 2 : ℂ))]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, UpperHalfPlane.coe_re,
      UpperHalfPlane.coe_im] at h
    norm_num at h
    nlinarith
  have hNsq : Complex.normSq (u : ℂ) = u.re * u.re + u.im * u.im := by
    rw [Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  have habs : |u.re| < Complex.normSq (u : ℂ) := by
    rw [hNsq]
    rcases le_or_gt 0 u.re with h | h
    · rw [abs_of_nonneg h]; nlinarith
    · rw [abs_of_neg h]; nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hre, neg_div, neg_lt_neg_iff, div_lt_one hNpos]
    exact (abs_lt.mp habs).2
  · rw [hre, neg_div, neg_lt, lt_div_iff₀ hNpos]
    linarith [(abs_lt.mp habs).1]
  · rw [hcoe, hsub, norm_div, norm_neg, norm_mul, Complex.norm_ofNat]
    rw [lt_div_iff₀ (by positivity)]
    have hkey : ‖(u : ℂ)‖ < ‖(u : ℂ) + 2‖ := by
      have hsq : ‖(u : ℂ)‖ ^ 2 < ‖(u : ℂ) + 2‖ ^ 2 := by
        rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
        rw [Complex.add_re, Complex.add_im, show ((2 : ℂ)).re = 2 from by norm_num,
          show ((2 : ℂ)).im = 0 from by norm_num, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
        nlinarith [hx1]
      nlinarith [hsq, norm_nonneg (u : ℂ), norm_nonneg ((u : ℂ) + 2)]
    linarith [hkey]
  · rw [hcoe, hadd, norm_div, norm_mul, Complex.norm_ofNat]
    rw [lt_div_iff₀ (by positivity)]
    have hkey : ‖(u : ℂ)‖ < ‖(u : ℂ) - 2‖ := by
      have hsq : ‖(u : ℂ)‖ ^ 2 < ‖(u : ℂ) - 2‖ ^ 2 := by
        rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
        rw [Complex.sub_re, Complex.sub_im, show ((2 : ℂ)).re = 2 from by norm_num,
          show ((2 : ℂ)).im = 0 from by norm_num, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
        nlinarith [hx2]
      nlinarith [hsq, norm_nonneg (u : ℂ), norm_nonneg ((u : ℂ) - 2)]
    linarith [hkey]

/-- `S` is an involution on `ℍ`. -/
lemma S_smul_S_smul (τ : ℍ) : ModularGroup.S • (ModularGroup.S • τ) = τ := by
  have h : (((ModularGroup.S • (ModularGroup.S • τ) : ℍ)) : ℂ) = (τ : ℂ) := by
    rw [modular_S_smul, modular_S_smul, UpperHalfPlane.coe_mk, UpperHalfPlane.coe_mk]
    field_simp
  exact UpperHalfPlane.ext h

/-- `S` maps the funnel `𝓕 = {τ ∈ 𝒟 : 2 ≤ Im τ}` into `E`. -/
lemma S_smul_mem_KEpsilon {τ : ℍ} (hτ : τ ∈ DomainD) (h2 : 2 ≤ τ.im) :
    ModularGroup.S • τ ∈ KEpsilon := by
  refine ⟨S_smul_mem_DomainD hτ, ?_⟩
  rw [S_smul_S_smul]
  exact h2

/-- `S` maps `E` into the funnel `𝓕`. -/
lemma S_smul_mem_funnel {w : ℍ} (hw : w ∈ KEpsilon) :
    ModularGroup.S • w ∈ DomainD ∧ 2 ≤ (ModularGroup.S • w).im :=
  ⟨S_smul_mem_DomainD hw.1, hw.2⟩

/-! ## The two analytic inputs on `E` -/

/-- **The flatness of `K` on `E`**: the cusp-`0` analogue of `Work.Asymptotics.Kaxis_local_flat`,
uniformly on the whole cusp-`0` neighbourhood up to powers of `scale w`. -/
def EFlat (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) : Prop :=
  ∀ N : ℝ, 0 ≤ N → ∃ c N' : ℝ, 0 ≤ c ∧
    ∀ (w : ℍ) (t : ℝ), w ∈ KEpsilon → 0 < t → t ≤ 1 →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t‖
        ≤ c * (Work.Kernels.scale w) ^ N' * t ^ N

/-- **Polynomial boundedness of `K` on `E` up to the cusp expansion threshold.**

For `w ∈ E` and `0 < t ≤ (scale w)^{N₀}` — i.e. below the height of the highest pole of
`z ↦ K(w,z)` — the kernel is bounded polynomially in `scale w` and `t`.  (Beyond the threshold
the kernel is described by the cusp expansion `Aexp`; see `Work.Asymptotics.Etail_Kfun`.  Note
that the bound cannot extend beyond the threshold in dimension `24`, where the expansion has a
non-vanishing `e^{2πt}` coefficient.) -/
def EPolyWin (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) : Prop :=
  ∃ N₀ C N M : ℝ, 0 ≤ N₀ ∧ 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
    ∀ (w : ℍ) (t : ℝ), w ∈ KEpsilon → 0 < t → t ≤ (Work.Kernels.scale w) ^ N₀ →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t‖
        ≤ C * (Work.Kernels.scale w) ^ N * (1 + t) ^ M

/-- **The cusp-`i∞` expansion of `z ↦ K(w,z)` on `E`, beyond the threshold.** -/
def ETail (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) : Prop :=
  ∃ N₀ C N M : ℝ, 0 ≤ N₀ ∧ 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
    ∀ (w : ℍ) (t : ℝ), w ∈ KEpsilon → (Work.Kernels.scale w) ^ N₀ ≤ t →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t
          - Aexp (Gcusp ℓ d) w t‖
        ≤ C * (Work.Kernels.scale w) ^ N * t ^ M * Real.exp (-(Real.pi * t))

/-- **The seminorm bound for `K` on the cusp-`0` neighbourhood `E = S(𝓕)`.**

By the `S`-transport `K̂ = -K|^τ_{d/2}S` (proved in
`Work.Asymptotics.kernelTransform_seminorm_funnel_khat_of_E`) this is *equivalent* to the target
`Work.Asymptotics.kernelTransform_seminorm_funnel_khat`.  It is proved from the three analytic
inputs `Work.Asymptotics.EFlat`, `Work.Asymptotics.EPolyWin`, `Work.Asymptotics.ETail` by splitting
the contour integral `∫_0^∞ K(w,it)e^{-πr²t}dt` at the threshold `(scale w)^{N₀}` of the cusp
expansion. -/
def SeminormK_E (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) : Prop :=
  ∀ k l : ℕ, ∃ α β γ δ : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ 0 ≤ δ ∧
    ∀ (w : ℍ) (r : ℝ), w ∈ KEpsilon →
      (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
        Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) w s) r‖
        ≤ α * (w.im) ^ (-β) + γ * (‖(w : ℂ)‖) ^ δ
/-- **The two regimes of `K` on `E` at a *common* threshold.**  Below the threshold
`(scale w)^{N₀}` — the height of the highest pole of `z ↦ K(w,z)` — the kernel is polynomially
bounded; above it, the cusp expansion `Work.Asymptotics.Aexp (Gcusp ℓ d)` describes it up to
`e^{-πt}`.  The shared threshold is what the four-piece splitting of the contour integral needs;
it is obtained from `Work.Asymptotics.EPolyWin` and `Work.Asymptotics.ETail` by
`Work.Asymptotics.ERegimes_of`. -/
def ERegimes (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) : Prop :=
  ∃ N₀ C N M : ℝ, 0 ≤ N₀ ∧ 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
    (∀ (w : ℍ) (t : ℝ), w ∈ KEpsilon → 0 < t → t ≤ (Work.Kernels.scale w) ^ N₀ →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t‖
        ≤ C * (Work.Kernels.scale w) ^ N * (1 + t) ^ M) ∧
    (∀ (w : ℍ) (t : ℝ), w ∈ KEpsilon → (Work.Kernels.scale w) ^ N₀ ≤ t →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t - Aexp (Gcusp ℓ d) w t‖
        ≤ C * (Work.Kernels.scale w) ^ N * t ^ M * Real.exp (-(Real.pi * t)))

end Work.Asymptotics
