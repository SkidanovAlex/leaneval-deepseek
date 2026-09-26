import Mathlib
import Submission.Work.Drive.Mono.OneEvBadAux
import Submission.Work.Drive.Mono.Band.critBranch_euclid

/-!
# `exists_critChart`

A nondegenerate critical point `p₀` of the sweep height `sH ψ a₀ b₀ τ₀` continues as a `C¹` branch
`P` of the tilt: on a neighbourhood `V` of `τ₀` the function `τ ↦ P τ` is a critical point of the
sweep height in direction `τ`, `P` is the unique critical point in a ball about `p₀`, and the level
`τ ↦ sH ψ a₀ b₀ τ (P τ)` has derivative `⟪∂_τ dirOf τ₀, par ψ p₀⟫` at `τ₀` (the envelope formula).

The Euclidean branch is `Work.Drive.Mono.Band.critBranch_euclid`, applied to the direction
`dirOf τ₀ a₀ b₀`; the tilt enters only through the smooth curve `τ ↦ dirOf τ a₀ b₀`.
-/

open LeanEval.KnotTheory.PardonDistortion Set
open scoped RealInnerProductSpace ENNReal

set_option maxHeartbeats 3000000

namespace Work.Drive.Mono

noncomputable section

/-- **The partial derivatives of a function of two variables.**  For `H : ℝ × E → F` the derivative
of `H` at `(a,b)` applied to `(1,w)` is the sum of the derivative along the first coordinate and the
derivative in the second coordinate applied to `w`. -/
theorem fderiv_prod_apply_one_add {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {H : ℝ × E → F} {a : ℝ} {b : E} (w : E)
    (h : DifferentiableAt ℝ H (a, b)) :
    fderiv ℝ H (a, b) (1, w)
      = deriv (fun t : ℝ => H (t, b)) a + (fderiv ℝ (fun x : E => H (a, x)) b) w := by
  have hinl : HasFDerivAt (fun t : ℝ => H (t, b))
      ((fderiv ℝ H (a, b)) ∘L ContinuousLinearMap.inl ℝ ℝ E) a :=
    HasFDerivAt.comp a h.hasFDerivAt (hasFDerivAt_prodMk_left a b)
  have hinr : HasFDerivAt (fun x : E => H (a, x))
      ((fderiv ℝ H (a, b)) ∘L ContinuousLinearMap.inr ℝ ℝ E) b :=
    HasFDerivAt.comp b h.hasFDerivAt (hasFDerivAt_prodMk_right a b)
  have h1 : (fderiv ℝ H (a, b)) (1, 0) = deriv (fun t : ℝ => H (t, b)) a := by
    have h2 := congrArg (fun T : ℝ →L[ℝ] F => T 1) hinl.fderiv
    rw [fderiv_apply_one_eq_deriv] at h2
    rw [h2]
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
  have h2 : (fderiv ℝ H (a, b)) (0, w) = (fderiv ℝ (fun x : E => H (a, x)) b) w := by
    rw [hinr.fderiv]
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
  have key : (fderiv ℝ H (a, b)) (1, w)
      = (fderiv ℝ H (a, b)) (1, 0) + (fderiv ℝ H (a, b)) (0, w) := by
    rw [← map_add]
    congr 1
    ext <;> simp
  rw [key, h1, h2]

theorem exists_critChart {a₀ b₀ : LeanEval.KnotTheory.PardonDistortion.R3} (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1)
    (hab : inner ℝ a₀ b₀ = 0) (ψ : Submission.Diffeo) {τ₀ : ℝ} {p₀ : ℝ × ℝ}
    (hcrit : fderiv ℝ (fun x : ℝ × ℝ => Work.Drive.Mono.sH ψ a₀ b₀ τ₀ x) p₀ = 0)
    (hinj : Function.Injective
      (fderiv ℝ (fderiv ℝ (fun x : ℝ × ℝ => Work.Drive.Mono.sH ψ a₀ b₀ τ₀ x)) p₀)) :
    Nonempty (Work.Drive.Mono.CritChart ψ a₀ b₀ τ₀ p₀) := by
  classical
  -- the branch of critical points of the Euclidean height in direction `n`
  obtain ⟨U, y, r, hUopen, hUmem, hr, hy0, hycd, hycrit, hyuniq⟩ :=
    Band.critBranch_euclid ψ (Band.dirOf τ₀ a₀ b₀) (x := p₀) hcrit hinj
  -- the tilt curve
  have hdir_cd : ContDiff ℝ 2 (fun τ : ℝ => Band.dirOf τ a₀ b₀) := contDiff_dirOf ha hb hab
  have hdir_cont : Continuous (fun τ : ℝ => Band.dirOf τ a₀ b₀) := hdir_cd.continuous
  have hdir_deriv : HasDerivAt (fun τ : ℝ => Band.dirOf τ a₀ b₀)
      (deriv (fun τ : ℝ => Band.dirOf τ a₀ b₀) τ₀) τ₀ :=
    ((hdir_cd.differentiable (by norm_num)).differentiableAt).hasDerivAt
  -- the chart
  let P : ℝ → ℝ × ℝ := fun τ => y (Band.dirOf τ a₀ b₀)
  let V : Set ℝ := {τ | Band.dirOf τ a₀ b₀ ∈ U}
  have hVopen : IsOpen V := hUopen.preimage hdir_cont
  have hVmem : τ₀ ∈ V := by
    change Band.dirOf τ₀ a₀ b₀ ∈ U
    exact hUmem
  have hPcd : ContDiffOn ℝ 1 P V := by
    have h1 : ContDiffOn ℝ 1 y U := hycd
    have h2 : ContDiffOn ℝ 1 (fun τ : ℝ => Band.dirOf τ a₀ b₀) V :=
      (hdir_cd.of_le (by norm_num)).contDiffOn
    exact h1.comp h2 (fun τ hτ => hτ)
  have hPmem : P τ₀ = p₀ := hy0
  have hcritV : ∀ τ ∈ V, fderiv ℝ (fun x : ℝ × ℝ => sH ψ a₀ b₀ τ x) (P τ) = 0 :=
    fun τ hτ => hycrit (Band.dirOf τ a₀ b₀) hτ
  have huniqV : ∀ τ ∈ V, ∀ q : ℝ × ℝ, ‖q - p₀‖ < r →
      fderiv ℝ (fun x : ℝ × ℝ => sH ψ a₀ b₀ τ x) q = 0 → q = P τ :=
    fun τ hτ q hq hzero => hyuniq (Band.dirOf τ a₀ b₀) hτ q hq hzero
  -- the envelope formula for the level
  have hLτ : deriv (fun τ : ℝ => sH ψ a₀ b₀ τ (P τ)) τ₀
      = inner ℝ (deriv (fun s : ℝ => Band.dirOf s a₀ b₀) τ₀) (Work.BoxShrink.Pinch.par ψ p₀) := by
    have hPat : ContDiffAt ℝ 1 P τ₀ := hPcd.contDiffAt (hVopen.mem_nhds hVmem)
    have hPd : HasFDerivAt P (fderiv ℝ P τ₀) τ₀ := (hPat.differentiableAt one_ne_zero).hasFDerivAt
    have hHc : ContDiff ℝ 2 (Function.uncurry (sH ψ a₀ b₀)) := contDiff_sH_uncurry ha hb hab ψ
    have hpair : HasFDerivAt (fun τ : ℝ => (τ, P τ))
        ((ContinuousLinearMap.id ℝ ℝ).prod (fderiv ℝ P τ₀)) τ₀ :=
      (hasFDerivAt_id τ₀).prodMk hPd
    have hHdQ : HasFDerivAt (Function.uncurry (sH ψ a₀ b₀))
        (fderiv ℝ (Function.uncurry (sH ψ a₀ b₀)) (τ₀, P τ₀)) (τ₀, P τ₀) :=
      ((hHc.differentiable (by norm_num)) (τ₀, P τ₀)).hasFDerivAt
    have hchain : HasFDerivAt (fun τ : ℝ => Function.uncurry (sH ψ a₀ b₀) (τ, P τ))
        ((fderiv ℝ (Function.uncurry (sH ψ a₀ b₀)) (τ₀, P τ₀)) ∘L
          ((ContinuousLinearMap.id ℝ ℝ).prod (fderiv ℝ P τ₀))) τ₀ := by
      simpa [Function.comp_def] using hHdQ.comp τ₀ hpair
    have hsplit : fderiv ℝ (Function.uncurry (sH ψ a₀ b₀)) (τ₀, P τ₀)
        = fderiv ℝ (Function.uncurry (sH ψ a₀ b₀)) (τ₀, p₀) := by rw [hPmem]
    have hL1 : deriv (fun τ : ℝ => Function.uncurry (sH ψ a₀ b₀) (τ, P τ)) τ₀
        = (fderiv ℝ (Function.uncurry (sH ψ a₀ b₀)) (τ₀, p₀)) (1, fderiv ℝ P τ₀ 1) := by
      calc deriv (fun τ : ℝ => Function.uncurry (sH ψ a₀ b₀) (τ, P τ)) τ₀
          = (fderiv ℝ (fun τ : ℝ => Function.uncurry (sH ψ a₀ b₀) (τ, P τ)) τ₀) 1 :=
            fderiv_apply_one_eq_deriv.symm
        _ = ((fderiv ℝ (Function.uncurry (sH ψ a₀ b₀)) (τ₀, P τ₀)) ∘L
              ((ContinuousLinearMap.id ℝ ℝ).prod (fderiv ℝ P τ₀))) 1 := by rw [hchain.fderiv]
        _ = (fderiv ℝ (Function.uncurry (sH ψ a₀ b₀)) (τ₀, p₀)) (1, fderiv ℝ P τ₀ 1) := by
              rw [hsplit]
              simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply]
    have hHd : DifferentiableAt ℝ (Function.uncurry (sH ψ a₀ b₀)) (τ₀, p₀) :=
      (hHc.differentiable (by norm_num)) (τ₀, p₀)
    have hdec := fderiv_prod_apply_one_add (H := Function.uncurry (sH ψ a₀ b₀)) (a := τ₀)
      (b := p₀) (fderiv ℝ P τ₀ 1) hHd
    have hzero_x : fderiv ℝ (fun x : ℝ × ℝ => Function.uncurry (sH ψ a₀ b₀) (τ₀, x)) p₀ = 0 :=
      hcrit
    have hzero_apply : (fderiv ℝ (fun x : ℝ × ℝ => Function.uncurry (sH ψ a₀ b₀) (τ₀, x)) p₀)
        (fderiv ℝ P τ₀ 1) = 0 := by
      rw [hzero_x]
      simp
    have hderiv_τ : deriv (fun t : ℝ => Function.uncurry (sH ψ a₀ b₀) (t, p₀)) τ₀
        = inner ℝ (deriv (fun s : ℝ => Band.dirOf s a₀ b₀) τ₀)
            (Work.BoxShrink.Pinch.par ψ p₀) := by
      have hfun : (fun t : ℝ => Function.uncurry (sH ψ a₀ b₀) (t, p₀))
          = fun t : ℝ => inner ℝ (Band.dirOf t a₀ b₀) (Work.BoxShrink.Pinch.par ψ p₀) := rfl
      rw [hfun]
      have hinner := HasDerivAt.inner ℝ hdir_deriv
        (hasDerivAt_const τ₀ (Work.BoxShrink.Pinch.par ψ p₀))
      rw [hinner.deriv]
      simp [inner_zero_right]
    have hcongr : (fun τ : ℝ => sH ψ a₀ b₀ τ (P τ))
        = (fun τ : ℝ => Function.uncurry (sH ψ a₀ b₀) (τ, P τ)) := rfl
    rw [hcongr, hL1, hdec, hzero_apply, add_zero, hderiv_τ]
  have hUmem2 : p₀ ∈ Metric.ball p₀ r := Metric.mem_ball_self hr
  have huniqF : ∀ τ ∈ V, ∀ q ∈ Metric.ball p₀ r,
      fderiv ℝ (fun x : ℝ × ℝ => sH ψ a₀ b₀ τ x) q = 0 → q = P τ := by
    intro τ hτ q hq hzero
    rw [Metric.mem_ball, dist_eq_norm] at hq
    exact huniqV τ hτ q hq hzero
  exact ⟨{ V := V
           hVopen := hVopen
           hVmem := hVmem
           P := P
           hPcd := hPcd
           hPmem := hPmem
           hcrit := hcritV
           hLτ := hLτ
           U := Metric.ball p₀ r
           hUopen := Metric.isOpen_ball
           hUmem := hUmem2
           huniq := huniqF }⟩

end

end Work.Drive.Mono
