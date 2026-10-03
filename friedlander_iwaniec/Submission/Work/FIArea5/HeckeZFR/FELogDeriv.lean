/-
# `Submission.Work.FIArea5.HeckeZFR.FELogDeriv`

The **log-derivative form of the functional equation**: if an entire `Lam` satisfies the reflection
`Lam s = W · conj (Lam (conj (1-s)))` with `W ≠ 0`, then

  `Λ'/Λ(s) = - conj (Λ'/Λ(conj(1-s)))`.

For `s = -1 + iγ` this gives `Λ'/Λ(-1+iγ) = - conj (Λ'/Λ(2+iγ))`, i.e. the bound at the base point
`s₁ = -1 + iγ` of the rebasing is equivalent to a bound at `2 + iγ`, **where everything is
absolutely convergent**.  The auxiliary `hasDerivAt_conj_conj` is the analytic form of
"`conj ∘ f ∘ conj` is holomorphic with the conjugated derivative".
-/
import Mathlib

set_option autoImplicit false

namespace Work.FIArea5.S16Hecke

open Complex Filter Asymptotics
open scoped Topology

noncomputable section

/-- `star` is `1`-Lipschitz, so it is `O(id)` at the origin. -/
lemma isBigO_star_id : (fun z : ℂ => star z) =O[𝓝 (0 : ℂ)] (fun z : ℂ => z) := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards with z
  simp

/-- `star ∘ g` is `O(g)`. -/
lemma isBigO_star_comp (g : ℂ → ℂ) :
    (fun z => star (g z)) =O[𝓝 (0 : ℂ)] g := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards with z
  simp

/-- **The conjugate–conjugate of a holomorphic function is holomorphic.**  If `f` has derivative
`c` at `star w`, then `t ↦ star (f (star t))` has derivative `star c` at `w`. -/
theorem hasDerivAt_conj_conj (f : ℂ → ℂ) {c w : ℂ} (h : HasDerivAt f c (star w)) :
    HasDerivAt (fun t => star (f (star t))) (star c) w := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero] at h ⊢
  have hconj : Tendsto (star : ℂ → ℂ) (𝓝 (0 : ℂ)) (𝓝 0) := by
    have h0 := Complex.continuous_conj.tendsto (0 : ℂ)
    simpa using h0
  have h1 := h.comp_tendsto hconj
  have h2 : (fun x : ℂ => f (star (w + x)) - f (star w) - star x • c)
      =o[𝓝 (0 : ℂ)] (fun x : ℂ => star x) := by
    refine h1.congr' ?_ (Filter.EventuallyEq.rfl)
    filter_upwards with x
    simp only [Function.comp_apply]
    rw [← star_add]
  have h3 : (fun x : ℂ => f (star (w + x)) - f (star w) - star x • c)
      =o[𝓝 (0 : ℂ)] (fun x : ℂ => x) := h2.trans_isBigO isBigO_star_id
  have h4 : (fun x : ℂ => star (f (star (w + x)) - f (star w) - star x • c))
      =o[𝓝 (0 : ℂ)] (fun x : ℂ => x) :=
    (isBigO_star_comp _).trans_isLittleO h3
  refine h4.congr' ?_ (Filter.EventuallyEq.rfl)
  filter_upwards with x
  simp only [smul_eq_mul, star_sub, star_mul, star_star]
  ring

/-- **Log-derivative form of the functional equation.** -/
theorem logDeriv_FE {Lam : ℂ → ℂ} {W : ℂ} (hW : W ≠ 0)
    (hFE : ∀ s : ℂ, Lam s = W * star (Lam (star (1 - s))))
    (hDiff : Differentiable ℂ Lam) {s : ℂ} (hs : Lam s ≠ 0)
    (hs' : Lam (star (1 - s)) ≠ 0) :
    deriv Lam s / Lam s = - star (deriv Lam (star (1 - s)) / Lam (star (1 - s))) := by
  set H : ℂ → ℂ := fun t => star (Lam (star t)) with hHdef
  have hH : ∀ t : ℂ, HasDerivAt H (star (deriv Lam (star t))) t := by
    intro t
    have hd : HasDerivAt Lam (deriv Lam (star t)) (star t) :=
      (hDiff.differentiableAt).hasDerivAt
    simpa [H] using hasDerivAt_conj_conj Lam hd
  set G : ℂ → ℂ := fun u => H (1 - u) with hGdef
  have hc : HasDerivAt (fun u : ℂ => 1 - u) (-1) s := by
    have h1 : HasDerivAt (fun _ : ℂ => (1 : ℂ)) 0 s := hasDerivAt_const s 1
    have h2 : HasDerivAt (fun u : ℂ => u) 1 s := hasDerivAt_id s
    have h3 : HasDerivAt (fun u : ℂ => (1 : ℂ) - u) (0 - 1) s := h1.sub h2
    simpa using h3
  have hcomp : HasDerivAt G (- star (deriv Lam (star (1 - s)))) s := by
    have h0 : HasDerivAt (fun u : ℂ => H (1 - u))
        (star (deriv Lam (star (1 - s))) * (-1)) s := by
      have h1 := (hH (1 - s)).comp s hc
      simpa [Function.comp_def] using h1
    have h1 : (star (deriv Lam (star (1 - s))) * (-1))
        = - star (deriv Lam (star (1 - s))) := by ring
    rw [h1] at h0
    simpa [G] using h0
  have hGs : G s ≠ 0 := by
    have h1 : G s = star (Lam (star (1 - s))) := by simp [G, H]
    exact fun h => hs' (by rw [h1] at h; simpa using h)
  have hLam : Lam = fun u : ℂ => W * G u := by
    funext u
    rw [hFE u]
  have hWL : HasDerivAt (fun u : ℂ => W * G u) (- (W * star (deriv Lam (star (1 - s))))) s := by
    have h0 := hcomp.const_mul W
    simpa [mul_neg, mul_one, neg_mul] using h0
  have hderiv : deriv Lam s = - W * star (deriv Lam (star (1 - s))) := by
    have h1 : deriv Lam s = deriv (fun u : ℂ => W * G u) s := by rw [hLam]
    rw [h1, hWL.deriv]
    ring
  have hLz : star (Lam (star (1 - s))) ≠ 0 := by
    have h1 : G s = star (Lam (star (1 - s))) := by simp [G, H]
    exact fun h => hGs (by rw [h1]; exact h)
  have hstar : star (deriv Lam (star (1 - s)) / Lam (star (1 - s)))
      = star (deriv Lam (star (1 - s))) / star (Lam (star (1 - s))) :=
    map_div₀ (starRingEnd ℂ) _ _
  rw [hderiv, hFE s, hstar]
  field_simp
  try ring

/-- The functional-equation reflection of the log-derivative at the **base point of the
rebasing**: `Λ'/Λ(-1+iγ) = - conj (Λ'/Λ(2+iγ))`.  At `2 + iγ` everything is absolutely
convergent, so this reduces the bound at the base point to an elementary estimate. -/
theorem logDeriv_FE_at_neg_one {Lam : ℂ → ℂ} {W : ℂ} (hW : W ≠ 0)
    (hFE : ∀ s : ℂ, Lam s = W * star (Lam (star (1 - s))))
    (hDiff : Differentiable ℂ Lam) {γ : ℝ}
    (hs : Lam ((-1 : ℂ) + I * (γ : ℂ)) ≠ 0)
    (hs' : Lam ((2 : ℂ) + I * (γ : ℂ)) ≠ 0) :
    deriv Lam ((-1 : ℂ) + I * (γ : ℂ)) / Lam ((-1 : ℂ) + I * (γ : ℂ))
      = - star (deriv Lam ((2 : ℂ) + I * (γ : ℂ)) / Lam ((2 : ℂ) + I * (γ : ℂ))) := by
  have harg : star (1 - ((-1 : ℂ) + I * (γ : ℂ))) = (2 : ℂ) + I * (γ : ℂ) := by
    have hz : (1 : ℂ) - ((-1 : ℂ) + I * (γ : ℂ)) = star ((2 : ℂ) + I * (γ : ℂ)) := by
      apply Complex.ext <;> simp [Complex.star_def, Complex.conj_re, Complex.conj_im] <;> ring
    rw [hz, star_star]
  have h1 : Lam (star (1 - ((-1 : ℂ) + I * (γ : ℂ)))) ≠ 0 := by rw [harg]; exact hs'
  have h := logDeriv_FE hW hFE hDiff hs h1
  simpa [harg] using h

end

end Work.FIArea5.S16Hecke
