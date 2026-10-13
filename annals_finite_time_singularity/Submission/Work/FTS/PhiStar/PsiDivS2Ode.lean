import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.H2.StarPkg.LzeroSubst.lzero_sin_cos_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `θ`-equation for the divided angular profile `ψ / sin 2θ`

`Work.FTS.PhiStar.Psi0Ode` constructs the angular model `ψ` with `Lzero1 ψ = Γ̄` on `(0,π/2)`.
Writing `ψ = sin 2θ · G` (so that `G = ψ / sin 2θ` is the *divided* profile), the elliptic
equation turns into the second-order equation without singular coefficients

  `sin 2θ · G'' = (6 sin²θ - 4 cos²θ) · G' - Γ̄(θ)`,

which is the statement of `PsiDivS2Ode` and the equation solved by the paper's profile.

The algebraic content is the substitution identity
`Work.FTS.H2.StarPkg.LzeroSubst.lzero_sin_cos_mul`,

  `Lzero (sin θ cos θ · w) = -sin θ cos θ · ∂_θθw + (3 sin²θ - 2 cos²θ) · ∂_θw`,

applied to `w = 2G` (because `sin 2θ = 2 sin θ cos θ`), together with the fact that `Lzero`
only sees the `θ`-slice of its argument at the given `z` (lemma `Lzero_congr_slice` below).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

set_option autoImplicit false

/-- `Lzero` only sees the `θ`-slice at the given `z`: two functions whose `z`-slices agree in a
neighbourhood of `θ` have the same `Lzero`-value at `(z,θ)`. -/
lemma Lzero_congr_slice {Ψ Φ : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : (fun t => Ψ z t) =ᶠ[𝓝 θ] fun t => Φ z t) :
    Work.Elliptic.Lzero Ψ z θ = Work.Elliptic.Lzero Φ z θ := by
  have h1 : Work.Spaces.pthIter 2 Ψ z θ = Work.Spaces.pthIter 2 Φ z θ := by
    show deriv (fun t => deriv (fun t' => Ψ z t') t) θ
      = deriv (fun t => deriv (fun t' => Φ z t') t) θ
    exact h.deriv.deriv_eq
  have h2 : Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ
      = Work.Spaces.pth (fun z θ => Real.tan θ * Φ z θ) z θ := by
    show deriv (fun t => Real.tan t * Ψ z t) θ = deriv (fun t => Real.tan t * Φ z t) θ
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [h] with t ht
    rw [ht]
  simp only [Work.Elliptic.Lzero, h1, h2, h.eq_of_nhds]

theorem PsiDivS2Ode {α : ℝ} {ψ : ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n ψ (Set.Ioo 0 (Real.pi / 2)))
    (heq : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Work.FTS.EllipticEst.Lzero1 ψ θ = Work.FTS.VocabO.GamBar α θ) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Real.sin (2 * θ) * deriv (fun t => deriv (fun θ' => ψ θ' / Real.sin (2 * θ')) t) θ
        = (6 * Real.sin θ ^ 2 - 4 * Real.cos θ ^ 2)
            * deriv (fun θ' => ψ θ' / Real.sin (2 * θ')) θ
          - Work.FTS.VocabO.GamBar α θ := by
  intro θ hθ
  set G : ℝ → ℝ := fun θ' => ψ θ' / Real.sin (2 * θ') with hG
  have hpos : 0 < Real.pi := Real.pi_pos
  -- `G` is smooth on the open interval (where `sin 2θ > 0`)
  have hsm2 : ∀ n : ℕ, ContDiffOn ℝ n G (Set.Ioo 0 (Real.pi / 2)) := by
    intro n
    have hsin : ContDiffOn ℝ n (fun t : ℝ => Real.sin (2 * t)) (Set.Ioo 0 (Real.pi / 2)) := by
      fun_prop
    have hd := (hsm n).div hsin (fun t ht => by
      have h2 : 0 < Real.sin (2 * t) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1]) (by linarith [ht.2, hpos])
      exact ne_of_gt h2)
    rw [hG]
    exact hd
  have hdiffG : DifferentiableOn ℝ G (Set.Ioo 0 (Real.pi / 2)) :=
    (hsm2 1).differentiableOn (by norm_num)
  have hderivG : DifferentiableOn ℝ (deriv G) (Set.Ioo 0 (Real.pi / 2)) :=
    ((hsm2 2).deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)).differentiableOn (by norm_num)
  -- `ψ` agrees near `θ` with `sin θ cos θ · (2G)`, i.e. with `sin 2θ · G`
  have hψeq : (fun t : ℝ => ψ t) =ᶠ[𝓝 θ]
      fun t : ℝ => Real.sin t * Real.cos t * (2 * G t) := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with t ht
    have h1 : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, hpos])
    have h2 : 0 < Real.cos t :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, hpos], ht.2⟩
    simp only [hG]
    rw [Real.sin_two_mul]
    calc ψ t = (2 * Real.sin t * Real.cos t) * (ψ t / (2 * Real.sin t * Real.cos t)) :=
          (mul_div_cancel₀ (ψ t) (by positivity)).symm
      _ = Real.sin t * Real.cos t * (2 * (ψ t / (2 * Real.sin t * Real.cos t))) := by ring
  -- transport the equation along the equality of the slices
  have hL1 : Work.FTS.EllipticEst.Lzero1 ψ θ
      = Work.Elliptic.Lzero (fun z t => Real.sin t * Real.cos t * (2 * G t)) 0 θ := by
    rw [Work.FTS.EllipticEst.Lzero1_eq_Lzero ψ 0]
    exact Lzero_congr_slice hψeq
  -- the `θ`-derivatives of the substituted function
  have hpthw : Work.Spaces.pth (fun _ t : ℝ => 2 * G t) 0 θ = 2 * deriv G θ := by
    show deriv (fun t : ℝ => 2 * G t) θ = 2 * deriv G θ
    exact Work.Spaces.deriv_const_mul' 2 θ G
  have hpthIter2w : Work.Spaces.pthIter 2 (fun _ t : ℝ => 2 * G t) 0 θ
      = 2 * deriv (deriv G) θ := by
    have hfun : (fun t : ℝ => Work.Spaces.pth (fun _ t : ℝ => 2 * G t) 0 t)
        = fun t => 2 * deriv G t := by
      funext t
      show deriv (fun t : ℝ => 2 * G t) t = 2 * deriv G t
      exact Work.Spaces.deriv_const_mul' 2 t G
    show deriv (fun t : ℝ => Work.Spaces.pth (fun _ t : ℝ => 2 * G t) 0 t) θ
      = 2 * deriv (deriv G) θ
    rw [hfun]
    exact Work.Spaces.deriv_const_mul' 2 θ (deriv G)
  -- the substitution identity
  have hsub := Work.FTS.H2.StarPkg.LzeroSubst.lzero_sin_cos_mul (w := fun _ t : ℝ => 2 * G t)
      (z := 0) (θ := θ) hθ (hdiffG.const_mul 2) (by
        have he : (fun θ' : ℝ => deriv (fun θ'' : ℝ => 2 * G θ'') θ')
            = fun θ' => 2 * deriv G θ' := by
          funext t
          exact Work.Spaces.deriv_const_mul' 2 t G
        rw [he]
        exact hderivG.const_mul 2)
  -- the divided equation
  have hkey : -(Real.sin (2 * θ)) * deriv (deriv G) θ
        + (6 * Real.sin θ ^ 2 - 4 * Real.cos θ ^ 2) * deriv G θ
      = Work.FTS.VocabO.GamBar α θ := by
    rw [← heq θ hθ, hL1, hsub, hpthIter2w, hpthw, Real.sin_two_mul]
    ring
  show Real.sin (2 * θ) * deriv (deriv G) θ
      = (6 * Real.sin θ ^ 2 - 4 * Real.cos θ ^ 2) * deriv G θ - Work.FTS.VocabO.GamBar α θ
  rw [← hkey]
  ring

end Work.FTS.PhiStar
