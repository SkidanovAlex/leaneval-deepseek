/-
# `FTS/PhiStar/CoreAux/Fb_basic.lean` — the shifted flat class `Fb` is closed under products

`Work.FTS.PhiStar.Fb n K f` (`CoreAux/Defs.lean`) is the *pair* of flat bounds
`F0 n K f` **and** `F0 n K (∂_θ f)`, i.e.

* `|(z+1)^k ∂_z^k D_θ^i f| ≤ K` for `k + i ≤ n`, and
* `|(z+1)^k ∂_z^k D_θ^i (∂_θ f)| ≤ K` for `k + i ≤ n`,

on the open quadrant `Q0 = (0,∞)×(0,π/2)`.  This is the class that survives products: the
product rule for `∂_θ` needs the shifted family `D_θ^i(∂_θ f)`, which `F0` alone does not
provide.

**Main result** (`Fb_basic`): `Fb n K f` and `Fb n K' g` imply
`Fb n (2^n (K+K')(K+K')) (f·g)`.

The two halves:

* `F0 n (2^n K K') (f·g)` is `F0_mul` applied to the first halves;
* `∂_θ(f·g) = ∂_θf·g + f·∂_θg` on `Q0` (the product rule, both slices being `C^∞` there by
  `SmoothOpen.curry_θ`), so `F0_add` and two more applications of `F0_mul` give
  `F0 n (2^{n+1} K K') (∂_θ(f·g))`.

Both constants are dominated by `2^n (K+K')²` because `(K+K')² - K K' = K² + KK' + K'² ≥ 0`
and `2 K K' ≤ (K+K')²` (with `K, K' ≥ 0`, which follows from `F0 n K f` by evaluating at the
point `(1, π/4)` of the open quadrant).

The only technical point is that the two derivations are *local*, so the identity
`∂_θ(f·g) = ∂_θf·g + f·∂_θg` can be transferred to `F0`; the small congruence lemmas
`Fbq_pzIter_congr`, `Fbq_DthIter_congr` and `Fbq_F0_congr` below do this (they need no
smoothness: they only use the locality of `deriv`).

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.PhiStar.CoreAux.Defs
import Submission.Work.FTS.PhiStar.CoreAux.F0_mul
import Submission.Work.FTS.PhiStar.CoreAux.F0_add
import Submission.Work.FTS.PhiStar.CoreAux.F0_congr

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.CoreAux

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped Real Topology
open Filter

/-! ## Two elementary closure facts -/

/-- `SmoothOpen` is closed under pointwise multiplication. -/
theorem Fbq_smoothOpen_mul {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ * g z θ) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ : ℝ => f z θ * g z θ)) Work.FTS.EllipticEst.Q0
  have hfun : Function.uncurry (fun z θ : ℝ => f z θ * g z θ)
      = fun p : ℝ × ℝ => Function.uncurry f p * Function.uncurry g p := rfl
  rw [hfun]
  exact hf.mul hg

/-- `F0 n K f` forces `0 ≤ K`: evaluate the bound at the point `(1, π/4)` of the open
quadrant (`k = i = 0`). -/
theorem Fbq_nonneg_of_F0 {n : ℕ} {K : ℝ} {f : ℝ → ℝ → ℝ} (h : F0 n K f) : 0 ≤ K := by
  have h0 := h 0 0 (Nat.zero_le n) 1 (Real.pi / 4) (by norm_num)
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have h0' : |f 1 (Real.pi / 4)| ≤ K := by
    simpa only [Work.Spaces.pzIter_zero, Work.Spaces.DthIter_zero, pow_zero, one_mul] using h0
  exact le_trans (abs_nonneg _) h0'

/-! ## Locality: the iterated operators depend only on the values on an open set

All three lemmas below are stated for data agreeing merely *pointwise on the open quadrant*
(no smoothness): every iterate of `∂_z`, `D_θ = sin(2·)∂_θ` is built from `deriv`, which is
local, and the quadrant is open (and its `θ`-slices `(0,π/2)` and `z`-slices `(0,∞)` are open
neighbourhoods of the relevant point). -/

/-- `∂_z^k` is local on the open quadrant. -/
theorem Fbq_pzIter_congr {F G : ℝ → ℝ → ℝ}
    (h : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → F z θ = G z θ) (k : ℕ) :
    ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pzIter k F z θ = Work.Spaces.pzIter k G z θ := by
  induction k with
  | zero => exact h
  | succ n ih =>
      intro z θ hz h1 h2
      have heq : (fun z' => Work.Spaces.pzIter n F z' θ)
          =ᶠ[𝓝 z] (fun z' => Work.Spaces.pzIter n G z' θ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact ih z' θ hz' h1 h2
      simp only [Work.Spaces.pzIter_succ, Work.Spaces.pz]
      exact heq.deriv_eq

/-- `D_θ^i` is local on the open quadrant. -/
theorem Fbq_DthIter_congr {F G : ℝ → ℝ → ℝ}
    (h : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → F z θ = G z θ) (i : ℕ) :
    ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DthIter i F z θ = Work.Spaces.DthIter i G z θ := by
  induction i with
  | zero => exact h
  | succ n ih =>
      intro z θ hz h1 h2
      have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨h1, h2⟩
      have heq : (fun θ' => Work.Spaces.DthIter n F z θ')
          =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.DthIter n G z θ') := by
        filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
        exact ih z θ' hz hθ'.1 hθ'.2
      simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
      rw [heq.deriv_eq]

/-- **`F0` is local**: two functions agreeing on the open quadrant are in the same flat class. -/
theorem Fbq_F0_congr {n : ℕ} {K : ℝ} {F G : ℝ → ℝ → ℝ}
    (h : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → F z θ = G z θ)
    (hG : F0 n K G) : F0 n K F := by
  intro k i hki z θ hz h1 h2
  have hcongr := Fbq_pzIter_congr
    (F := Work.Spaces.DthIter i F) (G := Work.Spaces.DthIter i G)
    (fun z θ hz h1 h2 => Fbq_DthIter_congr h i z θ hz h1 h2) k z θ hz h1 h2
  rw [hcongr]
  exact hG k i hki z θ hz h1 h2

/-! ## The product rule for `∂_θ` on the open quadrant -/

/-- **The product rule for `∂_θ`**: for data which are `C^∞` on the open quadrant, the partial
`θ`-derivative of the pointwise product is the sum of the products. -/
theorem Fbq_pth_mul {f g : ℝ → ℝ → ℝ}
    (hsf : Work.FTS.EllipticEst.SmoothOpen f) (hsg : Work.FTS.EllipticEst.SmoothOpen g) :
    ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pth (fun z θ => f z θ * g z θ) z θ
        = Work.Spaces.pth f z θ * g z θ + f z θ * Work.Spaces.pth g z θ := by
  intro z θ hz h1 h2
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨h1, h2⟩
  have hd1 : DifferentiableAt ℝ (fun θ' => f z θ') θ :=
    ((hsf.curry_θ hz).differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds hθ)
  have hd2 : DifferentiableAt ℝ (fun θ' => g z θ') θ :=
    ((hsg.curry_θ hz).differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds hθ)
  show deriv (fun θ' => f z θ' * g z θ') θ
      = deriv (fun θ' => f z θ') θ * g z θ + f z θ * deriv (fun θ' => g z θ') θ
  rw [show (fun θ' => f z θ' * g z θ') = (fun θ' => f z θ') * (fun θ' => g z θ') from rfl]
  exact deriv_mul hd1 hd2

/-! ## The main theorem -/

theorem Fb_basic {n : ℕ} {K K' : ℝ} {f g : ℝ → ℝ → ℝ} (hsf : Work.FTS.EllipticEst.SmoothOpen f) (hsg : Work.FTS.EllipticEst.SmoothOpen g) (hf : Work.FTS.PhiStar.Fb n K f) (hg : Work.FTS.PhiStar.Fb n K' g) : Work.FTS.PhiStar.Fb n ((2 : ℝ) ^ n * (K + K') * (K + K')) (fun z θ => f z θ * g z θ) := by
  have hp2 : (0 : ℝ) < (2 : ℝ) ^ n := pow_pos (by norm_num) n
  have hK : 0 ≤ K := Fbq_nonneg_of_F0 hf.f0
  have hK' : 0 ≤ K' := Fbq_nonneg_of_F0 hg.f0
  -- the two comparisons of the constants
  have hle1 : (2 : ℝ) ^ n * K * K' ≤ (2 : ℝ) ^ n * (K + K') * (K + K') := by
    have hsq : K * K' ≤ (K + K') * (K + K') := by
      nlinarith [sq_nonneg K, sq_nonneg K', sq_nonneg (K + K'), mul_nonneg hK hK']
    calc (2 : ℝ) ^ n * K * K' = (2 : ℝ) ^ n * (K * K') := by ring
      _ ≤ (2 : ℝ) ^ n * ((K + K') * (K + K')) := mul_le_mul_of_nonneg_left hsq hp2.le
      _ = (2 : ℝ) ^ n * (K + K') * (K + K') := by ring
  have hle2 : (2 : ℝ) ^ n * K * K' + (2 : ℝ) ^ n * K * K'
      ≤ (2 : ℝ) ^ n * (K + K') * (K + K') := by
    have h1 : (0 : ℝ) ≤ (2 : ℝ) ^ n * K ^ 2 := mul_nonneg hp2.le (sq_nonneg K)
    have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ n * K' ^ 2 := mul_nonneg hp2.le (sq_nonneg K')
    nlinarith [h1, h2]
  -- the first half: `F0` of `f * g`
  have hfg : F0 n ((2 : ℝ) ^ n * (K + K') * (K + K')) (fun z θ => f z θ * g z θ) :=
    (F0_mul hK hK' hsf hsg hf.f0 hg.f0).mono le_rfl hle1
  -- the second half: `F0` of `∂_θ (f * g)`
  have hQ : F0 n ((2 : ℝ) ^ n * (K + K') * (K + K'))
      (fun z θ => Work.Spaces.pth f z θ * g z θ + f z θ * Work.Spaces.pth g z θ) := by
    have h1 : F0 n ((2 : ℝ) ^ n * K * K') (fun z θ => Work.Spaces.pth f z θ * g z θ) :=
      F0_mul hK hK' hsf.pth hsg hf.fd hg.f0
    have h2 : F0 n ((2 : ℝ) ^ n * K * K') (fun z θ => f z θ * Work.Spaces.pth g z θ) :=
      F0_mul hK hK' hsf hsg.pth hf.f0 hg.fd
    have h3 : F0 n ((2 : ℝ) ^ n * K * K' + (2 : ℝ) ^ n * K * K')
        (fun z θ => Work.Spaces.pth f z θ * g z θ + f z θ * Work.Spaces.pth g z θ) :=
      F0_add (Fbq_smoothOpen_mul hsf.pth hsg) (Fbq_smoothOpen_mul hsf hsg.pth) h1 h2
    exact h3.mono le_rfl hle2
  exact ⟨hfg, Fbq_F0_congr (Fbq_pth_mul hsf hsg) hQ⟩

end Work.FTS.PhiStar.CoreAux
