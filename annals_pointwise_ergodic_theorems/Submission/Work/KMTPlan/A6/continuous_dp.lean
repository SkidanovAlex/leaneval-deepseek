/-
# Joint continuity of the mixed partial derivatives `∂₁^{j₁} ∂₂^{j₂} σ`

The §6 model approximation of Krause--Mirek--Tao works with the symbol `σ : ℝ → ℝ → ℂ` of the
model operator together with its mixed partial derivatives

  `dp j₁ j₂ σ x y = ∂₁^{j₁} ∂₂^{j₂} σ (x,y)`

as defined in `SymToolbox` (`dp = dp1 j₁ ∘ dp2 j₂`, with `dp1`/`dp2` the iterated `deriv` in the
first/second variable).  The estimates of §6 are stated for a symbol `σ` which is `C^4` on `ℝ²`
and use that these derivatives, up to order `2` in each variable, are *jointly continuous* in
`(x,y)`; that is exactly the statement proved here.

The argument is the standard one and avoids any explicit multilinear/Fréchet bookkeeping:

* for a `C¹` function `G : ℝ × ℝ → ℂ`, differentiating the curve `t ↦ G (x,t)` is evaluating the
  Fréchet derivative on `(0,1)`,  `∂₂ G (x,y) = fderiv ℝ G (x,y) (0,1)`, and analogously
  `∂₁ G (x,y) = fderiv ℝ G (x,y) (1,0)` (chain rule for `HasFDerivAt` along `HasDerivAt`);
* `ContDiff.contDiff_fderiv_apply` says that for `G` of class `C^{m+1}` the function
  `(x,y) ↦ fderiv ℝ G (x,y) (0,1)` is of class `C^m`: evaluation of a continuous linear map at the
  fixed vector `(0,1)` is itself a continuous linear map, and `p ↦ (p,(0,1))` is smooth
  (`contDiff_prodMk_left`);
* iterating gives that the `k`-th partial derivative of a `C^n` function is `C^{n-k}`, hence
  continuous as soon as `k ≤ n`; here we only need `ContDiff ℝ 0`, which follows by
  `ContDiff.of_le` from the `C^{n-k}` statement (`n - k` need not itself be `0`).
-/
import Mathlib
import Submission.Work.KMTPlan.A6.SymToolbox

set_option autoImplicit false

namespace Work.KMTPlan.A6

open MeasureTheory

noncomputable section

/-- The `k`-th partial derivative of `G : ℝ × ℝ → ℂ` in the **second** variable, as a function on
`ℝ × ℝ`: `iterDerivSnd k G (x,y) = ∂₂^k G (x,y)`. -/
def iterDerivSnd (k : ℕ) (G : ℝ × ℝ → ℂ) : ℝ × ℝ → ℂ :=
  fun p => iteratedDeriv k (fun t => G (p.1, t)) p.2

/-- The `k`-th partial derivative of `G : ℝ × ℝ → ℂ` in the **first** variable, as a function on
`ℝ × ℝ`: `iterDerivFst k G (x,y) = ∂₁^k G (x,y)`. -/
def iterDerivFst (k : ℕ) (G : ℝ × ℝ → ℂ) : ℝ × ℝ → ℂ :=
  fun p => iteratedDeriv k (fun s => G (s, p.2)) p.1

lemma iterDerivSnd_zero (G : ℝ × ℝ → ℂ) : iterDerivSnd 0 G = G := by
  funext p
  simp only [iterDerivSnd, iteratedDeriv_zero]

lemma iterDerivFst_zero (G : ℝ × ℝ → ℂ) : iterDerivFst 0 G = G := by
  funext p
  simp only [iterDerivFst, iteratedDeriv_zero]

/-- The `k+1`-st partial derivative in the second variable is the first partial derivative of the
`k`-th one. -/
lemma iterDerivSnd_one_comp (k : ℕ) (G : ℝ × ℝ → ℂ) :
    iterDerivSnd 1 (iterDerivSnd k G) = iterDerivSnd (k+1) G := by
  funext p
  simp only [iterDerivSnd, iteratedDeriv_succ, iteratedDeriv_zero]

/-- The `k+1`-st partial derivative in the first variable is the first partial derivative of the
`k`-th one. -/
lemma iterDerivFst_one_comp (k : ℕ) (G : ℝ × ℝ → ℂ) :
    iterDerivFst 1 (iterDerivFst k G) = iterDerivFst (k+1) G := by
  funext p
  simp only [iterDerivFst, iteratedDeriv_succ, iteratedDeriv_zero]

/-- The first partial derivative in the second variable of a `C^{m+1}` function is `C^m`. -/
lemma contDiff_iterDerivSnd_one {G : ℝ × ℝ → ℂ} {m : ℕ} (hG : ContDiff ℝ (m+1) G) :
    ContDiff ℝ m (iterDerivSnd 1 G) := by
  have hfun : iterDerivSnd 1 G = fun p : ℝ×ℝ => fderiv ℝ G p ((0:ℝ),(1:ℝ)) := by
    funext p
    simp only [iterDerivSnd, iteratedDeriv_one]
    have hγ : HasDerivAt (fun t : ℝ => (p.1, t)) ((0:ℝ),(1:ℝ)) p.2 :=
      (hasDerivAt_const (p.2) (p.1)).prodMk (hasDerivAt_id p.2)
    have h3 : HasDerivAt (G ∘ fun t : ℝ => (p.1, t)) ((fderiv ℝ G p) ((0:ℝ),(1:ℝ))) p.2 :=
      ((hG.differentiable (by simp) p).hasFDerivAt).comp_hasDerivAt (p.2) hγ
    exact h3.deriv
  rw [hfun]
  have hbase : ContDiff ℝ m (fun q : (ℝ×ℝ) × (ℝ×ℝ) => (fderiv ℝ G q.1) q.2) :=
    hG.contDiff_fderiv_apply (m := m) (by simp)
  have hemb : ContDiff ℝ m (fun q : ℝ×ℝ => (q, ((0:ℝ),(1:ℝ)))) := contDiff_prodMk_left _
  exact hbase.comp hemb

/-- The first partial derivative in the first variable of a `C^{m+1}` function is `C^m`. -/
lemma contDiff_iterDerivFst_one {G : ℝ × ℝ → ℂ} {m : ℕ} (hG : ContDiff ℝ (m+1) G) :
    ContDiff ℝ m (iterDerivFst 1 G) := by
  have hfun : iterDerivFst 1 G = fun p : ℝ×ℝ => fderiv ℝ G p ((1:ℝ),(0:ℝ)) := by
    funext p
    simp only [iterDerivFst, iteratedDeriv_one]
    have hγ : HasDerivAt (fun s : ℝ => (s, p.2)) ((1:ℝ),(0:ℝ)) p.1 :=
      (hasDerivAt_id p.1).prodMk (hasDerivAt_const (p.1) (p.2))
    have h3 : HasDerivAt (G ∘ fun s : ℝ => (s, p.2)) ((fderiv ℝ G p) ((1:ℝ),(0:ℝ))) p.1 :=
      ((hG.differentiable (by simp) p).hasFDerivAt).comp_hasDerivAt (p.1) hγ
    exact h3.deriv
  rw [hfun]
  have hbase : ContDiff ℝ m (fun q : (ℝ×ℝ) × (ℝ×ℝ) => (fderiv ℝ G q.1) q.2) :=
    hG.contDiff_fderiv_apply (m := m) (by simp)
  have hemb : ContDiff ℝ m (fun q : ℝ×ℝ => (q, ((1:ℝ),(0:ℝ)))) := contDiff_prodMk_left _
  exact hbase.comp hemb

/-- The `k`-th partial derivative in the second variable of a `C^{n}` function is `C^{n-k}`. -/
lemma contDiff_iterDerivSnd_aux : ∀ (k : ℕ) (n : ℕ) (G : ℝ×ℝ → ℂ),
    ContDiff ℝ ((n + k : ℕ) : WithTop ℕ∞) G → ContDiff ℝ (n : WithTop ℕ∞) (iterDerivSnd k G) := by
  intro k
  induction k with
  | zero =>
    intro n G hG
    rwa [iterDerivSnd_zero]
  | succ k ih =>
    intro n G hG
    have hcast : ((n + (k+1) : ℕ) : WithTop ℕ∞) = (((n+1) + k : ℕ) : WithTop ℕ∞) := by
      rw [show n + (k+1) = (n+1) + k from by omega]
    rw [hcast] at hG
    have h1 : ContDiff ℝ ((n+1 : ℕ) : WithTop ℕ∞) (iterDerivSnd k G) := ih (n+1) G hG
    have h2 : ContDiff ℝ (n : WithTop ℕ∞) (iterDerivSnd 1 (iterDerivSnd k G)) :=
      contDiff_iterDerivSnd_one h1
    rwa [iterDerivSnd_one_comp] at h2

/-- The `k`-th partial derivative in the first variable of a `C^{n}` function is `C^{n-k}`. -/
lemma contDiff_iterDerivFst_aux : ∀ (k : ℕ) (n : ℕ) (G : ℝ×ℝ → ℂ),
    ContDiff ℝ ((n + k : ℕ) : WithTop ℕ∞) G → ContDiff ℝ (n : WithTop ℕ∞) (iterDerivFst k G) := by
  intro k
  induction k with
  | zero =>
    intro n G hG
    rwa [iterDerivFst_zero]
  | succ k ih =>
    intro n G hG
    have hcast : ((n + (k+1) : ℕ) : WithTop ℕ∞) = (((n+1) + k : ℕ) : WithTop ℕ∞) := by
      rw [show n + (k+1) = (n+1) + k from by omega]
    rw [hcast] at hG
    have h1 : ContDiff ℝ ((n+1 : ℕ) : WithTop ℕ∞) (iterDerivFst k G) := ih (n+1) G hG
    have h2 : ContDiff ℝ (n : WithTop ℕ∞) (iterDerivFst 1 (iterDerivFst k G)) :=
      contDiff_iterDerivFst_one h1
    rwa [iterDerivFst_one_comp] at h2

/-- The mixed partial derivative `∂₁^{j₁} ∂₂^{j₂} σ` is `iterDerivFst j₁ (iterDerivSnd j₂ σ)`. -/
lemma dp_eq_iterDeriv (σ : ℝ → ℝ → ℂ) (j₁ j₂ : ℕ) :
    (fun p : ℝ × ℝ => Work.KMTPlan.A6.dp j₁ j₂ σ p.1 p.2)
      = iterDerivFst j₁ (iterDerivSnd j₂ (fun q : ℝ × ℝ => σ q.1 q.2)) := by
  funext p
  simp only [Work.KMTPlan.A6.dp, Work.KMTPlan.A6.dp1, Work.KMTPlan.A6.dp2,
    iterDerivFst, iterDerivSnd]

theorem continuous_dp (σ : ℝ → ℝ → ℂ)
    (hsm : ContDiff ℝ 4 (fun p : ℝ × ℝ => σ p.1 p.2))
    {j₁ j₂ : ℕ} (h₁ : j₁ ≤ 2) (h₂ : j₂ ≤ 2) :
    Continuous (fun p : ℝ × ℝ => Work.KMTPlan.A6.dp j₁ j₂ σ p.1 p.2) := by
  rw [dp_eq_iterDeriv]
  have hj₂4 : j₂ ≤ 4 := by omega
  have hG1 : ContDiff ℝ (((4 - j₂) + j₂ : ℕ) : WithTop ℕ∞) (fun q : ℝ × ℝ => σ q.1 q.2) := by
    rw [Nat.sub_add_cancel hj₂4]
    exact hsm
  have hQ : ContDiff ℝ ((4 - j₂ : ℕ) : WithTop ℕ∞)
      (iterDerivSnd j₂ (fun q : ℝ × ℝ => σ q.1 q.2)) :=
    contDiff_iterDerivSnd_aux j₂ (4 - j₂) _ hG1
  have hle : j₁ ≤ 4 - j₂ := by omega
  have hG2 : ContDiff ℝ ((((4 - j₂) - j₁) + j₁ : ℕ) : WithTop ℕ∞)
      (iterDerivSnd j₂ (fun q : ℝ × ℝ => σ q.1 q.2)) := by
    rw [Nat.sub_add_cancel hle]
    exact hQ
  have hP : ContDiff ℝ (((4 - j₂) - j₁ : ℕ) : WithTop ℕ∞)
      (iterDerivFst j₁ (iterDerivSnd j₂ (fun q : ℝ × ℝ => σ q.1 q.2))) :=
    contDiff_iterDerivFst_aux j₁ ((4 - j₂) - j₁) _ hG2
  have hP0 : ContDiff ℝ 0 (iterDerivFst j₁ (iterDerivSnd j₂ (fun q : ℝ × ℝ => σ q.1 q.2))) :=
    hP.of_le (by simp)
  exact contDiff_zero.mp hP0

end

end Work.KMTPlan.A6
