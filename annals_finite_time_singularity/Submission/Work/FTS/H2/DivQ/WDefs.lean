/-
Copyright: work module for the Elgindi finite-time singularity project.

# The vocabulary of the near-region inversion, exported

`Submission/Work/FTS/H2/DivQ/inversionNear.lean` proves the triangular inversion of §4 of
`Submission/Work/FTS/H2/DivQ/NOTES.md`

  `B_j := ∫_0^{x₁} x^{2j-γ}(∂_x^{j+1}(sliceX h))² dx ≤ C (Denη + Σ_{1≤m≤j} Denγ m)`

but all of its auxiliary objects (`Wide`, `Dom`, `AccDom`, `SubEta`, `HonGam`, …) are `private`,
so they cannot be reused by a consumer.  This file re-declares that vocabulary *publicly*, together
with the elementary substitution facts (`x = sin 2θ`) and the integrability of the two building
blocks `SubEta`, `HonGam` (the `x`-pullbacks of the two honest `θ`-data integrals).

The declarations here are copies (with the `private` tag removed) of the corresponding ones in
`inversionNear.lean`, so that the domination `Wide ≤ Dom` — and hence the integrability of `Wide`,
which `inversionNear`'s statement does not export — can be re-derived on top of them.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.H2.DivQ.Defs
import Submission.Work.FTS.H2.DivQ.thetaOfSubst
import Submission.Work.FTS.H2.DivQ.aCoeff_bounds
import Submission.Work.Elliptic.DivSinDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.DivQ

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The integrands

`PsiEta`/`PsiGam m` are the *honest angular data* (`θ`-integrals), `SubEta`/`SubGam m`/`HonGam m`
their pullbacks under `x = sin(2θ)` (with the Jacobian `1/(2κ x)`), `Wide l` the `x`-weighted
square of the `(l+1)`-st derivative of the slice, and `Dom`/`AccDom` the dominating functions
produced by the triangular inversion. -/

/-- `(∂_θh)² sin(2θ)^{-η}`. -/
def PsiEta (h : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))

/-- `(D_θ^m(∂_θh))² sin(2θ)^{-γ}`. -/
def PsiGam (α : ℝ) (h : ℝ → ℝ) (m : ℕ) : ℝ → ℝ :=
  fun θ => (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2
    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))

/-- The `x`-pullback of `PsiEta`. -/
def SubEta (h : ℝ → ℝ) : ℝ → ℝ :=
  fun x => PsiEta h (thetaOf x) * (1 / (2 * kappa x))

/-- The `x`-pullback of `PsiGam m`. -/
def SubGam (α : ℝ) (h : ℝ → ℝ) (m : ℕ) : ℝ → ℝ :=
  fun x => PsiGam α h m (thetaOf x) * (1 / (2 * kappa x))

/-- The `x`-pullback of `PsiGam m` with `sin(2θ(x))` evaluated as `x`. -/
def HonGam (α : ℝ) (h : ℝ → ℝ) (m : ℕ) : ℝ → ℝ :=
  fun x => (Work.Elliptic.Dth1Iter m (deriv h) (thetaOf x)) ^ 2
    * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))

/-- The integrand `x ↦ x^{2l-γ}(∂_x^{l+1}(sliceX h) x)²` of `B_l`. -/
def Wide (α : ℝ) (h : ℝ → ℝ) (l : ℕ) : ℝ → ℝ :=
  fun x => x ^ (2 * (l : ℝ) - Work.Spaces.gam α)
    * (iteratedDeriv (l + 1) (sliceX h) x) ^ 2

/-- The off-diagonal part of the level-`j` expansion. -/
def Restn (h : ℝ → ℝ) (j : ℕ) : ℝ → ℝ :=
  fun x => ∑ l ∈ Finset.range j,
    aCoeff j l x * (x ^ l * iteratedDeriv (l + 1) (sliceX h) x)

/-- The full `j`-th expansion of `D_θ^j(∂_θh)(θ x)`. -/
def Expn (h : ℝ → ℝ) (j : ℕ) : ℝ → ℝ :=
  fun x => ∑ l ∈ Finset.range (j + 1),
    aCoeff j l x * (x ^ l * iteratedDeriv (l + 1) (sliceX h) x)

/-- The joint recursion producing the dominating functions `Dom` and their partial sums
`AccDom`. -/
def domSeq (α : ℝ) (h : ℝ → ℝ) (Cm : ℝ) : ℕ → (ℝ → ℝ) × (ℝ → ℝ)
  | 0 => (SubEta h, fun _ => 0)
  | (l + 1) =>
      (fun x => 2 * HonGam α h (l + 1) x
          + 2 * (((l + 1 : ℕ) : ℝ)) * Cm ^ 2
              * ((domSeq α h Cm l).2 x + (domSeq α h Cm l).1 x),
        fun x => (domSeq α h Cm l).2 x + (domSeq α h Cm l).1 x)

/-- An integrable dominating function for the level-`l` quantity. -/
def Dom (α : ℝ) (h : ℝ → ℝ) (Cm : ℝ) (l : ℕ) : ℝ → ℝ := (domSeq α h Cm l).1

/-- The partial sum `Σ_{m < l} Dom m`. -/
def AccDom (α : ℝ) (h : ℝ → ℝ) (Cm : ℝ) (l : ℕ) : ℝ → ℝ := (domSeq α h Cm l).2

/-! ## Elementary substitution facts -/

private lemma xNear_sq : xNear ^ 2 = 1 / 2 := by
  rw [xNear, Real.sin_pi_div_four, div_pow, Real.sq_sqrt (by norm_num)]
  norm_num

/-- `sin (2 θ(x)) = x` for `x ∈ [-1,1]`. -/
lemma sin_two_thetaOf {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    Real.sin (2 * thetaOf x) = x := by
  have h2 : 2 * thetaOf x = Real.arcsin x := by simp only [thetaOf]; ring
  rw [h2, Real.sin_arcsin hx.1 hx.2]

/-- `sin (2 θ(x)) = x` on the near interval. -/
lemma sin_two_thetaOf_Ioo {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) xNear) :
    Real.sin (2 * thetaOf x) = x :=
  sin_two_thetaOf ⟨by linarith [hx.1], by linarith [hx.2, xNear_lt]⟩

/-- On the near interval `(0,x₁)`, `θ(x)` lands in the angular interval `(0,π/2)`. -/
lemma thetaOf_mem_Ioo {x : ℝ} (hx : x ∈ Set.Ioo 0 xNear) :
    thetaOf x ∈ Set.Ioo 0 (Real.pi / 2) := by
  have ha0 : 0 < Real.arcsin x := Real.arcsin_pos.mpr hx.1
  have ha2 : Real.arcsin x ≤ Real.pi / 2 := (Real.arcsin_mem_Icc x).2
  constructor <;> simp only [thetaOf] <;> linarith

/-- `θ(x₁) = π/8`. -/
lemma thetaOf_xNear : thetaOf xNear = Real.pi / 8 := by
  rw [thetaOf, xNear, Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])]
  ring

lemma thetaOf_zero : thetaOf 0 = 0 := by simp [thetaOf]

/-- `θ` is differentiable with derivative the Jacobian `1/(2κ x)`. -/
lemma hasDerivAt_thetaOf' {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt thetaOf (1 / (2 * kappa x)) x := by
  have h1 : HasDerivAt Real.arcsin (1 / Real.sqrt (1 - x ^ 2)) x :=
    Real.hasDerivAt_arcsin (ne_of_gt hx.1) (ne_of_lt hx.2)
  have h2 : HasDerivAt (fun y => Real.arcsin y / 2) ((1 / Real.sqrt (1 - x ^ 2)) / 2) x :=
    h1.div_const 2
  have hval : (1 / Real.sqrt (1 - x ^ 2)) / 2 = 1 / (2 * kappa x) := by
    rw [kappa_eq_sqrt]; ring
  exact h2.congr_deriv hval

/-- `1/√2 ≤ κ x` on `[0,x₁]`. -/
lemma kappa_ge {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) xNear) :
    1 / Real.sqrt 2 ≤ kappa x := by
  have hxnn : 0 ≤ x := hx.1
  have hxsq : x ^ 2 ≤ 1 / 2 := by
    have h1 : x * x ≤ xNear * xNear :=
      mul_le_mul hx.2 hx.2 hxnn (le_trans hxnn hx.2)
    have h2 : xNear * xNear = 1 / 2 := by simpa [pow_two] using xNear_sq
    nlinarith [h1, h2]
  have hsqrt : Real.sqrt (1 / 2) ≤ Real.sqrt (1 - x ^ 2) := Real.sqrt_le_sqrt (by linarith)
  have h2 : Real.sqrt (1 / 2) = 1 / Real.sqrt 2 := by
    rw [Real.sqrt_div (by norm_num : (0:ℝ) ≤ 1) 2, Real.sqrt_one]
  rw [kappa_eq_sqrt]
  linarith [hsqrt, h2]

/-- `1 ≤ 2 κ x` on `[0,x₁]`. -/
lemma two_kappa_ge_one {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) xNear) :
    1 ≤ 2 * kappa x := by
  have h := kappa_ge hx
  have h2 : (2:ℝ) * (1 / Real.sqrt 2) = Real.sqrt 2 := by
    rw [mul_one_div, div_eq_iff (by positivity : (Real.sqrt 2) ≠ 0)]
    rw [← pow_two, Real.sq_sqrt (by norm_num)]
  have h3 : (1:ℝ) ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  linarith [h, h2, h3]

/-- `γ < 4 + η` for `α ≤ 1`. -/
lemma gam_lt_four {α : ℝ} (hα : α ≤ 1) : Work.Spaces.gam α < 4 + Work.Spaces.eta := by
  unfold Work.Spaces.gam Work.Spaces.eta; linarith

lemma psiEta_nonneg (h : ℝ → ℝ) :
    ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ PsiEta h θ := by
  intro θ hθ
  have hs : 0 ≤ Real.sin (2 * θ) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi <;>
      simp only [Work.Spaces.Iθ, Set.mem_Icc] at hθ <;> linarith
  exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs _)

lemma psiGam_nonneg (α : ℝ) (h : ℝ → ℝ) (m : ℕ) :
    ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ PsiGam α h m θ := by
  intro θ hθ
  have hs : 0 ≤ Real.sin (2 * θ) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi <;>
      simp only [Work.Spaces.Iθ, Set.mem_Icc] at hθ <;> linarith
  exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs _)

/-- The chain rule for `sliceX h = h ∘ θ` on the near interval. -/
lemma deriv_sliceX_eq {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2))) {x : ℝ}
    (hx : x ∈ Set.Ioo 0 xNear) :
    deriv (sliceX h) x = deriv h (thetaOf x) * (1 / (2 * kappa x)) := by
  have hyI : x ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2, xNear_lt]⟩
  have hmem : thetaOf x ∈ Set.Ioo 0 (Real.pi / 2) := thetaOf_mem_Ioo hx
  have hdh : DifferentiableAt ℝ h (thetaOf x) :=
    ((hsm.contDiffAt (isOpen_Ioo.mem_nhds hmem)).differentiableAt (by simp))
  exact (hdh.hasDerivAt.comp x (hasDerivAt_thetaOf' hyI)).deriv

/-- `sliceX h = h ∘ θ` is `C^∞` on the near interval. -/
lemma contDiffOn_sliceX {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ (⊤ : ℕ∞) (sliceX h) (Set.Ioo 0 xNear) := by
  have hθ : ContDiffOn ℝ (⊤ : ℕ∞) thetaOf (Set.Ioo 0 xNear) := by
    intro x hx
    have h1 : ContDiffAt ℝ (⊤ : ℕ∞) Real.arcsin x :=
      Real.contDiffAt_arcsin (by linarith [hx.1]) (by linarith [hx.2, xNear_lt])
    have h2 : ContDiffAt ℝ (⊤ : ℕ∞) thetaOf x := h1.div_const 2
    exact h2.contDiffWithinAt
  exact hsm.comp hθ (fun x hx => thetaOf_mem_Ioo hx)

/-- Every iterated `x`-derivative of `sliceX h` is `C^∞` on the near interval. -/
lemma contDiffOn_iteratedDeriv_sliceX {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2))) (n : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (iteratedDeriv n (sliceX h)) (Set.Ioo 0 xNear) := by
  induction n with
  | zero => simpa using contDiffOn_sliceX hsm
  | succ n ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv_of_isOpen isOpen_Ioo (by simp)

/-- The auxiliary `x^{-η}(∂_x(sliceX h))²` of the `l = 0` slot is dominated by `SubEta`. -/
lemma etaPiece_le_subEta {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2))) {x : ℝ}
    (hx : x ∈ Set.Ioo 0 xNear) :
    x ^ (-(Work.Spaces.eta)) * (deriv (sliceX h) x) ^ 2 ≤ SubEta h x := by
  have hxnn : (0:ℝ) ≤ x := le_of_lt hx.1
  have hk1 : (1:ℝ) ≤ 2 * kappa x := two_kappa_ge_one ⟨hxnn, le_of_lt hx.2⟩
  have hkpos : (0:ℝ) < 2 * kappa x := lt_of_lt_of_le one_pos hk1
  have hs : Real.sin (2 * thetaOf x) = x := sin_two_thetaOf_Ioo hx
  have hd : deriv (sliceX h) x = deriv h (thetaOf x) * (1 / (2 * kappa x)) :=
    deriv_sliceX_eq hsm hx
  have h1 : (1:ℝ) / (2 * kappa x) ≤ 1 := by
    rw [div_le_one hkpos]; linarith
  have h2 : (0:ℝ) ≤ (deriv h (thetaOf x)) ^ 2 * x ^ (-(Work.Spaces.eta)) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hxnn _)
  simp only [SubEta, PsiEta, hs]
  rw [hd]
  have hrw : x ^ (-(Work.Spaces.eta))
        * (deriv h (thetaOf x) * (1 / (2 * kappa x))) ^ 2
      = (deriv h (thetaOf x)) ^ 2 * x ^ (-(Work.Spaces.eta))
          * (1 / (2 * kappa x)) ^ 2 := by
    ring
  rw [hrw]
  have h3 : (1 / (2 * kappa x)) ^ 2 ≤ 1 / (2 * kappa x) := by
    have hnn : (0:ℝ) ≤ 1 / (2 * kappa x) := by positivity
    nlinarith [h1, hnn]
  calc (deriv h (thetaOf x)) ^ 2 * x ^ (-(Work.Spaces.eta)) * (1 / (2 * kappa x)) ^ 2
      ≤ (deriv h (thetaOf x)) ^ 2 * x ^ (-(Work.Spaces.eta)) * (1 / (2 * kappa x)) :=
        mul_le_mul_of_nonneg_left h3 h2
    _ = (deriv h (thetaOf x)) ^ 2 * x ^ (-(Work.Spaces.eta)) * (1 / (2 * kappa x)) := rfl

/-! ## Integrability of the two building blocks -/

/-- The `η`-pullback of the honest `η`-data is integrable on `(0,x₁)`. -/
lemma subEta_integrable {h : ℝ → ℝ}
    (hint : MeasureTheory.IntegrableOn (PsiEta h) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (SubEta h) (Set.Ioo 0 xNear) := by
  have h1 : MeasureTheory.IntegrableOn (SubEta h) (Set.Ioc 0 xNear) :=
    (thetaOfSubst (Ψ := PsiEta h) hint (psiEta_nonneg h)).1
  rw [← integrableOn_Ioc_iff_integrableOn_Ioo]
  exact h1

/-- The `x`-pullback of the honest `γ`-data at order `m` is integrable on `(0,x₁)`. -/
lemma subGam_integrable {α : ℝ} {h : ℝ → ℝ} {m : ℕ}
    (hint : MeasureTheory.IntegrableOn (PsiGam α h m) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (SubGam α h m) (Set.Ioo 0 xNear) := by
  have h1 : MeasureTheory.IntegrableOn (SubGam α h m) (Set.Ioc 0 xNear) :=
    (thetaOfSubst (Ψ := PsiGam α h m) hint (psiGam_nonneg α h m)).1
  rw [← integrableOn_Ioc_iff_integrableOn_Ioo]
  exact h1

/-- The same, with `sin(2θ(x))` evaluated as `x`. -/
lemma honGam_integrable {α : ℝ} {h : ℝ → ℝ} {m : ℕ}
    (hint : MeasureTheory.IntegrableOn (PsiGam α h m) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (HonGam α h m) (Set.Ioo 0 xNear) := by
  refine (subGam_integrable hint).congr_fun (fun x hx => ?_) measurableSet_Ioo
  simp only [HonGam, SubGam, PsiGam, sin_two_thetaOf_Ioo hx]

/-! ## Elementary algebra of the weights -/

/-- `(x^m)² x^{c} = x^{2m+c}` for `x > 0`. -/
lemma pow_sq_mul_rpow {x : ℝ} (hx : 0 < x) (m : ℕ) (c : ℝ) :
    (x ^ m) ^ 2 * x ^ c = x ^ (2 * (m : ℝ) + c) := by
  rw [← pow_mul, show m * 2 = 2 * m by ring, ← Real.rpow_natCast x (2 * m),
    show ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) by push_cast; ring, ← Real.rpow_add hx]

/-- The Young inequality `A² ≤ 2(A+R)² + 2R²`. -/
lemma young (A R : ℝ) : A ^ 2 ≤ 2 * (A + R) ^ 2 + 2 * R ^ 2 := by
  nlinarith [sq_nonneg (A + 2 * R)]

lemma Wide_nonneg (α : ℝ) (h : ℝ → ℝ) (l : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ Wide α h l x :=
  mul_nonneg (Real.rpow_nonneg hx _) (sq_nonneg _)

/-! ## The recursion and its elementary properties -/

lemma AccDom_succ (α : ℝ) (h : ℝ → ℝ) (Cm : ℝ) (l : ℕ) :
    AccDom α h Cm (l + 1) = fun x => AccDom α h Cm l x + Dom α h Cm l x := by
  funext x
  simp only [AccDom, Dom, domSeq]

lemma Dom_succ (α : ℝ) (h : ℝ → ℝ) (Cm : ℝ) (l : ℕ) :
    Dom α h Cm (l + 1) = fun x => 2 * HonGam α h (l + 1) x
        + 2 * (((l + 1 : ℕ) : ℝ)) * Cm ^ 2 * AccDom α h Cm (l + 1) x := by
  funext x
  simp only [AccDom, Dom, domSeq]

lemma Dom_zero (α : ℝ) (h : ℝ → ℝ) (Cm : ℝ) :
    Dom α h Cm 0 = SubEta h := by
  funext x
  simp only [Dom, domSeq]

lemma AccDom_zero (α : ℝ) (h : ℝ → ℝ) (Cm : ℝ) :
    AccDom α h Cm 0 = fun _ => 0 := by
  funext x
  simp only [AccDom, domSeq]

lemma Dom_succ_eq (α : ℝ) (h : ℝ → ℝ) (Cm : ℝ) (k : ℕ) (x : ℝ) :
    Dom α h Cm (k + 1) x = 2 * HonGam α h (k + 1) x
      + 2 * (((k + 1 : ℕ) : ℝ)) * Cm ^ 2 * AccDom α h Cm (k + 1) x := by
  rw [Dom_succ]

lemma accDom_eq_sum (α : ℝ) (h : ℝ → ℝ) (Cm : ℝ) (l : ℕ) (x : ℝ) :
    AccDom α h Cm l x = ∑ m ∈ Finset.range l, Dom α h Cm m x := by
  induction l with
  | zero => rw [AccDom_zero]; simp
  | succ l ih =>
      rw [AccDom_succ]
      show AccDom α h Cm l x + Dom α h Cm l x = _
      rw [ih, Finset.sum_range_succ]

/-- Integrability of the dominating functions and of their partial sums. -/
lemma dom_integrable {α : ℝ} {h : ℝ → ℝ} {Cm : ℝ}
    (hEta : MeasureTheory.IntegrableOn (SubEta h) (Set.Ioo 0 xNear))
    (hGam : ∀ m ∈ Finset.Icc 1 4,
      MeasureTheory.IntegrableOn (HonGam α h m) (Set.Ioo 0 xNear)) :
    (∀ l ≤ 4, MeasureTheory.IntegrableOn (Dom α h Cm l) (Set.Ioo 0 xNear)) ∧
      (∀ l ≤ 4, MeasureTheory.IntegrableOn (AccDom α h Cm l) (Set.Ioo 0 xNear)) := by
  have key : ∀ l ≤ 4,
      MeasureTheory.IntegrableOn (Dom α h Cm l) (Set.Ioo 0 xNear) ∧
      MeasureTheory.IntegrableOn (AccDom α h Cm l) (Set.Ioo 0 xNear) ∧
      MeasureTheory.IntegrableOn (AccDom α h Cm (l + 1)) (Set.Ioo 0 xNear) := by
    intro l
    induction l with
    | zero =>
        intro _
        have h0 : MeasureTheory.IntegrableOn (Dom α h Cm 0) (Set.Ioo 0 xNear) := by
          rw [Dom_zero]; exact hEta
        have h1 : MeasureTheory.IntegrableOn (AccDom α h Cm 0) (Set.Ioo 0 xNear) := by
          rw [AccDom_zero]; exact MeasureTheory.integrableOn_zero
        have h2 : MeasureTheory.IntegrableOn (AccDom α h Cm (0 + 1)) (Set.Ioo 0 xNear) := by
          rw [AccDom_succ]
          exact h1.add h0
        exact ⟨h0, h1, h2⟩
    | succ l ih =>
        intro hl
        obtain ⟨hDl, hAl, hAl1⟩ := ih (by omega)
        have hG : MeasureTheory.IntegrableOn (HonGam α h (l + 1)) (Set.Ioo 0 xNear) :=
          hGam (l + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
        have hD : MeasureTheory.IntegrableOn (Dom α h Cm (l + 1)) (Set.Ioo 0 xNear) := by
          rw [Dom_succ]
          exact (hG.const_mul 2).add (hAl1.const_mul (2 * (((l + 1 : ℕ) : ℝ)) * Cm ^ 2))
        have hA : MeasureTheory.IntegrableOn (AccDom α h Cm (l + 1)) (Set.Ioo 0 xNear) := hAl1
        have hA2 : MeasureTheory.IntegrableOn (AccDom α h Cm (l + 2)) (Set.Ioo 0 xNear) := by
          rw [show l + 2 = (l + 1) + 1 from rfl, AccDom_succ]
          exact hA.add hD
        exact ⟨hD, hA, hA2⟩
  exact ⟨fun l hl => (key l hl).1, fun l hl => (key l hl).2.1⟩

end Work.FTS.H2.DivQ
