import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.H2.DivQ.Defs
import Submission.Work.FTS.H2.DivQ.aCoeff_expansion
import Submission.Work.FTS.H2.DivQ.aCoeff_bounds
import Submission.Work.FTS.H2.DivQ.DthIter_sliceX
import Submission.Work.FTS.H2.DivQ.aCoeff_diag
import Submission.Work.FTS.H2.DivQ.thetaOfSubst
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

/-! ## Elementary facts about the substitution `x = sin(2θ)` on the near region

We collect the one-variable calculus of `thetaOf x = arcsin x / 2`, `kappa x = cos(2·thetaOf x)`
and `xNear = sin(π/4) = 1/√2` needed by the inversion. -/

private lemma insv_xNear_sq : xNear ^ 2 = 1 / 2 := by
  rw [xNear, Real.sin_pi_div_four, div_pow, Real.sq_sqrt (by norm_num)]
  norm_num

/-- `κ x = √(1-x²)` for every real `x`. -/
private lemma kappa_eq (x : ℝ) : kappa x = Real.sqrt (1 - x ^ 2) := by
  simp only [kappa, thetaOf]
  rw [show 2 * (Real.arcsin x / 2) = Real.arcsin x by ring, Real.cos_arcsin]

/-- `sin (2 θ(x)) = x` for `x ∈ [-1,1]`. -/
private lemma sin_two_thetaOf {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    Real.sin (2 * thetaOf x) = x := by
  have h2 : 2 * thetaOf x = Real.arcsin x := by simp only [thetaOf]; ring
  rw [h2, Real.sin_arcsin hx.1 hx.2]

/-- On the near interval `(0,x₁)`, `θ(x)` lands in the angular interval `(0,π/2)`. -/
private lemma thetaOf_mem_Ioo {x : ℝ} (hx : x ∈ Set.Ioo 0 xNear) :
    thetaOf x ∈ Set.Ioo 0 (Real.pi / 2) := by
  have ha0 : 0 < Real.arcsin x := Real.arcsin_pos.mpr hx.1
  have ha2 : Real.arcsin x ≤ Real.pi / 2 := (Real.arcsin_mem_Icc x).2
  constructor <;> simp only [thetaOf] <;> linarith

private lemma thetaOf_xNear : thetaOf xNear = Real.pi / 8 := by
  rw [thetaOf, xNear, Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])]
  ring

private lemma thetaOf_zero : thetaOf 0 = 0 := by simp [thetaOf]

/-- `θ` is `C^∞` on the near region; its derivative there is the Jacobian `1/(2κ x)`. -/
private lemma hasDerivAt_thetaOf' {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt thetaOf (1 / (2 * kappa x)) x := by
  have h1 : HasDerivAt Real.arcsin (1 / Real.sqrt (1 - x ^ 2)) x :=
    Real.hasDerivAt_arcsin (ne_of_gt hx.1) (ne_of_lt hx.2)
  have h2 : HasDerivAt (fun y => Real.arcsin y / 2) ((1 / Real.sqrt (1 - x ^ 2)) / 2) x :=
    h1.div_const 2
  have hval : (1 / Real.sqrt (1 - x ^ 2)) / 2 = 1 / (2 * kappa x) := by
    rw [kappa_eq]; ring
  exact h2.congr_deriv hval

/-- `1/√2 ≤ κ x` on `[0,x₁]`. -/
private lemma kappa_ge {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) xNear) :
    1 / Real.sqrt 2 ≤ kappa x := by
  have hxnn : 0 ≤ x := hx.1
  have hxsq : x ^ 2 ≤ 1 / 2 := by
    have h1 : x * x ≤ xNear * xNear :=
      mul_le_mul hx.2 hx.2 hxnn (le_trans hxnn hx.2)
    have h2 : xNear * xNear = 1 / 2 := by simpa [pow_two] using insv_xNear_sq
    nlinarith [h1, h2]
  have hsqrt : Real.sqrt (1 / 2) ≤ Real.sqrt (1 - x ^ 2) := Real.sqrt_le_sqrt (by linarith)
  have h2 : Real.sqrt (1 / 2) = 1 / Real.sqrt 2 := by
    rw [Real.sqrt_div (by norm_num : (0:ℝ) ≤ 1) 2, Real.sqrt_one]
  rw [kappa_eq]
  linarith [hsqrt, h2]

/-- `1 ≤ 2 κ x` on `[0,x₁]`. -/
private lemma two_kappa_ge_one {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) xNear) :
    1 ≤ 2 * kappa x := by
  have h := kappa_ge hx
  have h2 : (2:ℝ) * (1 / Real.sqrt 2) = Real.sqrt 2 := by
    rw [mul_one_div, div_eq_iff (by positivity : (Real.sqrt 2) ≠ 0)]
    rw [← pow_two, Real.sq_sqrt (by norm_num)]
  have h3 : (1:ℝ) ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  linarith [h, h2, h3]

private lemma kappa_pos_of_Icc {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) xNear) : 0 < kappa x := by
  linarith [kappa_ge hx, one_div_pos.mpr (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2))]

/-- `sliceX h = h ∘ θ` is `C^∞` on the near interval whenever `h` is `C^∞` on `(0,π/2)`. -/
private lemma contDiffOn_sliceX {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ (⊤ : ℕ∞) (sliceX h) (Set.Ioo 0 xNear) := by
  have hθ : ContDiffOn ℝ (⊤ : ℕ∞) thetaOf (Set.Ioo 0 xNear) := by
    intro x hx
    have h1 : ContDiffAt ℝ (⊤ : ℕ∞) Real.arcsin x :=
      Real.contDiffAt_arcsin (by linarith [hx.1]) (by linarith [hx.2, xNear_lt])
    have h2 : ContDiffAt ℝ (⊤ : ℕ∞) thetaOf x := h1.div_const 2
    exact h2.contDiffWithinAt
  have hcomp : ContDiffOn ℝ (⊤ : ℕ∞) (sliceX h) (Set.Ioo 0 xNear) :=
    hsm.comp hθ (fun x hx => thetaOf_mem_Ioo hx)
  exact hcomp

/-- Every iterated `x`-derivative of `sliceX h` is `C^∞` on the near interval. -/
private lemma contDiffOn_iteratedDeriv_sliceX {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2))) (n : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (iteratedDeriv n (sliceX h)) (Set.Ioo 0 xNear) := by
  induction n with
  | zero => simpa using contDiffOn_sliceX hsm
  | succ n ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv_of_isOpen isOpen_Ioo (by simp)

/-- `Gop` is insensitive to replacing `u` by a function agreeing with it on an open set. -/
private lemma Gop_eqOn {u v : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s) (h : Set.EqOn u v s) :
    Set.EqOn (Gop u) (Gop v) s := by
  intro y hy
  have hd : deriv u y = deriv v y := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [hs.mem_nhds hy] with z hz
    exact h hz
  simp only [Gop, hd]

/-- Iterated version of `Gop_eqOn`. -/
private lemma Gop_iter_eqOn {u v : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s) (h : Set.EqOn u v s)
    (i : ℕ) : Set.EqOn ((Gop^[i]) u) ((Gop^[i]) v) s := by
  induction i with
  | zero => simpa using h
  | succ i ih =>
      intro y hy
      rw [Function.iterate_succ']
      exact Gop_eqOn hs ih hy

/-- **The `x`-expansion of the angular derivative `D_θ^i(∂_θ h)`.**  On the near region,
`Dth1Iter i (deriv h) (thetaOf x)` is the `aCoeff`-expansion of `G^i(2κ ∂_x(sliceX h))`, because
`sliceX (deriv h) = 2κ · ∂_x (sliceX h)` on `(0,x₁)`. -/
theorem Dth1Iter_deriv_expansion (i : ℕ) {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2))) {x : ℝ}
    (hx : x ∈ Set.Ioo 0 xNear) :
    Work.Elliptic.Dth1Iter i (deriv h) (thetaOf x)
      = ∑ l ∈ Finset.range (i + 1),
          aCoeff i l x * (x ^ l * iteratedDeriv (l + 1) (sliceX h) x) := by
  have hsm' : ContDiffOn ℝ (⊤ : ℕ∞) (deriv h) (Set.Ioo 0 (Real.pi / 2)) :=
    hsm.deriv_of_isOpen isOpen_Ioo (by simp)
  have hxI : x ∈ Set.Ioo (-1 : ℝ) 1 :=
    ⟨by linarith [hx.1], by linarith [hx.2, xNear_lt]⟩
  have hD : Work.Elliptic.Dth1Iter i (deriv h) (thetaOf x)
      = (Gop^[i] (sliceX (deriv h))) x := DthIter_sliceX i hsm' hx
  rw [hD]
  have heq : Set.EqOn (sliceX (deriv h))
      (fun y => 2 * kappa y * deriv (sliceX h) y) (Set.Ioo 0 xNear) := by
    intro y hy
    have hyI : y ∈ Set.Ioo (-1 : ℝ) 1 :=
      ⟨by linarith [hy.1], by linarith [hy.2, xNear_lt]⟩
    have hmem : thetaOf y ∈ Set.Ioo 0 (Real.pi / 2) := thetaOf_mem_Ioo hy
    have hdh : DifferentiableAt ℝ h (thetaOf y) :=
      ((hsm.contDiffAt (isOpen_Ioo.mem_nhds hmem)).differentiableAt (by simp))
    have hchain : HasDerivAt (sliceX h)
        (deriv h (thetaOf y) * (1 / (2 * kappa y))) y :=
      hdh.hasDerivAt.comp y (hasDerivAt_thetaOf' hyI)
    have hk0 : kappa y ≠ 0 := ne_of_gt (kappa_pos_of_mem ⟨le_of_lt hy.1, le_of_lt hy.2⟩)
    simp only [sliceX]
    rw [hchain.deriv]
    field_simp
  rw [Gop_iter_eqOn isOpen_Ioo heq i hx]
  exact aCoeff_expansion i (contDiffOn_sliceX hsm) hx

/-! ## The quantities of the inversion

`Denη = ∫_{Iθ}(∂_θh)²s^{-η}`, `Denγ m = ∫_{Iθ}(D_θ^m(∂_θh))²s^{-γ}`, the `x`-side quantities
`Wide l = x^{2l-γ}(∂_x^{l+1}(sliceX h))²`, and the pullbacks of the `θ`-integrands under
`x = sin(2θ)` (with the Jacobian `1/(2κ x)`).  All of these are `private`: they exist only to
structure the proof of `inversionNear`. -/

private def PsiEta (h : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))

private def PsiGam (α : ℝ) (h : ℝ → ℝ) (m : ℕ) : ℝ → ℝ :=
  fun θ => (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2
    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))

private def DenEta (h : ℝ → ℝ) : ℝ := ∫ θ in Work.Spaces.Iθ, PsiEta h θ

private def DenGam (α : ℝ) (h : ℝ → ℝ) (m : ℕ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, PsiGam α h m θ

/-- The right-hand side `Denη + Σ_{1 ≤ m ≤ j} Denγ m` of the inversion. -/
private def SS (α : ℝ) (h : ℝ → ℝ) (j : ℕ) : ℝ :=
  DenEta h + ∑ m ∈ Finset.Icc 1 j, DenGam α h m

/-- The integrand `x ↦ x^{2l-γ}(∂_x^{l+1}(sliceX h) x)²` of `B_l`. -/
private def Wide (α : ℝ) (h : ℝ → ℝ) (l : ℕ) : ℝ → ℝ :=
  fun x => x ^ (2 * (l : ℝ) - Work.Spaces.gam α)
    * (iteratedDeriv (l + 1) (sliceX h) x) ^ 2

/-- The `x`-pullback of `PsiEta`. -/
private def SubEta (h : ℝ → ℝ) : ℝ → ℝ :=
  fun x => PsiEta h (thetaOf x) * (1 / (2 * kappa x))

/-- The `x`-pullback of `PsiGam m`. -/
private def SubGam (α : ℝ) (h : ℝ → ℝ) (m : ℕ) : ℝ → ℝ :=
  fun x => PsiGam α h m (thetaOf x) * (1 / (2 * kappa x))

/-- The `x`-pullback of `PsiGam m` with `sin(2θ(x))` evaluated as `x`. -/
private def HonGam (α : ℝ) (h : ℝ → ℝ) (m : ℕ) : ℝ → ℝ :=
  fun x => (Work.Elliptic.Dth1Iter m (deriv h) (thetaOf x)) ^ 2
    * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))

/-- The full `j`-th expansion of `D_θ^j(∂_θh)(θ x)` and its off-diagonal part. -/
private def Expn (h : ℝ → ℝ) (j : ℕ) : ℝ → ℝ :=
  fun x => ∑ l ∈ Finset.range (j + 1),
    aCoeff j l x * (x ^ l * iteratedDeriv (l + 1) (sliceX h) x)

private def Restn (h : ℝ → ℝ) (j : ℕ) : ℝ → ℝ :=
  fun x => ∑ l ∈ Finset.range j,
    aCoeff j l x * (x ^ l * iteratedDeriv (l + 1) (sliceX h) x)

/-- `sin (2 θ(x)) = x` on the near interval. -/
private lemma sin_two_thetaOf_Ioo {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) xNear) :
    Real.sin (2 * thetaOf x) = x :=
  sin_two_thetaOf ⟨by linarith [hx.1], by linarith [hx.2, xNear_lt]⟩

private lemma gam_lt_four {α : ℝ} (hα : α ≤ 1) : Work.Spaces.gam α < 4 + Work.Spaces.eta := by
  unfold Work.Spaces.gam Work.Spaces.eta; linarith

private lemma psiEta_nonneg (h : ℝ → ℝ) :
    ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ PsiEta h θ := by
  intro θ hθ
  have hs : 0 ≤ Real.sin (2 * θ) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi <;>
      simp only [Work.Spaces.Iθ, Set.mem_Icc] at hθ <;> linarith
  exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs _)

private lemma psiGam_nonneg (α : ℝ) (h : ℝ → ℝ) (m : ℕ) :
    ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ PsiGam α h m θ := by
  intro θ hθ
  have hs : 0 ≤ Real.sin (2 * θ) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi <;>
      simp only [Work.Spaces.Iθ, Set.mem_Icc] at hθ <;> linarith
  exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs _)

/-- The chain rule for `sliceX h = h ∘ θ` on the near interval. -/
private lemma deriv_sliceX_eq {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2))) {x : ℝ}
    (hx : x ∈ Set.Ioo 0 xNear) :
    deriv (sliceX h) x = deriv h (thetaOf x) * (1 / (2 * kappa x)) := by
  have hyI : x ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2, xNear_lt]⟩
  have hmem : thetaOf x ∈ Set.Ioo 0 (Real.pi / 2) := thetaOf_mem_Ioo hx
  have hdh : DifferentiableAt ℝ h (thetaOf x) :=
    ((hsm.contDiffAt (isOpen_Ioo.mem_nhds hmem)).differentiableAt (by simp))
  exact (hdh.hasDerivAt.comp x (hasDerivAt_thetaOf' hyI)).deriv

/-- The `η`-instance of the substitution `x = sin(2θ)`. -/
private lemma subEta_data {h : ℝ → ℝ}
    (hint : MeasureTheory.IntegrableOn (PsiEta h) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (SubEta h) (Set.Ioo 0 xNear) ∧
      (∫ x in Set.Ioo (0 : ℝ) xNear, SubEta h x) ≤ DenEta h := by
  obtain ⟨h1, h2⟩ := thetaOfSubst (Ψ := PsiEta h) hint (psiEta_nonneg h)
  refine ⟨?_, ?_⟩
  · rw [← integrableOn_Ioc_iff_integrableOn_Ioo]; exact h1
  · rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le xNear_pos.le]
    exact h2

/-- The `γ`-instance of the substitution `x = sin(2θ)`, at angular order `m`. -/
private lemma subGam_data {α : ℝ} {h : ℝ → ℝ} {m : ℕ}
    (hint : MeasureTheory.IntegrableOn (PsiGam α h m) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (SubGam α h m) (Set.Ioo 0 xNear) ∧
      (∫ x in Set.Ioo (0 : ℝ) xNear, SubGam α h m x) ≤ DenGam α h m := by
  obtain ⟨h1, h2⟩ := thetaOfSubst (Ψ := PsiGam α h m) hint (psiGam_nonneg α h m)
  refine ⟨?_, ?_⟩
  · rw [← integrableOn_Ioc_iff_integrableOn_Ioo]; exact h1
  · rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le xNear_pos.le]
    exact h2

/-- The same, with `sin(2θ(x))` evaluated as `x`. -/
private lemma honGam_data {α : ℝ} {h : ℝ → ℝ} {m : ℕ}
    (hint : MeasureTheory.IntegrableOn (PsiGam α h m) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (HonGam α h m) (Set.Ioo 0 xNear) ∧
      (∫ x in Set.Ioo (0 : ℝ) xNear, HonGam α h m x) ≤ DenGam α h m := by
  obtain ⟨h1, h2⟩ := subGam_data hint
  have heq : Set.EqOn (SubGam α h m) (HonGam α h m) (Set.Ioo 0 xNear) := by
    intro x hx
    simp only [HonGam, SubGam, PsiGam, sin_two_thetaOf_Ioo hx]
  refine ⟨h1.congr_fun heq measurableSet_Ioo, ?_⟩
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioo heq] at h2
  exact h2

/-- The auxiliary `x^{-η}(∂_x(sliceX h))²` of the `l = 0` slot is dominated by `SubEta`. -/
private lemma etaPiece_le_subEta {h : ℝ → ℝ}
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

/-- The joint recursion producing the dominating functions `Dom` and their partial sums
`AccDom`. -/
private def domSeq (α : ℝ) (h : ℝ → ℝ) (Cm : ℝ) : ℕ → (ℝ → ℝ) × (ℝ → ℝ)
  | 0 => (SubEta h, fun _ => 0)
  | (l + 1) =>
      (fun x => 2 * HonGam α h (l + 1) x
          + 2 * (((l + 1 : ℕ) : ℝ)) * Cm ^ 2 * ((domSeq α h Cm l).2 x + (domSeq α h Cm l).1 x),
        fun x => (domSeq α h Cm l).2 x + (domSeq α h Cm l).1 x)

/-- An integrable dominating function for the level-`l` quantity. -/
private def Dom (α : ℝ) (h : ℝ → ℝ) (Cm : ℝ) (l : ℕ) : ℝ → ℝ := (domSeq α h Cm l).1

/-- The partial sum `Σ_{m < l} Dom m`. -/
private def AccDom (α : ℝ) (h : ℝ → ℝ) (Cm : ℝ) (l : ℕ) : ℝ → ℝ := (domSeq α h Cm l).2

private lemma AccDom_succ (α : ℝ) (h : ℝ → ℝ) (Cm : ℝ) (l : ℕ) :
    AccDom α h Cm (l + 1) = fun x => AccDom α h Cm l x + Dom α h Cm l x := by
  funext x
  simp only [AccDom, Dom, domSeq]

private lemma Dom_succ (α : ℝ) (h : ℝ → ℝ) (Cm : ℝ) (l : ℕ) :
    Dom α h Cm (l + 1) = fun x => 2 * HonGam α h (l + 1) x
        + 2 * (((l + 1 : ℕ) : ℝ)) * Cm ^ 2 * AccDom α h Cm (l + 1) x := by
  funext x
  simp only [AccDom, Dom, domSeq]

private lemma Dom_zero (α : ℝ) (h : ℝ → ℝ) (Cm : ℝ) :
    Dom α h Cm 0 = SubEta h := by
  funext x
  simp only [Dom, domSeq]

private lemma AccDom_zero (α : ℝ) (h : ℝ → ℝ) (Cm : ℝ) :
    AccDom α h Cm 0 = fun _ => 0 := by
  funext x
  simp only [AccDom, domSeq]

private lemma Dom_succ_eq (α : ℝ) (h : ℝ → ℝ) (Cm : ℝ) (k : ℕ) (x : ℝ) :
    Dom α h Cm (k + 1) x = 2 * HonGam α h (k + 1) x
      + 2 * (((k + 1 : ℕ) : ℝ)) * Cm ^ 2 * AccDom α h Cm (k + 1) x := by
  rw [Dom_succ]

private lemma accDom_eq_sum (α : ℝ) (h : ℝ → ℝ) (Cm : ℝ) (l : ℕ) (x : ℝ) :
    AccDom α h Cm l x = ∑ m ∈ Finset.range l, Dom α h Cm m x := by
  induction l with
  | zero => rw [AccDom_zero]; simp
  | succ l ih =>
      rw [AccDom_succ]
      show AccDom α h Cm l x + Dom α h Cm l x = _
      rw [ih, Finset.sum_range_succ]

private lemma Wide_nonneg (α : ℝ) (h : ℝ → ℝ) (l : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ Wide α h l x :=
  mul_nonneg (Real.rpow_nonneg hx _) (sq_nonneg _)

private lemma DenEta_nonneg {h : ℝ → ℝ} : 0 ≤ DenEta h := by
  rw [DenEta]
  exact MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ => psiEta_nonneg h θ hθ)

private lemma DenGam_nonneg {α : ℝ} {h : ℝ → ℝ} (m : ℕ) : 0 ≤ DenGam α h m := by
  rw [DenGam]
  exact MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ => psiGam_nonneg α h m θ hθ)

private lemma SS_nonneg (α : ℝ) (h : ℝ → ℝ) (l : ℕ) : 0 ≤ SS α h l :=
  add_nonneg DenEta_nonneg (Finset.sum_nonneg (fun m _ => DenGam_nonneg m))

private lemma SS_mono (α : ℝ) (h : ℝ → ℝ) {m l : ℕ} (hml : m ≤ l) :
    SS α h m ≤ SS α h l := by
  refine add_le_add le_rfl ?_
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro x hx
    simp only [Finset.mem_Icc] at hx ⊢
    exact ⟨hx.1, le_trans hx.2 hml⟩
  · intro x hx _
    exact DenGam_nonneg x

private lemma DenGam_le_SS (α : ℝ) (h : ℝ → ℝ) {l : ℕ} (hl : 1 ≤ l) :
    DenGam α h l ≤ SS α h l := by
  have hmem : l ∈ Finset.Icc 1 l := Finset.mem_Icc.mpr ⟨hl, le_rfl⟩
  have h := Finset.single_le_sum (f := fun m => DenGam α h m)
    (fun m _ => DenGam_nonneg m) hmem
  exact le_trans h (le_add_of_nonneg_left DenEta_nonneg)

private lemma DenEta_le_SS (α : ℝ) (h : ℝ → ℝ) (l : ℕ) : DenEta h ≤ SS α h l := by
  simp only [SS]
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun m _ => DenGam_nonneg m))

/-- Integrability of the dominating functions and of their partial sums. -/
private lemma dom_integrable {α : ℝ} {h : ℝ → ℝ} {Cm : ℝ}
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

/-- The Young inequality `A² ≤ 2(A+R)² + 2R²`. -/
private lemma young (A R : ℝ) : A ^ 2 ≤ 2 * (A + R) ^ 2 + 2 * R ^ 2 := by
  nlinarith [sq_nonneg (A + 2 * R)]

/-! ## The pointwise estimates -/

/-- `(x^m)² x^{c} = x^{2m+c}` for `x > 0`. -/
private lemma pow_sq_mul_rpow {x : ℝ} (hx : 0 < x) (m : ℕ) (c : ℝ) :
    (x ^ m) ^ 2 * x ^ c = x ^ (2 * (m : ℝ) + c) := by
  rw [← pow_mul, show m * 2 = 2 * m by ring, ← Real.rpow_natCast x (2 * m),
    show ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) by push_cast; ring, ← Real.rpow_add hx]

/-- **Diagonal domination.** -/
private lemma wide_le_diag {α : ℝ} {h : ℝ → ℝ} {j : ℕ} {x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) xNear) :
    Wide α h j x
      ≤ (aCoeff j j x * (x ^ j * iteratedDeriv (j + 1) (sliceX h) x)) ^ 2
          * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)) := by
  have hxpos : (0:ℝ) < x := hx.1
  have hk1 : (1:ℝ) ≤ 2 * kappa x := two_kappa_ge_one ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  have hk0 : (2 * kappa x) ≠ 0 := by positivity
  have hA : (2 * kappa x) ^ (2 * j + 2) * (1 / (2 * kappa x)) = (2 * kappa x) ^ (2 * j + 1) := by
    rw [show 2 * j + 2 = (2 * j + 1) + 1 by ring, pow_succ, one_div, mul_assoc,
      mul_inv_cancel₀ hk0, mul_one]
  have hB : (x ^ j) ^ 2 * x ^ (-(Work.Spaces.gam α))
      = x ^ (2 * (j : ℝ) - Work.Spaces.gam α) := by
    have h := pow_sq_mul_rpow hxpos j (-(Work.Spaces.gam α))
    rwa [show 2 * (j : ℝ) + (-(Work.Spaces.gam α)) = 2 * (j : ℝ) - Work.Spaces.gam α by ring]
      at h
  have key : ((2 * kappa x) ^ (j + 1) * (x ^ j * iteratedDeriv (j + 1) (sliceX h) x)) ^ 2
        * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))
      = (2 * kappa x) ^ (2 * j + 1)
        * (x ^ (2 * (j : ℝ) - Work.Spaces.gam α)
            * (iteratedDeriv (j + 1) (sliceX h) x) ^ 2) := by
    set g : ℝ := iteratedDeriv (j + 1) (sliceX h) x
    have h1 : ((2 * kappa x) ^ (j + 1)) ^ 2 = (2 * kappa x) ^ (2 * j + 2) := by
      rw [← pow_mul, show (j + 1) * 2 = 2 * j + 2 by ring]
    have h2 : (x ^ j * g) ^ 2 = (x ^ j) ^ 2 * g ^ 2 := mul_pow (x ^ j) g 2
    have h3 : ((2 * kappa x) ^ (j + 1) * (x ^ j * g)) ^ 2
        = ((2 * kappa x) ^ (j + 1)) ^ 2 * (x ^ j * g) ^ 2 :=
      mul_pow ((2 * kappa x) ^ (j + 1)) (x ^ j * g) 2
    have h4 : (2 * kappa x) ^ (2 * j + 2) * ((x ^ j) ^ 2 * g ^ 2)
          * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))
        = ((2 * kappa x) ^ (2 * j + 2) * (1 / (2 * kappa x)))
          * ((x ^ j) ^ 2 * x ^ (-(Work.Spaces.gam α))) * g ^ 2 := by ring
    rw [h3, h1, h2, h4, hA, hB]
    ring
  have hadiag : aCoeff j j x = (2 * kappa x) ^ (j + 1) := by rw [aCoeff_diag]
  rw [hadiag, key, Wide]
  have hnn : (0:ℝ) ≤ x ^ (2 * (j : ℝ) - Work.Spaces.gam α)
      * (iteratedDeriv (j + 1) (sliceX h) x) ^ 2 :=
    mul_nonneg (Real.rpow_nonneg hxpos.le _) (sq_nonneg _)
  have h2' : (1:ℝ) ≤ (2 * kappa x) ^ (2 * j + 1) := one_le_pow₀ hk1
  calc x ^ (2 * (j : ℝ) - Work.Spaces.gam α) * (iteratedDeriv (j + 1) (sliceX h) x) ^ 2
      = 1 * (x ^ (2 * (j : ℝ) - Work.Spaces.gam α)
          * (iteratedDeriv (j + 1) (sliceX h) x) ^ 2) := by ring
    _ ≤ (2 * kappa x) ^ (2 * j + 1)
          * (x ^ (2 * (j : ℝ) - Work.Spaces.gam α)
              * (iteratedDeriv (j + 1) (sliceX h) x) ^ 2) :=
        mul_le_mul_of_nonneg_right h2' hnn

/-- The `m ≥ 1` summand of `Restn`: the weight `x^{-γ}` combines with `x^{2m}` into `Wide m`. -/
private lemma rest_term_eq {α : ℝ} {h : ℝ → ℝ} {l m : ℕ} {x : ℝ} (hx : 0 < x) :
    (aCoeff l m x * (x ^ m * iteratedDeriv (m + 1) (sliceX h) x)) ^ 2
        * (x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)))
      = (aCoeff l m x) ^ 2 * Wide α h m x * (1 / (2 * kappa x)) := by
  have hB : (x ^ m) ^ 2 * x ^ (-(Work.Spaces.gam α))
      = x ^ (2 * (m : ℝ) - Work.Spaces.gam α) := by
    have h := pow_sq_mul_rpow hx m (-(Work.Spaces.gam α))
    rwa [show 2 * (m : ℝ) + (-(Work.Spaces.gam α)) = 2 * (m : ℝ) - Work.Spaces.gam α by ring]
      at h
  have h3 : (aCoeff l m x * (x ^ m * iteratedDeriv (m + 1) (sliceX h) x)) ^ 2
      = (aCoeff l m x) ^ 2
        * ((x ^ m) ^ 2 * (iteratedDeriv (m + 1) (sliceX h) x) ^ 2) := by
    rw [mul_pow (aCoeff l m x) (x ^ m * iteratedDeriv (m + 1) (sliceX h) x) 2,
      mul_pow (x ^ m) (iteratedDeriv (m + 1) (sliceX h) x) 2]
  rw [h3, Wide]
  set g : ℝ := iteratedDeriv (m + 1) (sliceX h) x
  rw [show (aCoeff l m x) ^ 2 * ((x ^ m) ^ 2 * g ^ 2)
        * (x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)))
      = (aCoeff l m x) ^ 2 * ((x ^ m) ^ 2 * x ^ (-(Work.Spaces.gam α)))
        * g ^ 2 * (1 / (2 * kappa x)) by ring]
  rw [hB]
  ring

/-- **The off-diagonal remainder.** -/
private lemma rest_le {α : ℝ} {h : ℝ → ℝ} {Cm : ℝ} (hCm : 0 ≤ Cm) (hα1 : α ≤ 1) {l : ℕ}
    (hl : 1 ≤ l)
    (hCb : ∀ m ≤ l, ∀ x ∈ Set.Icc (0:ℝ) xNear, |aCoeff l m x| ≤ Cm)
    (hC0 : ∀ x ∈ Set.Icc (0:ℝ) xNear, |aCoeff l 0 x| ≤ Cm * x ^ 2)
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2)))
    (hWle : ∀ m, 1 ≤ m → m < l → ∀ x ∈ Set.Ioo (0:ℝ) xNear, Wide α h m x ≤ Dom α h Cm m x)
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) xNear) :
    (Restn h l x) ^ 2 * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))
      ≤ ((l : ℝ)) * Cm ^ 2 * AccDom α h Cm l x := by
  have hxpos : (0:ℝ) < x := hx.1
  have hxIcc : x ∈ Set.Icc (0:ℝ) xNear := ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  have hxle1 : x ≤ 1 := by linarith [hx.2, xNear_lt]
  have hk1 : (1:ℝ) ≤ 2 * kappa x := two_kappa_ge_one hxIcc
  have hkpos : (0:ℝ) < 2 * kappa x := lt_of_lt_of_le one_pos hk1
  have hknn : (0:ℝ) ≤ 1 / (2 * kappa x) := by positivity
  have hlnn : (0:ℝ) ≤ (l : ℝ) := by positivity
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range l)
    (f := fun m => aCoeff l m x * (x ^ m * iteratedDeriv (m + 1) (sliceX h) x))
  have hCS : (∑ m ∈ Finset.range l,
        aCoeff l m x * (x ^ m * iteratedDeriv (m + 1) (sliceX h) x)) ^ 2
      ≤ ((l : ℝ)) * ∑ m ∈ Finset.range l,
          (aCoeff l m x * (x ^ m * iteratedDeriv (m + 1) (sliceX h) x)) ^ 2 := by
    simpa using hcs
  have hterm : ∀ m ∈ Finset.range l,
      (aCoeff l m x * (x ^ m * iteratedDeriv (m + 1) (sliceX h) x)) ^ 2
          * (x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)))
        ≤ Cm ^ 2 * Dom α h Cm m x := by
    intro m hm
    have hml : m ≤ l := by have := Finset.mem_range.mp hm; omega
    have hmlt : m < l := Finset.mem_range.mp hm
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0
      have hinv : 1 / (2 * kappa x) ≤ 1 := by rw [div_le_one hkpos]; linarith
      have h4η : x ^ (4 - Work.Spaces.gam α) ≤ x ^ (-(Work.Spaces.eta)) :=
        Real.rpow_le_rpow_of_exponent_ge hxpos hxle1 (by have := gam_lt_four hα1; linarith)
      have hsub : x ^ (-(Work.Spaces.eta)) * (deriv (sliceX h) x) ^ 2 ≤ SubEta h x :=
        etaPiece_le_subEta hsm hx
      have h1 : (aCoeff l 0 x) ^ 2 ≤ Cm ^ 2 * x ^ 4 := by
        have hle : |aCoeff l 0 x| ≤ Cm * x ^ 2 := hC0 x hxIcc
        rw [show (aCoeff l 0 x) ^ 2 = |aCoeff l 0 x| ^ 2 from (sq_abs _).symm]
        calc |aCoeff l 0 x| ^ 2 ≤ (Cm * x ^ 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hle 2
          _ = Cm ^ 2 * x ^ 4 := by ring
      have hx4 : x ^ 4 * x ^ (-(Work.Spaces.gam α)) = x ^ (4 - Work.Spaces.gam α) := by
        have hh := (Real.rpow_add hxpos (4:ℝ) (-(Work.Spaces.gam α))).symm
        rw [← Real.rpow_natCast x 4]
        exact hh.trans (congrArg (fun e => x ^ e)
          (by ring : (4:ℝ) + (-(Work.Spaces.gam α)) = 4 - Work.Spaces.gam α))
      have hkey : x ^ 4 * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))
          ≤ x ^ (-(Work.Spaces.eta)) := by
        calc x ^ 4 * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))
            = x ^ (4 - Work.Spaces.gam α) * (1 / (2 * kappa x)) := by rw [hx4]
          _ ≤ x ^ (4 - Work.Spaces.gam α) * 1 :=
              mul_le_mul_of_nonneg_left hinv (Real.rpow_nonneg hxpos.le _)
          _ = x ^ (4 - Work.Spaces.gam α) := by ring
          _ ≤ x ^ (-(Work.Spaces.eta)) := h4η
      simp only [pow_zero, one_mul, Nat.zero_add, iteratedDeriv_one]
      calc (aCoeff l 0 x * deriv (sliceX h) x) ^ 2
              * (x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)))
          = (aCoeff l 0 x) ^ 2 * (deriv (sliceX h) x) ^ 2
              * (x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))) := by ring
        _ ≤ (Cm ^ 2 * x ^ 4) * (deriv (sliceX h) x) ^ 2
              * (x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))) := by
            refine mul_le_mul_of_nonneg_right ?_ ?_
            · exact mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
            · exact mul_nonneg (Real.rpow_nonneg hxpos.le _) hknn
        _ = Cm ^ 2 * (deriv (sliceX h) x) ^ 2
              * (x ^ 4 * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))) := by ring
        _ ≤ Cm ^ 2 * (deriv (sliceX h) x) ^ 2 * x ^ (-(Work.Spaces.eta)) := by
            refine mul_le_mul_of_nonneg_left hkey (mul_nonneg (sq_nonneg Cm) (sq_nonneg _))
        _ ≤ Cm ^ 2 * SubEta h x := by
            have hh := mul_le_mul_of_nonneg_left hsub (sq_nonneg Cm)
            rw [show Cm ^ 2 * (deriv (sliceX h) x) ^ 2 * x ^ (-(Work.Spaces.eta))
              = Cm ^ 2 * (x ^ (-(Work.Spaces.eta)) * (deriv (sliceX h) x) ^ 2) by ring]
            exact hh
        _ = Cm ^ 2 * Dom α h Cm 0 x := by rw [Dom_zero]
    · have h1 : (aCoeff l m x) ^ 2 ≤ Cm ^ 2 := by
        have hle : |aCoeff l m x| ≤ Cm := hCb m hml x hxIcc
        rw [show (aCoeff l m x) ^ 2 = |aCoeff l m x| ^ 2 from (sq_abs _).symm]
        calc |aCoeff l m x| ^ 2 ≤ Cm ^ 2 := by
              simpa using pow_le_pow_left₀ (abs_nonneg _) hle 2
          _ = Cm ^ 2 := rfl
      have hinv : 1 / (2 * kappa x) ≤ 1 := by rw [div_le_one hkpos]; linarith
      rw [rest_term_eq (α := α) (h := h) (x := x) hxpos]
      calc (aCoeff l m x) ^ 2 * Wide α h m x * (1 / (2 * kappa x))
          ≤ Cm ^ 2 * Wide α h m x * 1 := by
            have hp : (0:ℝ) < 1 / (2 * kappa x) := div_pos one_pos hkpos
            exact mul_le_mul (mul_le_mul_of_nonneg_right h1 (Wide_nonneg α h m hxpos.le))
              hinv (le_of_lt hp) (mul_nonneg (sq_nonneg Cm) (Wide_nonneg α h m hxpos.le))
        _ ≤ Cm ^ 2 * Dom α h Cm m x := by
            have h3 := hWle m hmpos hmlt x hx
            nlinarith [h3, sq_nonneg Cm]
  have hstep1 : (Restn h l x) ^ 2 * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))
      ≤ ((l : ℝ)) * ∑ m ∈ Finset.range l,
          (aCoeff l m x * (x ^ m * iteratedDeriv (m + 1) (sliceX h) x)) ^ 2
            * (x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))) := by
    have hz : (0:ℝ) ≤ x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)) :=
      mul_nonneg (Real.rpow_nonneg hxpos.le _) hknn
    have h0 : (Restn h l x) ^ 2 * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))
        = (Restn h l x) ^ 2 * (x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))) := by
      ring
    have hS : Restn h l x = ∑ m ∈ Finset.range l,
        aCoeff l m x * (x ^ m * iteratedDeriv (m + 1) (sliceX h) x) := rfl
    rw [hS]
    rw [show (∑ m ∈ Finset.range l, aCoeff l m x * (x ^ m * iteratedDeriv (m + 1) (sliceX h) x)) ^ 2
          * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))
        = (∑ m ∈ Finset.range l, aCoeff l m x * (x ^ m * iteratedDeriv (m + 1) (sliceX h) x)) ^ 2
          * (x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))) by ring]
    refine (mul_le_mul_of_nonneg_right hCS hz).trans (le_of_eq ?_)
    rw [mul_assoc, Finset.sum_mul]
  calc (Restn h l x) ^ 2 * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))
      ≤ ((l : ℝ)) * ∑ m ∈ Finset.range l,
          (aCoeff l m x * (x ^ m * iteratedDeriv (m + 1) (sliceX h) x)) ^ 2
            * (x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))) := hstep1
    _ ≤ ((l : ℝ)) * ∑ m ∈ Finset.range l, Cm ^ 2 * Dom α h Cm m x :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) hlnn
    _ = ((l : ℝ)) * Cm ^ 2 * ∑ m ∈ Finset.range l, Dom α h Cm m x := by
        have h1 : ((l : ℝ)) * ∑ m ∈ Finset.range l, Cm ^ 2 * Dom α h Cm m x
            = ((l : ℝ)) * (Cm ^ 2 * ∑ m ∈ Finset.range l, Dom α h Cm m x) := by
          simp only [Finset.mul_sum]
        rw [show ((l : ℝ)) * Cm ^ 2 * ∑ m ∈ Finset.range l, Dom α h Cm m x
            = ((l : ℝ)) * (Cm ^ 2 * ∑ m ∈ Finset.range l, Dom α h Cm m x) by ring]
        exact h1
    _ = ((l : ℝ)) * Cm ^ 2 * AccDom α h Cm l x := by rw [accDom_eq_sum]

/-- The pointwise Young step at level `k+1`. -/
private lemma wide_le_dom_succ {α : ℝ} {h : ℝ → ℝ} {Cm : ℝ} {k : ℕ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2)))
    (hCm : 0 ≤ Cm) (hα1 : α ≤ 1) (hk : k + 1 ≤ 4)
    (hCb : ∀ m ≤ k + 1, ∀ x ∈ Set.Icc (0 : ℝ) xNear, |aCoeff (k + 1) m x| ≤ Cm)
    (hC0 : ∀ x ∈ Set.Icc (0 : ℝ) xNear, |aCoeff (k + 1) 0 x| ≤ Cm * x ^ 2)
    (hWle : ∀ m, 1 ≤ m → m ≤ k → ∀ x ∈ Set.Ioo (0 : ℝ) xNear,
      Wide α h m x ≤ Dom α h Cm m x)
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) xNear) :
    Wide α h (k + 1) x ≤ Dom α h Cm (k + 1) x := by
  have hxpos : (0 : ℝ) < x := hx.1
  have hkpos : (0 : ℝ) < 2 * kappa x :=
    lt_of_lt_of_le one_pos (two_kappa_ge_one ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
  have hknn : (0 : ℝ) ≤ x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)) :=
    mul_nonneg (Real.rpow_nonneg hxpos.le _) (le_of_lt (div_pos one_pos hkpos))
  set A : ℝ := aCoeff (k + 1) (k + 1) x
    * (x ^ (k + 1) * iteratedDeriv ((k + 1) + 1) (sliceX h) x) with hA
  set R : ℝ := Restn h (k + 1) x with hR
  have hExp : Work.Elliptic.Dth1Iter (k + 1) (deriv h) (thetaOf x) = Expn h (k + 1) x :=
    Dth1Iter_deriv_expansion (k + 1) hsm hx
  have hR' : (∑ l ∈ Finset.range (k + 1), aCoeff (k + 1) l x
      * (x ^ l * iteratedDeriv (l + 1) (sliceX h) x)) = R := by
    rw [hR]; rfl
  have hsplit : Expn h (k + 1) x = A + R := by
    have hE : Expn h (k + 1) x
        = (∑ l ∈ Finset.range (k + 1), aCoeff (k + 1) l x
            * (x ^ l * iteratedDeriv (l + 1) (sliceX h) x))
          + (aCoeff (k + 1) (k + 1) x
            * (x ^ (k + 1) * iteratedDeriv ((k + 1) + 1) (sliceX h) x)) := by
      simp only [Expn]
      rw [Finset.sum_range_succ]
    rw [hE, hR', ← hA, add_comm]
  have hHon : HonGam α h (k + 1) x
      = (A + R) ^ 2 * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)) := by
    simp only [HonGam]
    rw [← hsplit, ← hExp]
  have hdiag : Wide α h (k + 1) x
      ≤ A ^ 2 * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)) := by
    rw [hA]; exact wide_le_diag hx
  have hY2 : A ^ 2 * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))
      ≤ (2 * (A + R) ^ 2 + 2 * R ^ 2) * x ^ (-(Work.Spaces.gam α))
          * (1 / (2 * kappa x)) := by
    have := mul_le_mul_of_nonneg_right (young A R) hknn
    simpa only [mul_assoc] using this
  have h2 : (2 * (A + R) ^ 2 + 2 * R ^ 2) * x ^ (-(Work.Spaces.gam α))
        * (1 / (2 * kappa x))
      = 2 * HonGam α h (k + 1) x
        + 2 * (R ^ 2 * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))) := by
    rw [hHon]; ring
  have h3 : R ^ 2 * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))
      ≤ (((k + 1 : ℕ) : ℝ)) * Cm ^ 2 * AccDom α h Cm (k + 1) x := by
    rw [hR]
    exact rest_le (α := α) (h := h) (Cm := Cm) hCm hα1 (by omega) hCb hC0 hsm
      (fun m hm1 hmk => hWle m hm1 (by omega)) hx
  calc Wide α h (k + 1) x ≤ A ^ 2 * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)) := hdiag
    _ ≤ (2 * (A + R) ^ 2 + 2 * R ^ 2) * x ^ (-(Work.Spaces.gam α))
          * (1 / (2 * kappa x)) := hY2
    _ = 2 * HonGam α h (k + 1) x
          + 2 * (R ^ 2 * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))) := h2
    _ ≤ 2 * HonGam α h (k + 1) x
          + 2 * ((((k + 1 : ℕ) : ℝ)) * Cm ^ 2 * AccDom α h Cm (k + 1) x) := by
        linarith [h3]
    _ = Dom α h Cm (k + 1) x := by rw [Dom_succ_eq]; ring

/-- **Pointwise domination at every level `1 ≤ l ≤ 4`.** -/
private lemma wide_le_dom {α : ℝ} {h : ℝ → ℝ} {Cm : ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2)))
    (hα1 : α ≤ 1) (hCm : 0 ≤ Cm)
    (hCb : ∀ (n m : ℕ), 1 ≤ n → n ≤ 4 → m ≤ n →
      ∀ x ∈ Set.Icc (0 : ℝ) xNear, |aCoeff n m x| ≤ Cm)
    (hC0 : ∀ (n : ℕ), 1 ≤ n → n ≤ 4 →
      ∀ x ∈ Set.Icc (0 : ℝ) xNear, |aCoeff n 0 x| ≤ Cm * x ^ 2)
    {l : ℕ} (hl1 : 1 ≤ l) (hl4 : l ≤ 4) {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) xNear) :
    Wide α h l x ≤ Dom α h Cm l x := by
  have key : ∀ k ≤ 3, ∀ m, 1 ≤ m → m ≤ k + 1 → ∀ x ∈ Set.Ioo (0 : ℝ) xNear,
      Wide α h m x ≤ Dom α h Cm m x := by
    intro k hk
    induction k with
    | zero =>
        intro m hm1 hm2 x hx
        obtain rfl : m = 1 := by omega
        exact wide_le_dom_succ hsm hCm hα1 (by omega)
          (fun m hm x hx => hCb 1 m le_rfl (by norm_num) hm x hx)
          (fun x hx => hC0 1 le_rfl (by norm_num) x hx)
          (fun m hm1 hm2 => by omega) hx
    | succ k ih =>
        intro m hm1 hm2 x hx
        rcases Nat.lt_or_ge m (k + 2) with hlt | hge
        · exact ih (by omega) m hm1 (by omega) x hx
        · obtain rfl : m = k + 2 := by omega
          refine wide_le_dom_succ hsm hCm hα1 (by omega)
            (fun m hm x hx => hCb (k + 2) m (by omega) (by omega) hm x hx)
            (fun x hx => hC0 (k + 2) (by omega) (by omega) x hx) ?_ hx
          intro r hr1 hr2
          exact ih (by omega) r hr1 (by omega)
  obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
  exact key k (by omega) (k + 1) (by omega) le_rfl x hx

/-! ## The integral step -/

/-- **The integral step at level `k+1`.** -/
private lemma level_bound {α : ℝ} {h : ℝ → ℝ} {Cm T : ℝ} {k : ℕ}
    (hGamInt : MeasureTheory.IntegrableOn (HonGam α h (k + 1)) (Set.Ioo 0 xNear))
    (hAccInt : MeasureTheory.IntegrableOn (AccDom α h Cm (k + 1)) (Set.Ioo 0 xNear))
    (hGamBd : (∫ x in Set.Ioo (0 : ℝ) xNear, HonGam α h (k + 1) x) ≤ DenGam α h (k + 1))
    (hGamSS : DenGam α h (k + 1) ≤ SS α h (k + 1))
    (hAccBd : (∫ x in Set.Ioo (0 : ℝ) xNear, AccDom α h Cm (k + 1) x)
        ≤ T * SS α h (k + 1)) :
    (∫ x in Set.Ioo (0 : ℝ) xNear, Dom α h Cm (k + 1) x)
      ≤ (2 + 2 * (((k + 1 : ℕ) : ℝ)) * Cm ^ 2 * T) * SS α h (k + 1) := by
  have hI1 : MeasureTheory.IntegrableOn (fun x => 2 * HonGam α h (k + 1) x)
      (Set.Ioo 0 xNear) := hGamInt.const_mul 2
  have hI2 : MeasureTheory.IntegrableOn
      (fun x => (2 * (((k + 1 : ℕ) : ℝ)) * Cm ^ 2) * AccDom α h Cm (k + 1) x)
      (Set.Ioo 0 xNear) := hAccInt.const_mul _
  have hEq : (∫ x in Set.Ioo (0 : ℝ) xNear, Dom α h Cm (k + 1) x)
      = 2 * (∫ x in Set.Ioo (0 : ℝ) xNear, HonGam α h (k + 1) x)
        + (2 * (((k + 1 : ℕ) : ℝ)) * Cm ^ 2)
            * (∫ x in Set.Ioo (0 : ℝ) xNear, AccDom α h Cm (k + 1) x) := by
    simp only [Dom_succ_eq]
    rw [MeasureTheory.integral_add hI1 hI2,
      MeasureTheory.integral_const_mul 2 (fun x => HonGam α h (k + 1) x),
      MeasureTheory.integral_const_mul (2 * (((k + 1 : ℕ) : ℝ)) * Cm ^ 2)
        (fun x => AccDom α h Cm (k + 1) x)]
  rw [hEq]
  have hstep := mul_le_mul_of_nonneg_left hAccBd
    (by positivity : (0:ℝ) ≤ 2 * (((k + 1 : ℕ) : ℝ)) * Cm ^ 2)
  linarith [hGamBd, hGamSS, hstep]

/-- The accumulated constants of the level-by-level induction: `KT1` and `KK1 Cm` bound
`∫ AccDom 1` and `∫ Dom 1` by `KT1 · SS 1` and `KK1 Cm · SS 1`, and so on. -/
private def KT1 : ℝ := 1

private def KK1 (Cm : ℝ) : ℝ := 2 + 2 * 1 * Cm ^ 2 * KT1

private def KT2 (Cm : ℝ) : ℝ := KT1 + KK1 Cm

private def KK2 (Cm : ℝ) : ℝ := 2 + 2 * 2 * Cm ^ 2 * KT2 Cm

private def KT3 (Cm : ℝ) : ℝ := KT2 Cm + KK2 Cm

private def KK3 (Cm : ℝ) : ℝ := 2 + 2 * 3 * Cm ^ 2 * KT3 Cm

private def KT4 (Cm : ℝ) : ℝ := KT3 Cm + KK3 Cm

private def KK4 (Cm : ℝ) : ℝ := 2 + 2 * 4 * Cm ^ 2 * KT4 Cm

/-- The universal constant of `inversionNear`. -/
private def KC (Cm : ℝ) : ℝ := max 2 (max (KK1 Cm) (max (KK2 Cm) (max (KK3 Cm) (KK4 Cm))))

theorem inversionNear :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (h : ℝ → ℝ), 0 < α → α ≤ 1 →
      ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2)) →
      MeasureTheory.IntegrableOn
        (fun θ : ℝ => (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        Work.Spaces.Iθ →
      (∀ m : ℕ, m ∈ Finset.Icc 1 4 → MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ) →
      ∀ j : ℕ, j ∈ Finset.Icc 1 4 →
        (∫ x in (0 : ℝ)..xNear,
            x ^ (2 * (j : ℝ) - Work.Spaces.gam α)
              * (iteratedDeriv (j + 1) (sliceX h) x) ^ 2)
          ≤ C * ((∫ θ in Work.Spaces.Iθ,
                (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
              + ∑ m ∈ Finset.Icc 1 j, (∫ θ in Work.Spaces.Iθ,
                  (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2
                    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) := by
  obtain ⟨CG1, hCG1nn, hCG1⟩ := (aCoeff_bounds 1).2.1
  obtain ⟨CD1, hCD1nn, hCD1⟩ := (aCoeff_bounds 1).2.2 le_rfl
  obtain ⟨CG2, hCG2nn, hCG2⟩ := (aCoeff_bounds 2).2.1
  obtain ⟨CD2, hCD2nn, hCD2⟩ := (aCoeff_bounds 2).2.2 (by norm_num)
  obtain ⟨CG3, hCG3nn, hCG3⟩ := (aCoeff_bounds 3).2.1
  obtain ⟨CD3, hCD3nn, hCD3⟩ := (aCoeff_bounds 3).2.2 (by norm_num)
  obtain ⟨CG4, hCG4nn, hCG4⟩ := (aCoeff_bounds 4).2.1
  obtain ⟨CD4, hCD4nn, hCD4⟩ := (aCoeff_bounds 4).2.2 (by norm_num)
  have hCmnn : 0 ≤ CG1 + CD1 + CG2 + CD2 + CG3 + CD3 + CG4 + CD4 := by linarith
  refine ⟨KC (CG1 + CD1 + CG2 + CD2 + CG3 + CD3 + CG4 + CD4), ?_, ?_⟩
  · have h2 : (2:ℝ) ≤ KC (CG1 + CD1 + CG2 + CD2 + CG3 + CD3 + CG4 + CD4) := by
      simp only [KC]; exact le_max_left _ _
    linarith
  · intro α h hα0 hα1 hsm hDenEta hDenGam j hj
    obtain ⟨hj1, hj4⟩ := Finset.mem_Icc.mp hj
    set Cm : ℝ := CG1 + CD1 + CG2 + CD2 + CG3 + CD3 + CG4 + CD4 with hCm
    have hCmnn' : 0 ≤ Cm := by rw [hCm]; exact hCmnn
    have hB1 : CG1 ≤ Cm := by rw [hCm]; linarith
    have hB2 : CG2 ≤ Cm := by rw [hCm]; linarith
    have hB3 : CG3 ≤ Cm := by rw [hCm]; linarith
    have hB4 : CG4 ≤ Cm := by rw [hCm]; linarith
    have hD1 : CD1 ≤ Cm := by rw [hCm]; linarith
    have hD2 : CD2 ≤ Cm := by rw [hCm]; linarith
    have hD3 : CD3 ≤ Cm := by rw [hCm]; linarith
    have hD4 : CD4 ≤ Cm := by rw [hCm]; linarith
    have hCb : ∀ (n m : ℕ), 1 ≤ n → n ≤ 4 → m ≤ n →
        ∀ x ∈ Set.Icc (0 : ℝ) xNear, |aCoeff n m x| ≤ Cm := by
      intro n m hn1 hn4 hmn x hx
      interval_cases n
      · exact le_trans (hCG1 m hmn x hx) hB1
      · exact le_trans (hCG2 m hmn x hx) hB2
      · exact le_trans (hCG3 m hmn x hx) hB3
      · exact le_trans (hCG4 m hmn x hx) hB4
    have hC0 : ∀ (n : ℕ), 1 ≤ n → n ≤ 4 →
        ∀ x ∈ Set.Icc (0 : ℝ) xNear, |aCoeff n 0 x| ≤ Cm * x ^ 2 := by
      intro n hn1 hn4 x hx
      interval_cases n
      · exact le_trans (hCD1 x hx) (mul_le_mul_of_nonneg_right hD1 (sq_nonneg x))
      · exact le_trans (hCD2 x hx) (mul_le_mul_of_nonneg_right hD2 (sq_nonneg x))
      · exact le_trans (hCD3 x hx) (mul_le_mul_of_nonneg_right hD3 (sq_nonneg x))
      · exact le_trans (hCD4 x hx) (mul_le_mul_of_nonneg_right hD4 (sq_nonneg x))
    have hEtaInt : MeasureTheory.IntegrableOn (SubEta h) (Set.Ioo 0 xNear) :=
      (subEta_data hDenEta).1
    have hEtaBd : (∫ x in Set.Ioo (0 : ℝ) xNear, SubEta h x) ≤ DenEta h :=
      (subEta_data hDenEta).2
    have hGamInt : ∀ m, m ∈ Finset.Icc 1 4 →
        MeasureTheory.IntegrableOn (HonGam α h m) (Set.Ioo 0 xNear) :=
      fun m hm => (honGam_data (hDenGam m hm)).1
    have hGamBd : ∀ m, m ∈ Finset.Icc 1 4 →
        (∫ x in Set.Ioo (0 : ℝ) xNear, HonGam α h m x) ≤ DenGam α h m :=
      fun m hm => (honGam_data (hDenGam m hm)).2
    have hDomInt : ∀ l ≤ 4, MeasureTheory.IntegrableOn (Dom α h Cm l) (Set.Ioo 0 xNear) :=
      (dom_integrable hEtaInt hGamInt).1
    have hAccInt : ∀ l ≤ 4, MeasureTheory.IntegrableOn (AccDom α h Cm l) (Set.Ioo 0 xNear) :=
      (dom_integrable hEtaInt hGamInt).2
    have hEtaSS : ∀ l, DenEta h ≤ SS α h l := fun l => DenEta_le_SS α h l
    have hGamSS : ∀ l, 1 ≤ l → DenGam α h l ≤ SS α h l := fun l hl => DenGam_le_SS α h hl
    have hAccRec : ∀ l ≤ 3, (∫ x in Set.Ioo (0 : ℝ) xNear, AccDom α h Cm (l + 1) x)
        = (∫ x in Set.Ioo (0 : ℝ) xNear, AccDom α h Cm l x)
          + (∫ x in Set.Ioo (0 : ℝ) xNear, Dom α h Cm l x) := by
      intro l hl
      rw [AccDom_succ]
      exact MeasureTheory.integral_add (hAccInt l (by omega)) (hDomInt l (by omega))
    have hAcc1 : (∫ x in Set.Ioo (0 : ℝ) xNear, AccDom α h Cm 1 x) ≤ KT1 * SS α h 1 := by
      have h1 : (∫ x in Set.Ioo (0 : ℝ) xNear, AccDom α h Cm 1 x)
          = (∫ x in Set.Ioo (0 : ℝ) xNear, SubEta h x) := by
        rw [show (1:ℕ) = 0 + 1 from rfl, AccDom_succ, AccDom_zero, Dom_zero]
        simp only [Pi.add_apply, Pi.zero_apply, zero_add]
      rw [h1, KT1, one_mul]
      exact le_trans hEtaBd (hEtaSS 1)
    have hDom1 : (∫ x in Set.Ioo (0 : ℝ) xNear, Dom α h Cm 1 x) ≤ KK1 Cm * SS α h 1 := by
      have hb := level_bound (α := α) (h := h) (Cm := Cm) (T := KT1) (k := 0)
        (hGamInt 1 (Finset.mem_Icc.mpr ⟨le_rfl, by norm_num⟩))
        (hAccInt 1 (by norm_num))
        (hGamBd 1 (Finset.mem_Icc.mpr ⟨le_rfl, by norm_num⟩)) (hGamSS 1 le_rfl) hAcc1
      have hc : 2 + 2 * (((0 + 1 : ℕ) : ℝ)) * Cm ^ 2 * KT1 = KK1 Cm := by
        simp only [KK1, KT1]; norm_num
      rwa [hc] at hb
    have hK1pos : 0 < KK1 Cm := by simp only [KK1, KT1]; positivity
    have hT2pos : 0 < KT2 Cm := by simp only [KT2, KT1, KK1]; positivity
    have hK2pos : 0 < KK2 Cm := by simp only [KK2, KT2, KT1, KK1]; positivity
    have hT3pos : 0 < KT3 Cm := by simp only [KT3, KT2, KT1, KK1, KK2]; positivity
    have hK3pos : 0 < KK3 Cm := by simp only [KK3, KT3, KT2, KT1, KK1, KK2]; positivity
    have hAcc2 : (∫ x in Set.Ioo (0 : ℝ) xNear, AccDom α h Cm 2 x) ≤ KT2 Cm * SS α h 2 := by
      rw [show (2:ℕ) = 1 + 1 from rfl, hAccRec 1 (by norm_num), KT2]
      have h1 : (∫ x in Set.Ioo (0 : ℝ) xNear, AccDom α h Cm 1 x) ≤ KT1 * SS α h 2 :=
        le_trans hAcc1 (mul_le_mul_of_nonneg_left (SS_mono α h (by norm_num)) (by
          simp only [KT1]; norm_num))
      have h2 : (∫ x in Set.Ioo (0 : ℝ) xNear, Dom α h Cm 1 x) ≤ KK1 Cm * SS α h 2 :=
        le_trans hDom1 (mul_le_mul_of_nonneg_left (SS_mono α h (by norm_num)) (le_of_lt hK1pos))
      linarith
    have hDom2 : (∫ x in Set.Ioo (0 : ℝ) xNear, Dom α h Cm 2 x) ≤ KK2 Cm * SS α h 2 := by
      have hb := level_bound (α := α) (h := h) (Cm := Cm) (T := KT2 Cm) (k := 1)
        (hGamInt 2 (Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩))
        (hAccInt 2 (by norm_num))
        (hGamBd 2 (Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)) (hGamSS 2 (by norm_num)) hAcc2
      have hc : 2 + 2 * (((1 + 1 : ℕ) : ℝ)) * Cm ^ 2 * KT2 Cm = KK2 Cm := by
        simp only [KK2, KT2, KT1, KK1]; norm_num
      rwa [hc] at hb
    have hAcc3 : (∫ x in Set.Ioo (0 : ℝ) xNear, AccDom α h Cm 3 x) ≤ KT3 Cm * SS α h 3 := by
      rw [show (3:ℕ) = 2 + 1 from rfl, hAccRec 2 (by norm_num), KT3]
      have h1 : (∫ x in Set.Ioo (0 : ℝ) xNear, AccDom α h Cm 2 x) ≤ KT2 Cm * SS α h 3 :=
        le_trans hAcc2 (mul_le_mul_of_nonneg_left (SS_mono α h (by norm_num)) (le_of_lt hT2pos))
      have h2 : (∫ x in Set.Ioo (0 : ℝ) xNear, Dom α h Cm 2 x) ≤ KK2 Cm * SS α h 3 :=
        le_trans hDom2 (mul_le_mul_of_nonneg_left (SS_mono α h (by norm_num)) (le_of_lt hK2pos))
      linarith
    have hDom3 : (∫ x in Set.Ioo (0 : ℝ) xNear, Dom α h Cm 3 x) ≤ KK3 Cm * SS α h 3 := by
      have hb := level_bound (α := α) (h := h) (Cm := Cm) (T := KT3 Cm) (k := 2)
        (hGamInt 3 (Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩))
        (hAccInt 3 (by norm_num))
        (hGamBd 3 (Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)) (hGamSS 3 (by norm_num)) hAcc3
      have hc : 2 + 2 * (((2 + 1 : ℕ) : ℝ)) * Cm ^ 2 * KT3 Cm = KK3 Cm := by
        simp only [KK3, KT3, KT2, KT1, KK1, KK2]; norm_num
      rwa [hc] at hb
    have hAcc4 : (∫ x in Set.Ioo (0 : ℝ) xNear, AccDom α h Cm 4 x) ≤ KT4 Cm * SS α h 4 := by
      rw [show (4:ℕ) = 3 + 1 from rfl, hAccRec 3 (by norm_num), KT4]
      have h1 : (∫ x in Set.Ioo (0 : ℝ) xNear, AccDom α h Cm 3 x) ≤ KT3 Cm * SS α h 4 :=
        le_trans hAcc3 (mul_le_mul_of_nonneg_left (SS_mono α h (by norm_num)) (le_of_lt hT3pos))
      have h2 : (∫ x in Set.Ioo (0 : ℝ) xNear, Dom α h Cm 3 x) ≤ KK3 Cm * SS α h 4 :=
        le_trans hDom3 (mul_le_mul_of_nonneg_left (SS_mono α h (by norm_num)) (le_of_lt hK3pos))
      linarith
    have hDom4 : (∫ x in Set.Ioo (0 : ℝ) xNear, Dom α h Cm 4 x) ≤ KK4 Cm * SS α h 4 := by
      have hb := level_bound (α := α) (h := h) (Cm := Cm) (T := KT4 Cm) (k := 3)
        (hGamInt 4 (Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩))
        (hAccInt 4 (by norm_num))
        (hGamBd 4 (Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)) (hGamSS 4 (by norm_num)) hAcc4
      have hc : 2 + 2 * (((3 + 1 : ℕ) : ℝ)) * Cm ^ 2 * KT4 Cm = KK4 Cm := by
        simp only [KK4, KT4, KT3, KT2, KT1, KK1, KK2, KK3]; norm_num
      rwa [hc] at hb
    have hKK1le : KK1 Cm ≤ KC Cm := by
      rw [KC]
      have h1 : KK1 Cm
          ≤ max (KK1 Cm) (max (KK2 Cm) (max (KK3 Cm) (KK4 Cm))) := le_max_left _ _
      exact le_trans h1 (le_max_right _ _)
    have hKK2le : KK2 Cm ≤ KC Cm := by
      rw [KC]
      have h1 : KK2 Cm ≤ max (KK2 Cm) (max (KK3 Cm) (KK4 Cm)) := le_max_left _ _
      have h2 : max (KK2 Cm) (max (KK3 Cm) (KK4 Cm))
          ≤ max (KK1 Cm) (max (KK2 Cm) (max (KK3 Cm) (KK4 Cm))) := le_max_right _ _
      exact le_trans h1 (le_trans h2 (le_max_right _ _))
    have hKK3le : KK3 Cm ≤ KC Cm := by
      rw [KC]
      have h1 : KK3 Cm ≤ max (KK3 Cm) (KK4 Cm) := le_max_left _ _
      have h2 : max (KK3 Cm) (KK4 Cm) ≤ max (KK2 Cm) (max (KK3 Cm) (KK4 Cm)) := le_max_right _ _
      have h3 : max (KK2 Cm) (max (KK3 Cm) (KK4 Cm))
          ≤ max (KK1 Cm) (max (KK2 Cm) (max (KK3 Cm) (KK4 Cm))) := le_max_right _ _
      exact le_trans h1 (le_trans h2 (le_trans h3 (le_max_right _ _)))
    have hKK4le : KK4 Cm ≤ KC Cm := by
      simp only [KC]
      exact le_trans (le_max_right (KK3 Cm) (KK4 Cm))
        (le_trans (le_max_right (KK2 Cm) _) (le_trans (le_max_right (KK1 Cm) _) (le_max_right 2 _)))
    have hDomJ : (∫ x in Set.Ioo (0 : ℝ) xNear, Dom α h Cm j x) ≤ KC Cm * SS α h j := by
      have hcase : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
      rcases hcase with rfl | rfl | rfl | rfl
      · exact le_trans hDom1 (mul_le_mul_of_nonneg_right hKK1le (SS_nonneg α h 1))
      · exact le_trans hDom2 (mul_le_mul_of_nonneg_right hKK2le (SS_nonneg α h 2))
      · exact le_trans hDom3 (mul_le_mul_of_nonneg_right hKK3le (SS_nonneg α h 3))
      · exact le_trans hDom4 (mul_le_mul_of_nonneg_right hKK4le (SS_nonneg α h 4))
    have hWideJ : (∫ x in Set.Ioo (0 : ℝ) xNear, Wide α h j x) ≤ KC Cm * SS α h j := by
      have hle := le_trans
        (setIntegral_mono_of_nonneg (fun x hx => Wide_nonneg α h j (le_of_lt hx.1))
          (fun x hx => wide_le_dom hsm hα1 hCmnn' hCb hC0 hj1 hj4 hx) (hDomInt j hj4)) hDomJ
      exact hle
    rw [intervalIntegral.integral_of_le xNear_pos.le, MeasureTheory.integral_Ioc_eq_integral_Ioo]
    exact hWideJ

end Work.FTS.H2.DivQ
