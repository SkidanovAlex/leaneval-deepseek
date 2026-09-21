import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Existence.E1_E2_model
import Submission.Work.OddVolterra.Existence.exists_bound_comp_pair_sub_param
import Submission.Work.OddVolterra.Existence.E1_E2_diff_bounds
import Submission.Work.OddVolterra.Existence.xi_close_of_small
import Submission.Work.Analysis.Calculus.IteratedDeriv.contDiff_iteratedDeriv_param

/-!
# Derivative bounds for the odd inhomogeneity `E₁`

The target `Work.OddVolterra.Existence.E1_deriv_bounds` states that the difference
`E₁ n h - E₁ n 0` is `C δ`-small together with its first two derivatives on the slope window
`[7/10, 9/10]`, whenever `h` is `C^∞` with jets up to order `n+3` bounded by `δ` (and `δ` small).

The proof does not use the support hypothesis on `h`; it only uses that all derivatives of `h`
are globally bounded by `δ` (so in particular `|h| ≤ δ ≤ 1/100`).

## The idea

`E₁ n h v = ∫ t in (-x₀)..x₀, ∂^{n+1}_v (u ↦ mPhiF n (u, h u, t)) v` where `x₀ = profileX 1`
(`mE1_eq`), and the model radicand `mRad u y t = 1 - t² - (u t + y)²` is *strictly positive* on
the box `[-91/100, 91/100] × [-1/100, 1/100] × [-x₀, x₀]` (lemma `radEta_le_mRad`, with the
explicit threshold `radEta = 1/100`).  Consequently, on that box the smooth composite
`(u, t) ↦ mPhiF n (u, h u, t)` agrees with the composite of the *globally* smooth model
`PhiC n` obtained by clamping the radicand to stay above `radEta` (`radClamp`).

So the integrand `(u,t) ↦ ∂^{n+1}_u (mPhiF n (·, h ·, t)) u` may be replaced near the window by
a globally `C^∞` function, for which

* the parametric integral can be differentiated under the integral sign at every order
  (`Commons.Analysis.Calculus.iteratedDeriv_intervalIntegral_moving_endpoints` with constant
  endpoints: the boundary terms vanish), and
* the iterated derivatives of the graph composites are bounded by `C_i δ`
  (`exists_bound_comp_pair_sub_param`).

Everything is then integrated over `t ∈ (-x₀, x₀)`, giving the constant `2 x₀ C_i`.
-/

namespace Work.OddVolterra.Existence

set_option maxHeartbeats 2000000

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

open Commons.Geometry.Ulam
open Work.OddVolterra.DiffBounds

/-! ## The clamped model radicand -/

/-- The threshold above which the model radicand is left alone. -/
def radEta : ℝ := 1 / 100

lemma radEta_pos : 0 < radEta := by norm_num [radEta]

/-- The smooth clamp: the identity above the threshold `radEta`, and positive everywhere. -/
def radClamp (x : ℝ) : ℝ :=
  (1 - Real.smoothTransition (x / radEta)) * radEta + Real.smoothTransition (x / radEta) * x

lemma contDiff_radClamp : ContDiff ℝ (⊤ : ℕ∞) radClamp := by
  have h0 : ContDiff ℝ (⊤ : ℕ∞) fun x : ℝ => x / radEta := contDiff_id.div_const _
  have h1 : ContDiff ℝ (⊤ : ℕ∞) fun x : ℝ => Real.smoothTransition (x / radEta) :=
    Real.smoothTransition.contDiff.comp h0
  have h2 : ContDiff ℝ (⊤ : ℕ∞) fun x : ℝ => (1 - Real.smoothTransition (x / radEta)) * radEta :=
    ((contDiff_const.sub h1).mul contDiff_const)
  exact h2.add (h1.mul contDiff_id)

/-- Above the threshold, the clamp is the identity. -/
lemma radClamp_of_le {x : ℝ} (hx : radEta ≤ x) : radClamp x = x := by
  have h1 : (1 : ℝ) ≤ x / radEta := (one_le_div radEta_pos).mpr hx
  rw [radClamp, Real.smoothTransition.one_of_one_le h1]
  ring

/-- The clamp is positive everywhere. -/
lemma radClamp_pos (x : ℝ) : 0 < radClamp x := by
  by_cases hx : radEta ≤ x
  · rw [radClamp_of_le hx]
    exact lt_of_lt_of_le radEta_pos hx
  · have hlt : x / radEta < 1 := (div_lt_one radEta_pos).mpr (not_le.mp hx)
    have hφlt : Real.smoothTransition (x / radEta) < 1 := Real.smoothTransition.lt_one_of_lt_one hlt
    have hφnn : 0 ≤ Real.smoothTransition (x / radEta) := Real.smoothTransition.nonneg _
    by_cases hx0 : 0 ≤ x
    · have hthis : radClamp x = (1 - Real.smoothTransition (x / radEta)) * radEta
          + Real.smoothTransition (x / radEta) * x := rfl
      rw [hthis]
      nlinarith [hφlt, hφnn, radEta_pos, hx0]
    · have hz : Real.smoothTransition (x / radEta) = 0 :=
        Real.smoothTransition.zero_of_nonpos
          (div_nonpos_of_nonpos_of_nonneg (not_le.mp hx0).le radEta_pos.le)
      have hthis : radClamp x = (1 - Real.smoothTransition (x / radEta)) * radEta
          + Real.smoothTransition (x / radEta) * x := rfl
      rw [hthis, hz]
      linarith [radEta_pos]

/-- The globally smooth clamped model integrand of `E₁`. -/
def PhiC (n : ℕ) (p : ℝ × ℝ × ℝ) : ℝ :=
  radClamp (mRad p.1 p.2.1 p.2.2) ^ n * Real.sqrt (radClamp (mRad p.1 p.2.1 p.2.2))

lemma contDiff_PhiC (n : ℕ) : ContDiff ℝ ∞ (PhiC n) := by
  have hrad : ContDiff ℝ ∞ fun p : ℝ × ℝ × ℝ => radClamp (mRad p.1 p.2.1 p.2.2) :=
    contDiff_radClamp.comp mRad_contDiff
  exact (hrad.pow n).mul (hrad.sqrt (fun p => ne_of_gt (radClamp_pos _)))

/-- Above the threshold the clamped model agrees with the true model. -/
lemma PhiC_eq_mPhiF {n : ℕ} {u y t : ℝ} (h : radEta ≤ mRad u y t) :
    PhiC n (u, y, t) = mPhiF n (u, y, t) := by
  rw [PhiC, mPhiF, radClamp_of_le h]

/-! ## The parametrised clamped composites -/

/-- The clamped graph composite of `h`, as a function of the section parameter and the slope. -/
def PhiSlice (n : ℕ) (h : ℝ → ℝ) (t u : ℝ) : ℝ := PhiC n (u, h u, t)

/-- The `k`-th slope-derivative of the clamped graph composite, as a function of `(u, t)`. -/
def PhiParam (n : ℕ) (h : ℝ → ℝ) (k : ℕ) : ℝ × ℝ → ℝ :=
  fun p : ℝ × ℝ => iteratedDeriv k (PhiSlice n h p.2) p.1

/-- The difference of the two parametric families, `h` against the unperturbed profile. -/
def PhiParamDiff (n : ℕ) (h : ℝ → ℝ) (k : ℕ) : ℝ × ℝ → ℝ :=
  fun p : ℝ × ℝ => PhiParam n h k p - PhiParam n 0 k p

lemma PhiSlice_apply (n : ℕ) (h : ℝ → ℝ) (t u : ℝ) :
    PhiSlice n h t u = PhiC n (u, h u, t) := rfl

lemma PhiParam_apply (n : ℕ) (h : ℝ → ℝ) (k : ℕ) (p : ℝ × ℝ) :
    PhiParam n h k p = iteratedDeriv k (PhiSlice n h p.2) p.1 := rfl

/-- The `(n+1)`-st derivative of the graph composite is the parametrised family. -/
lemma iteratedDeriv_eq_PhiParam (n : ℕ) (h : ℝ → ℝ) (k : ℕ) (u t : ℝ) :
    iteratedDeriv k (fun x : ℝ => PhiC n (x, h x, t)) u = PhiParam n h k (u, t) := rfl

lemma iteratedDeriv_PhiSlice (n : ℕ) (h : ℝ → ℝ) (k : ℕ) (t u : ℝ) :
    iteratedDeriv k (PhiSlice n h t) u = PhiParam n h k (u, t) := rfl

/-! ## Calculus tools: constant endpoints, iterations, linearity -/

/-- With constant endpoints the boundary terms of the moving-endpoint Leibniz formula vanish. -/
lemma boundaryTerm_const_eq_zero (F : ℝ → ℝ → ℝ) (a b : ℝ) (k : ℕ) :
    Commons.Analysis.Calculus.boundaryTerm F (fun _ : ℝ => a) (fun _ : ℝ => b) k = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext s
    rw [Commons.Analysis.Calculus.boundaryTerm]
    rw [ih]
    simp [deriv_const]

/-- Differentiation under the integral sign, all orders, for a globally smooth integrand. -/
lemma iteratedDeriv_integral_fixed {j : ℕ} {F : ℝ → ℝ → ℝ} {a b x : ℝ}
    (hF : ContDiff ℝ ∞ (fun p : ℝ × ℝ => F p.1 p.2)) :
    iteratedDeriv j (fun u : ℝ => ∫ t in a..b, F u t) x
      = ∫ t in a..b, iteratedDeriv j (fun u : ℝ => F u t) x := by
  have hFj : ContDiff ℝ (((j : ℕ) : ℕ∞ω)) (fun p : ℝ × ℝ => F p.1 p.2) :=
    hF.of_le (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
  have h := Commons.Analysis.Calculus.iteratedDeriv_intervalIntegral_moving_endpoints
    (k := j) (F := F) (a := fun _ : ℝ => a) (b := fun _ : ℝ => b) (s := x)
    hFj contDiff_const contDiff_const
  rw [h, boundaryTerm_const_eq_zero]
  simp

/-- The `j`-th derivative of the `K`-th derivative is the `(j+K)`-th derivative. -/
lemma iteratedDeriv_iteratedDeriv (j K : ℕ) (f : ℝ → ℝ) :
    iteratedDeriv j (fun x : ℝ => iteratedDeriv K f x) = iteratedDeriv (j + K) f := by
  have h1 : (fun x : ℝ => iteratedDeriv K f x) = deriv^[K] f := by
    rw [iteratedDeriv_eq_iterate]
  have h2 : iteratedDeriv (j + K) f = deriv^[j + K] f := iteratedDeriv_eq_iterate
  rw [iteratedDeriv_eq_iterate, h1, h2]
  funext x
  rw [Function.iterate_add_apply]

/-- Sub-linearity of `iteratedDeriv` for globally smooth functions. -/
lemma iteratedDeriv_sub_of_contDiffAt (j : ℕ) {f g : ℝ → ℝ} {x : ℝ}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) :
    iteratedDeriv j (f - g) x = iteratedDeriv j f x - iteratedDeriv j g x :=
  iteratedDeriv_sub (hf.of_le (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤)))
    (hg.of_le (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤)))

/-- Slices of a jointly smooth function are smooth. -/
lemma contDiffAt_slice_of_contDiff {G : ℝ × ℝ → ℝ} (hG : ContDiff ℝ ∞ G) (u t : ℝ) :
    ContDiffAt ℝ ∞ (fun x : ℝ => G (x, t)) u := by
  have h1 : ContDiffAt ℝ ∞ (fun x : ℝ => (x, t)) u :=
    contDiffAt_id.prodMk contDiffAt_const
  exact hG.contDiffAt.fun_comp u h1

/-! ## A quantitative positivity bound for the model radicand -/

/-- On the enlarged box `[-91/100, 91/100] × [-1/100, 1/100] × [-x₀, x₀]` the model radicand is
at least `radEta = 1/100`. -/
lemma radEta_le_mRad {u y t : ℝ} (hu : |u| ≤ 91 / 100) (hy : |y| ≤ 1 / 100)
    (ht : |t| ≤ profileX 1) : radEta ≤ mRad u y t := by
  have hp : profileX 1 ^ 2 = 1 / 2 := profileX_one_sq'
  have hp0 : 0 < profileX 1 := profileX_one_pos'
  have hp1 : profileX 1 < 1 := profileX_one_lt_one
  have h1 : |u * t + y| ≤ (91 / 100) * profileX 1 + 1 / 100 := by
    calc |u * t + y| ≤ |u * t| + |y| := abs_add_le _ _
      _ = |u| * |t| + |y| := by rw [abs_mul]
      _ ≤ (91 / 100) * profileX 1 + 1 / 100 := by
          have h := mul_le_mul hu ht (abs_nonneg t) (by norm_num : (0 : ℝ) ≤ 91 / 100)
          linarith
  have ht2 : t ^ 2 ≤ profileX 1 ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg t) ht 2
    rwa [sq_abs] at h
  have h2 : (u * t + y) ^ 2 ≤ ((91 / 100) * profileX 1 + 1 / 100) ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg (u * t + y)) h1 2
    rwa [sq_abs] at h
  have hkey : ((91 / 100) * profileX 1 + 1 / 100) ^ 2 ≤ 49 / 100 := by
    nlinarith [hp, hp1, hp0]
  rw [radEta, mRad]
  nlinarith [hp, ht2, h2, hkey]

/-! ## Smoothness and integrability of the clamped graph composites -/

/-- The clamped graph composite is smooth. -/
lemma contDiff_PhiSlice (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (t : ℝ) :
    ContDiff ℝ ∞ (PhiSlice n h t) := by
  have hcurve : ContDiff ℝ ∞ fun u : ℝ => (u, h u, t) := by fun_prop
  exact (contDiff_PhiC n).comp hcurve

/-- The parametric family of `k`-th derivatives of the clamped graph composite is smooth. -/
lemma contDiff_PhiParam (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (k : ℕ) :
    ContDiff ℝ ∞ (PhiParam n h k) := by
  have hU : ContDiff ℝ ∞ fun p : ℝ × ℝ => PhiC n (p.1, h p.1, p.2) := by
    have hcurve : ContDiff ℝ ∞ fun p : ℝ × ℝ => (p.1, h p.1, p.2) := by fun_prop
    exact (contDiff_PhiC n).comp hcurve
  have hstep := Commons.Analysis.Calculus.contDiff_iteratedDeriv_param (E := ℝ) k hU
  have hfun : (fun p : ℝ × ℝ => iteratedDeriv k (fun x : ℝ => PhiC n (x, h x, p.2)) p.1)
      = PhiParam n h k := rfl
  rwa [hfun] at hstep

/-- Interval integrability of the clamped graph composite in the section parameter. -/
lemma intervalIntegrable_PhiParam (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (k : ℕ) (u : ℝ) :
    IntervalIntegrable (fun t : ℝ => PhiParam n h k (u, t)) volume
      (-(profileX 1)) (profileX 1) := by
  have hcont : Continuous fun t : ℝ => PhiParam n h k (u, t) :=
    (contDiff_PhiParam n hh k).continuous.comp (continuous_const.prodMk continuous_id)
  exact hcont.intervalIntegrable _ _

/-- The `j`-th derivative of the slice of `PhiParam` is the `(j+k)`-th derivative slice. -/
lemma iteratedDeriv_slice_PhiParam (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (k j : ℕ) (t u : ℝ) :
    iteratedDeriv j (fun x : ℝ => PhiParam n h k (x, t)) u
      = iteratedDeriv (j + k) (PhiSlice n h t) u := by
  have h2 : (fun x : ℝ => PhiParam n h k (x, t))
      = fun x : ℝ => iteratedDeriv k (PhiSlice n h t) x := by
    funext x
    rw [PhiParam_apply]
  rw [h2, iteratedDeriv_iteratedDeriv]

/-- The `j`-th derivative of the difference family, in terms of the two parametric families. -/
lemma iteratedDeriv_PhiParamDiff (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (k j : ℕ) (t x : ℝ) :
    iteratedDeriv j (fun u : ℝ => PhiParamDiff n h k (u, t)) x
      = PhiParam n h (j + k) (x, t) - PhiParam n 0 (j + k) (x, t) := by
  have hfe : (fun u : ℝ => PhiParamDiff n h k (u, t))
      = (fun u : ℝ => PhiParam n h k (u, t))
        - (fun u : ℝ => PhiParam n 0 k (u, t)) := by
    funext u
    rfl
  have h0cd : ContDiff ℝ (⊤ : ℕ∞) (0 : ℝ → ℝ) := contDiff_const
  have hA : ContDiff ℝ ∞ (PhiParam n h k) := contDiff_PhiParam n hh k
  have hB : ContDiff ℝ ∞ (PhiParam n 0 k) := contDiff_PhiParam n h0cd k
  rw [hfe, iteratedDeriv_sub_of_contDiffAt j
      (contDiffAt_slice_of_contDiff hA x t) (contDiffAt_slice_of_contDiff hB x t),
    iteratedDeriv_slice_PhiParam n hh k j t x,
    iteratedDeriv_slice_PhiParam n h0cd k j t x,
    iteratedDeriv_PhiSlice n h (j + k) t x,
    iteratedDeriv_PhiSlice n (0 : ℝ → ℝ) (j + k) t x]

/-! ## `E₁` as an integral of the clamped graph composite on the window -/

/-- On the enlarged window `(69/100, 91/100)` the inhomogeneity `E₁ n h` is the parametric
integral of the *clamped* graph composite. -/
lemma E1_eq_integral_PhiParam (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hb : ∀ u : ℝ, |h u| ≤ 1 / 100) {u : ℝ} (hu : u ∈ Set.Ioo (69 / 100 : ℝ) (91 / 100)) :
    E1 n h u = ∫ t in (-(profileX 1))..(profileX 1), PhiParam n h (n + 1) (u, t) := by
  rw [mE1_eq n h u]
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  have ht' : |t| ≤ profileX 1 := by
    rw [Set.uIcc_of_le (by linarith [profileX_one_pos'])] at ht
    rw [abs_le]
    exact ⟨by linarith [ht.1], ht.2⟩
  have hev : (fun x : ℝ => mPhiF n (x, h x, t)) =ᶠ[𝓝 u] (fun x : ℝ => PhiC n (x, h x, t)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hu] with x hx
    have hxabs : |x| ≤ 91 / 100 := by
      rw [abs_le]
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    exact (PhiC_eq_mPhiF (radEta_le_mRad hxabs (hb x) ht')).symm
  have h1 : iteratedDeriv (n + 1) (fun x : ℝ => mPhiF n (x, h x, t)) u
      = iteratedDeriv (n + 1) (fun x : ℝ => PhiC n (x, h x, t)) u :=
    (hev.iteratedDeriv (n + 1)).eq_of_nhds
  rw [h1]
  exact iteratedDeriv_eq_PhiParam n h (n + 1) u t

/-! ## The main step: bounding the `j`-th derivative of `E₁ n h - E₁ n 0` -/

/-- If the two parametric families differ by at most `C δ` at order `j+n+1` on the box, then
the `j`-th derivative of `E₁ n h - E₁ n 0` is bounded by `2 x₀ (C δ)` on the window. -/
lemma E1_deriv_step (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hb : ∀ u : ℝ, |h u| ≤ 1 / 100) {δ C : ℝ} (hδnn : 0 ≤ δ) (hCnn : 0 ≤ C)
    (j i : ℕ) (hji : i = j + (n + 1))
    (hpt : ∀ t ∈ Set.Icc (-(profileX 1)) (profileX 1),
      ∀ x ∈ Set.Icc (7 / 10 : ℝ) (9 / 10),
        |PhiParam n h i (x, t) - PhiParam n 0 i (x, t)| ≤ C * δ)
    {v : ℝ} (hv : v ∈ Set.Icc (7 / 10 : ℝ) (9 / 10)) :
    |iteratedDeriv j (fun u : ℝ => E1 n h u - E1 n 0 u) v| ≤ (2 * profileX 1) * (C * δ) := by
  rw [hji] at hpt
  have hab : -(profileX 1) ≤ profileX 1 := by linarith [profileX_one_pos']
  have h0cd : ContDiff ℝ (⊤ : ℕ∞) (0 : ℝ → ℝ) := contDiff_const
  have hA : ContDiff ℝ ∞ (PhiParam n h (n + 1)) := contDiff_PhiParam n hh (n + 1)
  have hB : ContDiff ℝ ∞ (PhiParam n 0 (n + 1)) := contDiff_PhiParam n h0cd (n + 1)
  have hD : ContDiff ℝ ∞ (fun p : ℝ × ℝ => PhiParamDiff n h (n + 1) (p.1, p.2)) := by
    have h : PhiParamDiff n h (n + 1) = PhiParam n h (n + 1) - PhiParam n 0 (n + 1) := rfl
    rw [h]
    exact hA.sub hB
  -- differentiate the parametric integral under the integral sign
  have hswap : iteratedDeriv j
        (fun u : ℝ => ∫ t in (-(profileX 1))..(profileX 1),
          PhiParamDiff n h (n + 1) (u, t)) v
      = ∫ t in (-(profileX 1))..(profileX 1),
          iteratedDeriv j (fun u : ℝ => PhiParamDiff n h (n + 1) (u, t)) v :=
    iteratedDeriv_integral_fixed hD
  -- `E₁ n h - E₁ n 0` agrees with the parametric integral near `v`
  have htransfer : (fun u : ℝ => E1 n h u - E1 n 0 u)
      =ᶠ[𝓝 v] (fun u : ℝ => ∫ t in (-(profileX 1))..(profileX 1),
        PhiParamDiff n h (n + 1) (u, t)) := by
    have hvI : v ∈ Set.Ioo (69 / 100 : ℝ) (91 / 100) :=
      ⟨by linarith [hv.1], by linarith [hv.2]⟩
    filter_upwards [isOpen_Ioo.mem_nhds hvI] with u hu
    have h1 := E1_eq_integral_PhiParam n hh hb hu
    have h2 : E1 n (0 : ℝ → ℝ) u
        = ∫ t in (-(profileX 1))..(profileX 1), PhiParam n (0 : ℝ → ℝ) (n + 1) (u, t) :=
      E1_eq_integral_PhiParam n h0cd (fun u => by
        simp only [Pi.zero_apply, abs_zero]; norm_num) hu
    have hi1 := intervalIntegrable_PhiParam n hh (n + 1) u
    have hi2 := intervalIntegrable_PhiParam n h0cd (n + 1) u
    rw [h1, h2, ← intervalIntegral.integral_sub hi1 hi2]
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rfl
  have hfin : iteratedDeriv j (fun u : ℝ => E1 n h u - E1 n 0 u) v
      = iteratedDeriv j (fun u : ℝ => ∫ t in (-(profileX 1))..(profileX 1),
          PhiParamDiff n h (n + 1) (u, t)) v :=
    (htransfer.iteratedDeriv j).eq_of_nhds
  rw [hfin, hswap]
  -- the integrand is the difference of the two parametric families
  have hcongr : (fun t : ℝ => iteratedDeriv j
        (fun u : ℝ => PhiParamDiff n h (n + 1) (u, t)) v)
      = fun t : ℝ => PhiParam n h (j + (n + 1)) (v, t)
          - PhiParam n 0 (j + (n + 1)) (v, t) := by
    funext t
    exact iteratedDeriv_PhiParamDiff n hh (n + 1) j t v
  rw [hcongr]
  have hintA := intervalIntegrable_PhiParam n hh (j + (n + 1)) v
  have hintB := intervalIntegrable_PhiParam n h0cd (j + (n + 1)) v
  have hint : IntervalIntegrable (fun t : ℝ =>
      |PhiParam n h (j + (n + 1)) (v, t) - PhiParam n 0 (j + (n + 1)) (v, t)|)
      volume (-(profileX 1)) (profileX 1) := (hintA.sub hintB).abs
  calc |∫ t in (-(profileX 1))..(profileX 1),
        (PhiParam n h (j + (n + 1)) (v, t) - PhiParam n 0 (j + (n + 1)) (v, t))|
      ≤ ∫ t in (-(profileX 1))..(profileX 1),
          |PhiParam n h (j + (n + 1)) (v, t) - PhiParam n 0 (j + (n + 1)) (v, t)| :=
        intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ t in (-(profileX 1))..(profileX 1), C * δ :=
        intervalIntegral.integral_mono_on hab hint intervalIntegrable_const
          (fun t ht => hpt t ht v hv)
    _ = (2 * profileX 1) * (C * δ) := by
        rw [intervalIntegral.integral_const]
        ring

/-! ## The target theorem -/

theorem E1_deriv_bounds (n : ℕ) (hn : 1 ≤ n) :
    ∃ C δ₀ : ℝ, 0 < C ∧ 0 < δ₀ ∧ δ₀ ≤ 1 / 100 ∧
      ∀ (h : ℝ → ℝ) (δ : ℝ), ContDiff ℝ (⊤ : ℕ∞) h → 0 < δ → δ ≤ δ₀ →
      Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) →
      (∀ k : ℕ, k ≤ n + 3 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      ∀ j ≤ 2, ∀ v ∈ Set.Icc (7 / 10 : ℝ) (9 / 10 : ℝ),
        |iteratedDeriv j (fun u : ℝ => Work.OddVolterra.E1 n h u - Work.OddVolterra.E1 n 0 u) v|
          ≤ C * δ := by
  obtain ⟨C₁, hC₁nn, hC₁⟩ := exists_bound_comp_pair_sub_param (i := n + 1) (Φ := PhiC n)
    (c := 7 / 10) (d := 9 / 10) (R := 1 / 100) (p := profileX 1) (U := Set.univ)
    isOpen_univ (Set.subset_univ _) (contDiff_PhiC n).contDiffOn (by norm_num) (by norm_num)
    (le_of_lt profileX_one_pos')
  obtain ⟨C₂, hC₂nn, hC₂⟩ := exists_bound_comp_pair_sub_param (i := n + 2) (Φ := PhiC n)
    (c := 7 / 10) (d := 9 / 10) (R := 1 / 100) (p := profileX 1) (U := Set.univ)
    isOpen_univ (Set.subset_univ _) (contDiff_PhiC n).contDiffOn (by norm_num) (by norm_num)
    (le_of_lt profileX_one_pos')
  obtain ⟨C₃, hC₃nn, hC₃⟩ := exists_bound_comp_pair_sub_param (i := n + 3) (Φ := PhiC n)
    (c := 7 / 10) (d := 9 / 10) (R := 1 / 100) (p := profileX 1) (U := Set.univ)
    isOpen_univ (Set.subset_univ _) (contDiff_PhiC n).contDiffOn (by norm_num) (by norm_num)
    (le_of_lt profileX_one_pos')
  refine ⟨(C₁ + C₂ + C₃ + 1) * (2 * profileX 1 + 1), 1 / 100, ?_, by norm_num, le_rfl, ?_⟩
  · have hp := profileX_one_pos'
    nlinarith [hC₁nn, hC₂nn, hC₃nn]
  · intro h δ hh hδpos hδδ₀ hsupp hjet j hj v hv
    have hδle : δ ≤ 1 / 100 := hδδ₀
    have hδ1 : δ ≤ 1 := by linarith
    have hδnn : 0 ≤ δ := le_of_lt hδpos
    have hhd : ∀ u : ℝ, |h u| ≤ 1 / 100 := fun u =>
      le_trans (hjet 0 (Nat.zero_le _) u) hδle
    have hpt1 : ∀ t ∈ Set.Icc (-(profileX 1)) (profileX 1),
        ∀ x ∈ Set.Icc (7 / 10 : ℝ) (9 / 10),
          |PhiParam n h (n + 1) (x, t) - PhiParam n 0 (n + 1) (x, t)| ≤ C₁ * δ := by
      intro t ht x hx
      have h1 := hC₁ h δ hδnn hδ1 hδle hh
        (fun k hk u _ => hjet k (le_trans hk (by omega)) u) x hx t ht
      rw [← iteratedDeriv_eq_PhiParam n h (n + 1) x t,
        ← iteratedDeriv_eq_PhiParam n 0 (n + 1) x t]
      exact h1
    have hpt2 : ∀ t ∈ Set.Icc (-(profileX 1)) (profileX 1),
        ∀ x ∈ Set.Icc (7 / 10 : ℝ) (9 / 10),
          |PhiParam n h (n + 2) (x, t) - PhiParam n 0 (n + 2) (x, t)| ≤ C₂ * δ := by
      intro t ht x hx
      have h1 := hC₂ h δ hδnn hδ1 hδle hh
        (fun k hk u _ => hjet k (le_trans hk (by omega)) u) x hx t ht
      rw [← iteratedDeriv_eq_PhiParam n h (n + 2) x t,
        ← iteratedDeriv_eq_PhiParam n 0 (n + 2) x t]
      exact h1
    have hpt3 : ∀ t ∈ Set.Icc (-(profileX 1)) (profileX 1),
        ∀ x ∈ Set.Icc (7 / 10 : ℝ) (9 / 10),
          |PhiParam n h (n + 3) (x, t) - PhiParam n 0 (n + 3) (x, t)| ≤ C₃ * δ := by
      intro t ht x hx
      have h1 := hC₃ h δ hδnn hδ1 hδle hh
        (fun k hk u _ => hjet k (le_trans hk (by omega)) u) x hx t ht
      rw [← iteratedDeriv_eq_PhiParam n h (n + 3) x t,
        ← iteratedDeriv_eq_PhiParam n 0 (n + 3) x t]
      exact h1
    have hp0 := profileX_one_pos'
    have harith : ∀ Ci : ℝ, 0 ≤ Ci → Ci ≤ C₁ + C₂ + C₃ → (2 * profileX 1) * (Ci * δ)
        ≤ (C₁ + C₂ + C₃ + 1) * (2 * profileX 1 + 1) * δ := by
      intro Ci hCinn hCi
      have h1 : Ci ≤ C₁ + C₂ + C₃ + 1 := by linarith
      have h2 : 2 * profileX 1 ≤ 2 * profileX 1 + 1 := by linarith
      have h4 : (2 * profileX 1) * Ci ≤ (2 * profileX 1 + 1) * (C₁ + C₂ + C₃ + 1) :=
        mul_le_mul h2 h1 hCinn (by linarith [hp0])
      calc (2 * profileX 1) * (Ci * δ) = ((2 * profileX 1) * Ci) * δ := by ring
        _ ≤ ((2 * profileX 1 + 1) * (C₁ + C₂ + C₃ + 1)) * δ :=
            mul_le_mul_of_nonneg_right h4 hδnn
        _ = (C₁ + C₂ + C₃ + 1) * (2 * profileX 1 + 1) * δ := by ring
    interval_cases j
    · have hstep := E1_deriv_step n hh hhd hδnn hC₁nn 0 (n + 1) (by omega) hpt1 hv
      exact le_trans hstep (harith C₁ hC₁nn (by linarith))
    · have hstep := E1_deriv_step n hh hhd hδnn hC₂nn 1 (n + 2) (by omega) hpt2 hv
      exact le_trans hstep (harith C₂ hC₂nn (by linarith))
    · have hstep := E1_deriv_step n hh hhd hδnn hC₃nn 2 (n + 3) (by omega) hpt3 hv
      exact le_trans hstep (harith C₃ hC₃nn (by linarith))

end

end Work.OddVolterra.Existence
