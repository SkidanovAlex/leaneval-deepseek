import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Submission.Work.FTS.H2.DivQ.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.DivQ

/-!
# The expansion of `G^i (2κ ∂_x f)` in powers of `x`

This file proves `aCoeff_expansion`, the `x`-coordinate counterpart of `bCoeff_expansion`:

  `(G^i (2κ ∂_x f)) x = Σ_{l ∈ range (i+1)} aCoeff i l x · (x^l · ∂_x^{l+1} f x)`

for `f` of class `C^∞` on `(0, xNear)`.  The proof is an induction on `i`; the pieces are

* `CoeffAux.deriv_sum_expansion` — the term-by-term derivative of `Σ_l c l y · (y^l · u l y)`;
* `CoeffAux.aCoeff_term_ident` — the elementary regrouping of one summand, which is the
  recursion `a (i+1) l = 2κ (x (a i l)' + l a i l) + 2κ a i (l-1)`;
* `CoeffAux.sum_step_reindex` — the index bookkeeping turning `Σ_{l ≤ i}` into `Σ_{j ≤ i+1}`;
* `aCoeff_contDiffOn`, `aCoeff_eq_zero_of_lt` — smoothness of the coefficients and the
  vanishing `a i j = 0` for `j > i`, needed to differentiate the induction hypothesis and to
  close the top index;
* `CoeffAux.contDiffOn_iteratedDeriv` — `iteratedDeriv n f` is again `C^∞` on an open set.

The mathematical heart is `aCoeff_step`, which performs one induction step for an arbitrary
point, and then `aCoeff_expansion` assembles the induction.
-/

/-- `y * y^l = y^(l+1)` for the (positive) exponents appearing in the expansion. -/
theorem mul_pow_succ (y : ℝ) (l : ℕ) : y * y ^ l = y ^ (l + 1) := by
  rw [pow_succ, mul_comm]

/-- The `l = 0`-degenerate case of `y * y^(l-1) = y^l`, with the factor `l` that kills it. -/
theorem coe_nat_mul_mul_pow_pred (y : ℝ) (l : ℕ) :
    (l : ℝ) * (y * y ^ (l - 1)) = (l : ℝ) * y ^ l := by
  rcases l with _ | m
  · ring
  · simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ]
    ring

namespace CoeffAux

/-- Differentiate a finite sum of the form `y ↦ c l y * (y^l * u l y)` term by term at a point
where every component is differentiable. -/
theorem deriv_sum_expansion (N : ℕ) (c u : ℕ → ℝ → ℝ) {x : ℝ}
    (hc : ∀ l, DifferentiableAt ℝ (c l) x) (hu : ∀ l, DifferentiableAt ℝ (u l) x) :
    deriv (fun y => ∑ l ∈ Finset.range (N + 1), c l y * (y ^ l * u l y)) x
      = ∑ l ∈ Finset.range (N + 1),
          (deriv (c l) x * (x ^ l * u l x)
            + c l x * ((l : ℝ) * x ^ (l - 1) * u l x + x ^ l * deriv (u l) x)) := by
  have hd : ∀ l, DifferentiableAt ℝ (fun y => c l y * (y ^ l * u l y)) x := fun l =>
    DifferentiableAt.mul (hc l) (DifferentiableAt.mul (differentiableAt_pow l) (hu l))
  have hfun : (fun y => ∑ l ∈ Finset.range (N + 1), c l y * (y ^ l * u l y))
      = ∑ l ∈ Finset.range (N + 1), fun y => c l y * (y ^ l * u l y) := by
    ext y; simp
  rw [hfun, deriv_sum (fun l _ => hd l)]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  have h1 : deriv (fun y => c l y * (y ^ l * u l y)) x
      = deriv (c l) x * (x ^ l * u l x) + c l x * deriv (fun y => y ^ l * u l y) x :=
    deriv_mul (hc l) (DifferentiableAt.mul (differentiableAt_pow l) (hu l))
  have h2 : deriv (fun y => y ^ l * u l y) x
      = (l : ℝ) * x ^ (l - 1) * u l x + x ^ l * deriv (u l) x := by
    show deriv ((fun y : ℝ => y ^ l) * u l) x
      = (l : ℝ) * x ^ (l - 1) * u l x + x ^ l * deriv (u l) x
    rw [deriv_mul (differentiableAt_pow l) (hu l)]
    rw [show deriv (fun y : ℝ => y ^ l) x = (l : ℝ) * x ^ (l - 1) from (hasDerivAt_pow l x).deriv]
  rw [h1, h2]

/-- The elementary identity behind the recursion for `aCoeff`: differentiating the summand
`c · (y^l · d) + a · (l y^(l-1) d + y^l e)` and multiplying by `k · y` regroups the result into
the `l`-th and `(l+1)`-st coefficient slots. -/
theorem aCoeff_term_ident (k y a c d e : ℝ) (l : ℕ) :
    k * (y * (c * (y ^ l * d) + a * ((l : ℝ) * y ^ (l - 1) * d + y ^ l * e)))
      = (k * (y * c + (l : ℝ) * a)) * (y ^ l * d) + (k * a) * (y ^ (l + 1) * e) := by
  rcases l with _ | m
  · ring
  · simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ]
    ring

/-- Reindexing identity: a sum of `P l * T l + Q l * T (l+1)` equals the sum over one more index
of `(P j + (if j = 0 then 0 else Q (j-1))) * T j`, given `P (N+1) = 0` (the hypothesis that makes
the top coefficient vanish, as it does for `aCoeff`). -/
theorem sum_step_reindex (N : ℕ) (P Q T : ℕ → ℝ) (hP : P (N + 1) = 0) :
    (∑ l ∈ Finset.range (N + 1), (P l * T l + Q l * T (l + 1)))
      = ∑ j ∈ Finset.range (N + 2), (P j + (if j = 0 then 0 else Q (j - 1))) * T j := by
  have hL : (∑ l ∈ Finset.range (N + 1), (P l * T l + Q l * T (l + 1)))
      = (∑ l ∈ Finset.range N, (P l * T l + Q l * T (l + 1))) + P N * T N + Q N * T (N + 1) := by
    rw [Finset.sum_range_succ]
    ring
  have hR : (∑ j ∈ Finset.range (N + 2), (P j + (if j = 0 then 0 else Q (j - 1))) * T j)
      = (∑ j ∈ Finset.range N, P (j + 1) * T (j + 1)) + (∑ j ∈ Finset.range N, Q j * T (j + 1))
          + P 0 * T 0 + Q N * T (N + 1) := by
    rw [Finset.sum_range_succ]
    rw [show (P (N + 1) + (if N + 1 = 0 then 0 else Q (N + 1 - 1))) * T (N + 1)
        = Q N * T (N + 1) by
      rw [hP]; simp]
    rw [Finset.sum_range_succ']
    rw [show (P 0 + (if (0 : ℕ) = 0 then 0 else Q (0 - 1))) * T 0 = P 0 * T 0 by simp]
    have hcongr : (∑ k ∈ Finset.range N,
          (P (k + 1) + (if k + 1 = 0 then 0 else Q (k + 1 - 1))) * T (k + 1))
        = (∑ k ∈ Finset.range N, (P (k + 1) * T (k + 1) + Q k * T (k + 1))) :=
      Finset.sum_congr rfl (fun k _ => by
        simp only [Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]; ring)
    rw [hcongr]
    rw [Finset.sum_add_distrib]
  rw [hL, hR]
  have hkey : (∑ j ∈ Finset.range N, P (j + 1) * T (j + 1)) + P 0 * T 0
      = (∑ j ∈ Finset.range N, P j * T j) + P N * T N := by
    rw [← Finset.sum_range_succ' (fun j => P j * T j) N]
    rw [Finset.sum_range_succ (fun j => P j * T j) N]
  have hkey' : (∑ j ∈ Finset.range N, P (j + 1) * T (j + 1))
      = (∑ j ∈ Finset.range N, P j * T j) + P N * T N - P 0 * T 0 := by linarith [hkey]
  rw [hkey', Finset.sum_add_distrib]
  ring

/-- Every iterated derivative of a function of class `C^∞` on an open set is again of class `C^∞`
there. -/
theorem contDiffOn_iteratedDeriv {f : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f s) (n : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (iteratedDeriv n f) s := by
  induction n with
  | zero => simpa using hf
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact ih.deriv_of_isOpen hs (by simp)

end CoeffAux

/-- The coefficient `aCoeff i j` vanishes identically once `j > i`: the `i`-th iterate
`G^i (2κ ∂_x f)` only involves `∂_x^{1}, …, ∂_x^{i+1} f`.  (This is the input that closes the
top index of the expansion at each induction step.) -/
theorem aCoeff_eq_zero_of_lt {i j : ℕ} (h : i < j) :
    aCoeff i j = fun _ => (0 : ℝ) := by
  induction i generalizing j with
  | zero =>
    funext x
    show (fun x => if j = 0 then 2 * kappa x else 0) x = 0
    simp [show j ≠ 0 by omega]
  | succ i ih =>
    have h1 : i < j := by omega
    have h2 : i < j - 1 := by omega
    funext x
    show (fun x => 2 * kappa x * (x * deriv (aCoeff i j) x + (j : ℝ) * aCoeff i j x)
      + (if j = 0 then 0 else 2 * kappa x * aCoeff i (j - 1) x)) x = 0
    rw [ih h1, ih h2]
    simp [show j ≠ 0 by omega]

/-- Every coefficient `aCoeff i j` is of class `C^∞` on the near interval `(0, xNear)`: it is
built from `κ = cos ∘ arcsin` and its derivatives by the recursion. -/
theorem aCoeff_contDiffOn (i j : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (aCoeff i j) (Set.Ioo 0 xNear) := by
  have hxNear1 : xNear < 1 := by
    unfold xNear
    rw [Real.sin_pi_div_four]
    have h : Real.sqrt 2 < 2 := by
      rw [Real.sqrt_lt' (by norm_num)]
      norm_num
    linarith
  have hk : ContDiffOn ℝ (⊤ : ℕ∞) kappa (Set.Ioo 0 xNear) := by
    have hfun : kappa = fun x => Real.cos (Real.arcsin x) := by
      funext x
      show Real.cos (2 * thetaOf x) = Real.cos (Real.arcsin x)
      rw [show 2 * thetaOf x = Real.arcsin x by unfold thetaOf; ring]
    rw [hfun]
    intro x hx
    exact (Real.contDiff_cos.contDiffAt.comp x
      (Real.contDiffAt_arcsin (by linarith [hx.1])
        (by linarith [hx.2, hxNear1]))).contDiffWithinAt
  have key : ∀ i j : ℕ, ContDiffOn ℝ (⊤ : ℕ∞) (aCoeff i j) (Set.Ioo 0 xNear) := by
    intro i
    induction i with
    | zero =>
      intro j
      by_cases hj : j = 0
      · have hf0 : aCoeff 0 j = fun x => 2 * kappa x := by
          funext x
          show (fun x => if j = 0 then 2 * kappa x else 0) x = 2 * kappa x
          simp [hj]
        rw [hf0]
        exact contDiffOn_const.mul hk
      · have hf0 : aCoeff 0 j = fun _ => (0 : ℝ) := by
          funext x
          show (fun x => if j = 0 then 2 * kappa x else 0) x = 0
          simp [hj]
        rw [hf0]
        exact contDiffOn_const
    | succ i ih =>
      intro j
      have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (deriv (aCoeff i j)) (Set.Ioo 0 xNear) :=
        (ih j).deriv_of_isOpen isOpen_Ioo (by simp)
      by_cases hj : j = 0
      · have hfs : aCoeff (i + 1) j
            = fun x => 2 * kappa x * (x * deriv (aCoeff i j) x + (j : ℝ) * aCoeff i j x) := by
          funext x
          show (fun x => 2 * kappa x * (x * deriv (aCoeff i j) x + (j : ℝ) * aCoeff i j x)
            + (if j = 0 then 0 else 2 * kappa x * aCoeff i (j - 1) x)) x
            = 2 * kappa x * (x * deriv (aCoeff i j) x + (j : ℝ) * aCoeff i j x)
          simp [hj]
        rw [hfs]
        exact ((contDiffOn_const.mul hk).mul
          ((contDiffOn_id.mul h1).add (contDiffOn_const.mul (ih j))))
      · have hfs : aCoeff (i + 1) j
            = fun x => 2 * kappa x * (x * deriv (aCoeff i j) x + (j : ℝ) * aCoeff i j x)
                + 2 * kappa x * aCoeff i (j - 1) x := by
          funext x
          show (fun x => 2 * kappa x * (x * deriv (aCoeff i j) x + (j : ℝ) * aCoeff i j x)
            + (if j = 0 then 0 else 2 * kappa x * aCoeff i (j - 1) x)) x
            = 2 * kappa x * (x * deriv (aCoeff i j) x + (j : ℝ) * aCoeff i j x)
              + 2 * kappa x * aCoeff i (j - 1) x
          simp [hj]
        rw [hfs]
        exact ((contDiffOn_const.mul hk).mul
          ((contDiffOn_id.mul h1).add (contDiffOn_const.mul (ih j)))).add
          ((contDiffOn_const.mul hk).mul (ih (j - 1)))
  exact key i j

/-- **One induction step of `aCoeff_expansion`.**  If the expansion is known at level `i`,
differentiating it (`G = 2κ x ∂_x`) and regrouping produces the expansion at level `i+1`. -/
theorem aCoeff_step {f : ℝ → ℝ} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ioo 0 xNear))
    (i : ℕ) {x : ℝ} (hx : x ∈ Set.Ioo 0 xNear) :
    2 * kappa x * (x * deriv (fun y => ∑ l ∈ Finset.range (i + 1),
        aCoeff i l y * (y ^ l * iteratedDeriv (l + 1) f y)) x)
      = ∑ l ∈ Finset.range (i + 2), aCoeff (i + 1) l x * (x ^ l * iteratedDeriv (l + 1) f x) := by
  have hc : ∀ l, DifferentiableAt ℝ (aCoeff i l) x := fun l =>
    ((aCoeff_contDiffOn i l).differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds hx)
  have hu : ∀ l, DifferentiableAt ℝ (iteratedDeriv (l + 1) f) x := fun l =>
    ((CoeffAux.contDiffOn_iteratedDeriv isOpen_Ioo hf (l + 1)).differentiableOn
      (by simp)).differentiableAt (isOpen_Ioo.mem_nhds hx)
  have hd := CoeffAux.deriv_sum_expansion i (fun l => aCoeff i l)
    (fun l => iteratedDeriv (l + 1) f) hc hu
  have hD : ∀ l, deriv (iteratedDeriv (l + 1) f) x = iteratedDeriv (l + 2) f x := fun l =>
    congrFun (iteratedDeriv_succ (n := l + 1) (f := f)).symm x
  have hd' : deriv (fun y => ∑ l ∈ Finset.range (i + 1),
        aCoeff i l y * (y ^ l * iteratedDeriv (l + 1) f y)) x
      = ∑ l ∈ Finset.range (i + 1), (deriv (aCoeff i l) x * (x ^ l * iteratedDeriv (l + 1) f x)
          + aCoeff i l x * ((l : ℝ) * x ^ (l - 1) * iteratedDeriv (l + 1) f x
              + x ^ l * iteratedDeriv (l + 2) f x)) := by
    rw [hd]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [hD l]
  rw [hd']
  have hL : 2 * kappa x * (x * (∑ l ∈ Finset.range (i + 1),
        (deriv (aCoeff i l) x * (x ^ l * iteratedDeriv (l + 1) f x)
          + aCoeff i l x * ((l : ℝ) * x ^ (l - 1) * iteratedDeriv (l + 1) f x
              + x ^ l * iteratedDeriv (l + 2) f x))))
      = ∑ l ∈ Finset.range (i + 1),
          ((2 * kappa x * (x * deriv (aCoeff i l) x + (l : ℝ) * aCoeff i l x))
              * (x ^ l * iteratedDeriv (l + 1) f x)
            + (2 * kappa x * aCoeff i l x) * (x ^ (l + 1) * iteratedDeriv (l + 2) f x)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    exact CoeffAux.aCoeff_term_ident (2 * kappa x) x (aCoeff i l x) (deriv (aCoeff i l) x)
      (iteratedDeriv (l + 1) f x) (iteratedDeriv (l + 2) f x) l
  have hP : 2 * kappa x * (x * deriv (aCoeff i (i + 1)) x
      + ((i + 1 : ℕ) : ℝ) * aCoeff i (i + 1) x) = 0 := by
    rw [aCoeff_eq_zero_of_lt (Nat.lt_succ_self i)]
    simp
  have hsum := CoeffAux.sum_step_reindex i
    (fun j => 2 * kappa x * (x * deriv (aCoeff i j) x + (j : ℝ) * aCoeff i j x))
    (fun j => 2 * kappa x * aCoeff i j x) (fun j => x ^ j * iteratedDeriv (j + 1) f x)
    (show (fun j => 2 * kappa x * (x * deriv (aCoeff i j) x + (j : ℝ) * aCoeff i j x)) (i + 1)
      = 0 from hP)
  have hR : (∑ j ∈ Finset.range (i + 2),
        aCoeff (i + 1) j x * (x ^ j * iteratedDeriv (j + 1) f x))
      = ∑ j ∈ Finset.range (i + 2),
          ((2 * kappa x * (x * deriv (aCoeff i j) x + (j : ℝ) * aCoeff i j x))
            + (if j = 0 then 0 else 2 * kappa x * aCoeff i (j - 1) x))
              * (x ^ j * iteratedDeriv (j + 1) f x) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    show ((fun x => 2 * kappa x * (x * deriv (aCoeff i j) x + (j : ℝ) * aCoeff i j x)
        + (if j = 0 then 0 else 2 * kappa x * aCoeff i (j - 1) x)) x)
          * (x ^ j * iteratedDeriv (j + 1) f x)
      = ((2 * kappa x * (x * deriv (aCoeff i j) x + (j : ℝ) * aCoeff i j x))
          + (if j = 0 then 0 else 2 * kappa x * aCoeff i (j - 1) x))
            * (x ^ j * iteratedDeriv (j + 1) f x)
    rfl
  rw [hL, hR]
  exact hsum

/-- **The expansion of `G^i (2κ ∂_x f)` in powers of `x`.**  With `aCoeff` as defined in
`Work.FTS.H2.DivQ.Defs` (`a 0 0 = 2κ`, `a 0 j = 0` for `j ≠ 0`, and the same recursion as `bCoeff`),

for every `f` of class `C^∞` on `(0, x₁)` (`x₁ = xNear = sin(π/4)`) and every `x ∈ (0,x₁)`:

  `(G^i (fun y => 2 κ y * ∂_x f y)) x = Σ_{l ∈ range (i+1)} a i l x · (x^l · ∂_x^{l+1} f (x))`.

This is the `x`-form of `D_θ^i(∂_θ h)(arcsin x / 2)`: indeed `∂_θ h(θ(x)) = 2κ(x) ∂_x(sliceX h) x`.

ROUTE.  Same as `bCoeff_expansion`, by induction on `i`, with the initial datum `u_0 = 2κ ∂_x f`
and the product rule `∂_x(2κ y ∂_x f y) = 2κ' y ∂_x f y + 2κ y ∂_x² f y`; the induction hypothesis
expresses `G^i(2κ∂_x f)` as `Σ_l a i l x · x^l ∂_x^{l+1} f x`, and `G` adds one more `∂_x` (the
`l ↦ l+1` re-indexing) and differentiates the coefficient (the `a (i+1) l` recursion). -/
theorem aCoeff_expansion (i : ℕ) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ioo 0 xNear)) {x : ℝ} (hx : x ∈ Set.Ioo 0 xNear) :
    (Gop^[i] (fun y => 2 * kappa y * deriv f y)) x
      = ∑ l ∈ Finset.range (i + 1), aCoeff i l x * (x ^ l * iteratedDeriv (l + 1) f x) := by
  have key : ∀ i : ℕ, ∀ x ∈ Set.Ioo 0 xNear,
      (Gop^[i] (fun y => 2 * kappa y * deriv f y)) x
        = ∑ l ∈ Finset.range (i + 1), aCoeff i l x * (x ^ l * iteratedDeriv (l + 1) f x) := by
    intro i
    induction i with
    | zero =>
      intro x hx
      show (fun y => 2 * kappa y * deriv f y) x = _
      simp [iteratedDeriv_one]
    | succ i ih =>
      intro x hx
      rw [Function.iterate_succ_apply']
      show 2 * kappa x * (x * deriv (Gop^[i] (fun y => 2 * kappa y * deriv f y)) x) = _
      have hev : (fun y => ∑ l ∈ Finset.range (i + 1),
            aCoeff i l y * (y ^ l * iteratedDeriv (l + 1) f y))
          =ᶠ[𝓝 x] (Gop^[i] (fun y => 2 * kappa y * deriv f y)) := by
        filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
        exact (ih y hy).symm
      rw [← hev.deriv_eq]
      show 2 * kappa x * (x * deriv (fun y => ∑ l ∈ Finset.range (i + 1),
            aCoeff i l y * (y ^ l * iteratedDeriv (l + 1) f y)) x)
          = ∑ l ∈ Finset.range (i + 2), aCoeff (i + 1) l x
              * (x ^ l * iteratedDeriv (l + 1) f x)
      exact aCoeff_step hf i hx
  exact key i x hx

end Work.FTS.H2.DivQ
