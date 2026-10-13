import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
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

set_option autoImplicit false

/-! ## Elementary facts about the right end `xNear = sin(π/4)` of the near region -/

lemma xNear_pos_b : 0 < xNear := by
  rw [xNear, Real.sin_pi_div_four]
  positivity

lemma xNear_lt_one_b : xNear < 1 := by
  rw [xNear, Real.sin_pi_div_four]
  have h : Real.sqrt 2 < 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  linarith

/-! ## Smoothness of the coefficients

`kappa x = cos (arcsin x)` is smooth on `(-1,1)`, hence on `(0, xNear)`; the coefficients
`bCoeff i j` are built from it by the recursion, so they are smooth too. -/

lemma contDiffOn_kappa_b : ContDiffOn ℝ (⊤ : ℕ∞) kappa (Set.Ioo 0 xNear) := by
  have h1 : ContDiffOn ℝ (⊤ : ℕ∞) Real.arcsin (Set.Ioo 0 xNear) :=
    (Real.contDiffOn_arcsin (n := (⊤ : ℕ∞))).mono (by
      intro x hx
      simp only [Set.mem_Ioo] at hx
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨by linarith [hx.1], by linarith [hx.2, xNear_lt_one_b]⟩)
  have h2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => Real.cos (Real.arcsin x)) (Set.Ioo 0 xNear) :=
    Real.contDiff_cos.comp_contDiffOn h1
  refine h2.congr (fun x hx => ?_)
  simp only [kappa, thetaOf]
  congr 1
  ring

/-- On an open set, `ContDiffOn` is preserved by `deriv`. -/
lemma contDiffOn_deriv_of_isOpen (s : Set ℝ) (hs : IsOpen s) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f s) : ContDiffOn ℝ (⊤ : ℕ∞) (deriv f) s := by
  have h := hf.derivWithin hs.uniqueDiffOn (m := (⊤ : ℕ∞)) (by simp)
  exact h.congr (fun x hx => (derivWithin_of_isOpen hs hx).symm)

/-- Every iterated derivative of a function smooth on `(0,xNear)` is smooth there. -/
lemma contDiffOn_iteratedDeriv_b {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (Set.Ioo 0 xNear)) (j : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (iteratedDeriv j u) (Set.Ioo 0 xNear) := by
  induction j with
  | zero => simpa using hu
  | succ j ih =>
      have h := contDiffOn_deriv_of_isOpen _ isOpen_Ioo ih
      rw [iteratedDeriv_succ]
      exact h

/-- The coefficients `bCoeff i j` are smooth on `(0, xNear)`. -/
lemma contDiffOn_bCoeff (i : ℕ) : ∀ j : ℕ,
    ContDiffOn ℝ (⊤ : ℕ∞) (bCoeff i j) (Set.Ioo 0 xNear) := by
  induction i with
  | zero =>
      intro j
      by_cases hj : j = 0
      · subst hj
        rw [bCoeff_zero_zero]
        exact contDiffOn_const
      · have : bCoeff 0 j = fun _ => (0:ℝ) := by
          funext x
          simp only [bCoeff, hj, ↓reduceIte]
        rw [this]
        exact contDiffOn_const
  | succ i ih =>
      intro j
      rw [show bCoeff (i + 1) j = (fun x => 2 * kappa x * (x * deriv (bCoeff i j) x
              + (j : ℝ) * bCoeff i j x)
            + (if j = 0 then 0 else 2 * kappa x * bCoeff i (j - 1) x)) from rfl]
      have hk : ContDiffOn ℝ (⊤ : ℕ∞) kappa (Set.Ioo 0 xNear) := contDiffOn_kappa_b
      have hderiv : ContDiffOn ℝ (⊤ : ℕ∞) (deriv (bCoeff i j)) (Set.Ioo 0 xNear) :=
        contDiffOn_deriv_of_isOpen _ isOpen_Ioo (ih j)
      have h1 : ContDiffOn ℝ (⊤ : ℕ∞)
          (fun x => x * deriv (bCoeff i j) x + (j : ℝ) * bCoeff i j x) (Set.Ioo 0 xNear) :=
        (contDiffOn_id.mul hderiv).add (contDiffOn_const.mul (ih j))
      have h2 : ContDiffOn ℝ (⊤ : ℕ∞)
          (fun x => 2 * kappa x * (x * deriv (bCoeff i j) x + (j : ℝ) * bCoeff i j x))
          (Set.Ioo 0 xNear) :=
        (contDiffOn_const.mul hk).mul h1
      have h3 : ContDiffOn ℝ (⊤ : ℕ∞)
          (fun x => (if j = 0 then (0:ℝ) else 2 * kappa x * bCoeff i (j - 1) x))
          (Set.Ioo 0 xNear) := by
        by_cases hj : j = 0
        · simp only [hj, ↓reduceIte]
          exact contDiffOn_const
        · simp only [hj, ↓reduceIte]
          exact (contDiffOn_const.mul hk).mul (ih (j - 1))
      exact h2.add h3

/-! ## The vanishing of the coefficients above the diagonal -/

/-- `bCoeff i j` vanishes identically once `j > i`. -/
lemma bCoeff_eq_zero_of_lt (i : ℕ) : ∀ j : ℕ, i < j → bCoeff i j = fun _ => (0:ℝ) := by
  induction i with
  | zero =>
      intro j hj
      funext x
      simp only [bCoeff, Nat.pos_iff_ne_zero.mp hj, ↓reduceIte]
  | succ i ih =>
      intro j hj
      funext x
      have h1 : bCoeff i j = fun _ => (0:ℝ) := ih j (by omega)
      have h2 : bCoeff i (j - 1) = fun _ => (0:ℝ) := ih (j - 1) (by omega)
      have h3 : j ≠ 0 := by omega
      rw [show bCoeff (i + 1) j = (fun x => 2 * kappa x * (x * deriv (bCoeff i j) x
            + (j : ℝ) * bCoeff i j x)
            + (if j = 0 then 0 else 2 * kappa x * bCoeff i (j - 1) x)) from rfl, h1, h2]
      simp [h3]

/-! ## The expansion sum `S` -/

/-- The right-hand side of the expansion: `∑_{j ≤ i} b i j x · (x^j · ∂_x^j u x)`. -/
def S (u : ℝ → ℝ) (i : ℕ) : ℝ → ℝ :=
  fun x => ∑ j ∈ Finset.range (i + 1), bCoeff i j x * (x ^ j * iteratedDeriv j u x)

/-! ## The two algebraic lemmas behind the induction step -/

/-- Pointwise form of the induction step: pulling `x ∂_x` through the `j`-th term of the
expansion shifts the summation index in the last summand. -/
lemma step_point (x K : ℝ) (P : ℕ → ℝ) (A A' : ℕ → ℝ) (j : ℕ) :
    K * (x * (A' j * (x ^ j * P j) + A j * ((j : ℝ) * x ^ (j - 1) * P j + x ^ j * P (j + 1))))
      = (K * (x * A' j + (j : ℝ) * A j)) * (x ^ j * P j)
        + K * A j * (x ^ (j + 1) * P (j + 1)) := by
  have key : x * ((j : ℝ) * x ^ (j - 1) * P j) = (j : ℝ) * x ^ j * P j := by
    match j with
    | 0 => simp
    | k + 1 => rw [show (k + 1) - 1 = k by omega, pow_succ']; ring
  have key2 : x * (x ^ j * P (j + 1)) = x ^ (j + 1) * P (j + 1) := by
    rw [← mul_assoc, ← pow_succ']
  calc K * (x * (A' j * (x ^ j * P j) + A j * ((j : ℝ) * x ^ (j - 1) * P j + x ^ j * P (j + 1))))
      = K * (x * (A' j * (x ^ j * P j))
          + (x * (A j * ((j : ℝ) * x ^ (j - 1) * P j)) + x * (A j * (x ^ j * P (j + 1))))) := by ring
    _ = K * ((A' j * (x * (x ^ j * P j)))
          + (A j * (x * ((j : ℝ) * x ^ (j - 1) * P j)) + A j * (x * (x ^ j * P (j + 1))))) := by ring
    _ = K * ((A' j * (x * (x ^ j * P j)))
          + (A j * ((j : ℝ) * x ^ j * P j) + A j * (x ^ (j + 1) * P (j + 1)))) := by rw [key, key2]
    _ = (K * (x * A' j + (j : ℝ) * A j)) * (x ^ j * P j)
        + K * A j * (x ^ (j + 1) * P (j + 1)) := by ring

/-- Sum form of the induction step, matching the recursion defining `bCoeff`. -/
lemma step_alg (i : ℕ) (x K : ℝ) (P : ℕ → ℝ) (A A' : ℕ → ℝ)
    (hA : A (i + 1) = 0) (hA' : A' (i + 1) = 0) :
    K * (x * ∑ j ∈ Finset.range (i + 1),
        (A' j * (x ^ j * P j) + A j * ((j : ℝ) * x ^ (j - 1) * P j + x ^ j * P (j + 1))))
      = ∑ j ∈ Finset.range (i + 2),
          (K * (x * A' j + (j : ℝ) * A j) + (if j = 0 then 0 else K * A (j - 1)))
            * (x ^ j * P j) := by
  have hL : K * (x * ∑ j ∈ Finset.range (i + 1),
        (A' j * (x ^ j * P j) + A j * ((j : ℝ) * x ^ (j - 1) * P j + x ^ j * P (j + 1))))
      = ∑ j ∈ Finset.range (i + 1),
          ((K * (x * A' j + (j : ℝ) * A j)) * (x ^ j * P j)
            + K * A j * (x ^ (j + 1) * P (j + 1))) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => step_point x K P A A' j)
  have hFtop : (K * (x * A' (i + 1) + ((i + 1 : ℕ)) * A (i + 1))) * (x ^ (i + 1) * P (i + 1)) = 0 := by
    simp [hA, hA']
  have hF : ∑ j ∈ Finset.range (i + 2), (K * (x * A' j + (j : ℝ) * A j)) * (x ^ j * P j)
      = ∑ j ∈ Finset.range (i + 1), (K * (x * A' j + (j : ℝ) * A j)) * (x ^ j * P j) := by
    rw [Finset.sum_range_succ, hFtop, add_zero]
  have hG : ∑ k ∈ Finset.range (i + 2), (if k = 0 then 0 else K * A (k - 1)) * (x ^ k * P k)
      = ∑ j ∈ Finset.range (i + 1), K * A j * (x ^ (j + 1) * P (j + 1)) := by
    rw [Finset.sum_range_succ']
    have h0 : (if (0 : ℕ) = 0 then (0 : ℝ) else K * A (0 - 1)) * (x ^ 0 * P 0) = 0 := by simp
    rw [h0, add_zero]
    apply Finset.sum_congr rfl
    intro k _
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.succ_sub_one]
  rw [hL, Finset.sum_add_distrib, ← hF, ← hG, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-! ## The derivative of the expansion sum -/

/-- The derivative of `S u i` is obtained by the product rule, term by term. -/
lemma deriv_S (i : ℕ) {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (Set.Ioo 0 xNear)) {x : ℝ} (hx : x ∈ Set.Ioo 0 xNear) :
    deriv (S u i) x
      = ∑ j ∈ Finset.range (i + 1),
          (deriv (bCoeff i j) x * (x ^ j * iteratedDeriv j u x)
            + bCoeff i j x * ((j : ℝ) * x ^ (j - 1) * iteratedDeriv j u x
                + x ^ j * iteratedDeriv (j + 1) u x)) := by
  have hs : Set.Ioo (0 : ℝ) xNear ∈ 𝓝 x := isOpen_Ioo.mem_nhds hx
  have hterm : ∀ j : ℕ, HasDerivAt (fun y => bCoeff i j y * (y ^ j * iteratedDeriv j u y))
      (deriv (bCoeff i j) x * (x ^ j * iteratedDeriv j u x)
        + bCoeff i j x * ((j : ℝ) * x ^ (j - 1) * iteratedDeriv j u x
            + x ^ j * iteratedDeriv (j + 1) u x)) x := by
    intro j
    have hb : HasDerivAt (bCoeff i j) (deriv (bCoeff i j) x) x :=
      (((contDiffOn_bCoeff i j).differentiableOn (by simp)).differentiableAt hs).hasDerivAt
    have hiu : HasDerivAt (iteratedDeriv j u) (iteratedDeriv (j + 1) u x) x := by
      have h := (((contDiffOn_iteratedDeriv_b hu j).differentiableOn (by simp)).differentiableAt hs).hasDerivAt
      rwa [← iteratedDeriv_succ] at h
    exact hb.mul ((hasDerivAt_pow j x).mul hiu)
  rw [show S u i = (fun y => ∑ j ∈ Finset.range (i + 1),
        bCoeff i j y * (y ^ j * iteratedDeriv j u y)) from rfl,
      deriv_fun_sum (fun j _ => (hterm j).differentiableAt)]
  exact Finset.sum_congr rfl (fun j _ => (hterm j).deriv)

/-! ## The expansion, as an equality of functions on the near region -/

lemma bCoeff_expansion_eqon (i : ℕ) {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (Set.Ioo 0 xNear)) :
    Set.EqOn ((Gop^[i]) u) (S u i) (Set.Ioo 0 xNear) := by
  induction i with
  | zero =>
      intro x hx
      simp [S, bCoeff]
  | succ i ih =>
      intro x hx
      have hEv : (Gop^[i]) u =ᶠ[𝓝 x] S u i :=
        ih.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hx)
      have hderiv : deriv ((Gop^[i]) u) x = deriv (S u i) x := hEv.deriv_eq
      rw [Function.iterate_succ_apply',
        show Gop ((Gop^[i]) u) x = 2 * kappa x * (x * deriv ((Gop^[i]) u) x) from rfl, hderiv,
        deriv_S i hu hx]
      have hA : (fun j => bCoeff i j x) (i + 1) = 0 := by
        show bCoeff i (i + 1) x = 0
        rw [bCoeff_eq_zero_of_lt i (i + 1) (by omega)]
      have hA' : (fun j => deriv (bCoeff i j) x) (i + 1) = 0 := by
        show deriv (bCoeff i (i + 1)) x = 0
        rw [bCoeff_eq_zero_of_lt i (i + 1) (by omega)]
        simp
      rw [step_alg i x (2 * kappa x) (fun j => iteratedDeriv j u x) (fun j => bCoeff i j x)
        (fun j => deriv (bCoeff i j) x) hA hA']
      rw [show S u (i + 1) x = ∑ j ∈ Finset.range (i + 2),
            bCoeff (i + 1) j x * (x ^ j * iteratedDeriv j u x) from rfl]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [show bCoeff (i + 1) j x = 2 * kappa x * (x * deriv (bCoeff i j) x
            + (j : ℝ) * bCoeff i j x) + (if j = 0 then 0 else 2 * kappa x * bCoeff i (j - 1) x)
          from rfl]

/-- **The expansion of `G^i u` in powers of `x`.**  With `bCoeff` as defined in
`Work.FTS.H2.DivQ.Defs` (`b 0 0 = 1`, `b 0 j = 0` for `j ≠ 0`, and

  `b (i+1) j = 2κ · (x · (b i j)' + j · b i j) + (if j = 0 then 0 else 2κ · b i (j-1))`),

for every `u` of class `C^∞` on `(0, x₁)` (`x₁ = xNear = sin(π/4)`) and every `x ∈ (0,x₁)`:

  `(G^i u) x = Σ_{j ∈ range (i+1)} b i j x · (x^j · ∂_x^j u (x))`.

ROUTE.  Induction on `i`.  `i = 0`: both sides are `u x`.  Step: write `u_i := G^i u`, assume the
expansion for `u_i` and compute
`G u_i = 2κ x ∂_x (Σ_j b i j · x^j ∂_x^j u)`.  Termwise (product rule, three terms)
`∂_x(b i j · x^j ∂_x^j u) = (b i j)' x^j ∂_x^j u + b i j · j x^{j-1} ∂_x^j u + b i j x^j ∂_x^{j+1} u`,
so `2κ x ∂_x(…) = Σ_j b (i+1) j x^j ∂_x^j u` after re-indexing `j ↦ j-1` in the last sum (the new
coefficient of `x^j ∂_x^j u` is `2κ(x (b i j)' + j b i j) + 2κ b i (j-1)`, which is the recursion).
All identities hold on the open interval `(0,x₁)`, where `u` is smooth, so `∂_x^j u = iteratedDeriv j u`
and the finite sum can be differentiated termwise; note the induction also needs
`ContDiffOn ⊤ (Gop u_i) (Ioo 0 x₁)`, which follows from the expansion and the smoothness of the
coefficients `b i j` on the open set. -/
theorem bCoeff_expansion (i : ℕ) {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (Set.Ioo 0 xNear)) {x : ℝ} (hx : x ∈ Set.Ioo 0 xNear) :
    (Gop^[i] u) x
      = ∑ j ∈ Finset.range (i + 1), bCoeff i j x * (x ^ j * iteratedDeriv j u x) := by
  have h := bCoeff_expansion_eqon i hu hx
  simpa [S] using h

end Work.FTS.H2.DivQ
