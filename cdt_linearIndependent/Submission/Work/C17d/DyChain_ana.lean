import Submission.Work.C17d.DyChainDefs

/-!
# The cleared class identity for a solution `y₁` of the order-two operator `M`

Let `M = P₂∂² + P₁∂ + P₀` (`Pᵢ = Work.C17.Pᵢx a b`) and let `y₁` be holomorphic on a disc
`B = ball (xs a b) δ`.  If `y₁` solves `M y₁ = 0` pointwise on `B`, then for every `k` the
`k`-th iterate `DyIter k y₁ = (D_y)^k y₁` of the `y`-derivative `D_y = ρ ∂_x`
(`ρ = (X-1)²/(X²-2X)`) is a combination `(A_k y₁ + B_k y₁')/D_k` with polynomial coefficients:
on `B \ {0,2}`,
  `D_k(z) · (D_y^k y₁)(z) = A_k(z) y₁(z) + B_k(z) (∂y₁)(z)`.

This is the analytic half of `Work.C17.DyIter_eq_cls`; the algebraic half (identifying
`A_k/D_k`, `B_k/D_k` with the class chain `cls`) is `Work.C17d.DyChain_rat`.
-/

namespace Work.C17d

open Polynomial Work.C17

open scoped Topology

noncomputable section

/-- The polynomial function `w ↦ p(w)` (with `p` over `ℚ` read in `ℂ`) has derivative
`p'(z)` — the `eval₂` version of `Polynomial.hasDerivAt`. -/
lemma hasDerivAt_eval₂ (p : Polynomial ℚ) (z : ℂ) :
    HasDerivAt (fun w => p.eval₂ (algebraMap ℚ ℂ) w) ((p.derivative).eval₂ (algebraMap ℚ ℂ) z) z := by
  have h := Polynomial.hasDerivAt (p.map (algebraMap ℚ ℂ)) z
  rw [Polynomial.derivative_map, Polynomial.eval_map] at h
  refine h.congr_of_eventuallyEq ?_
  filter_upwards with w
  exact Polynomial.eval₂_eq_eval_map (algebraMap ℚ ℂ) (x := w)

lemma deriv_eval₂ (p : Polynomial ℚ) (z : ℂ) :
    deriv (fun w => p.eval₂ (algebraMap ℚ ℂ) w) z = (p.derivative).eval₂ (algebraMap ℚ ℂ) z :=
  (hasDerivAt_eval₂ p z).deriv

lemma differentiableAt_eval₂ (p : Polynomial ℚ) (z : ℂ) :
    DifferentiableAt ℂ (fun w => p.eval₂ (algebraMap ℚ ℂ) w) z :=
  (hasDerivAt_eval₂ p z).differentiableAt

/-- The product rule for a polynomial function and an arbitrary differentiable function. -/
lemma deriv_mul_eval₂ (p : Polynomial ℚ) (f : ℂ → ℂ) (z : ℂ) (hf : DifferentiableAt ℂ f z) :
    deriv (fun w => p.eval₂ (algebraMap ℚ ℂ) w * f w) z
      = (p.derivative).eval₂ (algebraMap ℚ ℂ) z * f z + p.eval₂ (algebraMap ℚ ℂ) z * deriv f z := by
  rw [show (fun w => p.eval₂ (algebraMap ℚ ℂ) w * f w)
        = (fun w => p.eval₂ (algebraMap ℚ ℂ) w) * f from rfl,
    deriv_mul (differentiableAt_eval₂ p z) hf, deriv_eval₂]

/-- Additivity of `deriv` in the shape produced by `fun w => f w + g w`. -/
lemma deriv_add_fun (f g : ℂ → ℂ) (z : ℂ) (hf : DifferentiableAt ℂ f z)
    (hg : DifferentiableAt ℂ g z) :
    deriv (fun w => f w + g w) z = deriv f z + deriv g z := by
  rw [show (fun w => f w + g w) = f + g from rfl, deriv_add hf hg]

/-- Analyticity of `w ↦ (w-1)²`. -/
lemma analyticAt_sq_sub_one (z : ℂ) : AnalyticAt ℂ (fun w : ℂ => (w - 1) ^ 2) z := by
  have h : (fun w : ℂ => (w - 1) ^ 2) = (fun w : ℂ => w - 1) ^ 2 := rfl
  rw [h]
  exact ((analyticAt_id.sub analyticAt_const).pow 2)

/-- Analyticity of `w ↦ w² - 2w`. -/
lemma analyticAt_sq_sub_two (z : ℂ) : AnalyticAt ℂ (fun w : ℂ => w ^ 2 - 2 * w) z := by
  have h : (fun w : ℂ => w ^ 2 - 2 * w) = (fun w : ℂ => w ^ 2) - (fun w : ℂ => 2 * w) := rfl
  rw [h]
  exact ((analyticAt_id.pow 2).sub (analyticAt_const.mul analyticAt_id))

/-- Clearing identity for one step, in the form of a pure field computation. -/
lemma ana_step {D A B dD dA dB P2 P1 P0 F dF y dy ddy : ℂ}
    (h1 : D * F = A * y + B * dy)
    (h2 : dD * F + D * dF = dA * y + A * dy + dB * dy + B * ddy)
    (h3 : P2 * ddy + P1 * dy + P0 * y = 0) :
    D ^ 2 * P2 * dF = (D * P2 * dA - P2 * dD * A - D * B * P0) * y
      + (D * P2 * (A + dB) - D * B * P1 - P2 * dD * B) * dy := by
  linear_combination (D * P2) * h2 - (P2 * dD) * h1 + (D * B) * h3

/-- Evaluated form of the recursion for `D_k`. -/
lemma Dc_eval₂_succ (a b : ℚ) (k : ℕ) (z : ℂ) :
    (Dc a b (k + 1)).eval₂ (algebraMap ℚ ℂ) z
      = (Dc a b k).eval₂ (algebraMap ℚ ℂ) z ^ 2 * (P2x a b).eval₂ (algebraMap ℚ ℂ) z
        * (z ^ 2 - 2 * z) := by
  rw [Dc_succ]
  simp [wX]

/-- Evaluated form of the recursion for `A_k`. -/
lemma Ac_eval₂_succ (a b : ℚ) (k : ℕ) (z : ℂ) :
    (Ac a b (k + 1)).eval₂ (algebraMap ℚ ℂ) z
      = (z - 1) ^ 2
        * ((Dc a b k).eval₂ (algebraMap ℚ ℂ) z * (P2x a b).eval₂ (algebraMap ℚ ℂ) z
            * (Ac a b k).derivative.eval₂ (algebraMap ℚ ℂ) z
          - (P2x a b).eval₂ (algebraMap ℚ ℂ) z * (Dc a b k).derivative.eval₂ (algebraMap ℚ ℂ) z
            * (Ac a b k).eval₂ (algebraMap ℚ ℂ) z
          - (Dc a b k).eval₂ (algebraMap ℚ ℂ) z * (Bc a b k).eval₂ (algebraMap ℚ ℂ) z
            * (P0x a b).eval₂ (algebraMap ℚ ℂ) z) := by
  rw [Ac_succ]
  simp [rX]

/-- Evaluated form of the recursion for `B_k`. -/
lemma Bc_eval₂_succ (a b : ℚ) (k : ℕ) (z : ℂ) :
    (Bc a b (k + 1)).eval₂ (algebraMap ℚ ℂ) z
      = (z - 1) ^ 2
        * ((Dc a b k).eval₂ (algebraMap ℚ ℂ) z * (P2x a b).eval₂ (algebraMap ℚ ℂ) z
            * ((Ac a b k).eval₂ (algebraMap ℚ ℂ) z
              + (Bc a b k).derivative.eval₂ (algebraMap ℚ ℂ) z)
          - (Dc a b k).eval₂ (algebraMap ℚ ℂ) z * (Bc a b k).eval₂ (algebraMap ℚ ℂ) z
            * (P1x a b).eval₂ (algebraMap ℚ ℂ) z
          - (P2x a b).eval₂ (algebraMap ℚ ℂ) z * (Dc a b k).derivative.eval₂ (algebraMap ℚ ℂ) z
            * (Bc a b k).eval₂ (algebraMap ℚ ℂ) z) := by
  rw [Bc_succ]
  simp [rX]

theorem DyChain_ana (a b : ℚ) (y1 : ℂ → ℂ) {δ : ℝ} (hδ : 0 < δ)
    (hy1d : DifferentiableOn ℂ y1 (Metric.ball ((xs a b : ℂ)) δ))
    (hode : ∀ z ∈ Metric.ball ((xs a b : ℂ)) δ,
      (P2x a b).eval₂ (algebraMap ℚ ℂ) z * deriv (deriv y1) z
        + (P1x a b).eval₂ (algebraMap ℚ ℂ) z * deriv y1 z
        + (P0x a b).eval₂ (algebraMap ℚ ℂ) z * y1 z = 0) :
    ∀ k : ℕ, ∀ z ∈ Metric.ball ((xs a b : ℂ)) δ \ ({0, 2} : Set ℂ),
      (Dc a b k).eval₂ (algebraMap ℚ ℂ) z * DyIter k y1 z
        = (Ac a b k).eval₂ (algebraMap ℚ ℂ) z * y1 z
          + (Bc a b k).eval₂ (algebraMap ℚ ℂ) z * deriv y1 z := by
  have hBopen : IsOpen (Metric.ball ((xs a b : ℂ)) δ) := Metric.isOpen_ball
  have hcl : IsClosed ({0, 2} : Set ℂ) := by
    rw [show ({0, 2} : Set ℂ) = {0} ∪ {2} from rfl]
    exact isClosed_singleton.union isClosed_singleton
  have hGopen : IsOpen (Metric.ball ((xs a b : ℂ)) δ \ ({0, 2} : Set ℂ)) := hBopen.sdiff hcl
  have hAnal : AnalyticOn ℂ y1 (Metric.ball ((xs a b : ℂ)) δ) := hy1d.analyticOn hBopen
  have hy1diff : ∀ z ∈ Metric.ball ((xs a b : ℂ)) δ, DifferentiableAt ℂ y1 z :=
    fun z hz => (hAnal.analyticAt (hBopen.mem_nhds hz)).differentiableAt
  have hdy1diff : ∀ z ∈ Metric.ball ((xs a b : ℂ)) δ, DifferentiableAt ℂ (deriv y1) z :=
    fun z hz => (hAnal.analyticAt (hBopen.mem_nhds hz)).deriv.differentiableAt
  -- all iterates of `D_y` applied to `y₁` are analytic off `{0,2}`
  have hDi : ∀ k : ℕ, ∀ z ∈ Metric.ball ((xs a b : ℂ)) δ \ ({0, 2} : Set ℂ),
      AnalyticAt ℂ (DyIter k y1) z := by
    intro k
    induction k with
    | zero =>
        intro z hz
        simpa [DyIter] using hAnal.analyticAt (hBopen.mem_nhds hz.1)
    | succ k ih =>
        intro z hz
        have hz0 : z ≠ 0 := fun h => hz.2 (by simp [h])
        have hz2 : z ≠ 2 := fun h => hz.2 (by simp [h])
        have hzden : z ^ 2 - 2 * z ≠ 0 := by
          have h : z * (z - 2) ≠ 0 := mul_ne_zero hz0 (sub_ne_zero.mpr hz2)
          rw [show z ^ 2 - 2 * z = z * (z - 2) from by ring]
          exact h
        rw [show DyIter (k + 1) y1
            = (fun w : ℂ => deriv (DyIter k y1) w * (w - 1) ^ 2) / (fun w : ℂ => w ^ 2 - 2 * w) from by
          funext w; simp [DyIter, Function.iterate_succ_apply', Dy]]
        exact (((ih z hz).deriv.mul (analyticAt_sq_sub_one z)).div
          (analyticAt_sq_sub_two z) hzden)
  intro k
  induction k with
  | zero =>
      intro z hz
      simp only [Dc_zero, Ac_zero, Bc_zero, Polynomial.eval₂_one, Polynomial.eval₂_zero,
        DyIter, Function.iterate_zero, id_eq, one_mul, zero_mul, add_zero]
  | succ k ih =>
      intro z hz
      have hzB : z ∈ Metric.ball ((xs a b : ℂ)) δ := hz.1
      have hz0 : z ≠ 0 := fun h => hz.2 (by simp [h])
      have hz2 : z ≠ 2 := fun h => hz.2 (by simp [h])
      have hWne : z ^ 2 - 2 * z ≠ 0 := by
        have h : z * (z - 2) ≠ 0 := mul_ne_zero hz0 (sub_ne_zero.mpr hz2)
        rw [show z ^ 2 - 2 * z = z * (z - 2) from by ring]
        exact h
      have hdy : DifferentiableAt ℂ (DyIter k y1) z := (hDi k z hz).differentiableAt
      have h1 : (Dc a b k).eval₂ (algebraMap ℚ ℂ) z * DyIter k y1 z
          = (Ac a b k).eval₂ (algebraMap ℚ ℂ) z * y1 z
            + (Bc a b k).eval₂ (algebraMap ℚ ℂ) z * deriv y1 z := ih z hz
      have hder_eq : deriv (fun w => (Dc a b k).eval₂ (algebraMap ℚ ℂ) w * DyIter k y1 w) z
          = deriv (fun w => (Ac a b k).eval₂ (algebraMap ℚ ℂ) w * y1 w
              + (Bc a b k).eval₂ (algebraMap ℚ ℂ) w * deriv y1 w) z := by
        have hev : (fun w => (Dc a b k).eval₂ (algebraMap ℚ ℂ) w * DyIter k y1 w)
            =ᶠ[𝓝 z] (fun w => (Ac a b k).eval₂ (algebraMap ℚ ℂ) w * y1 w
              + (Bc a b k).eval₂ (algebraMap ℚ ℂ) w * deriv y1 w) := by
          filter_upwards [hGopen.mem_nhds hz] with w hw
          exact ih w hw
        exact hev.deriv_eq
      have hL : deriv (fun w => (Dc a b k).eval₂ (algebraMap ℚ ℂ) w * DyIter k y1 w) z
          = (Dc a b k).derivative.eval₂ (algebraMap ℚ ℂ) z * DyIter k y1 z
            + (Dc a b k).eval₂ (algebraMap ℚ ℂ) z * deriv (DyIter k y1) z :=
        deriv_mul_eval₂ _ _ _ hdy
      have hR : deriv (fun w => (Ac a b k).eval₂ (algebraMap ℚ ℂ) w * y1 w
              + (Bc a b k).eval₂ (algebraMap ℚ ℂ) w * deriv y1 w) z
          = (Ac a b k).derivative.eval₂ (algebraMap ℚ ℂ) z * y1 z
            + (Ac a b k).eval₂ (algebraMap ℚ ℂ) z * deriv y1 z
            + (Bc a b k).derivative.eval₂ (algebraMap ℚ ℂ) z * deriv y1 z
            + (Bc a b k).eval₂ (algebraMap ℚ ℂ) z * deriv (deriv y1) z := by
        have hfun : (fun w => (Ac a b k).eval₂ (algebraMap ℚ ℂ) w * y1 w
              + (Bc a b k).eval₂ (algebraMap ℚ ℂ) w * deriv y1 w)
            = (fun w => (Ac a b k).eval₂ (algebraMap ℚ ℂ) w * y1 w)
              + (fun w => (Bc a b k).eval₂ (algebraMap ℚ ℂ) w * deriv y1 w) := rfl
        rw [hfun,
            deriv_add (f := fun w => (Ac a b k).eval₂ (algebraMap ℚ ℂ) w * y1 w)
              (g := fun w => (Bc a b k).eval₂ (algebraMap ℚ ℂ) w * deriv y1 w)
              ((differentiableAt_eval₂ _ _).mul (hy1diff z hzB))
              ((differentiableAt_eval₂ _ _).mul (hdy1diff z hzB)),
            deriv_mul_eval₂ _ _ _ (hy1diff z hzB),
            deriv_mul_eval₂ _ _ _ (hdy1diff z hzB)]
        ring
      have h2 : (Dc a b k).derivative.eval₂ (algebraMap ℚ ℂ) z * DyIter k y1 z
            + (Dc a b k).eval₂ (algebraMap ℚ ℂ) z * deriv (DyIter k y1) z
          = (Ac a b k).derivative.eval₂ (algebraMap ℚ ℂ) z * y1 z
            + (Ac a b k).eval₂ (algebraMap ℚ ℂ) z * deriv y1 z
            + (Bc a b k).derivative.eval₂ (algebraMap ℚ ℂ) z * deriv y1 z
            + (Bc a b k).eval₂ (algebraMap ℚ ℂ) z * deriv (deriv y1) z :=
        hL.symm.trans (hder_eq.trans hR)
      have h3 : (P2x a b).eval₂ (algebraMap ℚ ℂ) z * deriv (deriv y1) z
            + (P1x a b).eval₂ (algebraMap ℚ ℂ) z * deriv y1 z
            + (P0x a b).eval₂ (algebraMap ℚ ℂ) z * y1 z = 0 := hode z hzB
      have hstep := ana_step h1 h2 h3
      have hWmul : (z ^ 2 - 2 * z) * ((z - 1) ^ 2 / (z ^ 2 - 2 * z)) = (z - 1) ^ 2 :=
        mul_div_cancel₀ _ hWne
      rw [show DyIter (k + 1) y1 z
            = deriv (DyIter k y1) z * (z - 1) ^ 2 / (z ^ 2 - 2 * z) from by
          simp [DyIter, Function.iterate_succ_apply', Dy],
        Dc_eval₂_succ, Ac_eval₂_succ, Bc_eval₂_succ]
      linear_combination (z - 1) ^ 2 * hstep
        + ((Dc a b k).eval₂ (algebraMap ℚ ℂ) z ^ 2 * (P2x a b).eval₂ (algebraMap ℚ ℂ) z
            * deriv (DyIter k y1) z) * hWmul

end

end Work.C17d
