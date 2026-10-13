import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.remov.TopCoreB.FarDefs
import Submission.Work.FTS.EllipticEst.remov.TopCoreB.FarHyp
import Submission.Work.FTS.EllipticEst.remov.TopCoreB.FarSlots
import Submission.Work.FTS.EllipticEst.remov.TopCoreB.sinDivDerivBounds
import Submission.Work.FTS.EllipticEst.remov.hardyDiv_fin
import Submission.Work.FTS.EllipticEst.remov.Lzero1_iteratedDeriv_eq
import Submission.Work.FTS.EllipticEst.remov.TopCoreB.FarReflect
import Submission.Work.FTS.EllipticEst.remov.TopCoreB.far_vBound
import Submission.Work.FTS.EllipticEst.remov.TopCoreB.FEL.uSlot_Icc_le_FarR

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov.TopCoreB

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## The auxiliary sums and the master algebraic identity for `A_b - T_b`

Writing `v = vF u = u / cos θ`, `Q = u^{(k+2)}` and
`Z`, `Y`, `W` for the three Leibniz remainders introduced below, the integrand of the lemma's
left-hand side satisfies the *exact* pointwise identity

`∂^{k+1}(tan θ·u)·u^{(k+2)} - tripleT k γ u
   = - X·Y + Q·(Z - Y) - (k+1)·(u^{(k)} + W)·((k+3)Q + (k+2)X + Y)`,
`X := 6u^{(k)} + g^{(k)} - Z`,

which is the form in which every term is controlled by the `u`-slots (orders `≤ k+1`), the
source slot `g^{(k)}` and the hypothesis' `v`-slots (orders `≤ k`) — in particular the
`(u^{(k+2)})²` terms cancel identically, so that only a `Young` budget of `1/32 < 1/16` on
`(u^{(k+2)})²` is needed.  All the pieces of the right-hand side carry coefficients bounded by
`C(k)` uniformly in `γ`, `u`, `g` and `b`. -/

/-- `iteratedDeriv (n+2) sin = - iteratedDeriv n sin`. -/
theorem iteratedDeriv_sin_add_two (n : ℕ) :
    iteratedDeriv (n + 2) Real.sin = -iteratedDeriv n Real.sin := by
  have h1 : iteratedDeriv (n + 2) Real.sin = iteratedDeriv (n + 1) Real.cos := by
    have h := iteratedDeriv_succ' (n := n + 1) (f := Real.sin)
    rwa [Real.deriv_sin] at h
  have h2 : iteratedDeriv (n + 1) Real.cos = -iteratedDeriv n Real.sin := by
    have h := iteratedDeriv_succ' (n := n) (f := Real.cos)
    have hcos : deriv Real.cos = fun x : ℝ => -Real.sin x := by
      funext x; exact Real.deriv_cos
    rw [hcos] at h
    have h3 : iteratedDeriv n (fun x : ℝ => -Real.sin x) = -iteratedDeriv n Real.sin := by
      funext x; exact iteratedDeriv_neg n Real.sin x
    rw [h3] at h
    exact h
  rw [h1, h2]

/-- `iteratedDeriv (n+2) cos = - iteratedDeriv n cos`. -/
theorem iteratedDeriv_cos_add_two (n : ℕ) :
    iteratedDeriv (n + 2) Real.cos = -iteratedDeriv n Real.cos := by
  have h1 : iteratedDeriv (n + 2) Real.cos = -iteratedDeriv (n + 1) Real.sin := by
    have h := iteratedDeriv_succ' (n := n + 1) (f := Real.cos)
    have hcos : deriv Real.cos = fun x : ℝ => -Real.sin x := by
      funext x; exact Real.deriv_cos
    rw [hcos] at h
    have h3 : iteratedDeriv (n + 1) (fun x : ℝ => -Real.sin x)
        = -iteratedDeriv (n + 1) Real.sin := by
      funext x; exact iteratedDeriv_neg (n + 1) Real.sin x
    rw [h3] at h
    exact h
  have h2 : iteratedDeriv (n + 1) Real.sin = iteratedDeriv n Real.cos := by
    have h := iteratedDeriv_succ' (n := n) (f := Real.sin)
    rwa [Real.deriv_sin] at h
  rw [h1, h2]

/-- All iterated derivatives of `sin` are bounded by `1`. -/
theorem abs_iteratedDeriv_sin_le_one (n : ℕ) (θ : ℝ) :
    |iteratedDeriv n Real.sin θ| ≤ 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simpa using Real.abs_sin_le_one θ
    | 1 => simpa using Real.abs_cos_le_one θ
    | (m + 2) =>
      rw [iteratedDeriv_sin_add_two m]
      simp only [Pi.neg_apply, abs_neg]
      exact ih m (by omega)

/-- All iterated derivatives of `cos` are bounded by `1`. -/
theorem abs_iteratedDeriv_cos_le_one (n : ℕ) (θ : ℝ) :
    |iteratedDeriv n Real.cos θ| ≤ 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simpa using Real.abs_cos_le_one θ
    | 1 =>
      have h : iteratedDeriv 1 Real.cos θ = -Real.sin θ := by
        rw [iteratedDeriv_one]; exact Real.deriv_cos
      rw [h, abs_neg]; exact Real.abs_sin_le_one θ
    | (m + 2) =>
      show |iteratedDeriv (m + 2) Real.cos θ| ≤ 1
      rw [iteratedDeriv_cos_add_two m]
      simp only [Pi.neg_apply, abs_neg]
      exact ih m (by omega)

/-- **Leibniz for `sin · X`, with the top-order term split off.**
For `X` of class `C^n` at `θ`,

`(sin · X)^{(n)}(θ) = sin θ · X^{(n)}(θ) + Σ_{r=1}^{n} C(n,r)·(sin)^{(r)}(θ)·X^{(n-r)}(θ)`. -/
theorem peel_sin {X : ℝ → ℝ} {n : ℕ} {θ : ℝ} (hX : ContDiffAt ℝ (n : ℕ∞ω) X θ) :
    iteratedDeriv n (fun t => Real.sin t * X t) θ
      = Real.sin θ * iteratedDeriv n X θ
        + ∑ r ∈ Finset.Icc 1 n, (n.choose r : ℝ) * iteratedDeriv r Real.sin θ
            * iteratedDeriv (n - r) X θ := by
  have hsin : ContDiffAt ℝ (n : ℕ∞ω) Real.sin θ := Real.contDiff_sin.contDiffAt
  have hfun : (fun t : ℝ => Real.sin t * X t) = Real.sin * X := rfl
  rw [hfun, iteratedDeriv_mul hsin hX]
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    simp
  · rw [Finset.sum_range_eq_add_Ico _ (Nat.succ_pos n)]
    rw [show Finset.Ico 1 n.succ = Finset.Icc 1 n from Finset.Ico_add_one_right_eq_Icc 1 n]
    rw [Nat.choose_zero_right, Nat.cast_one, iteratedDeriv_zero, Nat.sub_zero, one_mul]

/-- **Leibniz for `cos · X`, with the top-order term split off.**
For `X` of class `C^n` at `θ`,

`(cos · X)^{(n)}(θ) = cos θ · X^{(n)}(θ) + Σ_{j=1}^{n} C(n,j)·(cos)^{(j)}(θ)·X^{(n-j)}(θ)`. -/
theorem peel_cos {X : ℝ → ℝ} {n : ℕ} {θ : ℝ} (hX : ContDiffAt ℝ (n : ℕ∞ω) X θ) :
    iteratedDeriv n (fun t => Real.cos t * X t) θ
      = Real.cos θ * iteratedDeriv n X θ
        + ∑ j ∈ Finset.Icc 1 n, (n.choose j : ℝ) * iteratedDeriv j Real.cos θ
            * iteratedDeriv (n - j) X θ := by
  have hcos : ContDiffAt ℝ (n : ℕ∞ω) Real.cos θ := Real.contDiff_cos.contDiffAt
  have hfun : (fun t : ℝ => Real.cos t * X t) = Real.cos * X := rfl
  rw [hfun, iteratedDeriv_mul hcos hX]
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    simp
  · rw [Finset.sum_range_eq_add_Ico _ (Nat.succ_pos n)]
    rw [show Finset.Ico 1 n.succ = Finset.Icc 1 n from Finset.Ico_add_one_right_eq_Icc 1 n]
    rw [Nat.choose_zero_right, Nat.cast_one, iteratedDeriv_zero, Nat.sub_zero, one_mul]


/-! ## The three Leibniz remainders `Z`, `Y`, `W`, and `X = 6u^{(k)} + g^{(k)} - Z` -/

/-- The Leibniz remainder of `∂^{k+1}(sin θ · v)`: the sum of the terms with at least one
derivative falling on `sin` (`v = vF u = u / cos θ`). -/
def Zsum (k : ℕ) (u : ℝ → ℝ) : ℝ → ℝ := fun θ =>
  ∑ r ∈ Finset.Icc 1 (k + 1), ((k + 1).choose r : ℝ) * iteratedDeriv r Real.sin θ
    * iteratedDeriv (k + 1 - r) (vF u) θ

/-- The Leibniz remainder of `∂^{k+2}(cos θ · v)` beyond the `j = 0` and `j = 1` terms, with
the sign that makes `cos θ · v^{(k+2)} = u^{(k+2)} + (k+2)·sin θ v^{(k+1)} + Y`. -/
def Ysum (k : ℕ) (u : ℝ → ℝ) : ℝ → ℝ := fun θ =>
  -(∑ j ∈ Finset.Icc 2 (k + 2), ((k + 2).choose j : ℝ) * iteratedDeriv j Real.cos θ
    * iteratedDeriv (k + 2 - j) (vF u) θ)

/-- The Leibniz remainder of `∂^{k}(cos θ · v)`, with the sign that makes
`cos θ · v^{(k)} = u^{(k)} + W`. -/
def Wsum (k : ℕ) (u : ℝ → ℝ) : ℝ → ℝ := fun θ =>
  -(∑ j ∈ Finset.Icc 1 k, (k.choose j : ℝ) * iteratedDeriv j Real.cos θ
    * iteratedDeriv (k - j) (vF u) θ)

/-- `X = 6u^{(k)} + g^{(k)} - Z`, so that `sin θ · v^{(k+1)} = u^{(k+2)} + X`. -/
def Xsum (k : ℕ) (u g : ℝ → ℝ) : ℝ → ℝ := fun θ =>
  6 * iteratedDeriv k u θ + iteratedDeriv k g θ - Zsum k u θ

/-- `tan θ · u θ = sin θ · vF u θ` (both sides are `0` when `cos θ = 0`). -/
theorem tan_mul_eq_sin_mul_vF (u : ℝ → ℝ) :
    (fun t : ℝ => Real.tan t * u t) = fun t : ℝ => Real.sin t * vF u t := by
  funext t
  simp only [vF, Real.tan_eq_sin_div_cos]
  ring

/-- `u` agrees with `cos θ · vF u θ` on the open strip. -/
theorem eqOn_cos_mul_vF (u : ℝ → ℝ) :
    Set.EqOn u (fun θ => Real.cos θ * vF u θ) (Set.Ioo 0 (Real.pi / 2)) := by
  intro θ hθ
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  simp only [vF]
  field_simp

/-- `vF u` is `C^n` at every interior point, from `u ∈ C^{k+2}`. -/
theorem contDiffAt_vF {u : ℝ → ℝ} {k n : ℕ} (hu : ContDiffOn ℝ (k + 2) u (Set.Ioo 0 (Real.pi / 2)))
    (hn : n ≤ k + 2) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ContDiffAt ℝ (n : ℕ∞ω) (vF u) θ := by
  have hU : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2)) := isOpen_Ioo
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  have hu' : ContDiffAt ℝ (n : ℕ∞ω) u θ :=
    (hu.contDiffAt (hU.mem_nhds hθ)).of_le (by exact_mod_cast hn)
  have h := hu'.div Real.contDiff_cos.contDiffAt hcos
  rwa [show (u / Real.cos) = vF u from rfl] at h

/-- The differentiated ODE: `∂^{k+1}(tan θ·u) = u^{(k+2)} + 6u^{(k)} + g^{(k)}` on the open
strip, from `g = Lzero1 u`. -/
theorem iteratedDeriv_tan_mul_eq (k : ℕ) {u g : ℝ → ℝ}
    (hu : ContDiffOn ℝ (k + 2) u (Set.Ioo 0 (Real.pi / 2)))
    (hg : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), g θ = Work.FTS.EllipticEst.Lzero1 u θ) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      iteratedDeriv (k + 1) (fun t => Real.tan t * u t) θ
        = iteratedDeriv (k + 2) u θ + 6 * iteratedDeriv k u θ + iteratedDeriv k g θ := by
  intro θ hθ
  have hU : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2)) := isOpen_Ioo
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  have htan : ContDiffAt ℝ ((k + 1 : ℕ) : ℕ∞ω) Real.tan θ :=
    (Real.contDiffAt_tan (n := ((k + 1 : ℕ) : ℕ∞ω))).mpr hcos
  have hu1 : ContDiffAt ℝ ((k + 1 : ℕ) : ℕ∞ω) u θ :=
    (hu.contDiffAt (hU.mem_nhds hθ)).of_le (by exact_mod_cast (by omega : k + 1 ≤ k + 2))
  have hmul : iteratedDeriv (k + 1) (fun t => Real.tan t * u t) θ
      = ∑ i ∈ Finset.range (k + 2), ((k + 1).choose i : ℝ) * iteratedDeriv i Real.tan θ
          * iteratedDeriv (k + 1 - i) u θ := by
    rw [show (fun t : ℝ => Real.tan t * u t) = Real.tan * u from rfl, iteratedDeriv_mul htan hu1]
  have hL := Work.FTS.EllipticEst.remov.Lzero1_iteratedDeriv_eq k hu hg θ hθ
  rw [hmul]
  linarith [hL]

/-- **The peeled identity for the top `sin`-slot:**
`sin θ · v^{(k+1)} = u^{(k+2)} + X` on the open strip. -/
theorem sin_mul_vD_succ (k : ℕ) {u g : ℝ → ℝ}
    (hu : ContDiffOn ℝ (k + 2) u (Set.Ioo 0 (Real.pi / 2)))
    (hg : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), g θ = Work.FTS.EllipticEst.Lzero1 u θ) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Real.sin θ * iteratedDeriv (k + 1) (vF u) θ
        = iteratedDeriv (k + 2) u θ + Xsum k u g θ := by
  intro θ hθ
  have hpeel := peel_sin (X := vF u) (n := k + 1) (θ := θ) (contDiffAt_vF hu (by omega) hθ)
  have hode := iteratedDeriv_tan_mul_eq k hu hg θ hθ
  have h1 : iteratedDeriv (k + 1) (fun t : ℝ => Real.sin t * vF u t) θ
      = iteratedDeriv (k + 1) (fun t : ℝ => Real.tan t * u t) θ := by
    rw [tan_mul_eq_sin_mul_vF u]
  have hkey : iteratedDeriv (k + 2) u θ + 6 * iteratedDeriv k u θ + iteratedDeriv k g θ
      = Real.sin θ * iteratedDeriv (k + 1) (vF u) θ
        + ∑ r ∈ Finset.Icc 1 (k + 1), ((k + 1).choose r : ℝ) * iteratedDeriv r Real.sin θ
            * iteratedDeriv (k + 1 - r) (vF u) θ := by
    rw [← hpeel, h1, hode]
  simp only [Xsum, Zsum]
  linarith [hkey]

/-- **The peeled identity for the top `cos`-slot:**
`cos θ · v^{(k+2)} = u^{(k+2)} + (k+2)·sin θ v^{(k+1)} + Y` on the open strip. -/
theorem cos_mul_vD_succ (k : ℕ) {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ (k + 2) u (Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Real.cos θ * iteratedDeriv (k + 2) (vF u) θ
        = iteratedDeriv (k + 2) u θ + ((k : ℝ) + 2) * (Real.sin θ * iteratedDeriv (k + 1) (vF u) θ)
          + Ysum k u θ := by
  intro θ hθ
  have hpeel := peel_cos (X := vF u) (n := k + 2) (θ := θ) (contDiffAt_vF hu (by omega) hθ)
  have hEq : iteratedDeriv (k + 2) (fun θ => Real.cos θ * vF u θ) θ
      = iteratedDeriv (k + 2) u θ :=
    (Set.EqOn.iteratedDeriv_of_isOpen (fun θ hθ => (eqOn_cos_mul_vF u hθ).symm)
      isOpen_Ioo (k + 2)) hθ
  have hsplit : (∑ j ∈ Finset.Icc 1 (k + 2), ((k + 2).choose j : ℝ)
        * iteratedDeriv j Real.cos θ * iteratedDeriv (k + 2 - j) (vF u) θ)
      = ((k : ℝ) + 2) * (-Real.sin θ) * iteratedDeriv (k + 1) (vF u) θ
        + ∑ j ∈ Finset.Icc 2 (k + 2), ((k + 2).choose j : ℝ)
            * iteratedDeriv j Real.cos θ * iteratedDeriv (k + 2 - j) (vF u) θ := by
    rw [show Finset.Icc 1 (k + 2) = insert 1 (Finset.Icc 2 (k + 2)) from by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega,
      Finset.sum_insert (by simp)]
    have h1 : k + 2 - 1 = k + 1 := by omega
    rw [h1, iteratedDeriv_one, Real.deriv_cos, Nat.choose_one_right]
    push_cast
    ring
  have hkey : iteratedDeriv (k + 2) u θ
      = Real.cos θ * iteratedDeriv (k + 2) (vF u) θ
        + ((k : ℝ) + 2) * (-Real.sin θ) * iteratedDeriv (k + 1) (vF u) θ
        + ∑ j ∈ Finset.Icc 2 (k + 2), ((k + 2).choose j : ℝ)
            * iteratedDeriv j Real.cos θ * iteratedDeriv (k + 2 - j) (vF u) θ := by
    rw [← hEq, hpeel, hsplit]
    ring
  simp only [Ysum]
  linarith [hkey]

/-- **The peeled identity at order `k`:** `cos θ · v^{(k)} = u^{(k)} + W` on the open strip. -/
theorem cos_mul_vD_k (k : ℕ) {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ (k + 2) u (Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Real.cos θ * iteratedDeriv k (vF u) θ
        = iteratedDeriv k u θ + Wsum k u θ := by
  intro θ hθ
  have hpeel := peel_cos (X := vF u) (n := k) (θ := θ) (contDiffAt_vF hu (by omega) hθ)
  have hEq : iteratedDeriv k (fun θ => Real.cos θ * vF u θ) θ = iteratedDeriv k u θ :=
    (Set.EqOn.iteratedDeriv_of_isOpen (fun θ hθ => (eqOn_cos_mul_vF u hθ).symm)
      isOpen_Ioo k) hθ
  have hkey : iteratedDeriv k u θ = Real.cos θ * iteratedDeriv k (vF u) θ
      + ∑ j ∈ Finset.Icc 1 k, (k.choose j : ℝ) * iteratedDeriv j Real.cos θ
          * iteratedDeriv (k - j) (vF u) θ := by
    rw [← hEq, hpeel]
  simp only [Wsum]
  linarith [hkey]

/-- **The master algebraic identity.**  On the open strip,

`∂^{k+1}(tan θ·u)·u^{(k+2)} - tripleT k γ u
   = - X·Y + u^{(k+2)}·(Z - Y)
       - (k+1)·(u^{(k)} + W)·((k+3)u^{(k+2)} + (k+2)X + Y)`,

with `X = Xsum k u g`, `Y = Ysum k u`, `Z = Zsum k u`, `W = Wsum k u`. -/
theorem E_integrand_eq (k : ℕ) (γ : ℝ) {u g : ℝ → ℝ}
    (hu : ContDiffOn ℝ (k + 2) u (Set.Ioo 0 (Real.pi / 2)))
    (hg : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), g θ = Work.FTS.EllipticEst.Lzero1 u θ) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      iteratedDeriv (k + 1) (fun t => Real.tan t * u t) θ * iteratedDeriv (k + 2) u θ
          - tripleT k γ u θ
        = - Xsum k u g θ * Ysum k u θ
          + iteratedDeriv (k + 2) u θ * (Zsum k u θ - Ysum k u θ)
          - ((k : ℝ) + 1) * (iteratedDeriv k u θ + Wsum k u θ)
              * (((k : ℝ) + 3) * iteratedDeriv (k + 2) u θ
                  + ((k : ℝ) + 2) * Xsum k u g θ + Ysum k u θ) := by
  intro θ hθ
  have hode := iteratedDeriv_tan_mul_eq k hu hg θ hθ
  have hS := sin_mul_vD_succ k hu hg θ hθ
  have hC2 := cos_mul_vD_succ k hu θ hθ
  have hCk := cos_mul_vD_k k hu θ hθ
  -- rewrite `tripleT` in terms of the three products `sin θ v^{(k+1)}`, `cos θ v^{(k+2)}`,
  -- `cos θ v^{(k)}`
  have hT : tripleT k γ u θ
      = (Real.sin θ * iteratedDeriv (k + 1) (vF u) θ)
          * (Real.cos θ * iteratedDeriv (k + 2) (vF u) θ)
        - ((k : ℝ) + 2) * (Real.sin θ * iteratedDeriv (k + 1) (vF u) θ) ^ 2
        + ((k : ℝ) + 1) * (Real.cos θ * iteratedDeriv k (vF u) θ)
          * (Real.cos θ * iteratedDeriv (k + 2) (vF u) θ) := by
    simp only [tripleT]
    ring
  simp only [hT, hode, hS, hC2, hCk, Xsum]
  ring


/-! ## The constants and the pointwise estimate -/

/-- The product `(k+1)(k+3)`, the natural coefficient of the `W`-block. -/
def KW (k : ℕ) : ℝ := ((k : ℝ) + 1) * ((k : ℝ) + 3)

/-- The product `(k+1)(k+2)²`, the natural coefficient of the `u^{(k)}`-block. -/
def KUv (k : ℕ) : ℝ := ((k : ℝ) + 1) * ((k : ℝ) + 2) ^ 2

/-- Cauchy–Schwarz constant attached to the `Z`-sum (`k+1` terms, coefficients `≤ 2^(k+1)`). -/
def KapZ (k : ℕ) : ℝ := ((k : ℝ) + 1) * (4 : ℝ) ^ (k + 1)

/-- Cauchy–Schwarz constant attached to the `Y`-sum. -/
def KapY (k : ℕ) : ℝ := ((k : ℝ) + 1) * (4 : ℝ) ^ (k + 2)

/-- Cauchy–Schwarz constant attached to the `W`-sum. -/
def KapW (k : ℕ) : ℝ := (k : ℝ) * (4 : ℝ) ^ k

/-- Coefficient of `(u^{(k)})²` in the pointwise estimate. -/
def CU (k : ℕ) : ℝ := 54 + 64 * KW k ^ 2 + ((k : ℝ) + 1) + 108 * KUv k

/-- Coefficient of `(g^{(k)})²` in the pointwise estimate. -/
def CG (k : ℕ) : ℝ := 3 / 2 + 3 * KUv k

/-- Coefficient multiplying the `Z`-sum, before Cauchy–Schwarz. -/
def CZt (k : ℕ) : ℝ := 131 / 2 + 3 * KUv k

/-- Coefficient multiplying the `Y`-sum, before Cauchy–Schwarz. -/
def CYt (k : ℕ) : ℝ := 129 / 2 + ((k : ℝ) + 1)

/-- Coefficient multiplying the `W`-sum, before Cauchy–Schwarz. -/
def CWt (k : ℕ) : ℝ := 64 * KW k ^ 2 + ((k : ℝ) + 1)

/-- Coefficient of the `Z`-sum in the pointwise estimate. -/
def CS1 (k : ℕ) : ℝ := CZt k * KapZ k

/-- Coefficient of the `Y`-sum in the pointwise estimate. -/
def CS2 (k : ℕ) : ℝ := CYt k * KapY k

/-- Coefficient of the `W`-sum in the pointwise estimate. -/
def CS3 (k : ℕ) : ℝ := CWt k * KapW k

/-- The final constant of the estimate, for a given `Cv` (the constant of the slot hypothesis). -/
def CFinal (k : ℕ) (Cv : ℝ) : ℝ :=
  1 + CU k + CG k + CS1 k * ((k : ℝ) + 1) * Cv + CS2 k * ((k : ℝ) + 1) * Cv
    + CS3 k * (k : ℝ) * Cv

theorem KW_nonneg (k : ℕ) : 0 ≤ KW k := by rw [KW]; positivity

theorem KUv_nonneg (k : ℕ) : 0 ≤ KUv k := by rw [KUv]; positivity

theorem KapZ_nonneg (k : ℕ) : 0 ≤ KapZ k := by rw [KapZ]; positivity

theorem KapY_nonneg (k : ℕ) : 0 ≤ KapY k := by rw [KapY]; positivity

theorem KapW_nonneg (k : ℕ) : 0 ≤ KapW k := by
  rw [KapW]; exact mul_nonneg (Nat.cast_nonneg k) (by positivity)

theorem CZt_nonneg (k : ℕ) : 0 ≤ CZt k := by
  rw [CZt]; have := KUv_nonneg k; linarith

theorem CYt_nonneg (k : ℕ) : 0 ≤ CYt k := by
  rw [CYt]; have h : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k; linarith

theorem CWt_nonneg (k : ℕ) : 0 ≤ CWt k := by
  rw [CWt]; have := KW_nonneg k; nlinarith

theorem CU_nonneg (k : ℕ) : 0 ≤ CU k := by
  rw [CU]; have h1 := KW_nonneg k; have h2 := KUv_nonneg k; nlinarith

theorem CG_nonneg (k : ℕ) : 0 ≤ CG k := by
  rw [CG]; have h2 := KUv_nonneg k; nlinarith

theorem CS1_nonneg (k : ℕ) : 0 ≤ CS1 k := by
  rw [CS1]; exact mul_nonneg (CZt_nonneg k) (KapZ_nonneg k)

theorem CS2_nonneg (k : ℕ) : 0 ≤ CS2 k := by
  rw [CS2]; exact mul_nonneg (CYt_nonneg k) (KapY_nonneg k)

theorem CS3_nonneg (k : ℕ) : 0 ≤ CS3 k := by
  rw [CS3]; exact mul_nonneg (CWt_nonneg k) (KapW_nonneg k)

theorem choose_le_two_pow (n i : ℕ) : n.choose i ≤ 2 ^ n := by
  by_cases hi : i ≤ n
  · calc n.choose i ≤ ∑ j ∈ Finset.range (n + 1), n.choose j :=
        Finset.single_le_sum (fun j _ => Nat.zero_le _)
          (by simp only [Finset.mem_range]; omega)
      _ = 2 ^ n := Nat.sum_range_choose n
  · rw [Nat.choose_eq_zero_of_lt (by omega)]; exact Nat.zero_le _

/-- Cauchy–Schwarz for a sum of products `c i * σ i * v i` with `|σ i| ≤ 1` and `c i ≤ A`. -/
theorem sumsq_le_of {ι : Type*} (s : Finset ι) (c σ v : ι → ℝ) (A B : ℝ)
    (hA : 0 ≤ A) (hc : ∀ i ∈ s, c i ≤ A) (hc0 : ∀ i ∈ s, 0 ≤ c i)
    (hσ : ∀ i ∈ s, |σ i| ≤ 1) (hcard : ((s.card : ℕ) : ℝ) ≤ B) :
    (∑ i ∈ s, c i * σ i * v i) ^ 2 ≤ (A ^ 2 * B) * ∑ i ∈ s, (v i) ^ 2 := by
  have hterm : ∀ i ∈ s, (c i * σ i * v i) ^ 2 ≤ A ^ 2 * (v i) ^ 2 := by
    intro i hi
    have h1 : c i ≤ A := hc i hi
    have h2 : 0 ≤ c i := hc0 i hi
    have h3 : (σ i) ^ 2 ≤ 1 := by
      have h := hσ i hi
      nlinarith [abs_nonneg (σ i), sq_abs (σ i)]
    have h4 : 0 ≤ (v i) ^ 2 := sq_nonneg _
    have h5 : (c i) ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ h2 h1 2
    calc (c i * σ i * v i) ^ 2 = (c i) ^ 2 * (σ i) ^ 2 * (v i) ^ 2 := by ring
      _ ≤ A ^ 2 * 1 * (v i) ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul h5 h3 (by positivity) (by positivity)) h4
      _ = A ^ 2 * (v i) ^ 2 := by ring
  calc (∑ i ∈ s, c i * σ i * v i) ^ 2
      ≤ ((s.card : ℕ) : ℝ) * ∑ i ∈ s, (c i * σ i * v i) ^ 2 := sq_sum_le_card_mul_sum_sq
    _ ≤ ((s.card : ℕ) : ℝ) * ∑ i ∈ s, A ^ 2 * (v i) ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (by positivity)
    _ = ((s.card : ℕ) : ℝ) * (A ^ 2 * ∑ i ∈ s, (v i) ^ 2) := by
        congr 1
        rw [Finset.mul_sum]
    _ ≤ (A ^ 2 * B) * ∑ i ∈ s, (v i) ^ 2 := by
        have hsum : 0 ≤ ∑ i ∈ s, (v i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
        have hkey : ((s.card : ℕ) : ℝ) * A ^ 2 ≤ A ^ 2 * B := by nlinarith [hA, hcard]
        calc ((s.card : ℕ) : ℝ) * (A ^ 2 * ∑ i ∈ s, (v i) ^ 2)
            = (((s.card : ℕ) : ℝ) * A ^ 2) * ∑ i ∈ s, (v i) ^ 2 := by ring
          _ ≤ (A ^ 2 * B) * ∑ i ∈ s, (v i) ^ 2 := mul_le_mul_of_nonneg_right hkey hsum

theorem Zsum_sq_le (k : ℕ) (u : ℝ → ℝ) (θ : ℝ) :
    (Zsum k u θ) ^ 2
      ≤ KapZ k * ∑ r ∈ Finset.Icc 1 (k + 1), (iteratedDeriv (k + 1 - r) (vF u) θ) ^ 2 := by
  have hcard : (((Finset.Icc 1 (k + 1)).card : ℕ) : ℝ) ≤ (k : ℝ) + 1 := by simp
  have h := sumsq_le_of (Finset.Icc 1 (k + 1)) (fun r => ((k + 1).choose r : ℝ))
    (fun r => iteratedDeriv r Real.sin θ) (fun r => iteratedDeriv (k + 1 - r) (vF u) θ)
    ((2 : ℝ) ^ (k + 1)) ((k : ℝ) + 1) (by positivity)
    (fun r _ => by exact_mod_cast choose_le_two_pow (k + 1) r)
    (fun r _ => by positivity) (fun r _ => abs_iteratedDeriv_sin_le_one r θ) hcard
  rw [Zsum]
  have h2 : ((2 : ℝ) ^ (k + 1)) ^ 2 = (4 : ℝ) ^ (k + 1) := by
    rw [← pow_mul, show (k + 1) * 2 = 2 * (k + 1) from by ring, pow_mul]
    norm_num
  refine h.trans_eq ?_
  rw [KapZ, h2]
  ring

theorem Ysum_sq_le (k : ℕ) (u : ℝ → ℝ) (θ : ℝ) :
    (Ysum k u θ) ^ 2
      ≤ KapY k * ∑ j ∈ Finset.Icc 2 (k + 2), (iteratedDeriv (k + 2 - j) (vF u) θ) ^ 2 := by
  have hcard : (((Finset.Icc 2 (k + 2)).card : ℕ) : ℝ) ≤ (k : ℝ) + 1 := by simp
  have h := sumsq_le_of (Finset.Icc 2 (k + 2)) (fun j => ((k + 2).choose j : ℝ))
    (fun j => iteratedDeriv j Real.cos θ) (fun j => iteratedDeriv (k + 2 - j) (vF u) θ)
    ((2 : ℝ) ^ (k + 2)) ((k : ℝ) + 1) (by positivity)
    (fun j _ => by exact_mod_cast choose_le_two_pow (k + 2) j)
    (fun j _ => by positivity) (fun j _ => abs_iteratedDeriv_cos_le_one j θ) hcard
  rw [Ysum]
  have hneg : ∀ x : ℝ, (-x) ^ 2 = x ^ 2 := fun x => by ring
  rw [hneg]
  have h2 : ((2 : ℝ) ^ (k + 2)) ^ 2 = (4 : ℝ) ^ (k + 2) := by
    rw [← pow_mul, show (k + 2) * 2 = 2 * (k + 2) from by ring, pow_mul]
    norm_num
  refine h.trans_eq ?_
  rw [KapY, h2]
  ring

theorem Wsum_sq_le (k : ℕ) (u : ℝ → ℝ) (θ : ℝ) :
    (Wsum k u θ) ^ 2
      ≤ KapW k * ∑ j ∈ Finset.Icc 1 k, (iteratedDeriv (k - j) (vF u) θ) ^ 2 := by
  have hcard : (((Finset.Icc 1 k).card : ℕ) : ℝ) ≤ (k : ℝ) := by simp
  have h := sumsq_le_of (Finset.Icc 1 k) (fun j => (k.choose j : ℝ))
    (fun j => iteratedDeriv j Real.cos θ) (fun j => iteratedDeriv (k - j) (vF u) θ)
    ((2 : ℝ) ^ k) ((k : ℝ)) (by positivity)
    (fun j _ => by exact_mod_cast choose_le_two_pow k j)
    (fun j _ => by positivity) (fun j _ => abs_iteratedDeriv_cos_le_one j θ) hcard
  rw [Wsum]
  have hneg : ∀ x : ℝ, (-x) ^ 2 = x ^ 2 := fun x => by ring
  rw [hneg]
  have h2 : ((2 : ℝ) ^ k) ^ 2 = (4 : ℝ) ^ k := by
    rw [← pow_mul, show k * 2 = 2 * k from by ring, pow_mul]
    norm_num
  refine h.trans_eq ?_
  rw [KapW, h2]
  ring

/-- **The pointwise estimate.**  On the open strip the integrand of the lemma's left-hand side
is bounded by the six groups of terms used in the integral estimate. -/
theorem E_pointwise (k : ℕ) (γ : ℝ) {u g : ℝ → ℝ}
    (hu : ContDiffOn ℝ (k + 2) u (Set.Ioo 0 (Real.pi / 2)))
    (hg : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), g θ = Work.FTS.EllipticEst.Lzero1 u θ) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      iteratedDeriv (k + 1) (fun t => Real.tan t * u t) θ * iteratedDeriv (k + 2) u θ
          - tripleT k γ u θ
        ≤ 3 / 64 * (iteratedDeriv (k + 2) u θ) ^ 2
          + CU k * (iteratedDeriv k u θ) ^ 2
          + CG k * (iteratedDeriv k g θ) ^ 2
          + CS1 k * ∑ r ∈ Finset.Icc 1 (k + 1), (iteratedDeriv (k + 1 - r) (vF u) θ) ^ 2
          + CS2 k * ∑ j ∈ Finset.Icc 2 (k + 2), (iteratedDeriv (k + 2 - j) (vF u) θ) ^ 2
          + CS3 k * ∑ j ∈ Finset.Icc 1 k, (iteratedDeriv (k - j) (vF u) θ) ^ 2 := by
  intro θ hθ
  have hE := E_integrand_eq k γ hu hg θ hθ
  have hZb := Zsum_sq_le k u θ
  have hYb := Ysum_sq_le k u θ
  have hWb := Wsum_sq_le k u θ
  set X : ℝ := Xsum k u g θ with hX
  set Y : ℝ := Ysum k u θ with hY
  set Z : ℝ := Zsum k u θ with hZ
  set W : ℝ := Wsum k u θ with hW
  set Q : ℝ := iteratedDeriv (k + 2) u θ with hQ
  set Uk : ℝ := iteratedDeriv k u θ with hUk
  set Gk : ℝ := iteratedDeriv k g θ with hGk
  set S1 : ℝ := ∑ r ∈ Finset.Icc 1 (k + 1), (iteratedDeriv (k + 1 - r) (vF u) θ) ^ 2 with hS1
  set S2 : ℝ := ∑ j ∈ Finset.Icc 2 (k + 2), (iteratedDeriv (k + 2 - j) (vF u) θ) ^ 2 with hS2
  set S3 : ℝ := ∑ j ∈ Finset.Icc 1 k, (iteratedDeriv (k - j) (vF u) θ) ^ 2 with hS3
  have hXdef : X = 6 * Uk + Gk - Z := by rw [hX, hUk, hGk, hZ]; simp only [Xsum]
  have hZb' : Z ^ 2 ≤ KapZ k * S1 := by rw [hZ, hS1]; exact hZb
  have hYb' : Y ^ 2 ≤ KapY k * S2 := by rw [hY, hS2]; exact hYb
  have hWb' : W ^ 2 ≤ KapW k * S3 := by rw [hW, hS3]; exact hWb
  have hS1nn : 0 ≤ S1 := by rw [hS1]; exact Finset.sum_nonneg fun r _ => sq_nonneg _
  have hS2nn : 0 ≤ S2 := by rw [hS2]; exact Finset.sum_nonneg fun j _ => sq_nonneg _
  have hS3nn : 0 ≤ S3 := by rw [hS3]; exact Finset.sum_nonneg fun j _ => sq_nonneg _
  -- the master identity in the abbreviated notation
  have hE' : iteratedDeriv (k + 1) (fun t => Real.tan t * u t) θ * Q - tripleT k γ u θ
      = -X * Y + Q * (Z - Y)
        - ((k : ℝ) + 1) * (Uk + W) * (((k : ℝ) + 3) * Q + ((k : ℝ) + 2) * X + Y) := by
    exact hE
  have hsplit : -X * Y + Q * (Z - Y)
        - ((k : ℝ) + 1) * (Uk + W) * (((k : ℝ) + 3) * Q + ((k : ℝ) + 2) * X + Y)
      = -X * Y + Q * (Z - Y)
        + (-(((k : ℝ) + 1) * (Uk + W) * (((k : ℝ) + 3) * Q)))
        + (-(((k : ℝ) + 1) * (Uk + W) * (((k : ℝ) + 2) * X + Y))) := by ring
  rw [hE', hsplit]
  -- the elementary bounds
  have hXY : -X * Y ≤ (X ^ 2 + Y ^ 2) / 2 := by
    nlinarith [sq_nonneg (|X| - |Y|), sq_abs X, sq_abs Y, neg_le_abs (X * Y), abs_mul X Y]
  have hA : Q * (Z - Y) ≤ (1 / 128) * Q ^ 2 + 32 * (Z - Y) ^ 2 := by
    nlinarith [sq_nonneg (Q - 64 * (Z - Y))]
  have hB : -(((k : ℝ) + 1) * (Uk + W) * (((k : ℝ) + 3) * Q))
      ≤ (1 / 128) * Q ^ 2 + 32 * KW k ^ 2 * (Uk + W) ^ 2 := by
    have hkey : KW k * (Uk + W) * Q
        = ((k : ℝ) + 1) * (Uk + W) * (((k : ℝ) + 3) * Q) := by rw [KW]; ring
    have h1 : -(((k : ℝ) + 1) * (Uk + W) * (((k : ℝ) + 3) * Q))
        ≤ |KW k * (Uk + W)| * |Q| := by
      rw [← hkey, ← abs_mul]
      exact neg_le_abs _
    have h2 : |KW k * (Uk + W)| * |Q| ≤ (1 / 128) * Q ^ 2 + 32 * (KW k * (Uk + W)) ^ 2 := by
      nlinarith [sq_nonneg (|Q| - 64 * |KW k * (Uk + W)|), sq_abs Q, sq_abs (KW k * (Uk + W))]
    have h3 : (KW k * (Uk + W)) ^ 2 = KW k ^ 2 * (Uk + W) ^ 2 := by ring
    linarith [h1, h2, h3.le, h3.ge]
  have hC : -(((k : ℝ) + 1) * (Uk + W) * (((k : ℝ) + 2) * X + Y))
      ≤ ((k : ℝ) + 1) / 2 * ((Uk + W) ^ 2 + (((k : ℝ) + 2) * X + Y) ^ 2) := by
    have hk1' : 0 ≤ ((k : ℝ) + 1) := by positivity
    have h1 : -(((k : ℝ) + 1) * (Uk + W) * (((k : ℝ) + 2) * X + Y))
        ≤ ((k : ℝ) + 1) * |(Uk + W)| * |((k : ℝ) + 2) * X + Y| := by
      have habs : ((k : ℝ) + 1) * |(Uk + W)| * |((k : ℝ) + 2) * X + Y|
          = |((k : ℝ) + 1) * (Uk + W) * (((k : ℝ) + 2) * X + Y)| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hk1']
      rw [habs]
      exact neg_le_abs _
    have h2 : |(Uk + W)| * |((k : ℝ) + 2) * X + Y| ≤ ((Uk + W) ^ 2 + (((k : ℝ) + 2) * X + Y) ^ 2) / 2 := by
      nlinarith [sq_nonneg (|Uk + W| - |((k : ℝ) + 2) * X + Y|), sq_abs (Uk + W),
        sq_abs (((k : ℝ) + 2) * X + Y)]
    have hk1 : 0 ≤ ((k : ℝ) + 1) := by positivity
    nlinarith [h1, h2]
  have hX2 : X ^ 2 ≤ 108 * Uk ^ 2 + 3 * Gk ^ 2 + 3 * Z ^ 2 := by
    rw [hXdef]
    nlinarith [sq_nonneg (6 * Uk - Gk), sq_nonneg (Gk + Z), sq_nonneg (6 * Uk + Z)]
  have hZY : (Z - Y) ^ 2 ≤ 2 * Z ^ 2 + 2 * Y ^ 2 := by nlinarith [sq_nonneg (Z + Y)]
  have hUW : (Uk + W) ^ 2 ≤ 2 * Uk ^ 2 + 2 * W ^ 2 := by nlinarith [sq_nonneg (Uk - W)]
  have hcross : (((k : ℝ) + 2) * X + Y) ^ 2 ≤ 2 * ((k : ℝ) + 2) ^ 2 * X ^ 2 + 2 * Y ^ 2 := by
    nlinarith [sq_nonneg (((k : ℝ) + 2) * X - Y)]
  -- scaled versions with the coefficients appearing in the goal
  have hXYs : (X ^ 2 + Y ^ 2) / 2 ≤ 54 * Uk ^ 2 + (3 / 2) * Gk ^ 2 + (3 / 2) * Z ^ 2 + (1 / 2) * Y ^ 2 := by
    linarith [hX2]
  have hZs : 32 * (Z - Y) ^ 2 ≤ 64 * Z ^ 2 + 64 * Y ^ 2 := by linarith [hZY]
  have hWs : 32 * KW k ^ 2 * (Uk + W) ^ 2 ≤ 64 * KW k ^ 2 * Uk ^ 2 + 64 * KW k ^ 2 * W ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hUW (show 0 ≤ 32 * KW k ^ 2 by positivity)
    linarith [h]
  have hUs : ((k : ℝ) + 1) / 2 * ((Uk + W) ^ 2 + (((k : ℝ) + 2) * X + Y) ^ 2)
      ≤ ((k : ℝ) + 1) * Uk ^ 2 + ((k : ℝ) + 1) * W ^ 2
        + ((k : ℝ) + 1) * (((k : ℝ) + 2) * X + Y) ^ 2 / 2 := by
    have h := mul_le_mul_of_nonneg_left hUW (show 0 ≤ ((k : ℝ) + 1) / 2 by positivity)
    linarith [h]
  have hcrosss : ((k : ℝ) + 1) * (((k : ℝ) + 2) * X + Y) ^ 2 / 2
      ≤ KUv k * X ^ 2 + ((k : ℝ) + 1) * Y ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hcross (show 0 ≤ ((k : ℝ) + 1) by positivity)
    rw [KUv]
    linarith [h]
  have hXcs : KUv k * X ^ 2 ≤ 108 * KUv k * Uk ^ 2 + 3 * KUv k * Gk ^ 2 + 3 * KUv k * Z ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hX2 (KUv_nonneg k)
    calc KUv k * X ^ 2 ≤ KUv k * (108 * Uk ^ 2 + 3 * Gk ^ 2 + 3 * Z ^ 2) := h
      _ = 108 * KUv k * Uk ^ 2 + 3 * KUv k * Gk ^ 2 + 3 * KUv k * Z ^ 2 := by ring
  -- the scaled Cauchy–Schwarz bounds, already in the coefficient form of the final goal
  have hZsc0 : CZt k * Z ^ 2 ≤ CS1 k * S1 := by
    rw [CS1, mul_assoc]
    exact mul_le_mul_of_nonneg_left hZb' (CZt_nonneg k)
  have hYsc0 : CYt k * Y ^ 2 ≤ CS2 k * S2 := by
    rw [CS2, mul_assoc]
    exact mul_le_mul_of_nonneg_left hYb' (CYt_nonneg k)
  have hWsc0 : CWt k * W ^ 2 ≤ CS3 k * S3 := by
    rw [CS3, mul_assoc]
    exact mul_le_mul_of_nonneg_left hWb' (CWt_nonneg k)
  have e_CU : CU k * Uk ^ 2
      = 54 * Uk ^ 2 + 64 * KW k ^ 2 * Uk ^ 2 + ((k : ℝ) + 1) * Uk ^ 2
        + 108 * KUv k * Uk ^ 2 := by rw [CU]; ring
  have e_CG : CG k * Gk ^ 2 = (3 / 2) * Gk ^ 2 + 3 * KUv k * Gk ^ 2 := by rw [CG]; ring
  have e_CZ : CZt k * Z ^ 2 = (131 / 2) * Z ^ 2 + 3 * KUv k * Z ^ 2 := by rw [CZt]; ring
  have e_CY : CYt k * Y ^ 2 = (129 / 2) * Y ^ 2 + ((k : ℝ) + 1) * Y ^ 2 := by rw [CYt]; ring
  have e_CW : CWt k * W ^ 2 = 64 * KW k ^ 2 * W ^ 2 + ((k : ℝ) + 1) * W ^ 2 := by rw [CWt]; ring
  have e_S1 : CS1 k * S1 = CZt k * KapZ k * S1 := by rw [CS1]
  have e_S2 : CS2 k * S2 = CYt k * KapY k * S2 := by rw [CS2]
  have e_S3 : CS3 k * S3 = CWt k * KapW k * S3 := by rw [CS3]
  have hZsc : (131 / 2) * Z ^ 2 + 3 * KUv k * Z ^ 2 ≤ CZt k * KapZ k * S1 := by
    rw [e_CZ, e_S1] at hZsc0
    exact hZsc0
  have hYsc : (129 / 2) * Y ^ 2 + ((k : ℝ) + 1) * Y ^ 2 ≤ CYt k * KapY k * S2 := by
    rw [e_CY, e_S2] at hYsc0
    exact hYsc0
  have hWsc : 64 * KW k ^ 2 * W ^ 2 + ((k : ℝ) + 1) * W ^ 2 ≤ CWt k * KapW k * S3 := by
    rw [e_CW, e_S3] at hWsc0
    exact hWsc0
  have hchain : -X * Y + Q * (Z - Y)
        + (-(((k : ℝ) + 1) * (Uk + W) * (((k : ℝ) + 3) * Q)))
        + (-(((k : ℝ) + 1) * (Uk + W) * (((k : ℝ) + 2) * X + Y)))
      ≤ (1 / 64) * Q ^ 2
        + (54 * Uk ^ 2 + (3 / 2) * Gk ^ 2 + (3 / 2) * Z ^ 2 + (1 / 2) * Y ^ 2)
        + (64 * Z ^ 2 + 64 * Y ^ 2)
        + (64 * KW k ^ 2 * Uk ^ 2 + 64 * KW k ^ 2 * W ^ 2)
        + (((k : ℝ) + 1) * Uk ^ 2 + ((k : ℝ) + 1) * W ^ 2
            + KUv k * X ^ 2 + ((k : ℝ) + 1) * Y ^ 2) := by
    linarith [hXY, hA, hB, hC, hXYs, hZs, hWs, hUs, hcrosss]
  have hfinal : (1 / 64) * Q ^ 2
        + (54 * Uk ^ 2 + (3 / 2) * Gk ^ 2 + (3 / 2) * Z ^ 2 + (1 / 2) * Y ^ 2)
        + (64 * Z ^ 2 + 64 * Y ^ 2)
        + (64 * KW k ^ 2 * Uk ^ 2 + 64 * KW k ^ 2 * W ^ 2)
        + (((k : ℝ) + 1) * Uk ^ 2 + ((k : ℝ) + 1) * W ^ 2
            + KUv k * X ^ 2 + ((k : ℝ) + 1) * Y ^ 2)
      ≤ 3 / 64 * Q ^ 2 + CU k * Uk ^ 2 + CG k * Gk ^ 2 + CZt k * Z ^ 2 + CYt k * Y ^ 2
        + CWt k * W ^ 2 := by
    rw [e_CU, e_CG, e_CZ, e_CY, e_CW]
    nlinarith [hXcs, KUv_nonneg k, sq_nonneg Uk, sq_nonneg Gk, sq_nonneg Z, sq_nonneg Y,
      sq_nonneg W, sq_nonneg X, sq_nonneg Q]
  rw [e_S1, e_S2, e_S3]
  linarith [hchain, hfinal, hZsc, hYsc, hWsc]


/-! ## Continuity and the interval estimate -/

/-- `iteratedDeriv m f` is continuous wherever `f` is `C^n`. -/
theorem continuousOn_iteratedDeriv_of_contDiffOn {n m : ℕ} {f : ℝ → ℝ} {s : Set ℝ}
    (hs : IsOpen s) (hf : ContDiffOn ℝ n f s) (hm : m ≤ n) :
    ContinuousOn (iteratedDeriv m f) s := by
  have h1 : ContinuousOn (iteratedDerivWithin m f s) s :=
    hf.continuousOn_iteratedDerivWithin (by exact_mod_cast hm) hs.uniqueDiffOn
  refine h1.congr fun x hx => ?_
  exact (iteratedDerivWithin_eq_iteratedDeriv hs.uniqueDiffOn
    ((hf.contDiffAt (hs.mem_nhds hx)).of_le (by exact_mod_cast hm)) hx).symm

/-- `vF u = u / cos` is `C^n` on the open strip as soon as `u` is. -/
theorem contDiffOn_vF {n : ℕ} {u : ℝ → ℝ} (hu : ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ n (vF u) (Set.Ioo 0 (Real.pi / 2)) := by
  have hcos : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.cos θ ≠ 0 := fun θ hθ =>
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩).ne'
  have h := hu.div Real.contDiff_cos.contDiffOn hcos
  rwa [show (u / Real.cos) = vF u from rfl] at h

/-- `tan · u` is `C^n` on the open strip as soon as `u` is. -/
theorem contDiffOn_tan_mul {n : ℕ} {u : ℝ → ℝ} (hu : ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ n (fun t => Real.tan t * u t) (Set.Ioo 0 (Real.pi / 2)) := by
  have hcos : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.cos θ ≠ 0 := fun θ hθ =>
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩).ne'
  have htan : ContDiffOn ℝ n Real.tan (Set.Ioo 0 (Real.pi / 2)) := fun x hx =>
    ((Real.contDiffAt_tan (n := (n : ℕ∞ω))).mpr (hcos x hx)).contDiffWithinAt
  exact htan.mul hu

/-- The weight `qW k γ` is continuous on a compact sub-interval of the open strip. -/
theorem continuousOn_qW {k : ℕ} {γ a b : ℝ} (ha : 0 < a) (hb : b < Real.pi / 2) :
    ContinuousOn (qW k γ) (Set.Icc a b) := by
  have hsin2 : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Icc a b) :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id))).continuousOn
  have hpos : ∀ θ ∈ Set.Icc a b, Real.sin (2 * θ) ≠ 0 := by
    intro θ hθ
    exact (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, ha])
      (by linarith [hθ.2, hb])).ne'
  have hc : ContinuousOn (fun _ : ℝ => (2 * (k : ℝ) - γ)) (Set.Icc a b) := continuousOn_const
  have h := ContinuousOn.rpow hsin2 hc (fun θ hθ => Or.inl (hpos θ hθ))
  exact h.congr fun θ _ => rfl

/-- The `g^{(k)}`-slot on a compact sub-interval of the far window. -/
theorem gSlot_Icc_le_FarR (k : ℕ) (hk : 2 ≤ k) {γ : ℝ} {u g : ℝ → ℝ} (h : FarHyp k γ u g)
    {a b : ℝ} (ha : 3 * Real.pi / 8 ≤ a) (hab : a ≤ b) (hb : b ≤ Real.pi / 2) :
    (∫ θ in Set.Icc a b, (iteratedDeriv k g θ) ^ 2 * qW k γ θ) ≤ FarR k γ u g := by
  have hsub : Set.Icc a b ⊆ farSet := fun x hx =>
    ⟨by linarith [hx.1, ha], by linarith [hx.2, hb]⟩
  have hIntFar : MeasureTheory.IntegrableOn
      (fun θ => (iteratedDeriv k g θ) ^ 2 * qW k γ θ) farSet :=
    h.hH2.mono_set farSet_subset_Iθ
  have hnn : ∀ᵐ θ ∂(volume.restrict farSet), 0 ≤ (iteratedDeriv k g θ) ^ 2 * qW k γ θ := by
    filter_upwards [MeasureTheory.ae_restrict_mem (μ := volume)
      (show MeasurableSet farSet from measurableSet_Icc)] with θ hθ
    exact mul_nonneg (sq_nonneg _) (qW_nonneg (farSet_subset_Iθ hθ))
  have h1 : (∫ θ in Set.Icc a b, (iteratedDeriv k g θ) ^ 2 * qW k γ θ)
      ≤ ∫ θ in farSet, (iteratedDeriv k g θ) ^ 2 * qW k γ θ :=
    MeasureTheory.setIntegral_mono_set hIntFar hnn
      (Filter.Eventually.of_forall fun x hx => hsub hx)
  have hnnI : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      0 ≤ (iteratedDeriv k g θ) ^ 2 * qW k γ θ := by
    filter_upwards [MeasureTheory.ae_restrict_mem (μ := volume)
      (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with θ hθ
    exact mul_nonneg (sq_nonneg _) (qW_nonneg hθ)
  have h2 : (∫ θ in farSet, (iteratedDeriv k g θ) ^ 2 * qW k γ θ)
      ≤ ∫ θ in Work.Spaces.Iθ, (iteratedDeriv k g θ) ^ 2 * qW k γ θ :=
    MeasureTheory.setIntegral_mono_set h.hH2 hnnI
      (Filter.Eventually.of_forall fun x hx => farSet_subset_Iθ hx)
  have h3 : (∫ θ in Work.Spaces.Iθ, (iteratedDeriv k g θ) ^ 2 * qW k γ θ) ≤ FarR k γ u g := by
    have hA : 0 ≤ ∑ j ∈ Finset.Icc 3 (k + 1), ∫ θ in Work.Spaces.Iθ,
        (iteratedDeriv j u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ) :=
      Finset.sum_nonneg fun j _ => MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ hθ => mul_nonneg (sq_nonneg _) (slotWeight_nonneg hθ))
    have hB : 0 ≤ ∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta)) :=
      MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _))
    have hC : 0 ≤ ∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 :=
      MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _)
    have hD : 0 ≤ ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 :=
      MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _)
    simp only [FarR, qW] at *
    linarith
  linarith [h1, h2, h3]

/-- The `v`-slot on a compact sub-interval of the far window, from the far-window slot bound. -/
theorem vSlot_Icc_le (k : ℕ) (hk : 2 ≤ k) {Cv γ : ℝ} {u g : ℝ → ℝ} (h : FarHyp k γ u g)
    {m : ℕ} (hm : m ≤ k)
    (hInt : MeasureTheory.IntegrableOn
      (fun θ => (iteratedDeriv m (vF u) θ) ^ 2 * qW k γ θ) farSet)
    (hslot : (∫ θ in farSet, (iteratedDeriv m (vF u) θ) ^ 2 * qW k γ θ)
      ≤ Cv * FarR k γ u g)
    {a b : ℝ} (ha : 3 * Real.pi / 8 ≤ a) (hab : a ≤ b) (hb : b ≤ Real.pi / 2) :
    (∫ θ in Set.Icc a b, (iteratedDeriv m (vF u) θ) ^ 2 * qW k γ θ) ≤ Cv * FarR k γ u g := by
  have hsub : Set.Icc a b ⊆ farSet := fun x hx =>
    ⟨by linarith [hx.1, ha], by linarith [hx.2, hb]⟩
  have hnn : ∀ᵐ θ ∂(volume.restrict farSet), 0 ≤ (iteratedDeriv m (vF u) θ) ^ 2 * qW k γ θ := by
    filter_upwards [MeasureTheory.ae_restrict_mem (μ := volume)
      (show MeasurableSet farSet from measurableSet_Icc)] with θ hθ
    exact mul_nonneg (sq_nonneg _) (qW_nonneg (farSet_subset_Iθ hθ))
  exact le_trans (MeasureTheory.setIntegral_mono_set hInt hnn
    (Filter.Eventually.of_forall fun x hx => hsub hx)) hslot


/-- **The `v`-slot on `[3π/8, b]`, `b < π/2`.**  A self-contained bound, obtained from the
reflected-variable argument of `far_vBound` restricted to the compact interval `[π/2-b, π/8]`;
unlike the far-window bound it needs no integrability of the slot on `farSet`. -/
theorem vSlot_Icc_le_FarR (k : ℕ) (hk : 2 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ) (u g : ℝ → ℝ), FarHyp k γ u g → ∀ m : ℕ, m ≤ k →
      ∀ b : ℝ, 3 * Real.pi / 8 < b → b < Real.pi / 2 →
        (∫ θ in Set.Icc (3 * Real.pi / 8) b,
            (iteratedDeriv m (vF u) θ) ^ 2 * qW k γ θ) ≤ C * FarR k γ u g := by
  obtain ⟨K, hKpos, hKb⟩ := sinDivDerivBounds k
  refine ⟨((2 : ℝ) ^ k * K) ^ 2 * ((k + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ)
    * (2 : ℝ) ^ (2 * k + 3) + 1, by positivity, ?_⟩
  intro γ u g hF m hm b hb1 hb2
  have hK : ∀ i ≤ m, ∀ y ∈ Set.Ioc 0 xEnd, |iteratedDeriv i secH y| ≤ K :=
    fun i hi y hy => hKb i (le_trans hi hm) y hy
  have hFarR : (0 : ℝ) ≤ FarR k γ u g := FarR_nonneg hk hF
  have huC : ContDiffOn ℝ m u (Set.Ioo 0 (Real.pi / 2)) :=
    hF.huC.of_le (by exact_mod_cast (by omega : m ≤ k + 2))
  set A : ℝ := ((2 : ℝ) ^ m * K) ^ 2 * ((m + 1 : ℕ) : ℝ) with hA
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  set G : ℝ → ℝ := fun x => A * ∑ i ∈ Finset.range (m + 1),
      ((iteratedDeriv i (fun y : ℝ => shiftU u y / y) x) ^ 2
        * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ)) with hG
  have hGint : IntegrableOn G (Set.Ioc 0 xEnd) := by
    rw [hG]
    exact (MeasureTheory.integrable_finsetSum (Finset.range (m + 1))
      (fun i hi => integrableOn_sinWeight_xDivX hk hF
        (le_trans (by simpa [Finset.mem_range] using hi) hm))).const_mul A
  have hx0 : 0 < Real.pi / 2 - b := by linarith
  have hx0le : Real.pi / 2 - b < xEnd := by
    rw [xEnd]; linarith [Real.pi_pos, hb1]
  -- reflection of the interval integral
  have hrefl : (∫ θ in (3 * Real.pi / 8)..b, (iteratedDeriv m (vF u) θ) ^ 2 * qW k γ θ)
      = ∫ x in (Real.pi / 2 - b)..xEnd,
          (iteratedDeriv m (shiftV u) x) ^ 2 * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ) := by
    have step1 : (∫ θ in (3 * Real.pi / 8)..b, (iteratedDeriv m (vF u) θ) ^ 2 * qW k γ θ)
        = ∫ x in (Real.pi / 2 - b)..(Real.pi / 2 - 3 * Real.pi / 8),
            (iteratedDeriv m (vF u) (Real.pi / 2 - x)) ^ 2 * qW k γ (Real.pi / 2 - x) := by
      rw [← intervalIntegral.integral_comp_sub_left
        (fun y : ℝ => (iteratedDeriv m (vF u) (Real.pi / 2 - y)) ^ 2
          * qW k γ (Real.pi / 2 - y)) (Real.pi / 2)]
      exact intervalIntegral.integral_congr fun x _ => by
        simp only [show Real.pi / 2 - (Real.pi / 2 - x) = x from by ring]
    have step2 : (∫ x in (Real.pi / 2 - b)..(Real.pi / 2 - 3 * Real.pi / 8),
          (iteratedDeriv m (vF u) (Real.pi / 2 - x)) ^ 2 * qW k γ (Real.pi / 2 - x))
        = ∫ x in (Real.pi / 2 - b)..xEnd,
            (iteratedDeriv m (shiftV u) x) ^ 2 * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ) := by
      rw [show Real.pi / 2 - 3 * Real.pi / 8 = xEnd by rw [xEnd]; ring]
      exact intervalIntegral.integral_congr fun x _ => farSet_integrand_eq k γ m u x
    exact step1.trans step2
  -- the pointwise domination on the reflected window
  have hdom : (∫ x in Set.Ioc (Real.pi / 2 - b) xEnd,
        (iteratedDeriv m (shiftV u) x) ^ 2 * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ))
      ≤ ∫ x in Set.Ioc (Real.pi / 2 - b) xEnd, G x := by
    refine integral_mono_of_nonneg ?_ (hGint.mono_set fun x hx =>
      ⟨by linarith [hx.1, hx0], hx.2⟩) ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (sin_two_nonneg_Ioc ⟨by linarith [hx.1, hx0], hx.2⟩) _)
    · rw [← Measure.restrict_congr_set (Ioo_ae_eq_Ioc (μ := volume) (a := Real.pi / 2 - b)
        (b := xEnd))]
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      have hx' : x ∈ Set.Ioo 0 xEnd := ⟨by linarith [hx.1, hx0], hx.2⟩
      have hw_nn : 0 ≤ Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ) :=
        Real.rpow_nonneg (sin_two_nonneg_Ioc ⟨hx'.1, le_of_lt hx'.2⟩) _
      have h1 := shiftV_deriv_sq_le (u := u) (m := m) (K := K) hK huC hx'
      calc (iteratedDeriv m (shiftV u) x) ^ 2 * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ)
          ≤ (((2 : ℝ) ^ m * K) ^ 2 * ((m + 1 : ℕ) : ℝ)
              * ∑ i ∈ Finset.range (m + 1),
                  (iteratedDeriv i (fun y : ℝ => shiftU u y / y) x) ^ 2)
              * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ) :=
            mul_le_mul_of_nonneg_right h1 hw_nn
        _ = G x := by
            simp only [hG, hA]
            rw [← Finset.sum_mul]
            ring
  -- the monotonicity in the interval and the splitting of `G`
  have hle_int : (∫ x in Set.Ioc (Real.pi / 2 - b) xEnd, G x)
      ≤ ∫ x in Set.Ioc 0 xEnd, G x := by
    refine MeasureTheory.setIntegral_mono_set hGint ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      rw [hG]
      refine mul_nonneg hA0 (Finset.sum_nonneg fun i _ => ?_)
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Ioc ⟨hx.1, hx.2⟩) _)
    · exact Filter.Eventually.of_forall fun x hx => ⟨by linarith [hx.1, hx0], hx.2⟩
  have hsplit : (∫ x in Set.Ioc 0 xEnd, G x) = A * ∑ i ∈ Finset.range (m + 1),
      (∫ x in Set.Ioc 0 xEnd, (iteratedDeriv i (fun y : ℝ => shiftU u y / y) x) ^ 2
        * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ)) := by
    rw [hG, MeasureTheory.integral_const_mul]
    congr 1
    exact MeasureTheory.integral_finsetSum (Finset.range (m + 1))
      (fun i hi => integrableOn_sinWeight_xDivX hk hF
        (le_trans (by simpa [Finset.mem_range] using hi) hm))
  have hsum : ∑ i ∈ Finset.range (m + 1),
      (∫ x in Set.Ioc 0 xEnd, (iteratedDeriv i (fun y : ℝ => shiftU u y / y) x) ^ 2
        * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ))
      ≤ ((m + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ (2 * k + 3) * FarR k γ u g) := by
    calc ∑ i ∈ Finset.range (m + 1),
          (∫ x in Set.Ioc 0 xEnd, (iteratedDeriv i (fun y : ℝ => shiftU u y / y) x) ^ 2
            * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ))
        ≤ ∑ i ∈ Finset.range (m + 1), ((2 : ℝ) ^ (2 * k + 3) * FarR k γ u g) := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [← intervalIntegral.integral_of_le xEnd_pos.le]
          exact xTerm_le hk hF (le_trans (by simpa [Finset.mem_range] using hi) hm)
      _ = ((m + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ (2 * k + 3) * FarR k γ u g) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hAb : A ≤ ((2 : ℝ) ^ k * K) ^ 2 * ((k + 1 : ℕ) : ℝ) := by
    rw [hA]
    refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
    · refine pow_le_pow_left₀ (by positivity) ?_ 2
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hm) (le_of_lt hKpos)
    · exact_mod_cast (by omega : m + 1 ≤ k + 1)
  have hm1 : ((m + 1 : ℕ) : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : m + 1 ≤ k + 1)
  -- assemble
  have hmain : (∫ x in (Real.pi / 2 - b)..xEnd,
        (iteratedDeriv m (shiftV u) x) ^ 2 * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ))
      ≤ A * (((m + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ (2 * k + 3) * FarR k γ u g)) := by
    rw [intervalIntegral.integral_of_le hx0le.le]
    refine hdom.trans (hle_int.trans ?_)
    rw [hsplit]
    exact mul_le_mul_of_nonneg_left hsum hA0
  have hs1 : (∫ θ in Set.Icc (3 * Real.pi / 8) b,
        (iteratedDeriv m (vF u) θ) ^ 2 * qW k γ θ)
      = ∫ θ in (3 * Real.pi / 8)..b, (iteratedDeriv m (vF u) θ) ^ 2 * qW k γ θ := by
    rw [intervalIntegral.integral_of_le (le_of_lt hb1),
      MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [hs1, hrefl]
  refine hmain.trans ?_
  calc A * (((m + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ (2 * k + 3) * FarR k γ u g))
      ≤ (((2 : ℝ) ^ k * K) ^ 2 * ((k + 1 : ℕ) : ℝ))
          * (((k + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ (2 * k + 3) * FarR k γ u g)) := by
        refine mul_le_mul hAb ?_ (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_right hm1 (by positivity)
    _ ≤ (((2 : ℝ) ^ k * K) ^ 2 * ((k + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ)
          * (2 : ℝ) ^ (2 * k + 3) + 1) * FarR k γ u g := by
        nlinarith [hFarR]

/-- **The far-window interval estimate** (the body).  This is the lemma's conclusion with the
pointwise estimate integrated over `[3π/8, b]`.  The hypothesis `uSlot` is the `u`-slot bound on
sub-intervals of the far window and `hvSlot` is the `v`-slot bound on `[3π/8, b]` (both supplied
by the caller as proved lemmas). -/
theorem E_interval_le_main (k : ℕ) (hk : 2 ≤ k)
    (uSlot : ∀ (γ : ℝ) (u g : ℝ → ℝ), FarHyp k γ u g → ∀ j : ℕ, j ≤ k + 1 →
      ∀ a b : ℝ, 3 * Real.pi / 8 ≤ a → a ≤ b → b ≤ Real.pi / 2 →
        (∫ θ in Set.Icc a b, (iteratedDeriv j u θ) ^ 2 * qW k γ θ) ≤ FarR k γ u g)
    (Cv : ℝ) (hCv : 0 < Cv)
    (hvSlot : ∀ (γ : ℝ) (u g : ℝ → ℝ), FarHyp k γ u g → ∀ m : ℕ, m ≤ k →
      ∀ b : ℝ, 3 * Real.pi / 8 < b → b < Real.pi / 2 →
        (∫ θ in Set.Icc (3 * Real.pi / 8) b,
            (iteratedDeriv m (vF u) θ) ^ 2 * qW k γ θ) ≤ Cv * FarR k γ u g) :
    ∀ (γ : ℝ) (u g : ℝ → ℝ), FarHyp k γ u g →
      ∀ b : ℝ, 3 * Real.pi / 8 < b → b < Real.pi / 2 →
        (∫ θ in (3 * Real.pi / 8)..b, iteratedDeriv (k + 1) (fun t => Real.tan t * u t) θ
            * iteratedDeriv (k + 2) u θ * qW k γ θ)
          - (∫ θ in (3 * Real.pi / 8)..b, tripleT k γ u θ * qW k γ θ)
        ≤ CFinal k Cv * FarR k γ u g
          + (1 / 16) * (∫ θ in (3 * Real.pi / 8)..b, (iteratedDeriv (k + 2) u θ) ^ 2
              * qW k γ θ) := by
  intro γ u g h b hb1 hb2
  set a : ℝ := 3 * Real.pi / 8 with ha_eq
  have ha_pos : 0 < a := by rw [ha_eq]; linarith [Real.pi_pos]
  have ha3 : 3 * Real.pi / 8 ≤ a := by rw [ha_eq]
  have hab : a ≤ b := by rw [ha_eq]; linarith [hb1]
  have hsub : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun x hx =>
    ⟨by linarith [hx.1, ha_pos], by linarith [hx.2, hb2]⟩
  have hsubI : Set.Icc a b ⊆ Work.Spaces.Iθ := fun x hx =>
    ⟨by linarith [hx.1, ha_pos, Real.pi_pos], by linarith [hx.2, hb2, Real.pi_pos]⟩
  have hFar : Set.Icc a b ⊆ farSet := fun x hx =>
    ⟨by linarith [hx.1, ha_pos, Real.pi_pos], by linarith [hx.2, hb2, Real.pi_pos]⟩
  have uIcc_eq : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hab
  -- continuity of the ingredients
  have hcont_u : ∀ m : ℕ, m ≤ k + 2 → ContinuousOn (iteratedDeriv m u) (Set.Icc a b) :=
    fun m hm => (continuousOn_iteratedDeriv_of_contDiffOn isOpen_Ioo h.huC hm).mono hsub
  have hcont_v : ∀ m : ℕ, m ≤ k + 2 → ContinuousOn (iteratedDeriv m (vF u)) (Set.Icc a b) :=
    fun m hm =>
      (continuousOn_iteratedDeriv_of_contDiffOn isOpen_Ioo (contDiffOn_vF h.huC) hm).mono hsub
  have hcont_tan : ContinuousOn (iteratedDeriv (k + 1) (fun t => Real.tan t * u t))
      (Set.Icc a b) :=
    (continuousOn_iteratedDeriv_of_contDiffOn isOpen_Ioo
      (contDiffOn_tan_mul (n := k + 1)
        (h.huC.of_le (by exact_mod_cast (by omega : k + 1 ≤ k + 2))))
      (le_refl (k + 1))).mono hsub
  have hcont_q : ContinuousOn (qW k γ) (Set.Icc a b) := continuousOn_qW ha_pos hb2
  have hsin : ContinuousOn (fun θ : ℝ => Real.sin θ) (Set.Icc a b) :=
    Real.continuous_sin.continuousOn
  have hcos : ContinuousOn (fun θ : ℝ => Real.cos θ) (Set.Icc a b) :=
    Real.continuous_cos.continuousOn
  have hcont_T : ContinuousOn (fun θ => tripleT k γ u θ) (Set.Icc a b) := by
    have hv1 := hcont_v (k + 1) (by omega)
    have hv2 := hcont_v (k + 2) (le_refl _)
    have hv0 := hcont_v k (by omega)
    have hk2 : ContinuousOn (fun _ : ℝ => ((k : ℝ) + 2)) (Set.Icc a b) := continuousOn_const
    have hk1 : ContinuousOn (fun _ : ℝ => ((k : ℝ) + 1)) (Set.Icc a b) := continuousOn_const
    simp only [tripleT]
    exact ((((hsin.mul hcos).mul hv1).mul hv2).sub
      ((hk2.mul (hsin.pow 2)).mul (hv1.pow 2))).add
      (((hk1.mul (hcos.pow 2)).mul hv0).mul hv2)
  -- integrability helpers
  have hIntC : ∀ (f : ℝ → ℝ), ContinuousOn f (Set.Icc a b) → IntervalIntegrable f volume a b :=
    fun f hf => by
      have h' : ContinuousOn f (Set.uIcc a b) := by rw [uIcc_eq]; exact hf
      exact h'.intervalIntegrable
  have hIntI : ∀ (f : ℝ → ℝ), MeasureTheory.IntegrableOn f (Set.Icc a b) →
      IntervalIntegrable f volume a b := fun f hf => by
    have h' : MeasureTheory.IntegrableOn f (Set.uIcc a b) := by rw [uIcc_eq]; exact hf
    exact h'.intervalIntegrable
  -- the pointwise estimate, multiplied by the nonnegative weight
  have hpoint : ∀ θ ∈ Set.Icc a b,
      (iteratedDeriv (k + 1) (fun t => Real.tan t * u t) θ * iteratedDeriv (k + 2) u θ
          - tripleT k γ u θ) * qW k γ θ
      ≤ (3 / 64) * ((iteratedDeriv (k + 2) u θ) ^ 2 * qW k γ θ)
        + CU k * ((iteratedDeriv k u θ) ^ 2 * qW k γ θ)
        + CG k * ((iteratedDeriv k g θ) ^ 2 * qW k γ θ)
        + CS1 k * ((∑ r ∈ Finset.Icc 1 (k + 1),
              (iteratedDeriv (k + 1 - r) (vF u) θ) ^ 2) * qW k γ θ)
        + CS2 k * ((∑ j ∈ Finset.Icc 2 (k + 2),
              (iteratedDeriv (k + 2 - j) (vF u) θ) ^ 2) * qW k γ θ)
        + CS3 k * ((∑ j ∈ Finset.Icc 1 k,
              (iteratedDeriv (k - j) (vF u) θ) ^ 2) * qW k γ θ) := by
    intro θ hθ
    have hpw := E_pointwise k γ h.huC h.hg θ (hsub hθ)
    have hq : 0 ≤ qW k γ θ := qW_nonneg (hsubI hθ)
    have hmul := mul_le_mul_of_nonneg_right hpw hq
    refine hmul.trans_eq ?_
    ring
  -- the ingredients of the right-hand integrand, and their interval integrability
  have hIntQ : IntervalIntegrable (fun θ =>
      (iteratedDeriv (k + 2) u θ) ^ 2 * qW k γ θ) volume a b :=
    hIntI _ (h.hH1.mono_set (fun x hx => farSet_subset_Iθ (hFar hx)))
  have hIntUk : IntervalIntegrable (fun θ =>
      (iteratedDeriv k u θ) ^ 2 * qW k γ θ) volume a b :=
    hIntC _ (((hcont_u k (by omega)).pow 2).mul hcont_q)
  have hIntG : IntervalIntegrable (fun θ =>
      (iteratedDeriv k g θ) ^ 2 * qW k γ θ) volume a b :=
    hIntI _ (h.hH2.mono_set (fun x hx => farSet_subset_Iθ (hFar hx)))
  have hIntS1 : IntervalIntegrable (fun θ =>
      (∑ r ∈ Finset.Icc 1 (k + 1), (iteratedDeriv (k + 1 - r) (vF u) θ) ^ 2)
        * qW k γ θ) volume a b :=
    hIntC _ ((continuousOn_finsetSum _ (fun r hr => (hcont_v (k + 1 - r) (by
      have := (Finset.mem_Icc.mp hr).1; omega)).pow 2)).mul hcont_q)
  have hIntS2 : IntervalIntegrable (fun θ =>
      (∑ j ∈ Finset.Icc 2 (k + 2), (iteratedDeriv (k + 2 - j) (vF u) θ) ^ 2)
        * qW k γ θ) volume a b :=
    hIntC _ ((continuousOn_finsetSum _ (fun j hj => (hcont_v (k + 2 - j) (by
      have := (Finset.mem_Icc.mp hj).1; omega)).pow 2)).mul hcont_q)
  have hIntS3 : IntervalIntegrable (fun θ =>
      (∑ j ∈ Finset.Icc 1 k, (iteratedDeriv (k - j) (vF u) θ) ^ 2) * qW k γ θ)
      volume a b :=
    hIntC _ ((continuousOn_finsetSum _ (fun j hj => (hcont_v (k - j) (by
      have := (Finset.mem_Icc.mp hj).1; omega)).pow 2)).mul hcont_q)
  -- the chain of estimates: first the two integrals combine, then the pointwise bound
  have hstep1 : (∫ θ in a..b, iteratedDeriv (k + 1) (fun t => Real.tan t * u t) θ
        * iteratedDeriv (k + 2) u θ * qW k γ θ)
      - (∫ θ in a..b, tripleT k γ u θ * qW k γ θ)
      = ∫ θ in a..b, (iteratedDeriv (k + 1) (fun t => Real.tan t * u t) θ
          * iteratedDeriv (k + 2) u θ - tripleT k γ u θ) * qW k γ θ := by
    have hL : IntervalIntegrable (fun θ => iteratedDeriv (k + 1) (fun t => Real.tan t * u t) θ
        * iteratedDeriv (k + 2) u θ * qW k γ θ) volume a b :=
      hIntC _ ((hcont_tan.mul (hcont_u (k + 2) (le_refl _))).mul hcont_q)
    have hR : IntervalIntegrable (fun θ => tripleT k γ u θ * qW k γ θ) volume a b :=
      hIntC _ (hcont_T.mul hcont_q)
    rw [← intervalIntegral.integral_sub hL hR]
    exact intervalIntegral.integral_congr fun θ _ => by ring
  have hstep2 : (∫ θ in a..b, (iteratedDeriv (k + 1) (fun t => Real.tan t * u t) θ
        * iteratedDeriv (k + 2) u θ - tripleT k γ u θ) * qW k γ θ)
      ≤ ∫ θ in a..b, ((3 / 64) * ((iteratedDeriv (k + 2) u θ) ^ 2 * qW k γ θ)
        + CU k * ((iteratedDeriv k u θ) ^ 2 * qW k γ θ)
        + CG k * ((iteratedDeriv k g θ) ^ 2 * qW k γ θ)
        + CS1 k * ((∑ r ∈ Finset.Icc 1 (k + 1),
              (iteratedDeriv (k + 1 - r) (vF u) θ) ^ 2) * qW k γ θ)
        + CS2 k * ((∑ j ∈ Finset.Icc 2 (k + 2),
              (iteratedDeriv (k + 2 - j) (vF u) θ) ^ 2) * qW k γ θ)
        + CS3 k * ((∑ j ∈ Finset.Icc 1 k,
              (iteratedDeriv (k - j) (vF u) θ) ^ 2) * qW k γ θ)) := by
    have hL : IntervalIntegrable (fun θ => (iteratedDeriv (k + 1) (fun t => Real.tan t * u t) θ
        * iteratedDeriv (k + 2) u θ - tripleT k γ u θ) * qW k γ θ) volume a b :=
      hIntC _ (((hcont_tan.mul (hcont_u (k + 2) (le_refl _))).sub hcont_T).mul hcont_q)
    have hR : IntervalIntegrable (fun θ =>
        (3 / 64) * ((iteratedDeriv (k + 2) u θ) ^ 2 * qW k γ θ)
        + CU k * ((iteratedDeriv k u θ) ^ 2 * qW k γ θ)
        + CG k * ((iteratedDeriv k g θ) ^ 2 * qW k γ θ)
        + CS1 k * ((∑ r ∈ Finset.Icc 1 (k + 1),
              (iteratedDeriv (k + 1 - r) (vF u) θ) ^ 2) * qW k γ θ)
        + CS2 k * ((∑ j ∈ Finset.Icc 2 (k + 2),
              (iteratedDeriv (k + 2 - j) (vF u) θ) ^ 2) * qW k γ θ)
        + CS3 k * ((∑ j ∈ Finset.Icc 1 k,
              (iteratedDeriv (k - j) (vF u) θ) ^ 2) * qW k γ θ)) volume a b :=
      (((((hIntQ.const_mul (3 / 64)).add (hIntUk.const_mul (CU k))).add
        (hIntG.const_mul (CG k))).add (hIntS1.const_mul (CS1 k))).add
        (hIntS2.const_mul (CS2 k))).add (hIntS3.const_mul (CS3 k))
    exact intervalIntegral.integral_mono_on hab hL hR hpoint
  -- linearity of the integral of the right-hand side
  have hIntR_eq : (∫ θ in a..b, ((3 / 64) * ((iteratedDeriv (k + 2) u θ) ^ 2 * qW k γ θ)
        + CU k * ((iteratedDeriv k u θ) ^ 2 * qW k γ θ)
        + CG k * ((iteratedDeriv k g θ) ^ 2 * qW k γ θ)
        + CS1 k * ((∑ r ∈ Finset.Icc 1 (k + 1),
              (iteratedDeriv (k + 1 - r) (vF u) θ) ^ 2) * qW k γ θ)
        + CS2 k * ((∑ j ∈ Finset.Icc 2 (k + 2),
              (iteratedDeriv (k + 2 - j) (vF u) θ) ^ 2) * qW k γ θ)
        + CS3 k * ((∑ j ∈ Finset.Icc 1 k,
              (iteratedDeriv (k - j) (vF u) θ) ^ 2) * qW k γ θ)))
      = (3 / 64) * (∫ θ in a..b, (iteratedDeriv (k + 2) u θ) ^ 2 * qW k γ θ)
        + CU k * (∫ θ in a..b, (iteratedDeriv k u θ) ^ 2 * qW k γ θ)
        + CG k * (∫ θ in a..b, (iteratedDeriv k g θ) ^ 2 * qW k γ θ)
        + CS1 k * (∫ θ in a..b, (∑ r ∈ Finset.Icc 1 (k + 1),
              (iteratedDeriv (k + 1 - r) (vF u) θ) ^ 2) * qW k γ θ)
        + CS2 k * (∫ θ in a..b, (∑ j ∈ Finset.Icc 2 (k + 2),
              (iteratedDeriv (k + 2 - j) (vF u) θ) ^ 2) * qW k γ θ)
        + CS3 k * (∫ θ in a..b, (∑ j ∈ Finset.Icc 1 k,
              (iteratedDeriv (k - j) (vF u) θ) ^ 2) * qW k γ θ) := by
    rw [intervalIntegral.integral_add, intervalIntegral.integral_add,
      intervalIntegral.integral_add, intervalIntegral.integral_add,
      intervalIntegral.integral_add,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    all_goals first
      | exact hIntQ | exact hIntUk | exact hIntG | exact hIntS1 | exact hIntS2 | exact hIntS3
      | exact hIntQ.const_mul _ | exact hIntUk.const_mul _ | exact hIntG.const_mul _
      | exact hIntS1.const_mul _ | exact hIntS2.const_mul _ | exact hIntS3.const_mul _
      | exact (hIntQ.const_mul _).add (hIntUk.const_mul _)
      | exact ((hIntQ.const_mul _).add (hIntUk.const_mul _)).add (hIntG.const_mul _)
      | exact (((hIntQ.const_mul _).add (hIntUk.const_mul _)).add (hIntG.const_mul _)).add
          (hIntS1.const_mul _)
      | exact ((((hIntQ.const_mul _).add (hIntUk.const_mul _)).add (hIntG.const_mul _)).add
          (hIntS1.const_mul _)).add (hIntS2.const_mul _)
  -- the value bounds for the individual slots
  have hu_bound : (∫ θ in a..b, (iteratedDeriv k u θ) ^ 2 * qW k γ θ) ≤ FarR k γ u g := by
    have hbnd := uSlot γ u g h k (by omega) a b ha3 hab (le_of_lt hb2)
    rw [intervalIntegral.integral_of_le hab, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    exact hbnd
  have hg_bound : (∫ θ in a..b, (iteratedDeriv k g θ) ^ 2 * qW k γ θ) ≤ FarR k γ u g := by
    have hbnd := gSlot_Icc_le_FarR k hk h ha3 hab (le_of_lt hb2)
    rw [intervalIntegral.integral_of_le hab, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    exact hbnd
  have hv_bound : ∀ m : ℕ, m ≤ k → (∫ θ in a..b,
      (iteratedDeriv m (vF u) θ) ^ 2 * qW k γ θ) ≤ Cv * FarR k γ u g := by
    intro m hm
    have hbnd := hvSlot γ u g h m hm b (by rw [ha_eq]; exact hb1) hb2
    rw [intervalIntegral.integral_of_le hab, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    exact hbnd
  -- the `S`-terms
  have hS1_bound : (∫ θ in a..b, (∑ r ∈ Finset.Icc 1 (k + 1),
        (iteratedDeriv (k + 1 - r) (vF u) θ) ^ 2) * qW k γ θ)
      ≤ ((k : ℝ) + 1) * (Cv * FarR k γ u g) := by
    simp only [Finset.sum_mul]
    have hI : ∀ r ∈ Finset.Icc 1 (k + 1), IntervalIntegrable
        (fun θ => (iteratedDeriv (k + 1 - r) (vF u) θ) ^ 2 * qW k γ θ) volume a b :=
      fun r hr => hIntC _ (((hcont_v (k + 1 - r) (by
        have := (Finset.mem_Icc.mp hr).1; omega)).pow 2).mul hcont_q)
    rw [intervalIntegral.integral_finset_sum hI]
    have hterm : ∀ r ∈ Finset.Icc 1 (k + 1),
        (∫ θ in a..b, (iteratedDeriv (k + 1 - r) (vF u) θ) ^ 2 * qW k γ θ)
          ≤ Cv * FarR k γ u g := fun r hr =>
      hv_bound (k + 1 - r) (by have := (Finset.mem_Icc.mp hr).1; omega)
    calc (∑ r ∈ Finset.Icc 1 (k + 1), ∫ θ in a..b,
            (iteratedDeriv (k + 1 - r) (vF u) θ) ^ 2 * qW k γ θ)
        ≤ ∑ r ∈ Finset.Icc 1 (k + 1), Cv * FarR k γ u g := Finset.sum_le_sum hterm
      _ = ((k : ℝ) + 1) * (Cv * FarR k γ u g) := by
          rw [Finset.sum_const, nsmul_eq_mul,
            show ((Finset.Icc 1 (k + 1)).card : ℝ) = (k : ℝ) + 1 from by simp]
  have hS2_bound : (∫ θ in a..b, (∑ j ∈ Finset.Icc 2 (k + 2),
        (iteratedDeriv (k + 2 - j) (vF u) θ) ^ 2) * qW k γ θ)
      ≤ ((k : ℝ) + 1) * (Cv * FarR k γ u g) := by
    simp only [Finset.sum_mul]
    have hI : ∀ j ∈ Finset.Icc 2 (k + 2), IntervalIntegrable
        (fun θ => (iteratedDeriv (k + 2 - j) (vF u) θ) ^ 2 * qW k γ θ) volume a b :=
      fun j hj => hIntC _ (((hcont_v (k + 2 - j) (by
        have := (Finset.mem_Icc.mp hj).1; omega)).pow 2).mul hcont_q)
    rw [intervalIntegral.integral_finset_sum hI]
    have hterm : ∀ j ∈ Finset.Icc 2 (k + 2),
        (∫ θ in a..b, (iteratedDeriv (k + 2 - j) (vF u) θ) ^ 2 * qW k γ θ)
          ≤ Cv * FarR k γ u g := fun j hj =>
      hv_bound (k + 2 - j) (by have := (Finset.mem_Icc.mp hj).1; omega)
    calc (∑ j ∈ Finset.Icc 2 (k + 2), ∫ θ in a..b,
            (iteratedDeriv (k + 2 - j) (vF u) θ) ^ 2 * qW k γ θ)
        ≤ ∑ j ∈ Finset.Icc 2 (k + 2), Cv * FarR k γ u g := Finset.sum_le_sum hterm
      _ = ((k : ℝ) + 1) * (Cv * FarR k γ u g) := by
          rw [Finset.sum_const, nsmul_eq_mul,
            show ((Finset.Icc 2 (k + 2)).card : ℝ) = (k : ℝ) + 1 from by simp]
  have hS3_bound : (∫ θ in a..b, (∑ j ∈ Finset.Icc 1 k,
        (iteratedDeriv (k - j) (vF u) θ) ^ 2) * qW k γ θ)
      ≤ (k : ℝ) * (Cv * FarR k γ u g) := by
    simp only [Finset.sum_mul]
    have hI : ∀ j ∈ Finset.Icc 1 k, IntervalIntegrable
        (fun θ => (iteratedDeriv (k - j) (vF u) θ) ^ 2 * qW k γ θ) volume a b :=
      fun j hj => hIntC _ (((hcont_v (k - j) (by
        have := (Finset.mem_Icc.mp hj).1; omega)).pow 2).mul hcont_q)
    rw [intervalIntegral.integral_finset_sum hI]
    have hterm : ∀ j ∈ Finset.Icc 1 k,
        (∫ θ in a..b, (iteratedDeriv (k - j) (vF u) θ) ^ 2 * qW k γ θ)
          ≤ Cv * FarR k γ u g := fun j hj =>
      hv_bound (k - j) (by have := (Finset.mem_Icc.mp hj).1; omega)
    calc (∑ j ∈ Finset.Icc 1 k, ∫ θ in a..b,
            (iteratedDeriv (k - j) (vF u) θ) ^ 2 * qW k γ θ)
        ≤ ∑ j ∈ Finset.Icc 1 k, Cv * FarR k γ u g := Finset.sum_le_sum hterm
      _ = (k : ℝ) * (Cv * FarR k γ u g) := by
          rw [Finset.sum_const, nsmul_eq_mul,
            show ((Finset.Icc 1 k).card : ℝ) = (k : ℝ) from by simp]
  -- nonnegativity of the source slot
  have hU : (0 : ℝ) ≤ ∫ θ in a..b, (iteratedDeriv (k + 2) u θ) ^ 2 * qW k γ θ := by
    rw [intervalIntegral.integral_of_le hab]
    refine MeasureTheory.setIntegral_nonneg measurableSet_Ioc fun θ hθ => ?_
    exact mul_nonneg (sq_nonneg _) (qW_nonneg (hsubI ⟨le_of_lt hθ.1, hθ.2⟩))
  -- coefficient nonnegativity
  have hCU : 0 ≤ CU k := by
    rw [CU]; have h1 := KW_nonneg k; have h2 := KUv_nonneg k; nlinarith
  have hCG : 0 ≤ CG k := by
    rw [CG]; have h2 := KUv_nonneg k; nlinarith
  have hCS1 : 0 ≤ CS1 k := by rw [CS1]; exact mul_nonneg (CZt_nonneg k) (KapZ_nonneg k)
  have hCS2 : 0 ≤ CS2 k := by rw [CS2]; exact mul_nonneg (CYt_nonneg k) (KapY_nonneg k)
  have hCS3 : 0 ≤ CS3 k := by rw [CS3]; exact mul_nonneg (CWt_nonneg k) (KapW_nonneg k)
  rw [hstep1]
  refine hstep2.trans ?_
  rw [hIntR_eq]
  have h1' := mul_le_mul_of_nonneg_left hu_bound hCU
  have h2' := mul_le_mul_of_nonneg_left hg_bound hCG
  have h3' := mul_le_mul_of_nonneg_left hS1_bound hCS1
  have h4' := mul_le_mul_of_nonneg_left hS2_bound hCS2
  have h5' := mul_le_mul_of_nonneg_left hS3_bound hCS3
  have hQ' : (3 / 64) * (∫ θ in a..b, (iteratedDeriv (k + 2) u θ) ^ 2 * qW k γ θ)
      ≤ (1 / 16) * (∫ θ in a..b, (iteratedDeriv (k + 2) u θ) ^ 2 * qW k γ θ) := by
    nlinarith [hU]
  rw [CFinal]
  have hcomb : (3 / 64) * (∫ θ in a..b, (iteratedDeriv (k + 2) u θ) ^ 2 * qW k γ θ)
        + CU k * (∫ θ in a..b, (iteratedDeriv k u θ) ^ 2 * qW k γ θ)
        + CG k * (∫ θ in a..b, (iteratedDeriv k g θ) ^ 2 * qW k γ θ)
        + CS1 k * (∫ θ in a..b, (∑ r ∈ Finset.Icc 1 (k + 1),
              (iteratedDeriv (k + 1 - r) (vF u) θ) ^ 2) * qW k γ θ)
        + CS2 k * (∫ θ in a..b, (∑ j ∈ Finset.Icc 2 (k + 2),
              (iteratedDeriv (k + 2 - j) (vF u) θ) ^ 2) * qW k γ θ)
        + CS3 k * (∫ θ in a..b, (∑ j ∈ Finset.Icc 1 k,
              (iteratedDeriv (k - j) (vF u) θ) ^ 2) * qW k γ θ)
      ≤ (1 / 16) * (∫ θ in a..b, (iteratedDeriv (k + 2) u θ) ^ 2 * qW k γ θ)
        + FarR k γ u g + CU k * FarR k γ u g + CG k * FarR k γ u g
        + CS1 k * (((k : ℝ) + 1) * (Cv * FarR k γ u g))
        + CS2 k * (((k : ℝ) + 1) * (Cv * FarR k γ u g))
        + CS3 k * ((k : ℝ) * (Cv * FarR k γ u g)) := by
    have hFarR_nn : 0 ≤ FarR k γ u g := FarR_nonneg hk h
    linarith only [h1', h2', h3', h4', h5', hQ', hFarR_nn]
  refine hcomb.trans (le_of_eq ?_)
  ring


/-- **The far-window interval estimate.**  The `v`-slot bound is supplied internally by
`vSlot_Icc_le_FarR`, so only the `u`-slot bound is a hypothesis. -/
theorem E_interval_le (k : ℕ) (hk : 2 ≤ k)
    (uSlot : ∀ (γ : ℝ) (u g : ℝ → ℝ), FarHyp k γ u g → ∀ j : ℕ, j ≤ k + 1 →
      ∀ a b : ℝ, 3 * Real.pi / 8 ≤ a → a ≤ b → b ≤ Real.pi / 2 →
        (∫ θ in Set.Icc a b, (iteratedDeriv j u θ) ^ 2 * qW k γ θ) ≤ FarR k γ u g) :
    ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ) (u g : ℝ → ℝ), FarHyp k γ u g →
      ∀ b : ℝ, 3 * Real.pi / 8 < b → b < Real.pi / 2 →
        (∫ θ in (3 * Real.pi / 8)..b, iteratedDeriv (k + 1) (fun t => Real.tan t * u t) θ
            * iteratedDeriv (k + 2) u θ * qW k γ θ)
          - (∫ θ in (3 * Real.pi / 8)..b, tripleT k γ u θ * qW k γ θ)
        ≤ C * FarR k γ u g
          + (1 / 16) * (∫ θ in (3 * Real.pi / 8)..b, (iteratedDeriv (k + 2) u θ) ^ 2
              * qW k γ θ) := by
  obtain ⟨Cv, hCv, hvSlot⟩ := vSlot_Icc_le_FarR k hk
  refine ⟨CFinal k Cv, ?_, E_interval_le_main k hk uSlot Cv hCv hvSlot⟩
  rw [CFinal]
  have h1 := CU_nonneg k
  have h2 := CG_nonneg k
  have h3 : 0 ≤ CS1 k * ((k : ℝ) + 1) * Cv :=
    mul_nonneg (mul_nonneg (CS1_nonneg k) (by positivity)) (le_of_lt hCv)
  have h4 : 0 ≤ CS2 k * ((k : ℝ) + 1) * Cv :=
    mul_nonneg (mul_nonneg (CS2_nonneg k) (by positivity)) (le_of_lt hCv)
  have h5 : 0 ≤ CS3 k * (k : ℝ) * Cv :=
    mul_nonneg (mul_nonneg (CS3_nonneg k) (Nat.cast_nonneg k)) (le_of_lt hCv)
  linarith

theorem far_E_leibniz (k : ℕ) (hk : 2 ≤ k) (Cv : ℝ) (hCv : 0 < Cv) :
    ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ) (u g : ℝ → ℝ),
      Work.FTS.EllipticEst.remov.TopCoreB.FarHyp k γ u g →
      (∀ m : ℕ, m ≤ k →
        (∫ θ in Work.FTS.EllipticEst.remov.TopCoreB.farSet,
            (iteratedDeriv m (Work.FTS.EllipticEst.remov.TopCoreB.vF u) θ) ^ 2
              * Work.FTS.EllipticEst.remov.TopCoreB.qW k γ θ)
          ≤ Cv * Work.FTS.EllipticEst.remov.TopCoreB.FarR k γ u g) →
      ∀ b : ℝ, 3 * Real.pi / 8 < b → b < Real.pi / 2 →
        (∫ θ in (3 * Real.pi / 8)..b,
              iteratedDeriv (k + 1) (fun t => Real.tan t * u t) θ
                * iteratedDeriv (k + 2) u θ
                * Work.FTS.EllipticEst.remov.TopCoreB.qW k γ θ)
            - (∫ θ in (3 * Real.pi / 8)..b,
                Work.FTS.EllipticEst.remov.TopCoreB.tripleT k γ u θ
                  * Work.FTS.EllipticEst.remov.TopCoreB.qW k γ θ)
          ≤ C * Work.FTS.EllipticEst.remov.TopCoreB.FarR k γ u g
            + (1 / 16) * (∫ θ in (3 * Real.pi / 8)..b,
                (iteratedDeriv (k + 2) u θ) ^ 2
                  * Work.FTS.EllipticEst.remov.TopCoreB.qW k γ θ) := by
  obtain ⟨C, hC, hmain⟩ := E_interval_le k hk fun γ u g h j hj a b ha hab hb =>
    Work.FTS.EllipticEst.remov.TopCoreB.FEL.uSlot_Icc_le_FarR k hk γ u g h j hj a b ha hab hb
  exact ⟨C, hC, fun γ u g h _hslot b hb1 hb2 => hmain γ u g h b hb1 hb2⟩

end Work.FTS.EllipticEst.remov.TopCoreB
