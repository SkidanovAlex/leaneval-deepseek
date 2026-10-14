import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllipticEst.sin2_parseval_aesm
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.Regularity.hkIntegrandZfarBound
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.bt_f_bound
import Submission.Work.Spaces.continuousOn_HkIntegrand_Qd
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.EllipticEst.Cert.HkMem_Dth_of_pth =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cert

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.deprecated false
set_option linter.unusedTactic false

/-! ## The pieces of the pointwise domination

Everything rests on the fact that `D_θ f = sin(2θ)·∂_θ f`, so that the `ℋ^k`-integrand of
`D_θ f` is obtained from that of `∂_θ f` by (i) multiplying the `D_z`-summand of order `i` by
`sin(2θ)` (harmless, `|sin 2θ| ≤ 1`), and (ii) expanding
`D_z^j D_θ^n (D_θ f) = ∑_{m ≤ n} C(n,n-m)·sin(2θ)·hfun (n-m)·D_z^j D_θ^m (∂_θ f)`
(`mixed_Dth_expand`): the summands with `m ≥ 1` are honest mixed summands of the integrand of
`∂_θ f`, and the single summand with `m = 0` — which is weighted with the radial weight
`w/s^{η/2}` rather than the mixed one `Wt = w·s^{-γ/2}` — is controlled by
`sin(2θ)²·Wt² ≤ (w/s^{η/2})²` (`sin_sq_mul_Wt_sq_le`). -/

/-- `D_z` sees only the `z`-variable, so it commutes with multiplication by a factor `u(θ)`
depending on `θ` only.  (No differentiability hypothesis: `deriv_const_mul_field` is
unconditional.) -/
theorem Dz_mul_of_angular (u : ℝ → ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.Dz (fun z θ => u θ * g z θ) = fun z θ => u θ * Work.Spaces.Dz g z θ := by
  funext z θ
  show z * Work.Spaces.pz (fun z θ => u θ * g z θ) z θ = u θ * (z * Work.Spaces.pz g z θ)
  simp only [Work.Spaces.pz]
  rw [deriv_const_mul_field (u θ)]
  ring

/-- Iterated form of `Dz_mul_of_angular`. -/
theorem DzIter_mul_of_angular (i : ℕ) (u : ℝ → ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter i (fun z θ => u θ * g z θ)
      = fun z θ => u θ * Work.Spaces.DzIter i g z θ := by
  induction i with
  | zero => rfl
  | succ n ih =>
      rw [Work.Spaces.DzIter_succ, ih]
      exact Dz_mul_of_angular u (Work.Spaces.DzIter n g)

/-- `D_z^i (D_θ f) = sin(2θ)·D_z^i (∂_θ f)` pointwise. -/
theorem DzIter_Dth_eq (i : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.DzIter i (Work.Spaces.Dth f) z θ
      = Real.sin (2 * θ) * Work.Spaces.DzIter i (Work.Spaces.pth f) z θ := by
  have h := congrFun (congrFun
    (DzIter_mul_of_angular i (fun θ : ℝ => Real.sin (2 * θ)) (Work.Spaces.pth f)) z) θ
  show Work.Spaces.DzIter i (fun z θ => Real.sin (2 * θ) * Work.Spaces.pth f z θ) z θ
      = Real.sin (2 * θ) * Work.Spaces.DzIter i (Work.Spaces.pth f) z θ
  exact h

/-- At an angle where `sin(2θ) = 0` the `ℋ^k`-integrand vanishes identically: every summand
carries one of the two weights `w z / sin(2θ)^{η/2}` and `w z·sin(2θ)^{-γ/2}`, both of which
are `0` there (Lean's totalised division resp. `Real.zero_rpow`). -/
theorem HkIntegrand_eq_zero_of_sin_eq_zero (α : ℝ) (hα : 0 < α) (k : ℕ) (g : ℝ → ℝ → ℝ)
    {z θ : ℝ} (hs : Real.sin (2 * θ) = 0) :
    Work.Spaces.HkIntegrand α k g z θ = 0 := by
  have h2 : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) = 0 := by
    rw [hs, Real.zero_rpow (x := Work.Spaces.eta / 2)
      (div_ne_zero (ne_of_gt Work.Spaces.eta_pos) (by norm_num))]
  have h1 : (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) = 0 := by
    rw [hs, Real.zero_rpow (x := -(Work.Spaces.gam α / 2))
      (neg_ne_zero.mpr (div_ne_zero (ne_of_gt (Work.Spaces.gam_pos hα)) (by norm_num)))]
  have hA : (∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i g z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) = 0 :=
    Finset.sum_eq_zero (fun i _ => by rw [h2, div_zero, mul_zero]; ring)
  have hB : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
      (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0)) = 0 :=
    Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun j _ => by
      by_cases hc : 1 ≤ i ∧ i + j ≤ k
      · rw [if_pos hc]
        simp only [Work.Spaces.Wt, Work.Spaces.wTheta, h1, mul_zero]
        ring
      · rw [if_neg hc]))
  rw [Work.Spaces.HkIntegrand, hA, hB, add_zero]

/-- Each radial summand of the `ℋ^k`-integrand of `D_θ f` is a radial summand of the
integrand of `∂_θ f`: the extra factor `sin(2θ)` is bounded by `1` in modulus. -/
theorem radial_summand_le (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) {z θ : ℝ} (i : ℕ) (hi : i ≤ k) :
    (Work.Spaces.DzIter i (Work.Spaces.Dth f) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ Work.Spaces.HkIntegrand α k (Work.Spaces.pth f) z θ := by
  rw [DzIter_Dth_eq i f z θ]
  have h1 : (Real.sin (2 * θ) * Work.Spaces.DzIter i (Work.Spaces.pth f) z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ 2 * (Work.Spaces.DzIter i (Work.Spaces.pth f) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by ring
  rw [h1]
  refine le_trans ?_ (Work.Spaces.sq_le_HkIntegrand_z α k (Work.Spaces.pth f) z θ i hi)
  calc (Real.sin (2 * θ)) ^ 2 * (Work.Spaces.DzIter i (Work.Spaces.pth f) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ 1 * (Work.Spaces.DzIter i (Work.Spaces.pth f) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 :=
        mul_le_mul_of_nonneg_right (Real.sin_sq_le_one (2 * θ)) (sq_nonneg _)
    _ = (Work.Spaces.DzIter i (Work.Spaces.pth f) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := one_mul _

/-- **The mixed summands.**  For `1 ≤ n`, `n + j ≤ k` and `sin(2θ) ≠ 0`, the mixed summand
of the `ℋ^k`-integrand of `D_θ f` at indices `(n,j)` is bounded by `(k+1)²·((2^k·B)²)` times
the `ℋ^k`-integrand of `∂_θ f`, where `B` bounds the finitely many coefficient functions
`hfun i`, `i ≤ k`, on `Iθ`. -/
theorem mixed_summand_le (α : ℝ) (hα1 : α ≤ 1) (k n j : ℕ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.Spaces.SmoothNbhd f) {B : ℝ}
    (hB : ∀ i ≤ k, ∀ θ ∈ Work.Spaces.Iθ, |Work.FTS.EllipticEst.hfun i θ| ≤ B)
    (hBnn : 0 ≤ B) {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ)
    (hs : Real.sin (2 * θ) ≠ 0) (hn1 : 1 ≤ n) (hnk : n + j ≤ k) :
    (Work.Spaces.mixed j n (Work.Spaces.Dth f) z θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ ((k + 1 : ℝ) ^ 2 * ((2 : ℝ) ^ k * B) ^ 2)
          * Work.Spaces.HkIntegrand α k (Work.Spaces.pth f) z θ := by
  have hslt : 0 < Real.sin (2 * θ) :=
    lt_of_le_of_ne (Work.FTS.EllipticEst.sin_two_nonneg hθ) hs.symm
  have hnk' : n ≤ k := le_trans (Nat.le_add_right n j) hnk
  have hjk : j ≤ k := le_trans (Nat.le_add_left j n) hnk
  rw [mixed_Dth_expand n j hsm (Work.Spaces.mem_nbhU hz hθ)]
  set W : ℝ := Work.Spaces.Wt α z θ with hW
  set I : ℝ := Work.Spaces.HkIntegrand α k (Work.Spaces.pth f) z θ with hI
  have hInn : 0 ≤ I := by
    rw [hI]
    exact Work.Spaces.HkIntegrand_nonneg α k (Work.Spaces.pth f) z θ
  have hKc : 0 ≤ ((2 : ℝ) ^ k * B) ^ 2 := sq_nonneg _
  -- ### The summand bounds
  have hterm : ∀ m ∈ Finset.range (n + 1),
      ((↑(n.choose (n - m)) * (Real.sin (2 * θ) * Work.FTS.EllipticEst.hfun (n - m) θ))
        * (Work.Spaces.mixed j m (Work.Spaces.pth f) z θ * W)) ^ 2
      ≤ ((2 : ℝ) ^ k * B) ^ 2 * I := by
    intro m hm
    have hmle : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · -- the summand with no angular derivative of `∂_θ f`: the weight comparison applies
      subst hm0
      rw [Work.Spaces.mixed_zero_right]
      have hc0 : ↑(n.choose (n - 0)) * (Real.sin (2 * θ) * Work.FTS.EllipticEst.hfun (n - 0) θ)
          = Real.sin (2 * θ) * Work.FTS.EllipticEst.hfun n θ := by simp
      rw [hc0]
      have hhB : |Work.FTS.EllipticEst.hfun n θ| ≤ B := hB n hnk' θ hθ
      have hh2 : (Work.FTS.EllipticEst.hfun n θ) ^ 2 ≤ B ^ 2 := by
        rw [sq_le_sq, abs_of_nonneg hBnn]
        exact hhB
      have hwt : (Real.sin (2 * θ)) ^ 2 * W ^ 2
          ≤ (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 := by
        rw [hW]
        exact sin_sq_mul_Wt_sq_le α hα1 hθ hslt
      have hzJ : (Work.Spaces.DzIter j (Work.Spaces.pth f) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 ≤ I := by
        rw [hI]
        exact Work.Spaces.sq_le_HkIntegrand_z α k (Work.Spaces.pth f) z θ j hjk
      have hmain : (Real.sin (2 * θ) * Work.FTS.EllipticEst.hfun n θ
            * (Work.Spaces.DzIter j (Work.Spaces.pth f) z θ * W)) ^ 2 ≤ B ^ 2 * I := by
        have h1 : (Real.sin (2 * θ) * Work.FTS.EllipticEst.hfun n θ
              * (Work.Spaces.DzIter j (Work.Spaces.pth f) z θ * W)) ^ 2
            = (Work.FTS.EllipticEst.hfun n θ) ^ 2 * ((Real.sin (2 * θ)) ^ 2 * W ^ 2)
              * (Work.Spaces.DzIter j (Work.Spaces.pth f) z θ) ^ 2 := by ring
        rw [h1]
        have hprod : (Work.FTS.EllipticEst.hfun n θ) ^ 2 * ((Real.sin (2 * θ)) ^ 2 * W ^ 2)
              * (Work.Spaces.DzIter j (Work.Spaces.pth f) z θ) ^ 2
            ≤ B ^ 2 * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
              * (Work.Spaces.DzIter j (Work.Spaces.pth f) z θ) ^ 2 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul hh2 hwt (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg B))
            (sq_nonneg _)
        calc (Work.FTS.EllipticEst.hfun n θ) ^ 2 * ((Real.sin (2 * θ)) ^ 2 * W ^ 2)
              * (Work.Spaces.DzIter j (Work.Spaces.pth f) z θ) ^ 2
            ≤ B ^ 2 * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
              * (Work.Spaces.DzIter j (Work.Spaces.pth f) z θ) ^ 2 := hprod
          _ = B ^ 2 * (Work.Spaces.DzIter j (Work.Spaces.pth f) z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
                ring
          _ ≤ B ^ 2 * I := mul_le_mul_of_nonneg_left hzJ (sq_nonneg B)
      have h2k : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
      have hBB : B ≤ (2 : ℝ) ^ k * B := by
        simpa using mul_le_mul_of_nonneg_right h2k hBnn
      have hB2 : B ^ 2 ≤ ((2 : ℝ) ^ k * B) ^ 2 := pow_le_pow_left₀ hBnn hBB 2
      exact le_trans hmain (mul_le_mul_of_nonneg_right hB2 hInn)
    · -- a summand carrying a genuine angular derivative of `∂_θ f`
      have hm1 : 1 ≤ m := hmpos
      have hmj : m + j ≤ k := le_trans (Nat.add_le_add_right hmle j) hnk
      have hch : (↑(n.choose (n - m)) : ℝ) ≤ (2 : ℝ) ^ k := by
        have h1 : n.choose (n - m) ≤ 2 ^ n := Nat.choose_le_two_pow n (n - m)
        have h2 : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) hnk'
        calc (↑(n.choose (n - m)) : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast h1
          _ ≤ (2 : ℝ) ^ k := h2
      have hc2 : (↑(n.choose (n - m)) * (Real.sin (2 * θ)
            * Work.FTS.EllipticEst.hfun (n - m) θ)) ^ 2 ≤ ((2 : ℝ) ^ k * B) ^ 2 := by
        rw [mul_pow]
        have hsh : (Real.sin (2 * θ) * Work.FTS.EllipticEst.hfun (n - m) θ) ^ 2 ≤ B ^ 2 := by
          rw [mul_pow]
          have hhB : |Work.FTS.EllipticEst.hfun (n - m) θ| ≤ B :=
            hB (n - m) (le_trans (Nat.sub_le n m) hnk') θ hθ
          have hh2 : (Work.FTS.EllipticEst.hfun (n - m) θ) ^ 2 ≤ B ^ 2 := by
            rw [sq_le_sq, abs_of_nonneg hBnn]
            exact hhB
          calc (Real.sin (2 * θ)) ^ 2 * (Work.FTS.EllipticEst.hfun (n - m) θ) ^ 2
              ≤ 1 * B ^ 2 :=
                mul_le_mul (Real.sin_sq_le_one (2 * θ)) hh2 (sq_nonneg _) zero_le_one
            _ = B ^ 2 := one_mul _
        calc (↑(n.choose (n - m)) : ℝ) ^ 2
              * (Real.sin (2 * θ) * Work.FTS.EllipticEst.hfun (n - m) θ) ^ 2
            ≤ ((2 : ℝ) ^ k) ^ 2 * B ^ 2 :=
              mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) hch 2) hsh (sq_nonneg _)
                (by positivity)
          _ = ((2 : ℝ) ^ k * B) ^ 2 := by ring
      have hxw : (Work.Spaces.mixed j m (Work.Spaces.pth f) z θ * W) ^ 2 ≤ I := by
        rw [hW, hI]
        exact Work.Spaces.sq_le_HkIntegrand_mixed α k (Work.Spaces.pth f) z θ m j hm1 hmj
      calc ((↑(n.choose (n - m)) * (Real.sin (2 * θ) * Work.FTS.EllipticEst.hfun (n - m) θ))
            * (Work.Spaces.mixed j m (Work.Spaces.pth f) z θ * W)) ^ 2
          = (↑(n.choose (n - m)) * (Real.sin (2 * θ)
              * Work.FTS.EllipticEst.hfun (n - m) θ)) ^ 2
            * (Work.Spaces.mixed j m (Work.Spaces.pth f) z θ * W) ^ 2 := by ring
        _ ≤ ((2 : ℝ) ^ k * B) ^ 2 * I := mul_le_mul hc2 hxw (sq_nonneg _) hKc
  -- ### Cauchy–Schwarz and summation
  have hgather : (∑ m ∈ Finset.range (n + 1),
        ↑(n.choose (n - m)) * (Real.sin (2 * θ) * Work.FTS.EllipticEst.hfun (n - m) θ)
          * Work.Spaces.mixed j m (Work.Spaces.pth f) z θ * W)
      = ∑ m ∈ Finset.range (n + 1),
        (↑(n.choose (n - m)) * (Real.sin (2 * θ) * Work.FTS.EllipticEst.hfun (n - m) θ))
          * (Work.Spaces.mixed j m (Work.Spaces.pth f) z θ * W) :=
    Finset.sum_congr rfl (fun m _ => by ring)
  rw [Finset.sum_mul, hgather]
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (n + 1))
    (f := fun m => (↑(n.choose (n - m)) * (Real.sin (2 * θ)
          * Work.FTS.EllipticEst.hfun (n - m) θ))
        * (Work.Spaces.mixed j m (Work.Spaces.pth f) z θ * W))
  have hcard : ((Finset.range (n + 1)).card : ℝ) = (n + 1 : ℝ) := by simp
  rw [hcard] at hcs
  have h1 : (n : ℝ) + 1 ≤ (k : ℝ) + 1 := by
    have h : n + 1 ≤ k + 1 := Nat.succ_le_succ hnk'
    exact_mod_cast h
  calc (∑ m ∈ Finset.range (n + 1),
        (↑(n.choose (n - m)) * (Real.sin (2 * θ) * Work.FTS.EllipticEst.hfun (n - m) θ))
          * (Work.Spaces.mixed j m (Work.Spaces.pth f) z θ * W)) ^ 2
      ≤ (n + 1 : ℝ) * ∑ m ∈ Finset.range (n + 1),
          ((↑(n.choose (n - m)) * (Real.sin (2 * θ) * Work.FTS.EllipticEst.hfun (n - m) θ))
            * (Work.Spaces.mixed j m (Work.Spaces.pth f) z θ * W)) ^ 2 := hcs
    _ ≤ (n + 1 : ℝ) * ∑ m ∈ Finset.range (n + 1), ((2 : ℝ) ^ k * B) ^ 2 * I :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (by positivity)
    _ = (n + 1 : ℝ) * ((n + 1 : ℝ) * (((2 : ℝ) ^ k * B) ^ 2 * I)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
    _ = (((n : ℝ) + 1) ^ 2 * ((2 : ℝ) ^ k * B) ^ 2) * I := by ring
    _ ≤ (((k : ℝ) + 1) ^ 2 * ((2 : ℝ) ^ k * B) ^ 2) * I :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) h1 2) hKc) hInn
    _ = ((k + 1 : ℝ) ^ 2 * ((2 : ℝ) ^ k * B) ^ 2) * I := by push_cast; ring

/-- Pointwise domination of the `ℋ^k`-integrand of `D_θ f` by that of `∂_θ f` on the whole
closed quadrant. -/
theorem HkIntegrand_Dth_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.Spaces.SmoothNbhd f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (Work.Spaces.Dth f) z θ
        ≤ C * Work.Spaces.HkIntegrand α k (Work.Spaces.pth f) z θ := by
  obtain ⟨B, hBpos, hB⟩ := Work.FTS.EllipticEst.sd_exists_bound_hfun k
  refine ⟨(k + 1 : ℝ) + (k + 1 : ℝ) ^ 2 * ((k + 1 : ℝ) ^ 2 * ((2 : ℝ) ^ k * B) ^ 2),
    by positivity, ?_⟩
  intro z hz θ hθ
  set I : ℝ := Work.Spaces.HkIntegrand α k (Work.Spaces.pth f) z θ with hI
  by_cases hs : Real.sin (2 * θ) = 0
  · rw [HkIntegrand_eq_zero_of_sin_eq_zero α hα k (Work.Spaces.Dth f) hs]
    exact mul_nonneg (by positivity) (Work.Spaces.HkIntegrand_nonneg α k (Work.Spaces.pth f) z θ)
  · have hsum1 : (∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i (Work.Spaces.Dth f) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ (k + 1 : ℝ) * I := by
      calc (∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i (Work.Spaces.Dth f) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          ≤ ∑ i ∈ Finset.range (k + 1), I :=
            Finset.sum_le_sum (fun i hi => by
              rw [hI]
              exact radial_summand_le α k f i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
        _ = (k + 1 : ℝ) * I := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            push_cast
            ring
    have hsum2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i (Work.Spaces.Dth f) z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0))
        ≤ (k + 1 : ℝ) ^ 2 * (((k + 1 : ℝ) ^ 2 * ((2 : ℝ) ^ k * B) ^ 2) * I) := by
      calc (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k then
              (Work.Spaces.mixed j i (Work.Spaces.Dth f) z θ * Work.Spaces.Wt α z θ) ^ 2
            else 0))
          ≤ ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              ((k + 1 : ℝ) ^ 2 * ((2 : ℝ) ^ k * B) ^ 2) * I :=
            Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => by
              by_cases hc : 1 ≤ i ∧ i + j ≤ k
              · rw [if_pos hc]
                have h := mixed_summand_le α hα1 k i j hsm hB (le_of_lt hBpos) hz hθ hs hc.1 hc.2
                rw [← hI] at h
                exact h
              · rw [if_neg hc]
                have h0 : 0 ≤ I := by
                  rw [hI]
                  exact Work.Spaces.HkIntegrand_nonneg α k (Work.Spaces.pth f) z θ
                exact mul_nonneg (by positivity) h0))
        _ = (k + 1 : ℝ) ^ 2 * (((k + 1 : ℝ) ^ 2 * ((2 : ℝ) ^ k * B) ^ 2) * I) := by
            rw [Finset.sum_const, Finset.sum_const, Finset.card_range, nsmul_eq_mul, nsmul_eq_mul]
            push_cast
            ring
    calc Work.Spaces.HkIntegrand α k (Work.Spaces.Dth f) z θ
        = (∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i (Work.Spaces.Dth f) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              (if 1 ≤ i ∧ i + j ≤ k then
                (Work.Spaces.mixed j i (Work.Spaces.Dth f) z θ * Work.Spaces.Wt α z θ) ^ 2
              else 0) := by rw [Work.Spaces.HkIntegrand]
      _ ≤ (k + 1 : ℝ) * I + (k + 1 : ℝ) ^ 2 * (((k + 1 : ℝ) ^ 2 * ((2 : ℝ) ^ k * B) ^ 2) * I) :=
          add_le_add hsum1 hsum2
      _ = ((k + 1 : ℝ) + (k + 1 : ℝ) ^ 2 * ((k + 1 : ℝ) ^ 2 * ((2 : ℝ) ^ k * B) ^ 2)) * I := by
          ring


end Work.FTS.EllipticEst.Cert
end
end
-- ===== merged: Submission.Work.FTS.FinalClock.PhysClock =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory Set
open scoped Topology Interval

namespace Work.FTS.FinalClock

open Work.FTS.Physical (PhysClock)
open Work.FTS.Galerkin (Fam slice muDyn)

/-! ## The clock of a bounded, continuous modulation -/

/-- **The clock of a modulation `m` bounded by `1/2`.**  Its amplitude is the vorticity amplitude
of the design scaled by `2`: `A = 2 · Avort m`, i.e. `A(τ) = 2 e^{-∫₀^τ (1+m)}`; its modulation
is `m` itself.  `A` solves `A' = -(1+m)A` (so `PhysClock.hAderiv` holds), it is positive and
continuous, and `1/2 ≤ 1+m ≤ 3/2` gives `PhysClock.hmu_lo`/`hmu_hi`. -/
noncomputable def physClockOf (m : ℝ → ℝ) (hc : Continuous m) (hm : MuBound m) : PhysClock where
  A := fun τ => 2 * Avort m τ
  mu := m
  hApos := fun τ _ => by
    have := Avort_pos m τ
    linarith
  hAcont := (Avort_continuous hc).const_mul 2 |>.continuousOn
  hAderiv := fun τ _ => by
    have h := (Avort_hasDerivAt hc τ).const_mul 2
    have hval : 2 * (-(1 + m τ) * Avort m τ) = -(1 + m τ) * (2 * Avort m τ) := by ring
    rwa [hval] at h
  hmu_lo := fun τ _ => by linarith [hm.ge τ]
  hmu_hi := fun τ _ => by linarith [hm.le τ]

@[simp] theorem physClockOf_mu (m : ℝ → ℝ) (hc : Continuous m) (hm : MuBound m) :
    (physClockOf m hc hm).mu = m := rfl

@[simp] theorem physClockOf_A (m : ℝ → ℝ) (hc : Continuous m) (hm : MuBound m) :
    (physClockOf m hc hm).A = fun τ : ℝ => 2 * Avort m τ := rfl





/-! ## The quantitative consequences of the modulation bound -/




/-! ## The companion amplitude `B` (design §3) -/

/-- The companion amplitude `B(τ) = c · Bdyn m τ` of the clock: it solves `B' = -(1-m)B`, which
is exactly the `hBd` hypothesis of `meridianEq_of_dynEq` (§3) with `C.mu = m`. -/
theorem hasDerivAt_Bdyn_const_mul (m : ℝ → ℝ) (hc : Continuous m) (c τ : ℝ) :
    HasDerivAt (fun s : ℝ => c * Bdyn m s) (-(1 - m τ) * (c * Bdyn m τ)) τ := by
  have h := (Bdyn_hasDerivAt hc τ).const_mul c
  have hval : c * (-(1 - m τ) * Bdyn m τ) = -(1 - m τ) * (c * Bdyn m τ) := by ring
  rwa [hval] at h

/-- The same, with the modulation read off the clock produced by `physClockOf`: this is the form
in which `meridianEq_of_dynEq` consumes `hAdh`/`hBdh`. -/
theorem hasDerivAt_Bdyn_of_clock (m : ℝ → ℝ) (hc : Continuous m) (hm : MuBound m) (c τ : ℝ) :
    HasDerivAt (fun s : ℝ => c * Bdyn m s)
      (-(1 - (physClockOf m hc hm).mu τ) * (c * Bdyn m τ)) τ := by
  simpa only [physClockOf_mu] using hasDerivAt_Bdyn_const_mul m hc c τ


/-! ## The main theorem: the clock of the dynamic modulation `muDyn` -/





end Work.FTS.FinalClock
end
end
