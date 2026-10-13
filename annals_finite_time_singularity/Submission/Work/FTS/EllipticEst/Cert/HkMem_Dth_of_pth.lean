import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.HkMem_mixed_le
import Submission.Work.Spaces.continuousOn_HkIntegrand_Qd
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.pz_aux
import Submission.Work.Spaces.DthIter_mul
import Submission.Work.FTS.EllipticEst.LopIterSinDefs
import Submission.Work.FTS.EllipticEst.sd_lop_iter_sin_bound
import Submission.Work.FTS.LocData.HkMem_of_majorant
-- NB (2026-10-12): was `…Cert.ZzKidsTmp`, the temporary stub that carried the two lemmas as
-- placeholders.  Both have been proved in their real homes (`Cert/mixed_Dth_expand.lean`,
-- `Cert/sin_sq_mul_Wt_sq_le.lean`, same declaration names), so the stub is no longer imported
-- and its placeholders are out of this module's cone.  The stub file is left in place, retired.
import Submission.Work.FTS.EllipticEst.Cert.mixed_Dth_expand
import Submission.Work.FTS.EllipticEst.Cert.sin_sq_mul_Wt_sq_le

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

/-- **`ℋ^k`-membership of the weighted angular derivative `D_θ f = sin(2θ)·∂_θ f` from that of the
plain one `∂_θ f`**, for `0 < α ≤ 1`.

The `ℋ^k`-integrand of `D_θf` is dominated, pointwise on the quadrant, by a multiple of the
`ℋ^k`-integrand of `∂_θf`, so honesty transfers.  Route: with `M_sin` the multiplication operator
by `sin(2θ)` one has the operator identity `D_θ ∘ M_sin = M_{2 sin cos} + M_sin ∘ D_θ`, hence by
induction `D_θ^i (M_sin g) = ∑_{m≤i} b_{i,m}·D_θ^m g` with coefficients given recursively by
`b_{0,0} = sin(2θ)`, `b_{i+1,m} = sin(2θ)·∂_θ b_{i,m} + b_{i,m-1}` (and `b_{i,-1} = 0`); so all
`b_{i,m}` are smooth on `[0,π/2]`, hence bounded, and for `i ≥ 1` also `|b_{i,0}| ≤ C_i·sin(2θ)`
(each step multiplies `b_{i,0}` by `sin(2θ)` before differentiating).  Consequently:

* the radial summands of `HkIntegrand α k (D_θf)` are `(D_z^i(sin·∂_θf)·H)² ≤ (D_z^i∂_θf·H)²`,
  radial summands of `HkIntegrand α k (∂_θf)`;
* the mixed summands `(D_z^jD_θ^i(D_θf)·Wt)²` with `i ≥ 1` expand as
  `(D_z^j∑_m b_{i,m}D_θ^m∂_θf·Wt)²`; for `m ≥ 1` the summand is a mixed summand of
  `HkIntegrand α k (∂_θf)` (its index satisfies `m + j ≤ i + j ≤ k`), while for `m = 0` the
  coefficient bound and `2 - γ + η > 0` (`γ = 1+α/10`, `η = 99/100`, `α ≤ 1`) give
  `(b_{i,0}D_z^j∂_θf·Wt)² ≤ C_i (D_z^j∂_θf·H)²`, a radial summand of `HkIntegrand α k (∂_θf)`
  (here `Wt² = w²sin(2θ)^{-γ}` and `H² = w²sin(2θ)^{-η}`, so the two weights differ by
  `sin(2θ)^{2-γ+η} ≤ 1`).

The pointwise comparison is turned into `HkMem` with `Work.FTS.LocData.HkMem_of_majorant`
(the integrand of `D_θf` is continuous on the open quadrant by
`Work.Spaces.continuousOn_HkIntegrand_Qd` and `Work.Spaces.SmoothNbhd.Dth`). -/
theorem HkMem_Dth_of_pth (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.Spaces.SmoothNbhd f)
    (hdf : Work.Spaces.HkMem α k (Work.Spaces.pth f)) :
    Work.Spaces.HkMem α k (Work.Spaces.Dth f) := by
  obtain ⟨C, hCnn, hC⟩ := HkIntegrand_Dth_le α hα hα1 k hsm
  refine Work.FTS.LocData.HkMem_of_majorant α k (f := Work.Spaces.Dth f)
    (M := fun z θ => C * Work.Spaces.HkIntegrand α k (Work.Spaces.pth f) z θ)
    ?_ ?_ ?_ ?_
  · -- continuity of the integrand of `D_θ f` on the open quadrant
    refine Work.Spaces.continuousOn_HkIntegrand_Qd α k (Work.Spaces.Dth f) ?_
    exact (Work.Spaces.SmoothNbhd.Dth hsm).mono
      (fun p hp => ⟨hp.1, ⟨by linarith [hp.2.1], by linarith [hp.2.2, Real.pi_pos]⟩⟩)
  · -- integrability of the angular slices of the majorant
    intro z hz
    exact MeasureTheory.Integrable.const_mul (hdf.1 z hz) C
  · -- integrability of the `z`-integral of the majorant
    refine (MeasureTheory.Integrable.const_mul (hdf.2) C).congr
      (Filter.Eventually.of_forall fun z => ?_)
    exact (MeasureTheory.integral_const_mul C
      (fun θ => Work.Spaces.HkIntegrand α k (Work.Spaces.pth f) z θ)).symm
  · -- the pointwise domination
    intro z hz θ hθ
    exact hC z hz θ hθ

end Work.FTS.EllipticEst.Cert
