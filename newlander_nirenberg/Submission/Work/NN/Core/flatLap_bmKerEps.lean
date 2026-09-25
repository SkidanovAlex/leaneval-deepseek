import Mathlib
import Submission.Work.NN.Core.czB_L2_defs
import Submission.Work.CR.Flat.Cauchy.bmKerEpsAux
import Submission.Work.CR.Flat.Cauchy.bmDzKernel_ibp
import Submission.Work.CR.Flat.Polydisc.dbarCoord_mul
import Submission.Work.CR.Flat.Polydisc.dbarCoord_apply_conj_coord

noncomputable section
open scoped NNReal ENNReal
open MeasureTheory Set

namespace Work.NN.Core

open Work.CR.Flat.Cauchy
open Work.CR.Flat.Cauchy.bmIbp

/-! ### Auxiliary calculus on `ℂⁿ` -/

/-- The `(1,0)`-derivative of a holomorphic coordinate function. -/
lemma flatLap_dCoord_apply_coord {n : ℕ} (j k : Fin n) (z : Fin n → ℂ) :
    Work.CR.Flat.dCoord j (fun w : Fin n → ℂ => w k) z = if j = k then 1 else 0 := by
  rw [Work.CR.Flat.dCoord, Work.CR.Flat.Polydisc.fderiv_coord k z]
  simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.proj_apply]
  by_cases h : j = k
  · subst h; norm_num [Complex.I_mul_I]
  · rw [if_neg h, Pi.single_eq_of_ne (Ne.symm h), Pi.single_eq_of_ne (Ne.symm h)]
    ring

/-- The `(1,0)`-derivative of a constant function vanishes. -/
lemma flatLap_dCoord_const {n : ℕ} (j : Fin n) (c : ℂ) (z : Fin n → ℂ) :
    Work.CR.Flat.dCoord j (fun _ : Fin n → ℂ => c) z = 0 := by
  simp [Work.CR.Flat.dCoord]

/-- Additivity of the flat `(1,0)`-operator. -/
lemma flatLap_dCoord_add {n : ℕ} (j : Fin n) (u v : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ)
    (hu : DifferentiableAt ℝ u z) (hv : DifferentiableAt ℝ v z) :
    Work.CR.Flat.dCoord j (u + v) z = Work.CR.Flat.dCoord j u z + Work.CR.Flat.dCoord j v z := by
  have hfd : fderiv ℝ (fun w => (u + v) w) z = fderiv ℝ u z + fderiv ℝ v z := by
    rw [fderiv_add hu hv]
  simp only [Work.CR.Flat.dCoord, hfd, add_apply]
  ring

/-- `t ↦ (t + ε²)^{-n}` has derivative `-n (t + ε²)^{-n-1}` for `t ≥ 0`, `ε > 0`. -/
lemma flatLap_hasDerivAt_radProf {n : ℕ} {ε : ℝ} (hε : 0 < ε) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun s : ℝ => (s + ε ^ 2) ^ (-(n : ℤ)))
      (((-(n : ℤ) : ℝ)) * (t + ε ^ 2) ^ (-(n : ℤ) - 1)) t := by
  have hpos : (0 : ℝ) < t + ε ^ 2 := by have := pow_pos hε 2; linarith
  have h1 : HasDerivAt (fun s : ℝ => s + ε ^ 2) (1 : ℝ) t := by
    simpa using (hasDerivAt_id t).add_const (ε ^ 2)
  have h0 := hasDerivAt_zpow (-(n : ℤ)) (t + ε ^ 2) (Or.inl hpos.ne')
  simp only [Int.cast_neg] at h0
  simpa only [Function.comp_def, mul_one] using h0.comp t h1

/-- `t ↦ -n (t + ε²)^{-n-1}` has derivative `n(n+1)(t + ε²)^{-n-2}` for `t ≥ 0`, `ε > 0`. -/
lemma flatLap_hasDerivAt_radProfDeriv {n : ℕ} {ε : ℝ} (hε : 0 < ε) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun s : ℝ => (((-(n : ℤ) : ℝ)) * (s + ε ^ 2) ^ (-(n : ℤ) - 1)))
      ((((-(n : ℤ) : ℝ)) * (((-(n : ℤ) : ℝ)) - 1)) * (t + ε ^ 2) ^ (-(n : ℤ) - 2)) t := by
  have hpos : (0 : ℝ) < t + ε ^ 2 := by have := pow_pos hε 2; linarith
  have h1 : HasDerivAt (fun s : ℝ => s + ε ^ 2) (1 : ℝ) t := by
    simpa using (hasDerivAt_id t).add_const (ε ^ 2)
  have h0 : HasDerivAt (fun x : ℝ => x ^ (-(n : ℤ) - 1))
      (((-(n : ℤ) - 1 : ℤ) : ℝ) * (t + ε ^ 2) ^ (-(n : ℤ) - 2)) (t + ε ^ 2) := by
    have := hasDerivAt_zpow (-(n : ℤ) - 1) (t + ε ^ 2) (Or.inl hpos.ne')
    rwa [show ((-(n : ℤ) - 1) - 1 : ℤ) = -(n : ℤ) - 2 by ring] at this
  have h : HasDerivAt (fun s : ℝ => (s + ε ^ 2) ^ (-(n : ℤ) - 1))
      (((-(n : ℤ) - 1 : ℤ) : ℝ) * (t + ε ^ 2) ^ (-(n : ℤ) - 2)) t := by
    simpa only [Function.comp_def, mul_one] using h0.comp t h1
  have h2 := h.const_mul ((-(n : ℤ) : ℝ))
  convert h2 using 1
  · push_cast
    ring

/-- Complexified radial functions `x ↦ (Φ(nrmSq x) : ℂ)` are real-differentiable. -/
lemma flatLap_differentiableAt_ofReal_comp_nrmSq {n : ℕ} {Φ : ℝ → ℝ} {Φ' : ℝ}
    {w : Fin n → ℂ} (hΦ : HasDerivAt Φ Φ' (nrmSq w)) :
    DifferentiableAt ℝ (fun x : Fin n → ℂ => ((Φ (nrmSq x) : ℝ) : ℂ)) w := by
  have hg : DifferentiableAt ℝ (fun x : Fin n → ℂ => Φ (nrmSq x)) w :=
    hΦ.differentiableAt.comp w (differentiableAt_nrmSq w)
  have h := Complex.ofRealCLM.differentiableAt.comp w hg
  exact h

/-- **The second-order real algebra.** -/
lemma flatLap_radial_algebra {n : ℕ} {ε r : ℝ} (hε : 0 < ε) (hr : 0 ≤ r) :
    ((n : ℝ) + 1) * (((-(n : ℤ) : ℝ)) * (r + ε ^ 2) ^ (-(n : ℤ) - 1))
      + ((((-(n : ℤ) : ℝ)) * (((-(n : ℤ) : ℝ)) - 1)) * (r + ε ^ 2) ^ (-(n : ℤ) - 2)) * r
    = -(n : ℝ) * ((n : ℝ) + 1) * ε ^ 2 * (r + ε ^ 2) ^ (-(n : ℤ) - 2) := by
  have hε2 : (0 : ℝ) < ε ^ 2 := pow_pos hε 2
  have ha : (0 : ℝ) < r + ε ^ 2 := add_pos_of_nonneg_of_pos hr hε2
  have h1 : (r + ε ^ 2) ^ (-(n : ℤ) - 1) = ((r + ε ^ 2) ^ (n + 1))⁻¹ := by
    rw [show (-(n : ℤ) - 1 : ℤ) = -(((n + 1 : ℕ)) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
  have h2 : (r + ε ^ 2) ^ (-(n : ℤ) - 2) = ((r + ε ^ 2) ^ (n + 2))⁻¹ := by
    rw [show (-(n : ℤ) - 2 : ℤ) = -(((n + 2 : ℕ)) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
  rw [h1, h2]
  have hA : (r + ε ^ 2) ^ (n + 2) = (r + ε ^ 2) ^ (n + 1) * (r + ε ^ 2) := by rw [pow_succ]
  rw [hA]
  field_simp
  push_cast
  ring

/-- **Pointwise `∂̄`-expansion of the regularised Bochner–Martinelli kernel.** -/
lemma flatLap_dbarCoord_bmKerEps {n : ℕ} (j : Fin n) {ε : ℝ} (hε : 0 < ε) :
    ∀ (k : Fin n) (w : Fin n → ℂ),
      Work.CR.Flat.dbarCoord k (bmKerEps j ε) w
        = (if k = j then (((nrmSq w + ε ^ 2) ^ (-(n : ℤ)) : ℝ) : ℂ) else 0)
          + star (w j)
              * ((((-(n : ℤ) : ℝ)) * (nrmSq w + ε ^ 2) ^ (-(n : ℤ) - 1) : ℝ) : ℂ) * w k := by
  intro k w
  have hfun : bmKerEps j ε
      = fun y : Fin n → ℂ => star (y j) * (((nrmSq y + ε ^ 2) ^ (-(n : ℤ)) : ℝ) : ℂ) := by
    funext y
    exact Work.CR.Flat.Cauchy.bmKerEps_eq_zpow j ε y
  have hu : DifferentiableAt ℝ (fun y : Fin n → ℂ => star (y j)) w :=
    differentiableAt_star_coord j w
  have hv : DifferentiableAt ℝ
      (fun y : Fin n → ℂ => (((nrmSq y + ε ^ 2) ^ (-(n : ℤ)) : ℝ) : ℂ)) w :=
    flatLap_differentiableAt_ofReal_comp_nrmSq
      (flatLap_hasDerivAt_radProf (n := n) hε (nrmSq_nonneg w))
  rw [hfun, Work.CR.Flat.Polydisc.dbarCoord_mul k
        (fun y : Fin n → ℂ => star (y j))
        (fun y : Fin n → ℂ => (((nrmSq y + ε ^ 2) ^ (-(n : ℤ)) : ℝ) : ℂ)) w hu hv,
      Work.CR.Flat.Polydisc.dbarCoord_apply_conj_coord k j w]
  have hrad := Work.CR.Flat.Cauchy.dbarCoord_comp_nrmSq (n := n) (z := w) k
    (Φ := fun t : ℝ => (t + ε ^ 2) ^ (-(n : ℤ)))
    (Φ' := ((-(n : ℤ) : ℝ)) * (nrmSq w + ε ^ 2) ^ (-(n : ℤ) - 1))
    (flatLap_hasDerivAt_radProf (n := n) hε (nrmSq_nonneg w))
  rw [hrad]
  have hite : (if k = j then (1 : ℂ) else 0) * (((nrmSq w + ε ^ 2) ^ (-(n : ℤ)) : ℝ) : ℂ)
      = (if k = j then (((nrmSq w + ε ^ 2) ^ (-(n : ℤ)) : ℝ) : ℂ) else 0) := by
    split_ifs <;> ring
  rw [hite]
  ring

/-- **The `∂_k ∂̄_k`-derivative of the regularised Bochner–Martinelli kernel.** -/
lemma flatLap_dCoord_dbarCoord_bmKerEps {n : ℕ} (j k : Fin n) {ε : ℝ} (hε : 0 < ε)
    (x : Fin n → ℂ) :
    Work.CR.Flat.dCoord k (fun w => Work.CR.Flat.dbarCoord k (bmKerEps j ε) w) x
      = (if k = j then
            ((((-(n : ℤ) : ℝ)) * (nrmSq x + ε ^ 2) ^ (-(n : ℤ) - 1) : ℝ) : ℂ) * star (x k)
          else 0)
        + star (x j)
            * (((((-(n : ℤ) : ℝ)) * (((-(n : ℤ) : ℝ)) - 1))
                * (nrmSq x + ε ^ 2) ^ (-(n : ℤ) - 2) : ℝ) : ℂ)
            * star (x k) * x k
        + star (x j) * ((((-(n : ℤ) : ℝ)) * (nrmSq x + ε ^ 2) ^ (-(n : ℤ) - 1) : ℝ) : ℂ) := by
  set P1 : ℝ := ((-(n : ℤ) : ℝ)) * (nrmSq x + ε ^ 2) ^ (-(n : ℤ) - 1) with hP1
  set P2 : ℝ := (((-(n : ℤ) : ℝ)) * (((-(n : ℤ) : ℝ)) - 1)) * (nrmSq x + ε ^ 2) ^ (-(n : ℤ) - 2)
    with hP2
  set Afin : (Fin n → ℂ) → ℂ :=
    fun w => (if k = j then (((nrmSq w + ε ^ 2) ^ (-(n : ℤ)) : ℝ) : ℂ) else 0) with hAfin
  set Bfin : (Fin n → ℂ) → ℂ :=
    fun w => star (w j) * ((((-(n : ℤ) : ℝ)) * (nrmSq w + ε ^ 2) ^ (-(n : ℤ) - 1) : ℝ) : ℂ) * w k
    with hBfin
  have hdiff_star : DifferentiableAt ℝ (fun w : Fin n → ℂ => star (w j)) x :=
    differentiableAt_star_coord j x
  have hdiff_F : DifferentiableAt ℝ
      (fun w : Fin n → ℂ => (((nrmSq w + ε ^ 2) ^ (-(n : ℤ)) : ℝ) : ℂ)) x :=
    flatLap_differentiableAt_ofReal_comp_nrmSq
      (flatLap_hasDerivAt_radProf (n := n) hε (nrmSq_nonneg x))
  have hdiff_F' : DifferentiableAt ℝ
      (fun w : Fin n → ℂ => ((((-(n : ℤ) : ℝ)) * (nrmSq w + ε ^ 2) ^ (-(n : ℤ) - 1) : ℝ) : ℂ)) x :=
    flatLap_differentiableAt_ofReal_comp_nrmSq
      (flatLap_hasDerivAt_radProfDeriv (n := n) hε (nrmSq_nonneg x))
  have hdiff_coord : DifferentiableAt ℝ (fun w : Fin n → ℂ => w k) x := by
    have h : (fun w : Fin n → ℂ => w k)
        = ⇑(((ContinuousLinearMap.proj k : (Fin n → ℂ) →L[ℂ] ℂ)).restrictScalars ℝ) := by
      funext w; simp
    rw [h]
    exact (((ContinuousLinearMap.proj k : (Fin n → ℂ) →L[ℂ] ℂ)).restrictScalars ℝ).differentiableAt
  have hdiffA : DifferentiableAt ℝ Afin x := by
    by_cases hkj : k = j
    · rw [hAfin]
      rw [show (fun w : Fin n → ℂ =>
              (if k = j then (((nrmSq w + ε ^ 2) ^ (-(n : ℤ)) : ℝ) : ℂ) else 0))
            = (fun w : Fin n → ℂ => (((nrmSq w + ε ^ 2) ^ (-(n : ℤ)) : ℝ) : ℂ)) from by
          funext w; rw [if_pos hkj]]
      exact hdiff_F
    · rw [hAfin]
      rw [show (fun w : Fin n → ℂ =>
              (if k = j then (((nrmSq w + ε ^ 2) ^ (-(n : ℤ)) : ℝ) : ℂ) else 0))
            = (fun _ : Fin n → ℂ => (0 : ℂ)) from by funext w; rw [if_neg hkj]]
      exact differentiableAt_const 0
  have hdiffB : DifferentiableAt ℝ Bfin x := by
    rw [hBfin]
    exact (hdiff_star.mul hdiff_F').mul hdiff_coord
  have hdb : ∀ w, Work.CR.Flat.dbarCoord k (bmKerEps j ε) w = Afin w + Bfin w := by
    intro w
    rw [hAfin, hBfin]
    exact flatLap_dbarCoord_bmKerEps (n := n) j hε k w
  have hA : Work.CR.Flat.dCoord k Afin x
      = (if k = j then (P1 : ℂ) * star (x k) else 0) := by
    by_cases hkj : k = j
    · rw [if_pos hkj, hAfin]
      rw [show (fun w : Fin n → ℂ =>
              (if k = j then (((nrmSq w + ε ^ 2) ^ (-(n : ℤ)) : ℝ) : ℂ) else 0))
            = (fun w : Fin n → ℂ => (((nrmSq w + ε ^ 2) ^ (-(n : ℤ)) : ℝ) : ℂ)) from by
          funext w; rw [if_pos hkj]]
      rw [dCoord_comp_nrmSq (n := n) (z := x) k
        (Φ := fun t : ℝ => (t + ε ^ 2) ^ (-(n : ℤ))) (Φ' := P1)
        (flatLap_hasDerivAt_radProf (n := n) hε (nrmSq_nonneg x))]
    · rw [if_neg hkj, hAfin]
      rw [show (fun w : Fin n → ℂ =>
              (if k = j then (((nrmSq w + ε ^ 2) ^ (-(n : ℤ)) : ℝ) : ℂ) else 0))
            = (fun _ : Fin n → ℂ => (0 : ℂ)) from by funext w; rw [if_neg hkj]]
      exact flatLap_dCoord_const k 0 x
  have hB : Work.CR.Flat.dCoord k Bfin x
      = star (x j) * (P2 : ℂ) * star (x k) * x k + star (x j) * (P1 : ℂ) := by
    rw [hBfin]
    rw [dCoord_mul k
      (fun w : Fin n → ℂ =>
        star (w j) * ((((-(n : ℤ) : ℝ)) * (nrmSq w + ε ^ 2) ^ (-(n : ℤ) - 1) : ℝ) : ℂ))
      (fun w : Fin n → ℂ => w k) x (hdiff_star.mul hdiff_F') hdiff_coord]
    have hC : Work.CR.Flat.dCoord k
          (fun w : Fin n → ℂ =>
            star (w j) * ((((-(n : ℤ) : ℝ)) * (nrmSq w + ε ^ 2) ^ (-(n : ℤ) - 1) : ℝ) : ℂ)) x
        = star (x j) * (P2 : ℂ) * star (x k) := by
      rw [dCoord_mul k (fun w : Fin n → ℂ => star (w j))
        (fun w : Fin n → ℂ =>
          ((((-(n : ℤ) : ℝ)) * (nrmSq w + ε ^ 2) ^ (-(n : ℤ) - 1) : ℝ) : ℂ)) x
        hdiff_star hdiff_F',
        dCoord_apply_conj_coord k j x, zero_mul, zero_add]
      rw [dCoord_comp_nrmSq (n := n) (z := x) k
        (Φ := fun t : ℝ => (((-(n : ℤ) : ℝ)) * (t + ε ^ 2) ^ (-(n : ℤ) - 1))) (Φ' := P2)
        (flatLap_hasDerivAt_radProfDeriv (n := n) hε (nrmSq_nonneg x))]
      ring
    rw [hC, flatLap_dCoord_apply_coord k k x, if_pos rfl]
    ring
  have key : Work.CR.Flat.dCoord k (fun w => Work.CR.Flat.dbarCoord k (bmKerEps j ε) w) x
      = Work.CR.Flat.dCoord k (Afin + Bfin) x := by
    congr 1
    funext w
    exact hdb w
  rw [key, flatLap_dCoord_add k Afin Bfin x hdiffA hdiffB, hA, hB]
  ring

/-- **The Laplacian of the regularised Bochner–Martinelli kernel.**  With
`bmKerEps j ε x = \bar x_j / (‖x‖² + ε²)^n` (see `Work.CR.Flat.Cauchy.bmKerEps`) and
`flatLap f = 4 Σ_k ∂_k ∂̄_k f` (see `Work.NN.Core.czB_L2_defs`),
`flatLap (bmKerEps j ε) x = -4·n·(n+1)·ε²·\bar x_j / (‖x‖² + ε²)^{n+2}`, written with the
integer power `(nrmSq x + ε²)^{-(n+2)}`.

Route.  `bmKerEps j ε x = star(x j) * f (nrmSq x)` with `f t = (t+ε²)^{-n}` (see
`Work.CR.Flat.Cauchy.bmKerEps_eq_zpow`).  Compute `∂̄_k` first:
`∂̄_k (star(x j) * f(nrmSq)) = δ_{kj} f + star(x j) f'(nrmSq) * x_k` (product rule
`Work.CR.Flat.Polydisc.dbarCoord_mul`, `Work.CR.Flat.Polydisc.dbarCoord_apply_conj_coord`,
radial chain rule `Work.CR.Flat.Cauchy.dbarCoord_comp_nrmSq`).  Then `∂_k` of that:
`∂_k(δ_{kj} f) = δ_{kj} f'(nrmSq) * star(x k)` and
`∂_k(star(x j) f'(nrmSq) x_k) = star(x j) (f''(nrmSq)|x_k|² + f'(nrmSq))` (product rule,
radial chain rule for `∂` `dCoord_comp_nrmSq` in `Submission.Work.CR.Flat.Cauchy.bmDzKernel_ibp`,
`∂_k star(x j) = 0`, `∂_k x_k = 1`).  Summing over `k` and using `Σ_k |x_k|² = nrmSq x` gives
`Σ_k ∂_k ∂̄_k (bmKerEps j ε) x = star(x j) * ((n+1) f'(nrmSq x) + f''(nrmSq x) * nrmSq x)`;
with `f(t) = (t+ε²)^{-n}` the bracket is `-n(n+1)ε²(nrmSq x+ε²)^{-n-2}`.  Note
`Work.CR.Flat.Cauchy.bmKerEpsDivergence` proves the analogous first-order statement
`Σ_k ∂̄_k (bmKerEps k ε) = n ε² (nrmSq x+ε²)^{-(n+1)}` and is a good template. -/
theorem flatLap_bmKerEps {n : ℕ} (j : Fin n) {ε : ℝ} (hε : 0 < ε) (x : Fin n → ℂ) :
    flatLap (fun y => bmKerEps j ε y) x
      = (-4 * (n : ℝ) * ((n : ℝ) + 1) * ε ^ 2 : ℂ) * star (x j)
          * ((((nrmSq x + ε ^ 2) ^ (-(n : ℤ) - 2) : ℝ)) : ℂ) := by
  rw [flatLap_apply]
  set P1 : ℝ := ((-(n : ℤ) : ℝ)) * (nrmSq x + ε ^ 2) ^ (-(n : ℤ) - 1) with hP1
  set P2 : ℝ := (((-(n : ℤ) : ℝ)) * (((-(n : ℤ) : ℝ)) - 1)) * (nrmSq x + ε ^ 2) ^ (-(n : ℤ) - 2)
    with hP2
  have hterm : ∀ k : Fin n,
      Work.CR.Flat.dCoord k (fun w => Work.CR.Flat.dbarCoord k (bmKerEps j ε) w) x
        = (if k = j then (P1 : ℂ) * star (x k) else 0)
          + star (x j) * (P2 : ℂ) * star (x k) * x k
          + star (x j) * (P1 : ℂ) := by
    intro k
    exact flatLap_dCoord_dbarCoord_bmKerEps (n := n) j k hε x
  have hs1 : ∑ k : Fin n, (if k = j then (P1 : ℂ) * star (x k) else 0)
      = (P1 : ℂ) * star (x j) := by
    rw [Finset.sum_eq_single j]
    · rw [if_pos rfl]
    · intro k _ hk; rw [if_neg hk]
    · intro h; exact absurd (Finset.mem_univ j) h
  have hs2 : ∑ k : Fin n, star (x j) * (P2 : ℂ) * star (x k) * x k
      = star (x j) * (P2 : ℂ) * (((nrmSq x : ℝ)) : ℂ) := by
    rw [show (∑ k : Fin n, star (x j) * (P2 : ℂ) * star (x k) * x k)
          = ∑ k : Fin n, (star (x j) * (P2 : ℂ)) * (star (x k) * x k) from
        Finset.sum_congr rfl (fun k _ => by ring)]
    rw [← Finset.mul_sum, Work.CR.Flat.Cauchy.sum_conj_mul_self]
  have hs3 : ∑ _k : Fin n, star (x j) * (P1 : ℂ)
      = ((n : ℝ) : ℂ) * (star (x j) * (P1 : ℂ)) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  have hsum : ∑ k : Fin n, Work.CR.Flat.dCoord k (fun w => Work.CR.Flat.dbarCoord k (bmKerEps j ε) w) x
      = star (x j) * ((((n : ℝ) + 1) * P1 + P2 * nrmSq x : ℝ) : ℂ) := by
    rw [show (∑ k : Fin n, Work.CR.Flat.dCoord k (fun w => Work.CR.Flat.dbarCoord k (bmKerEps j ε) w) x)
          = ∑ k : Fin n, ((if k = j then (P1 : ℂ) * star (x k) else 0)
              + star (x j) * (P2 : ℂ) * star (x k) * x k
              + star (x j) * (P1 : ℂ)) from Finset.sum_congr rfl (fun k _ => hterm k)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hs1, hs2, hs3]
    rw [show ((((n : ℝ) + 1) * P1 + P2 * nrmSq x : ℝ) : ℂ)
          = (((n : ℝ) : ℂ) + 1) * (P1 : ℂ) + (P2 : ℂ) * (((nrmSq x : ℝ)) : ℂ) by
        push_cast; ring]
    ring
  rw [hsum]
  have halg : ((n : ℝ) + 1) * P1 + P2 * nrmSq x
      = -(n : ℝ) * ((n : ℝ) + 1) * ε ^ 2 * (nrmSq x + ε ^ 2) ^ (-(n : ℤ) - 2) := by
    rw [hP1, hP2]
    exact flatLap_radial_algebra hε (nrmSq_nonneg x)
  have hB : ((((n : ℝ) + 1) * P1 + P2 * nrmSq x : ℝ) : ℂ)
      = (((-(n : ℝ) * ((n : ℝ) + 1) * ε ^ 2 : ℝ)) : ℂ)
          * ((((nrmSq x + ε ^ 2) ^ (-(n : ℤ) - 2) : ℝ)) : ℂ) := by
    rw [halg]
    push_cast
    ring
  rw [hB]
  push_cast
  ring_nf

end Work.NN.Core
