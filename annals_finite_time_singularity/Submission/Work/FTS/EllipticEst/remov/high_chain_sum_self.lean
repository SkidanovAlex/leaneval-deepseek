import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Self-contained copy of the `∂_θ^m`-chain and of `remov.high_chain_sum`

This module reproduces, verbatim and under the fresh namespace
`Work.FTS.EllipticEst.remov.selfdth`, the declarations on which
`Work.FTS.EllipticEst.remov.high_chain_sum` rests:

* `dthCoef` and its basic properties (from `FTS/EllipticEst/alphaDzDthW_Hk_le.lean`),
* `dthCoef_succ_mul_sum` (from `FTS/EllipticEst/DthIter_expansion_identity.lean`),
* the exact angular expansion `DthIter_expansion_local` and the divisibility/boundedness of the
  coefficients (from `FTS/EllipticEst/remov/DthIter_expansion.lean`),
* `dthCoef_succ_zero` (from `FTS/EllipticEst/dthCoef_bound_fixed.lean`),
* `dthChain_core` (from `FTS/EllipticEst/remov/dthChain_core.lean`),
* the two integration-pushing lemmas and the slot identity
  (from `remov/theta_slice_mono.lean`, `remov/z_integral_mono_const.lean`,
  `remov/slot_sq_eq_Wt_sq.lean`),

and then proves the target `Work.FTS.EllipticEst.remov.high_chain_sum_self`, which has the same
statement as `remov.high_chain_sum`.

The point of the copy is that the import cone of `remov.high_chain_sum` is currently broken by an
unrelated in-flight module; this module imports only `Mathlib` and
`Submission.Work.Spaces.{Defs, HkSq_terms}` (kept unchanged), so the whole cone builds.

The TRAP documented in the original is preserved: the chain uses the EXACT expansion
`DthIter_expansion_local` together with the vanishing `dthCoef m 0 = 0` (`m ≥ 1`), NOT the weaker
two-sided `DthIter_expansion` inequality, whose `r = 0` term would produce the
`∫ v²w²sin^{-γ}` summand that is not controlled by `HkSq`.
-/

namespace Work.FTS.EllipticEst.remov

open MeasureTheory Filter

namespace selfdth

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The coefficients `a_{i,m}` of `D_θ^i = Σ_{m ≤ i} a_{i,m} ∂_θ^m` -/


def dthCoef : ℕ → ℕ → ℝ → ℝ
  | 0, 0 => fun _ => 1
  | 0, _ + 1 => fun _ => 0
  | i + 1, m => fun θ => Real.sin (2 * θ) *
      (deriv (dthCoef i m) θ + if 1 ≤ m then dthCoef i (m - 1) θ else 0)

/-- All the coefficients vanish above the diagonal: `a_{i,m} = 0` for `m > i`. -/
theorem dthCoef_zero_of_gt {i m : ℕ} (h : i < m) : dthCoef i m = 0 := by
  induction i generalizing m with
  | zero =>
      rcases m with _ | m
      · omega
      · rfl
  | succ i ih =>
      have hm : 1 ≤ m := by omega
      have h1 : dthCoef i m = 0 := ih (by omega)
      have h2 : dthCoef i (m - 1) = 0 := ih (by omega)
      funext θ
      show Real.sin (2 * θ) *
          (deriv (dthCoef i m) θ + (if 1 ≤ m then dthCoef i (m - 1) θ else 0)) = 0
      rw [h1, h2, if_pos hm]
      simp

/-- The leading coefficient is `sin(2θ)^i`. -/
theorem dthCoef_self (i : ℕ) : dthCoef i i = fun θ => (Real.sin (2 * θ)) ^ i := by
  induction i with
  | zero => rfl
  | succ i ih =>
      have h0 : dthCoef i (i + 1) = 0 := dthCoef_zero_of_gt (by omega)
      funext θ
      show Real.sin (2 * θ) *
          (deriv (dthCoef i (i + 1)) θ + (if 1 ≤ i + 1 then dthCoef i (i + 1 - 1) θ else 0))
        = (Real.sin (2 * θ)) ^ (i + 1)
      rw [h0, if_pos (by omega), show i + 1 - 1 = i from by omega, ih]
      simp [pow_succ]
      ring

/-- The coefficients are smooth. -/
theorem contDiff_dthCoef (i m : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (dthCoef i m) := by
  induction i generalizing m with
  | zero =>
      rcases m with _ | m
      · exact contDiff_const
      · exact contDiff_const
  | succ i ih =>
      have h1 : ContDiff ℝ (⊤ : ℕ∞) (deriv (dthCoef i m)) := by
        simpa using (contDiff_infty_iff_deriv (𝕜 := ℝ) (f := dthCoef i m)).mp (ih m) |>.2
      have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun θ => if 1 ≤ m then dthCoef i (m - 1) θ else 0) := by
        by_cases hm : 1 ≤ m
        · simp only [if_pos hm]; exact ih (m - 1)
        · simp only [if_neg hm]; exact contDiff_const
      exact (((Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)).mul
        (h1.add h2)))


/-! ## The recursion of the coefficients, read as an identity between sums -/


theorem dthCoef_succ_mul_sum (i : ℕ) (v : ℕ → ℝ) (θ : ℝ) :
    (∑ m ∈ Finset.range (i + 2), dthCoef (i + 1) m θ * v m)
      = Real.sin (2 * θ) * ∑ m ∈ Finset.range (i + 1),
          (deriv (dthCoef i m) θ * v m + dthCoef i m θ * v (m + 1)) := by
  have hterm : ∀ m : ℕ, dthCoef (i + 1) m θ
      = Real.sin (2 * θ) * (deriv (dthCoef i m) θ
          + (if 1 ≤ m then dthCoef i (m - 1) θ else 0)) := fun m => rfl
  have hlast : deriv (dthCoef i (i + 1)) θ = 0 := by
    have hz : dthCoef i (i + 1) = fun _ : ℝ => (0 : ℝ) :=
      dthCoef_zero_of_gt (show i < i + 1 by omega)
    rw [hz, deriv_const]
  have hA : (∑ m ∈ Finset.range (i + 2), deriv (dthCoef i m) θ * v m)
      = ∑ m ∈ Finset.range (i + 1), deriv (dthCoef i m) θ * v m := by
    rw [Finset.sum_range_succ, hlast, zero_mul, add_zero]
  have hB : (∑ m ∈ Finset.range (i + 2),
        (if 1 ≤ m then dthCoef i (m - 1) θ else 0) * v m)
      = ∑ m ∈ Finset.range (i + 1), dthCoef i m θ * v (m + 1) := by
    rw [Finset.sum_range_succ']
    have h0 : (if 1 ≤ 0 then dthCoef i (0 - 1) θ else 0) * v 0 = 0 := by simp
    rw [h0, add_zero]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp
  calc (∑ m ∈ Finset.range (i + 2), dthCoef (i + 1) m θ * v m)
      = ∑ m ∈ Finset.range (i + 2), Real.sin (2 * θ) *
          (deriv (dthCoef i m) θ * v m
            + (if 1 ≤ m then dthCoef i (m - 1) θ else 0) * v m) := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [hterm m]
        ring
    _ = Real.sin (2 * θ) * ∑ m ∈ Finset.range (i + 2),
          (deriv (dthCoef i m) θ * v m
            + (if 1 ≤ m then dthCoef i (m - 1) θ else 0) * v m) := by
        rw [Finset.mul_sum]
    _ = Real.sin (2 * θ) * ((∑ m ∈ Finset.range (i + 1), deriv (dthCoef i m) θ * v m)
          + ∑ m ∈ Finset.range (i + 1), dthCoef i m θ * v (m + 1)) := by
        rw [Finset.sum_add_distrib, hA, hB]
    _ = Real.sin (2 * θ) * ∑ m ∈ Finset.range (i + 1),
          (deriv (dthCoef i m) θ * v m + dthCoef i m θ * v (m + 1)) := by
        rw [Finset.sum_add_distrib]


/-! ## The local expansion identity and the coefficient bounds -/


local notation "Cinf" => ((⊤ : ℕ∞) : WithTop ℕ∞)



/-! ## Part 1: the local expansion identity -/

/-- `↑(n+1) = ↑n + 1` for the canonical coercion `ℕ → WithTop ℕ∞`. -/
theorem natCast_succ (n : ℕ) :
    (((n + 1 : ℕ)) : WithTop ℕ∞) = ((n : ℕ) : WithTop ℕ∞) + 1 := by
  push_cast; ring

/-- The `θ`-slice of a function of two variables that is `C^N` at a point is `C^N` at the
corresponding point of the line. -/
theorem contDiffAt_slice_snd_of_uncurry {f : ℝ → ℝ → ℝ} {z θ : ℝ} {N : ℕ}
    (h : ContDiffAt ℝ ((N : ℕ) : WithTop ℕ∞) (Function.uncurry f) (z, θ)) :
    ContDiffAt ℝ ((N : ℕ) : WithTop ℕ∞) (fun θ' => f z θ') θ := by
  have hlin : ContDiffAt ℝ ((N : ℕ) : WithTop ℕ∞) (fun θ' : ℝ => (z, θ')) θ := by fun_prop
  have hcomp := ContDiffAt.comp θ h hlin
  simpa [Function.comp_def] using hcomp

/-- The derivative of a function that is `C^{n+1}` at a point is `C^n` at that point. -/
theorem contDiffAt_deriv_of_succ {g : ℝ → ℝ} {x : ℝ} {n : ℕ}
    (h : ContDiffAt ℝ (((n + 1 : ℕ)) : WithTop ℕ∞) g x) :
    ContDiffAt ℝ ((n : ℕ) : WithTop ℕ∞) (deriv g) x :=
  h.derivWithin (m := ((n : ℕ) : WithTop ℕ∞)) (by push_cast; simp)

/-- Iterated derivatives lower the order of differentiability. -/
theorem contDiffAt_iteratedDeriv_of_add {φ : ℝ → ℝ} {θ : ℝ} :
    ∀ (k M : ℕ), ContDiffAt ℝ (((M + k : ℕ)) : WithTop ℕ∞) φ θ →
      ContDiffAt ℝ ((M : ℕ) : WithTop ℕ∞) (iteratedDeriv k φ) θ := by
  intro k
  induction k with
  | zero => intro M h; simpa using h
  | succ k ih =>
      intro M h
      rw [iteratedDeriv_succ]
      have hM : ContDiffAt ℝ (((M + 1 + k : ℕ)) : WithTop ℕ∞) φ θ := by
        rw [show M + 1 + k = M + (k + 1) by omega]
        exact h
      exact contDiffAt_deriv_of_succ (n := M) (ih (M + 1) hM)

/-- If `φ` is `C^N` at `θ` then its `k`-th iterated derivative is `C^{N-k}` at `θ`. -/
theorem contDiffAt_iteratedDeriv_of_le {φ : ℝ → ℝ} {θ : ℝ} {k N : ℕ} (hk : k ≤ N)
    (h : ContDiffAt ℝ ((N : ℕ) : WithTop ℕ∞) φ θ) :
    ContDiffAt ℝ (((N - k : ℕ)) : WithTop ℕ∞) (iteratedDeriv k φ) θ := by
  have h' : ContDiffAt ℝ ((((N - k) + k : ℕ)) : WithTop ℕ∞) φ θ := by
    rwa [Nat.sub_add_cancel hk]
  exact contDiffAt_iteratedDeriv_of_add k (N - k) h'

/-- If `φ` is `C^N` at `θ` with `k + 1 ≤ N`, its `k`-th iterated derivative is differentiable
at `θ`. -/
theorem differentiableAt_iteratedDeriv_of_le {φ : ℝ → ℝ} {θ : ℝ} {k N : ℕ}
    (h : ContDiffAt ℝ ((N : ℕ) : WithTop ℕ∞) φ θ) (hk : k + 1 ≤ N) :
    DifferentiableAt ℝ (iteratedDeriv k φ) θ := by
  have h1 := contDiffAt_iteratedDeriv_of_le (Nat.le_of_succ_le hk) h
  have hne : (((N - k : ℕ)) : WithTop ℕ∞) ≠ 0 := by
    intro hzero
    have : N - k = 0 := by exact_mod_cast hzero
    omega
  exact h1.differentiableAt hne

/-- `pthIter r f z θ` is the `r`-th iterated derivative of the `θ`-slice of `f`. -/
theorem pthIter_eq_iteratedDeriv_slice (r : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pthIter r f z θ = iteratedDeriv r (fun θ' => f z θ') θ := by
  induction r generalizing z θ with
  | zero => simp
  | succ k ih =>
      simp only [Work.Spaces.pthIter_succ, Work.Spaces.pth, iteratedDeriv_succ]
      congr 1
      funext θ'
      exact ih z θ'

/-- `∂_θ (pthIter r f z ·) θ = pthIter (r+1) f z θ`. -/
theorem deriv_pthIter_slice (r : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    deriv (fun θ' => Work.Spaces.pthIter r f z θ') θ = Work.Spaces.pthIter (r + 1) f z θ := by
  rw [Work.Spaces.pthIter_succ]
  rfl

/-- The exact expansion of `D_θ^m` in terms of the plain angular derivatives, at a point where
`f` is `C^{m+1}` and, more precisely, `C^{m+1}` on an open set containing the point. -/
theorem DthIter_expansion_of_contDiffOn :
    ∀ (m : ℕ) (f : ℝ → ℝ → ℝ) (U : Set (ℝ × ℝ)), IsOpen U →
      ContDiffOn ℝ (((m + 1 : ℕ)) : WithTop ℕ∞) (Function.uncurry f) U →
      ∀ z θ, (z, θ) ∈ U →
        Work.Spaces.DthIter m f z θ
          = ∑ r ∈ Finset.range (m + 1),
              dthCoef m r θ * Work.Spaces.pthIter r f z θ := by
  intro m
  induction m with
  | zero =>
      intro f U hU hsm z θ hzθ
      simp only [Work.Spaces.DthIter_zero, Work.Spaces.pthIter_zero]
      rw [Finset.sum_range_succ (f := fun r =>
        dthCoef 0 r θ * Work.Spaces.pthIter r f z θ) 0]
      simp [dthCoef]
  | succ m ih =>
      intro f U hU hsm z θ hzθ
      have hle : (((m + 1 : ℕ)) : WithTop ℕ∞) ≤ (((m + 2 : ℕ)) : WithTop ℕ∞) := by
        exact_mod_cast (by omega : m + 1 ≤ m + 2)
      have hsm_m : ContDiffOn ℝ (((m + 1 : ℕ)) : WithTop ℕ∞) (Function.uncurry f) U :=
        fun y hy => (hsm y hy).of_le hle
      have hsl_mem : {θ' : ℝ | (z, θ') ∈ U} ∈ 𝓝 θ := by
        apply IsOpen.mem_nhds
        · exact hU.preimage (by fun_prop : Continuous fun θ' : ℝ => (z, θ'))
        · exact hzθ
      have hev : (fun θ' => Work.Spaces.DthIter m f z θ')
          =ᶠ[𝓝 θ] (fun θ' => ∑ r ∈ Finset.range (m + 1),
              dthCoef m r θ' * Work.Spaces.pthIter r f z θ') := by
        filter_upwards [hsl_mem] with θ' hθ'
        exact ih f U hU hsm_m z θ' hθ'
      have hslice : ∀ r, r ≤ m → DifferentiableAt ℝ
          (fun θ' => Work.Spaces.pthIter r f z θ') θ := by
        intro r hr
        have hcdU : ContDiffWithinAt ℝ (((m + 2 : ℕ)) : WithTop ℕ∞)
            (Function.uncurry f) U (z, θ) := hsm (z, θ) hzθ
        have hcdAt : ContDiffAt ℝ (((m + 2 : ℕ)) : WithTop ℕ∞)
            (Function.uncurry f) (z, θ) :=
          hcdU.mono_of_mem_nhdsWithin (by rw [nhdsWithin_univ]; exact hU.mem_nhds hzθ)
        have hcdr : ContDiffAt ℝ (((r + 1 : ℕ)) : WithTop ℕ∞)
            (Function.uncurry f) (z, θ) :=
          hcdAt.of_le (by exact_mod_cast (by omega : r + 1 ≤ m + 2))
        have hslice_cd : ContDiffAt ℝ (((r + 1 : ℕ)) : WithTop ℕ∞)
            (fun θ' => f z θ') θ := contDiffAt_slice_snd_of_uncurry hcdr
        have heq : (fun θ' => Work.Spaces.pthIter r f z θ')
            = iteratedDeriv r (fun θ' => f z θ') := by
          funext θ'
          exact pthIter_eq_iteratedDeriv_slice r f z θ'
        rw [heq]
        exact differentiableAt_iteratedDeriv_of_le hslice_cd le_rfl
      have hdcoef : ∀ r, DifferentiableAt ℝ (dthCoef m r) θ := fun r =>
        (contDiff_dthCoef m r).contDiffAt.differentiableAt (by simp)
      have hfun : (fun θ' => ∑ r ∈ Finset.range (m + 1),
              dthCoef m r θ' * Work.Spaces.pthIter r f z θ')
          = ∑ r ∈ Finset.range (m + 1),
              (fun θ' => dthCoef m r θ' * Work.Spaces.pthIter r f z θ') := by
        funext θ'
        rw [Finset.sum_apply]
      have hsumderiv : deriv (fun θ' => ∑ r ∈ Finset.range (m + 1),
            dthCoef m r θ' * Work.Spaces.pthIter r f z θ') θ
          = ∑ r ∈ Finset.range (m + 1),
              (deriv (dthCoef m r) θ * Work.Spaces.pthIter r f z θ
                + dthCoef m r θ * Work.Spaces.pthIter (r + 1) f z θ) := by
        rw [hfun, deriv_sum]
        · refine Finset.sum_congr rfl fun r hr => ?_
          have hr' : r ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
          have hprod : (fun θ' => dthCoef m r θ'
                * Work.Spaces.pthIter r f z θ')
              = dthCoef m r
                * (fun θ' => Work.Spaces.pthIter r f z θ') := rfl
          rw [hprod, deriv_mul (hdcoef r) (hslice r hr'), deriv_pthIter_slice]
        · intro r hr
          have hr' : r ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
          exact (hdcoef r).mul (hslice r hr')
      rw [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
      rw [hev.deriv_eq, hsumderiv]
      exact (dthCoef_succ_mul_sum m
        (fun r => Work.Spaces.pthIter r f z θ) θ).symm

/-- **The local expansion identity**: at every point `(z,θ)` where `f` is `C^∞`,
`D_θ^m f = Σ_{r ≤ m} a_{m,r}(θ) ∂_θ^r f`. -/
theorem DthIter_expansion_local (m : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ)
    (hf : ∀ k : ℕ, ContDiffAt ℝ k (Function.uncurry f) (z, θ)) :
    Work.Spaces.DthIter m f z θ
      = ∑ r ∈ Finset.range (m + 1),
          dthCoef m r θ * Work.Spaces.pthIter r f z θ := by
  have htop : ContDiffAt ℝ (((m + 1 : ℕ)) : WithTop ℕ∞) (Function.uncurry f) (z, θ) :=
    hf (m + 1)
  obtain ⟨u, hu_mem, -, hcontOn⟩ := ContDiffWithinAt.contDiffOn (s := univ)
    (f := Function.uncurry f) (x := (z, θ))
    (m := (((m + 1 : ℕ)) : WithTop ℕ∞)) (n := (((m + 1 : ℕ)) : WithTop ℕ∞))
    le_rfl (by intro h; exact absurd h (by simp)) htop
  have hu_nhds : u ∈ 𝓝 (z, θ) := by
    simpa [nhdsWithin_univ] using hu_mem
  refine DthIter_expansion_of_contDiffOn m f (interior u) isOpen_interior ?_ z θ ?_
  · intro y hy
    exact (hcontOn y (interior_subset hy)).mono interior_subset
  · exact mem_of_mem_nhds (interior_mem_nhds.mpr hu_nhds)

/-! ## Part 2: the coefficient `a_{m,r}` is divisible by `sin(2θ)^r`, with bounded quotient -/

/-- The quotient `b_{m,r} = a_{m,r}/sin(2θ)^r`, defined by the recursion obtained from the
recursion of `dthCoef`. -/
noncomputable def dB : ℕ → ℕ → ℝ → ℝ
  | 0, 0 => fun _ => 1
  | 0, _ + 1 => fun _ => 0
  | m + 1, r => fun θ =>
      (r : ℝ) * (2 * Real.cos (2 * θ)) * dB m r θ
        + Real.sin (2 * θ) * deriv (dB m r) θ
        + (if 1 ≤ r then dB m (r - 1) θ else 0)

@[simp] theorem dB_zero_zero : dB 0 0 = fun _ : ℝ => 1 := rfl

@[simp] theorem dB_zero_succ (r : ℕ) : dB 0 (r + 1) = fun _ : ℝ => 0 := rfl

theorem dB_succ (m r : ℕ) : dB (m + 1) r = fun θ : ℝ =>
    (r : ℝ) * (2 * Real.cos (2 * θ)) * dB m r θ
      + Real.sin (2 * θ) * deriv (dB m r) θ
      + (if 1 ≤ r then dB m (r - 1) θ else 0) := rfl

/-- Every `dB m r` is `C^∞`. -/
theorem dB_contDiff : ∀ m r : ℕ, ContDiff ℝ Cinf (dB m r) := by
  intro m
  induction m with
  | zero =>
      intro r
      rcases r with _ | k
      · rw [dB_zero_zero]; exact contDiff_const
      · rw [dB_zero_succ]; exact contDiff_const
  | succ m ih =>
      intro r
      have hd : ContDiff ℝ Cinf (deriv (dB m r)) :=
        ((contDiff_infty_iff_deriv (𝕜 := ℝ) (f := dB m r)).mp (ih r)).2
      have hsin : ContDiff ℝ Cinf (fun θ : ℝ => Real.sin (2 * θ)) := by fun_prop
      have hA : ContDiff ℝ Cinf (fun θ : ℝ => (r : ℝ) * (2 * Real.cos (2 * θ))) := by fun_prop
      have hbase : ContDiff ℝ Cinf (fun θ : ℝ =>
          (r : ℝ) * (2 * Real.cos (2 * θ)) * dB m r θ
            + Real.sin (2 * θ) * deriv (dB m r) θ) := (hA.mul (ih r)).add (hsin.mul hd)
      rw [dB_succ]
      by_cases hr : 1 ≤ r
      · simpa [hr] using hbase.add (ih (r - 1))
      · simpa [hr] using hbase

/-- The product-rule computation underlying the recursion of `dB`. -/
theorem deriv_sin_two_pow_mul (r : ℕ) {g : ℝ → ℝ} {θ : ℝ} (hg : DifferentiableAt ℝ g θ) :
    deriv (fun θ' => (Real.sin (2 * θ')) ^ r * g θ') θ
      = (r : ℝ) * (Real.sin (2 * θ)) ^ (r - 1) * (2 * Real.cos (2 * θ)) * g θ
        + (Real.sin (2 * θ)) ^ r * deriv g θ := by
  have hsin : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (2 * Real.cos (2 * θ)) θ := by
    have h1 : HasDerivAt (fun θ' : ℝ => (2 : ℝ) * θ') 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
    have h2 := (Real.hasDerivAt_sin (2 * θ)).comp θ h1
    have h3 : Real.cos (2 * θ) * 2 = 2 * Real.cos (2 * θ) := by ring
    rw [h3] at h2
    simpa [Function.comp_def] using h2
  have hpow : HasDerivAt (fun θ' : ℝ => (Real.sin (2 * θ')) ^ r)
      ((r : ℝ) * (Real.sin (2 * θ)) ^ (r - 1) * (2 * Real.cos (2 * θ))) θ := hsin.pow r
  have hmul := hpow.mul hg.hasDerivAt
  exact hmul.deriv

/-- **`a_{m,r} = sin(2θ)^r · b_{m,r}`.** -/
theorem dthCoef_eq_sin_pow_mul_dB (m r : ℕ) :
    dthCoef m r = fun θ => (Real.sin (2 * θ)) ^ r * dB m r θ := by
  induction m generalizing r with
  | zero =>
      rcases r with _ | k
      · funext θ; simp [dthCoef]
      · funext θ; simp [dthCoef]
  | succ m ih =>
      rcases r with _ | k
      · funext θ
        show Real.sin (2 * θ) * (deriv (dthCoef m 0) θ
            + (if 1 ≤ (0 : ℕ) then dthCoef m (0 - 1) θ else 0))
          = (Real.sin (2 * θ)) ^ (0 : ℕ) * dB (m + 1) 0 θ
        rw [if_neg (by norm_num : ¬ (1 ≤ (0 : ℕ))), ih 0,
          deriv_sin_two_pow_mul 0 (((dB_contDiff m 0).differentiable (by simp)) θ), dB_succ]
        simp only [Nat.cast_zero, zero_mul, zero_add, pow_zero, one_mul,
          if_neg (by norm_num : ¬ (1 ≤ (0 : ℕ)))]
        ring
      · funext θ
        show Real.sin (2 * θ) * (deriv (dthCoef m (k + 1)) θ
            + (if 1 ≤ (k + 1) then dthCoef m ((k + 1) - 1) θ else 0))
          = (Real.sin (2 * θ)) ^ (k + 1) * dB (m + 1) (k + 1) θ
        rw [if_pos (by omega : 1 ≤ k + 1), Nat.succ_sub_one, ih (k + 1), ih k,
          deriv_sin_two_pow_mul (k + 1) (((dB_contDiff m (k + 1)).differentiable (by simp)) θ),
          dB_succ]
        simp only [Nat.succ_sub_one, if_pos (by omega : 1 ≤ k + 1), Nat.cast_add, Nat.cast_one,
          pow_succ']
        ring

/-- The derivative of a `π`-periodic differentiable function is `π`-periodic. -/
theorem deriv_periodic_pi {g : ℝ → ℝ} (hg : ∀ θ, g (θ + π) = g θ)
    (hgd : Differentiable ℝ g) : ∀ θ, deriv g (θ + π) = deriv g θ := by
  intro θ
  have h1 : HasDerivAt (fun x : ℝ => g (x + π)) (deriv g (θ + π) * 1) θ := by
    have hinner : HasDerivAt (fun x : ℝ => x + π) 1 θ := by
      simpa using (hasDerivAt_id θ).add_const π
    have h2 := (hgd (θ + π)).hasDerivAt.comp θ hinner
    simpa [Function.comp_def] using h2
  have h2 : (fun x : ℝ => g (x + π)) = g := funext hg
  rw [h2] at h1
  have h3 := h1.deriv
  simp only [mul_one] at h3
  exact h3.symm

/-- Every `dB m r` is `π`-periodic. -/
theorem dB_periodic : ∀ m : ℕ, ∀ r : ℕ, ∀ θ : ℝ, dB m r (θ + π) = dB m r θ := by
  intro m
  induction m with
  | zero =>
      intro r θ
      rcases r with _ | k <;> simp [dB]
  | succ m ih =>
      intro r θ
      have hd : ∀ x : ℝ, deriv (dB m r) (x + π) = deriv (dB m r) x :=
        deriv_periodic_pi (ih r) ((dB_contDiff m r).differentiable (by simp))
      have hs : Real.sin (2 * (θ + π)) = Real.sin (2 * θ) := by
        rw [show 2 * (θ + π) = 2 * θ + 2 * π by ring, Real.sin_add_two_pi]
      have hc : Real.cos (2 * (θ + π)) = Real.cos (2 * θ) := by
        rw [show 2 * (θ + π) = 2 * θ + 2 * π by ring, Real.cos_add_two_pi]
      rw [dB_succ]
      change (r : ℝ) * (2 * Real.cos (2 * (θ + π))) * dB m r (θ + π)
          + Real.sin (2 * (θ + π)) * deriv (dB m r) (θ + π)
          + (if 1 ≤ r then dB m (r - 1) (θ + π) else 0)
        = (r : ℝ) * (2 * Real.cos (2 * θ)) * dB m r θ
          + Real.sin (2 * θ) * deriv (dB m r) θ
          + (if 1 ≤ r then dB m (r - 1) θ else 0)
      rw [hs, hc, ih r θ, ih (r - 1) θ, hd θ]

/-- Every `dB m r` is bounded. -/
theorem dB_bounded (m r : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ θ : ℝ, |dB m r θ| ≤ K := by
  have hcont : Continuous (dB m r) := (dB_contDiff m r).continuous
  have hIc : IsCompact (Set.Icc (0 : ℝ) π) := isCompact_Icc
  obtain ⟨C, hC⟩ := hIc.exists_bound_of_continuousOn (f := dB m r) hcont.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun θ => ?_⟩
  have hπ : 0 < π := Real.pi_pos
  obtain ⟨n, θ₀, hθ₀, hge, hle⟩ : ∃ n : ℤ, ∃ θ₀ : ℝ,
      θ₀ = θ - (n : ℝ) * π ∧ 0 ≤ θ₀ ∧ θ₀ ≤ π := by
    refine ⟨Int.floor (θ / π), θ - (Int.floor (θ / π) : ℝ) * π, rfl, ?_, ?_⟩
    · have h1 : ((Int.floor (θ / π) : ℤ) : ℝ) ≤ θ / π := Int.floor_le (θ / π)
      have h2 : ((Int.floor (θ / π) : ℤ) : ℝ) * π ≤ θ := (le_div_iff₀ hπ).mp h1
      linarith
    · have h1 : θ / π < ((Int.floor (θ / π) : ℤ) : ℝ) + 1 := Int.lt_floor_add_one (θ / π)
      have h2 : θ < ((Int.floor (θ / π) : ℤ) : ℝ) * π + π := by
        have := (div_lt_iff₀ hπ).mp h1
        linarith
      linarith
  have hper : Function.Periodic (dB m r) π := dB_periodic m r
  have hkey : dB m r θ = dB m r θ₀ := by
    have h := (hper.int_mul n) θ₀
    rw [show θ₀ + (n : ℝ) * π = θ by rw [hθ₀]; ring] at h
    exact h
  rw [hkey]
  exact le_trans (hC θ₀ ⟨hge, hle⟩) (le_max_left _ _)

/-- **The coefficient bound** `|a_{m,r}(θ)| ≤ K·|sin(2θ)|^r`. -/
theorem DthCoef_sin_pow_bound (m r : ℕ) : ∃ K : ℝ, 0 < K ∧ ∀ θ : ℝ,
    |dthCoef m r θ| ≤ K * |Real.sin (2 * θ)| ^ r := by
  obtain ⟨C, hC0, hC⟩ := dB_bounded m r
  refine ⟨max C 1, lt_max_of_lt_right one_pos, fun θ => ?_⟩
  rw [show dthCoef m r θ
      = (Real.sin (2 * θ)) ^ r * dB m r θ
      from congrFun (dthCoef_eq_sin_pow_mul_dB m r) θ]
  rw [abs_mul, abs_pow]
  have hSpow : 0 ≤ |Real.sin (2 * θ)| ^ r := pow_nonneg (abs_nonneg _) r
  calc |Real.sin (2 * θ)| ^ r * |dB m r θ|
      ≤ |Real.sin (2 * θ)| ^ r * C := mul_le_mul_of_nonneg_left (hC θ) hSpow
    _ ≤ max C 1 * |Real.sin (2 * θ)| ^ r := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right (le_max_left C 1) hSpow


/-! ## `a_{i,0} = 0` for `i ≥ 1` -/


theorem dthCoef_succ_zero (i : ℕ) : dthCoef (i + 1) 0 = 0 := by
  induction i with
  | zero =>
      funext θ
      show Real.sin (2 * θ) * (deriv (dthCoef 0 0) θ +
        (if (1 : ℕ) ≤ 0 then dthCoef 0 (0 - 1) θ else 0)) = 0
      rw [if_neg (by omega)]
      simp [dthCoef]
  | succ i ih =>
      funext θ
      show Real.sin (2 * θ) * (deriv (dthCoef (i + 1) 0) θ +
        (if (1 : ℕ) ≤ 0 then dthCoef (i + 1) (0 - 1) θ else 0)) = 0
      rw [if_neg (by omega), ih]
      simp


/-! ## The `∂_θ^m`-chain -/


/-- The `q = 0` coefficient `b_{r,0}` of the quotient vanishes for `r ≥ 1`. -/
theorem dB_apply_zero_of_one_le (r : ℕ) (hr : 1 ≤ r) : dB r 0 = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  have h0 : dthCoef (j + 1) 0 = 0 :=
    dthCoef_succ_zero j
  have hdiv := dthCoef_eq_sin_pow_mul_dB (j + 1) 0
  funext θ
  have hzero : Real.sin (2 * θ) ^ 0 * dB (j + 1) 0 θ = 0 := by
    rw [← congrFun hdiv θ, congrFun h0 θ]
    simp
  simpa using hzero

/-- Peeling the `q = 0` term off a `range`-sum whose `0`-term vanishes. -/
theorem sum_range_eq_sum_range_pred {A : ℕ → ℝ} (h0 : A 0 = 0) (r : ℕ) :
    ∑ q ∈ Finset.range r, A q = ∑ q ∈ Finset.range (r - 1), A (q + 1) := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr; simp
  · obtain ⟨r', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
    rw [Nat.succ_sub_one, Finset.sum_range_succ', h0, add_zero]

/-- `(a - b)² ≤ 2a² + 2b²`. -/
theorem sq_sub_le_two (a b : ℝ) : (a - b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a + b)]

/-- The triangle inequality for a difference. -/
theorem abs_sub_le_abs_add (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  simpa [sub_eq_add_neg] using abs_add_le a (-b)

theorem dthChain_core (m : ℕ) (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : ℝ → ℝ → ℝ) (z θ : ℝ),
      θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (∀ k : ℕ, ContDiffAt ℝ k (Function.uncurry v) (z, θ)) →
      ((Real.sin (2 * θ)) ^ m * Work.Spaces.pthIter m v z θ) ^ 2
        ≤ C * ∑ r ∈ Finset.Icc 1 m, (Work.Spaces.DthIter r v z θ) ^ 2 := by
  classical
  -- a uniform bound on the coefficients `b_{r,q} = dB r q` for `1 ≤ q ≤ r ≤ m`
  choose KB hKB using fun (r q : ℕ) => dB_bounded r q
  set KD : ℝ := ∑ r ∈ Finset.Icc 1 m, ∑ q ∈ Finset.range (r + 1), (KB r q + 1) with hKDdef
  have hKDnn : 0 ≤ KD := by
    rw [hKDdef]
    exact Finset.sum_nonneg fun r _ =>
      Finset.sum_nonneg fun q _ => by linarith [(hKB r q).1]
  have hKDb : ∀ (r q : ℕ) (θ : ℝ), 1 ≤ r → r ≤ m → q ≤ r → |dB r q θ| ≤ KD := by
    intro r q θ hr1 hrm hqr
    have h1 : |dB r q θ| ≤ KB r q + 1 := by linarith [(hKB r q).2 θ]
    have h2 : KB r q + 1 ≤ ∑ q' ∈ Finset.range (r + 1), (KB r q' + 1) := by
      refine Finset.single_le_sum (f := fun q' => KB r q' + 1) (fun q' _ => ?_) ?_
      · linarith [(hKB r q').1]
      · simp only [Finset.mem_range]; omega
    have h3 : (∑ q' ∈ Finset.range (r + 1), (KB r q' + 1)) ≤ KD := by
      rw [hKDdef]
      refine Finset.single_le_sum
        (f := fun r' => ∑ q' ∈ Finset.range (r' + 1), (KB r' q' + 1))
        (fun r' _ => Finset.sum_nonneg fun q' _ => by linarith [(hKB r' q').1]) ?_
      simp only [Finset.mem_Icc]
      exact ⟨hr1, hrm⟩
    linarith
  set c : ℝ := 1 + KD * (m : ℝ) with hcdef
  have hc1 : 1 ≤ c := by rw [hcdef]; nlinarith [hKDnn]
  have hc0 : 0 ≤ c := by linarith
  refine ⟨c ^ (2 * m) * (m : ℝ), ?_, ?_⟩
  · have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have : 0 < c ^ (2 * m) := pow_pos (by linarith) _
    exact mul_pos this hmpos
  · intro v z θ _ hf
    set S : ℕ → ℝ := fun q => (Real.sin (2 * θ)) ^ q * Work.Spaces.pthIter q v z θ with hSdef
    set U : ℕ → ℝ := fun r => ∑ q ∈ Finset.Icc 1 r, |Work.Spaces.DthIter q v z θ| with hUdef
    have hU0 : ∀ r, 0 ≤ U r := by
      intro r; rw [hUdef]; exact Finset.sum_nonneg fun q _ => abs_nonneg _
    have hUmono : ∀ {a b : ℕ}, 1 ≤ a → a ≤ b → U a ≤ U b := by
      intro a b _ hab
      rw [hUdef]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro x hx
        simp only [Finset.mem_Icc] at hx ⊢
        exact ⟨hx.1, le_trans hx.2 hab⟩
      · intro x _ _
        exact abs_nonneg _
    have hSq : ∀ q, S q = (Real.sin (2 * θ)) ^ q * Work.Spaces.pthIter q v z θ := by
      intro q; rw [hSdef]
    -- the triangular identity `S r = D_θ^r f - Σ_{q<r} b_{r,q} S q`
    have hident : ∀ r, 1 ≤ r → S r = Work.Spaces.DthIter r v z θ
        - ∑ q ∈ Finset.range r, dB r q θ * S q := by
      intro r _
      have hexp := DthIter_expansion_local r v z θ hf
      have hself : dthCoef r r θ = (Real.sin (2 * θ)) ^ r :=
        congrFun (dthCoef_self r) θ
      have hsum : (∑ q ∈ Finset.range r,
            dthCoef r q θ * Work.Spaces.pthIter q v z θ)
          = ∑ q ∈ Finset.range r, dB r q θ * S q := by
        refine Finset.sum_congr rfl fun q _ => ?_
        have hcoef : dthCoef r q θ
            = (Real.sin (2 * θ)) ^ q * dB r q θ :=
          congrFun (dthCoef_eq_sin_pow_mul_dB r q) θ
        rw [hSq q, hcoef]
        ring
      rw [hSq r, hexp, Finset.sum_range_succ, hself, hsum]
      ring
    have hchain : ∀ r, 1 ≤ r → r ≤ m → |S r| ≤ c ^ r * U r := by
      intro r
      induction r using Nat.strong_induction_on with
      | h r ih =>
        intro hr1 hrm
        -- split off the `q = 0` term of the coefficient sum
        have hstep1 : |S r| ≤ |Work.Spaces.DthIter r v z θ|
            + ∑ q ∈ Finset.range (r - 1), |dB r (q + 1) θ| * |S (q + 1)| := by
          calc |S r|
              = |Work.Spaces.DthIter r v z θ
                  - ∑ q ∈ Finset.range r, dB r q θ * S q| := by rw [hident r hr1]
            _ ≤ |Work.Spaces.DthIter r v z θ|
                  + |∑ q ∈ Finset.range r, dB r q θ * S q| := abs_sub_le_abs_add _ _
            _ ≤ |Work.Spaces.DthIter r v z θ|
                  + ∑ q ∈ Finset.range r, |dB r q θ * S q| := by
                exact add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _)
            _ = |Work.Spaces.DthIter r v z θ|
                  + ∑ q ∈ Finset.range r, |dB r q θ| * |S q| := by
                simp [abs_mul]
            _ = |Work.Spaces.DthIter r v z θ|
                  + ∑ q ∈ Finset.range (r - 1), |dB r (q + 1) θ| * |S (q + 1)| := by
                have h0 : (fun q => |dB r q θ| * |S q|) 0 = 0 := by
                  simp [dB_apply_zero_of_one_le r hr1]
                rw [sum_range_eq_sum_range_pred h0 r]
        -- bound the sum by `KD · Σ |S (q+1)|`
        have hstep2 : ∑ q ∈ Finset.range (r - 1), |dB r (q + 1) θ| * |S (q + 1)|
            ≤ KD * ∑ q ∈ Finset.range (r - 1), |S (q + 1)| := by
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun q hq => ?_
          have hq1 : q + 1 ≤ r := by have := Finset.mem_range.mp hq; omega
          exact mul_le_mul_of_nonneg_right (hKDb r (q + 1) θ hr1 hrm hq1) (abs_nonneg _)
        -- apply the induction hypothesis
        have hstep3 : ∑ q ∈ Finset.range (r - 1), |S (q + 1)|
            ≤ ∑ q ∈ Finset.range (r - 1), c ^ (q + 1) * U (q + 1) := by
          refine Finset.sum_le_sum fun q hq => ?_
          have hq1 : q + 1 < r := by have := Finset.mem_range.mp hq; omega
          exact ih (q + 1) hq1 (by omega) (by omega)
        -- replace each `U (q+1)` by `U r` and sum the constants
        have hstep4 : ∑ q ∈ Finset.range (r - 1), c ^ (q + 1) * U (q + 1)
            ≤ ((m : ℝ) * c ^ (r - 1)) * U r := by
          have hUp : ∀ q ∈ Finset.range (r - 1), U (q + 1) ≤ U r := by
            intro q hq
            have hq1 : q + 1 ≤ r := by have := Finset.mem_range.mp hq; omega
            exact hUmono (by omega) hq1
          calc ∑ q ∈ Finset.range (r - 1), c ^ (q + 1) * U (q + 1)
              ≤ ∑ q ∈ Finset.range (r - 1), c ^ (q + 1) * U r := by
                refine Finset.sum_le_sum fun q hq => ?_
                exact mul_le_mul_of_nonneg_left (hUp q hq) (pow_nonneg hc0 _)
            _ = (∑ q ∈ Finset.range (r - 1), c ^ (q + 1)) * U r := by rw [Finset.sum_mul]
            _ ≤ ((m : ℝ) * c ^ (r - 1)) * U r := by
                refine mul_le_mul_of_nonneg_right ?_ (hU0 r)
                calc ∑ q ∈ Finset.range (r - 1), c ^ (q + 1)
                    ≤ ∑ q ∈ Finset.range (r - 1), c ^ (r - 1) := by
                      refine Finset.sum_le_sum fun q hq => ?_
                      have hq1 : q + 1 ≤ r - 1 := by
                        have := Finset.mem_range.mp hq; omega
                      exact pow_le_pow_right₀ hc1 hq1
                  _ = ((r - 1 : ℕ) : ℝ) * c ^ (r - 1) := by
                      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
                  _ ≤ (m : ℝ) * c ^ (r - 1) := by
                      refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hc0 _)
                      exact_mod_cast (by omega : r - 1 ≤ m)
        -- `|D_θ^r f|` is one of the terms of `U r`
        have hA : |Work.Spaces.DthIter r v z θ| ≤ U r := by
          rw [hUdef]
          refine Finset.single_le_sum (f := fun q => |Work.Spaces.DthIter q v z θ|)
            (fun q _ => abs_nonneg _) ?_
          simp only [Finset.mem_Icc]; omega
        -- the final arithmetic
        have hfin : U r + KD * (((m : ℝ) * c ^ (r - 1)) * U r) ≤ c ^ r * U r := by
          have hUr : 0 ≤ U r := hU0 r
          have hgle : 1 ≤ c ^ (r - 1) := one_le_pow₀ hc1
          have hcr : c ^ r = c ^ (r - 1) * c := by
            rw [← pow_succ]
            congr 1
            omega
          rw [hcr, hcdef]
          nlinarith [hUr, hgle, mul_nonneg hUr (pow_nonneg hc0 (r - 1))]
        calc |S r| ≤ |Work.Spaces.DthIter r v z θ|
                + ∑ q ∈ Finset.range (r - 1), |dB r (q + 1) θ| * |S (q + 1)| := hstep1
          _ ≤ |Work.Spaces.DthIter r v z θ| + KD * ∑ q ∈ Finset.range (r - 1), |S (q + 1)| :=
                add_le_add le_rfl hstep2
          _ ≤ |Work.Spaces.DthIter r v z θ|
                + KD * (((m : ℝ) * c ^ (r - 1)) * U r) := by
                refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ hKDnn)
                exact le_trans hstep3 hstep4
          _ ≤ U r + KD * (((m : ℝ) * c ^ (r - 1)) * U r) := add_le_add hA le_rfl
          _ ≤ c ^ r * U r := hfin
    have hmain : |S m| ≤ c ^ m * U m := hchain m hm le_rfl
    have hCS : U m ^ 2 ≤ (m : ℝ) * ∑ r ∈ Finset.Icc 1 m, (Work.Spaces.DthIter r v z θ) ^ 2 := by
      have h := sq_sum_le_card_mul_sum_sq (s := Finset.Icc 1 m)
        (f := fun q => |Work.Spaces.DthIter q v z θ|)
      have hcard : ((Finset.Icc 1 m).card : ℝ) = (m : ℝ) := by
        simp [Nat.card_Icc]
      rw [hcard] at h
      calc U m ^ 2 = (∑ q ∈ Finset.Icc 1 m, |Work.Spaces.DthIter q v z θ|) ^ 2 := by
            rw [hUdef]
        _ ≤ (m : ℝ) * ∑ q ∈ Finset.Icc 1 m, |Work.Spaces.DthIter q v z θ| ^ 2 := h
        _ = (m : ℝ) * ∑ q ∈ Finset.Icc 1 m, (Work.Spaces.DthIter q v z θ) ^ 2 := by
            congr 1
            exact Finset.sum_congr rfl fun q _ => sq_abs _
    change (S m) ^ 2 ≤ (c ^ (2 * m) * (m : ℝ))
      * ∑ r ∈ Finset.Icc 1 m, (Work.Spaces.DthIter r v z θ) ^ 2
    have hnm : 0 ≤ c ^ m * U m := mul_nonneg (pow_nonneg hc0 _) (hU0 m)
    have hsq : (S m) ^ 2 ≤ (c ^ m * U m) ^ 2 := by
      rw [← sq_abs (S m), ← sq_abs (c ^ m * U m)]
      exact pow_le_pow_left₀ (abs_nonneg _) (by rw [abs_of_nonneg hnm]; exact hmain) 2
    calc (S m) ^ 2 ≤ (c ^ m * U m) ^ 2 := hsq
      _ = (c ^ m) ^ 2 * U m ^ 2 := by ring
      _ = c ^ (2 * m) * U m ^ 2 := by rw [← pow_mul]; ring_nf
      _ ≤ c ^ (2 * m) * ((m : ℝ) * ∑ r ∈ Finset.Icc 1 m, (Work.Spaces.DthIter r v z θ) ^ 2) :=
            mul_le_mul_of_nonneg_left hCS (pow_nonneg hc0 _)
      _ = (c ^ (2 * m) * (m : ℝ))
            * ∑ r ∈ Finset.Icc 1 m, (Work.Spaces.DthIter r v z θ) ^ 2 := by ring


/-! ## The slot identity and the two integration-pushing lemmas -/


theorem slot_sq_eq_Wt_sq (m : ℕ) (α z θ : ℝ) (v : ℝ → ℝ → ℝ)
    (hs : 0 < Real.sin (2 * θ)) :
    (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pthIter m v z θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 * (m : ℝ) - Work.Spaces.gam α))
      = ((Real.sin (2 * θ)) ^ m * Work.Spaces.pthIter m v z θ) ^ 2
        * (Work.Spaces.Wt α z θ) ^ 2 := by
  -- Work with the `rpow` notation `^` so that `Real.rpow_add` / `Real.rpow_mul` match.
  change (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pthIter m v z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * (m : ℝ) - Work.Spaces.gam α))
      = ((Real.sin (2 * θ)) ^ m * Work.Spaces.pthIter m v z θ) ^ 2
        * (Work.Spaces.Wt α z θ) ^ 2
  -- `(S ^ m) ^ 2 = S ^ (2 * m)` for the natural power.
  have hpow : ((Real.sin (2 * θ)) ^ m) ^ 2
      = (Real.sin (2 * θ)) ^ (2 * (m : ℝ)) := by
    rw [← pow_mul, ← Real.rpow_natCast (Real.sin (2 * θ)) (m * 2)]
    congr 1
    push_cast
    ring
  -- `(S ^ (-γ/2)) ^ 2 = S ^ (-γ)` for the `rpow` residue.
  have hneg : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [← Real.rpow_natCast ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) 2]
    rw [← Real.rpow_mul hs.le (-(Work.Spaces.gam α / 2)) ((2 : ℕ) : ℝ)]
    congr 1
    push_cast
    ring
  -- The exponent addition `S ^ (2m - γ) = S ^ (2m) * S ^ (-γ)`.
  have hsub : (Real.sin (2 * θ)) ^ (2 * (m : ℝ) - Work.Spaces.gam α)
      = (Real.sin (2 * θ)) ^ (2 * (m : ℝ))
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [sub_eq_add_neg, Real.rpow_add hs]
  rw [Work.Spaces.Wt, Work.Spaces.wTheta]
  simp only [mul_pow]
  rw [hpow, hneg, hsub]
  ring

theorem theta_slice_mono {α : ℝ} {K m : ℕ} {v : ℝ → ℝ → ℝ} {z C : ℝ} (hC : 0 ≤ C)
    (hint : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α K v z θ) Work.Spaces.Iθ)
    (hae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pthIter m v z θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (2 * (m : ℝ) - Work.Spaces.gam α))
        ≤ C * Work.Spaces.HkIntegrand α K v z θ) :
    (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.pthIter m v z θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (2 * (m : ℝ) - Work.Spaces.gam α))
      ≤ C * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α K v z θ := by
  -- write both sides as integrals of the (constant multiple of the) integrand
  rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul]
  by_cases h : MeasureTheory.Integrable (fun θ => (Work.Spaces.w z) ^ 2 *
      ((Work.Spaces.pthIter m v z θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 * (m : ℝ) - Work.Spaces.gam α)))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)
  · -- integrable case: compare the integrals pointwise a.e.
    exact MeasureTheory.integral_mono_ae h (hint.const_mul C) hae
  · -- non-integrable case: the integral of the left-hand side is `0`
    rw [MeasureTheory.integral_undef h]
    exact MeasureTheory.integral_nonneg
      (fun θ => mul_nonneg hC (Work.Spaces.HkIntegrand_nonneg α K v z θ))

-- `hC : 0 ≤ C` belongs to the requested interface (the bound is stated for a nonnegative
-- constant); the argument below is a pure a.e.-monotonicity statement and does not consume
-- it, so the unused-variable linter is silenced here.
set_option linter.unusedVariables false in
/-- Integrate a slicewise bound in `z`: if for a.e. `z ∈ Iz` the slice
`θ ↦ w(z)^2 · (pthIter m v z θ)^2 · sin(2θ)^{2m-γ}` has `θ`-integral bounded by the
`θ`-integral of `C · HkIntegrand α K v z ·`, and the latter is `z`-integrable, then the
same bound holds after integrating in `z`.

The hypotheses are only needed to make the two `z`-integrals meaningful: the set integral
in the conclusion is a Bochner integral, and `integral_mono_of_nonneg` takes an a.e.-nonnegative
integrand bounded by an integrable one.  Nonnegativity comes from `w² ≥ 0`, the square, and
`sin(2θ) ≥ 0` for `θ ∈ Iθ`; the majorant is integrable by `hint`. -/
theorem z_integral_mono_const {α : ℝ} {K m : ℕ} {v : ℝ → ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hint : MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α K v z θ) Work.Spaces.Iz)
    (hae : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 *
          ((Work.Spaces.pthIter m v z θ) ^ 2 *
            Real.rpow (Real.sin (2 * θ)) (2 * (m : ℝ) - Work.Spaces.gam α)))
        ≤ ∫ θ in Work.Spaces.Iθ, C * Work.Spaces.HkIntegrand α K v z θ) :
    (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter m v z θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (2 * (m : ℝ) - Work.Spaces.gam α)))
      ≤ C * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α K v z θ) := by
  -- Pull the `z`-dependent constant `w z ^ 2` inside the `θ`-integral, so that the
  -- hypothesis `hae` becomes a bound on the `z`-integrands.
  have hae' : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter m v z θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (2 * (m : ℝ) - Work.Spaces.gam α))
      ≤ C * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α K v z θ) := by
    filter_upwards [hae] with z hz
    rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul]
    exact hz
  -- The `z`-integrand is nonnegative: `w z ^ 2 ≥ 0`, a square, and `sin (2θ) ≥ 0` on `Iθ`.
  have hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
      (fun z => (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter m v z θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (2 * (m : ℝ) - Work.Spaces.gam α))) := by
    refine Filter.Eventually.of_forall (fun z => mul_nonneg (sq_nonneg _) ?_)
    refine MeasureTheory.setIntegral_nonneg ?_ ?_
    · rw [Work.Spaces.Iθ]; exact measurableSet_Icc
    · intro θ hθ
      refine mul_nonneg (sq_nonneg _) (Real.rpow_nonneg ?_ _)
      rw [Work.Spaces.Iθ] at hθ
      exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  -- The majorant `z ↦ C * ∫ θ, HkIntegrand α K v z θ` is integrable.
  have hint' : MeasureTheory.Integrable
      (fun z => C * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α K v z θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hint.const_mul C
  -- Monotonicity of the Bochner integral, then pull the constant `C` out.
  calc (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter m v z θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (2 * (m : ℝ) - Work.Spaces.gam α)))
      ≤ ∫ z in Work.Spaces.Iz, C * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α K v z θ) :=
        MeasureTheory.integral_mono_of_nonneg hnn hint' hae'
    _ = C * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α K v z θ) :=
        MeasureTheory.integral_const_mul C _


/-! ## The a.e. reduction to the open interval, and the pointwise slot bound -/


/-- Almost every point of `Iθ = [0,π/2]` lies in the open interval `(0,π/2)`. -/
theorem ae_mem_Ioo_of_Iθ :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo 0 (Real.pi / 2) := by
  have h : (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) : Measure ℝ)
      = MeasureTheory.volume.restrict Work.Spaces.Iθ :=
    MeasureTheory.Measure.restrict_congr_set
      (by rw [Work.Spaces.Iθ]; exact MeasureTheory.Ioo_ae_eq_Icc)
  rw [← h]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-- **The pointwise slot bound.**  On the open quadrant the `m`-th plain angular slot with
weight `sin(2θ)^{2m-γ}` is dominated by the `H^K`-integrand; the bound is a.e. in `θ` because
the chain of `remov.dthChain_core` is only needed off the two endpoints of `Iθ`, where the
factor `sin(2θ)^m` vanishes.  The constant depends on `m` only (in particular not on `α`,
`K`, `v`). -/
theorem slot_pointwise_HkIntegrand (m : ℕ) (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (v : ℝ → ℝ → ℝ) (K : ℕ), m ≤ K → 0 < α →
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry v)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) →
      ∀ z ∈ Work.Spaces.Iz, ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pthIter m v z θ) ^ 2 *
            Real.rpow (Real.sin (2 * θ)) (2 * (m : ℝ) - Work.Spaces.gam α))
          ≤ C * Work.Spaces.HkIntegrand α K v z θ := by
  obtain ⟨C0, hC0pos, hC0⟩ := dthChain_core m hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hm1R : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  refine ⟨C0 * m, mul_pos hC0pos hmpos, ?_⟩
  intro α v K hmK hα hsm z hz
  have hz0 : (0 : ℝ) ≤ z := hz
  rcases eq_or_lt_of_le hz0 with hzeq | hzpos
  · -- `z = 0`: both sides vanish / are nonnegative.
    have hw0 : (Work.Spaces.w z) ^ 2 = 0 := by rw [hzeq.symm]; norm_num [Work.Spaces.w]
    refine Eventually.of_forall (fun θ => ?_)
    rw [hw0, zero_mul]
    exact mul_nonneg (mul_pos hC0pos hmpos).le
      (Work.Spaces.HkIntegrand_nonneg α K v z θ)
  · -- `z > 0`: the genuine pointwise chain.
    refine ae_mem_Ioo_of_Iθ.mono (fun θ hθ => ?_)
    have hs : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos])
    have hcd : ∀ k : ℕ, ContDiffAt ℝ k (Function.uncurry v) (z, θ) := fun k =>
      (hsm k).contDiffAt ((isOpen_Ioi.prod isOpen_Ioo).mem_nhds ⟨hzpos, hθ⟩)
    rw [slot_sq_eq_Wt_sq m α z θ v hs]
    have hsum : (∑ r ∈ Finset.Icc 1 m,
          (Work.Spaces.DthIter r v z θ) ^ 2 * (Work.Spaces.Wt α z θ) ^ 2)
        ≤ (m : ℝ) * Work.Spaces.HkIntegrand α K v z θ := by
      have hbd : ∀ r ∈ Finset.Icc 1 m,
          (Work.Spaces.DthIter r v z θ) ^ 2 * (Work.Spaces.Wt α z θ) ^ 2
            ≤ Work.Spaces.HkIntegrand α K v z θ := by
        intro r hr
        obtain ⟨hr1, hrm⟩ := Finset.mem_Icc.mp hr
        simpa only [Work.Spaces.mixed_zero_left, mul_pow] using
          (Work.Spaces.sq_le_HkIntegrand_mixed α K v z θ r 0 hr1 (by omega))
      calc (∑ r ∈ Finset.Icc 1 m,
            (Work.Spaces.DthIter r v z θ) ^ 2 * (Work.Spaces.Wt α z θ) ^ 2)
          ≤ ∑ _r ∈ Finset.Icc 1 m, Work.Spaces.HkIntegrand α K v z θ :=
            Finset.sum_le_sum hbd
        _ = (m : ℝ) * Work.Spaces.HkIntegrand α K v z θ := by
            rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    calc ((Real.sin (2 * θ)) ^ m * Work.Spaces.pthIter m v z θ) ^ 2
            * (Work.Spaces.Wt α z θ) ^ 2
        ≤ (C0 * ∑ r ∈ Finset.Icc 1 m, (Work.Spaces.DthIter r v z θ) ^ 2)
            * (Work.Spaces.Wt α z θ) ^ 2 :=
          mul_le_mul_of_nonneg_right (hC0 v z θ hθ hcd) (sq_nonneg _)
      _ = C0 * ((∑ r ∈ Finset.Icc 1 m, (Work.Spaces.DthIter r v z θ) ^ 2)
            * (Work.Spaces.Wt α z θ) ^ 2) := by ring
      _ = C0 * ∑ r ∈ Finset.Icc 1 m,
            (Work.Spaces.DthIter r v z θ) ^ 2 * (Work.Spaces.Wt α z θ) ^ 2 := by
          rw [Finset.sum_mul]
      _ ≤ C0 * ((m : ℝ) * Work.Spaces.HkIntegrand α K v z θ) :=
          mul_le_mul_of_nonneg_left hsum hC0pos.le
      _ = (C0 * m) * Work.Spaces.HkIntegrand α K v z θ := by ring


end

end selfdth

open Work.FTS.EllipticEst.remov.selfdth


/-- **SELF-CONTAINED copy of `Work.FTS.EllipticEst.remov.high_chain_sum`.**

This is the SAME statement as `Work.FTS.EllipticEst.remov.high_chain_sum`
(`Submission/Work/FTS/EllipticEst/remov/high_chain_sum.lean`), which is already PROVED there by
the colleagues of `remov.dthChain_core` / `remov.slot_sq_eq_Wt_sq` / `remov.theta_slice_mono` /
`remov.z_integral_mono_const`.  The purpose of this request is DIFFERENT: the import cone of
that file is currently BROKEN by an unrelated, in-flight file of another area,
`Submission/Work/EllipticEst/EllHyp_hkMem_V_fts.lean` (it refers to
`Work.FTS.EllipticEst.Cert.continuousOn_rDzIter_of_contDiffOn`, which no longer exists), and
that file is reachable from
`remov.DthIter_expansion` → `DthIter_expansion_identity` → `alphaDzDthW_Hk_le`
→ `EllHyp_hkMem_V_fts`.  So the module you create must NOT import anything in that cone:
in particular do NOT import `Submission.Work.FTS.EllipticEst.remov.DthIter_expansion`,
`...DthIter_expansion_identity`, `...alphaDzDthW_Hk_le`, `...EllEstUnifStepAux`,
`...remov.PsiSlotBounds`, `...remov.dthChain_core`, `...remov.high_chain_sum`,
`...remov.theta_slice_mono`, `...remov.dthCoeff_bounds`, `...remov.Baux.*`, `...DzAmgm.*`,
`...RPFresh.*`, `...Coercivity.*`.  Import only `Mathlib`,
`Submission.Work.Spaces.Defs`, `Submission.Work.Spaces.HkSq_terms`, and (if you need them)
other `Submission.Work.Spaces.*` primitives that do not reach the files above; check with
`lake build Submission.Work.FTS.EllipticEst.remov.high_chain_sum_self` that the whole cone
builds.

RECIPE (all the mathematics is already written down; this is a careful COPY + rename job).
Create `Submission/Work/FTS/EllipticEst/remov/high_chain_sum_self.lean` containing, ABOVE the
target, verbatim copies of the declarations below, all placed in the fresh namespace
`Work.FTS.EllipticEst.remov.selfdth` (so that no name clashes with the originals are possible),
with every fully-qualified reference to the copied names rewritten to refer to the copies
(e.g. `Work.FTS.EllipticEst.dthCoef` → the `dthCoef` declared in the new namespace).  Keep all
`Work.Spaces.*` references unchanged.

* from `Submission/Work/FTS/EllipticEst/alphaDzDthW_Hk_le.lean` (≈ lines 218–275):
  `dthCoef`, `dthCoef_zero_of_gt`, `dthCoef_self`, `contDiff_dthCoef`;
* from `Submission/Work/FTS/EllipticEst/DthIter_expansion_identity.lean` (≈ lines 20–75):
  `dthCoef_succ_mul_sum`;
* from `Submission/Work/FTS/EllipticEst/remov/DthIter_expansion.lean` (≈ lines 30–420):
  `contDiffAt_slice_snd_of_uncurry`, `contDiffAt_deriv_of_succ`,
  `contDiffAt_iteratedDeriv_of_add`, `contDiffAt_iteratedDeriv_of_le`,
  `differentiableAt_iteratedDeriv_of_le`, `pthIter_eq_iteratedDeriv_slice`,
  `deriv_pthIter_slice`, `DthIter_expansion_of_contDiffOn`, `DthIter_expansion_local`,
  `dB` (with `dB_zero_zero`, `dB_zero_succ`, `dB_succ`), `dB_contDiff`,
  `deriv_sin_two_pow_mul`, `dthCoef_eq_sin_pow_mul_dB`, `deriv_periodic_pi`, `dB_periodic`,
  `dB_bounded`, `DthCoef_sin_pow_bound`;
* from `Submission/Work/FTS/EllipticEst/dthCoef_bound_fixed.lean`: `dthCoef_succ_zero`
  (and, if you want, `dthCoef_succ_le_sin` and the one-line `sin(2θ) ≥ 0` on `Iθ`);
* from `Submission/Work/FTS/EllipticEst/remov/dthChain_core.lean`: `dB_apply_zero_of_one_le`,
  `sum_range_eq_sum_range_pred`, `sq_sub_le_two`, `abs_sub_le_abs_add`, `dthChain_core`;
* from `Submission/Work/FTS/EllipticEst/remov/slot_sq_eq_Wt_sq.lean`,
  `.../theta_slice_mono.lean`, `.../z_integral_mono_const.lean`: `slot_sq_eq_Wt_sq`,
  `theta_slice_mono`, `z_integral_mono_const`;
* finally the proof of `high_chain_sum` itself from
  `Submission/Work/FTS/EllipticEst/remov/high_chain_sum.lean` (including its local helper
  `ae_mem_Ioo_of_Iθ`), with `dthChain_core` etc. referring to the copies.

The TRAP (documented in the original file) must be preserved: the chain uses the EXACT
expansion `DthIter_expansion_local` together with the vanishing `dthCoef m 0 = 0` (`m ≥ 1`),
NOT the weaker two-sided `DthIter_expansion` inequality, whose `r = 0` term would produce the
`∫ v²w²sin^{-γ}` summand that is not controlled by `HkSq`.

The target statement (name `Work.FTS.EllipticEst.remov.high_chain_sum_self`, in namespace
`Work.FTS.EllipticEst.remov`): -/
theorem high_chain_sum_self (K : ℕ) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (v : ℝ → ℝ → ℝ), 0 < α →
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry v)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) →
      Work.Spaces.HkMem α K v →
      (∑ m ∈ Finset.Icc 1 K,
        ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
          (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.pthIter m v z θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (2 * (m : ℝ) - Work.Spaces.gam α)))
      ≤ C * Work.Spaces.HkSq α K v := by

  classical
  have hcc : ∀ m : ℕ, ∃ C : ℝ, 0 < C ∧ (1 ≤ m →
      ∀ (α : ℝ) (v : ℝ → ℝ → ℝ) (K : ℕ), m ≤ K → 0 < α →
        (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry v)
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) →
        ∀ z ∈ Work.Spaces.Iz, ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
          (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pthIter m v z θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (2 * (m : ℝ) - Work.Spaces.gam α))
            ≤ C * Work.Spaces.HkIntegrand α K v z θ) := by
    intro m
    by_cases hm : 1 ≤ m
    · obtain ⟨C, hC0, hC⟩ := slot_pointwise_HkIntegrand m hm
      exact ⟨C, hC0, fun _ => hC⟩
    · exact ⟨1, one_pos, fun h => absurd h hm⟩
  choose Cp hCppos hCp using hcc
  have hsum_nn : 0 ≤ ∑ m ∈ Finset.Icc 1 K, Cp m * (m : ℝ) :=
    Finset.sum_nonneg fun m hm => (mul_pos (hCppos m) (by
      have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hm).1
      linarith)).le
  refine ⟨1 + ∑ m ∈ Finset.Icc 1 K, Cp m * (m : ℝ), by linarith, ?_⟩
  intro α v hα hsm hmem
  have hterm : ∀ m ∈ Finset.Icc 1 K,
      (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter m v z θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (2 * (m : ℝ) - Work.Spaces.gam α)))
        ≤ (Cp m * (m : ℝ)) * Work.Spaces.HkSq α K v := by
    intro m hm
    obtain ⟨hm1, hmK⟩ := Finset.mem_Icc.mp hm
    have hm1R : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    have hCm : (0 : ℝ) ≤ Cp m * (m : ℝ) := (mul_pos (hCppos m) (by linarith)).le
    have hpw := hCp m hm1 α v K hmK hα hsm
    have hpw' : ∀ z ∈ Work.Spaces.Iz, ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pthIter m v z θ) ^ 2 *
            Real.rpow (Real.sin (2 * θ)) (2 * (m : ℝ) - Work.Spaces.gam α))
          ≤ (Cp m * (m : ℝ)) * Work.Spaces.HkIntegrand α K v z θ := by
      intro z hz
      refine (hpw z hz).mono (fun θ hθ => ?_)
      refine hθ.trans ?_
      have hHk : (0 : ℝ) ≤ Work.Spaces.HkIntegrand α K v z θ :=
        Work.Spaces.HkIntegrand_nonneg α K v z θ
      calc Cp m * Work.Spaces.HkIntegrand α K v z θ
          = (Cp m * 1) * Work.Spaces.HkIntegrand α K v z θ := by ring
        _ ≤ (Cp m * (m : ℝ)) * Work.Spaces.HkIntegrand α K v z θ :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hm1R (hCppos m).le) hHk
    have htheta : ∀ z ∈ Work.Spaces.Iz,
        (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.pthIter m v z θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (2 * (m : ℝ) - Work.Spaces.gam α))
          ≤ (Cp m * (m : ℝ)) * ∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α K v z θ :=
      fun z hz => theta_slice_mono (α := α) (K := K) (m := m) (v := v) (z := z)
        (C := Cp m * (m : ℝ)) hCm (hmem.1 z hz) (hpw' z hz)
    have hae : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 *
            ((Work.Spaces.pthIter m v z θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (2 * (m : ℝ) - Work.Spaces.gam α)))
          ≤ ∫ θ in Work.Spaces.Iθ,
              (Cp m * (m : ℝ)) * Work.Spaces.HkIntegrand α K v z θ := by
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => ?_)
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
      exact htheta z hz
    have hz2 := z_integral_mono_const (α := α) (K := K) (m := m) (v := v)
      (C := Cp m * (m : ℝ)) hCm hmem.2 hae
    rw [Work.Spaces.HkSq]
    exact hz2
  calc (∑ m ∈ Finset.Icc 1 K, ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter m v z θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (2 * (m : ℝ) - Work.Spaces.gam α)))
      ≤ ∑ m ∈ Finset.Icc 1 K, (Cp m * (m : ℝ)) * Work.Spaces.HkSq α K v :=
        Finset.sum_le_sum hterm
    _ = (∑ m ∈ Finset.Icc 1 K, Cp m * (m : ℝ)) * Work.Spaces.HkSq α K v := by
        rw [← Finset.sum_mul]
    _ ≤ (1 + ∑ m ∈ Finset.Icc 1 K, Cp m * (m : ℝ)) * Work.Spaces.HkSq α K v :=
        mul_le_mul_of_nonneg_right (by linarith) (Work.Spaces.HkSq_nonneg α K v)

end Work.FTS.EllipticEst.remov
