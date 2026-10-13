import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.Galerkin.Defs
import Submission.Work.FTS.EllExist.Honesty.hkMem_of_liminf_slice
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.FTS.StrongLWP.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `H^k`-membership and the `H^k`-norm of a pointwise limit

This file proves `Work.FTS.StrongEps.HkMem_of_tendsto`: the `ℋ^k`-membership and the uniform
`ℋ^k`-bound of a limit `f` of a sequence `G n` of profiles of class `ℋ^m` (`m ≥ k`), from

* the pointwise convergence of *every* mixed slot `D_z^jD_θ^i` with `i + j ≤ k` on the open
  quadrant,
* a uniform `ℋ^m`-bound `HkNorm α m (G n) ≤ B`,
* a `z`-dependent uniform bound on the angular `ℋ^k`-integrals of the approximants.

The proof applies Fatou's lemma twice (the engine
`Work.FTS.EllExist.Honesty.hkMem_of_liminf_slice`): the pointwise convergence of the slots makes
the `ℋ^k`-integrand of `f` the (pointwise) liminf of those of the approximants, and the uniform
bounds give the two uniform domination hypotheses.  The engine also needs the *measurability* of
the slice and of the angular integral of the limit integrand; both are supplied here from the
hypothesis that `f` is `C^k` on the open quadrant, via the finite-order form of the
`D_z`/`D_θ`-calculus (`continuousOn_HkIntegrand_fin`) and the two measurability lemmas
`Work.Spaces.aesm_slice_of_continuousOn_Qd` / `Work.Spaces.aesm_of_continuousOn_Qd`.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Real Topology

namespace Work.FTS.StrongEps

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## The finite-order `D`-calculus on an open set

`Work.FTS.LocData.SmoothChain` proves that `pz`, `pth`, `Dz`, `Dth` and their iterates preserve
`C^∞` on an open set.  Here the same calculus is needed at the *finite* order `k` in which the
hypotheses of the statement are phrased, so the lemmas are repeated with a natural-number order.
-/

/-- `∂_z` lowers the differentiability order by one on an open set. -/
theorem contDiffOn_uncurry_pz_fin {G : ℝ → ℝ → ℝ} {n : ℕ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pz G)) V := by
  have hchain : ∀ p ∈ V, Work.Spaces.pz G p.1 p.2
      = fderiv ℝ (Function.uncurry G) p (1, 0) := fun p hp =>
    Work.Spaces.pz_eq_fderiv
      ((h.differentiableOn (by norm_num : ((n + 1 : ℕ) : WithTop ℕ∞) ≠ 0)).differentiableAt
        (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V :=
    h.fderiv_of_isOpen hV (m := n) (by norm_num)
  have hcomp : ContDiffOn ℝ n (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (1, 0)) V :=
    hfd.clm_apply contDiffOn_const
  refine hcomp.congr (fun p hp => ?_)
  exact hchain p hp

/-- `∂_θ` lowers the differentiability order by one on an open set. -/
theorem contDiffOn_uncurry_pth_fin {G : ℝ → ℝ → ℝ} {n : ℕ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pth G)) V := by
  have hchain : ∀ p ∈ V, Work.Spaces.pth G p.1 p.2
      = fderiv ℝ (Function.uncurry G) p (0, 1) := fun p hp =>
    Work.Spaces.pth_eq_fderiv
      ((h.differentiableOn (by norm_num : ((n + 1 : ℕ) : WithTop ℕ∞) ≠ 0)).differentiableAt
        (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V :=
    h.fderiv_of_isOpen hV (m := n) (by norm_num)
  have hcomp : ContDiffOn ℝ n (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (0, 1)) V :=
    hfd.clm_apply contDiffOn_const
  refine hcomp.congr (fun p hp => ?_)
  exact hchain p hp

/-- `D_z` lowers the differentiability order by one on an open set. -/
theorem contDiffOn_uncurry_Dz_fin {G : ℝ → ℝ → ℝ} {n : ℕ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.Dz G)) V := by
  have hpz := contDiffOn_uncurry_pz_fin hV h
  have hfun : ContDiffOn ℝ n (fun p : ℝ × ℝ => p.1 * Function.uncurry (Work.Spaces.pz G) p) V :=
    contDiff_fst.contDiffOn.mul hpz
  refine hfun.congr (fun p hp => ?_)
  rfl

/-- `D_θ` lowers the differentiability order by one on an open set. -/
theorem contDiffOn_uncurry_Dth_fin {G : ℝ → ℝ → ℝ} {n : ℕ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.Dth G)) V := by
  have hpth := contDiffOn_uncurry_pth_fin hV h
  have hsin : ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.sin (2 * p.2)) V :=
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
  have hfun : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => Real.sin (2 * p.2) * Function.uncurry (Work.Spaces.pth G) p) V :=
    hsin.mul hpth
  refine hfun.congr (fun p hp => ?_)
  rfl

/-- `D_z^i` lowers the differentiability order by `i` on an open set. -/
theorem contDiffOn_uncurry_DzIter_shift {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (i n : ℕ) (h : ContDiffOn ℝ (n + i) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.DzIter i G)) V := by
  induction i generalizing n with
  | zero => simpa using h
  | succ i ih =>
      rw [Work.Spaces.DzIter_succ]
      refine contDiffOn_uncurry_Dz_fin hV (ih (n + 1) ?_)
      exact h.of_le (Nat.cast_le.mpr (by omega : n + 1 + i ≤ n + (i + 1)))

/-- `D_θ^i` lowers the differentiability order by `i` on an open set. -/
theorem contDiffOn_uncurry_DthIter_shift {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (i n : ℕ) (h : ContDiffOn ℝ (n + i) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.DthIter i G)) V := by
  induction i generalizing n with
  | zero => simpa using h
  | succ i ih =>
      rw [Work.Spaces.DthIter_succ]
      refine contDiffOn_uncurry_Dth_fin hV (ih (n + 1) ?_)
      exact h.of_le (Nat.cast_le.mpr (by omega : n + 1 + i ≤ n + (i + 1)))

/-- **The slots of `HkIntegrand α k F` are continuous on the open quadrant** as soon as `F` is
`C^k` there: `D_z^i F` for `i ≤ k` and `D_z^jD_θ^iF` for `i + j ≤ k`. -/
theorem continuousOn_DzIter_of_contDiffOn {G : ℝ → ℝ → ℝ} {k i : ℕ}
    (h : ContDiffOn ℝ k (Function.uncurry G) Work.FTS.EllipticEst.Q0) (hi : i ≤ k) :
    ContinuousOn (Function.uncurry (Work.Spaces.DzIter i G)) Work.FTS.EllipticEst.Q0 := by
  have h' : ContDiffOn ℝ ((k - i) + i : ℕ) (Function.uncurry G) Work.FTS.EllipticEst.Q0 := by
    rwa [Nat.sub_add_cancel hi]
  exact (contDiffOn_uncurry_DzIter_shift Work.FTS.EllipticEst.isOpen_Q0 i (k - i) h').continuousOn

/-- The mixed slots `D_z^jD_θ^iF` (`i + j ≤ k`) are continuous on the open quadrant as soon as
`F` is `C^k` there. -/
theorem continuousOn_mixed_of_contDiffOn {G : ℝ → ℝ → ℝ} {k j i : ℕ}
    (h : ContDiffOn ℝ k (Function.uncurry G) Work.FTS.EllipticEst.Q0) (hji : i + j ≤ k) :
    ContinuousOn (Function.uncurry (Work.Spaces.mixed j i G)) Work.FTS.EllipticEst.Q0 := by
  have hi : i ≤ k := by omega
  have hj : j ≤ k - i := by omega
  have h1 : ContDiffOn ℝ (k - i) (Function.uncurry (Work.Spaces.DthIter i G))
      Work.FTS.EllipticEst.Q0 := by
    have h' : ContDiffOn ℝ ((k - i) + i : ℕ) (Function.uncurry G) Work.FTS.EllipticEst.Q0 := by
      rwa [Nat.sub_add_cancel hi]
    exact contDiffOn_uncurry_DthIter_shift Work.FTS.EllipticEst.isOpen_Q0 i (k - i) h'
  have h1' : ContDiffOn ℝ ((k - i - j) + j : ℕ) (Function.uncurry (Work.Spaces.DthIter i G))
      Work.FTS.EllipticEst.Q0 := by
    rwa [Nat.sub_add_cancel hj]
  exact (contDiffOn_uncurry_DzIter_shift Work.FTS.EllipticEst.isOpen_Q0 j (k - i - j)
    h1').continuousOn

/-! ## Continuity of the weights and of the `ℋ^k`-integrand on the open quadrant -/

/-- The angular weight `W = w·sin(2θ)^{-γ/2}` is continuous on the open quadrant. -/
theorem continuousOn_Wt_Q0_fin (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) Work.FTS.EllipticEst.Q0 := by
  have hsinpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      = fun p : ℝ × ℝ =>
          Work.Spaces.w p.1 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
    funext p; rfl
  rw [hfun]
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Work.FTS.EllipticEst.Q0 := by
    have hfun2 : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
      funext p; rfl
    rw [hfun2]
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => ?_)
    exact pow_ne_zero 2 (ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
  exact hw.mul
    (((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (hsinpos p hp))))

/-- **The `ℋ^k`-integrand of a `C^k` datum is continuous on the open quadrant.**  Every slot
occurring in `HkIntegrand α k F` has order at most `k`, so `C^k`-regularity of `F` on the open
quadrant suffices. -/
theorem continuousOn_HkIntegrand_fin (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : ContDiffOn ℝ k (Function.uncurry F) Work.FTS.EllipticEst.Q0) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k F p.1 p.2)
      Work.FTS.EllipticEst.Q0 := by
  have hz : ∀ i : ℕ, i ≤ k → ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.DzIter i F p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    fun i hi => continuousOn_DzIter_of_contDiffOn hF hi
  have hm : ∀ j i : ℕ, i + j ≤ k → ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.mixed j i F p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    fun j i hji => continuousOn_mixed_of_contDiffOn hF hji
  have hHk : (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k F p.1 p.2)
      = fun p : ℝ × ℝ =>
          (∑ i ∈ Finset.range (k + 1),
              (Work.Spaces.DzIter i F p.1 p.2
                * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
            + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
                if 1 ≤ i ∧ i + j ≤ k
                then (Work.Spaces.mixed j i F p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2
                else 0 := by
    funext p; rfl
  rw [hHk]
  refine ContinuousOn.add ?_ ?_
  · refine continuousOn_finsetSum (Finset.range (k + 1)) (fun i hi => ?_)
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    exact (((hz i hik).mul Work.FTS.EllipticEst.continuousOn_wdivsin_Q0)).pow 2
  · refine continuousOn_finsetSum (Finset.range (k + 1)) (fun i _ =>
      continuousOn_finsetSum (Finset.range (k + 1)) (fun j _ => ?_))
    split_ifs with h
    · exact (((hm j i h.2).mul (continuousOn_Wt_Q0_fin α))).pow 2
    · exact continuousOn_const

/-! ## Measurability and integrability of the `ℋ^k`-integrand of a `C^k` datum -/

/-- At `z = 0` the radial weight `w` vanishes and with it every summand of the `ℋ^k`-integrand. -/
theorem HkIntegrand_eq_zero_at_z_zero (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α k F 0 θ = 0 := by
  simp only [Work.Spaces.HkIntegrand, Work.Spaces.Wt, Work.Spaces.wTheta, Work.Spaces.w]
  simp

/-- The angular slices of the `ℋ^k`-integrand of a `C^k` datum are a.e. strongly measurable. -/
theorem aesm_slice_HkIntegrand_of_contDiffOn (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : ContDiffOn ℝ k (Function.uncurry F) Work.FTS.EllipticEst.Q0) :
    ∀ z ∈ Work.Spaces.Iz, AEStronglyMeasurable
      (fun θ => Work.Spaces.HkIntegrand α k F z θ) (volume.restrict Work.Spaces.Iθ) := by
  intro z hz
  rcases lt_or_eq_of_le (show (0 : ℝ) ≤ z from hz) with hzpos | hz0
  · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _ (continuousOn_HkIntegrand_fin α k F hF)
      hzpos
  · subst hz0
    rw [show (fun θ => Work.Spaces.HkIntegrand α k F 0 θ) = fun _ : ℝ => (0 : ℝ) from
      funext fun θ => HkIntegrand_eq_zero_at_z_zero α k F θ]
    exact aestronglyMeasurable_const

/-- The angular integral of the `ℋ^k`-integrand of a `C^k` datum is a.e. strongly measurable
on the half-line. -/
theorem aesm_integral_HkIntegrand_of_contDiffOn (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : ContDiffOn ℝ k (Function.uncurry F) Work.FTS.EllipticEst.Q0) :
    AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ)
      (volume.restrict Work.Spaces.Iz) :=
  (Work.Spaces.aesm_of_continuousOn_Qd
    (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k F p.1 p.2)
    (continuousOn_HkIntegrand_fin α k F hF)).integral_prod_right'

/-- **`ℋ^k`-membership descends in the order**, for a datum only known to be `C^k` on the open
quadrant: the extra order-`k` regularity is used only to make the smaller integrand measurable,
which is exactly what `Integrable.mono'` needs. -/
theorem HkMem_mono_of_contDiffOn {α : ℝ} {k m : ℕ} (hkm : k ≤ m) {F : ℝ → ℝ → ℝ}
    (hF : ContDiffOn ℝ k (Function.uncurry F) Work.FTS.EllipticEst.Q0)
    (hm : Work.Spaces.HkMem α m F) : Work.Spaces.HkMem α k F := by
  constructor
  · intro z hz
    refine Integrable.mono' (hm.1 z hz) (aesm_slice_HkIntegrand_of_contDiffOn α k F hF z hz) ?_
    filter_upwards with θ
    rw [Real.norm_of_nonneg (Work.Spaces.HkIntegrand_nonneg α k F z θ)]
    exact Work.FTS.StrongLWP.HkIntegrand_mono α F hkm z θ
  · refine Integrable.mono' hm.2 (aesm_integral_HkIntegrand_of_contDiffOn α k F hF) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
    rw [Real.norm_of_nonneg (integral_nonneg fun θ =>
      Work.Spaces.HkIntegrand_nonneg α k F z θ)]
    exact integral_mono_of_nonneg (Eventually.of_forall fun θ =>
      Work.Spaces.HkIntegrand_nonneg α k F z θ) (hm.1 z hz)
      (Eventually.of_forall fun θ => Work.FTS.StrongLWP.HkIntegrand_mono α F hkm z θ)

/-! ## Pointwise convergence of the `ℋ^k`-integrand from that of the slots -/

/-- **Slot-wise convergence gives convergence of the `ℋ^k`-integrand.**  The integrand is an
explicit finite sum of squares of the slots `D_z^i` (`i ≤ k`) and `D_z^jD_θ^i` (`1 ≤ i`,
`i + j ≤ k`), so convergence of all of them gives convergence of the sum. -/
theorem HkIntegrand_tendsto_of_mixed {α : ℝ} {k : ℕ} {F : ℝ → ℝ → ℝ}
    {Fs : ℕ → ℝ → ℝ → ℝ} {z θ : ℝ}
    (hconv : ∀ j i : ℕ, j + i ≤ k → Filter.Tendsto
      (fun n => Work.Spaces.mixed j i (Fs n) z θ) Filter.atTop
      (nhds (Work.Spaces.mixed j i F z θ))) :
    Filter.Tendsto (fun n => Work.Spaces.HkIntegrand α k (Fs n) z θ) Filter.atTop
      (nhds (Work.Spaces.HkIntegrand α k F z θ)) := by
  have hDz : ∀ i : ℕ, i ≤ k → Filter.Tendsto (fun n => Work.Spaces.DzIter i (Fs n) z θ)
      Filter.atTop (nhds (Work.Spaces.DzIter i F z θ)) :=
    fun i hi => by
      simpa only [Work.Spaces.mixed_zero_right] using hconv i 0 (by omega)
  simp only [Work.Spaces.HkIntegrand]
  refine Filter.Tendsto.add ?_ ?_
  · refine tendsto_finset_sum _ fun i hi => ?_
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    exact ((hDz i hik).mul_const _).pow 2
  · refine tendsto_finset_sum _ fun i _ => ?_
    refine tendsto_finset_sum _ fun j _ => ?_
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · have hfun1 : (fun n => (if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i (Fs n) z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
          = fun n => (Work.Spaces.mixed j i (Fs n) z θ * Work.Spaces.Wt α z θ) ^ 2 :=
        funext fun n => if_pos hc
      have hfun2 : (if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
          = (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2 := if_pos hc
      rw [hfun1, hfun2]
      exact ((hconv j i (by omega)).mul_const (Work.Spaces.Wt α z θ)).pow 2
    · have hfun1 : (fun n => (if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i (Fs n) z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
          = fun _ => (0 : ℝ) := funext fun n => if_neg hc
      have hfun2 : (if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) = (0 : ℝ) :=
        if_neg hc
      rw [hfun1, hfun2]
      exact tendsto_const_nhds

/-! ## The target -/

theorem HkMem_of_tendsto {α B : ℝ} {k m : ℕ} (hkm : k ≤ m) {G : ℕ → Work.FTS.Galerkin.Fn}
    {f : Work.FTS.Galerkin.Fn}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ (k : ℕ) (Function.uncurry (G n))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hreg : ContDiffOn ℝ (k : ℕ) (Function.uncurry f)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hconv : ∀ j i : ℕ, j + i ≤ k → ∀ z θ, (z, θ) ∈ (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i (G n) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed j i f z θ)))
    (hmem : ∀ n : ℕ, Work.Spaces.HkMem α m (G n))
    (hb : ∀ n : ℕ, Work.Spaces.HkNorm α m (G n) ≤ B)
    (hz : ∀ z ∈ Work.Spaces.Iz, ∃ Bz : ℝ, ∀ n : ℕ,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (G n) z θ) ≤ Bz) :
    Work.Spaces.HkMem α k f ∧ Work.Spaces.HkNorm α k f ≤ B := by
  -- the level-`k` membership of the approximants, from their level-`m` membership
  have hmemG : ∀ n : ℕ, Work.Spaces.HkMem α k (G n) :=
    fun n => HkMem_mono_of_contDiffOn hkm (hsm n) (hmem n)
  -- the level-`k` bounds of the approximants: `HkSq α k ≤ HkSq α m = HkNorm α m ^ 2 ≤ B ^ 2`
  have hbSq : ∀ n : ℕ, Work.Spaces.HkSq α k (G n) ≤ B ^ 2 := by
    intro n
    refine le_trans (Work.FTS.StrongLWP.HkSq_mono_of_mem (k := m) (k' := k) hkm (hmem n)) ?_
    have hsq : Work.Spaces.HkSq α m (G n) = Work.Spaces.HkNorm α m (G n) ^ 2 := by
      rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α m (G n))]
    rw [hsq]
    exact pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α m (G n)) (hb n) 2
  -- the a.e. domination of the limit integrand by the `liminf` of the approximants
  have hae : ∀ z ∈ Work.Spaces.Iz, ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      Work.Spaces.HkIntegrand α k f z θ
        ≤ Filter.liminf (fun n => Work.Spaces.HkIntegrand α k (G n) z θ) Filter.atTop := by
    intro z hz'
    rcases lt_or_eq_of_le (show (0 : ℝ) ≤ z from hz') with hzpos | hz0
    · have hμ : volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo 0 (π / 2)) :=
        (Measure.restrict_congr_set
          (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ))
            (b := (π / 2)))).symm
      rw [hμ]
      refine ae_restrict_of_forall_mem measurableSet_Ioo fun θ hθ => ?_
      have hmem' : (z, θ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) := ⟨hzpos, hθ⟩
      have hc := HkIntegrand_tendsto_of_mixed (α := α) (k := k) (F := f) (Fs := G)
        (z := z) (θ := θ) (fun j i hji => hconv j i hji z θ hmem')
      rw [hc.liminf_eq]
    · subst hz0
      filter_upwards with θ
      have hzero : (fun n : ℕ => Work.Spaces.HkIntegrand α k (G n) 0 θ) = fun _ : ℕ => (0 : ℝ) :=
        funext fun n => HkIntegrand_eq_zero_at_z_zero α k (G n) θ
      rw [HkIntegrand_eq_zero_at_z_zero α k f θ, hzero, Filter.liminf_const]
  -- Fatou, twice
  obtain ⟨hmemf, hsq⟩ := Work.FTS.EllExist.Honesty.hkMem_of_liminf_slice
    (α := α) (k := k) (f := f) (fs := G) (C := B ^ 2) (sq_nonneg B)
    hmemG hbSq
    (aesm_slice_HkIntegrand_of_contDiffOn α k f hreg)
    (aesm_integral_HkIntegrand_of_contDiffOn α k f hreg) hae hz
  refine ⟨hmemf, ?_⟩
  have hB0 : 0 ≤ B := le_trans (Work.Spaces.HkNorm_nonneg α m (G 0)) (hb 0)
  calc Work.Spaces.HkNorm α k f = Real.sqrt (Work.Spaces.HkSq α k f) := rfl
    _ ≤ Real.sqrt (B ^ 2) := Real.sqrt_le_sqrt hsq
    _ = B := Real.sqrt_sq hB0

end Work.FTS.StrongEps
