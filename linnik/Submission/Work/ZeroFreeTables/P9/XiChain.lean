/-
# ZeroFreeTables/P9/XiChain

A **clean local copy** of the small `Ξ`-cofactor chain that the `P9` engine needs, so that the
`P₃`/`P9` chapter builds without touching the (currently non-building) shared-library chain
`FarRepel.xiDerivPF → FarRepel.xiE_cofactor_logbound → FarRepel.xiE_facLogLower`.

*Why a copy.*  The shared library contains two files declaring the same names in
`Commons.NumberTheory.Linnik` — `logDeriv_pf_identity` and `completedL_pf_identity_rect` (both
define `pfP`, `pfZ`, …).  Any module whose closure contains both fails with
`environment already contains 'Commons.NumberTheory.Linnik.pfP'`; `FarRepel.xiE_facLogLower`
imports the former while the round-2 contract transitively imports the latter, so the chain
above cannot build in the presence of the contract.  Its only use of the old file is the
auxiliary family `pf_norm_zpow_eq`, `pf_zpow_pos`, `pf_zpow_le_of_le`, `pf_log_zpow`,
`pf_norm_finset_prod`, all of which the *rect* file states identically — so replacing the
import by `completedL_pf_identity_rect` makes the chain build unchanged.

The three theorems below (`xiE_facLogLower`, `xiE_cofactor_logbound`, `xiE_truncBound`,
`xiDerivPF`) are verbatim the shared ones, in the same namespace
`Work.LinnikAreas.FarRepel`, with only the broken import replaced.  Only
`P9/zetaDiffExplicit_gen` consumes them.
-/
import Mathlib
import Submission.Commons.NumberTheory.Linnik.completedL_pf_identity_rect
import Submission.Work.LinnikAreas.DhK.XiAux
import Submission.Work.LinnikAreas.FarRepel.xiCofactorDefs
import Submission.Work.LinnikAreas.FarRepel.xiE_P0_log_bound
import Submission.Work.LinnikAreas.FarRepel.xiE_annulusBound
import Submission.Work.LinnikAreas.FarRepel.xiE_goodRadius
import Submission.Work.ZeroFreeTables.P3.CompletedDerivPF

open scoped Classical BigOperators
open Filter Metric
open Work.LinnikAreas.DhK

set_option autoImplicit false
set_option maxHeartbeats 0

noncomputable section

namespace Work.LinnikAreas.FarRepel


open scoped Classical BigOperators
open Metric

set_option maxHeartbeats 0

theorem xiE_facLogLower {A T : ℝ} (hA0 : 0 ≤ A) (hT0 : 0 < T)
    (hmargin : ∀ u : ℂ, Work.LinnikAreas.DhK.Xi u = 0 →
      (Work.LinnikAreas.DhK.xiL A) ^ 2 * |‖u‖ - T| ≥ 1)
    {ζ : ℂ} (hζ : ‖ζ‖ = T) :
    -Real.log ‖∏ᶠ u : ℂ, (ζ - u) ^
        (MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi (Metric.closedBall (0 : ℂ) T) u)‖ ≤
      (2 * Real.log (Work.LinnikAreas.DhK.xiL A)) *
        (∑ᶠ u : ℂ, ((MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi
          (Metric.closedBall (0 : ℂ) T)) u : ℝ)) := by
  classical
  let d : ℂ → ℤ := fun u =>
    MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi (closedBall (0 : ℂ) T) u
  let L : ℝ := Work.LinnikAreas.DhK.xiL A
  have hLpos : 0 < L := Work.LinnikAreas.DhK.xiL_pos hA0
  have hL2pos : 0 < L ^ 2 := pow_pos hLpos 2
  let m : ℝ := 1 / L ^ 2
  have hmpos : 0 < m := by dsimp [m]; exact div_pos (by norm_num) hL2pos
  have hd_nonneg : ∀ u, 0 ≤ d u := by
    intro u
    dsimp [d]
    exact Work.LinnikAreas.DhK.Xi_divisor_nonneg T u
  have hsupport : (Function.support d).Finite := by
    dsimp [d]
    exact Work.LinnikAreas.DhK.Xi_divisor_support_finite T
  let S : Finset ℂ := hsupport.toFinset
  have hmemS : ∀ u : ℂ, u ∈ S ↔ d u ≠ 0 := by
    intro u
    dsimp [S]
    rw [Set.Finite.mem_toFinset]
    rfl
  have hdist : ∀ u : ℂ, u ∈ S → m ≤ ‖ζ - u‖ := by
    intro u hu
    have hdne : d u ≠ 0 := (hmemS u).mp hu
    have hzu : Work.LinnikAreas.DhK.Xi u = 0 :=
      Work.LinnikAreas.DhK.Xi_divisor_ne_zero_is_zero (R := T) (by simpa [d] using hdne)
    have hmarg := hmargin u hzu
    have hmul' : 1 ≤ |‖u‖ - T| * (L ^ 2) := by
      simpa [mul_comm, L] using hmarg
    have hle_m : m ≤ |‖u‖ - T| := (div_le_iff₀ hL2pos).mpr hmul'
    have habs : |‖u‖ - ‖ζ‖| ≤ ‖ζ - u‖ := by
      simpa [abs_sub_comm] using (abs_norm_sub_norm_le ζ u)
    have hrew : |‖u‖ - T| = |‖u‖ - ‖ζ‖| := by rw [hζ]
    exact le_trans hle_m (by rwa [hrew])
  have hprod_pos_fac : ∀ u : ℂ, u ∈ S → 0 < ‖(ζ - u) ^ (d u)‖ := by
    intro u hu
    have hb : 0 < ‖ζ - u‖ := lt_of_lt_of_le hmpos (hdist u hu)
    have hpow : ‖(ζ - u) ^ (d u)‖ = ‖ζ - u‖ ^ (d u) :=
      Commons.NumberTheory.Linnik.pf_norm_zpow_eq (ζ - u) (d u)
    rw [hpow]
    exact Commons.NumberTheory.Linnik.pf_zpow_pos hb (hd_nonneg u)
  have hlog_per : ∀ u : ℂ, u ∈ S →
      -Real.log ‖(ζ - u) ^ (d u)‖ ≤ (d u : ℝ) * (2 * Real.log L) := by
    intro u hu
    have hmle : m ≤ ‖ζ - u‖ := hdist u hu
    have hb : 0 < ‖ζ - u‖ := lt_of_lt_of_le hmpos hmle
    have hpow_le : m ^ (d u) ≤ ‖ζ - u‖ ^ (d u) :=
      Commons.NumberTheory.Linnik.pf_zpow_le_of_le (le_of_lt hmpos) hmle (hd_nonneg u)
    have hnorm : ‖(ζ - u) ^ (d u)‖ = ‖ζ - u‖ ^ (d u) :=
      Commons.NumberTheory.Linnik.pf_norm_zpow_eq (ζ - u) (d u)
    have h1 : 0 < m ^ (d u) := Commons.NumberTheory.Linnik.pf_zpow_pos hmpos (hd_nonneg u)
    have hlog_ge : Real.log (m ^ (d u)) ≤ Real.log ‖(ζ - u) ^ (d u)‖ := by
      rw [hnorm]
      exact Real.log_le_log h1 hpow_le
    have hlogm : Real.log (m ^ (d u)) = (d u : ℝ) * Real.log m :=
      Commons.NumberTheory.Linnik.pf_log_zpow hmpos (hd_nonneg u)
    have hlogmval : Real.log m = -2 * Real.log L := by
      dsimp [m]
      rw [one_div, Real.log_inv, Real.log_pow]
      ring
    have hstep : (d u : ℝ) * Real.log m ≤ Real.log ‖(ζ - u) ^ (d u)‖ := by
      simpa [hlogm] using hlog_ge
    have hcalc : -Real.log ‖(ζ - u) ^ (d u)‖ ≤ -(d u : ℝ) * Real.log m := by linarith
    have hmval : -(d u : ℝ) * Real.log m = (d u : ℝ) * (2 * Real.log L) := by
      rw [hlogmval]; ring
    linarith
  have hsubP : Function.mulSupport (fun u : ℂ => (ζ - u) ^ (d u)) ⊆ (S : Set ℂ) := by
    intro u hu
    rw [Function.mem_mulSupport] at hu
    have hdne : d u ≠ 0 := by
      intro hd0
      exact hu (by simp [hd0])
    exact (hmemS u).mpr hdne
  have hprod_eq : (∏ᶠ u : ℂ, (ζ - u) ^ (d u)) = ∏ u ∈ S, (ζ - u) ^ (d u) :=
    finprod_eq_prod_of_mulSupport_subset (fun u : ℂ => (ζ - u) ^ (d u)) hsubP
  have hfin_eq : (∑ᶠ u : ℂ, ((d u : ℤ) : ℝ)) = ∑ u ∈ S, ((d u : ℤ) : ℝ) := by
    refine finsum_eq_sum_of_support_subset (fun u : ℂ => ((d u : ℤ) : ℝ)) ?_
    intro u hu
    rw [Function.mem_support] at hu
    have hdne : d u ≠ 0 := by
      intro hd0
      exact hu (by simp [hd0])
    exact (hmemS u).mpr hdne
  calc
    -Real.log ‖∏ᶠ u : ℂ, (ζ - u) ^ (d u)‖
        = -Real.log ‖∏ u ∈ S, (ζ - u) ^ (d u)‖ := by rw [hprod_eq]
    _ = -Real.log (∏ u ∈ S, ‖(ζ - u) ^ (d u)‖) := by
        rw [Commons.NumberTheory.Linnik.pf_norm_finset_prod S (fun u => (ζ - u) ^ (d u))]
    _ = -(∑ u ∈ S, Real.log ‖(ζ - u) ^ (d u)‖) := by
        rw [Real.log_prod]
        intro u hu
        exact (hprod_pos_fac u hu).ne'
    _ = ∑ u ∈ S, -Real.log ‖(ζ - u) ^ (d u)‖ := by simp [Finset.sum_neg_distrib]
    _ ≤ ∑ u ∈ S, ((d u : ℤ) : ℝ) * (2 * Real.log L) :=
        Finset.sum_le_sum (fun u hu => hlog_per u hu)
    _ = (∑ u ∈ S, ((d u : ℤ) : ℝ)) * (2 * Real.log L) := by rw [Finset.sum_mul]
    _ = (∑ᶠ u : ℂ, ((d u : ℤ) : ℝ)) * (2 * Real.log L) := by rw [← hfin_eq]
    _ = (2 * Real.log L) * (∑ᶠ u : ℂ, ((d u : ℤ) : ℝ)) := by ring
    _ = (2 * Real.log (Work.LinnikAreas.DhK.xiL A)) *
        (∑ᶠ u : ℂ, ((MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi
          (Metric.closedBall (0 : ℂ) T)) u : ℝ)) := by
        simp only [d, L]



/-- **Cofactor of `Ξ` on the disc of radius `T`, with logarithmic bound `M0`.**

`Ξ = DhK.Xi = 1/2 + (1/2)·s(s-1)·Λ₀(s)` is the entire completion of `ζ`.  If `T` is a "good
radius" (no zero `u` of `Ξ` comes within `1/(xiL A)²` of the circle `‖u‖ = T`, i.e.
`(xiL A)²·|‖u‖ - T| ≥ 1`), and `zc`, `gc` are the zero-counting and circle-growth constants of
`Ξ` in the `xiL` scale, then there is an analytic non-vanishing cofactor `g` with
`Ξ z = (∏ᶠ u, (z-u)^{divisor Ξ (closedBall 0 T) u})·g z` on `B(0,T)` (and on a slightly larger
disc `B(0,T+ε)`), with `log‖g‖ ≤ M0` on `B(0,T)` and `M0` bounded by
`(4·gc + 20·zc + |log‖Ξ 0‖| + 1)·(A·(xiL A)² + 1)`.  Exact analogue of
`Commons.NumberTheory.Linnik.pf_cofactor_logbound` with `Λ := DhK.Xi`, `L_N N A := xiL A`.

PROOF ROUTE: mirror `Commons.NumberTheory.Linnik.pf_cofactor_logbound` and its helpers
(`pf_fac_log_lower`, `pf_P0_log_bound`, `pf_P_ne_zero_circle`, `pf_LogΛ_bound`); the same
argument is also carried out in `Submission/Work/LinnikAreas/ownRepelNW/xiE_cofactor_logbound.lean`
and its helper modules (readable for the shape of the proof and the constants), but that module
must not be imported.  Use `Commons.NumberTheory.Linnik.factorization_open` (generic, in the
import closure of `XiAux`) for the cofactor, `DhK.Xi_divisor_nonneg`,
`DhK.Xi_divisor_support_finite`, `DhK.Xi_divisor_ne_zero_is_zero`,
`Commons.NumberTheory.Linnik.pf_norm_finset_prod`, `...pf_zpow_pos`, `...pf_zpow_le_of_le`,
`...pf_log_zpow`, `...pf_norm_zpow_eq`, the maximum-modulus principle
`Complex.norm_le_of_forall_mem_frontier_norm_le`, and the `xiL`-arithmetic `DhK.xiL_ge_two`,
`DhK.xiL_pos`, `DhK.xiL_mono`, `DhK.xiL_log_le`, `DhK.xiL_two_mul_le`. -/
theorem xiE_cofactor_logbound {A T : ℝ} (hA0 : 0 ≤ A) (hA1 : 1 ≤ A)
    (hTpos : 0 < T) (hT2 : 2 ≤ T) (hT2A : T ≤ 2 * A)
    (hmargin : ∀ u : ℂ, Work.LinnikAreas.DhK.Xi u = 0 →
      (Work.LinnikAreas.DhK.xiL A) ^ 2 * |‖u‖ - T| ≥ 1)
    (zc gc : ℝ) (hzc_nonneg : 0 ≤ zc) (hgc_nonneg : 0 ≤ gc)
    (hzc : ∀ R : ℝ, 2 ≤ R →
      (∑ᶠ u : ℂ, ((MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi
        (Metric.closedBall (0 : ℂ) R)) u : ℝ)) ≤ zc * R * Work.LinnikAreas.DhK.xiL R)
    (hgc : ∀ R : ℝ, 2 ≤ R → ∀ z : ℂ, ‖z‖ = R →
      ‖Work.LinnikAreas.DhK.Xi z‖ ≤ Real.exp (gc * R * Work.LinnikAreas.DhK.xiL R))
    (δ₀ : ℝ) (hδ₀pos : 0 < δ₀)
    (hLgeD : |Real.log δ₀| ≤ Work.LinnikAreas.DhK.xiL A)
    (hδ₀ : ∀ u : ℂ, Work.LinnikAreas.DhK.Xi u = 0 → δ₀ ≤ ‖u‖) :
    XiCofactorBound A T zc gc := by
  classical
  unfold XiCofactorBound
  -- `Ξ` is entire, nonzero at `0`, and has no zero on the good circle `‖u‖ = T`
  have hXi0 : Xi 0 ≠ 0 := Xi_zero_ne
  have hXidiff : Differentiable ℂ Xi := Xi_differentiable
  have hcirc : ∀ u : ℂ, ‖u‖ = T → Xi u ≠ 0 := by
    intro u hu hz
    have hmm := hmargin u hz
    have hzero : |‖u‖ - T| = 0 := by simp [hu]
    have hb : (1 : ℝ) ≤ 0 := by simpa [hzero, mul_zero] using hmm
    linarith
  -- canonical factorization of `Ξ` on a disc slightly larger than `B(0,T)`
  rcases Commons.NumberTheory.Linnik.factorization_open (f := Xi) (R := T) hTpos hXidiff
    hXi0 hcirc with ⟨g, ε, hε, hg_an, hg_nz, hfac⟩
  have hg_an_T : AnalyticOnNhd ℂ g (ball 0 T) := by
    intro w hw
    have hwT : ‖w‖ < T := mem_ball_zero_iff.mp hw
    have hw' : ‖w‖ < T + ε := by linarith
    exact hg_an w (mem_ball_zero_iff.mpr hw')
  have hg_nz_T : ∀ w : ℂ, w ∈ ball 0 T → g w ≠ 0 := by
    intro w hw
    have hwT : ‖w‖ < T := mem_ball_zero_iff.mp hw
    have hw' : ‖w‖ < T + ε := by linarith
    exact hg_nz w (mem_ball_zero_iff.mpr hw')
  have hfac_T : ∀ z : ℂ, z ∈ ball 0 T → Xi z =
      (∏ᶠ u : ℂ, (z - u) ^ (MeromorphicOn.divisor Xi (Metric.closedBall 0 T) u)) * g z := by
    intro z hz
    have hzT : ‖z‖ < T := mem_ball_zero_iff.mp hz
    have hz' : ‖z‖ < T + ε := by linarith
    exact hfac z (mem_ball_zero_iff.mpr hz')
  -- the four terms of the logarithmic bound
  let L : ℝ := xiL A
  let LT : ℝ := xiL T
  let Z : ℝ := ∑ᶠ u : ℂ, ((MeromorphicOn.divisor Xi (Metric.closedBall 0 T)) u : ℝ)
  let Q1 : ℝ := gc * T * LT
  let Q2 : ℝ := (2 * Real.log L) * (zc * T * LT)
  let Q3 : ℝ := |Real.log ‖Xi 0‖|
  let Q4 : ℝ := (zc * T * LT) * (Real.log T + |Real.log δ₀|)
  let M0 : ℝ := Q1 + Q2 + Q3 + Q4 + 1
  have hL2 : 2 ≤ L := xiL_ge_two hA0
  have hLpos : 0 < L := xiL_pos hA0
  have hL1 : 1 ≤ L := by linarith
  have hLTpos : 0 < LT := xiL_pos (le_of_lt hTpos)
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hlogδ0 : 0 ≤ |Real.log δ₀| := abs_nonneg _
  have hTge0 : 0 ≤ T := le_of_lt hTpos
  have hQ1 : 0 ≤ Q1 := by dsimp [Q1]; positivity
  have hQ2 : 0 ≤ Q2 := by dsimp [Q2]; positivity
  have hQ3 : 0 ≤ Q3 := by dsimp [Q3]; exact abs_nonneg _
  have hQ4 : 0 ≤ Q4 := by
    dsimp [Q4]
    have h1 : 0 ≤ Real.log T + |Real.log δ₀| := by linarith
    positivity
  have hM0_nonneg : 0 ≤ M0 := by dsimp [M0]; linarith
  -- boundary (circle) estimate: `log ‖g ζ‖ ≤ Q1 + Q2` for `‖ζ‖ = T`
  have hbnd : ∀ ζ : ℂ, ‖ζ‖ = T → Real.log ‖g ζ‖ ≤ Q1 + Q2 := by
    intro ζ hζ
    have hζε : ζ ∈ ball 0 (T + ε) := mem_ball_zero_iff.mpr (by linarith [hζ, hε])
    have hXiζ : Xi ζ ≠ 0 := hcirc ζ hζ
    have hgζ : g ζ ≠ 0 := hg_nz ζ hζε
    have hfacζ : Xi ζ =
        (∏ᶠ u : ℂ, (ζ - u) ^ (MeromorphicOn.divisor Xi (Metric.closedBall 0 T) u)) * g ζ :=
      hfac ζ hζε
    have hPζ : (∏ᶠ u : ℂ, (ζ - u) ^
        (MeromorphicOn.divisor Xi (Metric.closedBall 0 T) u)) ≠ 0 := by
      have hmul : (∏ᶠ u : ℂ, (ζ - u) ^
          (MeromorphicOn.divisor Xi (Metric.closedBall 0 T) u)) * g ζ ≠ 0 := by
        simpa [hfacζ] using hXiζ
      exact (mul_ne_zero_iff.mp hmul).1
    have hlog_mul : Real.log ‖Xi ζ‖ =
        Real.log ‖(∏ᶠ u : ℂ, (ζ - u) ^
          (MeromorphicOn.divisor Xi (Metric.closedBall 0 T) u))‖
          + Real.log ‖g ζ‖ := by
      rw [hfacζ]
      exact Commons.NumberTheory.Linnik.pf_log_eq_of_mul hPζ hgζ
    have hlogXi : Real.log ‖Xi ζ‖ ≤ gc * T * LT := by
      have hb := hgc T hT2 ζ hζ
      have hle : Real.log ‖Xi ζ‖ ≤ Real.log (Real.exp (gc * T * xiL T)) :=
        Real.log_le_log (norm_pos_iff.mpr hXiζ) hb
      rwa [Real.log_exp] at hle
    have hfaclow : -Real.log ‖(∏ᶠ u : ℂ, (ζ - u) ^
        (MeromorphicOn.divisor Xi (Metric.closedBall 0 T) u))‖ ≤ (2 * Real.log L) * Z := by
      have hb := xiE_facLogLower (A := A) (T := T) hA0 hTpos hmargin hζ
      simpa only [L, Z] using hb
    have hZle : Z ≤ zc * T * LT := by
      have h := hzc T hT2
      simpa only [Z, LT] using h
    have hstep : Real.log ‖g ζ‖ = Real.log ‖Xi ζ‖ -
        Real.log ‖(∏ᶠ u : ℂ, (ζ - u) ^
          (MeromorphicOn.divisor Xi (Metric.closedBall 0 T) u))‖ := by
      rw [hlog_mul]; ring
    have h2L : 0 ≤ 2 * Real.log L := by linarith
    have hQ2ge : (2 * Real.log L) * Z ≤ Q2 := by
      have h := mul_le_mul_of_nonneg_left hZle h2L
      simpa only [Q2] using h
    calc Real.log ‖g ζ‖
        = Real.log ‖Xi ζ‖ - Real.log ‖(∏ᶠ u : ℂ, (ζ - u) ^
            (MeromorphicOn.divisor Xi (Metric.closedBall 0 T) u))‖ := hstep
      _ ≤ gc * T * LT + (2 * Real.log L) * Z := by linarith
      _ ≤ gc * T * LT + Q2 := by linarith
      _ = Q1 + Q2 := by dsimp [Q1]
  -- the boundary estimate extends to the whole disc by the maximum modulus principle
  have hball : ∀ w : ℂ, w ∈ ball 0 T → Real.log ‖g w‖ ≤ M0 := by
    intro w hw
    have hg_cont : DiffContOnCl ℂ g (ball 0 T) := by
      refine DifferentiableOn.diffContOnCl ?_
      have hcl : DifferentiableOn ℂ g (closedBall 0 T) := by
        intro x hx
        rw [Metric.mem_closedBall, dist_eq_norm] at hx
        have hx' : x ∈ ball 0 (T + ε) := by
          have hxT : ‖x‖ ≤ T := by simpa using hx
          exact mem_ball_zero_iff.mpr (by linarith [hε])
        exact (hg_an.differentiableOn.differentiableAt
          (Metric.isOpen_ball.mem_nhds hx')).differentiableWithinAt
      simpa [closure_ball (0 : ℂ) (ne_of_gt hTpos)] using hcl
    have hfront : ∀ ζ : ℂ, ζ ∈ frontier (ball 0 T) → ‖g ζ‖ ≤ Real.exp M0 := by
      intro ζ hζf
      rw [frontier_ball (0 : ℂ) (ne_of_gt hTpos), Metric.mem_sphere, dist_eq_norm] at hζf
      have hζ : ‖ζ‖ = T := by simpa using hζf
      have hb := hbnd ζ hζ
      have hζε : ζ ∈ ball 0 (T + ε) := mem_ball_zero_iff.mpr (by linarith [hζ, hε])
      have hle : Real.log ‖g ζ‖ ≤ M0 := by
        have hQ12 : Q1 + Q2 ≤ M0 := by dsimp [M0]; linarith [hQ3, hQ4]
        linarith
      exact le_trans (le_of_eq (Real.exp_log (norm_pos_iff.mpr (hg_nz ζ hζε))).symm)
        (Real.exp_le_exp.mpr hle)
    have hcl : w ∈ closure (ball 0 T) := by
      rw [closure_ball (0 : ℂ) (ne_of_gt hTpos), Metric.mem_closedBall, dist_eq_norm]
      have hw' : ‖w‖ < T := mem_ball_zero_iff.mp hw
      simpa using le_of_lt hw'
    have hnorm : ‖g w‖ ≤ Real.exp M0 :=
      Complex.norm_le_of_forall_mem_frontier_norm_le
        (Metric.isBounded_ball (x := (0 : ℂ)) (r := T)) hg_cont hfront hcl
    have hpos : 0 < ‖g w‖ := norm_pos_iff.mpr (hg_nz_T w hw)
    have hle : Real.log ‖g w‖ ≤ Real.log (Real.exp M0) := Real.log_le_log hpos hnorm
    rwa [Real.log_exp] at hle
  -- the value at the origin
  have horigin : |Real.log ‖g 0‖| ≤ M0 := by
    have h0T : (0 : ℂ) ∈ ball 0 T := mem_ball_zero_iff.mpr (by simpa using hTpos)
    have hfac0 := hfac_T 0 h0T
    have hP0 : (∏ᶠ u : ℂ, ((0 : ℂ) - u) ^
        (MeromorphicOn.divisor Xi (Metric.closedBall 0 T) u)) ≠ 0 := by
      have hmul : (∏ᶠ u : ℂ, ((0 : ℂ) - u) ^
          (MeromorphicOn.divisor Xi (Metric.closedBall 0 T) u)) * g 0 ≠ 0 := by
        simpa [hfac0] using hXi0
      exact (mul_ne_zero_iff.mp hmul).1
    have hg0nz : g 0 ≠ 0 := hg_nz_T 0 h0T
    have hlog_mul0 : Real.log ‖Xi 0‖ = Real.log
        ‖(∏ᶠ u : ℂ, ((0 : ℂ) - u) ^ (MeromorphicOn.divisor Xi (Metric.closedBall 0 T) u))‖
          + Real.log ‖g 0‖ := by
      rw [hfac0]
      exact Commons.NumberTheory.Linnik.pf_log_eq_of_mul hP0 hg0nz
    have hP0b := xiE_P0_log_bound (T := T) (le_trans (by norm_num) hT2) δ₀ hδ₀pos hδ₀
    have hZle : Z ≤ zc * T * LT := by
      have h := hzc T hT2
      simpa only [Z, LT] using h
    have hP0le : |Real.log
        ‖(∏ᶠ u : ℂ, ((0 : ℂ) - u) ^
          (MeromorphicOn.divisor Xi (Metric.closedBall 0 T) u))‖| ≤ Q4 := by
      have hBnn : 0 ≤ Real.log T + |Real.log δ₀| := by linarith
      have h1 : Z * (Real.log T + |Real.log δ₀|) ≤
          (zc * T * LT) * (Real.log T + |Real.log δ₀|) :=
        mul_le_mul_of_nonneg_right hZle hBnn
      calc |Real.log ‖(∏ᶠ u : ℂ, ((0 : ℂ) - u) ^
              (MeromorphicOn.divisor Xi (Metric.closedBall 0 T) u))‖|
            ≤ Z * (Real.log T + |Real.log δ₀|) := by simpa only [Z] using hP0b
        _ ≤ (zc * T * LT) * (Real.log T + |Real.log δ₀|) := h1
        _ = Q4 := by dsimp [Q4]
    have hlogg0 : |Real.log ‖g 0‖| ≤ Q3 + Q4 := by
      have hAb : |Real.log ‖Xi 0‖ - Real.log
          ‖(∏ᶠ u : ℂ, ((0 : ℂ) - u) ^
            (MeromorphicOn.divisor Xi (Metric.closedBall 0 T) u))‖| ≤
          |Real.log ‖Xi 0‖| + |Real.log
          ‖(∏ᶠ u : ℂ, ((0 : ℂ) - u) ^
            (MeromorphicOn.divisor Xi (Metric.closedBall 0 T) u))‖| := by
        rw [sub_eq_add_neg]
        calc |Real.log ‖Xi 0‖ + -Real.log ‖(∏ᶠ u : ℂ, ((0 : ℂ) - u) ^
                (MeromorphicOn.divisor Xi (Metric.closedBall 0 T) u))‖|
              ≤ |Real.log ‖Xi 0‖| + |(-Real.log ‖(∏ᶠ u : ℂ, ((0 : ℂ) - u) ^
                (MeromorphicOn.divisor Xi (Metric.closedBall 0 T) u))‖)| := abs_add_le _ _
          _ = |Real.log ‖Xi 0‖| + |Real.log ‖(∏ᶠ u : ℂ, ((0 : ℂ) - u) ^
                (MeromorphicOn.divisor Xi (Metric.closedBall 0 T) u))‖| := by rw [abs_neg]
      have hrew : Real.log ‖g 0‖ = Real.log ‖Xi 0‖ - Real.log
          ‖(∏ᶠ u : ℂ, ((0 : ℂ) - u) ^
            (MeromorphicOn.divisor Xi (Metric.closedBall 0 T) u))‖ := by
        rw [hlog_mul0]; ring
      rw [hrew]
      have h3 : |Real.log ‖Xi 0‖ - Real.log ‖(∏ᶠ u : ℂ, ((0 : ℂ) - u) ^
          (MeromorphicOn.divisor Xi (Metric.closedBall 0 T) u))‖| ≤ Q3 + Q4 := by
        have hQ3eq : |Real.log ‖Xi 0‖| = Q3 := by dsimp [Q3]
        linarith [hAb, hP0le, hQ3eq]
      exact h3
    have h34 : Q3 + Q4 ≤ M0 := by dsimp [M0]; linarith [hQ1, hQ2]
    have hg0ball : Real.log ‖g 0‖ ≤ M0 := hball 0 h0T
    have h2 : -M0 ≤ Real.log ‖g 0‖ := by
      have hle' : |Real.log ‖g 0‖| ≤ M0 := le_trans hlogg0 h34
      linarith [abs_le.mp hle']
    exact abs_le.mpr ⟨h2, hg0ball⟩
  -- arithmetic: the four terms fit the prescribed shape of `M0`
  have hM0_bound : M0 ≤ (4 * gc + 20 * zc + |Real.log ‖Xi 0‖| + 1) * (A * L ^ 2 + 1) := by
    have hLT2 : LT ≤ 2 * L := by
      have hmono : xiL T ≤ xiL (2 * A) := xiL_mono hTge0 hT2A
      have h2 : xiL (2 * A) ≤ 2 * xiL A := xiL_two_mul_le hA1
      dsimp only [LT, L]
      linarith
    have hlogT_le_LT : Real.log T ≤ LT := by
      have h1 : Real.log T ≤ Real.log (T + 2) := Real.log_le_log hTpos (by linarith)
      dsimp only [LT, xiL]
      linarith
    have hlogT_le : Real.log T ≤ 2 * L := le_trans hlogT_le_LT hLT2
    have hTl : T * LT ≤ (2 * A) * (2 * L) := by
      have h1 : T ≤ 2 * A := hT2A
      have h2 : LT ≤ 2 * L := hLT2
      nlinarith [hTge0, le_of_lt hLTpos, hA0, le_of_lt hLpos]
    have hQ1le : Q1 ≤ 4 * gc * A * L ^ 2 := by
      have hga : 0 ≤ gc * A := mul_nonneg hgc_nonneg hA0
      have hLsq : L ≤ L ^ 2 := by nlinarith [hL1]
      have hstep : gc * T * LT ≤ gc * ((2 * A) * (2 * L)) := by
        have := mul_le_mul_of_nonneg_left hTl hgc_nonneg
        nlinarith [this]
      have hstep2 : gc * ((2 * A) * (2 * L)) = 4 * (gc * A * L) := by ring
      have hstep3 : gc * A * L ≤ gc * A * L ^ 2 := mul_le_mul_of_nonneg_left hLsq hga
      calc Q1 = gc * T * LT := rfl
        _ ≤ gc * ((2 * A) * (2 * L)) := hstep
        _ = 4 * (gc * A * L) := hstep2
        _ ≤ 4 * (gc * A * L ^ 2) := by linarith
        _ = 4 * gc * A * L ^ 2 := by ring
    have hQ2le : Q2 ≤ 8 * zc * A * L ^ 2 := by
      have hlogL_le : Real.log L ≤ L := Real.log_le_self (le_of_lt hLpos)
      have h2log : 2 * Real.log L ≤ 2 * L := by linarith
      have hzT : 0 ≤ zc * T * LT := by positivity
      have hzle : zc * T * LT ≤ zc * ((2 * A) * (2 * L)) := by
        have := mul_le_mul_of_nonneg_left hTl hzc_nonneg
        nlinarith [this]
      calc Q2 = (2 * Real.log L) * (zc * T * LT) := rfl
        _ ≤ (2 * L) * (zc * T * LT) := mul_le_mul_of_nonneg_right h2log hzT
        _ ≤ (2 * L) * (zc * ((2 * A) * (2 * L))) := by
            have h2L : 0 ≤ 2 * L := by linarith
            exact mul_le_mul_of_nonneg_left hzle h2L
        _ = 8 * zc * A * L ^ 2 := by ring
    have hQ3le : Q3 ≤ |Real.log ‖Xi 0‖| * (A * L ^ 2 + 1) := by
      have h1 : 1 ≤ A * L ^ 2 + 1 := by nlinarith [hA0, sq_nonneg L]
      dsimp only [Q3]
      nlinarith [abs_nonneg (Real.log ‖Xi 0‖)]
    have hQ4le : Q4 ≤ 12 * zc * A * L ^ 2 := by
      have hB : Real.log T + |Real.log δ₀| ≤ 3 * L := by
        have h2 : |Real.log δ₀| ≤ L := by dsimp only [L]; exact hLgeD
        linarith
      have hzle : zc * T * LT ≤ zc * ((2 * A) * (2 * L)) := by
        have := mul_le_mul_of_nonneg_left hTl hzc_nonneg
        nlinarith [this]
      have hBnn : 0 ≤ Real.log T + |Real.log δ₀| := by linarith
      have hz2A : 0 ≤ zc * ((2 * A) * (2 * L)) := by positivity
      calc Q4 = (zc * T * LT) * (Real.log T + |Real.log δ₀|) := rfl
        _ ≤ (zc * ((2 * A) * (2 * L))) * (3 * L) :=
            mul_le_mul hzle hB hBnn hz2A
        _ = 12 * zc * A * L ^ 2 := by ring
    dsimp only [M0]
    nlinarith [hQ1le, hQ2le, hQ3le, hQ4le, hgc_nonneg, hzc_nonneg, hA0, sq_nonneg L,
      abs_nonneg (Real.log ‖Xi 0‖), hLpos]
  exact ⟨g, M0, hM0_nonneg, hg_an_T, hg_nz_T, hfac_T,
    ⟨ε, hε, hg_an, hfac⟩, hball, horigin, by simpa only [L] using hM0_bound⟩



open Work.LinnikAreas.DhK

/-- **Truncation error of the `k`-th derivative partial-fraction sum for `Ξ`.** -/
lemma xiE_truncBound (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ A₁ : ℝ, ∀ A : ℝ, A₁ ≤ A → ∀ T : ℝ, A ≤ T → T ≤ 2 * A →
      (∀ u : ℂ, Xi u = 0 → (xiL A) ^ 2 * |‖u‖ - T| ≥ 1) →
      ∀ s : ℂ, Xi s ≠ 0 → 8 * ‖s‖ ≤ T →
        ‖iteratedDeriv k (fun z => deriv Xi z / Xi z) s
            - ((-1 : ℂ) ^ k * (k.factorial : ℂ)) *
              (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Xi (Metric.closedBall 0 T)) u : ℤ) : ℂ) *
                (1 / (s - u)) ^ (k + 1))‖
          ≤ C * (xiL A) ^ 2 / A * (1 + ‖s‖) := by
  classical
  obtain ⟨zc, hzcnn, hzc⟩ := Xi_zeroCount_L
  obtain ⟨gc, hgcnn, hgc⟩ := Xi_growth_L
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := Xi_zero_ge_delta
  let K0 : ℝ := 4 * gc + 20 * zc + |Real.log ‖Xi 0‖| + 1
  have hK0nn : 0 ≤ K0 := by
    dsimp [K0]
    nlinarith [hzcnn, hgcnn, abs_nonneg (Real.log ‖Xi 0‖)]
  have hK0one : 1 ≤ K0 := by
    dsimp [K0]
    nlinarith [hzcnn, hgcnn, abs_nonneg (Real.log ‖Xi 0‖)]
  let C : ℝ := (k.factorial : ℝ) * 192 * 16 ^ k * K0 * 2
  have hCnn : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hCnn, max (Real.exp |Real.log δ₀|) 2, ?_⟩
  intro A hA T hAT hT2A hmargin s hXis hsT
  have hA2 : 2 ≤ A := le_trans (le_max_right _ _) hA
  have hA1 : 1 ≤ A := by linarith
  have hA0 : 0 ≤ A := by linarith
  have hApos : 0 < A := by linarith
  have hAexp : Real.exp |Real.log δ₀| ≤ A := le_trans (le_max_left _ _) hA
  have hTpos : 0 < T := by linarith
  have hT2 : 2 ≤ T := by linarith
  have hLgeD : |Real.log δ₀| ≤ xiL A := by
    have h1 : |Real.log δ₀| ≤ Real.log A := by
      have h := Real.log_le_log (Real.exp_pos _) hAexp
      rwa [Real.log_exp] at h
    have h2 : Real.log A ≤ xiL A := by
      dsimp [xiL]
      have h3 : Real.log A ≤ Real.log (A + 2) := Real.log_le_log (by linarith) (by linarith)
      linarith
    linarith
  have hcof := xiE_cofactor_logbound hA0 hA1 hTpos hT2 hT2A hmargin zc gc hzcnn hgcnn hzc hgc
      δ₀ hδ₀pos hLgeD hδ₀
  unfold XiCofactorBound at hcof
  obtain ⟨g, M0, hM0nn, hg_an_T, hg_nz_T, hfac_T, hfacs, hball, horigin, hM0le⟩ := hcof
  obtain ⟨ε, hε, hg_an_ε, hfac_ε⟩ := hfacs
  have hs_ball : s ∈ Metric.ball (0 : ℂ) (T + ε) := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    have h8 : ‖s‖ ≤ T / 8 := by linarith
    linarith
  have hdec := Work.ZeroFreeTables.P3.iteratedDeriv_logDeriv_decompose (f := Xi) (g := g)
    (R := T) (ε := ε) Xi_differentiable hfac_ε hg_an_ε hs_ball hXis k
  have hgd := Work.ZeroFreeTables.P3.cofactorIteratedDeriv_le hTpos k hk hg_an_T hg_nz_T
    hM0nn hball horigin hsT
  rw [← Work.ZeroFreeTables.P3.logDeriv_eq_div Xi]
  have hgoal_eq : iteratedDeriv k (logDeriv Xi) s
      - ((-1 : ℂ) ^ k * (k.factorial : ℂ)) *
        (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Xi (Metric.closedBall (0:ℂ) T)) u : ℤ) : ℂ)
          * (1 / (s - u)) ^ (k + 1))
      = iteratedDeriv k (logDeriv g) s := by
    rw [hdec]; ring
  rw [hgoal_eq]
  have hm0 : max M0 1 ≤ K0 * (A * (xiL A) ^ 2 + 1) := by
    have h1 : M0 ≤ (4 * gc + 20 * zc + |Real.log ‖Xi 0‖| + 1)
        * (A * (xiL A) ^ 2 + 1) := by
      simpa [K0] using hM0le
    have h2 : (4 * gc + 20 * zc + |Real.log ‖Xi 0‖| + 1) * (A * (xiL A) ^ 2 + 1)
        ≤ K0 * (A * (xiL A) ^ 2 + 1) := le_of_eq rfl
    have h3 : 1 ≤ K0 * (A * (xiL A) ^ 2 + 1) := by
      have h4 : 1 ≤ A * (xiL A) ^ 2 + 1 := by
        have h5 : 0 ≤ (xiL A) ^ 2 := sq_nonneg _
        nlinarith
      nlinarith [hK0one, h4, hK0nn]
    exact max_le (le_trans h1 h2) h3
  have hTpow : A * A ^ k ≤ T ^ (k + 1) := by
    have hAk : A ^ k ≤ T ^ k := pow_le_pow_left₀ hA0 hAT k
    have h1 : A * A ^ k ≤ A * T ^ k := mul_le_mul_of_nonneg_left hAk hA0
    have h2 : A * T ^ k ≤ T * T ^ k :=
      mul_le_mul_of_nonneg_right hAT (pow_nonneg (by linarith : (0:ℝ) ≤ T) k)
    have h3 : T * T ^ k = T ^ (k + 1) := by rw [pow_succ]; ring
    linarith
  have hden1 : (0:ℝ) < T ^ (k + 1) := pow_pos hTpos _
  have hden2 : (0:ℝ) < A * A ^ k := mul_pos hApos (pow_pos hApos k)
  have hAL2 : 1 ≤ (xiL A) ^ 2 := by
    have h := xiL_ge_two hA0
    nlinarith
  have hAkge : A ≤ A ^ k := by
    calc A = A ^ 1 := (pow_one A).symm
      _ ≤ A ^ k := pow_le_pow_right₀ hA1 hk
  have hkey : max M0 1 / T ^ (k + 1) ≤ 2 * K0 * (xiL A) ^ 2 / A := by
    have s1 : max M0 1 / T ^ (k + 1) ≤ max M0 1 / (A * A ^ k) :=
      div_le_div_of_nonneg_left (by positivity) hden2 hTpow
    have s2 : max M0 1 / (A * A ^ k) ≤ K0 * (A * (xiL A) ^ 2 + 1) / (A * A ^ k) :=
      div_le_div_of_nonneg_right hm0 (le_of_lt hden2)
    have s3 : K0 * (A * (xiL A) ^ 2 + 1) / (A * A ^ k)
        ≤ K0 * (2 * (xiL A) ^ 2 * A) / (A * A ^ k) := by
      have hnum : A * (xiL A) ^ 2 + 1 ≤ 2 * (xiL A) ^ 2 * A := by nlinarith [hAL2, hA1]
      have := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnum hK0nn) (le_of_lt hden2)
      simpa [mul_assoc] using this
    have s4 : K0 * (2 * (xiL A) ^ 2 * A) / (A * A ^ k) = 2 * K0 * (xiL A) ^ 2 / A ^ k := by
      rw [div_eq_div_iff (ne_of_gt hden2) (ne_of_gt (pow_pos hApos k))]
      ring
    have s5 : 2 * K0 * (xiL A) ^ 2 / A ^ k ≤ 2 * K0 * (xiL A) ^ 2 / A := by
      have hnum2 : 0 ≤ 2 * K0 * (xiL A) ^ 2 := by positivity
      exact div_le_div_of_nonneg_left hnum2 hApos hAkge
    linarith [s1, s2, s3, s4.le, s4.ge, s5]
  have hCeq : C = (k.factorial : ℝ) * 192 * 16 ^ k * K0 * 2 := rfl
  have hstep : (k.factorial : ℝ) * 192 * 16 ^ k * max M0 1 / T ^ (k + 1)
      ≤ (k.factorial : ℝ) * 192 * 16 ^ k * (2 * K0 * (xiL A) ^ 2 / A) := by
    have hfac : 0 ≤ (k.factorial : ℝ) * 192 * 16 ^ k := by positivity
    calc (k.factorial : ℝ) * 192 * 16 ^ k * max M0 1 / T ^ (k + 1)
        = (k.factorial : ℝ) * 192 * 16 ^ k * (max M0 1 / T ^ (k + 1)) := by ring
      _ ≤ (k.factorial : ℝ) * 192 * 16 ^ k * (2 * K0 * (xiL A) ^ 2 / A) :=
          mul_le_mul_of_nonneg_left hkey hfac
  refine le_trans hgd ?_
  refine le_trans hstep ?_
  rw [hCeq]
  have hpos : 1 ≤ 1 + ‖s‖ := by have := norm_nonneg s; linarith
  have hL2n : 0 ≤ (xiL A) ^ 2 := sq_nonneg _
  have hAinv : 0 ≤ (xiL A) ^ 2 / A := div_nonneg hL2n hA0
  have hbase : (k.factorial : ℝ) * 192 * 16 ^ k * (2 * K0 * (xiL A) ^ 2 / A)
      ≤ (k.factorial : ℝ) * 192 * 16 ^ k * (2 * K0) * ((xiL A) ^ 2 / A * (1 + ‖s‖)) := by
    have hfac2 : 0 ≤ (k.factorial : ℝ) * 192 * 16 ^ k * (2 * K0) := by positivity
    have he : (k.factorial : ℝ) * 192 * 16 ^ k * (2 * K0 * (xiL A) ^ 2 / A)
        = (k.factorial : ℝ) * 192 * 16 ^ k * (2 * K0) * ((xiL A) ^ 2 / A) := by ring
    rw [he]
    exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hAinv hpos) hfac2
  refine le_trans hbase ?_
  have heq2 : (k.factorial : ℝ) * 192 * 16 ^ k * (2 * K0) * ((xiL A) ^ 2 / A * (1 + ‖s‖))
      = C * (xiL A) ^ 2 / A * (1 + ‖s‖) := by
    rw [hCeq]; ring
  rw [heq2]

/-- **Hadamard partial fraction at order `k` for the Riemann zeta completion.** (module `Submission.Work.LinnikAreas.FarRepel.xiDerivPF`; declare in `namespace Work.LinnikAreas.FarRepel`; import `Submission.Work.LinnikAreas.DhK.XiAux`, `Submission.Work.LinnikAreas.FarRepel.xiE_annulusBound`, `Submission.Work.LinnikAreas.FarRepel.xiE_goodRadius`.)

`Ξ = DhK.Xi = 1/2 + (1/2)·s(s-1)·Λ₀(s)` is the entire completion of the Riemann zeta function:
entire, `Ξ 0 = 1/2 ≠ 0`, with zeros exactly the non-trivial zeros of `ζ` and the same
multiplicities.  For every `k ≥ 1` and every `s` with `Ξ s ≠ 0`, the closed-ball divisor sums
converge, as `R → ∞`, to the `k`-th derivative of the logarithmic derivative:

`(-1)^k k! · ∑ᶠ_{‖u‖ ≤ R} MeromorphicOn.divisor Ξ (closedBall 0 R) u · (1/(s-u))^{k+1} → ((logDeriv Ξ)^{(k)})(s)`.

PROOF ROUTE (mirror `Work.ZeroFreeTables.P3.CompletedDerivPF_identity`, the `L`-function template,
with `Λ := DhK.Xi` and `L_N N R ↦ xiL R`): the generic engine
`Work.ZeroFreeTables.P3.iteratedDeriv_logDeriv_decompose`,
`...iteratedDeriv_finsum_inv_sub`, `...finsum_divisor_diff_eq`, `...cofactorIteratedDeriv_le` is
already in the import closure of `XiAux`; the count/growth/separation inputs are
`DhK.Xi_zeroCount_L`, `DhK.Xi_growth_L`, `DhK.Xi_zero_ge_delta`.  The one piece that must be
supplied by hand is the truncation error (`CompletedDerivPF_bound`'s analogue): factor
`Xi = (∏_{‖u‖≤T}(z-u)^{d_T u})·g` on the good disc (mirror
`Commons.NumberTheory.Linnik.pf_cofactor_logbound` with `Ξ`, including the `pf_fac_log_lower` and
`pf_P0_log_bound` analogues), bound `log ‖g‖ ≤ M0` with the `xiL`-arithmetic of the template, then
apply `cofactorIteratedDeriv_le`.  For the `R → ∞` passage use
`Work.LinnikAreas.FarRepel.xiE_annulusBound` (annulus bound) and
`Work.LinnikAreas.FarRepel.xiE_goodRadius` (good radius), squeezing with
`xiL_sq_div_self_tendsto_zero`, `xiL_div_self_tendsto_zero`, exactly as in the template.
NOTE: `Submission/Work/LinnikAreas/DhK/xiDerivPF_new.lean` contains a (currently non-building,
because of an unresolved import) version of this very argument — you may READ it for the shape of
the proof and the constants, but you must make this file build on its own without importing
`DhK.xiDerivPF_new`, `DhK.xiE_cofactor_logbound` or `DhK.XiFacLogLower`. -/
theorem xiDerivPF (k : ℕ) (hk : 1 ≤ k) :
    ∀ s : ℂ, Work.LinnikAreas.DhK.Xi s ≠ 0 →
      Filter.Tendsto (fun R : ℝ => ((-1 : ℂ) ^ k * (k.factorial : ℂ)) *
          (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi
              (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (s - u)) ^ (k + 1)))
        Filter.atTop (nhds (iteratedDeriv k (logDeriv Work.LinnikAreas.DhK.Xi) s)) := by
  classical
  intro s hXis
  rw [Work.ZeroFreeTables.P3.logDeriv_eq_div Work.LinnikAreas.DhK.Xi]
  obtain ⟨Ag, hAgpos, hgood⟩ := xiE_goodRadius
  obtain ⟨C2, hC2nn, A2, hbound2⟩ := xiE_truncBound k hk
  obtain ⟨CB, hCBnn, hann⟩ := xiE_annulusBound k hk
  set eR : ℝ → ℝ := fun R => (k.factorial : ℝ) * (CB * xiL R / R)
      + C2 * (xiL R) ^ 2 / R * (1 + ‖s‖) with heRdef
  have hterm1 : Filter.Tendsto (fun R : ℝ => (k.factorial : ℝ) * (CB * xiL R / R))
      Filter.atTop (nhds 0) := by
    have h : Filter.Tendsto (fun R : ℝ => ((k.factorial : ℝ) * CB) * (xiL R / R))
        Filter.atTop (nhds 0) := by
      simpa using xiL_div_self_tendsto_zero.const_mul ((k.factorial : ℝ) * CB)
    refine h.congr' ?_
    filter_upwards with R
    ring
  have hterm2 : Filter.Tendsto (fun R : ℝ => C2 * (xiL R) ^ 2 / R * (1 + ‖s‖))
      Filter.atTop (nhds 0) := by
    have h : Filter.Tendsto (fun R : ℝ => (C2 * (1 + ‖s‖)) * ((xiL R) ^ 2 / R))
        Filter.atTop (nhds 0) := by
      simpa using xiL_sq_div_self_tendsto_zero.const_mul (C2 * (1 + ‖s‖))
    refine h.congr' ?_
    filter_upwards with R
    ring
  have heR0 : Filter.Tendsto eR Filter.atTop (nhds 0) := by
    have h : Filter.Tendsto (fun R : ℝ => (k.factorial : ℝ) * (CB * xiL R / R)
        + C2 * (xiL R) ^ 2 / R * (1 + ‖s‖)) Filter.atTop (nhds 0) := by
      simpa using hterm1.add hterm2
    refine h.congr' ?_
    filter_upwards with R
    simp only [heRdef]
  have hev : ∀ᶠ R : ℝ in Filter.atTop,
      ‖((-1 : ℂ) ^ k * (k.factorial : ℂ)) *
          (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Xi (Metric.closedBall 0 R)) u : ℤ) : ℂ)
            * (1 / (s - u)) ^ (k + 1))
        - iteratedDeriv k (fun z => deriv Xi z / Xi z) s‖ ≤ eR R := by
    filter_upwards [Filter.eventually_ge_atTop (max (max Ag A2) (max 2 (8 * ‖s‖ + 1)))]
      with R hR
    have hRAg : Ag ≤ R := le_trans (le_trans (le_max_left Ag A2) (le_max_left _ _)) hR
    have hRA2 : A2 ≤ R := le_trans (le_trans (le_max_right Ag A2) (le_max_left _ _)) hR
    have hR2 : 2 ≤ R := le_trans (le_trans (le_max_left 2 (8 * ‖s‖ + 1)) (le_max_right _ _)) hR
    have hRs : 8 * ‖s‖ + 1 ≤ R :=
      le_trans (le_trans (le_max_right 2 (8 * ‖s‖ + 1)) (le_max_right _ _)) hR
    have hsR : 8 * ‖s‖ ≤ R := by linarith
    obtain ⟨T, hRT, hT2R, hmargin⟩ := hgood R hRAg
    have hTR : 8 * ‖s‖ ≤ T := by linarith
    have hb2 := hbound2 R hRA2 T hRT hT2R hmargin s hXis hTR
    set SR : ℂ := ∑ᶠ u : ℂ, (((MeromorphicOn.divisor Xi (Metric.closedBall 0 R)) u : ℤ) : ℂ)
        * (1 / (s - u)) ^ (k + 1) with hSR
    set ST : ℂ := ∑ᶠ u : ℂ, (((MeromorphicOn.divisor Xi (Metric.closedBall 0 T)) u : ℤ) : ℂ)
        * (1 / (s - u)) ^ (k + 1) with hST
    set V : ℂ := iteratedDeriv k (fun z => deriv Xi z / Xi z) s with hV
    have hb2' : ‖V - ((-1 : ℂ) ^ k * (k.factorial : ℂ)) * ST‖
        ≤ C2 * (xiL R) ^ 2 / R * (1 + ‖s‖) := by
      simpa only [hST, hV] using hb2
    have hann' : ‖∑ᶠ u : ℂ, ((((MeromorphicOn.divisor Xi (Metric.closedBall 0 T)) u
          - MeromorphicOn.divisor Xi (Metric.closedBall 0 R) u : ℤ)) : ℂ)
          * (1 / (s - u)) ^ (k + 1)‖ ≤ CB * xiL R / R := hann s R T hR2 hRT hsR
    have hnormident : ‖((-1 : ℂ) ^ k * (k.factorial : ℂ)) *
        (∑ᶠ u : ℂ, ((((MeromorphicOn.divisor Xi (Metric.closedBall 0 T)) u
            - MeromorphicOn.divisor Xi (Metric.closedBall 0 R) u : ℤ)) : ℂ)
          * (1 / (s - u)) ^ (k + 1))‖ ≤ (k.factorial : ℝ) * (CB * xiL R / R) := by
      rw [norm_mul]
      have hnorm : ‖((-1 : ℂ) ^ k * (k.factorial : ℂ))‖ = (k.factorial : ℝ) := by
        rw [norm_mul, Complex.norm_natCast]
        simp
      rw [hnorm]
      exact mul_le_mul_of_nonneg_left hann' (by positivity)
    have hsumdiff : (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Xi (Metric.closedBall 0 R)) u : ℤ) : ℂ)
            * (1 / (s - u)) ^ (k + 1))
        - (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Xi (Metric.closedBall 0 T)) u : ℤ) : ℂ)
            * (1 / (s - u)) ^ (k + 1))
        = -(∑ᶠ u : ℂ, ((((MeromorphicOn.divisor Xi (Metric.closedBall 0 T)) u
            - MeromorphicOn.divisor Xi (Metric.closedBall 0 R) u : ℤ)) : ℂ)
            * (1 / (s - u)) ^ (k + 1)) := by
      rw [← neg_sub, Work.ZeroFreeTables.P3.finsum_divisor_diff_eq Xi_meromorphicOn hRT s k]
    have hfirst : ‖((-1 : ℂ) ^ k * (k.factorial : ℂ)) * SR
        - ((-1 : ℂ) ^ k * (k.factorial : ℂ)) * ST‖
        ≤ (k.factorial : ℝ) * (CB * xiL R / R) := by
      have hid : ((-1 : ℂ) ^ k * (k.factorial : ℂ)) * SR
          - ((-1 : ℂ) ^ k * (k.factorial : ℂ)) * ST
          = -(((-1 : ℂ) ^ k * (k.factorial : ℂ)) *
              (∑ᶠ u : ℂ, ((((MeromorphicOn.divisor Xi (Metric.closedBall 0 T)) u
                  - MeromorphicOn.divisor Xi (Metric.closedBall 0 R) u : ℤ)) : ℂ)
                * (1 / (s - u)) ^ (k + 1))) := by
        rw [← mul_sub, hSR, hST, hsumdiff, mul_neg]
      rw [hid, norm_neg]
      exact hnormident
    have hsplit : ((-1 : ℂ) ^ k * (k.factorial : ℂ)) * SR - V
        = (((-1 : ℂ) ^ k * (k.factorial : ℂ)) * SR
            - ((-1 : ℂ) ^ k * (k.factorial : ℂ)) * ST)
          + (((-1 : ℂ) ^ k * (k.factorial : ℂ)) * ST - V) := by ring
    have hsecond : ‖((-1 : ℂ) ^ k * (k.factorial : ℂ)) * ST - V‖
        ≤ C2 * (xiL R) ^ 2 / R * (1 + ‖s‖) := by
      rw [norm_sub_rev]
      exact hb2'
    rw [hsplit]
    refine le_trans (norm_add_le _ _) ?_
    simp only [heRdef]
    linarith [hfirst, hsecond]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero' (Filter.Eventually.of_forall fun R => norm_nonneg _) hev heR0

end Work.LinnikAreas.FarRepel
