import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.PhiStar.RadialWAux.Defs
import Submission.Work.FTS.PhiStar.RadialWAux.radPsi_iteratedDeriv
import Submission.Work.FTS.PhiStar.RadialWAux.Aux2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `RadialWAux.Aux3` — the tail integration by parts and the Euler relation for `Ψ`

* `radPsi_tail_ibp_aux`: the integration-by-parts identity for the tail kernel;
* `radPsi_deriv_value_aux`: the first-order Euler relation `z Ψ' = p Ψ - c`;
* `radPsi_base_aux`: the base case `HasDerivAt Ψ (psiFormal 1 z) z`.
-/
noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.RadialWAux

set_option autoImplicit false

/-! ### C. The tail integration by parts -/

theorem radPsi_tail_ibp_aux {c : ℝ → ℝ} {k : ℕ} {K s z : ℝ} (hk : 1 ≤ k) (hz : 0 < z)
    (hK : 0 ≤ K) (hs : s < -1) (hc : ContDiffOn ℝ k c (Set.Ioi 0))
    (hb : ∀ j : ℕ, j ≤ k → ∀ t : ℝ, 0 < t → |iteratedDeriv j c t| ≤ K) :
    ∫ u in Set.Ioi (1 : ℝ), iteratedDeriv k c (z * u) * u ^ s
      = -(1 / z) * iteratedDeriv (k - 1) c z
        - (s / z) * (∫ u in Set.Ioi (1 : ℝ),
            iteratedDeriv (k - 1) c (z * u) * u ^ (s - 1)) := by
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hk1' : k - 1 + 1 = k := Nat.sub_add_cancel hk
  have hcontk : ContinuousOn (iteratedDeriv k c) (Set.Ioi 0) :=
    continuousOn_iteratedDeriv_of (n := k) hc le_rfl
  have hcontk1 : ContinuousOn (iteratedDeriv (k - 1) c) (Set.Ioi 0) :=
    continuousOn_iteratedDeriv_of (n := k) hc (by omega)
  have hdiffc : ∀ y : ℝ, 0 < y → DifferentiableAt ℝ (iteratedDeriv (k - 1) c) y := by
    intro y hy
    have hEq : Set.EqOn (iteratedDeriv (k - 1) c) (iteratedDerivWithin (k - 1) c (Set.Ioi 0))
        (Set.Ioi 0) := by
      intro t ht
      exact (iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioi 0)
        ((hc.contDiffAt (isOpen_Ioi.mem_nhds ht)).of_le
          (by exact_mod_cast (by omega : k - 1 ≤ k))) ht).symm
    have hd : DifferentiableOn ℝ (iteratedDerivWithin (k - 1) c (Set.Ioi 0)) (Set.Ioi 0) :=
      hc.differentiableOn_iteratedDerivWithin (by exact_mod_cast (by omega : k - 1 < k))
        (uniqueDiffOn_Ioi 0)
    exact (hd.congr hEq).differentiableAt (isOpen_Ioi.mem_nhds hy)
  -- the antiderivative and its derivative
  have hFderiv : ∀ u ∈ Set.Ioi (1 : ℝ),
      HasDerivAt (fun w : ℝ => iteratedDeriv (k - 1) c (z * w) * w ^ s)
        (z * iteratedDeriv k c (z * u) * u ^ s
          + iteratedDeriv (k - 1) c (z * u) * (s * u ^ (s - 1))) u := by
    intro u hu
    have hu0 : 0 < u := lt_trans zero_lt_one hu
    have hzu : 0 < z * u := mul_pos hz hu0
    have hgd : HasDerivAt (iteratedDeriv (k - 1) c) (iteratedDeriv k c (z * u)) (z * u) := by
      simpa only [← iteratedDeriv_succ, hk1'] using (hdiffc (z * u) hzu).hasDerivAt
    have hlin : HasDerivAt (fun y : ℝ => z * y) z u := by
      simpa using (hasDerivAt_id u).const_mul z
    have hcomp : HasDerivAt (fun y : ℝ => iteratedDeriv (k - 1) c (z * y))
        (iteratedDeriv k c (z * u) * z) u := by
      simpa only [Function.comp_def] using hgd.comp u hlin
    have hmul := hcomp.mul (Real.hasDerivAt_rpow_const (x := u) (p := s) (Or.inl (ne_of_gt hu0)))
    have hval : iteratedDeriv k c (z * u) * z * u ^ s
          + iteratedDeriv (k - 1) c (z * u) * (s * u ^ (s - 1))
        = z * iteratedDeriv k c (z * u) * u ^ s
          + iteratedDeriv (k - 1) c (z * u) * (s * u ^ (s - 1)) := by
      ring
    exact hmul.congr_deriv hval
  -- the two summands of the derivative are integrable
  have hcont1 : ContinuousOn (fun u : ℝ => z * iteratedDeriv k c (z * u) * u ^ s)
      (Set.Ioi 1) := by
    have h5 : ContinuousOn (fun u : ℝ => iteratedDeriv k c (z * u)) (Set.Ioi 1) :=
      hcontk.comp ((continuous_const.mul continuous_id).continuousOn)
        (fun u hu => mul_pos hz (lt_trans zero_lt_one hu))
    have h4 : ContinuousOn (fun u : ℝ => u ^ s) (Set.Ioi 1) :=
      ContinuousOn.rpow_const continuousOn_id
        (fun u hu => Or.inl (ne_of_gt (lt_trans zero_lt_one hu)))
    exact ((h5.mul h4).const_mul z).congr (fun u _ => by simp only [Pi.mul_apply]; try ring)
  have hint1 : IntegrableOn (fun u : ℝ => z * iteratedDeriv k c (z * u) * u ^ s) (Set.Ioi 1) := by
    refine integrableOn_Ioi_of_le_rpow (C := z * K) hs (by positivity) hcont1 ?_
    intro u hu
    have hu0 : 0 < u := lt_trans zero_lt_one hu
    rw [abs_mul, abs_mul, abs_of_nonneg hz.le, abs_of_nonneg (Real.rpow_nonneg (le_of_lt hu0) _)]
    have h1 : |iteratedDeriv k c (z * u)| ≤ K := hb k le_rfl (z * u) (mul_pos hz hu0)
    have h2 : (0 : ℝ) ≤ u ^ s := Real.rpow_nonneg (le_of_lt hu0) s
    have h3 : z * |iteratedDeriv k c (z * u)| ≤ z * K := mul_le_mul_of_nonneg_left h1 hz.le
    calc (z * |iteratedDeriv k c (z * u)|) * u ^ s ≤ (z * K) * u ^ s :=
          mul_le_mul_of_nonneg_right h3 h2
      _ = z * K * u ^ s := by ring
  have hcont2 : ContinuousOn
      (fun u : ℝ => iteratedDeriv (k - 1) c (z * u) * (s * u ^ (s - 1))) (Set.Ioi 1) := by
    have h5 : ContinuousOn (fun u : ℝ => iteratedDeriv (k - 1) c (z * u)) (Set.Ioi 1) :=
      hcontk1.comp ((continuous_const.mul continuous_id).continuousOn)
        (fun u hu => mul_pos hz (lt_trans zero_lt_one hu))
    have h4 : ContinuousOn (fun u : ℝ => u ^ (s - 1)) (Set.Ioi 1) :=
      ContinuousOn.rpow_const continuousOn_id
        (fun u hu => Or.inl (ne_of_gt (lt_trans zero_lt_one hu)))
    exact (h5.mul (h4.const_mul s)).congr (fun u _ => by simp only [Pi.mul_apply]; try ring)
  have hint2 : IntegrableOn
      (fun u : ℝ => iteratedDeriv (k - 1) c (z * u) * (s * u ^ (s - 1))) (Set.Ioi 1) := by
    refine integrableOn_Ioi_of_le_rpow (C := K * |s|) (t := s - 1) (by linarith) (by positivity) hcont2 ?_
    intro u hu
    have hu0 : 0 < u := lt_trans zero_lt_one hu
    rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (le_of_lt hu0) _)]
    have h1 : |iteratedDeriv (k - 1) c (z * u)| ≤ K := hb (k - 1) (by omega) (z * u) (mul_pos hz hu0)
    have h2 : 0 ≤ |s| * u ^ (s - 1) := by positivity
    calc |iteratedDeriv (k - 1) c (z * u)| * (|s| * u ^ (s - 1)) ≤ K * (|s| * u ^ (s - 1)) :=
          mul_le_mul_of_nonneg_right h1 h2
      _ = K * |s| * u ^ (s - 1) := by ring
  have hF'int : IntegrableOn (fun u : ℝ => z * iteratedDeriv k c (z * u) * u ^ s
      + iteratedDeriv (k - 1) c (z * u) * (s * u ^ (s - 1))) (Set.Ioi 1) :=
    hint1.add hint2
  -- the limit at `∞`
  have hlim : Tendsto (fun w : ℝ => iteratedDeriv (k - 1) c (z * w) * w ^ s) atTop (𝓝 0) := by
    have h0 : Tendsto (fun w : ℝ => K * w ^ s) atTop (𝓝 0) := by
      have h := tendsto_rpow_neg_atTop (y := -s) (by linarith)
      simpa only [neg_neg, mul_zero] using h.const_mul K
    refine squeeze_zero_norm' ?_ h0
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (le_of_lt hu) _)]
    exact mul_le_mul_of_nonneg_right
      (hb (k - 1) (by omega) (z * u) (mul_pos hz hu)) (Real.rpow_nonneg (le_of_lt hu) _)
  have hFcont : ContinuousWithinAt (fun w : ℝ => iteratedDeriv (k - 1) c (z * w) * w ^ s)
      (Set.Ici (1 : ℝ)) 1 := by
    have hAt : HasDerivAt (fun w : ℝ => iteratedDeriv (k - 1) c (z * w))
        (iteratedDeriv k c (z * 1) * z) 1 := by
      have hgd : HasDerivAt (iteratedDeriv (k - 1) c) (iteratedDeriv k c (z * 1)) (z * 1) := by
        simpa only [← iteratedDeriv_succ, hk1'] using (hdiffc (z * 1) (by simpa using hz)).hasDerivAt
      have hlin : HasDerivAt (fun y : ℝ => z * y) z 1 := by
        simpa using (hasDerivAt_id (1 : ℝ)).const_mul z
      simpa only [Function.comp_def] using hgd.comp 1 hlin
    exact (hAt.continuousAt.mul
      (continuousAt_id.rpow_const (Or.inl (by norm_num : (1 : ℝ) ≠ 0)))).continuousWithinAt
  have hF1 : iteratedDeriv (k - 1) c (z * 1) * (1 : ℝ) ^ s = iteratedDeriv (k - 1) c z := by
    rw [mul_one, Real.one_rpow, mul_one]
  have hFTC := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hFcont hFderiv hF'int hlim
  have hsplit : ∫ u in Set.Ioi (1 : ℝ), (z * iteratedDeriv k c (z * u) * u ^ s
        + iteratedDeriv (k - 1) c (z * u) * (s * u ^ (s - 1)))
      = z * (∫ u in Set.Ioi (1 : ℝ), iteratedDeriv k c (z * u) * u ^ s)
        + s * (∫ u in Set.Ioi (1 : ℝ),
            iteratedDeriv (k - 1) c (z * u) * u ^ (s - 1)) := by
    rw [MeasureTheory.integral_add hint1 hint2]
    congr 1
    · rw [show (fun u : ℝ => z * iteratedDeriv k c (z * u) * u ^ s)
          = fun u : ℝ => z * (iteratedDeriv k c (z * u) * u ^ s) from by funext u; ring,
        MeasureTheory.integral_const_mul]
    · rw [show (fun u : ℝ => iteratedDeriv (k - 1) c (z * u) * (s * u ^ (s - 1)))
          = fun u : ℝ => s * (iteratedDeriv (k - 1) c (z * u) * u ^ (s - 1)) from by
        funext u; ring,
        MeasureTheory.integral_const_mul]
  have hmain : z * (∫ u in Set.Ioi (1 : ℝ), iteratedDeriv k c (z * u) * u ^ s)
      + s * (∫ u in Set.Ioi (1 : ℝ), iteratedDeriv (k - 1) c (z * u) * u ^ (s - 1))
      = -iteratedDeriv (k - 1) c z := by
    rw [← hsplit, hFTC, hF1]
    ring
  field_simp
  linarith [hmain]

/-! ### E′. The formal-derivative machinery for `Ψ` (self-contained) -/

/-- The formal iterated derivatives of `Ψ`: `psiF 0 = Ψ` and
`z · psiF (j+1) z = (p - j) · psiF j z - c^{(j)}(z)`. -/
noncomputable def psiF (α : ℝ) (m : ℕ) (c : ℝ → ℝ) : ℕ → ℝ → ℝ :=
  fun n => Nat.rec (radPsi α m c)
    (fun j (fj : ℝ → ℝ) => fun z => ((radP α m - (j : ℝ)) * fj z - iteratedDeriv j c z) / z) n

lemma psiF_zero (α : ℝ) (m : ℕ) (c : ℝ → ℝ) : psiF α m c 0 = radPsi α m c := rfl

lemma psiF_succ (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (j : ℕ) :
    psiF α m c (j + 1) =
      fun z => ((radP α m - (j : ℝ)) * psiF α m c j z - iteratedDeriv j c z) / z := rfl

lemma psiF_rec {α : ℝ} {m : ℕ} {c : ℝ → ℝ} (j : ℕ) {z : ℝ} (hz : z ≠ 0) :
    z * psiF α m c (j + 1) z
      = (radP α m - (j : ℝ)) * psiF α m c j z - iteratedDeriv j c z := by
  rw [psiF_succ]
  field_simp

lemma psiF_hasDerivAt_of_base {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hc : ContDiffOn ℝ 22 c (Set.Ioi 0))
    (hbase : ∀ z : ℝ, 0 < z → HasDerivAt (radPsi α m c) (psiF α m c 1 z) z) :
    ∀ j : ℕ, j ≤ 21 → ∀ z : ℝ, 0 < z →
      HasDerivAt (psiF α m c j) (psiF α m c (j + 1) z) z := by
  intro j
  induction j with
  | zero =>
    intro _ z hz
    rw [psiF_zero]
    exact hbase z hz
  | succ j ih =>
    intro hj z hz
    show HasDerivAt (psiF α m c (j + 1)) (psiF α m c (j + 1 + 1) z) z
    have hj21 : j ≤ 21 := by omega
    have hdF : HasDerivAt (psiF α m c j) (psiF α m c (j + 1) z) z := ih hj21 z hz
    have hcderiv : HasDerivAt (iteratedDeriv j c) (iteratedDeriv (j + 1) c z) z :=
      radPsiAux_hasDerivAt_iteratedDeriv (hc.contDiffAt (isOpen_Ioi.mem_nhds hz)) (by omega)
    have hnum : HasDerivAt
        (fun w : ℝ => (radP α m - (j : ℝ)) * psiF α m c j w - iteratedDeriv j c w)
        ((radP α m - (j : ℝ)) * psiF α m c (j + 1) z - iteratedDeriv (j + 1) c z) z :=
      (hdF.const_mul (radP α m - (j : ℝ))).sub hcderiv
    have hdiv := hnum.div (hasDerivAt_id z) (ne_of_gt hz)
    have hv : (((radP α m - (j : ℝ)) * psiF α m c (j + 1) z - iteratedDeriv (j + 1) c z) * z
          - ((radP α m - (j : ℝ)) * psiF α m c j z - iteratedDeriv j c z) * 1) / z ^ 2
        = psiF α m c (j + 1 + 1) z := by
      have hrec := psiF_rec (α := α) (m := m) (c := c) j (z := z) (ne_of_gt hz)
      rw [psiF_succ (α := α) (m := m) (c := c) (j + 1)]
      rw [← hrec]
      field_simp
      push_cast
      ring
    rw [psiF_succ (α := α) (m := m) (c := c) j, ← hv]
    exact hdiv

lemma iteratedDeriv_eq_psiF_of_base {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hc : ContDiffOn ℝ 22 c (Set.Ioi 0))
    (hbase : ∀ z : ℝ, 0 < z → HasDerivAt (radPsi α m c) (psiF α m c 1 z) z) :
    ∀ k : ℕ, k ≤ 22 → ∀ z : ℝ, 0 < z →
      iteratedDeriv k (radPsi α m c) z = psiF α m c k z := by
  have hsa := psiF_hasDerivAt_of_base hc hbase
  intro k
  induction k with
  | zero =>
    intro _ z _
    rw [psiF_zero]
    rfl
  | succ j ih =>
    intro hk z hz
    show iteratedDeriv (j + 1) (radPsi α m c) z = psiF α m c (j + 1) z
    have hj21 : j ≤ 21 := by omega
    have hd := hsa j hj21 z hz
    have hev : iteratedDeriv j (radPsi α m c) =ᶠ[𝓝 z] psiF α m c j := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with x hx
      exact ih (by omega) x hx
    rw [iteratedDeriv_succ, hev.deriv_eq, hd.deriv]

/-! ### D. The first-order Euler relation and the base case for `Ψ` -/

theorem radPsi_deriv_value_aux {α : ℝ} (hα : 0 < α) (hα5 : α ≤ 1 / 5) (m : ℕ) (hm : 1 ≤ m)
    {c : ℝ → ℝ} {K : ℝ} (hK : 0 ≤ K) (hc : ContDiffOn ℝ 22 c (Set.Ioi 0))
    (hb : Work.FTS.PhiStar.BddDeriv 22 c K) {z : ℝ} (hz : 0 < z) :
    z * deriv (radPsi α m c) z = radP α m * radPsi α m c z - c z := by
  have hp10 : (10 : ℝ) ≤ radP α m := ten_le_radP hα hα5 hm
  have hp1 : (1 : ℝ) < radP α m := by linarith
  -- the derivative is the rescaled integral with exponent `-p`
  have hderiv : deriv (radPsi α m c) z
      = ∫ u in Set.Ioi (1 : ℝ), iteratedDeriv 1 c (z * u) * u ^ (-(radP α m)) := by
    have h := radPsi_iteratedDeriv hα m hK hc hb 1 (by norm_num)
      (by push_cast; linarith [hp10]) z hz
    rw [iteratedDeriv_one] at h
    rw [h]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with u
    rw [show ((1 : ℕ) : ℝ) - radP α m - 1 = -(radP α m) from by push_cast; ring]
  -- the IBP identity at `k = 1`, `s = -p`
  have hbnd : ∀ j : ℕ, j ≤ 1 → ∀ t : ℝ, 0 < t → |iteratedDeriv j c t| ≤ K := by
    intro j hj t ht
    exact hb j (by omega) t ht
  have hcont1 : ContDiffOn ℝ 1 c (Set.Ioi 0) := hc.of_le (by norm_num)
  have hIBP := radPsi_tail_ibp_aux (c := c) (k := 1) (K := K) (s := -(radP α m)) (z := z)
    le_rfl hz hK (by linarith) hcont1 hbnd
  rw [show (1 : ℕ) - 1 = 0 from rfl, iteratedDeriv_zero] at hIBP
  rw [hderiv, hIBP]
  rw [show radPsi α m c z
      = ∫ u in Set.Ioi (1 : ℝ), c (z * u) * u ^ (-(radP α m) - 1) from rfl]
  field_simp
  ring

/-- The base case for the formal-derivative recursion of `Ψ`. -/
theorem radPsi_base_aux {α : ℝ} (hα : 0 < α) (hα5 : α ≤ 1 / 5) (m : ℕ) (hm : 1 ≤ m)
    {c : ℝ → ℝ} {K : ℝ} (hK : 0 ≤ K) (hc : ContDiffOn ℝ 22 c (Set.Ioi 0))
    (hb : Work.FTS.PhiStar.BddDeriv 22 c K) :
    ∀ z : ℝ, 0 < z → HasDerivAt (radPsi α m c) (psiF α m c 1 z) z := by
  intro z hz
  have hp10 : (10 : ℝ) ≤ radP α m := ten_le_radP hα hα5 hm
  have hode := radPsi_deriv_value_aux hα hα5 m hm hK hc hb hz
  have hker := radPsiAux_kernel_hasDerivAt (c := c) (K := K) (p := radP α m) hc hb
    (k := 0) (by norm_num) (by push_cast; linarith [hp10] : ((0 : ℕ) : ℝ) + 1 < radP α m) hz
  have hdiff : DifferentiableAt ℝ (radPsi α m c) z := by
    have h := hker
    simp only [iteratedDeriv_zero] at h
    rw [show (((0 : ℕ)) : ℝ) - radP α m - 1 = -(radP α m) - 1 from by push_cast; ring] at h
    exact h.differentiableAt
  have hder : HasDerivAt (radPsi α m c) (deriv (radPsi α m c) z) z := hdiff.hasDerivAt
  have hval : psiF α m c 1 z = deriv (radPsi α m c) z := by
    have h1 : psiF α m c 1 z = (radP α m * radPsi α m c z - c z) / z := by
      have hs : psiF α m c (0 + 1) =
          fun w => (radP α m * radPsi α m c w - c w) / w := by
        rw [psiF_succ]
        simp only [psiF_zero, iteratedDeriv_zero, Nat.cast_zero, sub_zero]
      rw [show (0 : ℕ) + 1 = 1 from rfl] at hs
      exact congrFun hs z
    rw [h1, ← hode, div_eq_iff (ne_of_gt hz)]
    ring
  rwa [hval]

end Work.FTS.PhiStar.RadialWAux
