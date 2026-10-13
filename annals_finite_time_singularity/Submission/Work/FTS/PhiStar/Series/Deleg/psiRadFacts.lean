import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.FTS.PhiStar.Radial.Defs
import Submission.Work.FTS.PhiStar.Radial.radGreen_solves
import Submission.Work.FTS.PhiStar.Radial.radGreenIntended
import Submission.Work.FTS.PhiStar.RadialWAux.Defs
import Submission.Work.FTS.PhiStar.RadialWAux.radGreen_eq_rescaled
import Submission.Work.FTS.PhiStar.RadialWAux.radPhi_iteratedDeriv
import Submission.Work.FTS.PhiStar.RadialWAux.radPsi_iteratedDeriv
import Submission.Work.FTS.PhiStar.RadialWAux.radPsi_integral_bound
import Submission.Work.FTS.PhiStar.RadialWAux.radPsi_contDiffOn
import Submission.Work.FTS.PhiStar.Series.radGreenI_differentiableAt
import Submission.Work.FTS.PhiStar.StarDefs
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.PhiStar.Series.Deleg.phiABddDeriv
import Submission.Work.FTS.PhiStar.Series.Deleg.radGreenSolvesNoH0

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series.Deleg

/-!
# `psiRadFacts`

Three radial facts about the mode-wise Green function `Radial.radGreen` used by the `Φ_*` series:

1. the profile `VocabO.phiA α` has bounded derivatives up to order `22` (delegated);
2. a uniform-in-`m` bound `|∂_z^k (radGreen α m c) z| ≤ C K / lam m` for `k ≤ 2`, `0 < z`, for
   sources `c` of class `C^22` with `|c^{(j)}| ≤ K` (this file);
3. the mode-`m` Euler equation solved by `radGreen`, without the extra integrability hypothesis
   of `Radial.radGreen_solves` on `(0,1)` (delegated).

The second fact is proved through the *rescaled* form of the Green function
(`RadialWAux.radGreen_eq_rescaled`): on `(0,∞)`,

  `radGreen α m c = radK α m · (radPhi α m c + radPsi α m c)`,

and the two summands are bounded, together with their first two `z`-derivatives, by
`K/(k + q)` resp. `K/(p - k)` (`radPhi_iteratedDeriv_bound`, `radPsi_integral_bound`).  The only
delicate point is the transfer of the two `iteratedDeriv`s through the sum: it is done with the
eventual-equality and differentiability lemmas proved below, no `C^∞`-regularity of `radPhi`
being needed (`ContDiffOn` of `radPhi` is only available through the currently unbuildable
`radPhi_contDiffOn`, so we avoid it).
-/

open Work.FTS.PhiStar.RadialWAux (radPhi radPsi radP radQ radK radP_pos radQ_pos ten_le_radP
  thirtyfive_le_radQ radP_add_radQ)
open Work.FTS.PhiStar.Radial (radGreen)
open Work.FTS.PhiStar.Series (rgiA rgiB rgiF1 rgiF2 rgiK rgiSn rgiSp rgiD1)

variable {α : ℝ} {m : ℕ} {c : ℝ → ℝ} {K : ℝ}

/-! ### Elementary bounds and integrability of the two source kernels -/

private lemma c_abs_le (hb : BddDeriv 22 c K) : ∀ t : ℝ, 0 < t → |c t| ≤ K := by
  intro t ht
  simpa only [iteratedDeriv_zero] using hb 0 (by norm_num) t ht

private lemma integrableOn_rgiF1 (hα : 0 < α) (hα5 : α ≤ 1 / 5) (hK : 0 ≤ K)
    (hc : ContDiffOn ℝ 22 c (Set.Ioi 0)) (hb : ∀ t : ℝ, 0 < t → |c t| ≤ K) :
    IntegrableOn (rgiF1 α m c) (Set.Ioo 0 1) := by
  have h25 : (25 : ℝ) ≤ radQ α m := by
    rw [show radQ α m = (2 * (m : ℝ) + 5) / α from rfl]
    rw [le_div_iff₀ hα]
    nlinarith [Nat.cast_nonneg (α := ℝ) m, hα5]
  have hq : (1 : ℝ) < radQ α m := by linarith
  refine IntegrableOn.of_bound (measure_Ioo_lt_top) ?_ K ?_
  · exact ((Work.FTS.PhiStar.Series.rgiF1_continuousOn hc.continuousOn).mono
      (fun t ht => ht.1)).aestronglyMeasurable (μ := volume) measurableSet_Ioo
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have ht0 : 0 < t := ht.1
    have ht1 : t < 1 := ht.2
    have he : (0 : ℝ) ≤ (2 * (m : ℝ) + 5) / α - 1 := by
      simpa only [radQ] using sub_nonneg.mpr (le_of_lt hq)
    have hle : t ^ ((2 * (m : ℝ) + 5) / α - 1) ≤ 1 := by
      calc t ^ ((2 * (m : ℝ) + 5) / α - 1) ≤ 1 ^ ((2 * (m : ℝ) + 5) / α - 1) :=
            Real.rpow_le_rpow (le_of_lt ht0) (le_of_lt ht1) he
        _ = 1 := Real.one_rpow _
    rw [Real.norm_eq_abs, Work.FTS.PhiStar.Series.rgiF1, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
    calc |c t| * t ^ ((2 * (m : ℝ) + 5) / α - 1) ≤ K * 1 :=
          mul_le_mul (hb t ht0) hle (Real.rpow_nonneg ht0.le _) hK
      _ = K := mul_one K

private lemma integrableOn_rgiF2 (hα : 0 < α) (hm : 1 ≤ m)
    (hc : ContDiffOn ℝ 22 c (Set.Ioi 0)) (hb : ∀ t : ℝ, 0 < t → |c t| ≤ K) :
    IntegrableOn (rgiF2 α m c) (Set.Ioi 1) := by
  have hmr : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hpos : 0 < 2 * (m : ℝ) / α := div_pos (by linarith) hα
  have hlt : -(2 * (m : ℝ) / α) - 1 < -1 := by linarith
  have hg : IntegrableOn (fun t : ℝ => K * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt hlt zero_lt_one).const_mul K
  have hcont : ContinuousOn (rgiF2 α m c) (Set.Ioi 1) :=
    (Work.FTS.PhiStar.Series.rgiF2_continuousOn hc.continuousOn).mono
      (fun t ht => by simp only [Set.mem_Ioi] at ht ⊢; linarith)
  refine Integrable.mono' hg (hcont.aestronglyMeasurable (μ := volume) measurableSet_Ioi) ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := lt_trans zero_lt_one ht
    rw [Real.norm_eq_abs, Work.FTS.PhiStar.Series.rgiF2, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
    exact mul_le_mul_of_nonneg_right (hb t ht0) (Real.rpow_nonneg ht0.le _)

/-! ### The rescaled form: pointwise identities, derivatives, differentiability -/

/-- The Green function in rescaled form, with the normalisation `rgiK` of the series file. -/
private lemma radGreen_eq_rescaled' (hα : 0 < α) {w : ℝ} (hw : 0 < w) :
    radGreen α m c w = rgiK α m * (radPhi α m c w + radPsi α m c w) := by
  rw [Work.FTS.PhiStar.RadialWAux.radGreen_eq_rescaled hα m c w hw]
  simp only [Work.FTS.PhiStar.RadialWAux.radK, rgiK]

private lemma radPhi_eq_rpow {w : ℝ} (hw : 0 < w) :
    radPhi α m c w = w ^ (rgiSn α m) * rgiA α m c w := by
  simp only [radPhi, rgiA]
  rw [Work.FTS.PhiStar.RadialWAux.integral_zero_one_rpow c (radQ α m - 1) hw]
  have hexp : -((radQ α m - 1) + 1) = rgiSn α m := by
    simp only [radQ, rgiSn]; rw [sub_add_cancel, neg_div]
  rw [hexp]
  congr 1

private lemma radPsi_eq_rpow {w : ℝ} (hw : 0 < w) :
    radPsi α m c w = w ^ (rgiSp α m) * rgiB α m c w := by
  simp only [radPsi, rgiB]
  rw [Work.FTS.PhiStar.RadialWAux.integral_Ioi_one_rpow c (-(radP α m) - 1) hw]
  have hexp : -(-(radP α m) - 1 + 1) = rgiSp α m := by
    simp only [radP, rgiSp]; ring
  rw [hexp]
  congr 1

private lemma deriv_radPhi (hc : ContDiffOn ℝ 22 c (Set.Ioi 0))
    (hF1 : IntegrableOn (rgiF1 α m c) (Set.Ioo 0 1)) {w : ℝ} (hw : 0 < w) :
    deriv (radPhi α m c) w
      = rgiSn α m * w ^ (rgiSn α m - 1) * rgiA α m c w
        + w ^ (rgiSn α m) * rgiF1 α m c w := by
  have hwne : w ≠ 0 := ne_of_gt hw
  have heq : radPhi α m c =ᶠ[𝓝 w] (fun u : ℝ => u ^ (rgiSn α m) * rgiA α m c u) := by
    filter_upwards [isOpen_Ioi.mem_nhds hw] with u hu
    exact radPhi_eq_rpow hu
  rw [Filter.EventuallyEq.deriv_eq heq]
  have hp : HasDerivAt (fun u : ℝ => u ^ (rgiSn α m))
      (rgiSn α m * w ^ (rgiSn α m - 1)) w := Real.hasDerivAt_rpow_const (Or.inl hwne)
  have hA : HasDerivAt (rgiA α m c) (rgiF1 α m c w) w :=
    Work.FTS.PhiStar.Series.rgiA_hasDerivAt hc.continuousOn hF1 w hw
  exact (hp.mul hA).deriv

private lemma deriv_radPsi (hc : ContDiffOn ℝ 22 c (Set.Ioi 0))
    (hF2 : IntegrableOn (rgiF2 α m c) (Set.Ioi 1)) {w : ℝ} (hw : 0 < w) :
    deriv (radPsi α m c) w
      = rgiSp α m * w ^ (rgiSp α m - 1) * rgiB α m c w
        - w ^ (rgiSp α m) * rgiF2 α m c w := by
  have hwne : w ≠ 0 := ne_of_gt hw
  have heq : radPsi α m c =ᶠ[𝓝 w] (fun u : ℝ => u ^ (rgiSp α m) * rgiB α m c u) := by
    filter_upwards [isOpen_Ioi.mem_nhds hw] with u hu
    exact radPsi_eq_rpow hu
  rw [Filter.EventuallyEq.deriv_eq heq]
  have hp : HasDerivAt (fun u : ℝ => u ^ (rgiSp α m))
      (rgiSp α m * w ^ (rgiSp α m - 1)) w := Real.hasDerivAt_rpow_const (Or.inl hwne)
  have hB : HasDerivAt (rgiB α m c) (-(rgiF2 α m c w)) w :=
    Work.FTS.PhiStar.Series.rgiB_hasDerivAt hc.continuousOn hF2 w hw
  have h := (hp.mul hB).deriv
  rw [mul_neg] at h
  rw [sub_eq_add_neg]
  exact h

private lemma rpow_mul_rgiF1 {w : ℝ} (hw : 0 < w) :
    w ^ (rgiSn α m) * rgiF1 α m c w = c w / w := by
  have he : (2 * (m : ℝ) + 5) / α - 1 = -1 - (-(2 * (m : ℝ) + 5) / α) := by ring
  have hf : rgiF1 α m c w = c w * w ^ (-1 - rgiSn α m) := by
    simp only [rgiF1, rgiSn]; rw [he]
  calc w ^ (rgiSn α m) * rgiF1 α m c w
      = w ^ (rgiSn α m) * (c w * w ^ (-1 - rgiSn α m)) := by rw [hf]
    _ = c w * (w ^ (rgiSn α m) * w ^ (-1 - rgiSn α m)) := by ring
    _ = c w * w ^ (-(1 : ℝ)) := by
          have hExp : rgiSn α m + (-1 - rgiSn α m) = -(1 : ℝ) := by ring
          rw [← Real.rpow_add hw, hExp]
    _ = c w / w := by rw [Real.rpow_neg_one, div_eq_mul_inv]

private lemma rpow_mul_rgiF2 {w : ℝ} (hw : 0 < w) :
    w ^ (rgiSp α m) * rgiF2 α m c w = c w / w := by
  have he : -(2 * (m : ℝ) / α) - 1 = -1 - (2 * (m : ℝ) / α) := by ring
  have hf : rgiF2 α m c w = c w * w ^ (-1 - rgiSp α m) := by
    simp only [rgiF2, rgiSp]; rw [he]
  calc w ^ (rgiSp α m) * rgiF2 α m c w
      = w ^ (rgiSp α m) * (c w * w ^ (-1 - rgiSp α m)) := by rw [hf]
    _ = c w * (w ^ (rgiSp α m) * w ^ (-1 - rgiSp α m)) := by ring
    _ = c w * w ^ (-(1 : ℝ)) := by
          have hExp : rgiSp α m + (-1 - rgiSp α m) = -(1 : ℝ) := by ring
          rw [← Real.rpow_add hw, hExp]
    _ = c w / w := by rw [Real.rpow_neg_one, div_eq_mul_inv]

/-- `rgiD1` is the derivative of `rgiK · (radPhi + radPsi)`. -/
private lemma rgiD1_eq (hc : ContDiffOn ℝ 22 c (Set.Ioi 0))
    (hF1 : IntegrableOn (rgiF1 α m c) (Set.Ioo 0 1))
    (hF2 : IntegrableOn (rgiF2 α m c) (Set.Ioi 1)) {w : ℝ} (hw : 0 < w) :
    rgiD1 α m c w
      = rgiK α m * (deriv (radPhi α m c) w + deriv (radPsi α m c) w) := by
  rw [deriv_radPhi hc hF1 hw, deriv_radPsi hc hF2 hw, rpow_mul_rgiF1 hw, rpow_mul_rgiF2 hw]
  simp only [rgiD1]
  ring

private lemma differentiableAt_radPhi (hc : ContDiffOn ℝ 22 c (Set.Ioi 0))
    (hF1 : IntegrableOn (rgiF1 α m c) (Set.Ioo 0 1)) {w : ℝ} (hw : 0 < w) :
    DifferentiableAt ℝ (radPhi α m c) w := by
  have hwne : w ≠ 0 := ne_of_gt hw
  have heq : radPhi α m c =ᶠ[𝓝 w] (fun u : ℝ => u ^ (rgiSn α m) * rgiA α m c u) := by
    filter_upwards [isOpen_Ioi.mem_nhds hw] with u hu
    exact radPhi_eq_rpow hu
  refine (heq.differentiableAt_iff).mpr ?_
  exact ((Real.hasDerivAt_rpow_const (p := rgiSn α m) (Or.inl hwne)).differentiableAt).mul
    (Work.FTS.PhiStar.Series.rgiA_hasDerivAt hc.continuousOn hF1 w hw).differentiableAt

private lemma differentiableAt_radPsi (hc : ContDiffOn ℝ 22 c (Set.Ioi 0))
    (hF2 : IntegrableOn (rgiF2 α m c) (Set.Ioi 1)) {w : ℝ} (hw : 0 < w) :
    DifferentiableAt ℝ (radPsi α m c) w := by
  have hwne : w ≠ 0 := ne_of_gt hw
  have heq : radPsi α m c =ᶠ[𝓝 w] (fun u : ℝ => u ^ (rgiSp α m) * rgiB α m c u) := by
    filter_upwards [isOpen_Ioi.mem_nhds hw] with u hu
    exact radPsi_eq_rpow hu
  refine (heq.differentiableAt_iff).mpr ?_
  exact ((Real.hasDerivAt_rpow_const (p := rgiSp α m) (Or.inl hwne)).differentiableAt).mul
    (Work.FTS.PhiStar.Series.rgiB_hasDerivAt hc.continuousOn hF2 w hw).differentiableAt

private lemma differentiableAt_deriv_radPhi (hc : ContDiffOn ℝ 22 c (Set.Ioi 0))
    (hF1 : IntegrableOn (rgiF1 α m c) (Set.Ioo 0 1)) {w : ℝ} (hw : 0 < w) :
    DifferentiableAt ℝ (deriv (radPhi α m c)) w := by
  have hwne : w ≠ 0 := ne_of_gt hw
  have hd1 : deriv (radPhi α m c) =ᶠ[𝓝 w] (fun u : ℝ => rgiSn α m * u ^ (rgiSn α m - 1)
        * rgiA α m c u + u ^ (rgiSn α m) * rgiF1 α m c u) := by
    filter_upwards [isOpen_Ioi.mem_nhds hw] with u hu
    exact deriv_radPhi hc hF1 hu
  refine (hd1.differentiableAt_iff).mpr ?_
  have h1 : DifferentiableAt ℝ (fun u : ℝ => rgiSn α m * u ^ (rgiSn α m - 1)
      * rgiA α m c u) w :=
    (((Real.hasDerivAt_rpow_const (p := rgiSn α m - 1) (Or.inl hwne)).const_mul
      (rgiSn α m)).mul
      (Work.FTS.PhiStar.Series.rgiA_hasDerivAt hc.continuousOn hF1 w hw)).differentiableAt
  have h2 : DifferentiableAt ℝ (fun u : ℝ => u ^ (rgiSn α m) * rgiF1 α m c u) w :=
    (Real.hasDerivAt_rpow_const (p := rgiSn α m) (Or.inl hwne)).differentiableAt.mul (by
      have hc' : DifferentiableAt ℝ c w :=
        (hc.contDiffAt (isOpen_Ioi.mem_nhds hw)).differentiableAt (by norm_num)
      have h3 : DifferentiableAt ℝ (fun u : ℝ => u ^ ((2 * (m : ℝ) + 5) / α - 1)) w :=
        (Real.hasDerivAt_rpow_const (p := (2 * (m : ℝ) + 5) / α - 1)
          (Or.inl hwne)).differentiableAt
      exact hc'.mul h3)
  exact h1.add h2

private lemma differentiableAt_deriv_radPsi (hc : ContDiffOn ℝ 22 c (Set.Ioi 0))
    (hF2 : IntegrableOn (rgiF2 α m c) (Set.Ioi 1)) {w : ℝ} (hw : 0 < w) :
    DifferentiableAt ℝ (deriv (radPsi α m c)) w := by
  have hwne : w ≠ 0 := ne_of_gt hw
  have hd1 : deriv (radPsi α m c) =ᶠ[𝓝 w] (fun u : ℝ => rgiSp α m * u ^ (rgiSp α m - 1)
        * rgiB α m c u - u ^ (rgiSp α m) * rgiF2 α m c u) := by
    filter_upwards [isOpen_Ioi.mem_nhds hw] with u hu
    exact deriv_radPsi hc hF2 hu
  refine (hd1.differentiableAt_iff).mpr ?_
  have h1 : DifferentiableAt ℝ (fun u : ℝ => rgiSp α m * u ^ (rgiSp α m - 1)
      * rgiB α m c u) w :=
    (((Real.hasDerivAt_rpow_const (p := rgiSp α m - 1) (Or.inl hwne)).const_mul
      (rgiSp α m)).mul
      (Work.FTS.PhiStar.Series.rgiB_hasDerivAt hc.continuousOn hF2 w hw)).differentiableAt
  have h2 : DifferentiableAt ℝ (fun u : ℝ => u ^ (rgiSp α m) * rgiF2 α m c u) w :=
    (Real.hasDerivAt_rpow_const (p := rgiSp α m) (Or.inl hwne)).differentiableAt.mul (by
      have hc' : DifferentiableAt ℝ c w :=
        (hc.contDiffAt (isOpen_Ioi.mem_nhds hw)).differentiableAt (by norm_num)
      have h3 : DifferentiableAt ℝ (fun u : ℝ => u ^ (-(2 * (m : ℝ) / α) - 1)) w :=
        (Real.hasDerivAt_rpow_const (p := -(2 * (m : ℝ) / α) - 1)
          (Or.inl hwne)).differentiableAt
      exact hc'.mul h3)
  exact h1.sub h2

/-! ### Linearity of `iteratedDeriv` up to order `2` -/

/-- `iteratedDeriv` is additive up to order `2` on the open set `(0,∞)`, where both functions and
their derivatives are differentiable. -/
private lemma iteratedDeriv_add_le_two {f g : ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hf : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ f x)
    (hg : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ g x)
    (hf' : DifferentiableAt ℝ (deriv f) z) (hg' : DifferentiableAt ℝ (deriv g) z)
    {n : ℕ} (hn : n ≤ 2) :
    iteratedDeriv n (fun x : ℝ => f x + g x) z = iteratedDeriv n f z + iteratedDeriv n g z := by
  interval_cases n
  · simp only [iteratedDeriv_zero]
  · rw [iteratedDeriv_one, iteratedDeriv_one, iteratedDeriv_one]
    exact deriv_add (hf z hz) (hg z hz)
  · have e2 : ∀ X : ℝ → ℝ, iteratedDeriv 2 X = deriv (deriv X) := fun X => by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    rw [e2 (fun x : ℝ => f x + g x), e2 f, e2 g]
    have hder : deriv (fun x : ℝ => f x + g x) =ᶠ[𝓝 z] (deriv f + deriv g) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with x hx
      rw [show deriv (fun y : ℝ => f y + g y) x = deriv (f + g) x from rfl]
      exact deriv_add (hf x hx) (hg x hx)
    rw [Filter.EventuallyEq.deriv_eq hder]
    exact deriv_add hf' hg'

/-! ### The second conjunct -/

private theorem radGreen_iteratedDeriv_le (hα : 0 < α) (hα5 : α ≤ 1 / 5) (hm : 1 ≤ m)
    (hK : 0 ≤ K) (hc : ContDiffOn ℝ 22 c (Set.Ioi 0)) (hb : BddDeriv 22 c K)
    (k : ℕ) (hk : k ≤ 2) (z : ℝ) (hz : 0 < z) :
    |iteratedDeriv k (radGreen α m c) z| ≤ 2 * K / Work.FTS.PhiStar.Gegenbauer.lam m := by
  have hb0 : ∀ t : ℝ, 0 < t → |c t| ≤ K := c_abs_le hb
  have hF1 := integrableOn_rgiF1 (α := α) (m := m) (c := c) (K := K) hα hα5 hK hc hb0
  have hF2 := integrableOn_rgiF2 (α := α) (m := m) (c := c) (K := K) hα hm hc hb0
  -- the two indicial exponents and their bounds
  have hqpos : 0 < radQ α m := radQ_pos hα m
  have hp10 : 10 ≤ radP α m := ten_le_radP hα hα5 hm
  have hkp : (k : ℝ) < radP α m := by
    have : (k : ℝ) ≤ 2 := by exact_mod_cast hk
    linarith
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hkq : 0 < (k : ℝ) + radQ α m := by linarith
  have hpk : 0 < radP α m - (k : ℝ) := by
    have h2 : (k : ℝ) ≤ 2 := by exact_mod_cast hk
    linarith
  have hk22 : k ≤ 22 := by omega
  -- the identity `iteratedDeriv k (radGreen) = rgiK * (iteratedDeriv k radPhi + ...)`
  have hres : iteratedDeriv k (radGreen α m c) z
      = rgiK α m * (iteratedDeriv k (radPhi α m c) z
          + iteratedDeriv k (radPsi α m c) z) := by
    have hEq : radGreen α m c =ᶠ[𝓝 z]
        (fun w => rgiK α m * (radPhi α m c w + radPsi α m c w)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
      exact radGreen_eq_rescaled' (m := m) (c := c) hα hw
    rw [Filter.EventuallyEq.iteratedDeriv_eq k hEq,
      show iteratedDeriv k (fun w => rgiK α m * (radPhi α m c w + radPsi α m c w)) z
          = rgiK α m * iteratedDeriv k (fun w => radPhi α m c w + radPsi α m c w) z from
        iteratedDeriv_const_mul_field (rgiK α m)
          (fun w => radPhi α m c w + radPsi α m c w)]
    congr 1
    exact iteratedDeriv_add_le_two hz
      (fun x hx => differentiableAt_radPhi hc hF1 hx)
      (fun x hx => differentiableAt_radPsi hc hF2 hx)
      (differentiableAt_deriv_radPhi hc hF1 hz) (differentiableAt_deriv_radPsi hc hF2 hz) hk
  -- the two integral bounds
  have hΦ : |iteratedDeriv k (radPhi α m c) z| ≤ K / ((k : ℝ) + radQ α m) :=
    Work.FTS.PhiStar.RadialWAux.radPhi_iteratedDeriv_bound hα m hK hc hb k hk22 z hz
  have hΨ : |iteratedDeriv k (radPsi α m c) z| ≤ K / (radP α m - (k : ℝ)) := by
    rw [Work.FTS.PhiStar.RadialWAux.radPsi_iteratedDeriv hα m hK hc hb k hk22 hkp z hz]
    exact Work.FTS.PhiStar.RadialWAux.radPsi_integral_bound hα m hK hb k hk22 hkp z hz
  -- positivity of the normalisation
  have hKr : 0 < rgiK α m := by simp only [rgiK]; positivity
  -- the algebraic form of the product
  have h1c : (k : ℝ) + radQ α m = ((k : ℝ) * α + 2 * (m : ℝ) + 5) / α := by
    simp only [radQ]
    field_simp <;> ring
  have h2c : radP α m - (k : ℝ) = (2 * (m : ℝ) - (k : ℝ) * α) / α := by
    simp only [radP]
    field_simp <;> ring
  have hE : rgiK α m * (K / ((k : ℝ) + radQ α m) + K / (radP α m - (k : ℝ)))
      = K / (α ^ 2 * ((k : ℝ) + radQ α m) * (radP α m - (k : ℝ))) := by
    have hαne : α ≠ 0 := ne_of_gt hα
    have h45 : 4 * (m : ℝ) + 5 ≠ 0 := by positivity
    have hx : (k : ℝ) + radQ α m ≠ 0 := ne_of_gt hkq
    have hy : radP α m - (k : ℝ) ≠ 0 := ne_of_gt hpk
    have hd : α ^ 2 * ((k : ℝ) + radQ α m) * (radP α m - (k : ℝ)) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hαne) hx) hy
    have hαpq : α * (radP α m + radQ α m) = 4 * (m : ℝ) + 5 := by
      rw [radP_add_radQ hα m]
      field_simp <;> ring
    simp only [rgiK]
    field_simp [hαne, h45, hx, hy, hd] <;> linear_combination (K : ℝ) * hαpq
  -- the numerical inequality
  have hden : (4 / 5) * Work.FTS.PhiStar.Gegenbauer.lam m
      ≤ α ^ 2 * ((k : ℝ) + radQ α m) * (radP α m - (k : ℝ)) := by
    have hmr : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hk2 : (k : ℝ) ≤ 2 := by exact_mod_cast hk
    have hka : (k : ℝ) * α ≤ (1 / 5) * (2 * (m : ℝ)) := by
      have h1 : (k : ℝ) * α ≤ 2 * α := mul_le_mul_of_nonneg_right hk2 (le_of_lt hα)
      have h2 : 2 * α ≤ 2 / 5 := by linarith
      have h5 : (2 : ℝ) / 5 ≤ (1 / 5) * (2 * (m : ℝ)) := by linarith
      linarith
    have h1 : (4 / 5) * (2 * (m : ℝ)) ≤ 2 * (m : ℝ) - (k : ℝ) * α := by linarith
    have h2 : 2 * (m : ℝ) + 5 ≤ (k : ℝ) * α + 2 * (m : ℝ) + 5 := by
      have hnn : (0 : ℝ) ≤ (k : ℝ) * α := mul_nonneg hk0 (le_of_lt hα)
      linarith
    have h3 : (0 : ℝ) ≤ (4 / 5) * (2 * (m : ℝ)) := by linarith
    have h4 : (0 : ℝ) ≤ (k : ℝ) * α + 2 * (m : ℝ) + 5 := by linarith
    have hprod : (4 / 5) * (2 * (m : ℝ) * (2 * (m : ℝ) + 5))
        ≤ ((k : ℝ) * α + 2 * (m : ℝ) + 5) * (2 * (m : ℝ) - (k : ℝ) * α) :=
      calc (4 / 5) * (2 * (m : ℝ) * (2 * (m : ℝ) + 5))
          = (2 * (m : ℝ) + 5) * ((4 / 5) * (2 * (m : ℝ))) := by ring
        _ ≤ ((k : ℝ) * α + 2 * (m : ℝ) + 5) * (2 * (m : ℝ) - (k : ℝ) * α) :=
            mul_le_mul h2 h1 h3 h4
    have hXeq : α ^ 2 * ((k : ℝ) + radQ α m) * (radP α m - (k : ℝ))
        = ((k : ℝ) * α + 2 * (m : ℝ) + 5) * (2 * (m : ℝ) - (k : ℝ) * α) := by
      rw [h1c, h2c]
      field_simp <;> ring
    rw [hXeq]
    simpa only [Work.FTS.PhiStar.Gegenbauer.lam] using hprod
  have hXpos : 0 < α ^ 2 * ((k : ℝ) + radQ α m) * (radP α m - (k : ℝ)) :=
    mul_pos (mul_pos (pow_pos hα 2) hkq) hpk
  have hLpos : 0 < Work.FTS.PhiStar.Gegenbauer.lam m := by
    simp only [Work.FTS.PhiStar.Gegenbauer.lam]
    have hmr : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have h1 : (0 : ℝ) < 2 * (m : ℝ) := by linarith
    have h2 : (0 : ℝ) < 2 * (m : ℝ) + 5 := by linarith
    exact mul_pos h1 h2
  have hfinal : K / (α ^ 2 * ((k : ℝ) + radQ α m) * (radP α m - (k : ℝ)))
      ≤ 2 * K / Work.FTS.PhiStar.Gegenbauer.lam m := by
    have hLne : Work.FTS.PhiStar.Gegenbauer.lam m ≠ 0 := ne_of_gt hLpos
    have h45 : 0 < (4 / 5) * Work.FTS.PhiStar.Gegenbauer.lam m := by linarith
    calc K / (α ^ 2 * ((k : ℝ) + radQ α m) * (radP α m - (k : ℝ)))
        ≤ K / ((4 / 5) * Work.FTS.PhiStar.Gegenbauer.lam m) :=
          div_le_div_of_nonneg_left hK h45 hden
      _ = (5 / 4) * (K / Work.FTS.PhiStar.Gegenbauer.lam m) := by
          field_simp <;> ring
      _ ≤ 2 * (K / Work.FTS.PhiStar.Gegenbauer.lam m) := by
          linarith [div_nonneg hK (le_of_lt hLpos)]
      _ = 2 * K / Work.FTS.PhiStar.Gegenbauer.lam m := by ring
  rw [hres]
  calc |rgiK α m * (iteratedDeriv k (radPhi α m c) z
          + iteratedDeriv k (radPsi α m c) z)|
      = rgiK α m * |iteratedDeriv k (radPhi α m c) z
          + iteratedDeriv k (radPsi α m c) z| := by
        rw [abs_mul, abs_of_nonneg (le_of_lt hKr)]
    _ ≤ rgiK α m * (|iteratedDeriv k (radPhi α m c) z|
          + |iteratedDeriv k (radPsi α m c) z|) :=
        mul_le_mul_of_nonneg_left (abs_add_le _ _) (le_of_lt hKr)
    _ ≤ rgiK α m * (K / ((k : ℝ) + radQ α m) + K / (radP α m - (k : ℝ))) :=
        mul_le_mul_of_nonneg_left (add_le_add hΦ hΨ) (le_of_lt hKr)
    _ = K / (α ^ 2 * ((k : ℝ) + radQ α m) * (radP α m - (k : ℝ))) := hE
    _ ≤ 2 * K / Work.FTS.PhiStar.Gegenbauer.lam m := hfinal

theorem psiRadFacts (α : ℝ) (hα : 0 < α) (hα5 : α ≤ 1 / 5) :
    (∃ K : ℝ, 0 ≤ K ∧ Work.FTS.PhiStar.BddDeriv 22 (Work.FTS.VocabO.phiA α) K) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (c : ℝ → ℝ) (K : ℝ), 0 ≤ K → 1 ≤ m →
        ContDiffOn ℝ 22 c (Set.Ioi 0) → Work.FTS.PhiStar.BddDeriv 22 c K →
          ∀ k : ℕ, k ≤ 2 → ∀ z : ℝ, 0 < z →
            |iteratedDeriv k (Work.FTS.PhiStar.Radial.radGreen α m c) z|
              ≤ C * K / Work.FTS.PhiStar.Gegenbauer.lam m) ∧
    (∀ (m : ℕ) (c : ℝ → ℝ), ContinuousOn c (Set.Ioi 0) →
        MeasureTheory.IntegrableOn (fun t => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
          (Set.Ioo 0 1) →
        MeasureTheory.IntegrableOn (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1))
          (Set.Ioi 1) →
        ∀ z, 0 < z →
          -α ^ 2 * z ^ 2 * deriv (deriv (Work.FTS.PhiStar.Radial.radGreen α m c)) z
            - α * (5 + α) * z * deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z
            + Work.FTS.PhiStar.Radial.lamR m * Work.FTS.PhiStar.Radial.radGreen α m c z
            = c z) := by
  refine ⟨phiABddDeriv α hα hα5, ⟨2, by norm_num, ?_⟩, ?_⟩
  · intro m c K hK hm hc hb k hk z hz
    exact radGreen_iteratedDeriv_le hα hα5 hm hK hc hb k hk z hz
  · exact fun m c hc h0 hinf => radGreenSolvesNoH0 α hα m hc h0 hinf

end Work.FTS.PhiStar.Series.Deleg
