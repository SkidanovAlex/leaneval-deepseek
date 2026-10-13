import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongPersist.L3Rhs.L12fJetUniform
import Submission.Work.FTS.StrongPersist.N6_L12H
import Submission.Work.FTS.StrongPersist.QangDiff6
import Submission.Work.FTS.OpenPkg.QangOpen
import Submission.Work.FTS.OpenPkg.ProdOpen.Tools1d
import Submission.Work.FTS.StrongPersist.L3Rhs.window_le_slot
import Submission.Work.FTS.StrongPersist.L3Aux.L12f_slot_le
import Submission.Work.FTS.H2.CS1D

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-!
# `L12Sup4` — the uniform `z`-jet bound `|D_z^b L₁₂(g)(z)| ≤ C |g|_{ℋ⁴}`, `b ≤ 4`

The sibling `Work.FTS.StrongPersist.L3Rhs.L12fJetUniform` covers `b ≤ 3` in the
open-quadrant class (`SmoothOpen g`, `HkMem α 4 g`, `L12 g 0 = 0`).  The missing case is
`b = 4`, where

  `D_z^4 L₁₂(g)(z) = -Q₃(g)(z)`,  `Q_j(g)(z) = ∫_θ K(θ) D_z^j g(z,θ) dθ`,

and `Q₃` is not directly an `L²`-quantity.  What *is* available in the class (from
`Work.FTS.OpenPkg.QangOpen`) is

* the primitive identity `Q₃(z) - Q₃(z₀) = ∫_{z₀}^{z} Q₄(x)/x dx`,
* the weighted `L²`-bounds `∫_Iz Q_j² w² ≤ (∫_θ K²) |g|²_{ℋ⁴}` for `j ≤ 4`,
* continuity of `Q₃` on `(0,∞)`.

Pick `ξ ∈ [1,2]` minimising `Q₃²` on `[1,2]` (`exists_min_le_mean`): then
`Q₃(ξ)² ≤ ∫_1^2 Q₃² ≤ ∫_Iz Q₃² w²` (as `w ≥ 1` on `[1,2]`), and Cauchy–Schwarz on the
interval between `ξ` and `z` against `1/(x w x) = x/(1+x)²` bounds the primitive.  All the
`L²`/measurability bookkeeping is `Work.FTS.H2.CS1D`.
-/

/-! ## Elementary helpers -/

theorem dzdIter_eq_zop_iter (b : ℕ) (u : ℝ → ℝ) :
    Work.Elliptic.DzdIter b u = Work.Spaces.Zop^[b] u := by
  induction b with
  | zero => rfl
  | succ k ih =>
      rw [Work.Elliptic.DzdIter_succ, Function.iterate_succ_apply', ih]
      rfl

theorem one_div_le_w_div (x : ℝ) (hx : 0 < x) :
    1 / x ≤ Work.Spaces.w x / (1 + x) := by
  rw [Work.Spaces.w]
  have h1x : (0 : ℝ) < 1 + x := by linarith
  have hx2 : (0 : ℝ) < x ^ 2 := by positivity
  rw [le_div_iff₀ h1x, le_div_iff₀ hx2]
  field_simp
  nlinarith [hx]

theorem uIoc_subset_Iz {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Set.uIoc a b ⊆ Work.Spaces.Iz := by
  intro x hx
  rcases le_total a b with hle | hle
  · rw [Set.uIoc_of_le hle] at hx
    exact le_of_lt (lt_trans ha hx.1)
  · rw [Set.uIoc_comm a b, Set.uIoc_of_le hle] at hx
    exact le_of_lt (lt_trans hb hx.1)

theorem uIoc_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {x : ℝ} (hx : x ∈ Set.uIoc a b) :
    0 < x := by
  rcases le_total a b with hle | hle
  · rw [Set.uIoc_of_le hle] at hx
    exact lt_trans ha hx.1
  · rw [Set.uIoc_comm a b, Set.uIoc_of_le hle] at hx
    exact lt_trans hb hx.1

theorem measurableSet_uIoc' (a b : ℝ) : MeasurableSet (Set.uIoc a b) := by
  rw [Set.uIoc]
  exact measurableSet_Ioc

theorem continuousOn_w_sq_Icc : ContinuousOn (fun x : ℝ => (Work.Spaces.w x) ^ 2)
    (Set.Icc (1 : ℝ) 2) := by
  have hfun : (fun x : ℝ => (Work.Spaces.w x) ^ 2)
      = fun x : ℝ => (((1 + x) ^ 2 / x ^ 2) ^ 2) := by
    funext x; rw [Work.Spaces.w]
  rw [hfun]
  apply ContinuousOn.pow
  apply ContinuousOn.div
  · exact (continuousOn_const.add continuousOn_id).pow 2
  · exact continuousOn_id.pow 2
  · intro x hx
    exact pow_ne_zero 2 (ne_of_gt (by linarith [hx.1] : (0 : ℝ) < x))

/-! ## The recurrence `D_z^{k+1} L₁₂(g) = -Q_k(g)` for `k ≤ 3` -/

/-- **The recurrence up to order four.**  For `g` smooth on the open quadrant, `HkMem α 4 g`
and `L₁₂(g)(0) = 0`, the `z ∂_z`-iterates of `L₁₂(g)` are the (negated) angular moments,

  `D_z^{k+1} L₁₂(g)(z) = -Q_k(g)(z)`,  `k ≤ 3`, `z > 0`.

This is the `k ≤ 3` truncation of `Work.FTS.StrongPersist.H6Pair6Aux.L12Rec7`; only the
derivatives `∂_z Q_j = Q_{j+1}/z` for `j ≤ 2` are needed, which is
`Work.FTS.OpenPkg.QangOpen.QangDiff_open`. -/
theorem L12_dzdIter_neg_Qang {α : ℝ} {g : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hO : Work.FTS.EllipticEst.SmoothOpen g) (hmem4 : Work.Spaces.HkMem α 4 g)
    (h0 : Work.Construction.L12 g 0 = 0) :
    ∀ k : ℕ, k ≤ 3 → ∀ z : ℝ, 0 < z →
      Work.Elliptic.DzdIter (k + 1) (fun z => Work.Construction.L12 g z) z
        = - Work.Elliptic.Qang g k z := by
  have hqder : ∀ j : ℕ, j ≤ 2 → ∀ z : ℝ, 0 < z →
      HasDerivAt (fun x => Work.Elliptic.Qang g j x) (Work.Elliptic.Qang g (j + 1) z / z) z :=
    (Work.FTS.OpenPkg.QangOpen.QangDiff_open α g hα hα1 hO hmem4).1
  have hderiv : ∀ z : ℝ, 0 < z →
      HasDerivAt (fun z => Work.Construction.L12 g z) (-(Work.Elliptic.L12dens g z)) z := by
    intro z hz
    have h12 := (Work.FTS.EllipticEst.UopHk.contDiffOn_L12_of_smoothOpen_Hk α 4 g hO hmem4
      (by norm_num : 2 ≤ 4)).2 z hz
    refine h12.congr_deriv ?_
    rw [Work.Elliptic.L12dens_eq_three_Fstar_div]
    ring
  intro k
  induction k with
  | zero =>
      intro _ z hz
      have hd : deriv (fun z => Work.Construction.L12 g z) z = -(Work.Elliptic.L12dens g z) :=
        (hderiv z hz).deriv
      change z * deriv (fun z => Work.Construction.L12 g z) z = - Work.Elliptic.Qang g 0 z
      rw [hd, Work.Elliptic.L12dens_eq_Qang_div, mul_neg, neg_inj,
        mul_div_cancel₀ _ (ne_of_gt hz)]
  | succ n ih =>
      intro hn z hz
      have hev : Work.Elliptic.DzdIter (n + 1) (fun z => Work.Construction.L12 g z)
          =ᶠ[𝓝 z] (fun z' => - Work.Elliptic.Qang g n z') := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact ih (by omega) z' hz'
      have hdv : deriv (Work.Elliptic.DzdIter (n + 1) (fun z => Work.Construction.L12 g z)) z
          = - deriv (fun z' => Work.Elliptic.Qang g n z') z := by
        rw [hev.deriv_eq]
        exact deriv.neg
      change z * deriv (Work.Elliptic.DzdIter (n + 1) (fun z => Work.Construction.L12 g z)) z
          = - Work.Elliptic.Qang g (n + 1) z
      rw [hdv, mul_neg, neg_inj, (hqder n (by omega) z hz).deriv,
        mul_div_cancel₀ _ (ne_of_gt hz)]

/-! ## Cauchy–Schwarz on the interval between the anchor and `z` -/

/-- **The `L²` bound for the fourth angular moment on an interval.**  For `a, b > 0`,

  `|∫_{uIoc a b} Q₄(g)(x)/x dx| ≤ √2 · (∫_θ K²)^{1/2} · |g|_{ℋ⁴}`.

The point is the decomposition `1/x = w(x) · x/(1+x)²`, Cauchy–Schwarz in the form
`CS1D` with `A = |Q₄|·w` (whose square is the radial `ℋ⁴`-slot of `Q₄`) and
`B = 1/(1+x)` (whose square has integral `≤ 2`, `InvOneAddSq`). -/
theorem Qang_four_ioc_integral_le {α : ℝ} {g : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hO : Work.FTS.EllipticEst.SmoothOpen g) (hmem4 : Work.Spaces.HkMem α 4 g)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    |∫ x in Set.uIoc a b, Work.Elliptic.Qang g 4 x / x|
      ≤ Real.sqrt 2 * (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          * Work.Spaces.HkNorm α 4 g) := by
  obtain ⟨hInt4, hBnd4⟩ :=
    Work.FTS.OpenPkg.QangOpen.Qang_sq_w_sq_integral_open (α := α) (g := g) hα hα1 hO hmem4
      (i := 4) (by norm_num)
  have hK2nn : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2 :=
    integral_nonneg fun θ => sq_nonneg _
  have hsub : Set.uIoc a b ⊆ Work.Spaces.Iz := uIoc_subset_Iz ha hb
  have hsub' : Set.uIoc a b ⊆ Set.Ioi (0 : ℝ) := fun x hx => uIoc_pos ha hb hx
  have hμle : volume.restrict (Set.uIoc a b) ≤ volume.restrict Work.Spaces.Iz :=
    MeasureTheory.Measure.restrict_mono hsub le_rfl
  have hmemu : ∀ᵐ x ∂(volume.restrict (Set.uIoc a b)), x ∈ Set.uIoc a b :=
    MeasureTheory.ae_restrict_mem (measurableSet_uIoc' a b)
  -- measurability of `Q₄`
  have hQmeas : AEStronglyMeasurable (fun x => Work.Elliptic.Qang g 4 x)
      (volume.restrict Work.Spaces.Iz) := by
    have h := (Work.Spaces.aesm_of_continuousOn_Qd
      (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2 * Work.Spaces.DzIter 4 g p.1 p.2)
      (Work.FTS.OpenPkg.QangOpen.continuousOn_Ktheta_DzIter_open hO 4)).integral_prod_right'
    simpa only [Work.Elliptic.Qang] using h
  have hAmeas : AEStronglyMeasurable
      (fun x => |Work.Elliptic.Qang g 4 x| * Work.Spaces.w x)
      (volume.restrict (Set.uIoc a b)) := by
    have hw : AEStronglyMeasurable (fun x : ℝ => Work.Spaces.w x)
        (volume.restrict (Set.uIoc a b)) :=
      (by unfold Work.Spaces.w; fun_prop : Measurable fun x : ℝ => Work.Spaces.w x)
        |>.aestronglyMeasurable
    exact MeasureTheory.AEStronglyMeasurable.mul
      (MeasureTheory.AEStronglyMeasurable.mono_measure hQmeas.norm hμle) hw
  have hAint : Integrable (fun x => (|Work.Elliptic.Qang g 4 x| * Work.Spaces.w x) ^ 2)
      (volume.restrict (Set.uIoc a b)) := by
    refine (hInt4.mono_set hsub).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [mul_pow, sq_abs]
  have hAmem : MemLp (fun x => |Work.Elliptic.Qang g 4 x| * Work.Spaces.w x) 2
      (volume.restrict (Set.uIoc a b)) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hAmeas).mpr hAint
  -- measurability and integrability of `B`
  have hBmeas : AEStronglyMeasurable (fun x : ℝ => 1 / (1 + x))
      (volume.restrict (Set.uIoc a b)) :=
    (by fun_prop : Measurable fun x : ℝ => 1 / (1 + x)).aestronglyMeasurable
  have hBint : Integrable (fun x : ℝ => (1 / (1 + x)) ^ 2)
      (volume.restrict (Set.uIoc a b)) :=
    (Work.FTS.H2.InvOneAddSq).1.mono_set hsub'
  have hBmem : MemLp (fun x : ℝ => 1 / (1 + x)) 2 (volume.restrict (Set.uIoc a b)) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hBmeas).mpr hBint
  -- the pointwise domination
  have hdom : ∀ᵐ x ∂(volume.restrict (Set.uIoc a b)),
      |Work.Elliptic.Qang g 4 x / x|
        ≤ (|Work.Elliptic.Qang g 4 x| * Work.Spaces.w x) * (1 / (1 + x)) := by
    filter_upwards [hmemu] with x hx
    have hxpos : 0 < x := uIoc_pos ha hb hx
    have h1 : 1 / x ≤ Work.Spaces.w x / (1 + x) := one_div_le_w_div x hxpos
    rw [abs_div, abs_of_pos hxpos]
    calc |Work.Elliptic.Qang g 4 x| / x
        = |Work.Elliptic.Qang g 4 x| * (1 / x) := by ring
      _ ≤ |Work.Elliptic.Qang g 4 x| * (Work.Spaces.w x / (1 + x)) :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = (|Work.Elliptic.Qang g 4 x| * Work.Spaces.w x) * (1 / (1 + x)) := by ring
  have hA0 : 0 ≤ᵐ[volume.restrict (Set.uIoc a b)]
      (fun x => |Work.Elliptic.Qang g 4 x| * Work.Spaces.w x) :=
    Filter.Eventually.of_forall fun x =>
      mul_nonneg (abs_nonneg _) (by rw [Work.Spaces.w]; positivity)
  have hB0 : 0 ≤ᵐ[volume.restrict (Set.uIoc a b)] (fun x : ℝ => 1 / (1 + x)) := by
    filter_upwards [hmemu] with x hx
    have hxpos : 0 < x := uIoc_pos ha hb hx
    exact div_nonneg zero_le_one (by linarith)
  -- Cauchy–Schwarz
  have hcs := Work.FTS.H2.CS1D (μ := volume.restrict (Set.uIoc a b))
    (g := fun x => Work.Elliptic.Qang g 4 x / x)
    (A := fun x => |Work.Elliptic.Qang g 4 x| * Work.Spaces.w x)
    (B := fun x => 1 / (1 + x)) hAmem hBmem hA0 hB0 hdom
  -- the two `L²`-integrals
  have hA2 : ∫ x, (|Work.Elliptic.Qang g 4 x| * Work.Spaces.w x) ^ 2
        ∂(volume.restrict (Set.uIoc a b))
      ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) * Work.Spaces.HkSq α 4 g := by
    have hcongr : (fun x => (|Work.Elliptic.Qang g 4 x| * Work.Spaces.w x) ^ 2)
        = fun x => (Work.Elliptic.Qang g 4 x) ^ 2 * (Work.Spaces.w x) ^ 2 := by
      funext x; rw [mul_pow, sq_abs]
    rw [hcongr]
    exact (MeasureTheory.setIntegral_mono_set hInt4
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici
        (fun x _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)))
      (Filter.Eventually.of_forall (fun x hx => hsub hx))).trans hBnd4
  have hB2 : ∫ x, (1 / (1 + x)) ^ 2 ∂(volume.restrict (Set.uIoc a b)) ≤ 2 :=
    (MeasureTheory.setIntegral_mono_set (Work.FTS.H2.InvOneAddSq).1
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun x _ => sq_nonneg _))
      (Filter.Eventually.of_forall (fun x hx => uIoc_pos ha hb hx))).trans
      (Work.FTS.H2.InvOneAddSq).2
  -- assemble
  calc |∫ x in Set.uIoc a b, Work.Elliptic.Qang g 4 x / x|
      = |∫ x, Work.Elliptic.Qang g 4 x / x ∂(volume.restrict (Set.uIoc a b))| := rfl
    _ ≤ Real.sqrt (∫ x, (|Work.Elliptic.Qang g 4 x| * Work.Spaces.w x) ^ 2
          ∂(volume.restrict (Set.uIoc a b)))
          * Real.sqrt (∫ x, (1 / (1 + x)) ^ 2 ∂(volume.restrict (Set.uIoc a b))) := hcs
    _ ≤ Real.sqrt ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          * Work.Spaces.HkSq α 4 g) * Real.sqrt 2 :=
        mul_le_mul (Real.sqrt_le_sqrt hA2) (Real.sqrt_le_sqrt hB2)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = Real.sqrt 2 * (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          * Work.Spaces.HkNorm α 4 g) := by
        rw [Real.sqrt_mul hK2nn]
        simp only [Work.Spaces.HkNorm]
        ring

/-! ## The pointwise bound on the third angular moment -/

/-- **`Q₃` is bounded by the `ℋ⁴`-norm**, uniformly in `z > 0`. -/
theorem Qang_three_abs_le {α : ℝ} {g : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hO : Work.FTS.EllipticEst.SmoothOpen g) (hmem4 : Work.Spaces.HkMem α 4 g)
    {z : ℝ} (hz : 0 < z) :
    |Work.Elliptic.Qang g 3 z|
      ≤ 3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          * Work.Spaces.HkNorm α 4 g := by
  obtain ⟨hInt3, hBnd3⟩ :=
    Work.FTS.OpenPkg.QangOpen.Qang_sq_w_sq_integral_open (α := α) (g := g) hα hα1 hO hmem4
      (i := 3) (by norm_num)
  have hK2nn : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2 :=
    integral_nonneg fun θ => sq_nonneg _
  have hXnn : 0 ≤ Work.Spaces.HkNorm α 4 g := Work.Spaces.HkNorm_nonneg α 4 g
  -- continuity of `Q₃`
  have hcont3 : ContinuousOn (fun x => Work.Elliptic.Qang g 3 x) (Set.Ioi 0) :=
    Work.FTS.OpenPkg.QangOpen.continuousOn_Qang_open α g hO hmem4 (j := 3) le_rfl
  have hcont3I : ContinuousOn (fun x => Work.Elliptic.Qang g 3 x) (Set.Icc (1 : ℝ) 2) :=
    hcont3.mono fun x hx => Set.mem_Ioi.mpr (by linarith [hx.1])
  have hcont3U : ContinuousOn (fun x => Work.Elliptic.Qang g 3 x) (Set.uIcc (1 : ℝ) 2) := by
    rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)]
    exact hcont3I
  -- a minimiser of `Q₃²` on `[1,2]`
  obtain ⟨ξ, hξmem, hξmin⟩ := Work.FTS.OpenPkg.ProdOpen.exists_min_le_mean
    (φ := fun x => (Work.Elliptic.Qang g 3 x) ^ 2) (a := 1) (b := 2) (by norm_num)
    (hcont3I.pow 2)
  have hξpos : 0 < ξ := by linarith [hξmem.1]
  -- the anchor value
  have hanchor : (Work.Elliptic.Qang g 3 ξ) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) * Work.Spaces.HkSq α 4 g := by
    have hwin : (Work.Elliptic.Qang g 3 ξ) ^ 2
        ≤ ∫ x in (1 : ℝ)..2, (Work.Elliptic.Qang g 3 x) ^ 2 := by
      have h := hξmin
      rw [show (2 - 1 : ℝ)⁻¹ = 1 by norm_num, one_mul] at h
      exact h
    have hmono : ∫ x in (1 : ℝ)..2, (Work.Elliptic.Qang g 3 x) ^ 2
        ≤ ∫ x in Work.Spaces.Iz, (Work.Elliptic.Qang g 3 x) ^ 2 * (Work.Spaces.w x) ^ 2 := by
      refine le_trans (intervalIntegral.integral_mono_on (by norm_num) ?_ ?_ ?_)
        (Work.Spaces.hardyZ_integral_Ioc_le_integral_Iz (a := 1) (b := 2) (by norm_num)
          (by norm_num) hInt3 (fun x _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)))
      · exact (hcont3U.pow 2).intervalIntegrable
      · refine ContinuousOn.intervalIntegrable ?_
        exact (hcont3U.pow 2).mul (by
          rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)]
          exact continuousOn_w_sq_Icc)
      · intro x hx
        have hw : (1 : ℝ) ≤ (Work.Spaces.w x) ^ 2 := by
          have h1 := Work.FTS.OpenPkg.ProdOpen.one_le_w_of_pos
            (by linarith [hx.1] : (0 : ℝ) < x)
          nlinarith
        nlinarith [sq_nonneg (Work.Elliptic.Qang g 3 x)]
    exact (hwin.trans hmono).trans hBnd3
  -- the primitive identity
  have hprim := Work.FTS.OpenPkg.QangOpen.Qang_primitive_open α g hO hmem4 (j := 3) le_rfl hz hξpos
  -- Cauchy–Schwarz on the interval between `ξ` and `z`
  have hsplit : |∫ x in ξ..z, Work.Elliptic.Qang g 4 x / x|
      = |∫ x in Set.uIoc ξ z, Work.Elliptic.Qang g 4 x / x| := by
    rcases le_total ξ z with hle | hle
    · rw [intervalIntegral.integral_of_le hle, Set.uIoc_of_le hle]
    · rw [intervalIntegral.integral_of_ge hle, Set.uIoc_comm ξ z, Set.uIoc_of_le hle, abs_neg]
  have hcs := Qang_four_ioc_integral_le hα hα1 hO hmem4 (a := ξ) (b := z) hξpos hz
  have hbound : |Work.Elliptic.Qang g 3 z| ≤ Real.sqrt 2
        * (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * Work.Spaces.HkNorm α 4 g)
      + Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
        * Work.Spaces.HkNorm α 4 g := by
    have h1 : Work.Elliptic.Qang g 3 z - Work.Elliptic.Qang g 3 ξ
        = ∫ x in ξ..z, Work.Elliptic.Qang g 4 x / x := hprim
    have h2 : |Work.Elliptic.Qang g 3 z|
        ≤ |Work.Elliptic.Qang g 3 z - Work.Elliptic.Qang g 3 ξ|
          + |Work.Elliptic.Qang g 3 ξ| := by
      have h := abs_add_le (Work.Elliptic.Qang g 3 z - Work.Elliptic.Qang g 3 ξ)
        (Work.Elliptic.Qang g 3 ξ)
      rw [sub_add_cancel] at h
      exact h
    have h3 : |Work.Elliptic.Qang g 3 ξ|
        ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          * Work.Spaces.HkNorm α 4 g := by
      have h := Real.sqrt_le_sqrt hanchor
      rw [Real.sqrt_mul hK2nn] at h
      rw [Real.sqrt_sq_eq_abs] at h
      exact h
    have h4 : |Work.Elliptic.Qang g 3 z - Work.Elliptic.Qang g 3 ξ| ≤ Real.sqrt 2
        * (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * Work.Spaces.HkNorm α 4 g) := by
      rw [h1, hsplit]
      exact hcs
    linarith [h2, h3, h4]
  -- `√2·A + A ≤ 3A`
  have hA0 : 0 ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
      * Work.Spaces.HkNorm α 4 g := mul_nonneg (Real.sqrt_nonneg _) hXnn
  calc |Work.Elliptic.Qang g 3 z|
      ≤ Real.sqrt 2 * (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * Work.Spaces.HkNorm α 4 g)
        + Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          * Work.Spaces.HkNorm α 4 g := hbound
    _ ≤ 3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          * Work.Spaces.HkNorm α 4 g := by
        have h2 : Real.sqrt 2 ≤ 2 := by
          nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
        nlinarith [hA0, h2]

/-! ## The main theorem -/

theorem L12Sup4 : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 6 g →
    Work.Construction.L12 g 0 = 0 →
    ∀ b : ℕ, b ≤ 4 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 g z) z|
        ≤ C * Work.Spaces.HkNorm α 4 g := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.FTS.StrongPersist.L3Rhs.L12fJetUniform
  refine ⟨max C₁ (3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)) + 1,
    by positivity, ?_⟩
  intro α g hα hα1 hO hmem h0 b hb z hz
  have hmem4 : Work.Spaces.HkMem α 4 g :=
    Work.FTS.OpenPkg.HkMem_mono_open hO 4 (by norm_num) hmem
  have hXnn : 0 ≤ Work.Spaces.HkNorm α 4 g := Work.Spaces.HkNorm_nonneg α 4 g
  rcases lt_or_eq_of_le hb with hb4 | hb4
  · -- the case `b ≤ 3`: the mixed jet bound of `L12fJetUniform`
    have hb3 : b ≤ 3 := by omega
    have hjet := hC₁ α hα hα1 g hO hmem4 h0 b hb3 z hz
    calc |Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 g z) z|
        = |Work.Spaces.Zop^[b] (fun z => Work.Construction.L12 g z) z| := by
          rw [dzdIter_eq_zop_iter b (fun z => Work.Construction.L12 g z)]
      _ ≤ C₁ * Work.Spaces.HkNorm α 4 g := hjet
      _ ≤ (max C₁ (3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)) + 1)
            * Work.Spaces.HkNorm α 4 g := by
          refine mul_le_mul_of_nonneg_right ?_ hXnn
          have := le_max_left C₁ (3 * Real.sqrt (∫ θ in Work.Spaces.Iθ,
            Work.Elliptic.Ktheta θ ^ 2))
          linarith
  · -- the case `b = 4`: `D_z^4 L₁₂(g) = -Q₃(g)`
    subst hb4
    have hrec := L12_dzdIter_neg_Qang hα hα1 hO hmem4 h0 3 le_rfl z hz
    have hqq := Qang_three_abs_le hα hα1 hO hmem4 hz
    calc |Work.Elliptic.DzdIter 4 (fun z => Work.Construction.L12 g z) z|
        = |Work.Elliptic.Qang g 3 z| := by
          rw [hrec, abs_neg]
      _ ≤ 3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * Work.Spaces.HkNorm α 4 g := hqq
      _ ≤ (max C₁ (3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)) + 1)
            * Work.Spaces.HkNorm α 4 g := by
          refine mul_le_mul_of_nonneg_right ?_ hXnn
          have := le_max_right C₁ (3 * Real.sqrt (∫ θ in Work.Spaces.Iθ,
            Work.Elliptic.Ktheta θ ^ 2))
          linarith

end Work.FTS.StrongPersist.H6Pair6Aux
