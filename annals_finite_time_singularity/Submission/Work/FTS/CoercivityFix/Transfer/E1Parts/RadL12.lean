/-
# The `D_z`-iterates of `L₁₂ f` and their weighted `L²`-integrability

For the transfer defect `E1 α f = D_θΓ(θ)·radA α f (z)` the radial profile `radA α f` is
`−ampA·L₁₂ f + (ampB/c)·L₁₂(Transport f)(0)`, so all its `D_z`-iterates are built from the
`D_z`-iterates of `L₁₂ f`.  This file collects the two facts about those iterates:

* `DzdIter_L12f_eq_neg_Qang` — for `1 ≤ c ≤ 4` and `z > 0`,
  `D_z^c (L₁₂ f)(z) = −Qang f (c−1) z`, where `Qang f j z = ∫_θ K(θ)·D_z^j f (z,θ) dθ` is the
  `j`-th angular moment (differentiating the primitive identity of `QangDiff` in `z`);
* `L12f_DzdIter_sq_w_sq_integrable` — `∫_0^∞ (D_z^c (L₁₂ f)(z))² w(z)² dz < ∞` for `c ≤ 3`,
  from the Hardy inequality `L12f_w_hardy` (`c = 0`) and `Qang_sq_w_sq_integral` (`c ≥ 1`).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.HardyOne
import Submission.Work.FTS.CoercivityFix.Transfer.Profiles
import Submission.Work.FTS.H2.QangDiff
import Submission.Work.FTS.Nonlinear.N4Fields.Qang_sq_w_sq_integral
import Submission.Work.Coercivity.L12f_w_hardy
import Submission.Work.Coercivity.DzRIter_L12f
import Submission.Work.FM.Core2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer.E1Parts

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The `FM`-density of `L₁₂` in terms of the angular moment: `L12dens f z = Qang f 0 z / z`. -/
theorem L12dens_eq_Qang0 (f : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.FM.L12dens Work.Spaces.K f z = Work.Elliptic.Qang f 0 z / z := by
  rw [← Work.FTS.H2.L12dens_eq_FM_K f z, Work.Elliptic.L12dens_eq_Qang_div]

/-- `Qang f 0 z = ∫_θ K θ · f z θ`: the zeroth angular moment is the `K`-average of `f`. -/
theorem Qang_zero_eq_integral (f : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Elliptic.Qang f 0 z = ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * f z θ := by
  have h := Work.Coercivity.DzRIter_L12f_bridge_Qang f 0 z
  simpa using h

/-- **The derivative of `L₁₂ f`** at `z > 0`, in terms of the angular moment: from
`L₁₂ f = ∫_z^∞ L12dens` and `L12dens = Qang f 0 / z`. -/
theorem hasDerivAt_L12f_Qang (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.Nonlin.CoerAdm α f) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (Work.Coercivity.L12f f) (-(Work.Elliptic.Qang f 0 z / z)) z := by
  have hH := hardyHyp_of_coerAdm_le_one α hα hα1 hf
  have hint : IntegrableOn (Work.FM.L12dens Work.Spaces.K f) (Ioi (z / 2)) :=
    hH.hint.mono_set (fun x hx => by
      rw [Set.mem_Ioi] at hx ⊢
      linarith)
  have h := Work.FM.hasDerivAt_L12 (K := Work.Spaces.K) (f := f) (a := z / 2) (ρ := z)
    hint (hH.hcont z hz) (by linarith)
  rw [L12dens_eq_Qang0 f z] at h
  exact h

/-- **The `D_z`-iterates of `L₁₂ f`.**  For `1 ≤ c ≤ 4` and `z > 0`,
`D_z^c (L₁₂ f)(z) = −Qang f (c−1) z`. -/
theorem DzdIter_L12f_eq_neg_Qang (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.Nonlin.CoerAdm α f) :
    ∀ c : ℕ, 1 ≤ c → c ≤ 4 → ∀ z : ℝ, 0 < z →
      Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z
        = - Work.Elliptic.Qang f (c - 1) z := by
  have hsm : Work.FTS.LocData.SmoothQuad f := hf.reg.1
  have hmem : Work.Spaces.HkMem α 4 f :=
    Work.FTS.CoercivityFix.Coer1T.HkMem_four_of_five α hsm hf.reg.2.1
  have hQderiv := (Work.FTS.H2.QangDiff α f hα hα1 hsm hmem).1
  have hQcont := (Work.FTS.H2.QangDiff α f hα hα1 hsm hmem).2
  intro c
  induction c with
  | zero => intro hc; omega
  | succ n ih =>
      intro hc hc4 z hz
      rcases Nat.eq_zero_or_pos n with hn | hn
      · -- `c = 1`
        subst hn
        have hd := hasDerivAt_L12f_Qang α hα hα1 hf hz
        have h1 : Work.Elliptic.DzdIter 1 (Work.Coercivity.L12f f) z
            = z * deriv (Work.Coercivity.L12f f) z := rfl
        rw [h1, hd.deriv]
        have hz0 : z ≠ 0 := ne_of_gt hz
        field_simp
      · -- `c = n + 1 ≥ 2`
        have hn1 : 1 ≤ n := hn
        have hn4 : n ≤ 4 := by omega
        have hn3 : n ≤ 3 := by omega
        have hev : Work.Elliptic.DzdIter n (Work.Coercivity.L12f f)
            =ᶠ[𝓝 z] (fun w => - Work.Elliptic.Qang f (n - 1) w) := by
          filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
          exact ih hn1 hn4 w hw
        have hderiv : deriv (Work.Elliptic.DzdIter n (Work.Coercivity.L12f f)) z
            = - (Work.Elliptic.Qang f n z / z) := by
          have hfun : (fun w : ℝ => - Work.Elliptic.Qang f (n - 1) w)
              = -(Work.Elliptic.Qang f (n - 1)) := by
            funext w; simp
          have hd0 : HasDerivAt (-(Work.Elliptic.Qang f (n - 1)))
              (-(Work.Elliptic.Qang f n z / z)) z := by
            have h := (hQderiv (n - 1) (by omega) z hz).neg
            rwa [Nat.sub_add_cancel hn1] at h
          rw [hev.deriv_eq, hfun, hd0.deriv]
        have h1 : Work.Elliptic.DzdIter (n + 1) (Work.Coercivity.L12f f) z
            = z * deriv (Work.Elliptic.DzdIter n (Work.Coercivity.L12f f)) z := rfl
        rw [h1, hderiv, Nat.succ_sub_one]
        have hz0 : z ≠ 0 := ne_of_gt hz
        field_simp

/-- **Weighted `L²`-integrability of the `D_z`-iterates of `L₁₂ f`** for `c ≤ 3`, i.e.
`∫_0^∞ (D_z^c (L₁₂ f)(z))² w(z)² dz < ∞`. -/
theorem L12f_DzdIter_sq_w_sq_integrable (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.Nonlin.CoerAdm α f) :
    ∀ c : ℕ, c ≤ 3 → IntegrableOn
      (fun z : ℝ => (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2
        * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz := by
  have hsm : Work.FTS.LocData.SmoothQuad f := hf.reg.1
  have hmem : Work.Spaces.HkMem α 4 f :=
    Work.FTS.CoercivityFix.Coer1T.HkMem_four_of_five α hsm hf.reg.2.1
  intro c hc
  rcases Nat.eq_zero_or_pos c with h0 | h0
  · -- `c = 0`: the Hardy inequality for `L₁₂ f`
    subst h0
    have hH := hardyHyp_of_coerAdm_le_one α hα hα1 hf
    have hQ := Work.FTS.Nonlinear.N4Fields.Qang_sq_w_sq_integral (α := α) hα hα1 hsm hmem
      (i := 0) (by norm_num)
    have hgint : IntegrableOn
        (fun z : ℝ => (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * f z θ) ^ 2
          * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz :=
      hQ.1.congr_fun (fun z _ => by
        show Work.Elliptic.Qang f 0 z ^ 2 * Work.Spaces.w z ^ 2 = _
        rw [Qang_zero_eq_integral]) measurableSet_Ici
    have hhardy := (Work.Coercivity.L12f_w_hardy f hH hgint).1
    exact hhardy.congr_fun (fun z _ => by
      show (Work.Coercivity.L12f f z * Work.Spaces.w z) ^ 2
        = (Work.Elliptic.DzdIter 0 (Work.Coercivity.L12f f) z) ^ 2 * (Work.Spaces.w z) ^ 2
      simp only [Work.Elliptic.DzdIter_zero, mul_pow]) measurableSet_Ici
  · -- `c ≥ 1`: the angular moment bounds
    have hid := DzdIter_L12f_eq_neg_Qang α hα hα1 hf c h0 (by omega)
    have hQ := Work.FTS.Nonlinear.N4Fields.Qang_sq_w_sq_integral (α := α) hα hα1 hsm hmem
      (i := c - 1) (by omega)
    have hQioi : IntegrableOn
        (fun z : ℝ => Work.Elliptic.Qang f (c - 1) z ^ 2 * (Work.Spaces.w z) ^ 2)
        (Set.Ioi 0) :=
      hQ.1.congr_set_ae (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))
    have h1 : IntegrableOn
        (fun z : ℝ => (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2
          * (Work.Spaces.w z) ^ 2) (Set.Ioi 0) :=
      hQioi.congr_fun (fun z hz => by
        show Work.Elliptic.Qang f (c - 1) z ^ 2 * Work.Spaces.w z ^ 2
          = (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2 * Work.Spaces.w z ^ 2
        rw [hid z hz]
        ring) measurableSet_Ioi
    exact h1.congr_set_ae (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ))).symm

end Work.FTS.CoercivityFix.Transfer.E1Parts
