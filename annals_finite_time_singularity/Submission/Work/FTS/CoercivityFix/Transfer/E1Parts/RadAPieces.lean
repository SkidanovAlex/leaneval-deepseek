/-
# `E1Parts/RadAPieces` — the pieces of the radial profile `radA`

Facts about `radA α f z = −ampA α z·L₁₂ f(z) + (ampB α z/c α)·L₁₂(Transport f)(0)` and the
explicit expressions used in `RadA.lean`:

* `L12f_DzdIter_sq_w_sq_integrable_Ioi` — `∫ (D_z^c (L₁₂ f))²w² < ∞` on `(0,∞)` for `c ≤ 3`;
* `ampB_DzdIter_sq_w_sq_integrable_Ioi` — `∫ (D_z^c (ampB α))²w² < ∞` for `c ≤ 4`;
* `Qang_sq_w_sq_integrable_Ioi` — `∫ (Qang f i)²w² < ∞` for `i ≤ 4`;
* `differentiableOn_DzdIter_L12f` — the `D_z`-iterates of `L₁₂ f` are differentiable up to
  order `2`;
* `dzdIter_L_as_if` — the conditional form of `D_z^c (L₁₂ f)`;
* `Efun`, `Maj` — the explicit expression equal to the integrand on `(0,∞)` and its majorant.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.CoercivityFix.Transfer.Profiles
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.RadL12
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_coeff_bound
import Submission.Work.FTS.CoercivityFix.Transfer.L12f_contDiffOn
import Submission.Work.FTS.H2.QangDiff
import Submission.Work.FTS.Nonlinear.N4Fields.Qang_sq_w_sq_integral
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.L12Aux
import Submission.Work.Spaces.c_bounds

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

/-- `(D_z^c (L₁₂ f))²w² ∈ L¹((0,∞))` for `c ≤ 3`. -/
theorem L12f_DzdIter_sq_w_sq_integrable_Ioi (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    {f : ℝ → ℝ → ℝ} (hf : Work.FTS.Nonlin.CoerAdm α f) :
    ∀ c : ℕ, c ≤ 3 → IntegrableOn
      (fun z : ℝ => (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2
        * (Work.Spaces.w z) ^ 2) (Set.Ioi (0 : ℝ)) := by
  intro c hc
  exact (L12f_DzdIter_sq_w_sq_integrable α hα hα1 hf c hc).congr_set_ae
    (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))

/-- `(D_z^c (ampB α))²w² ∈ L¹((0,∞))` for `c ≤ 4`. -/
theorem ampB_DzdIter_sq_w_sq_integrable_Ioi (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    {c : ℕ} (hc : c ≤ 4) : IntegrableOn
      (fun z : ℝ => (Work.Elliptic.DzdIter c (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
        * (Work.Spaces.w z) ^ 2) (Set.Ioi (0 : ℝ)) :=
  ((Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_coeff_bound α hα hα1).2 c hc).congr_set_ae
    (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))

/-- `(Qang f i)²w² ∈ L¹((0,∞))` for `i ≤ 4`. -/
theorem Qang_sq_w_sq_integrable_Ioi (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad f) (hmem : Work.Spaces.HkMem α 4 f)
    {i : ℕ} (hi : i ≤ 4) : IntegrableOn
      (fun z : ℝ => (Work.Elliptic.Qang f i z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (Set.Ioi (0 : ℝ)) :=
  ((Work.FTS.Nonlinear.N4Fields.Qang_sq_w_sq_integral (α := α) hα hα1 hsm hmem hi).1).congr_set_ae
    (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))

/-- The `D_z`-iterates of `L₁₂ f` are differentiable on `(0,∞)` up to order `2`. -/
theorem differentiableOn_DzdIter_L12f (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    {f : ℝ → ℝ → ℝ} (hf : Work.FTS.Nonlin.CoerAdm α f) {b : ℕ} (hb : b ≤ 2) :
    DifferentiableOn ℝ (Work.Elliptic.DzdIter b (Work.Coercivity.L12f f))
      (Set.Ioi (0 : ℝ)) := by
  have hsm : Work.FTS.LocData.SmoothQuad f := hf.reg.1
  have hmem : Work.Spaces.HkMem α 4 f :=
    Work.FTS.CoercivityFix.Coer1T.HkMem_four_of_five α hsm hf.reg.2.1
  intro z hz
  rcases Nat.eq_zero_or_pos b with h0 | h0
  · subst h0
    exact (((Work.FTS.CoercivityFix.Transfer.L12f_contDiffOn α hα hα1 f hsm hmem).differentiableOn
      (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds hz)).differentiableWithinAt
  · have hq : HasDerivAt (Work.Elliptic.Qang f (b - 1))
        (Work.Elliptic.Qang f b z / z) z := by
      have h := (Work.FTS.H2.QangDiff α f hα hα1 hsm hmem).1 (b - 1) (by omega) z hz
      rwa [Nat.sub_add_cancel h0] at h
    have hev : Work.Elliptic.DzdIter b (Work.Coercivity.L12f f)
        =ᶠ[𝓝 z] (fun w => - Work.Elliptic.Qang f (b - 1) w) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
      exact DzdIter_L12f_eq_neg_Qang α hα hα1 hf b h0 (by omega) w hw
    exact (hq.neg.differentiableAt.congr_of_eventuallyEq hev).differentiableWithinAt

/-- The conditional form of `D_z^c (L₁₂ f)` on `(0,∞)`. -/
theorem dzdIter_L_as_if (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.Nonlin.CoerAdm α f) {c : ℕ} (hc : c ≤ 4) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z
        = if c = 0 then Work.Coercivity.L12f f z else - Work.Elliptic.Qang f (c - 1) z := by
  intro z hz
  by_cases h : c = 0
  · subst h; simp
  · rw [if_neg h]
    exact DzdIter_L12f_eq_neg_Qang α hα hα1 hf c (Nat.pos_of_ne_zero h) hc z hz

/-- The explicit expression to which the integrand of `radA` is equal on `(0,∞)`. -/
noncomputable def Efun (α : ℝ) (f : ℝ → ℝ → ℝ) (j : ℕ) (z : ℝ) : ℝ :=
  (-(∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
        * (Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z)
        * (if j - b = 0 then Work.Coercivity.L12f f z
            else - Work.Elliptic.Qang f (j - b - 1) z))
      + (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α)
        * (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z))
    * (-(∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
        * (Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z)
        * (if j - b = 0 then Work.Coercivity.L12f f z
            else - Work.Elliptic.Qang f (j - b - 1) z))
      + (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α)
        * (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z))
    * (Work.Spaces.w z * Work.Spaces.w z)

/-- The bracket of `Efun`, exposed for the estimates. -/
noncomputable def Big (α : ℝ) (f : ℝ → ℝ → ℝ) (j : ℕ) (z : ℝ) : ℝ :=
  -(∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
      * (Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z)
      * (if j - b = 0 then Work.Coercivity.L12f f z
          else - Work.Elliptic.Qang f (j - b - 1) z))
    + (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α)
      * (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z)

theorem Efun_eq_Big (α : ℝ) (f : ℝ → ℝ → ℝ) (j : ℕ) (z : ℝ) :
    Efun α f j z = Big α f j z * Big α f j z * (Work.Spaces.w z * Work.Spaces.w z) := rfl

theorem Big_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (j : ℕ) (z : ℝ) :
    Big α f j z = -(∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
        * (Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z)
        * (if j - b = 0 then Work.Coercivity.L12f f z
            else - Work.Elliptic.Qang f (j - b - 1) z))
      + (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α)
        * (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z) := rfl

/-- The majorant of `Efun`. -/
noncomputable def Maj (α : ℝ) (f : ℝ → ℝ → ℝ) (j : ℕ) (K : ℝ) (z : ℝ) : ℝ :=
  2 * ((K * 2 ^ j) ^ 2 * ((j : ℝ) + 1))
      * (∑ c ∈ Finset.range (j + 1),
          (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2 * (Work.Spaces.w z) ^ 2)
    + 2 * ((Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α) ^ 2)
      * ((Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
          * (Work.Spaces.w z) ^ 2)

theorem Maj_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (j : ℕ) (K : ℝ) (z : ℝ) :
    Maj α f j K z = 2 * ((K * 2 ^ j) ^ 2 * ((j : ℝ) + 1))
        * (∑ c ∈ Finset.range (j + 1),
            (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2 * (Work.Spaces.w z) ^ 2)
      + 2 * ((Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α) ^ 2)
        * ((Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
            * (Work.Spaces.w z) ^ 2) := rfl

end Work.FTS.CoercivityFix.Transfer.E1Parts
