/-
# Order-`4` weighted `L²`-integrability of the `D_z`-iterates of `L₁₂ f`

`Submission.Work.FTS.GalFields.Norm.RadA4.L12f_DzdIter_sq_w_sq_integrable_four`.

For `0 < α ≤ 1`, `f ∈ CoerAdm α` and `c ≤ 4`, the weighted square
`(D_z^c (L₁₂ f)(z))² w(z)²` is integrable over `Iz = [0,∞)`.

This is `E1Parts.L12f_DzdIter_sq_w_sq_integrable` (the case `c ≤ 3`) one order up.  No new
mathematics is needed: the two ingredients of that proof already reach order `4`:

* `E1Parts.DzdIter_L12f_eq_neg_Qang` is stated for `1 ≤ c ≤ 4` and identified the iterates with
  the angular moments, `D_z^c (L₁₂ f)(z) = −Qang f (c−1) z` for `z > 0` (it is the `z`-derivative
  of the primitive identity `QangDiff`, and `HkMem α 4 f` — obtained from `RegQ α 5` through
  `HkMem_four_of_five` — is exactly what closes the induction at `c = 4`);
* `N4Fields.Qang_sq_w_sq_integral` bounds `∫_z (Qang f i z)² w²` for every `i ≤ 4`, i.e. for
  `i = 3`, the iterate `c = 4`'s companion.

So the only change with respect to `RadL12` is the range `c ≤ 4` and the instantiation
`i = c − 1 ≤ 3` (`≤ 4`).  The `c = 0` case is the Hardy inequality `L12f_w_hardy` and is
delegated unchanged to `L12f_DzdIter_sq_w_sq_integrable`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.RadL12
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.RadAPieces
import Submission.Work.FTS.Nonlinear.N4Fields.Qang_sq_w_sq_integral
import Submission.Work.Coercivity.L12f_w_hardy

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalFields.Norm.RadA4

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- **Weighted `L²`-integrability of the `D_z`-iterates of `L₁₂ f` for `c ≤ 4`**, i.e.
`∫_0^∞ (D_z^c (L₁₂ f)(z))² w(z)² dz < ∞` for every `0 < α ≤ 1` and `f ∈ CoerAdm α`.

Same proof as `E1Parts.L12f_DzdIter_sq_w_sq_integrable` with the range extended from `3` to `4`:
`c = 0` is the weighted Hardy inequality of `L₁₂`, and `1 ≤ c ≤ 4` is the angular moment bound
`Qang_sq_w_sq_integral` at index `c − 1 ≤ 3`, transported through the identity
`D_z^c (L₁₂ f) = −Qang f (c−1)` valid on `(0,∞)`. -/
theorem L12f_DzdIter_sq_w_sq_integrable_four (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    {f : ℝ → ℝ → ℝ} (hf : Work.FTS.Nonlin.CoerAdm α f) :
    ∀ c : ℕ, c ≤ 4 → MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2
        * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz := by
  intro c hc
  rcases Nat.eq_zero_or_pos c with h0 | h0
  · -- `c = 0`: the weighted Hardy inequality for `L₁₂ f`
    subst h0
    exact Work.FTS.CoercivityFix.Transfer.E1Parts.L12f_DzdIter_sq_w_sq_integrable
      α hα hα1 hf 0 (by norm_num)
  · -- `c ≥ 1`: the iterate is the angular moment `Qang f (c−1)`
    have hsm : Work.FTS.LocData.SmoothQuad f := hf.reg.1
    have hmem : Work.Spaces.HkMem α 4 f :=
      Work.FTS.CoercivityFix.Coer1T.HkMem_four_of_five α hsm hf.reg.2.1
    have hid := Work.FTS.CoercivityFix.Transfer.E1Parts.DzdIter_L12f_eq_neg_Qang
      α hα hα1 hf c h0 hc
    have hQ := Work.FTS.Nonlinear.N4Fields.Qang_sq_w_sq_integral (α := α) hα hα1 hsm hmem
      (i := c - 1) (by omega)
    have hQioi : IntegrableOn
        (fun z : ℝ => Work.Elliptic.Qang f (c - 1) z ^ 2 * (Work.Spaces.w z) ^ 2)
        (Set.Ioi (0 : ℝ)) :=
      hQ.1.congr_set_ae (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))
    have h1 : IntegrableOn
        (fun z : ℝ => (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2
          * (Work.Spaces.w z) ^ 2) (Set.Ioi (0 : ℝ)) :=
      hQioi.congr_fun (fun z hz => by
        show Work.Elliptic.Qang f (c - 1) z ^ 2 * Work.Spaces.w z ^ 2
          = (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2 * Work.Spaces.w z ^ 2
        rw [hid z hz]
        ring) measurableSet_Ioi
    exact h1.congr_set_ae (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ))).symm

end Work.FTS.GalFields.Norm.RadA4
