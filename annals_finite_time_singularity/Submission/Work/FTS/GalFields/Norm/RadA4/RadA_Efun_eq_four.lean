/-
# `GalFields/Norm/RadA4/RadA_Efun_eq_four` — the order-`4` pointwise identity for `radA`

This is the order-`4` companion of `Work.FTS.CoercivityFix.Transfer.E1Parts.RadA_Efun_eq`
(order `3`): for coercivity-admissible `f` (`Work.FTS.Nonlin.CoerAdm α f`) and every `j ≤ 4`,

  `(D_z^j (radA α f)(z))² w(z)² = Efun α f j z`     on `(0,∞)`,

where `Efun` is the explicit expression of `E1Parts.RadAPieces` (the square of the bracket
obtained from the Leibniz rule on `radA = −ampA α·L₁₂ f + (ampB α/c α)·L₁₂(Transport f)(0)`,
with `D_z^c (L₁₂ f)` rewritten through `E1Parts.dzdIter_L_as_if`).

The whole order-`4` strengthening is in the *smoothness* of the pieces, and it comes from the
fact that `CoerAdm α f` supplies `ℋ⁵`-membership: the localised `C⁴`-regularity of `L₁₂ f`
(`AuxE2.L12_contDiffOn_four_of_five`, via the angular-moment calculus `H2.QangDiff`, which
needs only `ℋ⁴`) and the `C⁵`-regularity of the two profile coefficients
(`E2pkg.contDiffOn_ampA_five`, `E2pkg.contDiffOn_ampB_five`).  With these, the three steps of
`RadAId` — additivity of the `D_z`-iterates on the split of `radA`, the Leibniz expansion of
the `ampA·L₁₂ f` summand, and the constant-multiple form of the `ampB` summand — run
verbatim at order `4`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.RadAId
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.RadAZop
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.RadAPieces
import Submission.Work.FTS.Nonlinear.Pieces.rowsN0Q
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.RadSAux
import Submission.Work.FTS.CoercivityFix.Transfer.AuxE2.L12_contDiffOn_four_of_five

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalFields.Norm.RadA4

set_option maxHeartbeats 1000000

/-- **`L₁₂ f` is `C⁴` on `(0,∞)`** for coercivity-admissible data: `CoerAdm α f` supplies
`ℋ⁵`-membership, and order `4` costs nothing beyond `ℋ⁴` in the localised class. -/
theorem L12f_contDiffOn_four (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.Nonlin.CoerAdm α f) :
    ContDiffOn ℝ 4 (Work.Coercivity.L12f f) (Set.Ioi (0 : ℝ)) :=
  Work.FTS.CoercivityFix.Transfer.AuxE2.L12_contDiffOn_four_of_five α hα hα1
    hf.reg.1 hf.reg.2.1 hf.l12

/-- **Additivity of the `D_z`-iterates of `radA`, order `4`.** -/
theorem radA_iter_add_four (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ)
    (hf : Work.FTS.Nonlin.CoerAdm α f) {j : ℕ} (hj : j ≤ 4) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radA α f) z
        = Work.Elliptic.DzdIter j (fun z : ℝ => -1
            * (Work.FTS.CoercivityFix.Transfer.ampA α z * Work.Coercivity.L12f f z)) z
          + Work.Elliptic.DzdIter j (fun z : ℝ =>
              (Work.FTS.CoercivityFix.Transfer.ampB α z / Work.Spaces.c α)
                * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) z := by
  have hsm : Work.FTS.LocData.SmoothQuad f := hf.reg.1
  have hL4 : ContDiffOn ℝ 4 (Work.Coercivity.L12f f) (Set.Ioi (0 : ℝ)) :=
    L12f_contDiffOn_four α hα hα1 hf
  have hA4 : ContDiffOn ℝ 4 (Work.FTS.CoercivityFix.Transfer.ampA α) (Set.Ioi (0 : ℝ)) :=
    (Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_ampA_five α).of_le (by norm_num)
  have hB4 : ContDiffOn ℝ 4 (Work.FTS.CoercivityFix.Transfer.ampB α) (Set.Ioi (0 : ℝ)) :=
    (Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_ampB_five α).of_le (by norm_num)
  have hPsm : ContDiffOn ℝ 4
      (fun z : ℝ => Work.FTS.CoercivityFix.Transfer.ampA α z * Work.Coercivity.L12f f z)
      (Set.Ioi (0 : ℝ)) := hA4.mul hL4
  have hU₁sm : ContDiffOn ℝ 4 (fun z : ℝ => -1
      * (Work.FTS.CoercivityFix.Transfer.ampA α z * Work.Coercivity.L12f f z))
      (Set.Ioi (0 : ℝ)) := contDiffOn_const.mul hPsm
  have hU₂sm : ContDiffOn ℝ 4 (fun z : ℝ =>
      (Work.FTS.CoercivityFix.Transfer.ampB α z / Work.Spaces.c α)
        * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) (Set.Ioi (0 : ℝ)) :=
    (hB4.div_const (Work.Spaces.c α)).mul contDiffOn_const
  have hdiff₁ : ∀ b < j, ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b (fun z : ℝ => -1
        * (Work.FTS.CoercivityFix.Transfer.ampA α z * Work.Coercivity.L12f f z))) z := by
    intro b hb z hz
    have hb4 : b + 1 ≤ 4 := by omega
    have hZ : DifferentiableAt ℝ (Work.Spaces.Zop^[b] (fun z : ℝ => -1
        * (Work.FTS.CoercivityFix.Transfer.ampA α z * Work.Coercivity.L12f f z))) z :=
      Work.FTS.CoercivityFix.Transfer.E1Parts.differentiableAt_Zop_iter_of_contDiffOn
        (hu := hU₁sm.of_le (by exact_mod_cast hb4)) hz
    have haux : Work.Elliptic.DzdIter b (fun z : ℝ => -1
        * (Work.FTS.CoercivityFix.Transfer.ampA α z * Work.Coercivity.L12f f z))
        = Work.Spaces.Zop^[b] (fun z : ℝ => -1
            * (Work.FTS.CoercivityFix.Transfer.ampA α z * Work.Coercivity.L12f f z)) :=
      Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter b _
    rw [haux]
    exact hZ
  have hdiff₂ : ∀ b < j, ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b (fun z : ℝ =>
        (Work.FTS.CoercivityFix.Transfer.ampB α z / Work.Spaces.c α)
          * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0)) z := by
    intro b hb z hz
    have hb4 : b + 1 ≤ 4 := by omega
    have hZ : DifferentiableAt ℝ (Work.Spaces.Zop^[b] (fun z : ℝ =>
        (Work.FTS.CoercivityFix.Transfer.ampB α z / Work.Spaces.c α)
          * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0)) z :=
      Work.FTS.CoercivityFix.Transfer.E1Parts.differentiableAt_Zop_iter_of_contDiffOn
        (hu := hU₂sm.of_le (by exact_mod_cast hb4)) hz
    have haux : Work.Elliptic.DzdIter b (fun z : ℝ =>
        (Work.FTS.CoercivityFix.Transfer.ampB α z / Work.Spaces.c α)
          * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0)
        = Work.Spaces.Zop^[b] (fun z : ℝ =>
            (Work.FTS.CoercivityFix.Transfer.ampB α z / Work.Spaces.c α)
              * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) :=
      Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter b _
    rw [haux]
    exact hZ
  intro z hz
  rw [Work.FTS.CoercivityFix.Transfer.E1Parts.DzdIter_congr_of_eqOn
    (Work.FTS.CoercivityFix.Transfer.radA α f)
    (fun z : ℝ => (-1 * (Work.FTS.CoercivityFix.Transfer.ampA α z
          * Work.Coercivity.L12f f z))
        + ((Work.FTS.CoercivityFix.Transfer.ampB α z / Work.Spaces.c α)
            * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0))
    (Work.FTS.CoercivityFix.Transfer.E1Parts.radA_split α) j z hz]
  exact Work.FTS.CoercivityFix.Transfer.E1Parts.DzdIter_add_of_diff j _ _ hdiff₁ hdiff₂ z hz

/-- **The Leibniz expansion of the first summand of `radA`, order `4`.** -/
theorem radA_iter_U1_four (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ)
    (hf : Work.FTS.Nonlin.CoerAdm α f) {j : ℕ} (hj : j ≤ 4) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.Elliptic.DzdIter j (fun z : ℝ => -1
          * (Work.FTS.CoercivityFix.Transfer.ampA α z * Work.Coercivity.L12f f z)) z
        = -1 * ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
            * (Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z)
            * (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z) := by
  have hL4 : ContDiffOn ℝ 4 (Work.Coercivity.L12f f) (Set.Ioi (0 : ℝ)) :=
    L12f_contDiffOn_four α hα hα1 hf
  have hA4 : ContDiffOn ℝ 4 (Work.FTS.CoercivityFix.Transfer.ampA α) (Set.Ioi (0 : ℝ)) :=
    (Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_ampA_five α).of_le (by norm_num)
  intro z hz
  have hAdiff : ∀ b < j, ∀ z' ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b
        (Work.FTS.CoercivityFix.Transfer.ampA α)) z' := by
    intro b hb z' hz'
    have hb4 : b + 1 ≤ 4 := by omega
    have hZ : DifferentiableAt ℝ (Work.Spaces.Zop^[b]
        (Work.FTS.CoercivityFix.Transfer.ampA α)) z' :=
      Work.FTS.CoercivityFix.Transfer.E1Parts.differentiableAt_Zop_iter_of_contDiffOn
        (hu := hA4.of_le (by exact_mod_cast hb4)) hz'
    have haux : Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α)
        = Work.Spaces.Zop^[b] (Work.FTS.CoercivityFix.Transfer.ampA α) :=
      Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter b _
    rw [haux]
    exact hZ
  have hLdiff : ∀ b < j, ∀ z' ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b (Work.Coercivity.L12f f)) z' := by
    intro b hb z' hz'
    have hb4 : b + 1 ≤ 4 := by omega
    exact Work.FTS.CoercivityFix.Transfer.E2pkg.differentiableAt_dzdIter_of_contDiffOn_general
      (N := 4) (c := b) hL4 hb4 hz'
  have hleib := Work.FTS.Nonlinear.Pieces.dzdIter_mul_leibniz j
    (Work.FTS.CoercivityFix.Transfer.ampA α) (Work.Coercivity.L12f f) hAdiff hLdiff z hz
  have heq : Work.Elliptic.DzdIter j (fun z : ℝ => -1
      * (Work.FTS.CoercivityFix.Transfer.ampA α z * Work.Coercivity.L12f f z))
      = Work.Spaces.Zop^[j] (fun z : ℝ => -1
          * (Work.FTS.CoercivityFix.Transfer.ampA α z * Work.Coercivity.L12f f z)) :=
    Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter j _
  rw [heq, Work.FTS.CoercivityFix.Transfer.E2pkg.Zop_iter_const_mul]
  dsimp only
  rw [← Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter j
    (fun z : ℝ => Work.FTS.CoercivityFix.Transfer.ampA α z * Work.Coercivity.L12f f z)]
  rw [hleib]
  simp only [mul_assoc]

/-- **The pointwise identity for the integrand of `radA`, order `4`.** -/
theorem RadA_Efun_eq_four (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ)
    (hf : Work.FTS.Nonlin.CoerAdm α f) {j : ℕ} (hj : j ≤ 4) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
        * (Work.Spaces.w z) ^ 2 = Work.FTS.CoercivityFix.Transfer.E1Parts.Efun α f j z := by
  intro z hz
  have hsum : (∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
        * (Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z)
        * (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z))
      = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
        * (Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z)
        * (if j - b = 0 then Work.Coercivity.L12f f z
            else - Work.Elliptic.Qang f (j - b - 1) z) := by
    refine Finset.sum_congr rfl fun b hb => ?_
    have hbj : j - b ≤ 4 := by
      have := Finset.mem_range.mp hb
      omega
    rw [Work.FTS.CoercivityFix.Transfer.E1Parts.dzdIter_L_as_if α hα hα1 hf hbj z hz]
  rw [radA_iter_add_four α hα hα1 f hf hj z hz, radA_iter_U1_four α hα hα1 f hf hj z hz,
    Work.FTS.CoercivityFix.Transfer.E1Parts.radA_iter_U2 α f j z hz,
    Work.FTS.CoercivityFix.Transfer.E1Parts.Efun_eq_Big,
    Work.FTS.CoercivityFix.Transfer.E1Parts.Big_eq, hsum]
  ring

end Work.FTS.GalFields.Norm.RadA4
