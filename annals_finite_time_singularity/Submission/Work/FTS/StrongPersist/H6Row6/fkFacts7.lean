/-
# `H6Row6/fkFacts7` — the six facts about the angular moment `FK f` at level `6`

The angular moment of the datum,
`FK f z = ∫_θ f(z,θ) K(θ) dθ` (`Work.Construction.FK`, `K(θ) = 3 sin θ cos²θ`), is a *radial*
function of `z`.  This module collects the six facts about it that the level-six `N`-row needs,
from the honest open-quadrant hypotheses `HQo α 6 f` (`C^∞` on the open quadrant plus honest
`ℋ⁶`), the extra honesty `ℋ⁷` and the vanishing zero mode `L₁₂ f 0 = 0`:

1. **regularity**: `z ↦ FK f z` is `C⁶` on the open quadrant (this is the finite-order
   smoothness that `SmoothOpen (FK f)` would fail to capture — see
   `H6Rows/Npair6BWork/NOTES_coefData_FK_FALSE.md`); the level `7` hypothesis is used here, via
   `FK f = 3 F_*(f)` and the downward induction of
   `EllipticEst.UopHk.contDiffOn_Fstar_of_smoothOpen_Hk`;
2. **level-four membership** and **level-four norm bound** `|FK f|_{ℋ⁴} ≤ C |f|_{ℋ⁴}` — the
   clause `fkH` of the level-four norm interface (`OpenPkg.fkH_field`), which needs only
   `HQo α 4 f` (obtained from `HQo α 6 f` by monotonicity of the honesty order);
3. **level-six membership** (`H6Rows.Npair6BWork.fk_hkMem`, the angular Cauchy–Schwarz
   `QangSq6Full` summed over `i ≤ 6`);
4. **level-six norm bound** `|FK f|_{ℋ⁶} ≤ Ξ α^{-Cpow} |f|_{ℋ⁶}` (`fkH6_norm_le`, the sharp
   homogeneous form of the level-six estimate; the witness has `Cpow = 0`);
5. **the pointwise bound** `|FK f z| ≤ C α^{-1/2} |f|_{ℋ⁴}` for `z > 0`: Cauchy–Schwarz in `θ`
   (`n5_FK_abs_le`, constant `4`) against the *uniform in `z`* angular slice bound
   `∫_θ (f z θ)² ≤ 3 |f|²_{ℋ⁴}` (`TransportS.SupDzAux.sup_dz_avg_le`), and `1 ≤ α^{-1/2}`.

The `θ`-dependence of the pointwise clause is vacuous (`FK f z` does not depend on `θ`), but the
statement is kept in the requested form.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.N6_fkH
import Submission.Work.FTS.StrongPersist.SupOpenH2
import Submission.Work.FTS.StrongPersist.H6Rows.piecesC6
import Submission.Work.FTS.OpenPkg.fkH_field
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.StrongLWP.Basic
import Submission.Work.FTS.EllipticEst.UopHk.GsingFactsInterior
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.Basic
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.NfkSmooth
import Submission.Work.FTS.Nonlinear.Pieces.Rl1.n5Bound
import Submission.Work.FTS.TransportS.SupDzAux.sup_dz_avg_le
import Submission.Work.FTS.EllipticEst.Dispatch.RadAux
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.fk_hkMem
import Submission.Work.FTS.StrongPersist.H6Rows.NZaux.Slots
import Submission.Work.FTS.StrongPersist.H6Row6.fkH6_norm_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Row6

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem fkFacts7 : ∃ C Xi Cpow : ℝ, 0 < C ∧ 0 < Xi ∧ 0 ≤ Cpow ∧ ∀ {α : ℝ}, 0 < α → α ≤ 1 →
    ∀ (f : Work.FTS.Galerkin.Fn),
    Work.FTS.VocabO.HQo α 6 f → Work.Spaces.HkMem α 7 f →
      Work.Construction.L12 f 0 = 0 →
    ContDiffOn ℝ 6 (Function.uncurry (fun z _ => Work.Construction.FK f z))
        Work.FTS.EllipticEst.Q0 ∧
    Work.Spaces.HkMem α 4 (fun z _ => Work.Construction.FK f z) ∧
    Work.Spaces.HkNorm α 4 (fun z _ => Work.Construction.FK f z)
      ≤ C * Work.Spaces.HkNorm α 4 f ∧
    Work.Spaces.HkMem α 6 (fun z _ => Work.Construction.FK f z) ∧
    Work.Spaces.HkNorm α 6 (fun z _ => Work.Construction.FK f z)
      ≤ Xi * α ^ (-Cpow) * Work.Spaces.HkNorm α 6 f ∧
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Construction.FK f z| ≤ C * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 4 f) := by
  -- the level-four `fkH` clause and the uniform angular slice bound
  obtain ⟨C4, hC4pos, hC4⟩ := Work.FTS.OpenPkg.fkH_field
  obtain ⟨Cavg, hCavpos, hCavg⟩ := Work.FTS.TransportS.SupDzAux.sup_dz_avg_le
  -- the level-six norm bound (sharp, homogeneous form)
  obtain ⟨C6, hC6pos, hC6⟩ := Work.FTS.StrongPersist.H6Row6.fkH6_norm_le
  refine ⟨max C4 (4 * Real.sqrt Cavg), C6, 0, lt_max_of_lt_left hC4pos, hC6pos,
    le_refl 0, ?_⟩
  intro α hα hα1 f hQ h7 hL12
  have hsm : Work.FTS.EllipticEst.SmoothOpen f := hQ.1
  have hmem6 : Work.Spaces.HkMem α 6 f := hQ.2
  have hmem4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hsm (l := 4) (k := 6) (by norm_num) hmem6
  -- ## 1. regularity: `FK f = 3 F_*(f)` is `C⁶` on `(0,∞)`, hence `C⁶` on the open quadrant
  have hA : ContDiffOn ℝ 6 (Function.uncurry (fun z (_ : ℝ) => Work.Construction.FK f z))
      Work.FTS.EllipticEst.Q0 := by
    have hF : ContDiffOn ℝ 6 (Work.Elliptic.Fstar f) (Set.Ioi (0 : ℝ)) :=
      Work.FTS.EllipticEst.UopHk.contDiffOn_Fstar_of_smoothOpen_Hk α 7 f hsm h7 (by norm_num)
    have h3 : ContDiffOn ℝ 6 (fun z => (3 : ℝ) • Work.Elliptic.Fstar f z) (Set.Ioi (0 : ℝ)) :=
      hF.const_smul (3 : ℝ)
    have hFK6 : ContDiffOn ℝ 6 (fun z => Work.Construction.FK f z) (Set.Ioi (0 : ℝ)) := by
      rw [Work.FTS.StrongPersist.L3Rhs.NfkAux.fk_eq_three_Fstar f]
      simpa only [Pi.smul_apply, smul_eq_mul] using h3
    exact Work.FTS.StrongPersist.L3Rhs.NfkAux.contDiffOn_radial hFK6
  -- ## 2./3. the level-four membership and norm bound
  have hQ4 : Work.FTS.VocabO.HQo α 4 f := Work.FTS.OpenPkg.HQo.mono hQ (by norm_num)
  obtain ⟨hBmem, hBnorm0⟩ := hC4 α hα hα1 f hQ4 hL12
  have hBnorm : Work.Spaces.HkNorm α 4 (fun z _ => Work.Construction.FK f z)
      ≤ max C4 (4 * Real.sqrt Cavg) * Work.Spaces.HkNorm α 4 f :=
    le_trans hBnorm0 (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Work.Spaces.HkNorm_nonneg α 4 f))
  -- ## 4./5. the level-six membership and norm bound
  have hCmem : Work.Spaces.HkMem α 6 (fun z _ => Work.Construction.FK f z) :=
    Work.FTS.StrongPersist.H6Rows.Npair6BWork.fk_hkMem α ⟨hα, hα1⟩ f hsm hmem6
  have hCnorm : Work.Spaces.HkNorm α 6 (fun z _ => Work.Construction.FK f z)
      ≤ C6 * α ^ (-(0 : ℝ)) * Work.Spaces.HkNorm α 6 f := by
    simpa [Real.rpow_zero] using hC6 α hα hα1 f hsm hmem6
  -- ## 6. the pointwise bound
  have hD : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Construction.FK f z| ≤ max C4 (4 * Real.sqrt Cavg)
        * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 4 f := by
    intro z θ hz hθ hθ2
    have haesm : MeasureTheory.AEStronglyMeasurable (fun θ' => f z θ')
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      Work.FTS.EllipticEst.Dispatch.RadAux.aesm_slice_of_smoothOpen hsm hz
    have hsl : MeasureTheory.IntegrableOn (fun θ' => (f z θ') ^ 2) Work.Spaces.Iθ :=
      Work.FTS.EllipticEst.Dispatch.RadAux.integrableOn_sq_of_hkMem
        (Work.FTS.OpenPkg.HkMem_mono_open hsm (l := 0) (k := 6) (Nat.zero_le _) hmem6) hz haesm
    have hFKpt := Work.FTS.Nonlinear.Pieces.Rl1.n5_FK_abs_le hz hsl haesm
    have hslice : (∫ θ' in Work.Spaces.Iθ, (f z θ') ^ 2)
        ≤ Cavg * Work.Spaces.HkSq α 4 f := by
      have h := hCavg α f 0 hα hα1 hsm hmem4 (by norm_num) z hz
      simpa only [Work.Spaces.DzIter_zero] using h
    have hXn4 : 0 ≤ Work.Spaces.HkNorm α 4 f := Work.Spaces.HkNorm_nonneg α 4 f
    have hpc : (1 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) :=
      Work.FTS.StrongPersist.H6Rows.one_le_rpow_neg_half hα hα1
    calc |Work.Construction.FK f z|
        ≤ 4 * Real.sqrt (∫ θ' in Work.Spaces.Iθ, (f z θ') ^ 2) := hFKpt
      _ ≤ 4 * Real.sqrt (Cavg * Work.Spaces.HkSq α 4 f) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hslice) (by norm_num)
      _ = 4 * (Real.sqrt Cavg * Work.Spaces.HkNorm α 4 f) := by
          rw [Real.sqrt_mul hCavpos.le]
          rfl
      _ = (4 * Real.sqrt Cavg) * Work.Spaces.HkNorm α 4 f := by ring
      _ ≤ (4 * Real.sqrt Cavg) * (α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 4 f) :=
          mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hXn4 hpc) (by positivity)
      _ ≤ max C4 (4 * Real.sqrt Cavg)
            * (α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 4 f) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
      _ = max C4 (4 * Real.sqrt Cavg) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 4 f := by ring
  exact ⟨hA, hBmem, hBnorm, hCmem, hCnorm, hD⟩

end Work.FTS.StrongPersist.H6Row6
