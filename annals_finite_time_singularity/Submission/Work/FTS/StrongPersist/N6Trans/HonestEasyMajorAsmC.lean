/-
The open-class assembly `AssemblyQ_o`.
Part of the auxiliary module `HonestEasyMajorAux` for
`HonestEasyMajorLem`; see the aggregator file for the full description.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.H2.T1EasyBound
import Submission.Work.FTS.H2.T2Aesm
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.FTS.H2.T1Q.Basic
import Submission.Work.FTS.H2.HQ.HardyZQ
import Submission.Work.FTS.H2.MinLeAvg
import Submission.Work.FTS.H2.OscSqLe
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.H2.HQ.DthDzIterComm
import Submission.Work.Spaces.bt_aux
import Submission.Work.H2.T1Q.SlotOpen
import Submission.Work.H2.T1Q.SlotPtQ
import Submission.Work.H2.T1Q.ExpandQ
import Submission.Work.H2.T1Q.T1EasyContQ
import Submission.Work.H2.T1Q.ExcBoundQ
import Submission.Work.H2.T1Q.SupThetaIntQ
import Submission.Work.H2.T1Q.SliceSupOpen
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS.StrongPersist.N6Trans.HonestEasyMajorAsmB

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter
open Work.Spaces
open Work.FTS.H2
open Work.H2.T1Q

namespace Work.FTS.StrongPersist.N6Trans.HonestEasyMajorAux

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-- **The `2`-dimensional bound for the pointwise majorant `EasyMajor` in the interior class.**

For `0 < α ≤ 1`, `SmoothQuad` data `f`, `g` with `DecayAll 4` and `HkMem α 4`, the two pointwise
bounds `|mixed b a f| ≤ Kf`, `|mixed b a g| ≤ Kg` on the *open* quadrant for `a + b ≤ 2`, and an
`L²`-bound `K3` for `z ↦ supAbsThO (D_z³f) z · w z`, the pointwise majorant `EasyMajor α f g`
(the sum of the absolute values of the Leibniz summands `xD`, `yM` of `H4PairInt α (f·D_θg) g`
with the five `T1Hard` summands removed) is integrable on the product measure `pm` with

  `∫ EasyMajor ≤ 5000000 · (Kf·|g|²_{ℋ⁴} + Kg·|f|_{ℋ⁴}·|g|_{ℋ⁴} + √K3·|g|²_{ℋ⁴})`.

Route: copy the assembly `Work.FTS.H2.EMS_int_and_le` of
`Submission/Work/FTS/H2/T1EasyBound.lean` verbatim (its `EMx`/`EMyA`/`EMy`/`EMS` decomposition,
`EasyMajor_eq_EMS`, `sum_range_range_le_25`, `sum_le_25_of_le4`, `integrable_finsetSum` bookkeeping
and the final arithmetic), replacing:
* its per-summand bounds `xD_summand_bound` / `yM_summand_bound` (stated for `Spaces.SmoothNbhd`
  and `supAbs`) by the interior versions described below;
* the template's `slot_pair_bound`/`term_of_slot` (closed-quadrant `V`-bound) by
  `Work.FTS.H2.term_of_slot_open` (open-quadrant `V`-bound, `Submission/Work/H2/T1Q/SlotOpen.lean`);
* the measurability helper `Work.FTS.H2.aesm_prod_three` by `Work.H2.T1Q.aesm_prod_three_qd`.

Each of the four per-summand bounds is: a pointwise comparison
(`Work.H2.T1Q.xD_Kf_pt`, `xD_Kg_pt`, `yM_Kf_pt`, `yM_Kg_mixed_pt` — all in
`Submission/Work/H2/T1Q/SlotPtQ.lean`) with `term_of_slot_open` and the template's
`xD_finish`/`yM_finish`/`choose_le_16`/`choose_mul_le_256`, giving
`Integrable (fun p => |xD f g i b p.1 p.2|) pm ∧ ∫ ≤ 16·TTot` and
`Integrable (fun p => |yM α f g i j a b p.1 p.2|) pm ∧ ∫ ≤ 256·TTot`
(with the excluded summands contributing `0`).
The single exceptional summand `(i,j,a,b) = (1,3,0,3)` — where the `f`-factor is `D_z³f` and no
pointwise bound `Kf` is available — is handled by `Work.H2.T1Q.ExcBoundOpen`
(`Submission/Work/H2/T1Q/ExcBoundOpen.lean`), which gives the sharper `√K3·|g|²_{ℋ⁴}`. -/
theorem AssemblyQ_o (α : ℝ) (f g : ℝ → ℝ → ℝ) (Kf Kg K3 : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hdecg : Work.Spaces.DecayAll 4 g)
    (hmemf : Work.Spaces.HkMem α 4 f) (hmemg : Work.Spaces.HkMem α 4 g)
    (hKf : ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed b a f z θ| ≤ Kf)
    (hKg : ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed b a g z θ| ≤ Kg)
    (hGint : MeasureTheory.IntegrableOn
      (fun z => (Work.FTS.H2.supAbsThO (Work.Spaces.DzIter 3 f) z * Work.Spaces.w z) ^ 2)
      Work.Spaces.Iz)
    (hGle : (∫ z in Work.Spaces.Iz,
      (Work.FTS.H2.supAbsThO (Work.Spaces.DzIter 3 f) z * Work.Spaces.w z) ^ 2) ≤ K3)
    (hKf0 : 0 ≤ Kf) (hKg0 : 0 ≤ Kg) (hK3 : 0 ≤ K3) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.FTS.H2.EasyMajor α f g p.1 p.2)
        Work.FTS.H2.pm ∧
      ∫ p, Work.FTS.H2.EasyMajor α f g p.1 p.2 ∂Work.FTS.H2.pm
        ≤ 5000000 * Work.FTS.H2.TTot α f g Kf Kg K3 := by
  have hT := TTot_nonneg α f g Kf Kg K3 hKf0 hKg0 hK3
  -- ### the `D_z` part
  have hxD : ∀ i ∈ Finset.range 5, ∀ b ∈ Finset.range (i + 1),
      MeasureTheory.Integrable (fun p : ℝ × ℝ => EMx f g i b p) Work.FTS.H2.pm ∧
        ∫ p, EMx f g i b p ∂Work.FTS.H2.pm ≤ 16 * TTot α f g Kf Kg K3 :=
    fun i hi b hb => xD_summand_bound_q_o α hα hα1 f g Kf Kg K3 hf hg hdecg hmemf hmemg
      hKf hKg hKf0 hKg0 hK3 i b (by have := Finset.mem_range.mp hi; omega)
      (by have := Finset.mem_range.mp hb; omega)
  have hxD_int : ∀ i ∈ Finset.range 5,
      MeasureTheory.Integrable (fun p : ℝ × ℝ => ∑ b ∈ Finset.range (i + 1), EMx f g i b p)
        Work.FTS.H2.pm :=
    fun i hi => integrable_finsetSum _ fun b hb => (hxD i hi b hb).1
  have hSx_int : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => ∑ i ∈ Finset.range 5, ∑ b ∈ Finset.range (i + 1), EMx f g i b p)
      Work.FTS.H2.pm :=
    integrable_finsetSum _ hxD_int
  have hSx_val : (∫ p, (∑ i ∈ Finset.range 5, ∑ b ∈ Finset.range (i + 1), EMx f g i b p)
        ∂Work.FTS.H2.pm)
      = ∑ i ∈ Finset.range 5, ∑ b ∈ Finset.range (i + 1),
          ∫ p, EMx f g i b p ∂Work.FTS.H2.pm := by
    rw [integral_finsetSum _ hxD_int]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [integral_finsetSum _ fun b hb => (hxD i hi b hb).1]
  have hSx_le : (∫ p, (∑ i ∈ Finset.range 5, ∑ b ∈ Finset.range (i + 1), EMx f g i b p)
        ∂Work.FTS.H2.pm)
      ≤ 25 * (16 * TTot α f g Kf Kg K3) := by
    rw [hSx_val]
    calc (∑ i ∈ Finset.range 5, ∑ b ∈ Finset.range (i + 1),
            ∫ p, EMx f g i b p ∂Work.FTS.H2.pm)
        ≤ ∑ i ∈ Finset.range 5, ∑ b ∈ Finset.range (i + 1), (16 * TTot α f g Kf Kg K3) :=
          Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun b hb => (hxD i hi b hb).2
      _ ≤ 25 * (16 * TTot α f g Kf Kg K3) :=
          sum_range_range_le_25 (16 * TTot α f g Kf Kg K3) (mul_nonneg (by norm_num) hT)
  -- ### the mixed part
  have hyM : ∀ i ∈ Finset.range 5, ∀ j ∈ Finset.range 5, ∀ a ∈ Finset.range (i + 1),
      ∀ b ∈ Finset.range (j + 1),
      MeasureTheory.Integrable (fun p : ℝ × ℝ => EMyA α f g i j a b p) Work.FTS.H2.pm ∧
        ∫ p, EMyA α f g i j a b p ∂Work.FTS.H2.pm ≤ 256 * TTot α f g Kf Kg K3 := by
    intro i hi j hj a ha b hb
    exact yM_summand_bound_q_o α hα hα1 f g Kf Kg K3 hf hg hdecg hmemf hmemg
      hKf hKg hKf0 hKg0 hK3 hGint hGle i j a b (by have := Finset.mem_range.mp hi; omega)
      (by have := Finset.mem_range.mp hj; omega) (by have := Finset.mem_range.mp ha; omega)
      (by have := Finset.mem_range.mp hb; omega)
  have hyM_ij : ∀ i ∈ Finset.range 5, ∀ j ∈ Finset.range 5,
      MeasureTheory.Integrable (fun p : ℝ × ℝ => EMy α f g i j p) Work.FTS.H2.pm ∧
        ∫ p, EMy α f g i j p ∂Work.FTS.H2.pm ≤ 625 * (256 * TTot α f g Kf Kg K3) := by
    intro i hi j hj
    constructor
    · exact integrable_finsetSum _ fun a ha =>
        integrable_finsetSum _ fun b hb => (hyM i hi j hj a ha b hb).1
    · rw [integral_finsetSum _ (fun a ha =>
          integrable_finsetSum _ fun b hb => (hyM i hi j hj a ha b hb).1)]
      have hval : (∑ a ∈ Finset.range (i + 1),
            ∫ p, (∑ b ∈ Finset.range (j + 1), EMyA α f g i j a b p) ∂Work.FTS.H2.pm)
          = ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
              ∫ p, EMyA α f g i j a b p ∂Work.FTS.H2.pm := by
        refine Finset.sum_congr rfl fun a ha => ?_
        rw [integral_finsetSum _ fun b hb => (hyM i hi j hj a ha b hb).1]
      rw [hval]
      calc (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            ∫ p, EMyA α f g i j a b p ∂Work.FTS.H2.pm)
          ≤ ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
              (256 * TTot α f g Kf Kg K3) :=
            Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => (hyM i hi j hj a ha b hb).2
        _ ≤ 25 * (256 * TTot α f g Kf Kg K3) :=
            sum_le_25_of_le4 (256 * TTot α f g Kf Kg K3) (mul_nonneg (by norm_num) hT) i j
              (by have := Finset.mem_range.mp hi; omega) (by have := Finset.mem_range.mp hj; omega)
        _ ≤ 625 * (256 * TTot α f g Kf Kg K3) := by
            have h1 : (0 : ℝ) ≤ 256 * TTot α f g Kf Kg K3 := mul_nonneg (by norm_num) hT
            nlinarith [h1]
  have hSy_int : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5, EMy α f g i j p)
      Work.FTS.H2.pm :=
    integrable_finsetSum _ fun i hi => integrable_finsetSum _ fun j hj => (hyM_ij i hi j hj).1
  have hSy_val : (∫ p, (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5, EMy α f g i j p)
        ∂Work.FTS.H2.pm)
      = ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
          ∫ p, EMy α f g i j p ∂Work.FTS.H2.pm := by
    rw [integral_finsetSum _ fun i hi => integrable_finsetSum _ fun j hj => (hyM_ij i hi j hj).1]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [integral_finsetSum _ fun j hj => (hyM_ij i hi j hj).1]
  have hSy_le : (∫ p, (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5, EMy α f g i j p)
        ∂Work.FTS.H2.pm)
      ≤ 25 * (625 * (256 * TTot α f g Kf Kg K3)) := by
    rw [hSy_val]
    calc (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5, ∫ p, EMy α f g i j p ∂Work.FTS.H2.pm)
        ≤ ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
            (625 * (256 * TTot α f g Kf Kg K3)) :=
          Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => (hyM_ij i hi j hj).2
      _ = 25 * (625 * (256 * TTot α f g Kf Kg K3)) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
  -- ### assembly
  have hEMS_int : MeasureTheory.Integrable (fun p : ℝ × ℝ => EMS α f g p) Work.FTS.H2.pm :=
    hSx_int.add hSy_int
  have hval : (∫ p, EMS α f g p ∂Work.FTS.H2.pm)
      = (∫ p, (∑ i ∈ Finset.range 5, ∑ b ∈ Finset.range (i + 1), EMx f g i b p)
          ∂Work.FTS.H2.pm)
        + ∫ p, (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5, EMy α f g i j p)
            ∂Work.FTS.H2.pm := by
    show (∫ p, ((∑ i ∈ Finset.range 5, ∑ b ∈ Finset.range (i + 1), EMx f g i b p)
        + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5, EMy α f g i j p) ∂Work.FTS.H2.pm) = _
    rw [integral_add hSx_int hSy_int]
  refine ⟨hEMS_int.congr (Eventually.of_forall fun p => (EasyMajor_eq_EMS α f g p).symm), ?_⟩
  rw [integral_congr_ae (Eventually.of_forall fun p => EasyMajor_eq_EMS α f g p), hval]
  have h1 : (∫ p, (∑ i ∈ Finset.range 5, ∑ b ∈ Finset.range (i + 1),
        EMx f g i b p) ∂Work.FTS.H2.pm) + (∫ p, (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
        EMy α f g i j p) ∂Work.FTS.H2.pm)
      ≤ 25 * (16 * TTot α f g Kf Kg K3) + 25 * (625 * (256 * TTot α f g Kf Kg K3)) :=
    add_le_add hSx_le hSy_le
  have h2 : 25 * (16 * TTot α f g Kf Kg K3) + 25 * (625 * (256 * TTot α f g Kf Kg K3))
      ≤ 5000000 * TTot α f g Kf Kg K3 := by
    nlinarith [hT]
  linarith


end Work.FTS.StrongPersist.N6Trans.HonestEasyMajorAux
