/-
Copyright: work module for the Elgindi finite-time singularity project.

# `N6Trans/Hon/SlotAbsHon`: the honest per-slot transport engine

The honest (`SmoothOpen`-based) copy of `Submission/Work/FTS/TransportS/T2Sup/slotAbsBound.lean`.
The frozen engine takes `T2SF α f` and `T2SG α g = RegQ α 4 g ∧ HkMem α 5 g ∧ DecayAll 4 g`; here
the `g`-side is the honest bundle `SmoothOpen g ∧ HkMem α 4 g ∧ HkMem α 5 g ∧ DecayAll 4 g`.  All
the machinery the frozen file itself introduces (`integrableOn_Maj1_slice_fts`,
`Maj1_integral_le_fts`, `sdel_integral_le_of_eta`, `canonW_mul_z_le_of_le`,
`canonW_mul_mixed_le_of_le`, `srestBound`, `Smain`, `Srest`, `Sdel`, `Ssum_eq_leibniz`,
`Ssum_eq_Smain_Srest_Sdel`, `integrableOnSliceDelicate`) is hypothesis-explicit and therefore
reused verbatim.  The three places where the frozen bundle was really consumed are:

* `supQ_T2Q` (order-`≤ 2` sup bounds of `g`, needing `SmoothQuad g` and `DecayAll`): replaced by
  `pwAny_sup` (`OpenPkg.ProdOpen.PwAny`), which needs only `SmoothOpen g ∧ HkMem α 4 g`;
* `smainBound` (the top slot `a + b = 4`, whose boundary term came from `BdryTraces`): replaced
  by the honest `smainBound_hon` (which consumes `TopSlotHonProp`);
* `delicateBound`/`delicateMargInt`/`sdel_integral_le_of_gam`: replaced by their honest copies.

The final arithmetic is `slot_arith_hon` (`Hon/SlotArithHon`), the honest form of the frozen
`slot_arith` with the honest `Smain` constant `Csm` in place of `2`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.Defs
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.SmainHon
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.SdelGamHon
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.SlotArithHon
import Submission.Work.FTS.TransportS.T2Sup.FinalAux
import Submission.Work.FTS.TransportS.T2Sup.PairBnd
import Submission.Work.FTS.TransportS.T2Sup.GenSlot
import Submission.Work.FTS.TransportS.T2Sup.absIntegralAddLe
import Submission.Work.FTS.TransportS.T2Sup.integrableOnSliceDelicate
import Submission.Work.FTS.TransportS.T2Sup.delicateBound
import Submission.Work.FTS.TransportS.T2Sup.Main
import Submission.Work.FTS.TransportS.T2Sup.FinalMain
import Submission.Work.FTS.TransportS.T2Sup.smainBound
import Submission.Work.FTS.TransportS.T2Sup.srestBound
import Submission.Work.FTS.TransportS.T2Sup.slotAbsBound
import Submission.Work.FTS.TransportS.Slots

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.Hon

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Work.FTS.TransportS
open Work.FTS.TransportS.SlotT2
open Work.FTS.TransportS.T2Sup

/-- **The per-slot transport bound in the honest class.** -/
theorem slotAbsBound_hon (hTop : TopSlotHonProp) (hDel : DelicateHonProp) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ) (a b : ℕ) (q : ℝ),
      0 < α → α ≤ 1 → HonF α f → Work.FTS.EllipticEst.SmoothOpen g →
      Work.Spaces.HkMem α 4 g → Work.Spaces.HkMem α 5 g → Work.Spaces.DecayAll 4 g →
      a + b ≤ 4 → 0 ≤ q →
      (a = 0 → q ≤ Work.Spaces.eta) → q ≤ Work.Spaces.gam α →
      (q ≤ Work.Spaces.eta ∨ q = Work.Spaces.gam α) →
      |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          Work.FTS.TransportS.SlotT2.canonW q z θ
            * Work.Spaces.mixed b a (fun z θ => f z θ * Work.Spaces.Dz g z θ) z θ
            * Work.Spaces.mixed b a g z θ|
        ≤ C * α ^ (-(1 / 2 : ℝ))
            * (Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 1 f)
            * Work.FTS.Nonlin.Xn α g ^ 2 := by
  obtain ⟨Cs, hCs0, hCs⟩ := Work.FTS.TransportS.sup_dz_le_hk
  obtain ⟨Cl, hCl0, hCl⟩ := Work.FTS.TransportS.flat_mixed_le 1
  obtain ⟨Cp, hCp0, hCgp⟩ := pwAny_sup
  obtain ⟨Cd, hCd0, hCd⟩ := hDel
  obtain ⟨Csm, hCsm1, hSmainb⟩ := smainBound_hon hTop
  set Cg : ℝ := Cp with hCgdef
  have hCg0 : 0 ≤ Cg := by rw [hCgdef]; exact hCp0.le
  refine ⟨(11 * Csm + 10 ^ 8) * (Cs + Cl + Cg + Cd + 1), by positivity, ?_⟩
  intro α f g a b q hα hα1 hf hg hmg4 hmg5 hdec hab hqnn hq0 hqγ hqcase
  have hFsm : Work.FTS.EllipticEst.SmoothOpen f := hf.1
  have hmf : Work.Spaces.HkMem α 4 f := hf.2.1
  have hGsm : Work.FTS.EllipticEst.SmoothOpen g := hg
  set Mf : ℝ := Cs / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α f with hMfdef
  set MK : ℝ := Cl * Work.FTS.VocabO.CoefTh 1 f with hMKdef
  set Mg : ℝ := Cg / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α g with hMgdef
  have hXn_f_nn : 0 ≤ Work.FTS.Nonlin.Xn α f := Work.Spaces.HkNorm_nonneg α 4 f
  have hXn_g_nn : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hKf_nn : 0 ≤ Work.FTS.VocabO.CoefTh 1 f := coefTh_nonneg 1 f
  have hMf0 : 0 ≤ Mf := by
    rw [hMfdef]
    exact mul_nonneg (div_nonneg hCs0.le (Real.sqrt_nonneg _)) hXn_f_nn
  have hMK0 : 0 ≤ MK := by rw [hMKdef]; exact mul_nonneg hCl0.le hKf_nn
  have hMg0 : 0 ≤ Mg := by
    rw [hMgdef]
    exact mul_nonneg (div_nonneg hCg0 (Real.sqrt_nonneg _)) hXn_g_nn
  have hFsup : ∀ j : ℕ, j ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.DzIter j f z θ| ≤ Mf := by
    intro j hj z θ hz hθ hθ2
    rw [hMfdef]
    exact hCs α f hα hα1 hFsm hmf j hj z θ hz hθ hθ2
  have hFσ : ∀ j i : ℕ, 1 ≤ i → i + j ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed j i f z θ| ≤ MK * Real.sin (2 * θ) := by
    intro j i hi hij z θ hz hθ hθ2
    have hK : ∀ b i' : ℕ, b + i' ≤ 1 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
        |Work.Spaces.mixed b i' (Work.Spaces.pth f) z θ| ≤ Work.FTS.VocabO.CoefTh 1 f :=
      fun b i' hbi z θ hz hθ hθ2 => Work.FTS.TransportS.t2SupF_pth_le_coefTh hf hbi hz hθ hθ2
    have h := hCl f hFsm (Work.FTS.VocabO.CoefTh 1 f) hKf_nn hK i j hi hij z θ hz hθ hθ2
    rw [hMKdef]
    calc |Work.Spaces.mixed j i f z θ|
        ≤ Cl * Real.sin (2 * θ) * Work.FTS.VocabO.CoefTh 1 f := h
      _ = (Cl * Work.FTS.VocabO.CoefTh 1 f) * Real.sin (2 * θ) := by ring
  have hGsup : ∀ j i : ℕ, i + j ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed j i g z θ| ≤ Mg := by
    intro j i hij z θ hz hθ hθ2
    rw [hMgdef, hCgdef]
    exact hCgp α g j i hα hα1 hGsm hmg4 hij z θ hz hθ hθ2
  have hSmain := hSmainb α f g a b q Mf hα hα1 hMf0 hab hq0 hqγ hFsm hGsm hmg4 hmg5 hdec
    (fun z θ hz hθ hθ2 => hFsup 0 (by norm_num) z θ hz hθ hθ2)
    (fun z θ hz hθ hθ2 => hFsup 1 (by norm_num) z θ hz hθ hθ2)
  have hSrest := srestBound (α := α) hα hα1 (f := f) (g := g) (a := a) (b := b) (q := q)
    (Mf := Mf) (MK := MK) (Mg := Mg) hMf0 hMK0 hMg0 hqnn hFsm hGsm hmf hmg4 hab
    hq0 hqγ hqcase hFsup hFσ hGsup
  set FA : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
    canonW q z θ * Smain f g a b z θ * Work.Spaces.mixed b a g z θ with hFAdef
  set Fr : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
    canonW q z θ * Srest f g a b z θ * Work.Spaces.mixed b a g z θ with hFrdef
  set Fd : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
    canonW q z θ * Sdel f g a b z θ * Work.Spaces.mixed b a g z θ with hFddef
  set FL : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
    canonW q z θ * Work.Spaces.mixed b a (fun z θ => f z θ * Work.Spaces.Dz g z θ) z θ
      * Work.Spaces.mixed b a g z θ with hFLdef
  have hsliceA : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
      (fun θ => canonW q z θ * Smain f g a b z θ * Work.Spaces.mixed b a g z θ)
      Work.Spaces.Iθ := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · subst h0
      rw [show (fun θ => canonW q 0 θ * Smain f g a b 0 θ * Work.Spaces.mixed b a g 0 θ)
          = fun _ => (0 : ℝ) from by
        funext θ; rw [canonW_zero_z]; ring]
      exact MeasureTheory.integrableOn_zero
    · refine MeasureTheory.Integrable.mono' ((hmg5.1 z hz).const_mul Mf) ?_ ?_
      · refine Work.Spaces.aesm_slice_of_continuousOn_Qd (fun p : ℝ × ℝ =>
          canonW q p.1 p.2 * Smain f g a b p.1 p.2 * Work.Spaces.mixed b a g p.1 p.2) ?_ hz0
        have hS : ContinuousOn (fun p : ℝ × ℝ => Smain f g a b p.1 p.2)
            (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) := by
          simp only [Smain, Function.uncurry_apply_pair]
          exact hFsm.continuousOn.mul (hGsm.mixed (b + 1) a).continuousOn
        exact ((continuousOn_canonW q).mul hS).mul (hGsm.mixed b a).continuousOn
      · refine ae_of_forall_Ioo (fun θ hθ => ?_)
        rw [Real.norm_eq_abs]
        have h := canonW_Smain_le (α := α) (f := f) (g := g) hα hMf0 hqnn hab hq0 hqγ
          (fun z θ hz hθ hθ2 => hFsup 0 (by norm_num) z θ hz hθ hθ2) z θ hz0 hθ.1 hθ.2
        calc |canonW q z θ * Smain f g a b z θ * Work.Spaces.mixed b a g z θ|
            = canonW q z θ * |Smain f g a b z θ| * |Work.Spaces.mixed b a g z θ| := by
              rw [abs_mul, abs_mul, abs_of_nonneg (canonW_nonneg ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)]
          _ ≤ Mf * Work.Spaces.HkIntegrand α 5 g z θ := h
  have hsliceR : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
      (fun θ => canonW q z θ * Srest f g a b z θ * Work.Spaces.mixed b a g z θ)
      Work.Spaces.Iθ := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · subst h0
      rw [show (fun θ => canonW q 0 θ * Srest f g a b 0 θ * Work.Spaces.mixed b a g 0 θ)
          = fun _ => (0 : ℝ) from by
        funext θ; rw [canonW_zero_z]; ring]
      exact MeasureTheory.integrableOn_zero
    · refine MeasureTheory.Integrable.mono'
          ((integrableOn_Maj1_slice_fts (α := α) (f := f) (g := g) (Mf := Mf) (MK := MK) (Mg := Mg) hmf hmg4 z hz).const_mul 6400) ?_ ?_
      · refine Work.Spaces.aesm_slice_of_continuousOn_Qd (fun p : ℝ × ℝ =>
          canonW q p.1 p.2 * Srest f g a b p.1 p.2 * Work.Spaces.mixed b a g p.1 p.2) ?_ hz0
        exact ((continuousOn_canonW q).mul (continuousOn_uncurry_Srest hFsm hGsm a b)).mul
          (hGsm.mixed b a).continuousOn
      · refine ae_of_forall_Ioo (fun θ hθ => ?_)
        rw [Real.norm_eq_abs]
        have h := canonW_mul_Srest_le (α := α) hα hα1 (f := f) (g := g) (a := a) (b := b)
          (q := q) (Mf := Mf) (MK := MK) (Mg := Mg) hMf0 hMK0 hMg0 hqnn hab hq0 hqγ hqcase
          hFsup hFσ hGsup z θ hz0 hθ.1 hθ.2
        calc |canonW q z θ * Srest f g a b z θ * Work.Spaces.mixed b a g z θ|
            = canonW q z θ * |Srest f g a b z θ| * |Work.Spaces.mixed b a g z θ| := by
              rw [abs_mul, abs_mul, abs_of_nonneg (canonW_nonneg ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)]
          _ ≤ 6400 * Maj1 α f g Mf MK Mg z θ := h
  have hsliceD : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
      (fun θ => canonW q z θ * Sdel f g a b z θ * Work.Spaces.mixed b a g z θ)
      Work.Spaces.Iθ := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · subst h0
      rw [show (fun θ => canonW q 0 θ * Sdel f g a b 0 θ * Work.Spaces.mixed b a g 0 θ)
          = fun _ => (0 : ℝ) from by
        funext θ; rw [canonW_zero_z]; ring]
      exact MeasureTheory.integrableOn_zero
    · have haesm : MeasureTheory.AEStronglyMeasurable
          (fun θ => canonW q z θ * Sdel f g a b z θ * Work.Spaces.mixed b a g z θ)
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
        refine Work.Spaces.aesm_slice_of_continuousOn_Qd (fun p : ℝ × ℝ =>
          canonW q p.1 p.2 * Sdel f g a b p.1 p.2 * Work.Spaces.mixed b a g p.1 p.2) ?_ hz0
        have hS : ContinuousOn (fun p : ℝ × ℝ => Sdel f g a b p.1 p.2)
            (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) := by
          simp only [Sdel, Function.uncurry_apply_pair]
          exact continuousOn_const.mul ((hFsm.mixed 3 0).continuousOn.mul
            ((hGsm.mixed (b - 2) a).continuousOn))
        exact ((continuousOn_canonW q).mul hS).mul (hGsm.mixed b a).continuousOn
      rcases hqcase with hqη | hqγ'
      · refine MeasureTheory.Integrable.mono'
            ((integrableOn_Maj1_slice_fts (α := α) (f := f) (g := g) (Mf := Mf) (MK := MK) (Mg := Mg) hmf hmg4 z hz).const_mul 16) haesm ?_
        refine ae_of_forall_Ioo (fun θ hθ => ?_)
        rw [Real.norm_eq_abs]
        have h := canonW_Sdel_le (α := α) hα hα1 hMf0 hMK0 hMg0 hqnn hab hq0 hqγ hqη
          hFsup hFσ hGsup z θ hz0 hθ.1 hθ.2
        calc |canonW q z θ * Sdel f g a b z θ * Work.Spaces.mixed b a g z θ|
            = canonW q z θ * |Sdel f g a b z θ| * |Work.Spaces.mixed b a g z θ| := by
              rw [abs_mul, abs_mul, abs_of_nonneg (canonW_nonneg ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)]
          _ ≤ 16 * Maj1 α f g Mf MK Mg z θ := h
      · subst hqγ'
        by_cases hb2 : b ≤ 2
        · rw [show (fun θ => canonW (Work.Spaces.gam α) z θ * Sdel f g a b z θ
              * Work.Spaces.mixed b a g z θ) = fun _ => (0 : ℝ) from by
            funext θ
            rw [Sdel, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]
            ring]
          exact MeasureTheory.integrableOn_zero
        · have ha0 : a ≠ 0 := by
            intro h0
            exact absurd (hq0 h0) (not_le.mpr (eta_lt_gam_of_pos hα))
          have ha1 : a = 1 := by omega
          have hb3 : b = 3 := by omega
          have hmaj : MeasureTheory.IntegrableOn (fun θ => canonW (Work.Spaces.gam α) z θ
              * |Work.Spaces.DzIter 3 f z θ| * |Work.Spaces.mixed 1 1 g z θ|
              * |Work.Spaces.mixed 3 1 g z θ|) Work.Spaces.Iθ :=
            integrableOnSliceDelicate hα hα1 hFsm hmf hGsm hmg4 hz0
          refine MeasureTheory.Integrable.mono' hmaj haesm ?_
          refine ae_of_forall_Ioo (fun θ hθ => ?_)
          rw [Real.norm_eq_abs, ha1, hb3]
          have hsdel : Sdel f g 1 3 z θ
              = Work.Spaces.mixed 3 0 f z θ * Work.Spaces.mixed 1 1 g z θ := by
            simp only [Sdel, Nat.choose_self, Nat.cast_one, one_mul, Nat.reduceSub]
          rw [hsdel, abs_mul, abs_mul, abs_mul, abs_of_nonneg (canonW_nonneg
            ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)]
          simp only [Work.Spaces.mixed_zero_right]
          exact le_of_eq (by ring)
  have hsplit : ∀ z : ℝ, 0 < z → FL z = FA z + (Fr z + Fd z) := by
    intro z hz0
    have h1 : FL z = ∫ θ in Work.Spaces.Iθ,
        canonW q z θ * Ssum f g a b z θ * Work.Spaces.mixed b a g z θ := by
      simp only [hFLdef]
      refine MeasureTheory.integral_congr_ae ?_
      rw [Work.FTS.TransportS.SlotT2.supOpen_restrict_Iθ]
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      show canonW q z θ * Work.Spaces.mixed b a (fun z θ => f z θ * Work.Spaces.Dz g z θ) z θ
          * Work.Spaces.mixed b a g z θ
        = canonW q z θ * Ssum f g a b z θ * Work.Spaces.mixed b a g z θ
      rw [Ssum_eq_leibniz b a hFsm hGsm z θ hz0 hθ.1 hθ.2]
    have h2 : (∫ θ in Work.Spaces.Iθ,
          canonW q z θ * Ssum f g a b z θ * Work.Spaces.mixed b a g z θ)
        = ∫ θ in Work.Spaces.Iθ,
            (canonW q z θ * Smain f g a b z θ * Work.Spaces.mixed b a g z θ
              + (canonW q z θ * Srest f g a b z θ * Work.Spaces.mixed b a g z θ
                + canonW q z θ * Sdel f g a b z θ * Work.Spaces.mixed b a g z θ)) := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
      show canonW q z θ * Ssum f g a b z θ * Work.Spaces.mixed b a g z θ
        = canonW q z θ * Smain f g a b z θ * Work.Spaces.mixed b a g z θ
          + (canonW q z θ * Srest f g a b z θ * Work.Spaces.mixed b a g z θ
            + canonW q z θ * Sdel f g a b z θ * Work.Spaces.mixed b a g z θ)
      rw [Ssum_eq_Smain_Srest_Sdel]
      ring
    have h3 : (∫ θ in Work.Spaces.Iθ,
            (canonW q z θ * Smain f g a b z θ * Work.Spaces.mixed b a g z θ
              + (canonW q z θ * Srest f g a b z θ * Work.Spaces.mixed b a g z θ
                + canonW q z θ * Sdel f g a b z θ * Work.Spaces.mixed b a g z θ)))
        = FA z + (Fr z + Fd z) := by
      have hAB : (∫ θ in Work.Spaces.Iθ,
            canonW q z θ * Smain f g a b z θ * Work.Spaces.mixed b a g z θ
              + (canonW q z θ * Srest f g a b z θ * Work.Spaces.mixed b a g z θ
                + canonW q z θ * Sdel f g a b z θ * Work.Spaces.mixed b a g z θ))
          = (∫ θ in Work.Spaces.Iθ,
              canonW q z θ * Smain f g a b z θ * Work.Spaces.mixed b a g z θ)
            + (∫ θ in Work.Spaces.Iθ,
              canonW q z θ * Srest f g a b z θ * Work.Spaces.mixed b a g z θ
                + canonW q z θ * Sdel f g a b z θ * Work.Spaces.mixed b a g z θ) :=
        MeasureTheory.integral_add (hsliceA z hz0.le)
          ((hsliceR z hz0.le).add (hsliceD z hz0.le))
      have hBC : (∫ θ in Work.Spaces.Iθ,
              canonW q z θ * Srest f g a b z θ * Work.Spaces.mixed b a g z θ
                + canonW q z θ * Sdel f g a b z θ * Work.Spaces.mixed b a g z θ)
          = (∫ θ in Work.Spaces.Iθ,
              canonW q z θ * Srest f g a b z θ * Work.Spaces.mixed b a g z θ)
            + (∫ θ in Work.Spaces.Iθ,
              canonW q z θ * Sdel f g a b z θ * Work.Spaces.mixed b a g z θ) :=
        MeasureTheory.integral_add (hsliceR z hz0.le) (hsliceD z hz0.le)
      rw [hAB, hBC]
    rw [h1, h2, h3]
  have hFd_le : |∫ z in Work.Spaces.Iz, Fd z|
      ≤ 16 * ((Mf + MK) * Work.Spaces.HkSq α 4 g
          + Mg * (Work.FTS.Nonlin.Xn α f * Work.FTS.Nonlin.Xn α g))
        + Cd * α ^ (-(1 / 2 : ℝ))
            * (Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 1 f)
            * Work.Spaces.HkSq α 4 g := by
    rcases hqcase with hqη | hqγ'
    · have h := sdel_integral_le_of_eta (α := α) (f := f) (g := g) (a := a) (b := b) (q := q)
        (Mf := Mf) (MK := MK) (Mg := Mg) hα hα1 hMf0 hMK0 hMg0 hqnn hab hq0
        hqγ hqη hFsup hFσ hGsup hmf hmg4
      simp only [hFddef] at h ⊢
      simp only [Work.FTS.Nonlin.Xn] at h ⊢
      have hnn : 0 ≤ Cd * α ^ (-(1 / 2 : ℝ))
          * (Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 1 f)
          * Work.Spaces.HkSq α 4 g :=
        mul_nonneg (mul_nonneg (mul_nonneg hCd0.le (Real.rpow_nonneg hα.le _))
          (add_nonneg hXn_f_nn hKf_nn)) (Work.Spaces.HkSq_nonneg α 4 g)
      linarith
    · subst hqγ'
      by_cases hb2 : b ≤ 2
      · have hfd : Fd = fun _ => (0 : ℝ) := by
          rw [hFddef]
          funext z
          rw [show (fun θ => canonW (Work.Spaces.gam α) z θ * Sdel f g a b z θ
                * Work.Spaces.mixed b a g z θ) = fun _ => (0 : ℝ) from by
            funext θ
            rw [Sdel, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]
            ring]
          simp
        rw [hfd]
        simp only [MeasureTheory.integral_zero, abs_zero]
        have hnn : 0 ≤ 16 * ((Mf + MK) * Work.Spaces.HkSq α 4 g
            + Mg * (Work.FTS.Nonlin.Xn α f * Work.FTS.Nonlin.Xn α g))
            + Cd * α ^ (-(1 / 2 : ℝ))
              * (Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 1 f)
              * Work.Spaces.HkSq α 4 g := by
          have h1 : 0 ≤ (Mf + MK) * Work.Spaces.HkSq α 4 g :=
            mul_nonneg (add_nonneg hMf0 hMK0) (Work.Spaces.HkSq_nonneg α 4 g)
          have h2 : 0 ≤ Mg * (Work.FTS.Nonlin.Xn α f * Work.FTS.Nonlin.Xn α g) :=
            mul_nonneg hMg0 (mul_nonneg hXn_f_nn hXn_g_nn)
          have h3 : 0 ≤ Cd * α ^ (-(1 / 2 : ℝ))
              * (Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 1 f)
              * Work.Spaces.HkSq α 4 g :=
            mul_nonneg (mul_nonneg (mul_nonneg hCd0.le (Real.rpow_nonneg hα.le _))
              (add_nonneg hXn_f_nn hKf_nn)) (Work.Spaces.HkSq_nonneg α 4 g)
          linarith
        linarith
      · have ha0 : a ≠ 0 := by
          intro h0
          exact absurd (hq0 h0) (not_le.mpr (eta_lt_gam_of_pos hα))
        have ha1 : a = 1 := by omega
        have hb3 : b = 3 := by omega
        have h := sdel_integral_le_of_gam_hon (α := α) (Cd := Cd) (f := f) (g := g) hα hα1 hf
          hGsm hmg4
          (fun q hq0 hqγ => hCd α q f g hα hα1 hq0 hqγ hf.1 hf.2.1 hf.2.2 hGsm hmg4 hmg5 hdec)
        have hFdval : (∫ z in Work.Spaces.Iz, Fd z)
            = (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
                canonW (Work.Spaces.gam α) z θ * Sdel f g 1 3 z θ
                  * Work.Spaces.mixed 3 1 g z θ) := by
          simp only [hFddef]
          rw [ha1, hb3]
        rw [hFdval]
        have hnn : 0 ≤ 16 * ((Mf + MK) * Work.Spaces.HkSq α 4 g
            + Mg * (Work.FTS.Nonlin.Xn α f * Work.FTS.Nonlin.Xn α g)) := by
          have h1 : 0 ≤ (Mf + MK) * Work.Spaces.HkSq α 4 g :=
            mul_nonneg (add_nonneg hMf0 hMK0) (Work.Spaces.HkSq_nonneg α 4 g)
          have h2 : 0 ≤ Mg * (Work.FTS.Nonlin.Xn α f * Work.FTS.Nonlin.Xn α g) :=
            mul_nonneg hMg0 (mul_nonneg hXn_f_nn hXn_g_nn)
          linarith
        linarith
  have hFL_eq : (∫ z in Work.Spaces.Iz, FL z)
      = ∫ z in Work.Spaces.Iz, (FA z + (Fr z + Fd z)) :=
    MeasureTheory.integral_congr_ae (ae_of_forall_Ioi (fun z hz => hsplit z hz))
  have hb1 : |∫ z in Work.Spaces.Iz, FL z|
      ≤ |∫ z in Work.Spaces.Iz, FA z| + |∫ z in Work.Spaces.Iz, (Fr z + Fd z)| := by
    rw [hFL_eq]
    exact absIntegralAddLe (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (f := FA) (g := fun z => Fr z + Fd z) hSmain.1
  have hb2 : |∫ z in Work.Spaces.Iz, (Fr z + Fd z)|
      ≤ |∫ z in Work.Spaces.Iz, Fr z| + |∫ z in Work.Spaces.Iz, Fd z| :=
    absIntegralAddLe (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (f := Fr) (g := Fd) hSrest.1
  have htotal : |∫ z in Work.Spaces.Iz, FL z|
      ≤ Csm * Mf * Work.Spaces.HkSq α 4 g
        + (6400 * ((Mf + MK) * Work.Spaces.HkSq α 4 g
              + Mg * (Work.FTS.Nonlin.Xn α f * Work.FTS.Nonlin.Xn α g))
          + (16 * ((Mf + MK) * Work.Spaces.HkSq α 4 g
                + Mg * (Work.FTS.Nonlin.Xn α f * Work.FTS.Nonlin.Xn α g))
            + Cd * α ^ (-(1 / 2 : ℝ))
                * (Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 1 f)
                * Work.Spaces.HkSq α 4 g)) := by
    have h1 : |∫ z in Work.Spaces.Iz, FA z| ≤ Csm * Mf * Work.Spaces.HkSq α 4 g := by
      simpa only [hFAdef] using hSmain.2
    have h2 : |∫ z in Work.Spaces.Iz, Fr z| ≤ 6400 * ((Mf + MK) * Work.Spaces.HkSq α 4 g
        + Mg * (Work.FTS.Nonlin.Xn α f * Work.FTS.Nonlin.Xn α g)) := by
      simpa only [hFrdef] using hSrest.2
    linarith [hb1, hb2, h1, h2, hFd_le]
  have hsq10 : Real.sqrt 10 ≤ 10 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10), Real.sqrt_nonneg 10]
  have hr1 : (1 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := by
    have h := Real.rpow_le_rpow_of_exponent_ge hα hα1 (by norm_num : (-(1 / 2 : ℝ)) ≤ 0)
    simpa using h
  have hr0 : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
  have hMfeq : Mf = Cs * (Real.sqrt 10 * α ^ (-(1 / 2 : ℝ))) * Work.FTS.Nonlin.Xn α f := by
    rw [hMfdef, show Cs / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α f
        = Cs * (1 / Real.sqrt (Work.Spaces.gam α - 1)) * Work.FTS.Nonlin.Xn α f from by ring,
      Work.FTS.TransportS.T2Sup.one_div_sqrt_gam_sub_one hα]
  have hMgeq : Mg = Cg * (Real.sqrt 10 * α ^ (-(1 / 2 : ℝ))) * Work.FTS.Nonlin.Xn α g := by
    rw [hMgdef, show Cg / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α g
        = Cg * (1 / Real.sqrt (Work.Spaces.gam α - 1)) * Work.FTS.Nonlin.Xn α g from by ring,
      Work.FTS.TransportS.T2Sup.one_div_sqrt_gam_sub_one hα]
  have harith := slot_arith_hon (r := α ^ (-(1 / 2 : ℝ))) (Xf := Work.FTS.Nonlin.Xn α f)
    (Kf := Work.FTS.VocabO.CoefTh 1 f) (Xg := Work.FTS.Nonlin.Xn α g)
    (Cs := Cs) (Cl := Cl) (Cg := Cg) (Cd := Cd) (Csm := Csm)
    hr1 hr0 hXn_f_nn hKf_nn hXn_g_nn hCs0.le hCl0.le hCg0 hCd0.le (by linarith) hsq10
  rw [hMfeq, hMgeq, hMKdef, ← Xn_sq α g] at htotal
  exact le_trans htotal harith

end Work.FTS.StrongPersist.N6Trans.Hon
