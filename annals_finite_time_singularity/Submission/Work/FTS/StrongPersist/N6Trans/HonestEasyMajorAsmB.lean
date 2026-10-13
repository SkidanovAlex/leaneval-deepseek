/-
The per-summand bounds of the open-class (honest) assembly.
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
import Submission.Work.FTS.StrongPersist.N6Trans.HonestEasyMajorAsmA
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.ExcBoundOpen

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

/-! ## The per-summand bounds -/

/-- Each `D_z`-slot Leibniz summand (with the hard one removed) is integrable on the product
measure and bounded by `16` times the total. -/
theorem xD_summand_bound_q_o (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f g : ℝ → ℝ → ℝ)
    (Kf Kg K3 : ℝ) (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hdecg : Work.Spaces.DecayAll 4 g)
    (hmemf : Work.Spaces.HkMem α 4 f) (hmemg : Work.Spaces.HkMem α 4 g)
    (hKf : ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed b a f z θ| ≤ Kf)
    (hKg : ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed b a g z θ| ≤ Kg)
    (hKf0 : 0 ≤ Kf) (hKg0 : 0 ≤ Kg) (hK3 : 0 ≤ K3) (i b : ℕ) (hi : i ≤ 4) (hbi : b ≤ i) :
    MeasureTheory.Integrable
        (fun p : ℝ × ℝ => if i = 4 ∧ b = 0 then 0 else |xD f g i b p.1 p.2|)
        Work.FTS.H2.pm ∧
      ∫ p, (if i = 4 ∧ b = 0 then 0 else |xD f g i b p.1 p.2|) ∂Work.FTS.H2.pm
        ≤ 16 * TTot α f g Kf Kg K3 := by
  have hT := TTot_nonneg α f g Kf Kg K3 hKf0 hKg0 hK3
  by_cases hcase : i = 4 ∧ b = 0
  · have hz : (fun p : ℝ × ℝ => if i = 4 ∧ b = 0 then 0 else |xD f g i b p.1 p.2|)
        = fun _ => 0 := by funext p; rw [if_pos hcase]
    rw [hz]
    refine ⟨integrable_zero _ _ _, ?_⟩
    rw [MeasureTheory.integral_zero]
    exact mul_nonneg (by norm_num) hT
  · have hz : (fun p : ℝ × ℝ => if i = 4 ∧ b = 0 then 0 else |xD f g i b p.1 p.2|)
        = fun p => |xD f g i b p.1 p.2| := by funext p; rw [if_neg hcase]
    rw [hz]
    have hch : (i.choose b : ℝ) ≤ 16 := choose_le_16 hi hbi
    have hc0 : 0 ≤ (i.choose b : ℝ) := by positivity
    by_cases hb2 : b ≤ 2
    · have hib : i - b ≤ 3 := by
        by_contra hcon
        push_neg at hcon
        exact hcase ⟨by omega, by omega⟩
      obtain ⟨hslot_int, hslot_le⟩ := xD_Kf_int_q_o α g Kf hKf0 hg hmemg i b hi hib
      have hle : ∀ᵐ p ∂Work.FTS.H2.pm, |xD f g i b p.1 p.2| ≤ (i.choose b : ℝ) *
          (Kf * ((|Work.Spaces.mixed (i - b) 1 g p.1 p.2| * Wm α p.1 p.2)
            * (|Work.Spaces.DzIter i g p.1 p.2| * Whz p.1 p.2))) := by
        filter_upwards [ae_pm_z_pos_o, ae_pm_theta_mem_Ioo] with p hzpos hθ
        have hpt := xD_Kf_pt α hα f g Kf hKf0 hKf i b hi hbi hib hb2 p.1 p.2 hzpos hθ.1 hθ.2
        calc |xD f g i b p.1 p.2|
            ≤ (i.choose b : ℝ) * Kf * ((|Work.Spaces.mixed (i - b) 1 g p.1 p.2| * Wm α p.1 p.2)
              * (|Work.Spaces.DzIter i g p.1 p.2| * Whz p.1 p.2)) := hpt
          _ = (i.choose b : ℝ) * (Kf * ((|Work.Spaces.mixed (i - b) 1 g p.1 p.2| * Wm α p.1 p.2)
              * (|Work.Spaces.DzIter i g p.1 p.2| * Whz p.1 p.2))) := by ring
      obtain ⟨hint, hbd⟩ := xD_finish (f := f) (g := g) (i := i) (b := b) (c := (i.choose b : ℝ))
        (K := Kf * Work.Spaces.HkNorm α 4 g * Work.Spaces.HkNorm α 4 g)
        (S := fun p : ℝ × ℝ => Kf * ((|Work.Spaces.mixed (i - b) 1 g p.1 p.2| * Wm α p.1 p.2)
          * (|Work.Spaces.DzIter i g p.1 p.2| * Whz p.1 p.2)))
        hc0 hslot_int hslot_le hle (abs_aesm_pm (xD_aesm_q_o f g hf hg i b))
      refine ⟨hint, ?_⟩
      have hK : Kf * Work.Spaces.HkNorm α 4 g * Work.Spaces.HkNorm α 4 g
          = Kf * Work.Spaces.HkSq α 4 g := by
        have h2 : Work.Spaces.HkNorm α 4 g * Work.Spaces.HkNorm α 4 g
            = Work.Spaces.HkSq α 4 g := Real.mul_self_sqrt (Work.Spaces.HkSq_nonneg α 4 g)
        rw [mul_assoc, h2]
      calc ∫ p, |xD f g i b p.1 p.2| ∂Work.FTS.H2.pm
          ≤ (i.choose b : ℝ) * (Kf * Work.Spaces.HkNorm α 4 g * Work.Spaces.HkNorm α 4 g) := hbd
        _ = (i.choose b : ℝ) * (Kf * Work.Spaces.HkSq α 4 g) := by rw [hK]
        _ ≤ 16 * (Kf * Work.Spaces.HkSq α 4 g) :=
            mul_le_mul_of_nonneg_right hch (mul_nonneg hKf0 (Work.Spaces.HkSq_nonneg α 4 g))
        _ ≤ 16 * TTot α f g Kf Kg K3 :=
            mul_le_mul_of_nonneg_left (le_TTot_Kf α f g Kf Kg K3 hKg0 hK3) (by norm_num)
    · have hb3 : 3 ≤ b := by omega
      obtain ⟨hslot_int, hslot_le⟩ := xD_Kg_int_q_o α f g Kg hKg0 hf hg hmemf hmemg i b hi hb3 hbi
      have hle : ∀ᵐ p ∂Work.FTS.H2.pm, |xD f g i b p.1 p.2| ≤ (i.choose b : ℝ) *
          (Kg * ((|Work.Spaces.DzIter b f p.1 p.2| * Whz p.1 p.2)
            * (|Work.Spaces.DzIter i g p.1 p.2| * Whz p.1 p.2))) := by
        filter_upwards [ae_pm_z_pos_o, ae_pm_theta_mem_Ioo] with p hzpos hθ
        have hpt := xD_Kg_pt α hα f g Kg hKg0 hKg i b hi hbi hb3 p.1 p.2 hzpos hθ.1 hθ.2
        calc |xD f g i b p.1 p.2|
            ≤ (i.choose b : ℝ) * Kg * ((|Work.Spaces.DzIter b f p.1 p.2| * Whz p.1 p.2)
              * (|Work.Spaces.DzIter i g p.1 p.2| * Whz p.1 p.2)) := hpt
          _ = (i.choose b : ℝ) * (Kg * ((|Work.Spaces.DzIter b f p.1 p.2| * Whz p.1 p.2)
              * (|Work.Spaces.DzIter i g p.1 p.2| * Whz p.1 p.2))) := by ring
      obtain ⟨hint, hbd⟩ := xD_finish (f := f) (g := g) (i := i) (b := b) (c := (i.choose b : ℝ))
        (K := Kg * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 4 g)
        (S := fun p : ℝ × ℝ => Kg * ((|Work.Spaces.DzIter b f p.1 p.2| * Whz p.1 p.2)
          * (|Work.Spaces.DzIter i g p.1 p.2| * Whz p.1 p.2)))
        hc0 hslot_int hslot_le hle (abs_aesm_pm (xD_aesm_q_o f g hf hg i b))
      refine ⟨hint, ?_⟩
      calc ∫ p, |xD f g i b p.1 p.2| ∂Work.FTS.H2.pm
          ≤ (i.choose b : ℝ) * (Kg * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 4 g) := hbd
        _ ≤ 16 * (Kg * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 4 g) :=
            mul_le_mul_of_nonneg_right hch
              (mul_nonneg (mul_nonneg hKg0 (Work.Spaces.HkNorm_nonneg α 4 f))
                (Work.Spaces.HkNorm_nonneg α 4 g))
        _ ≤ 16 * TTot α f g Kf Kg K3 :=
            mul_le_mul_of_nonneg_left (le_TTot_Kg α f g Kf Kg K3 hKf0 hK3) (by norm_num)

/-- Each mixed-slot Leibniz summand (with the hard ones removed) is integrable on the product
measure and bounded by `256` times the total. -/
theorem yM_summand_bound_q_o (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f g : ℝ → ℝ → ℝ)
    (Kf Kg K3 : ℝ) (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hdecg : Work.Spaces.DecayAll 4 g)
    (hmemf : Work.Spaces.HkMem α 4 f) (hmemg : Work.Spaces.HkMem α 4 g)
    (hKf : ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed b a f z θ| ≤ Kf)
    (hKg : ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed b a g z θ| ≤ Kg)
    (hKf0 : 0 ≤ Kf) (hKg0 : 0 ≤ Kg) (hK3 : 0 ≤ K3)
    (hGint : MeasureTheory.IntegrableOn
      (fun z => (Work.FTS.H2.supAbsThO (Work.Spaces.DzIter 3 f) z * Work.Spaces.w z) ^ 2)
      Work.Spaces.Iz)
    (hGle : (∫ z in Work.Spaces.Iz,
      (Work.FTS.H2.supAbsThO (Work.Spaces.DzIter 3 f) z * Work.Spaces.w z) ^ 2) ≤ K3)
    (i j a b : ℕ) (hi4 : i ≤ 4) (hj4 : j ≤ 4) (hai : a ≤ i) (hbj : b ≤ j) :
    MeasureTheory.Integrable
        (fun p : ℝ × ℝ => if 1 ≤ i ∧ i + j ≤ 4 then
          (if a = 0 ∧ b = 0 ∧ i + j = 4 then 0 else |yM α f g i j a b p.1 p.2|) else 0)
        Work.FTS.H2.pm ∧
      ∫ p, (if 1 ≤ i ∧ i + j ≤ 4 then
          (if a = 0 ∧ b = 0 ∧ i + j = 4 then 0 else |yM α f g i j a b p.1 p.2|) else 0)
          ∂Work.FTS.H2.pm
        ≤ 256 * TTot α f g Kf Kg K3 := by
  have hT := TTot_nonneg α f g Kf Kg K3 hKf0 hKg0 hK3
  by_cases houter : 1 ≤ i ∧ i + j ≤ 4
  · have hzo : (fun p : ℝ × ℝ => if 1 ≤ i ∧ i + j ≤ 4 then
          (if a = 0 ∧ b = 0 ∧ i + j = 4 then 0 else |yM α f g i j a b p.1 p.2|) else 0)
        = fun p => (if a = 0 ∧ b = 0 ∧ i + j = 4 then 0
            else |yM α f g i j a b p.1 p.2|) := by
      funext p; rw [if_pos houter]
    rw [hzo]
    obtain ⟨hi1, hij4⟩ := houter
    by_cases hex : a = 0 ∧ b = 0 ∧ i + j = 4
    · have hz : (fun p : ℝ × ℝ =>
          if a = 0 ∧ b = 0 ∧ i + j = 4 then 0 else |yM α f g i j a b p.1 p.2|)
          = fun _ => 0 := by funext p; rw [if_pos hex]
      rw [hz]
      refine ⟨integrable_zero _ _ _, ?_⟩
      rw [MeasureTheory.integral_zero]
      exact mul_nonneg (by norm_num) hT
    · have hz : (fun p : ℝ × ℝ =>
          if a = 0 ∧ b = 0 ∧ i + j = 4 then 0 else |yM α f g i j a b p.1 p.2|)
          = fun p => |yM α f g i j a b p.1 p.2| := by funext p; rw [if_neg hex]
      rw [hz]
      have hch : (i.choose a : ℝ) * (j.choose b : ℝ) ≤ 256 :=
        choose_mul_le_256 hi4 hai hj4 hbj
      have hc0 : 0 ≤ (i.choose a : ℝ) * (j.choose b : ℝ) := by positivity
      by_cases hab2 : a + b ≤ 2
      · obtain ⟨hslot_int, hslot_le⟩ := yM_Kf_int_q_o α g Kf hKf0 hg hmemg i j a b hi1 hij4
          hai hbj hex
        have hle : ∀ᵐ p ∂Work.FTS.H2.pm, |yM α f g i j a b p.1 p.2|
            ≤ ((i.choose a : ℝ) * (j.choose b : ℝ)) *
              (Kf * ((|Work.Spaces.mixed (j - b) (i - a + 1) g p.1 p.2| * Wm α p.1 p.2)
                * (|Work.Spaces.mixed j i g p.1 p.2| * Wm α p.1 p.2))) := by
          filter_upwards [ae_pm_z_pos_o, ae_pm_theta_mem_Ioo] with p hzpos hθ
          have hpt := yM_Kf_pt α f g Kf hKf0 hKf i j a b hi1 hij4 hai hbj hab2 p.1 p.2 hzpos
            hθ.1 hθ.2
          calc |yM α f g i j a b p.1 p.2|
              ≤ (i.choose a : ℝ) * (j.choose b : ℝ) * Kf
                * ((|Work.Spaces.mixed (j - b) (i - a + 1) g p.1 p.2| * Wm α p.1 p.2)
                  * (|Work.Spaces.mixed j i g p.1 p.2| * Wm α p.1 p.2)) := hpt
            _ = ((i.choose a : ℝ) * (j.choose b : ℝ))
                * (Kf * ((|Work.Spaces.mixed (j - b) (i - a + 1) g p.1 p.2| * Wm α p.1 p.2)
                  * (|Work.Spaces.mixed j i g p.1 p.2| * Wm α p.1 p.2))) := by ring
        obtain ⟨hint, hbd⟩ := yM_finish hc0 hslot_int hslot_le hle
          (abs_aesm_pm (yM_aesm_q_o α f g hf hg i j a b))
        refine ⟨hint, ?_⟩
        have hK : Kf * Work.Spaces.HkNorm α 4 g * Work.Spaces.HkNorm α 4 g
            = Kf * Work.Spaces.HkSq α 4 g := by
          have h2 : Work.Spaces.HkNorm α 4 g * Work.Spaces.HkNorm α 4 g
              = Work.Spaces.HkSq α 4 g := Real.mul_self_sqrt (Work.Spaces.HkSq_nonneg α 4 g)
          rw [mul_assoc, h2]
        calc ∫ p, |yM α f g i j a b p.1 p.2| ∂Work.FTS.H2.pm
            ≤ ((i.choose a : ℝ) * (j.choose b : ℝ))
                * (Kf * Work.Spaces.HkNorm α 4 g * Work.Spaces.HkNorm α 4 g) := hbd
          _ = ((i.choose a : ℝ) * (j.choose b : ℝ)) * (Kf * Work.Spaces.HkSq α 4 g) := by rw [hK]
          _ ≤ 256 * (Kf * Work.Spaces.HkSq α 4 g) :=
              mul_le_mul_of_nonneg_right hch (mul_nonneg hKf0 (Work.Spaces.HkSq_nonneg α 4 g))
          _ ≤ 256 * TTot α f g Kf Kg K3 :=
              mul_le_mul_of_nonneg_left (le_TTot_Kf α f g Kf Kg K3 hKg0 hK3) (by norm_num)
      · by_cases ha1 : 1 ≤ a
        · have hab3 : 3 ≤ a + b := by omega
          obtain ⟨hslot_int, hslot_le⟩ := yM_Kg_int_q_o α f g Kg hKg0 hf hg hmemf hmemg i j a b
            hi1 hij4 hai hbj ha1 hab3
          have hle : ∀ᵐ p ∂Work.FTS.H2.pm, |yM α f g i j a b p.1 p.2|
              ≤ ((i.choose a : ℝ) * (j.choose b : ℝ)) *
                (Kg * ((|Work.Spaces.mixed b a f p.1 p.2| * Wm α p.1 p.2)
                  * (|Work.Spaces.mixed j i g p.1 p.2| * Wm α p.1 p.2))) := by
            filter_upwards [ae_pm_z_pos_o, ae_pm_theta_mem_Ioo] with p hzpos hθ
            have hpt := yM_Kg_mixed_pt α f g Kg hKg0 hKg i j a b hi1 hij4 hai hbj ha1 hab3 p.1
              p.2 hzpos hθ.1 hθ.2
            calc |yM α f g i j a b p.1 p.2|
                ≤ (i.choose a : ℝ) * (j.choose b : ℝ) * Kg
                  * ((|Work.Spaces.mixed b a f p.1 p.2| * Wm α p.1 p.2)
                    * (|Work.Spaces.mixed j i g p.1 p.2| * Wm α p.1 p.2)) := hpt
              _ = ((i.choose a : ℝ) * (j.choose b : ℝ))
                  * (Kg * ((|Work.Spaces.mixed b a f p.1 p.2| * Wm α p.1 p.2)
                    * (|Work.Spaces.mixed j i g p.1 p.2| * Wm α p.1 p.2))) := by ring
          obtain ⟨hint, hbd⟩ := yM_finish hc0 hslot_int hslot_le hle
            (abs_aesm_pm (yM_aesm_q_o α f g hf hg i j a b))
          refine ⟨hint, ?_⟩
          calc ∫ p, |yM α f g i j a b p.1 p.2| ∂Work.FTS.H2.pm
              ≤ ((i.choose a : ℝ) * (j.choose b : ℝ))
                  * (Kg * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 4 g) := hbd
            _ ≤ 256 * (Kg * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 4 g) :=
                mul_le_mul_of_nonneg_right hch
                  (mul_nonneg (mul_nonneg hKg0 (Work.Spaces.HkNorm_nonneg α 4 f))
                    (Work.Spaces.HkNorm_nonneg α 4 g))
            _ ≤ 256 * TTot α f g Kf Kg K3 :=
                mul_le_mul_of_nonneg_left (le_TTot_Kg α f g Kf Kg K3 hKf0 hK3) (by norm_num)
        · -- the exceptional summand `(i,j,a,b) = (1,3,0,3)`
          have ha0 : a = 0 := by omega
          subst ha0
          have hb3 : 3 ≤ b := by omega
          have hj3 : j = 3 := by omega
          subst hj3
          have hi1' : i = 1 := by omega
          subst hi1'
          have hb3' : b = 3 := by omega
          subst hb3'
          obtain ⟨⟨hexc_int, hexc_le⟩, _⟩ := Work.FTS.StrongPersist.N6Trans.OpenTwins.ExcBoundOpen α f g K3 hα hα1 hf hg
            hdecg hmemf hmemg hGint hGle hK3
          have hyMeq : (fun p : ℝ × ℝ => |Work.Spaces.DzIter 3 f p.1 p.2
                * Work.Spaces.mixed 0 2 g p.1 p.2
                * Work.Spaces.mixed 3 1 g p.1 p.2 * (Wm α p.1 p.2) ^ 2|)
              =ᵐ[Work.FTS.H2.pm] fun p => |yM α f g 1 3 0 3 p.1 p.2| := by
            filter_upwards with p
            have hinner : yM α f g 1 3 0 3 p.1 p.2
                = Work.Spaces.DzIter 3 f p.1 p.2 * Work.Spaces.mixed 0 2 g p.1 p.2
                  * Work.Spaces.mixed 3 1 g p.1 p.2 * (Wm α p.1 p.2) ^ 2 := by
              simp only [yM, Work.Spaces.mixed_zero_right]
              norm_num
              try ring
            exact (congrArg abs hinner).symm
          refine ⟨hexc_int.congr hyMeq, ?_⟩
          rw [← integral_congr_ae hyMeq]
          have h5 : Real.sqrt K3 * Work.Spaces.HkSq α 4 g ≤ TTot α f g Kf Kg K3 :=
            le_TTot_sqrt α f g Kf Kg K3 hKf0 hKg0
          have h6 : TTot α f g Kf Kg K3 ≤ 256 * TTot α f g Kf Kg K3 := by linarith
          linarith
  · have hz : (fun p : ℝ × ℝ => if 1 ≤ i ∧ i + j ≤ 4 then
        (if a = 0 ∧ b = 0 ∧ i + j = 4 then 0 else |yM α f g i j a b p.1 p.2|) else 0)
        = fun _ => 0 := by funext p; rw [if_neg houter]
    rw [hz]
    refine ⟨integrable_zero _ _ _, ?_⟩
    rw [MeasureTheory.integral_zero]
    exact mul_nonneg (by norm_num) hT


end Work.FTS.StrongPersist.N6Trans.HonestEasyMajorAux
