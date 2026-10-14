import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.fkPairingSup
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkShiftHigh_shiftF
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkSlotInt
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkThetaAux
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.DzIter_FK_eq_ae
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.NSplit6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzdIterBound
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.NfkSmooth
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBound
import Submission.Work.FTS.TransportS.T2SupB2.mixed_pointwise_le_Xn
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.FTS_MuLamOK.Main
import Submission.Work.FTS_MuLamOK.Rows.Rl1Open
import Submission.Work.FTS_RegExport.RXT.StarVopWlInf
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat
import Submission.Work.Spaces.ThetaAgmon.agmon_interval
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Row6.RowFKfCore =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Row6

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

noncomputable section

/-! ## The expansion of `D_z^bD_θ^a ((FK f)·D_θf)` -/

/-- **The `z`-Leibniz expansion of the `(f,K)`-row.** -/
theorem fkRow_expand1 {α : ℝ} {f : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem7 : Work.Spaces.HkMem α 7 f)
    {a b : ℕ} (hab : a + b ≤ 6) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.mixed b a
          (fun z θ => Work.Construction.FK f z * Work.Spaces.Dth f z θ) z θ
        = ∑ b₁ ∈ Finset.range (b + 1), (b.choose b₁ : ℝ)
            * (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z
                * Work.Spaces.mixed (b - b₁) (a + 1) f z θ) := by
  have hRcd : ContDiffOn ℝ 6
      (Function.uncurry (fun z (_ : ℝ) => Work.Construction.FK f z))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongPersist.H6Rows.co6_FK_radial hα hα1 hsm hmem7
  have hgdth : ContDiffOn ℝ 6 (Function.uncurry (Work.Spaces.Dth f))
      Work.FTS.EllipticEst.Q0 := hsm.Dth.forall 6
  have hmixed_shift : ∀ j : ℕ,
      Work.Spaces.mixed j a (Work.Spaces.Dth f) = Work.Spaces.mixed j (a + 1) f := by
    intro j
    show Work.Spaces.DzIter j (Work.Spaces.DthIter a (Work.Spaces.Dth f))
        = Work.Spaces.DzIter j (Work.Spaces.DthIter (a + 1) f)
    rw [dthIter_succ_shift a f]
  intro z θ hz hθ0 hθ1
  by_cases ha : 1 ≤ a
  · have h := Work.FTS.StrongPersist.H6Rows.Npair6SupAux.RadAux.leibniz_rad_mixed_cd6
      (r := fun z => Work.Construction.FK f z) (g := Work.Spaces.Dth f)
      hRcd hgdth (j := b) (i := a) ha hab z θ hz hθ0 hθ1
    rw [h]
    refine Finset.sum_congr rfl fun b₁ _ => ?_
    rw [hmixed_shift (b - b₁)]
  · have ha0 : a = 0 := by omega
    subst ha0
    rw [Work.Spaces.mixed_zero_right]
    have h := Work.FTS.StrongPersist.H6Rows.Npair6SupAux.RadAux.leibniz_rad_Dz_cd6
      (r := fun z => Work.Construction.FK f z) (g := Work.Spaces.Dth f)
      hRcd hgdth (j := b) (by omega) z θ hz hθ0 hθ1
    rw [h]
    exact Finset.sum_congr rfl fun b₁ _ => congrArg _ (by rfl)

/-- The expansion for the actual coefficient `-(1/2)·FK f·D_θf` of the target. -/
theorem fkRow_expand1_half {α : ℝ} {f : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem7 : Work.Spaces.HkMem α 7 f)
    {a b : ℕ} (hab : a + b ≤ 6) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.mixed b a
          (fun z θ => -(1 / 2) * Work.Construction.FK f z * Work.Spaces.Dth f z θ) z θ
        = -(1 / 2) * ∑ b₁ ∈ Finset.range (b + 1), (b.choose b₁ : ℝ)
            * (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z
                * Work.Spaces.mixed (b - b₁) (a + 1) f z θ) := by
  intro z θ hz hθ0 hθ1
  have hfun : (fun z θ => -(1 / 2) * Work.Construction.FK f z * Work.Spaces.Dth f z θ)
      = fun z θ => -(1 / 2) * (Work.Construction.FK f z * Work.Spaces.Dth f z θ) := by
    funext z θ; ring
  have hlin : Work.Spaces.mixed b a
        (fun z θ => -(1 / 2) * (Work.Construction.FK f z * Work.Spaces.Dth f z θ)) z θ
      = -(1 / 2) * Work.Spaces.mixed b a
          (fun z θ => Work.Construction.FK f z * Work.Spaces.Dth f z θ) z θ := by
    rw [mixed_const_mul_row]
  rw [hfun, hlin, fkRow_expand1 hα hα1 hsm hmem7 hab z θ hz hθ0 hθ1]

/-! ## The angular splitting of a single slice -/

/-- **The `θ`-splitting of one slice of the pairing.**  For `z > 0` the inner `θ`-integral of
the pairing is the (finite) sum of the Leibniz summands. -/
theorem fkRow_inner_eq {α : ℝ} {f : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (h7 : Work.Spaces.HkMem α 7 f)
    {a b : ℕ} (hab : a + b ≤ 6) {ρ : ℝ → ℝ → ℝ}
    (hρ : Work.FTS.TransportS.IsLeafW α a ρ) {z : ℝ} (hz : 0 < z) :
    (∫ θ in Work.Spaces.Iθ, ρ z θ
        * Work.Spaces.mixed b a
            (fun z θ => -(1 / 2) * Work.Construction.FK f z * Work.Spaces.Dth f z θ) z θ
        * Work.Spaces.mixed b a f z θ)
      = ∑ k ∈ Finset.range (b + 1), (-(1 / 2)) * ((b.choose k : ℝ)
          * (Work.Elliptic.DzdIter k (fun z => Work.Construction.FK f z) z
              * ∫ θ in Work.Spaces.Iθ, ρ z θ * Work.Spaces.mixed (b - k) (a + 1) f z θ
                * Work.Spaces.mixed b a f z θ)) := by
  have haeθ : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := Work.FTS.IPGen.ip_ae_mem_Ioo_Iθ
  -- every Leibniz summand is `θ`-integrable
  have hβ : ∀ k : ℕ, MeasureTheory.Integrable (fun θ => (b.choose k : ℝ)
      * (Work.Elliptic.DzdIter k (fun z => Work.Construction.FK f z) z
          * (ρ z θ * Work.Spaces.mixed (b - k) (a + 1) f z θ
              * Work.Spaces.mixed b a f z θ)))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    intro k
    have hcont : ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2
        * Work.Spaces.mixed (b - k) (a + 1) f p.1 p.2
        * Work.Spaces.mixed b a f p.1 p.2)
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      ((Work.FTS.StrongPersist.H6Pair6Aux.continuousOn_leaf hρ).mul
        (hsm.mixed (b - k) (a + 1)).continuousOn).mul (hsm.mixed b a).continuousOn
    have haesm : MeasureTheory.AEStronglyMeasurable (fun θ => (b.choose k : ℝ)
        * (Work.Elliptic.DzdIter k (fun z => Work.Construction.FK f z) z
            * (ρ z θ * Work.Spaces.mixed (b - k) (a + 1) f z θ
                * Work.Spaces.mixed b a f z θ)))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      (((Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hz).const_mul
          (Work.Elliptic.DzdIter k (fun z => Work.Construction.FK f z) z)).const_mul
          ((b.choose k : ℝ)))
    refine MeasureTheory.Integrable.mono'
      (g := fun θ => (((b.choose k : ℝ)
        * |Work.Elliptic.DzdIter k (fun z => Work.Construction.FK f z) z|))
        * Work.Spaces.HkIntegrand α 7 f z θ) ?_ haesm ?_
    · exact (h7.1 z (Set.mem_Ici.mpr hz.le)).const_mul _
    · filter_upwards [haeθ] with θ hθ
      have hρ0 : 0 ≤ ρ z θ :=
        Work.FTS.StrongPersist.H6Pair6Aux.leaf_nonneg hρ z
          ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      have hVe := domLeaf_le_row (f := f) hα hρ (by omega) (by omega : (a + 1) + (b - k) ≤ 7)
        (Set.mem_Ici.mpr hz.le) hθ
      have hVf := domLeaf_le_row (f := f) hα hρ (le_refl a) (by omega : a + b ≤ 7)
        (Set.mem_Ici.mpr hz.le) hθ
      have hAM : |ρ z θ * Work.Spaces.mixed (b - k) (a + 1) f z θ
          * Work.Spaces.mixed b a f z θ| ≤ Work.Spaces.HkIntegrand α 7 f z θ := by
        rw [abs_mul, abs_mul, abs_of_nonneg hρ0]
        have h4 : |Work.Spaces.mixed (b - k) (a + 1) f z θ|
              * |Work.Spaces.mixed b a f z θ|
            ≤ ((Work.Spaces.mixed (b - k) (a + 1) f z θ) ^ 2
              + (Work.Spaces.mixed b a f z θ) ^ 2) / 2 := by
          have h2 := Work.Spaces.abs_mul_abs_le_half_add_sq
            (Work.Spaces.mixed (b - k) (a + 1) f z θ) (Work.Spaces.mixed b a f z θ)
          linarith [h2, sq_abs (Work.Spaces.mixed (b - k) (a + 1) f z θ),
            sq_abs (Work.Spaces.mixed b a f z θ)]
        have h3 : ρ z θ * |Work.Spaces.mixed (b - k) (a + 1) f z θ|
              * |Work.Spaces.mixed b a f z θ|
            ≤ ρ z θ * (((Work.Spaces.mixed (b - k) (a + 1) f z θ) ^ 2
                + (Work.Spaces.mixed b a f z θ) ^ 2) / 2) := by
          calc ρ z θ * |Work.Spaces.mixed (b - k) (a + 1) f z θ|
                * |Work.Spaces.mixed b a f z θ|
              = ρ z θ * (|Work.Spaces.mixed (b - k) (a + 1) f z θ|
                  * |Work.Spaces.mixed b a f z θ|) := by ring
            _ ≤ ρ z θ * (((Work.Spaces.mixed (b - k) (a + 1) f z θ) ^ 2
                  + (Work.Spaces.mixed b a f z θ) ^ 2) / 2) :=
                mul_le_mul_of_nonneg_left h4 hρ0
        linarith [h3, hVe, hVf]
      have hc0 : (0 : ℝ) ≤ (b.choose k : ℝ) := Nat.cast_nonneg _
      have hA0 : (0 : ℝ) ≤ |Work.Elliptic.DzdIter k (fun z => Work.Construction.FK f z) z| :=
        abs_nonneg _
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hc0]
      calc (b.choose k : ℝ)
            * (|Work.Elliptic.DzdIter k (fun z => Work.Construction.FK f z) z|
                * |ρ z θ * Work.Spaces.mixed (b - k) (a + 1) f z θ
                    * Work.Spaces.mixed b a f z θ|)
          ≤ (b.choose k : ℝ)
              * (|Work.Elliptic.DzdIter k (fun z => Work.Construction.FK f z) z|
                  * Work.Spaces.HkIntegrand α 7 f z θ) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hAM hA0) hc0
        _ = ((b.choose k : ℝ)
              * |Work.Elliptic.DzdIter k (fun z => Work.Construction.FK f z) z|)
            * Work.Spaces.HkIntegrand α 7 f z θ := by ring
  -- the rearranged identity
  have hkey : (fun θ => ρ z θ * Work.Spaces.mixed b a
        (fun z θ => -(1 / 2) * Work.Construction.FK f z * Work.Spaces.Dth f z θ) z θ
        * Work.Spaces.mixed b a f z θ)
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ => ∑ k ∈ Finset.range (b + 1), (-(1 / 2)) * ((b.choose k : ℝ)
        * (Work.Elliptic.DzdIter k (fun z => Work.Construction.FK f z) z
            * (ρ z θ * Work.Spaces.mixed (b - k) (a + 1) f z θ
                * Work.Spaces.mixed b a f z θ)))) := by
    filter_upwards [haeθ] with θ hθ
    rw [fkRow_expand1_half hα hα1 hsm h7 hab z θ hz hθ.1 hθ.2]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  calc (∫ θ in Work.Spaces.Iθ, ρ z θ
          * Work.Spaces.mixed b a
              (fun z θ => -(1 / 2) * Work.Construction.FK f z * Work.Spaces.Dth f z θ) z θ
          * Work.Spaces.mixed b a f z θ)
      = ∫ θ in Work.Spaces.Iθ, ∑ k ∈ Finset.range (b + 1), (-(1 / 2)) * ((b.choose k : ℝ)
          * (Work.Elliptic.DzdIter k (fun z => Work.Construction.FK f z) z
              * (ρ z θ * Work.Spaces.mixed (b - k) (a + 1) f z θ
                  * Work.Spaces.mixed b a f z θ))) := MeasureTheory.integral_congr_ae hkey
    _ = ∑ k ∈ Finset.range (b + 1), ∫ θ in Work.Spaces.Iθ, (-(1 / 2)) * ((b.choose k : ℝ)
          * (Work.Elliptic.DzdIter k (fun z => Work.Construction.FK f z) z
              * (ρ z θ * Work.Spaces.mixed (b - k) (a + 1) f z θ
                  * Work.Spaces.mixed b a f z θ))) := by
        refine MeasureTheory.integral_finsetSum _ (fun k _ => ?_)
        exact (hβ k).const_mul _
    _ = ∑ k ∈ Finset.range (b + 1), (-(1 / 2)) * ((b.choose k : ℝ)
          * (Work.Elliptic.DzdIter k (fun z => Work.Construction.FK f z) z
              * ∫ θ in Work.Spaces.Iθ, ρ z θ * Work.Spaces.mixed (b - k) (a + 1) f z θ
                * Work.Spaces.mixed b a f z θ)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [MeasureTheory.integral_const_mul]

end

end Work.FTS.StrongPersist.H6Row6
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.psi6LowSlice =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## The two halves of the level-`m` slice sum, as integrability statements

These are the a.e.-integrability side conditions needed to apply `MeasureTheory.integral_add`
to the two `Finset.range` sums of `lowSum`.  Each summand of the `γ`-weighted half is
integrable by `lowGamSlotIntegrable` (the `if`-branch being `0`), and each summand of the
`η`-weighted half by `fkSliceSup_slice_integrable`. -/

/-- Integrability of the `γ`-weighted angular half of the level-`m` slice sum. -/
theorem psi6LowMixedHalf_integrable {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    {m : ℕ} (hm : m ≤ 2) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.Integrable (fun θ : ℝ => ∑ i ∈ Finset.range (m + 1),
        ∑ j ∈ Finset.range (m + 1),
          if 1 ≤ i ∧ i + j ≤ m then (Work.Spaces.mixed j i f z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  refine MeasureTheory.integrable_finsetSum (Finset.range (m + 1)) (fun i _ => ?_)
  refine MeasureTheory.integrable_finsetSum (Finset.range (m + 1)) (fun j _ => ?_)
  by_cases hc : 1 ≤ i ∧ i + j ≤ m
  · simp only [if_pos hc]
    exact lowGamSlotIntegrable hα hα1 hF hmem hc.1 (by omega) hz
  · simp only [if_neg hc]
    simp

/-- Integrability of the `η`-weighted radial half of the level-`m` slice sum. -/
theorem psi6LowZHalf_integrable {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    {m : ℕ} (hm : m ≤ 2) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.Integrable (fun θ : ℝ => ∑ i ∈ Finset.range (m + 1),
        (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          * (Work.Spaces.mixed i 0 f z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  refine MeasureTheory.integrable_finsetSum (Finset.range (m + 1)) (fun i hi => ?_)
  have hi2 : i ≤ 2 := by
    have := Finset.mem_range.mp hi
    omega
  exact fkSliceSup_slice_integrable hα hF hmem (j := i) (i := 0) (by omega) hz

/-- **The level-`m` `lowSum` slice**, `m ≤ 2`: `∫_θ lowSum α m f z θ ≤ 36 · HkSq α 4 f`.
This is the sum of the two independent halves: the radial one
(`lowZSliceLe`, `≤ 9 · HkSq α 4 f`, `m+1 ≤ 3` slots) and the angular one
(`psi6LowMixedHalf`, `≤ 27 · HkSq α 4 f`). -/
theorem psi6LowSumSliceLe {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    {m : ℕ} (hm : m ≤ 2) {z : ℝ} (hz : 0 < z) :
    (∫ θ in Work.Spaces.Iθ, lowSum α m f z θ) ≤ 36 * Work.Spaces.HkSq α 4 f := by
  have hZint := psi6LowZHalf_integrable (α := α) hα hF hmem hm hz
  have hMint := psi6LowMixedHalf_integrable (α := α) hα hα1 hF hmem hm hz
  have hZ := lowZSliceLe (α := α) hα hF hmem hm hz
  have hM := psi6LowMixedHalf (α := α) hα hα1 hF hmem hm hz
  have hsplit : (∫ θ in Work.Spaces.Iθ, lowSum α m f z θ)
      = (∫ θ in Work.Spaces.Iθ, ∑ i ∈ Finset.range (m + 1),
            (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
              * (Work.Spaces.mixed i 0 f z θ) ^ 2)
        + ∫ θ in Work.Spaces.Iθ, ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
            if 1 ≤ i ∧ i + j ≤ m then (Work.Spaces.mixed j i f z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0 := by
    unfold lowSum
    exact MeasureTheory.integral_add hZint hMint
  rw [hsplit]
  refine le_trans (add_le_add hZ hM) ?_
  linarith [Work.Spaces.HkSq_nonneg α 4 f]

/-- **The low-level angular slice of `HkIntegrand`, uniformly in `z`.**

For a datum `f` of the open class lying honestly in `ℋ⁴` and `m ≤ 2`, at every `z > 0` the
angular slice of the level-`m` `ℋ`-integrand is bounded by `C · HkSq α 4 f · (w z)²`.

Route: `HkIntegrand α m f z θ = (w z)² · lowSum α m f z θ` a.e. on `Iθ`
(`HkIntegrand_eq_w_sq_mul_lowSum` / `ae_HkIntegrand_eq_w_sq_mul_lowSum` in `fkLowAux`), so
`∫_θ HkIntegrand α m f z θ = (w z)² · ∫_θ lowSum α m f z θ`; splitting the two `Finset.range`
sums of `lowSum` with `MeasureTheory.integral_finsetSum` (the `if`-branches by `by_cases`, the
else-branch being `0`) reduces to the slots: the radial ones `(j,i) = (i,0)` with `i ≤ m` are
`≤ 3 · HkSq α 4 f` by `fkSliceSup_sliceSupGraded` at `k = 4` (its hypothesis `i + 0 + 1 ≤ 4`
holds), integrable by `fkSliceSup_slice_integrable`; the mixed ones (`1 ≤ i`, `i + j ≤ m ≤ 2`,
i.e. only `(j,i) ∈ {(0,1),(1,1),(0,2)}`) are `≤ 3 · HkSq α 4 f` by
`H6Row6Gam.mixed_slice_z_le_three` (its hypothesis `i + j ≤ 3` holds), integrable by
`lowGamSlotIntegrable`. At most `(m+1) + 9 ≤ 12` slots occur, so `C = 36` works. -/
theorem psi6LowSlice : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1, ∀ (f : Work.FTS.Galerkin.Fn),
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    ∀ (m : ℕ), m ≤ 2 → ∀ z : ℝ, 0 < z →
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α m f z θ)
        ≤ C * Work.Spaces.HkSq α 4 f * (Work.Spaces.w z) ^ 2 := by
  refine ⟨36, by norm_num, ?_⟩
  intro α hαmem f hF hmem m hm z hz
  have hα : 0 < α := hαmem.1
  have hα1 : α ≤ 1 := hαmem.2
  have hlow := psi6LowSumSliceLe (α := α) hα hα1 hF hmem hm hz
  have h1 : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α m f z θ)
      = (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ, lowSum α m f z θ := by
    rw [MeasureTheory.integral_congr_ae (ae_HkIntegrand_eq_w_sq_mul_lowSum hα m f z),
      MeasureTheory.integral_const_mul]
  calc (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α m f z θ)
      = (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ, lowSum α m f z θ := h1
    _ ≤ (Work.Spaces.w z) ^ 2 * (36 * Work.Spaces.HkSq α 4 f) :=
        mul_le_mul_of_nonneg_left hlow (sq_nonneg _)
    _ = 36 * Work.Spaces.HkSq α 4 f * (Work.Spaces.w z) ^ 2 := by ring

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
end
end
