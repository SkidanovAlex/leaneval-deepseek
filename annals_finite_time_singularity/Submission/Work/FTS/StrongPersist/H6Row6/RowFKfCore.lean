/- # `H6Row6/RowFKfCore` — the Leibniz expansion and the angular splitting -/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Row6.RowFKfAux
import Submission.Work.FTS.StrongPersist.H6Row6.RowFKfAux2
import Submission.Work.FTS.StrongPersist.H6Row6.FkRowPrices
import Submission.Work.FTS.StrongPersist.H6Row6.fkSlotShift

import Submission.Work.FTS.StrongPersist.H6Row6.fkPairCSae
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkThetaEnd
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkThetaAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.fkPairingSup
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.fkSlotSqInt
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.RadAux.leibniz_rad_mixed_cd6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.RadAux.leibniz_rad_Dz_cd6
import Submission.Work.FTS.StrongPersist.H6Rows.piecesC6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.DzIter_FK_eq_ae
import Submission.Work.FTS.TransportS.T2SupB2.mixed_pointwise_le_Xn
import Submission.Work.FTS.VocabO
import Submission.Work.Construction.Defs

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
