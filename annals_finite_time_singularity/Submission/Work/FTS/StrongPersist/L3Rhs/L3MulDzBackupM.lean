import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.zmollDzComm
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.integrableOn_term
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.StrongEps.blocks.L12_Fstar_add_open
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.tracePi4
import Submission.Work.FTS_RegExport.RXT.StarVopWlInf
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.H2.T1Q.SlotPtQ
import Submission.Work.H2.WPQ.m_term_le_smoothQuad
import Submission.Work.Spaces.HProductRule_bad_term
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.pz_mixed_mul_le_4
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollDom.zmollDzEq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.EllSol.PkgK5.K5c
open Work.Spaces (Dz pz)
open Work.EllipticEst.Core

local notation "Iθ" => Work.Spaces.Iθ

set_option maxHeartbeats 4000000

/-- **The engine applied to `G`**: the log-mollification commutes with `D_z`,
`D_z (zmoll G δ ε) z θ = zmoll (D_z G) δ ε z θ` for `z > 0`, `θ ∈ Iθ`. -/
theorem zmoll_dz_eq (G : ℝ → ℝ → ℝ) (hT : TraceClass G) (hF : FourInts G) (δ ε : ℝ)
    (hP : Params δ ε) :
    ∀ z : ℝ, 0 < z → ∀ θ ∈ Iθ,
      Dz (zmoll G δ ε) z θ = zmoll (Dz G) δ ε z θ := by
  obtain ⟨hsd1, hsd2, hsd3, hsd4, -, -, -⟩ := slice_data hT
  obtain ⟨C, hCpos, hCint, hCb, hCint', hCb'⟩ := sliceL1_bound hT hF
  have hCnn : (0 : ℝ) ≤ C := le_of_lt hCpos
  have hdnn : ∀ w : ℝ, 0 ≤ dIntS G w := by
    intro w
    rw [dIntS]
    exact mul_nonneg (sq_nonneg _) (MeasureTheory.setIntegral_nonneg
      (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc)
      (fun θ hθ => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)))
  set F₁ : ℝ → ℝ := fun w => C * MGf G w + C * (1 + dIntS G w) with hF₁def
  have hF₁int : ∀ a b : ℝ, 0 < a → a ≤ b → IntegrableOn F₁ (Set.Icc a b) := by
    intro a b ha hab
    rw [hF₁def]
    exact (hCint a b ha hab).add (hCint' a b ha hab)
  have hF₁b : ∀ w : ℝ, 0 < w → ∫ s in Iθ, |G w s| ≤ F₁ w := by
    intro w hw
    rw [hF₁def]
    exact (hCb w hw).trans (le_add_of_nonneg_right
      (mul_nonneg hCnn (by linarith [hdnn w])))
  have hF₁b' : ∀ w : ℝ, 0 < w → ∫ s in Iθ, |Dz G w s| ≤ F₁ w := by
    intro w hw
    rw [hF₁def]
    have hmg : (0 : ℝ) ≤ C * MGf G w := by
      rw [MGf]
      exact mul_nonneg hCnn (by positivity)
    exact (hCb' w hw).trans (le_add_of_nonneg_left hmg)
  have hc := zmoll_dz_comm (u := G) (F := F₁) hP hT.2.1 hT.2.2.1 hsd1 hT.1.continuousOn
    (fun w hw s hs => hT.1.hasDerivAt_slice hs hw) (hT.1.pz).continuousOn hF₁int hF₁b hF₁b'
    (fun w hw => (hsd2 w hw).integrableOn_compact isCompact_Icc)
  intro z hz θ hθ
  rw [hc z hz θ hθ]
  rw [show zmoll (Dz G) δ ε z θ
      = ∫ t : ℝ, sKer δ (Real.log z - t) * thMoll (Dz G) ε (Real.exp t) θ from rfl]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  show sKer δ (Real.log z - t)
      * (∫ s in Iθ, Kern (sKer ε) θ s * Dz G (Real.exp t) s)
    = sKer δ (Real.log z - t) * thMoll (Dz G) ε (Real.exp t) θ
  rw [← thMoll_fold (u := Dz G) (z := Real.exp t) (θ' := θ) hP.1 hP.2.1
    (hsd3 (Real.exp t)) (hsd4 (Real.exp t)) (hsd2 (Real.exp t) (Real.exp_pos t))
    (by linarith [hθ.1, Real.pi_pos]) (by linarith [hθ.2])]

end Work.FTS.EllSol.EllPkgAux.MollDom
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AeI1Fts.slice_rate =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `AeI1Fts/slice_rate` — the slicewise rate of `U = z∂_zu` at the two endpoints

For a datum `AeData α u G`, with the two `ℋ⁰`-honesties of the slots
`U u = z ∂_z u` and `V u = z ∂_z∂_θu = ∂_θ(U u)` (Clairaut), the angular slice of `U` obeys,
for almost every `z > 0`, the two endpoint rates

* `|U(z,θ)| ≤ C (∫_{0<θ'<θ} V(z,θ')² σ(θ'))^{1/2} θ^{(1+η)/2}`,
* `|U(z,θ)| ≤ C (∫_{θ<θ'<π/2} V(z,θ')² σ(θ'))^{1/2} (π/2-θ)^{(1+η)/2}`

with `σ = sigE = sin(2θ)^{-η}` and a universal constant `C` (`C = √2` outright).

## Proof

`Work.EllipticEst.Core.sliceBoundaryLimit` (the sharp boundary-rate lemma of the `TT`
workstream) gives, for a `C¹` slice `f` whose weighted derivative square `(f')²·thEta` is
integrable on `(0,π/2)`, two endpoint constants `c₀`, `c₁` with

`(f θ - c)² ≤ K θ^{1+η} ∫_{0<θ'<θ} (f')² thEta`,  resp. the `(π/2-θ)`-analogue, `K = 2`.

The two constants vanish because the trace lemma
`Work.FTS.EllipticEst.TT.AeI1.aeDzTraceHk` shows that `U u z ·` tends to `0` at both endpoints
for a.e. `z > 0` (the hypothesis on `z * ∂_θ∂_zu` is transported from `HkMem α 0 (V u)` by
Clairaut), so the two limits coincide with `0` by uniqueness.  Taking square roots
(`√f ≤ √(c^{1+η}A) = c^{(1+η)/2}√A` because `∫ (sin 2θ')^{η} ≤ (2θ)^{1+η}/(1+η)`) and
rewriting `∂_θ(U u z ·) = V u z ·` (Clairaut, on the open interval) and
`thEta = sigE` finishes.

-/

namespace Work.FTS.EllipticEst.AeI1Fts

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

local notation "Iθo" => Set.Ioo (0 : ℝ) (Real.pi / 2)

/-! ## The two angular weights agree -/


/-! ## Transport of `HkMem` along equality on the open quadrant -/



/-! ## Slice integrability of `V z θ' ² σ θ'` -/


/-! ## Nonnegativity of the slice energy -/



/-! ## From the squared rate to the square-root rate -/


/-! ## The per-slice rate -/


/-! ## The target -/


end

end Work.FTS.EllipticEst.AeI1Fts
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Rhs.L3MulDzBackupM =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs.L3MulDzBackupM

open Work.Spaces (Dz DzIter DthIter mixed Wt w wTheta HkIntegrand eta gam)

set_option autoImplicit false
set_option maxHeartbeats 1600000

open Work.FTS.OpenPkg.WProdWin

/-! ## Elementary angular algebra -/

private theorem sin_two_nonneg_of_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    0 ≤ Real.sin (2 * θ) :=
  (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])).le

private theorem phi_sq_b {α θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
      = (α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5) := by
  rw [mul_pow]
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_Ioo hθ
  have hss : ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2 = (Real.sin (2 * θ)) ^ (2 * α / 5) := by
    rw [show ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2
          = ((Real.sin (2 * θ)) ^ (α / 5)) ^ ((2 : ℝ)) from (Real.rpow_natCast _ 2).symm,
      ← Real.rpow_mul hs, show (α / 5) * (2 : ℝ) = 2 * α / 5 by ring]
  rw [hss]

private theorem psi2_le_four_b {α θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5) ≤ 4 := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_Ioo hθ
  have h1 : (Real.sin (2 * θ)) ^ (2 * α / 5) ≤ 1 :=
    Real.rpow_le_one hs (Real.sin_le_one _) (by linarith)
  have h2 : (α + Real.sin (2 * θ)) ^ 2 ≤ 4 := by
    nlinarith [hs, Real.sin_le_one (2 * θ), hα, hα1]
  nlinarith [h1, h2, Real.rpow_nonneg hs (2 * α / 5)]

/-- On the open quadrant, `(x·Wt)² = (x·w)² sin(2θ)^{-γ}`. -/
private theorem mul_Wt_sq_b {α z θ x : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (x * Wt α z θ) ^ 2 = (x * w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α)) := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hstep : ((Real.sin (2 * θ)) ^ (-(gam α / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-(gam α)) := by
    rw [pow_two, ← Real.rpow_add hs]
    congr 1
    ring
  simp only [Wt, wTheta, mul_pow, hstep]
  ring

/-! ## The `f`-side step: the mean-term estimate produces the `TW`-block of `GmajW` -/

private theorem gside_le_b {α CB : ℝ} {f : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hfm : Work.Spaces.HkMem α 4 f)
    (hCB : ∀ d : ℕ, d ≤ 3 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        (DzIter d f z θ * w z) ^ 2
          ≤ CB * ((w z) ^ 2 * (∫ σ in Work.Spaces.Iθ, (DzIter d f z σ) ^ 2)
              + (gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α f d z))
    {d : ℕ} (hd : d ≤ 3) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5))
        * (DzIter d f z θ * Wt α z θ) ^ 2
      ≤ max CB 1 * GmajW α f z θ := by
  have hγ1 : (0 : ℝ) < gam α - 1 := by rw [Work.Spaces.gam_sub_one]; linarith
  have hγinv : 0 ≤ (gam α - 1)⁻¹ := inv_nonneg.mpr hγ1.le
  have hCBB0 : (0 : ℝ) ≤ max CB 1 := le_trans zero_le_one (le_max_right CB 1)
  have hCBle : CB ≤ max CB 1 := le_max_left CB 1
  have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_Ioo hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hTWnn : 0 ≤ TW α θ := TW_nonneg hα.le hθI
  have hX0 : 0 ≤ (w z) ^ 2 * (∫ σ in Work.Spaces.Iθ, (DzIter d f z σ) ^ 2)
      + (gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α f d z :=
    add_nonneg (mul_nonneg (sq_nonneg _)
        (setIntegral_nonneg measurableSet_Icc (fun σ _ => sq_nonneg _)))
      (mul_nonneg hγinv (Work.FTS.H2.WPQ.Aang_nonneg α f d z))
  have hg1 : (DzIter d f z θ * w z) ^ 2
      ≤ max CB 1 * ((w z) ^ 2 * (∫ σ in Work.Spaces.Iθ, (DzIter d f z σ) ^ 2)
        + (gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α f d z) :=
    le_trans (hCB d hd z θ hz hθ.1 hθ.2) (mul_le_mul_of_nonneg_right hCBle hX0)
  have hmem : d ∈ Finset.range 4 := Finset.mem_range.mpr (by omega)
  have hAang_le : Work.FTS.H2.WPQ.Aang α f d z
      ≤ ∑ d' ∈ Finset.range 4, Work.FTS.H2.WPQ.Aang α f d' z :=
    Finset.single_le_sum (fun d' _ => Work.FTS.H2.WPQ.Aang_nonneg α f d' z) hmem
  have hw : (w z) ^ 2 * (∫ σ in Work.Spaces.Iθ, (DzIter d f z σ) ^ 2) ≤ HgInt α f z :=
    w_sq_mul_slice_le_HgInt hfm (by omega) hz
  have hXle : (w z) ^ 2 * (∫ σ in Work.Spaces.Iθ, (DzIter d f z σ) ^ 2)
        + (gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α f d z
      ≤ HgInt α f z + (gam α - 1)⁻¹ * ∑ d' ∈ Finset.range 4,
          Work.FTS.H2.WPQ.Aang α f d' z :=
    add_le_add hw (mul_le_mul_of_nonneg_left hAang_le hγinv)
  rw [mul_Wt_sq_b hθ]
  have hBS : (Real.sin (2 * θ)) ^ (-(gam α))
        * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5)) = TW α θ := by
    rw [TW_eq_mul hθ]; ring
  rw [show ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5))
        * ((DzIter d f z θ * w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α)))
      = (DzIter d f z θ * w z) ^ 2 * TW α θ from by rw [← hBS]; ring]
  refine le_trans (mul_le_mul_of_nonneg_right hg1 hTWnn) ?_
  have hXTW : ((w z) ^ 2 * (∫ σ in Work.Spaces.Iθ, (DzIter d f z σ) ^ 2)
        + (gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α f d z) * TW α θ
      ≤ GmajW α f z θ := by
    simp only [GmajW]
    exact le_trans (mul_le_mul_of_nonneg_right hXle hTWnn)
      (le_add_of_nonneg_left (Work.Spaces.HkIntegrand_nonneg α 4 f z θ))
  calc (max CB 1 * ((w z) ^ 2 * (∫ σ in Work.Spaces.Iθ, (DzIter d f z σ) ^ 2)
          + (gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α f d z)) * TW α θ
      = max CB 1 * (((w z) ^ 2 * (∫ σ in Work.Spaces.Iθ, (DzIter d f z σ) ^ 2)
          + (gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α f d z) * TW α θ) := by ring
    _ ≤ max CB 1 * GmajW α f z θ := mul_le_mul_of_nonneg_left hXTW hCBB0

/-! ## The mixed slots -/

theorem mslot_dz_le_b : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (h f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen h → Work.Spaces.WlInfMem α 4 h →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      ∀ I J : ℕ, 1 ≤ I → I + J ≤ 3 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (mixed J I (fun z θ => h z θ * Dz f z θ) z θ * Wt α z θ) ^ 2
        ≤ C * (Work.Spaces.WlInf α 4 h) ^ 2 * GmajW α f z θ := by
  obtain ⟨CB, hCB0, hCBmean⟩ := dzIter_w_mean_le
  have hCpos : (0 : ℝ) < 2 * 10 ^ 12 * (1 + max CB 1) := by
    have h2 : (0 : ℝ) < 2 * 10 ^ 12 := by norm_num
    have h1 : (1 : ℝ) ≤ max CB 1 := le_max_right CB 1
    have h3 : (0 : ℝ) < 1 + max CB 1 := by linarith
    exact mul_pos h2 h3
  refine ⟨2 * 10 ^ 12 * (1 + max CB 1), hCpos, ?_⟩
  intro α h f hα hα1 hsmh hWm hsmf hfm I J hI hIJ z θ hz hθ0 hθ1
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hW : 0 ≤ Work.Spaces.WlInf α 4 h := Work.Spaces.WlInf_nonneg α 4 h hWm
  have hWsq : 0 ≤ (Work.Spaces.WlInf α 4 h) ^ 2 := sq_nonneg _
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
  have hGnn : 0 ≤ GmajW α f z θ := GmajW_nonneg hα f hθI
  have hHkG : HkIntegrand α 4 f z θ ≤ GmajW α f z θ := HkIntegrand_le_GmajW hα f hθI
  have hHknn : 0 ≤ HkIntegrand α 4 f z θ := Work.Spaces.HkIntegrand_nonneg α 4 f z θ
  have hM0 : (0 : ℝ) ≤ max CB 1 := le_trans zero_le_one (le_max_right CB 1)
  have hJ3 : J ≤ 3 := by omega
  have hJ4 : J ≤ 4 := by omega
  have hI4 : I ≤ 4 := by omega
  have h1M : (1 : ℝ) ≤ 1 + max CB 1 := by linarith
  have hDzsm : Work.FTS.EllipticEst.SmoothOpen (Dz f) :=
    Work.FTS.EllipticEst.SmoothOpen.Dz hsmf
  -- Leibniz in the open class
  have heq := Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed J I h (Dz f) hsmh hDzsm z θ hz hθ0 hθ1
  set Y : ℕ → ℕ → ℝ := fun a b => (I.choose a : ℝ) * (J.choose b : ℝ)
    * ((mixed b a h z θ) * (mixed (J - b) (I - a) (Dz f) z θ * Wt α z θ)) with hYdef
  have hYsplit : (mixed J I (fun z θ => h z θ * Dz f z θ) z θ * Wt α z θ) ^ 2
      = (∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1), Y a b) ^ 2 := by
    have hkey : (mixed J I (fun z θ => h z θ * Dz f z θ) z θ) * Wt α z θ
        = ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1), Y a b := by
      rw [heq, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro b hb
      simp only [hYdef]
      ring
    rw [hkey]
  -- the pointwise bound for each summand
  have hper : ∀ a ∈ Finset.range (I + 1), ∀ b ∈ Finset.range (J + 1),
      (Y a b) ^ 2 ≤ (65536 * 40000 * (1 + max CB 1)) * (Work.Spaces.WlInf α 4 h) ^ 2
        * GmajW α f z θ := by
    intro a ha b hb
    have haI : a ≤ I := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
    have hbJ : b ≤ J := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
    have hch : (I.choose a : ℝ) ^ 2 * (J.choose b : ℝ) ^ 2 ≤ 65536 :=
      calc (I.choose a : ℝ) ^ 2 * (J.choose b : ℝ) ^ 2 ≤ 256 * 256 :=
            mul_le_mul (Work.Spaces.choose_sq_le_256 I a (by omega) (by omega))
              (Work.Spaces.choose_sq_le_256 J b (by omega) (by omega))
              (by positivity) (by norm_num)
        _ = 65536 := by norm_num
    have hY : (Y a b) ^ 2 = (I.choose a : ℝ) ^ 2 * (J.choose b : ℝ) ^ 2
        * ((mixed b a h z θ) * (mixed (J - b) (I - a) (Dz f) z θ * Wt α z θ)) ^ 2 := by
      rw [hYdef]; ring
    rw [hY]
    -- the `h`-factor, in both regimes
    have hma : (mixed b a h z θ) ^ 2
        ≤ 40000 * (Work.Spaces.WlInf α 4 h) ^ 2 := by
      rcases eq_or_ne a 0 with ha0 | ha0
      · subst ha0
        rw [Work.Spaces.mixed_zero_right]
        have hh : |DzIter b h z θ| ≤ 100 * Work.Spaces.WlInf α 4 h :=
          Work.FTS.OpenPkg.DzIter_le_WlInf_open hsmh hWm (by omega) hz hθ
        have h1 : (DzIter b h z θ) ^ 2 ≤ (100 * Work.Spaces.WlInf α 4 h) ^ 2 :=
          Work.Spaces.sq_le_sq_of_abs_le hh
        nlinarith [h1, sq_nonneg (Work.Spaces.WlInf α 4 h)]
      · have ha1 : 1 ≤ a := by omega
        have hh := Work.FTS.OpenPkg.Mixed_le_WlInf_open (α := α) (f := h) (a := a) (b := b)
          hα hsmh hWm ha1 (by omega) hz hθ
        calc (mixed b a h z θ) ^ 2
            ≤ (100 * (Work.Spaces.WlInf α 4 h
                * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))) ^ 2 :=
              Work.Spaces.sq_le_sq_of_abs_le hh
          _ = (100 * Work.Spaces.WlInf α 4 h) ^ 2
                * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5)) := by
              rw [mul_pow, mul_pow, phi_sq_b hθ]; ring
          _ ≤ (100 * Work.Spaces.WlInf α 4 h) ^ 2 * 4 :=
              mul_le_mul_of_nonneg_left (psi2_le_four_b hα hα1 hθ) (sq_nonneg _)
          _ = 40000 * (Work.Spaces.WlInf α 4 h) ^ 2 := by ring
    by_cases hlt : a < I
    · -- at least one `θ`-derivative falls on the `D_z f` factor
      have hIa : 1 ≤ I - a := by omega
      have hmg : (mixed (J - b) (I - a) (Dz f) z θ * Wt α z θ) ^ 2
          ≤ HkIntegrand α 4 f z θ := by
        have hshift : mixed (J - b) (I - a) (Dz f) z θ = mixed (J - b + 1) (I - a) f z θ :=
          mixed_Dz_eq hsmf (J - b) (I - a) hz hθ0 hθ1
        rw [hshift]
        exact Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z θ (I - a) (J - b + 1) hIa
          (by omega)
      have hbase2 : ((mixed b a h z θ)
            * (mixed (J - b) (I - a) (Dz f) z θ * Wt α z θ)) ^ 2
          ≤ (40000 * (Work.Spaces.WlInf α 4 h) ^ 2) * HkIntegrand α 4 f z θ := by
        rw [mul_pow]
        exact mul_le_mul hma hmg (sq_nonneg _) (by positivity)
      calc (I.choose a : ℝ) ^ 2 * (J.choose b : ℝ) ^ 2
            * ((mixed b a h z θ)
              * (mixed (J - b) (I - a) (Dz f) z θ * Wt α z θ)) ^ 2
          ≤ 65536 * ((mixed b a h z θ)
              * (mixed (J - b) (I - a) (Dz f) z θ * Wt α z θ)) ^ 2 :=
            mul_le_mul_of_nonneg_right hch (sq_nonneg _)
        _ ≤ 65536 * ((40000 * (Work.Spaces.WlInf α 4 h) ^ 2)
              * HkIntegrand α 4 f z θ) :=
            mul_le_mul_of_nonneg_left hbase2 (by norm_num)
        _ ≤ (65536 * 40000 * (1 + max CB 1)) * (Work.Spaces.WlInf α 4 h) ^ 2
              * GmajW α f z θ := by
            rw [show 65536 * ((40000 * (Work.Spaces.WlInf α 4 h) ^ 2)
                  * HkIntegrand α 4 f z θ)
                = (65536 * 40000 : ℝ) * ((Work.Spaces.WlInf α 4 h) ^ 2
                  * HkIntegrand α 4 f z θ) from by ring]
            calc (65536 * 40000 : ℝ) * ((Work.Spaces.WlInf α 4 h) ^ 2
                  * HkIntegrand α 4 f z θ)
                ≤ (65536 * 40000 : ℝ) * ((Work.Spaces.WlInf α 4 h) ^ 2 * GmajW α f z θ) :=
                  mul_le_mul_of_nonneg_left
                    (mul_le_mul_of_nonneg_left hHkG hWsq) (by norm_num)
              _ ≤ (65536 * 40000 * (1 + max CB 1))
                    * ((Work.Spaces.WlInf α 4 h) ^ 2 * GmajW α f z θ) :=
                  mul_le_mul_of_nonneg_right (by nlinarith [hM0]) (mul_nonneg hWsq hGnn)
              _ = (65536 * 40000 * (1 + max CB 1)) * (Work.Spaces.WlInf α 4 h) ^ 2
                    * GmajW α f z θ := by ring
    · -- all `θ`-derivatives fall on `h`: the mean-term estimate is consumed
      have hac : a = I := by omega
      have hsub : I - a = 0 := by omega
      have hdJ : J - b + 1 ≤ 3 := by omega
      have hmb : (mixed b a h z θ) ^ 2
          ≤ (100 * Work.Spaces.WlInf α 4 h) ^ 2
            * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5)) := by
        have ha1 : 1 ≤ a := by omega
        have hh := Work.FTS.OpenPkg.Mixed_le_WlInf_open (α := α) (f := h) (a := a) (b := b)
          hα hsmh hWm ha1 (by omega) hz hθ
        calc (mixed b a h z θ) ^ 2
            ≤ (100 * (Work.Spaces.WlInf α 4 h
                * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))) ^ 2 :=
              Work.Spaces.sq_le_sq_of_abs_le hh
          _ = (100 * Work.Spaces.WlInf α 4 h) ^ 2
                * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5)) := by
              rw [mul_pow, mul_pow, phi_sq_b hθ]; ring
      have hT : (mixed (J - b) (I - a) (Dz f) z θ * Wt α z θ) ^ 2
          = (DzIter (J - b + 1) f z θ * Wt α z θ) ^ 2 := by
        rw [hsub, Work.Spaces.mixed_zero_right, dzIter_Dz_eq]
      have hgside := gside_le_b (α := α) (CB := CB) (f := f) hα hfm
        (fun d hd z' θ' hz' hθ0' hθ1' =>
          hCBmean α f d hα hα1 hsmf hfm hd z' θ' hz' hθ0' hθ1') hdJ hz hθ
      have hbase2 : ((mixed b a h z θ)
            * (mixed (J - b) (I - a) (Dz f) z θ * Wt α z θ)) ^ 2
          ≤ (100 * Work.Spaces.WlInf α 4 h) ^ 2 * (max CB 1) * GmajW α f z θ := by
        rw [mul_pow, hT]
        calc (mixed b a h z θ) ^ 2 * (DzIter (J - b + 1) f z θ * Wt α z θ) ^ 2
            ≤ ((100 * Work.Spaces.WlInf α 4 h) ^ 2
                * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5)))
              * (DzIter (J - b + 1) f z θ * Wt α z θ) ^ 2 :=
              mul_le_mul_of_nonneg_right hmb (sq_nonneg _)
          _ = (100 * Work.Spaces.WlInf α 4 h) ^ 2
              * (((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5))
                * (DzIter (J - b + 1) f z θ * Wt α z θ) ^ 2) := by ring
          _ ≤ (100 * Work.Spaces.WlInf α 4 h) ^ 2
                * (max CB 1 * GmajW α f z θ) :=
              mul_le_mul_of_nonneg_left hgside (sq_nonneg _)
          _ = (100 * Work.Spaces.WlInf α 4 h) ^ 2 * (max CB 1) * GmajW α f z θ := by ring
      calc (I.choose a : ℝ) ^ 2 * (J.choose b : ℝ) ^ 2
            * ((mixed b a h z θ)
              * (mixed (J - b) (I - a) (Dz f) z θ * Wt α z θ)) ^ 2
          ≤ 65536 * ((mixed b a h z θ)
              * (mixed (J - b) (I - a) (Dz f) z θ * Wt α z θ)) ^ 2 :=
            mul_le_mul_of_nonneg_right hch (sq_nonneg _)
        _ ≤ 65536 * ((100 * Work.Spaces.WlInf α 4 h) ^ 2 * (max CB 1)
              * GmajW α f z θ) :=
            mul_le_mul_of_nonneg_left hbase2 (by norm_num)
        _ ≤ (65536 * 40000 * (1 + max CB 1)) * (Work.Spaces.WlInf α 4 h) ^ 2
              * GmajW α f z θ := by
            rw [show 65536 * ((100 * Work.Spaces.WlInf α 4 h) ^ 2 * (max CB 1)
                  * GmajW α f z θ)
                = (65536 * 10000 * (max CB 1)) * ((Work.Spaces.WlInf α 4 h) ^ 2
                    * GmajW α f z θ) from by ring]
            have hAB : (65536 * 10000 * (max CB 1) : ℝ)
                ≤ 65536 * 40000 * (1 + max CB 1) := by nlinarith [hM0]
            calc (65536 * 10000 * (max CB 1)) * ((Work.Spaces.WlInf α 4 h) ^ 2
                    * GmajW α f z θ)
                ≤ (65536 * 40000 * (1 + max CB 1))
                    * ((Work.Spaces.WlInf α 4 h) ^ 2 * GmajW α f z θ) :=
                  mul_le_mul_of_nonneg_right hAB (mul_nonneg hWsq hGnn)
              _ = (65536 * 40000 * (1 + max CB 1)) * (Work.Spaces.WlInf α 4 h) ^ 2
                    * GmajW α f z θ := by ring
  -- Cauchy–Schwarz on the double sum
  have hIJ25 : ((I : ℝ) + 1) * ((J : ℝ) + 1) ≤ 25 := by
    have h1 : (I : ℝ) ≤ 4 := by exact_mod_cast hI4
    have h2 : (J : ℝ) ≤ 4 := by exact_mod_cast hJ4
    nlinarith
  have hsum2 : ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1), (Y a b) ^ 2
      ≤ ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1),
          ((65536 * 40000 * (1 + max CB 1)) * (Work.Spaces.WlInf α 4 h) ^ 2
            * GmajW α f z θ) :=
    Finset.sum_le_sum (fun a ha => Finset.sum_le_sum (fun b hb => hper a ha b hb))
  have hsumconst : ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1),
        ((65536 * 40000 * (1 + max CB 1)) * (Work.Spaces.WlInf α 4 h) ^ 2 * GmajW α f z θ)
      = ((I : ℝ) + 1) * ((J : ℝ) + 1)
        * ((65536 * 40000 * (1 + max CB 1)) * (Work.Spaces.WlInf α 4 h) ^ 2
            * GmajW α f z θ) := by
    rw [Finset.sum_const, Finset.sum_const, Finset.card_range, Finset.card_range,
      nsmul_eq_mul, nsmul_eq_mul]
    push_cast
    ring
  rw [hYsplit]
  have hcardI : (((Finset.range (I + 1)).card : ℕ) : ℝ) = (I : ℝ) + 1 := by
    rw [Finset.card_range]; push_cast; ring
  have hcardJ : (((Finset.range (J + 1)).card : ℕ) : ℝ) = (J : ℝ) + 1 := by
    rw [Finset.card_range]; push_cast; ring
  have hKper_nn : (0 : ℝ) ≤ 65536 * 40000 * (1 + max CB 1) :=
    mul_nonneg (mul_nonneg (by norm_num) (by norm_num)) (by linarith)
  calc (∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1), Y a b) ^ 2
      ≤ ((I : ℝ) + 1) * ∑ a ∈ Finset.range (I + 1),
          ((J : ℝ) + 1) * ∑ b ∈ Finset.range (J + 1), (Y a b) ^ 2 := by
        have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (I + 1))
          (f := fun a => ∑ b ∈ Finset.range (J + 1), Y a b)
        rw [hcardI] at hcs
        refine hcs.trans ?_
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun a _ => ?_)) (by positivity)
        have hcs2 := sq_sum_le_card_mul_sum_sq (s := Finset.range (J + 1))
          (f := fun b => Y a b)
        rwa [hcardJ] at hcs2
    _ = ((I : ℝ) + 1) * ((J : ℝ) + 1)
          * ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1), (Y a b) ^ 2 := by
        rw [← Finset.mul_sum]; ring
    _ ≤ ((I : ℝ) + 1) * ((J : ℝ) + 1)
          * ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1),
              ((65536 * 40000 * (1 + max CB 1)) * (Work.Spaces.WlInf α 4 h) ^ 2
                * GmajW α f z θ) :=
        mul_le_mul_of_nonneg_left hsum2 (by positivity)
    _ = (((I : ℝ) + 1) * ((J : ℝ) + 1)) ^ 2
          * ((65536 * 40000 * (1 + max CB 1)) * (Work.Spaces.WlInf α 4 h) ^ 2
              * GmajW α f z θ) := by rw [hsumconst]; ring
    _ ≤ 625 * ((65536 * 40000 * (1 + max CB 1)) * (Work.Spaces.WlInf α 4 h) ^ 2
            * GmajW α f z θ) := by
        refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (mul_nonneg hKper_nn hWsq) hGnn)
        have h0 : (0 : ℝ) ≤ ((I : ℝ) + 1) * ((J : ℝ) + 1) := by positivity
        nlinarith [hIJ25, h0]
    _ ≤ (2 * 10 ^ 12 * (1 + max CB 1)) * (Work.Spaces.WlInf α 4 h) ^ 2 * GmajW α f z θ := by
        rw [show 625 * ((65536 * 40000 * (1 + max CB 1)) * (Work.Spaces.WlInf α 4 h) ^ 2
              * GmajW α f z θ)
            = (625 * (65536 * 40000 * (1 + max CB 1))) * ((Work.Spaces.WlInf α 4 h) ^ 2
              * GmajW α f z θ) from by ring]
        have hle : 625 * (65536 * 40000 * (1 + max CB 1)) ≤ 2 * 10 ^ 12 * (1 + max CB 1) := by
          nlinarith [hM0]
        calc (625 * (65536 * 40000 * (1 + max CB 1)))
              * ((Work.Spaces.WlInf α 4 h) ^ 2 * GmajW α f z θ)
            ≤ (2 * 10 ^ 12 * (1 + max CB 1))
              * ((Work.Spaces.WlInf α 4 h) ^ 2 * GmajW α f z θ) :=
              mul_le_mul_of_nonneg_right hle (mul_nonneg hWsq hGnn)
          _ = (2 * 10 ^ 12 * (1 + max CB 1)) * (Work.Spaces.WlInf α 4 h) ^ 2
                * GmajW α f z θ := by ring

end Work.FTS.StrongPersist.L3Rhs.L3MulDzBackupM
end
end
