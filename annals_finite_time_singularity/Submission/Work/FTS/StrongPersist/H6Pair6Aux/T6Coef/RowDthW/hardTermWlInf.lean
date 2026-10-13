/-
# `RowDthW/hardTermWlInf` — the `(0,0)` transport summand of the `D_θ`-row with a
`𝒲^{6,∞}`-priced coefficient

The integrand `ρ · A · D_θ(D_z^bD_θ^a f) · D_z^bD_θ^af` carries *no* derivative on the
coefficient `A`, so it is controlled by the slice-level transport inequality
`N6Trans.T1SixAux.hardSlotSliceSixZero`, which is stated for a coefficient `F` with *both*
`|F| ≤ Kf` and `|D_θF| ≤ Kf`.  The hypotheses `WlInfMem α 6 A`, `WlInf α 6 A ≤ K` give
`|A| ≤ K` (the `k = 0` term of the first sum of `WlInf`) and `|D_θA| ≤ 2K` (the `(j,k) = (1,0)`
term of the second sum), so the slice inequality applies with `Kf := 2K`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.AuxProof
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.hardSlotSliceSixZero
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6Aux.zeroTerm
import Submission.Work.FTS.StrongPersist.N6Trans.L6FBound.mixed_le_WlInf6
import Submission.Work.FTS.StrongPersist.N6Trans.L6Core

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDthW

set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem hardTermWlInf : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (A f : Work.FTS.Galerkin.Fn) (K M : ℝ) (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen A → Work.Spaces.WlInfMem α 6 A →
      Work.Spaces.WlInf α 6 A ≤ K →
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ : ℝ => ρ z θ * A z θ
          * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
          * Work.Spaces.mixed b a f z θ) Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, ρ z θ * A z θ
          * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
          * Work.Spaces.mixed b a f z θ) Work.Spaces.Iz ∧
      |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ * A z θ
          * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
          * Work.Spaces.mixed b a f z θ|
        ≤ C * (1 + K) * (1 + Work.Spaces.HkSq α 6 f) := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.StrongPersist.N6Trans.T1SixAux.hardSlotSliceSixZero
  refine ⟨2 * C, by positivity, ?_⟩
  intro α hαmem A f K M a b ρ hsmA hWmem hWK hdat hab hleaf
  have hα : 0 < α := hαmem.1
  have hα1 : α ≤ 1 := hαmem.2
  have hWnn : 0 ≤ Work.Spaces.WlInf α 6 A := Work.Spaces.WlInf_nonneg α 6 A hWmem
  have hK0 : 0 ≤ K := le_trans hWnn hWK
  have hKf : 0 ≤ 2 * K := by linarith
  have hS0 : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  -- ## pointwise bounds on `A` and `D_θ A`
  have hval : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |A z θ| ≤ 2 * K := by
    intro z θ hz hθ hθ2
    have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ, le_of_lt hθ2⟩
    have h := Work.FTS.StrongPersist.N6Trans.zpz_le_WlInf6 hWmem (j := 0) (by norm_num) hzI hθI
    simp only [pow_zero, one_mul, Work.Spaces.pzIter_zero] at h
    linarith
  have hdb : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.Dth A z θ| ≤ 2 * K := by
    intro z θ hz hθ hθ2
    have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ, le_of_lt hθ2⟩
    have h := Work.FTS.StrongPersist.N6Trans.L6FBound.zpz_Dth_le_WlInf6 hα hWmem (a := 1)
      (j := 0) (by norm_num) (by norm_num) hzI hθI
    simp only [pow_zero, one_mul, Work.Spaces.pzIter_zero, Work.Spaces.DthIter_succ,
      Work.Spaces.DthIter_zero] at h
    have hσ : 0 ≤ Real.sin (2 * θ) := Work.Spaces.sin_two_nonneg' hθI
    have hσ1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hr1 : (Real.sin (2 * θ)) ^ (α / 5) ≤ 1 := Real.rpow_le_one hσ hσ1 (by linarith)
    have hr0 : 0 ≤ (Real.sin (2 * θ)) ^ (α / 5) := Real.rpow_nonneg hσ _
    have hfac : (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) ≤ 2 := by
      nlinarith [hσ, Real.pi_pos]
    have h2 : Work.Spaces.WlInf α 6 A
        * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
        ≤ 2 * Work.Spaces.WlInf α 6 A := by
      calc Work.Spaces.WlInf α 6 A
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
          ≤ Work.Spaces.WlInf α 6 A * 2 :=
            mul_le_mul_of_nonneg_left hfac hWnn
        _ = 2 * Work.Spaces.WlInf α 6 A := by ring
    linarith [hWnn, hWK, hr0]
  -- ## the three leaf cases, each reducing to `zeroTerm_canon`
  have hmain : ∀ q : ℝ, ρ = Work.FTS.TransportS.SlotT2.canonW q → 0 ≤ q → q ≤ 2 →
      q ≤ Work.Spaces.gam α → (a = 0 → q ≤ Work.Spaces.eta) →
      (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ : ℝ => ρ z θ * A z θ
          * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
          * Work.Spaces.mixed b a f z θ) Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, ρ z θ * A z θ
          * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
          * Work.Spaces.mixed b a f z θ) Work.Spaces.Iz ∧
      |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ * A z θ
          * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
          * Work.Spaces.mixed b a f z θ|
        ≤ (2 * C) * (1 + K) * (1 + Work.Spaces.HkSq α 6 f) := by
    intro q hρ hq0 hq2 hqγ hqη
    subst hρ
    obtain ⟨h1, h2, h3⟩ := Work.FTS.StrongPersist.H6Rows.Npair6Aux.zeroTerm_canon hCpos hC
      (α := α) (A := A) (f := f) (K0 := 2 * K) (a := a) (b := b) (q := q)
      hsmA hKf hval hdb hdat.sm hdat.h6 hdat.h7 hab hq0 hq2 hqγ hqη
    refine ⟨h1, h2, le_trans h3 ?_⟩
    calc C * (2 * K) * Work.Spaces.HkSq α 6 f
        = (2 * C) * (K * Work.Spaces.HkSq α 6 f) := by ring
      _ ≤ (2 * C) * ((1 + K) * (1 + Work.Spaces.HkSq α 6 f)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          nlinarith [hK0, hS0]
      _ = 2 * C * (1 + K) * (1 + Work.Spaces.HkSq α 6 f) := by ring
  rcases hleaf with hρ | hρ | ⟨ha1, hρ⟩
  · exact hmain Work.Spaces.eta
      (hρ.trans Work.FTS.TransportS.T2Sup.leafWeight_eq_canon.1)
      Work.Spaces.eta_pos.le (by linarith [Work.Spaces.eta_lt_one])
      (Work.FTS.TransportS.T2Sup.eta_le_gam hα) (fun _ => le_rfl)
  · exact hmain 0 (hρ.trans Work.FTS.TransportS.T2Sup.leafWeight_eq_canon.2.1) le_rfl
      (by norm_num) (le_of_lt (Work.Spaces.gam_pos hα)) (fun _ => Work.Spaces.eta_pos.le)
  · exact hmain (Work.Spaces.gam α)
      (hρ.trans (Work.FTS.TransportS.T2Sup.leafWeight_eq_canon.2.2 α))
      (le_of_lt (Work.Spaces.gam_pos hα)) (by rw [Work.Spaces.gam]; linarith)
      le_rfl (fun ha0 => by omega)

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDthW
