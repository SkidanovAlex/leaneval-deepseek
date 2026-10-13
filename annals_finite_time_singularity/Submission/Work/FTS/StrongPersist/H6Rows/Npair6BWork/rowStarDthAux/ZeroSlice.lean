import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowAux
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.hardSlotSliceSixZero
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.Asm
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowStarDthAux.FlatW

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **The transport term, slicewise.**  For `0 ≤ q ≤ γ` (with `q ≤ η` when `a = 0`), a flat
priced coefficient `A` and `v = D_z^bD_θ^af`,

`|∫_θ canonW q z θ·A z θ·D_θ(v) z θ·v z θ| ≤ C·KA·(z/(1+z))·∫_θ canonW q z θ·(v z θ)²`,

uniformly in `z ∈ Iz`.  This is `T1SixAux.hardSlotSliceSixZero` at the two-constant data
`K1 = KA·z/(1+z)` for `|A|` and `K2 = KA·(z/(1+z))·(α+σ)σ^{α/5} ≤ 2K1` for `|D_θA|`. -/
theorem dthZeroSliceAux : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (A f : Work.FTS.Galerkin.Fn) (KA : ℝ) (a b : ℕ) (q : ℝ),
      Work.FTS.EllipticEst.SmoothOpen A →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      0 ≤ KA →
      (∀ j i : ℕ, j + i ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
          |Work.Spaces.mixed j i A z θ| ≤ KA * (z / (1 + z)) *
            (if 1 ≤ i then (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) else 1)) →
      0 ≤ q → q ≤ Work.Spaces.gam α → (a = 0 → q ≤ Work.Spaces.eta) →
      a + b ≤ 6 →
      ∀ z ∈ Work.Spaces.Iz,
        |∫ θ in Work.Spaces.Iθ, Work.FTS.TransportS.SlotT2.canonW q z θ * A z θ
            * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ * Work.Spaces.mixed b a f z θ|
          ≤ C * KA * (z / (1 + z)) *
              ∫ θ in Work.Spaces.Iθ, Work.FTS.TransportS.SlotT2.canonW q z θ
                * (Work.Spaces.mixed b a f z θ) ^ 2 := by
  obtain ⟨Chard, hChardpos, hhard⟩ :=
    Work.FTS.StrongPersist.N6Trans.T1SixAux.hardSlotSliceSixZero
  refine ⟨3 * Chard, by positivity, ?_⟩
  intro α hα A f KA a b q hA hfsm hf6 hKA0 hflat hq0 hqγ hqη hab z hz
  obtain ⟨hα0, hα1⟩ := hα
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · -- `z = 0`: both sides vanish
    subst hz0
    have hL : (fun θ : ℝ => Work.FTS.TransportS.SlotT2.canonW q 0 θ * A 0 θ
        * Work.Spaces.Dth (Work.Spaces.mixed b a f) 0 θ
        * Work.Spaces.mixed b a f 0 θ) = fun _ => (0 : ℝ) := by
      funext θ
      rw [Work.FTS.TransportS.SlotT2.canonW_zero_z]; ring
    rw [hL, MeasureTheory.integral_zero, abs_zero]
    simp
  · have hz0 : 0 ≤ z := hzpos.le
    have hzfac0 : 0 ≤ z / (1 + z) := div_nonneg hz0 (by linarith)
    have hzfac1 : z / (1 + z) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    have hZsm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.mixed b a f) := hfsm.mixed b a
    have hq2 : q ≤ 2 := by
      have h1 : Work.Spaces.gam α ≤ 2 := by rw [Work.Spaces.gam]; linarith
      linarith
    have hKf0 : 0 ≤ 2 * KA * (z / (1 + z)) := by positivity
    -- `|A z θ| ≤ 2 KA z/(1+z)`
    have hAb : ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
        |A z θ| ≤ 2 * KA * (z / (1 + z)) := by
      intro θ hθ0 hθ1
      have h := hflat 0 0 (by norm_num) z θ hzpos hθ0 hθ1
      simp only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero] at h
      have hif : (if (1 : ℕ) ≤ 0 then
          (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) else (1 : ℝ)) = 1 :=
        if_neg (by norm_num)
      rw [hif, mul_one] at h
      have hfac : 0 ≤ KA * (z / (1 + z)) := mul_nonneg hKA0 hzfac0
      linarith
    -- `|D_θA z θ| ≤ 2 KA z/(1+z)`
    have hDb : ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.Dth A z θ| ≤ 2 * KA * (z / (1 + z)) := by
      intro θ hθ0 hθ1
      have h := hflat 0 1 (by norm_num) z θ hzpos hθ0 hθ1
      have hif : (if (1 : ℕ) ≤ 1 then
          (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) else (1 : ℝ))
          = (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) := if_pos le_rfl
      rw [hif] at h
      have hs : 0 ≤ Real.sin (2 * θ) :=
        (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])).le
      have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
      have hgain : (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) ≤ 2 := by
        have h1 : (α + Real.sin (2 * θ)) ≤ 2 := by linarith
        have h2 : (Real.sin (2 * θ)) ^ (α / 5) ≤ 1 := Real.rpow_le_one hs hs1 (by linarith)
        have h3 : (0 : ℝ) ≤ α + Real.sin (2 * θ) := by linarith
        calc (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)
            ≤ (α + Real.sin (2 * θ)) * 1 := mul_le_mul_of_nonneg_left h2 h3
          _ ≤ 2 := by linarith
      have hDth : Work.Spaces.Dth A z θ = Work.Spaces.mixed 0 1 A z θ := rfl
      rw [hDth]
      calc |Work.Spaces.mixed 0 1 A z θ|
          ≤ KA * (z / (1 + z))
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := h
        _ ≤ KA * (z / (1 + z)) * 2 :=
            mul_le_mul_of_nonneg_left hgain (mul_nonneg hKA0 hzfac0)
        _ = 2 * KA * (z / (1 + z)) := by ring
    have hint : MeasureTheory.IntegrableOn (fun θ : ℝ =>
        Work.FTS.TransportS.SlotT2.canonW q z θ * (Work.Spaces.mixed b a f z θ) ^ 2)
        Work.Spaces.Iθ :=
      Work.FTS.StrongPersist.N6Trans.T1SixAux.slotSliceIntegrable α q hfsm hf6 hqγ hqη hab hz
    have hmain := hhard q (2 * KA * (z / (1 + z))) z A (Work.Spaces.mixed b a f)
      hq0 hq2 hKf0 hz hA hZsm hAb hDb hint
    have hJnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.FTS.TransportS.SlotT2.canonW q z θ
        * (Work.Spaces.mixed b a f z θ) ^ 2 :=
      MeasureTheory.integral_nonneg_of_ae
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
          (fun θ hθ => mul_nonneg (Work.FTS.TransportS.SlotT2.canonW_nonneg hθ) (sq_nonneg _)))
    calc |∫ θ in Work.Spaces.Iθ, Work.FTS.TransportS.SlotT2.canonW q z θ * A z θ
          * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ * Work.Spaces.mixed b a f z θ|
        ≤ Chard * (2 * KA * (z / (1 + z)))
            * ∫ θ in Work.Spaces.Iθ, Work.FTS.TransportS.SlotT2.canonW q z θ
                * (Work.Spaces.mixed b a f z θ) ^ 2 := hmain
      _ ≤ 3 * Chard * KA * (z / (1 + z))
            * ∫ θ in Work.Spaces.Iθ, Work.FTS.TransportS.SlotT2.canonW q z θ
                * (Work.Spaces.mixed b a f z θ) ^ 2 := by
          have h1 : Chard * (2 * KA * (z / (1 + z))) ≤ 3 * Chard * KA * (z / (1 + z)) := by
            have := hChardpos.le
            nlinarith [hzfac0, hKA0]
          exact mul_le_mul_of_nonneg_right h1 hJnn
      _ = (3 * Chard) * KA * (z / (1 + z))
            * ∫ θ in Work.Spaces.Iθ, Work.FTS.TransportS.SlotT2.canonW q z θ
                * (Work.Spaces.mixed b a f z θ) ^ 2 := by ring

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
