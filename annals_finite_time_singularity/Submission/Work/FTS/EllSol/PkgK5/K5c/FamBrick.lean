import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.ClassC.VopGen.truncAux
import Submission.Work.FTS.StrongPersist.SP6.F0SixYblk
import Submission.Work.FTS_RegExport.RXB.l12dens_weighted_bound
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_l12fstar
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2W.PsiSlices.shiftedSourcePoleBound
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.PkgK5.K5c

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-! ## Elementary square-root inequalities -/

private theorem sqrt_add_le_aux {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have h0 : 0 ≤ Real.sqrt a + Real.sqrt b := by positivity
  have hle : a + b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
    nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sqrt_nonneg a, Real.sqrt_nonneg b]
  calc Real.sqrt (a + b) ≤ Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2) := Real.sqrt_le_sqrt hle
    _ = Real.sqrt a + Real.sqrt b := Real.sqrt_sq h0

private theorem two_sqrt_mul_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    2 * Real.sqrt (x * y) ≤ x + y := by
  have h0 : 0 ≤ Real.sqrt (x * y) := Real.sqrt_nonneg _
  have hs : Real.sqrt (x * y) ^ 2 = x * y := Real.sq_sqrt (mul_nonneg hx hy)
  have h3 : 0 ≤ x + y := by linarith
  nlinarith [sq_nonneg (x - y), hs, h0]

private theorem sqrt_sq_four {α : ℝ} (hα2 : 0 ≤ α ^ 2) : Real.sqrt (α ^ 4) = α ^ 2 := by
  rw [show α ^ 4 = (α ^ 2) ^ 2 by ring, Real.sqrt_sq hα2]

/-! ## The arithmetic of one family summand -/

/-- The `α`-bookkeeping of one family summand: from the brick's output (`X ≤ Ctb (Z + √(DD·TT))`)
and the three slot comparisons `Z ≤ Sd`, `DD ≤ 18 (Sdd2 + Sd)`, `TT ≤ Sdd`, one gets the summand
bound with the `α`-powers distributed as in the target. -/
private theorem famTermArith {Ctb α Sd Sdd2 Sdd X Z DD TT : ℝ}
    (hCtb : 0 < Ctb) (hα0 : 0 < α) (hα4 : α ≤ 1 / 4)
    (hSd : 0 ≤ Sd) (hSdd2 : 0 ≤ Sdd2) (hSdd : 0 ≤ Sdd)
    (hZ0 : 0 ≤ Z) (hDD0 : 0 ≤ DD) (hTT0 : 0 ≤ TT)
    (hZ : Z ≤ Sd) (hDD : DD ≤ 18 * Sdd2 + 18 * Sd) (hTT : TT ≤ Sdd)
    (hmain : X ≤ Ctb * (Z + Real.sqrt (DD * TT))) :
    α ^ 2 * X ≤ Ctb * (α ^ 2 * Sd + Real.sqrt 18 * (α ^ 4 * Sdd2 + α ^ 2 * Sd + Sdd)) := by
  have h18 : 0 ≤ Real.sqrt 18 := Real.sqrt_nonneg 18
  have hα2 : 0 ≤ α ^ 2 := by positivity
  have hα4n : 0 ≤ α ^ 4 := by positivity
  have hα21 : α ^ 2 ≤ 1 := by nlinarith [hα0, hα4, sq_nonneg α]
  have hsqrt : α ^ 2 * Real.sqrt (DD * TT)
      ≤ Real.sqrt 18 * (α ^ 4 * Sdd2 + α ^ 2 * Sd + Sdd) := by
    have hA0 : 0 ≤ α ^ 4 * Sdd2 := mul_nonneg hα4n hSdd2
    have hA'0 : 0 ≤ α ^ 2 * Sd := mul_nonneg hα2 hSd
    have hDD' : DD ≤ 18 * (Sdd2 + Sd) := by linarith
    have h2 : DD * TT ≤ (18 * (Sdd2 + Sd)) * Sdd :=
      mul_le_mul hDD' hTT hTT0 (by linarith)
    have h1 : α ^ 4 * (DD * TT) ≤ 18 * (α ^ 4 * (Sdd2 + Sd) * Sdd) := by
      nlinarith [h2, hα4n, hSdd, hSdd2, hSd, mul_nonneg hα4n (mul_nonneg (by linarith) hSdd)]
    have hstep2 : Real.sqrt (α ^ 4 * (DD * TT))
        ≤ Real.sqrt (18 * (α ^ 4 * (Sdd2 + Sd) * Sdd)) := Real.sqrt_le_sqrt h1
    have hstep3 : Real.sqrt (18 * (α ^ 4 * (Sdd2 + Sd) * Sdd))
        = Real.sqrt 18 * (α ^ 2 * Real.sqrt ((Sdd2 + Sd) * Sdd)) := by
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 18)]
      congr 1
      rw [show α ^ 4 * (Sdd2 + Sd) * Sdd = α ^ 4 * ((Sdd2 + Sd) * Sdd) by ring]
      rw [Real.sqrt_mul hα4n, sqrt_sq_four hα2]
    have hstep4 : Real.sqrt ((Sdd2 + Sd) * Sdd)
        ≤ Real.sqrt (Sdd2 * Sdd) + Real.sqrt (Sd * Sdd) := by
      have e : (Sdd2 + Sd) * Sdd = Sdd2 * Sdd + Sd * Sdd := by ring
      rw [e]
      exact sqrt_add_le_aux (mul_nonneg hSdd2 hSdd) (mul_nonneg hSd hSdd)
    have hstep5 : α ^ 2 * Real.sqrt (Sdd2 * Sdd) ≤ (α ^ 4 * Sdd2 + Sdd) / 2 := by
      have e : α ^ 2 * Real.sqrt (Sdd2 * Sdd) = Real.sqrt (α ^ 4 * (Sdd2 * Sdd)) := by
        rw [Real.sqrt_mul hα4n, sqrt_sq_four hα2]
      rw [e, show α ^ 4 * (Sdd2 * Sdd) = (α ^ 4 * Sdd2) * Sdd by ring]
      linarith [two_sqrt_mul_le hA0 hSdd]
    have hstep6 : α ^ 2 * Real.sqrt (Sd * Sdd) ≤ (α ^ 2 * Sd + Sdd) / 2 := by
      have e : α ^ 2 * Real.sqrt (Sd * Sdd) = Real.sqrt (α ^ 4 * (Sd * Sdd)) := by
        rw [Real.sqrt_mul hα4n, sqrt_sq_four hα2]
      rw [e, show α ^ 4 * (Sd * Sdd) = (α ^ 4 * Sd) * Sdd by ring]
      have h45 : (α ^ 4 * Sd) * Sdd ≤ (α ^ 2 * Sd) * Sdd := by
        have h : α ^ 4 * Sd ≤ α ^ 2 * Sd := by nlinarith [hSd, hα4n, hα21]
        exact mul_le_mul_of_nonneg_right h hSdd
      have h7 := two_sqrt_mul_le hA'0 hSdd
      have h8 : Real.sqrt ((α ^ 4 * Sd) * Sdd) ≤ Real.sqrt ((α ^ 2 * Sd) * Sdd) :=
        Real.sqrt_le_sqrt h45
      linarith [h7, h8]
    have hstep9 : α ^ 2 * (Real.sqrt (Sdd2 * Sdd) + Real.sqrt (Sd * Sdd))
        ≤ (α ^ 4 * Sdd2 + Sdd) / 2 + (α ^ 2 * Sd + Sdd) / 2 := by
      have h4' := mul_le_mul_of_nonneg_left hstep4 hα2
      have hdist : α ^ 2 * (Real.sqrt (Sdd2 * Sdd) + Real.sqrt (Sd * Sdd))
          = α ^ 2 * Real.sqrt (Sdd2 * Sdd) + α ^ 2 * Real.sqrt (Sd * Sdd) := by ring
      rw [hdist]
      linarith [h4', hstep5, hstep6]
    have hstep10 : (α ^ 4 * Sdd2 + Sdd) / 2 + (α ^ 2 * Sd + Sdd) / 2
        ≤ α ^ 4 * Sdd2 + α ^ 2 * Sd + Sdd := by linarith
    calc α ^ 2 * Real.sqrt (DD * TT)
        = Real.sqrt (α ^ 4 * (DD * TT)) := by
          rw [Real.sqrt_mul hα4n, sqrt_sq_four hα2]
      _ ≤ Real.sqrt (18 * (α ^ 4 * (Sdd2 + Sd) * Sdd)) := hstep2
      _ = Real.sqrt 18 * (α ^ 2 * Real.sqrt ((Sdd2 + Sd) * Sdd)) := hstep3
      _ ≤ Real.sqrt 18 * (α ^ 2 * (Real.sqrt (Sdd2 * Sdd) + Real.sqrt (Sd * Sdd))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hstep4 hα2) h18
      _ ≤ Real.sqrt 18 * ((α ^ 4 * Sdd2 + Sdd) / 2 + (α ^ 2 * Sd + Sdd) / 2) :=
          mul_le_mul_of_nonneg_left hstep9 h18
      _ ≤ Real.sqrt 18 * (α ^ 4 * Sdd2 + α ^ 2 * Sd + Sdd) :=
          mul_le_mul_of_nonneg_left hstep10 h18
  calc α ^ 2 * X ≤ α ^ 2 * (Ctb * (Z + Real.sqrt (DD * TT))) :=
        mul_le_mul_of_nonneg_left hmain hα2
    _ = Ctb * (α ^ 2 * Z + α ^ 2 * Real.sqrt (DD * TT)) := by ring
    _ ≤ Ctb * (α ^ 2 * Sd + Real.sqrt 18 * (α ^ 4 * Sdd2 + α ^ 2 * Sd + Sdd)) := by
        refine mul_le_mul_of_nonneg_left ?_ hCtb.le
        have h1 : α ^ 2 * Z ≤ α ^ 2 * Sd := mul_le_mul_of_nonneg_left hZ hα2
        linarith [h1, hsqrt]

/-- The final arithmetic of the family sum. -/
private theorem famSumArith {α : ℝ} (hα0 : 0 < α) (hα4 : α ≤ 1 / 4)
    {Sd Sdd2 Sdd : ℝ} (hSd : 0 ≤ Sd) (hSdd2 : 0 ≤ Sdd2) (hSdd : 0 ≤ Sdd) :
    α ^ 2 * Sd + Real.sqrt 18 * (α ^ 4 * Sdd2 + α ^ 2 * Sd + Sdd)
      ≤ (1 + 3 * Real.sqrt 18) * (α ^ 4 * Sdd2 + Sdd + α ^ 2 * Sd) := by
  have h18 : 0 ≤ Real.sqrt 18 := Real.sqrt_nonneg 18
  have hα2 : 0 ≤ α ^ 2 := by positivity
  have hα4n : 0 ≤ α ^ 4 := by positivity
  have hα21 : α ^ 2 ≤ 1 := by nlinarith [hα0, hα4, sq_nonneg α]
  have hA : 0 ≤ α ^ 4 * Sdd2 := mul_nonneg hα4n hSdd2
  have hSd' : 0 ≤ α ^ 2 * Sd := mul_nonneg hα2 hSd
  have hR : (0:ℝ) ≤ α ^ 4 * Sdd2 + Sdd + α ^ 2 * Sd := by linarith
  have hbracket : α ^ 4 * Sdd2 + α ^ 2 * Sd + Sdd
      ≤ 3 * (α ^ 4 * Sdd2 + Sdd + α ^ 2 * Sd) := by linarith
  have h1 : Real.sqrt 18 * (α ^ 4 * Sdd2 + α ^ 2 * Sd + Sdd)
      ≤ Real.sqrt 18 * (3 * (α ^ 4 * Sdd2 + Sdd + α ^ 2 * Sd)) :=
    mul_le_mul_of_nonneg_left hbracket h18
  have h2 : α ^ 2 * Sd ≤ α ^ 4 * Sdd2 + Sdd + α ^ 2 * Sd := by linarith
  rw [show (1 + 3 * Real.sqrt 18) * (α ^ 4 * Sdd2 + Sdd + α ^ 2 * Sd)
      = (α ^ 4 * Sdd2 + Sdd + α ^ 2 * Sd)
        + Real.sqrt 18 * (3 * (α ^ 4 * Sdd2 + Sdd + α ^ 2 * Sd)) by ring]
  linarith [h1, h2]

/-! ## The `X`-slot of the engine at the datum `D_z^r V` -/

/-- On `Iz ×ˢ Iθ` the two forms of the `X`-slot integrand agree (Clairaut on the open quadrant). -/
theorem famX_ae_eq {V : ℝ → ℝ → ℝ} (hV : Work.FTS.EllipticEst.SmoothOpen V) (r : ℕ) :
    (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
        * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter r V)) p.1 p.2) ^ 2)
      =ᵐ[MeasureTheory.volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)]
    (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
        * (Work.Spaces.Dz (Work.Spaces.DzIter r (Work.Spaces.pth V)) p.1 p.2) ^ 2) := by
  filter_upwards [Work.FTS.ClassC.VopGen.ae_mem_Q0_prod] with p hp
  have hcl : Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter r V)) p.1 p.2
      = Work.Spaces.Dz (Work.Spaces.DzIter r (Work.Spaces.pth V)) p.1 p.2 := by
    have h := Work.FTS.H2.Dz_congr_of_isOpen (u := Work.Spaces.pth (Work.Spaces.DzIter r V))
      (v := Work.Spaces.DzIter r (Work.Spaces.pth V)) Work.FTS.EllipticEst.isOpen_Q0
      (Work.FTS.EllipticEst.ThetaU.OpenSliceAux.pth_DzIter_eqOn_of_isOpen
        Work.FTS.EllipticEst.isOpen_Q0 (Work.FTS.EllipticEst.SmoothOpen.forall hV) r) hp
    simpa only [Function.uncurry] using h
  rw [hcl]

/-- **The `X`-slot of the engine at the datum `D_z^r V` is product-integrable**, from the
membership `HkMem α k (D_z∂_θV)` (`slotAux_slotZ_prod` applied to `∂_θV`). -/
theorem slotX_prod {k : ℕ} {α : ℝ} {V : ℝ → ℝ → ℝ}
    (hV : Work.FTS.EllipticEst.SmoothOpen V)
    (hmix : Work.Spaces.HkMem α k (Work.Spaces.Dz (Work.Spaces.pth V))) (r : ℕ) (hr : r ≤ k) :
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
        * Work.FTS.EllipticEst.thEta p.2
        * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter r V)) p.1 p.2) ^ 2)
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  have h := (Work.FTS.EllSol.PkgK5.TraceEngine.slotAux_slotZ_prod (k := k) (α := α)
    (V := Work.Spaces.pth V) (r := r) hV.pth hmix hr).1
  exact h.congr (famX_ae_eq hV r).symm

/-! ## The Tonelli bridge between the product and the iterated form -/

/-- The product-measure integral of the `X`-slot integrand equals the iterated integral which
`mixIntS` defines. -/
theorem famX_iterated {V : ℝ → ℝ → ℝ} (r : ℕ)
    (hint : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
        * Work.FTS.EllipticEst.thEta p.2
        * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter r V)) p.1 p.2) ^ 2)
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    (∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, (Work.Spaces.w p.1) ^ 2
        * Work.FTS.EllipticEst.thEta p.2
        * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter r V)) p.1 p.2) ^ 2)
      = ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z := by
  have hInt : MeasureTheory.Integrable (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
      * Work.FTS.EllipticEst.thEta p.2
      * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter r V)) p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [← Work.FTS.EllSol.PkgK5.TraceEngine.slotAux_volume_restrict_dom]
    exact hint
  have h1 : (∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, (Work.Spaces.w p.1) ^ 2
        * Work.FTS.EllipticEst.thEta p.2
        * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter r V)) p.1 p.2) ^ 2)
      = ∫ p, (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
          * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter r V)) p.1 p.2) ^ 2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [Work.FTS.EllSol.PkgK5.TraceEngine.slotAux_volume_restrict_dom]
  rw [h1, MeasureTheory.integral_prod (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
      * Work.FTS.EllipticEst.thEta p.2
      * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter r V)) p.1 p.2) ^ 2) hInt]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  rw [Work.EllipticEst.Core.mixIntS, ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  ring

/-! ## The family brick -/

/-- **The family interpolation with the four memberships.** -/
theorem famBrick (k : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (V : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.SmoothOpen V →
      (∀ z : ℝ, V z 0 = 0) → (∀ z : ℝ, V z (Real.pi / 2) = 0) →
      (∀ j : ℕ, j ≤ k + 1 → ∀ z : ℝ, 0 < z →
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j V z θ)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j V z θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) →
      Work.Spaces.HkMem α k (Work.Spaces.Dz V) →
      Work.Spaces.HkMem α k (Work.Spaces.DzIter 2 V) →
      Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 V) →
      Work.Spaces.HkMem α k (Work.Spaces.Dz (Work.Spaces.pth V)) →
      α ^ 2 * (∑ r ∈ Finset.range (k + 1),
          ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z)
        ≤ C * (α ^ 4 * Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V)
            + Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V)
            + α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V)) := by
  obtain ⟨Ctb, hCtb, htb⟩ := Work.FTS.EllSol.PkgK5.TraceEngine.traceBrick
  refine ⟨Ctb * ((k : ℝ) + 1) * (1 + 3 * Real.sqrt 18), by positivity, ?_⟩
  intro α V hα hα4 hV h0 hpi htr hd hdd htt hmix
  have hSd0 : 0 ≤ Work.Spaces.HkSq α k (Work.Spaces.Dz V) :=
    Work.Spaces.HkSq_nonneg α k (Work.Spaces.Dz V)
  have hSdd20 : 0 ≤ Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V) :=
    Work.Spaces.HkSq_nonneg α k (Work.Spaces.DzIter 2 V)
  have hSdd0 : 0 ≤ Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V) :=
    Work.Spaces.HkSq_nonneg α k (Work.Spaces.pthIter 2 V)
  have hα2 : (0 : ℝ) ≤ α ^ 2 := by positivity
  -- the per-`r` estimate
  have hper : ∀ r ∈ Finset.range (k + 1),
      α ^ 2 * (∫ z in Work.Spaces.Iz,
          Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z)
        ≤ Ctb * (α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V)
            + Real.sqrt 18 * (α ^ 4 * Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V)
                + α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V)
                + Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V))) := by
    intro r hr
    have hrk : r ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    have hrk1 : r + 1 ≤ k + 1 := Nat.succ_le_succ hrk
    obtain ⟨⟨hZi, hZv⟩, ⟨hTi, hTv⟩, ⟨hDDi, hDDv⟩⟩ :=
      Work.FTS.EllSol.PkgK5.TraceEngine.slotBounds (k := k) (α := α) (V := V)
        hV hdd htt hd r hrk
    have hXi : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
        * Work.FTS.EllipticEst.thEta p.2
        * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter r V)) p.1 p.2) ^ 2)
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := slotX_prod hV hmix r hrk
    have hmain := htb (Work.Spaces.DzIter r V) (hV.DzIter r)
      (fun z hz => (htr (r + 1) hrk1 z hz).1) (fun z hz => (htr (r + 1) hrk1 z hz).2)
      hXi hZi hDDi hTi
    rw [famX_iterated (V := V) r hXi] at hmain
    have hZ0 : 0 ≤ (∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, (Work.Spaces.w p.1) ^ 2
        * Work.FTS.EllipticEst.thEta p.2
        * (Work.Spaces.Dz (Work.Spaces.DzIter r V) p.1 p.2) ^ 2) :=
      MeasureTheory.setIntegral_nonneg (measurableSet_Ici.prod measurableSet_Icc)
        (fun p hp => mul_nonneg (mul_nonneg (sq_nonneg _)
          (Work.EllipticEst.Core.i0Aux.thEta_nonneg_Iθ hp.2)) (sq_nonneg _))
    have hT0 : 0 ≤ (∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, (Work.Spaces.w p.1) ^ 2
        * Work.FTS.EllipticEst.thEta p.2
        * (Work.Spaces.pthIter 2 (Work.Spaces.DzIter r V) p.1 p.2) ^ 2) :=
      MeasureTheory.setIntegral_nonneg (measurableSet_Ici.prod measurableSet_Icc)
        (fun p hp => mul_nonneg (mul_nonneg (sq_nonneg _)
          (Work.EllipticEst.Core.i0Aux.thEta_nonneg_Iθ hp.2)) (sq_nonneg _))
    have hDD0 : 0 ≤ (∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, (Work.Spaces.w p.1) ^ 2
        * Work.FTS.EllipticEst.thEta p.2
        * (Work.Spaces.DzIter 2 (Work.Spaces.DzIter r V) p.1 p.2
            + ((p.1 - 3) / (1 + p.1)) * Work.Spaces.Dz (Work.Spaces.DzIter r V) p.1 p.2) ^ 2) :=
      MeasureTheory.setIntegral_nonneg (measurableSet_Ici.prod measurableSet_Icc)
        (fun p hp => mul_nonneg (mul_nonneg (sq_nonneg _)
          (Work.EllipticEst.Core.i0Aux.thEta_nonneg_Iθ hp.2)) (sq_nonneg _))
    exact famTermArith hCtb hα hα4 hSd0 hSdd20 hSdd0 hZ0 hDD0 hT0 hZv hDDv hTv hmain
  -- summing over `r ≤ k`
  have hsum : (∑ r ∈ Finset.range (k + 1),
        α ^ 2 * (∫ z in Work.Spaces.Iz,
          Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z))
      ≤ ((k : ℝ) + 1) * (Ctb * (α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V)
            + Real.sqrt 18 * (α ^ 4 * Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V)
                + α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V)
                + Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V)))) := by
    calc (∑ r ∈ Finset.range (k + 1),
          α ^ 2 * (∫ z in Work.Spaces.Iz,
            Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z))
        ≤ ∑ _r ∈ Finset.range (k + 1),
            Ctb * (α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V)
              + Real.sqrt 18 * (α ^ 4 * Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V)
                  + α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V)
                  + Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V))) :=
          Finset.sum_le_sum hper
      _ = ((k : ℝ) + 1) * (Ctb * (α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V)
            + Real.sqrt 18 * (α ^ 4 * Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V)
                + α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V)
                + Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V)))) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  have hkey := famSumArith (α := α) hα hα4 hSd0 hSdd20 hSdd0
  have hk0 : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
  calc α ^ 2 * (∑ r ∈ Finset.range (k + 1),
        ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z)
      = ∑ r ∈ Finset.range (k + 1),
          α ^ 2 * (∫ z in Work.Spaces.Iz,
            Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z) := by
        rw [Finset.mul_sum]
    _ ≤ ((k : ℝ) + 1) * (Ctb * (α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V)
          + Real.sqrt 18 * (α ^ 4 * Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V)
              + α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V)
              + Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V)))) := hsum
    _ ≤ Ctb * ((k : ℝ) + 1) * (1 + 3 * Real.sqrt 18)
          * (α ^ 4 * Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V)
            + Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V)
            + α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V)) := by
        calc ((k : ℝ) + 1) * (Ctb * (α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V)
              + Real.sqrt 18 * (α ^ 4 * Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V)
                  + α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V)
                  + Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V))))
            ≤ ((k : ℝ) + 1) * (Ctb * ((1 + 3 * Real.sqrt 18)
                * (α ^ 4 * Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V)
                  + Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V)
                  + α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V)))) := by
              refine mul_le_mul_of_nonneg_left ?_ hk0
              refine mul_le_mul_of_nonneg_left hkey hCtb.le
          _ = Ctb * ((k : ℝ) + 1) * (1 + 3 * Real.sqrt 18)
                * (α ^ 4 * Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V)
                  + Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V)
                  + α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V)) := by ring

end Work.FTS.EllSol.PkgK5.K5c
