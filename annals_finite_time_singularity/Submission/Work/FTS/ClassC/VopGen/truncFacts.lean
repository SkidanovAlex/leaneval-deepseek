import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.ClassC.VopGen.Gate
import Submission.Work.FTS.ClassC.VopGen.a11OfCore
import Submission.Work.FTS.ClassC.VopGen.hkMem_pth2_Dz_AofGen
import Submission.Work.FTS.EllipticEst.Prop.aslotTwoShift
import Submission.Work.FTS.EllipticEst.Prop.levelTopSlotsTwoBnds
import Submission.Work.FTS.EllipticEst.TT.ESW.Tk_B_le_chain_uniform
import Submission.Work.FTS_RegExport.RXT.StarVopWlInf
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.ClassC.VopGen.sliceAgmonAofGen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.ClassC.VopGen.sliceAgmonAofGen` — the a.e.-slicewise Agmon inequality for
`f = D_z (z²∂_z²Ψ)`

This module proves the "slice half" `SliceAgmonStmt` of the level-`2` core inequality
(`VopGen/CoreSplit.lean`): for every datum of the weak class `TT.EllWeakPos α 2 F Ψ` with
`0 < α ≤ 1/4`, for almost every `z > 0`,

  `∫_θ (∂_θ D_zA)² σ ≤ -∫_θ D_zA · ∂_θ²(D_zA) · σ`,   `σ = sin(2θ)^{2-γ(α)}`, `A = z²∂_z²Ψ`.

## The reduction

The `z`-variable is *parametrised away*: for each `z > 0` the angular slice
`f := θ ↦ D_zA(z,θ)` satisfies the pointwise Agmon inequality
`Work.FTS.ClassC.VopGen.muSliceAgmonPointwise`, whose three hypotheses are

* `ContDiffOn ℝ 2 f (Ioo 0 (π/2))` — the slice of the `C^∞`-function `D_zA` on the open quadrant
  (`SmoothOpen.curry_θ`);
* the two vanishing endpoint traces of `f` — a.e. `z`, this is
  `Prop.aof_tendsto_zero` (`D_zA = z ∂_z A`);
* the `σ`-weighted integrability of the second derivative `∂_θ²(D_zA)` — this is the
  `ℋ⁰`-honesty `VopGen.hkMem_pth2_Dz_AofGen` (the `∂_θ²`-slot of the level-`2` weak class)
  together with the weight transfer `VopGen.HkMem_zero_slice_mu`, which converts the level-`0`
  integrand `(∂_θ²(D_zA))² w² sin(2θ)^{-η}` of `ℋ⁰` into the slicewise
  `(∂_θ²(D_zA))² sin(2θ)^{2-γ}`.

The `∀ᵐ z` of the statement is taken with respect to `volume.restrict Iz` (`Iz = [0,∞)`); the
statement is proved a.e. on `Ioi 0` (where the traces live) and transported along the a.e.
equality `Ioi 0 =ᵐ Ici 0`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/

namespace Work.FTS.ClassC.VopGen

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-- **The a.e.-slicewise angular Agmon inequality** for `f = D_z(z²∂_z²Ψ)`. -/
theorem sliceAgmonAofGen : Work.FTS.ClassC.VopGen.SliceAgmonStmt := by
  intro α F Ψ hα hα4 h
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hA : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.EllipticEst.H2W.Aof Ψ) :=
    Work.FTS.EllipticEst.Prop.aofSmoothOpen hΨ
  have hg : Work.Spaces.HkMem α 0
      (Work.Spaces.pthIter 2 (Work.Spaces.Dz (Work.FTS.EllipticEst.H2W.Aof Ψ))) :=
    Work.FTS.ClassC.VopGen.hkMem_pth2_Dz_AofGen h
  have hsmg : Work.FTS.EllipticEst.SmoothOpen
      (Work.Spaces.pthIter 2 (Work.Spaces.Dz (Work.FTS.EllipticEst.H2W.Aof Ψ))) :=
    (hA.Dz).pth.pth
  have htr := Work.FTS.EllipticEst.Prop.aof_tendsto_zero hα hα4 h
  -- the slicewise inequality, a.e. on `Ioi 0`
  have key : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pth (Work.Spaces.Dz (Work.FTS.EllipticEst.H2W.Aof Ψ)) z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
        ≤ -(∫ θ in Work.Spaces.Iθ,
            Work.Spaces.Dz (Work.FTS.EllipticEst.H2W.Aof Ψ) z θ
              * (Work.Spaces.pthIter 2 (Work.Spaces.Dz (Work.FTS.EllipticEst.H2W.Aof Ψ))) z θ
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) := by
    filter_upwards [htr, MeasureTheory.ae_restrict_mem (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi]
      with z htz hz
    have hzpos : 0 < z := hz
    -- the slice is `C²` on the open angle interval
    have hcd : ContDiffOn ℝ 2
        (fun θ : ℝ => Work.Spaces.Dz (Work.FTS.EllipticEst.H2W.Aof Ψ) z θ)
        (Set.Ioo 0 (Real.pi / 2)) :=
      ((hA.Dz).curry_θ hzpos).of_le (by simp [Work.Stability.smoothOrder])
    -- the `σ`-weighted `L²`-integrability of `∂_θ²` of the slice
    have hDμ : MeasureTheory.IntegrableOn (fun θ : ℝ =>
        (deriv (deriv (fun θ' : ℝ => Work.Spaces.Dz (Work.FTS.EllipticEst.H2W.Aof Ψ) z θ')) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) (Set.Ioo 0 (Real.pi / 2)) := by
      have h1 := Work.FTS.ClassC.VopGen.HkMem_zero_slice_mu (α := α) hα hα4 hsmg hg z hzpos
      exact MeasureTheory.IntegrableOn.congr_set_ae h1 (by
        rw [Work.Spaces.Iθ]
        exact MeasureTheory.Ioo_ae_eq_Icc)
    exact Work.FTS.ClassC.VopGen.muSliceAgmonPointwise (α := α) hα hα4 hcd htz.1 htz.2 hDμ
  -- transport `Ioi 0` to `Iz = Ici 0` (they differ by the null set `{0}`)
  have hIoi : (MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Ioi (0 : ℝ))
      = MeasureTheory.volume.restrict (Set.Ici (0 : ℝ)) :=
    MeasureTheory.Measure.restrict_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))
  rw [show Work.Spaces.Iz = Set.Ici (0 : ℝ) from rfl, ← hIoi]
  exact key

end Work.FTS.ClassC.VopGen
end
-- ===== merged: Submission.Work.FTS.ClassC.VopGen.truncFacts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.ClassC.VopGen.truncFacts`

Infrastructure for the truncation half `VopGen.TruncStmt` of the level-`2` core inequality
(`Cores.Aux.coreASlot11`).

The module collects

* the elementary facts about the light angular weight `σ = sin(2θ)^{2-γ}` and its relation to the
  heavy weight `sin(2θ)^{-η}` of the `ℋ`-norms, including the identity
  `(sin(2θ)·Wt)² = w²·σ` of the mixed slots;
* the *pointwise dominations* of the six light-weighted slot integrands of the chain by the
  `HkIntegrand`-majorants whose honesty is supplied by the weak class `EllWeakPos α 2 F Ψ` and by
  `VopGen.hkMemPth2DzAof`;
* the measure-theoretic engine `slotFacts` producing, for a nonnegative slot with such a
  majorant, its slicewise, outer and product integrability (with the Fubini identity);
* the Fubini identity `prod_eq_iterated` for a general nonnegative honest pair.
-/
noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.ClassC.VopGen

set_option autoImplicit false
set_option maxHeartbeats 1600000

open Work.Spaces (HkSq HkMem HkIntegrand w Iz Iθ)

local notation "Q0" => Work.FTS.EllipticEst.Q0

/-- The light angular weight `σ = sin(2θ)^{2-γ}` (definitionally the weight appearing in the
target statements). -/
def sgm (α θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)


/-- The shifted datum `X = D_z(z²∂_z²Ψ)` of the level-`2` core inequality. -/
def XX (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := Work.Spaces.Dz (Work.FTS.EllipticEst.H2W.Aof Ψ)

/-- The angular datum `Y = ∂_θ²(z²∂_z²Ψ)` of the level-`2` core inequality. -/
def YY (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := Work.Spaces.pthIter 2 (Work.FTS.EllipticEst.H2W.Aof Ψ)

/-- `sin(2θ) ≥ 0` on `Iθ`. -/
theorem sinTwo_nonneg {θ : ℝ} (hθ : θ ∈ Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- The light angular weight is nonnegative on `Iθ`. -/
theorem sigma_nonneg {α θ : ℝ} (hθ : θ ∈ Iθ) : 0 ≤ (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) :=
  Real.rpow_nonneg (sinTwo_nonneg hθ) _

/-- The light angular weight is at most `1` on `Iθ` (for `α ≤ 1`). -/
theorem sigma_le_one {α θ : ℝ} (hα4 : α ≤ 1 / 4) (hθ : θ ∈ Iθ) :
    (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) ≤ 1 := by
  refine Real.rpow_le_one (sinTwo_nonneg hθ) (Real.sin_le_one _) ?_
  rw [Work.Spaces.gam]; linarith

/-- **The key weight comparison**: on `Iθ` the light weight `sin(2θ)^{2-γ}` is dominated by the
heavy weight `sin(2θ)^{-η}`. -/
theorem sigma_le_sEta {α θ : ℝ} (hα1 : α ≤ 1) (hθ : θ ∈ Iθ) :
    (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
  Work.FTS.EllipticEst.TT.sigA_le_sEta hα1 hθ

/-- **The mixed-slot weight identity** `(sin(2θ)·Wt α z θ)² = w z²·sin(2θ)^{2-γ}` on `Iθ`. -/
theorem sin_mul_Wt_sq {α : ℝ} (hα1 : α ≤ 1) (z θ : ℝ) (hθ : θ ∈ Iθ) :
    (Real.sin (2 * θ) * Work.Spaces.Wt α z θ) ^ 2
      = (w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := by
  have hs : 0 ≤ Real.sin (2 * θ) := sinTwo_nonneg hθ
  have h1 : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ (2 : ℕ)
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [← Real.rpow_mul_natCast hs (-(Work.Spaces.gam α / 2)) 2]
    congr 1; push_cast; ring
  have htwo : (Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      = (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := by
    have hne : ((2 : ℕ) : ℝ) + (-(Work.Spaces.gam α)) ≠ 0 := by
      rw [Work.Spaces.gam]; intro hc; linarith
    rw [← Real.rpow_natCast (Real.sin (2 * θ)) 2,
      ← Real.rpow_add' (x := Real.sin (2 * θ)) hs (y := ((2 : ℕ) : ℝ))
        (z := -(Work.Spaces.gam α)) hne]
    congr 1 <;> push_cast <;> ring
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow, mul_pow, h1]
  calc (Real.sin (2 * θ)) ^ 2 * ((w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      = (w z) ^ 2
          * ((Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by ring
    _ = (w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := by rw [htwo]

/-! ## The pointwise dominations of the six slot integrands -/

/-- **The `(1,1)`-slot of `A = z²∂_z²Ψ`.** -/
theorem dom_mixed11 {α : ℝ} {Ψ : ℝ → ℝ → ℝ} (hα1 : α ≤ 1)
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (z θ : ℝ) (hz : 0 < z) (hθ : 0 < θ) (hlt : θ < Real.pi / 2) :
    (Work.Spaces.pth (Work.Spaces.Dz (Work.FTS.EllipticEst.H2W.Aof Ψ)) z θ) ^ 2 * (w z) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
      ≤ HkIntegrand α 2 (Work.FTS.EllipticEst.H2W.Aof Ψ) z θ := by
  have hS : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.EllipticEst.H2W.Aof Ψ) :=
    Work.FTS.EllipticEst.Prop.aofSmoothOpen hΨ
  have hcla := Work.FTS.EllipticEst.Prop.pth_Dz_eq_of_smooth hS (z := z) (θ := θ)
      ⟨hz, hθ, hlt⟩
  have hmix : Work.Spaces.mixed 1 1 (Work.FTS.EllipticEst.H2W.Aof Ψ) z θ
      = Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.Dz (Work.FTS.EllipticEst.H2W.Aof Ψ)) z θ := by
    simp only [Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
      Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero, Work.Spaces.Dth, Work.Spaces.Dz,
      Work.Spaces.pth, Work.Spaces.pz] at hcla ⊢
    rw [deriv_const_mul_field (u := Real.sin (2 * θ))]
    rw [deriv_const_mul_field (u := z)]
    rw [deriv_const_mul_field (u := z)] at hcla
    rw [hcla]
    ring
  have hslot := Work.Spaces.sq_le_HkIntegrand_mixed α 2 (Work.FTS.EllipticEst.H2W.Aof Ψ) z θ 1 1
    (by norm_num) (by norm_num)
  have hkey : (Real.sin (2 * θ) * Work.Spaces.Wt α z θ) ^ 2
      = (w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) :=
    sin_mul_Wt_sq hα1 z θ ⟨hθ.le, hlt.le⟩
  calc (Work.Spaces.pth (Work.Spaces.Dz (Work.FTS.EllipticEst.H2W.Aof Ψ)) z θ) ^ 2 * (w z) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
      = (Work.Spaces.pth (Work.Spaces.Dz (Work.FTS.EllipticEst.H2W.Aof Ψ)) z θ) ^ 2
        * ((w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) := by ring
    _ = (Work.Spaces.pth (Work.Spaces.Dz (Work.FTS.EllipticEst.H2W.Aof Ψ)) z θ) ^ 2
        * (Real.sin (2 * θ) * Work.Spaces.Wt α z θ) ^ 2 := by rw [hkey]
    _ = ((Real.sin (2 * θ)
          * Work.Spaces.pth (Work.Spaces.Dz (Work.FTS.EllipticEst.H2W.Aof Ψ)) z θ)
          * Work.Spaces.Wt α z θ) ^ 2 := by ring
    _ = (Work.Spaces.mixed 1 1 (Work.FTS.EllipticEst.H2W.Aof Ψ) z θ * Work.Spaces.Wt α z θ) ^ 2 := by
        rw [hmix]
    _ ≤ HkIntegrand α 2 (Work.FTS.EllipticEst.H2W.Aof Ψ) z θ := hslot

/-- **The pure radial `j`-slot of `A = z²∂_z²Ψ`**, `j ≤ 2`. -/
theorem dom_pure {α : ℝ} {Ψ : ℝ → ℝ → ℝ} (hα1 : α ≤ 1) (z θ : ℝ) (j : ℕ) (hj : j ≤ 2)
    (hz : 0 < z) (hθ : 0 < θ) (hlt : θ < Real.pi / 2) :
    (Work.Spaces.DzIter j (Work.FTS.EllipticEst.H2W.Aof Ψ) z θ) ^ 2 * (w z) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
      ≤ HkIntegrand α 2 (Work.FTS.EllipticEst.H2W.Aof Ψ) z θ := by
  have hslot := Work.Spaces.sq_le_HkIntegrand_z α 2 (Work.FTS.EllipticEst.H2W.Aof Ψ) z θ j hj
  have hη : (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    sigma_le_sEta hα1 ⟨hθ.le, hlt.le⟩
  have hsq : (Work.Spaces.DzIter j (Work.FTS.EllipticEst.H2W.Aof Ψ) z θ
        * (w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.DzIter j (Work.FTS.EllipticEst.H2W.Aof Ψ) z θ) ^ 2 * (w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    rw [show Work.Spaces.DzIter j (Work.FTS.EllipticEst.H2W.Aof Ψ) z θ
          * (w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))
        = (Work.Spaces.DzIter j (Work.FTS.EllipticEst.H2W.Aof Ψ) z θ * w z)
          / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) from by ring]
    rw [Work.FTS.EllipticEst.Prop.div_rpow_half_sq_Iθ ⟨hθ.le, hlt.le⟩]
    ring
  rw [hsq] at hslot
  calc (Work.Spaces.DzIter j (Work.FTS.EllipticEst.H2W.Aof Ψ) z θ) ^ 2 * (w z) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
      ≤ (Work.Spaces.DzIter j (Work.FTS.EllipticEst.H2W.Aof Ψ) z θ) ^ 2 * (w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
        mul_le_mul_of_nonneg_left hη (by positivity)
    _ ≤ HkIntegrand α 2 (Work.FTS.EllipticEst.H2W.Aof Ψ) z θ := hslot

/-- **The general level-`0` domination**: any function `B` is dominated, in the light weight, by
its own `ℋ⁰`-integrand. -/
theorem dom_zero {α : ℝ} {B : ℝ → ℝ → ℝ} (hα1 : α ≤ 1) (z θ : ℝ)
    (hz : 0 < z) (hθ : 0 < θ) (hlt : θ < Real.pi / 2) :
    (B z θ) ^ 2 * (w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
      ≤ HkIntegrand α 0 B z θ := by
  rw [Work.FTS.EllipticEst.Prop.HkIntegrand_zero_apply]
  have hkey : (B z θ * (w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2
      = (B z θ) ^ 2 * (w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    rw [show B z θ * (w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))
        = (B z θ * w z) / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) from by ring]
    rw [Work.FTS.EllipticEst.Prop.div_rpow_half_sq_Iθ ⟨hθ.le, hlt.le⟩]
    ring
  rw [hkey]
  exact mul_le_mul_of_nonneg_left (sigma_le_sEta hα1 ⟨hθ.le, hlt.le⟩) (by positivity)

end Work.FTS.ClassC.VopGen
end
end
