import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.ClassC.VopGen.CoreSplit
import Submission.Work.FTS.ClassC.VopGen.hkMem_pth2_Dz_AofGen
import Submission.Work.Spaces.integrable_prod_of_iterated
import Submission.Work.FTS.EllipticEst.Prop.thetaIbpTwoD

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

/-- The light-weighted slot integrand `(h)²·w²·σ`. -/
def Slt (α : ℝ) (h : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (h z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * sgm α θ

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
