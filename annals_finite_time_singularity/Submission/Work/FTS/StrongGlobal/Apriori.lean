/-
# `Work.FTS.StrongGlobal.Apriori` — **S4: the a-priori bound along a strong solution**

`apriori_strong` is item S4 of `Submission/Work/FTS/FTS_STRONG_ROUTE.md` §3: the `Pₙ = id`
version of the delivered Galerkin bootstrap
`Work.FTS.OpenPkg.AprioriOpen.galerkin_bound_explicit`.

**Statement.**  Let `IP` be a uniform coercive inner product (`Work.FTS.Nonlin.UnifIP`, the N2
obligation) and let `g` be a strong solution (`Work.FTS.StrongGlobal.StrongSolOn`) of the dynamic
modulated equation on `[0,T]`, whose datum satisfies the paper's smallness `Xn₄(g(0)) ≤ α²` and
along which

* the *energy identity* `E(τ) = IP α (g(τ)) (g(τ))` has the correct fake-time derivative
  (`E'(τ) = 2 IP α (∂_τg(τ)) (g(τ))`, `hEderiv`), and
* N4's pairing estimate `IP α (dynRHS) (g(τ)) ≤ CcN · Pbd α (Xn₄(g(τ)))` holds at every time at
  which `Xn₄ ≤ α^{7/4}` (`hPair`).

Then `Xn₄(g(τ)) ≤ C₀·α²` on the whole interval `[0,T]`, with `C₀ = Work.FTS.Apriori.C0` the
delivered constant (a function of `CcN, cc, clo, Cup, Ccs` only).

**Proof.**  This is the barrier argument of `Work.FTS.Apriori.barrier_within` applied to the
*energy functional* `E(τ) = IP α (g(τ)) (g(τ))` instead of the Galerkin coefficient energy
`∑ₖ cₖ(τ)²`:

* the coercivity of `𝓛_Γ^T` (`UnifIP.coer`) and the additivity of `IP` along the equation
  (`UnifIP.add_fst`, `UnifIP.smul_fst`) turn the pairing of `dynLin` with `g` into the dissipation
  `cc·HkSq₄`;
* `UnifIP.up` converts the level `E = Y = clo·C₀²α⁴` into `HkSq₄ ≥ Y/Cup`, and
  `UnifIP.lo` converts it into `Xn₄ ≤ C₀α²`, which is where N4's pairing estimate may be applied
  (`C0_mul_sq_le`);
* the closing inequality `Work.FTS.Apriori.energy_closing` then makes the derivative strictly
  negative at the level `Y`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongGlobal.Defs
import Submission.Work.FTS.Apriori.Barrier

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.StrongGlobal

open Work.FTS.Nonlin
open Work.FTS.Apriori
open Work.FTS.Galerkin (Fn Fam slice dynLin dynRHS)

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- **S4 — the a-priori bound along a strong solution** (design §3 S4).

For `α ≤ α₅ = Work.FTS.Apriori.alpha5 …` and a strong solution `g` on `[0,T]` of the dynamic
modulated equation with `Xn₄(g(0)) ≤ α²`, along which the energy identity `hEderiv` and N4's
pairing estimate `hPair` hold, the `ℋ⁴`-size stays below `C₀α²` for all `τ ∈ [0,T]`. -/
theorem apriori_strong (IP : ℝ → Fn → Fn → ℝ) {α₂ cc clo Cup Ccs CcN α₄ : ℝ}
    (hIP : UnifIP IP α₂ cc clo Cup Ccs) (hCcN : 0 < CcN) (hα₄ : 0 < α₄)
    {α : ℝ} (hα : 0 < α) (hα5 : α ≤ alpha5 CcN cc clo Cup Ccs α₂ α₄)
    {Φs : Fn} {EllSol : Fn → Fn} {g : Fam} {T : ℝ} (hT : 0 ≤ T)
    (hSol : StrongSolOn α Φs EllSol 0 T g)
    (hEderiv : ∀ τ ∈ Set.Icc 0 T,
      HasDerivWithinAt (fun s => IP α (slice g s) (slice g s))
        (2 * (IP α (dynLin α g τ) (slice g τ)
          + IP α (dynRHS α (PsiCan Φs EllSol g) g τ) (slice g τ))) (Set.Icc 0 T) τ)
    (hPair : ∀ τ ∈ Set.Icc 0 T, Xn α (slice g τ) ≤ α ^ (7 / 4 : ℝ) →
      IP α (dynRHS α (PsiCan Φs EllSol g) g τ) (slice g τ)
        ≤ CcN * Pbd α (Xn α (slice g τ)))
    (hXn0 : Xn α (slice g 0) ≤ α ^ 2) :
    ∀ τ ∈ Set.Icc 0 T, Xn α (slice g τ) ≤ C0 CcN cc clo Cup Ccs * α ^ 2 := by
  have hcc := hIP.pos.2.1
  have hclo := hIP.pos.2.2.1
  have hCup := hIP.pos.2.2.2.1
  have hCcs := hIP.pos.2.2.2.2
  have hαIoc : α ∈ Set.Ioc 0 α₂ :=
    ⟨hα, le_trans hα5 (le_trans alpha5_le_alpha2 le_rfl)⟩
  have hC₀ : 0 < C0 CcN cc clo Cup Ccs := C0_pos hCcN hcc hclo hCup hCcs
  set Yr : ℝ := clo * C0 CcN cc clo Cup Ccs ^ 2 * α ^ 4 with hYr
  have hYrpos : 0 < Yr := by
    rw [hYr]
    exact mul_pos (mul_pos hclo (pow_pos hC₀ 2)) (pow_pos hα 4)
  -- the energy of the datum is strictly below the barrier level
  have h0 : IP α (slice g 0) (slice g 0) < Yr := by
    have hreg0 : RegQ α 4 (slice g 0) := hSol.reg4 0 ⟨le_refl 0, hT⟩
    have hcs := hIP.cs α hαIoc (slice g 0) (slice g 0) hreg0 hreg0
    have hleabs : IP α (slice g 0) (slice g 0) ≤ |IP α (slice g 0) (slice g 0)| :=
      le_abs_self _
    have hbound : Ccs * Xn α (slice g 0) * Xn α (slice g 0) ≤ Ccs * (α ^ 2 * α ^ 2) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul hXn0 hXn0 (Work.Spaces.HkNorm_nonneg α 4 (slice g 0))
          (le_of_lt (pow_pos hα 2))) hCcs.le
    have hα4 : Ccs * (α ^ 2 * α ^ 2) = Ccs * α ^ 4 := by ring
    have hlt := mul_lt_mul_of_pos_right (Ccs_lt_lower (CcN := CcN) hcc hclo hCup hCcs)
      (pow_pos hα 4)
    rw [hYr]
    linarith
  -- continuity of the energy on `[0,T]`
  have hcont : ContinuousOn (fun s => IP α (slice g s) (slice g s)) (Set.Icc 0 T) :=
    fun ρ hρ => (hEderiv ρ hρ).continuousWithinAt
  -- the energy is strictly decreasing at the barrier level
  have hneg : ∀ ρ ∈ Set.Ico 0 T,
      IP α (slice g ρ) (slice g ρ) = Yr →
      (2 * (IP α (dynLin α g ρ) (slice g ρ)
        + IP α (dynRHS α (PsiCan Φs EllSol g) g ρ) (slice g ρ))) < 0 := by
    intro ρ hρ hρY
    have hρIcc : ρ ∈ Set.Icc 0 T := ⟨hρ.1, hρ.2.le⟩
    have hcoerρ : CoerAdm α (slice g ρ) := hSol.coer ρ hρIcc
    have hregρ : RegQ α 4 (slice g ρ) := hSol.reg4 ρ hρIcc
    have hlo := hIP.lo α hαIoc (slice g ρ) hcoerρ
    have hup := hIP.up α hαIoc (slice g ρ) hcoerρ
    set X : ℝ := Xn α (slice g ρ) with hX
    have hXnn : 0 ≤ X := Work.Spaces.HkNorm_nonneg α 4 (slice g ρ)
    -- `HkSq ≥ Yr / Cup` at the barrier level
    have hHkge : Yr / Cup ≤ Work.Spaces.HkSq α 4 (slice g ρ) := by
      rw [div_le_iff₀ hCup]
      linarith [hup, hρY]
    -- `X ≤ C₀α²` at the barrier level
    have hXle : X ≤ C0 CcN cc clo Cup Ccs * α ^ 2 := by
      have hHkle : Work.Spaces.HkSq α 4 (slice g ρ)
          ≤ C0 CcN cc clo Cup Ccs ^ 2 * α ^ 4 := by
        have h1 : clo * Work.Spaces.HkSq α 4 (slice g ρ)
            ≤ clo * (C0 CcN cc clo Cup Ccs ^ 2 * α ^ 4) := by
          have hh := hlo
          rw [hρY, hYr] at hh
          rw [mul_assoc] at hh
          exact hh
        exact le_of_mul_le_mul_left h1 hclo
      rw [hX]
      show Work.Spaces.HkNorm α 4 (slice g ρ) ≤ C0 CcN cc clo Cup Ccs * α ^ 2
      have h2 : Work.Spaces.HkSq α 4 (slice g ρ)
          ≤ (C0 CcN cc clo Cup Ccs * α ^ 2) ^ 2 := by
        rw [mul_pow, show (α ^ 2) ^ 2 = α ^ 4 by ring]
        exact hHkle
      calc Real.sqrt (Work.Spaces.HkSq α 4 (slice g ρ))
          ≤ Real.sqrt ((C0 CcN cc clo Cup Ccs * α ^ 2) ^ 2) := Real.sqrt_le_sqrt h2
        _ = C0 CcN cc clo Cup Ccs * α ^ 2 := Real.sqrt_sq (by positivity)
    -- the smallness under which N4's pairing estimate applies
    have h7 : Xn α (slice g ρ) ≤ α ^ (7 / 4 : ℝ) := by
      rw [show Xn α (slice g ρ) = X from hX.symm]
      exact le_trans hXle (C0_mul_sq_le hC₀ hα (le_trans hα5 alpha5_le_C0pow))
    -- coercivity of `dynLin = -𝓛_Γ^T`
    have hregLT : RegQ α 4 (Work.Coercivity.LGammaT α (slice g ρ)) := by
      have h := regQ_neg (hSol.regLin ρ hρIcc)
      simpa [dynLin] using h
    have hdynLin : IP α (dynLin α g ρ) (slice g ρ)
        = - IP α (Work.Coercivity.LGammaT α (slice g ρ)) (slice g ρ) := by
      have h := hIP.smul_fst α hαIoc (-1) (Work.Coercivity.LGammaT α (slice g ρ))
        (slice g ρ) hregLT hregρ
      have hfun : (fun z θ => (-1) * Work.Coercivity.LGammaT α (slice g ρ) z θ)
          = dynLin α g ρ := by
        funext z θ
        show (-1) * Work.Coercivity.LGammaT α (slice g ρ) z θ
          = -(Work.Coercivity.LGammaT α (slice g ρ) z θ)
        ring
      rw [hfun] at h
      simpa using h
    have hcoer' : cc * Work.Spaces.HkSq α 4 (slice g ρ)
        ≤ IP α (Work.Coercivity.LGammaT α (slice g ρ)) (slice g ρ) :=
      hIP.coer α hαIoc (slice g ρ) hcoerρ
    -- N4's pairing estimate
    have hN4 := hPair ρ hρIcc h7
    -- the closing arithmetic
    have hclosing := energy_closing (CcN := CcN) (α := α) (α₂ := α₂) (α₄ := α₄)
      hCcN hcc hclo hCup hCcs hα hα5
    have hPbd := Pbd_mono hα hXnn hXle
    have hYrCup : kappa cc clo Cup * C0 CcN cc clo Cup Ccs ^ 2 * α ^ 4 = cc * (Yr / Cup) := by
      rw [hYr, kappa, div_eq_mul_inv]
      ring
    have hstep1 : IP α (dynLin α g ρ) (slice g ρ) ≤ - cc * Work.Spaces.HkSq α 4 (slice g ρ) := by
      rw [hdynLin]
      linarith [hcoer']
    have hstep2 : cc * (Yr / Cup) ≤ cc * Work.Spaces.HkSq α 4 (slice g ρ) :=
      mul_le_mul_of_nonneg_left hHkge hcc.le
    have hstep3 : CcN * Pbd α (Xn α (slice g ρ)) ≤ CcN * Pbd α (C0 CcN cc clo Cup Ccs * α ^ 2) :=
      mul_le_mul_of_nonneg_left hPbd hCcN.le
    linarith [hstep1, hstep2, hstep3, hN4, hclosing, hYrCup]
  -- the barrier
  have hbarrier : ∀ τ ∈ Set.Icc 0 T, IP α (slice g τ) (slice g τ) ≤ Yr :=
    barrier_within hcont h0 (fun τ hτ => hEderiv τ ⟨hτ.1, hτ.2.le⟩) hneg
  intro τ hτ
  have hcoerτ : CoerAdm α (slice g τ) := hSol.coer τ hτ
  have hloτ := hIP.lo α hαIoc (slice g τ) hcoerτ
  have hEτ := hbarrier τ hτ
  have hHkle : Work.Spaces.HkSq α 4 (slice g τ)
      ≤ C0 CcN cc clo Cup Ccs ^ 2 * α ^ 4 := by
    have h1 : clo * Work.Spaces.HkSq α 4 (slice g τ)
        ≤ clo * (C0 CcN cc clo Cup Ccs ^ 2 * α ^ 4) := by
      have hh : clo * Work.Spaces.HkSq α 4 (slice g τ) ≤ Yr := le_trans hloτ hEτ
      rw [hYr] at hh
      rw [mul_assoc] at hh
      exact hh
    exact le_of_mul_le_mul_left h1 hclo
  show Work.Spaces.HkNorm α 4 (slice g τ) ≤ C0 CcN cc clo Cup Ccs * α ^ 2
  have h2 : Work.Spaces.HkSq α 4 (slice g τ)
      ≤ (C0 CcN cc clo Cup Ccs * α ^ 2) ^ 2 := by
    rw [mul_pow, show (α ^ 2) ^ 2 = α ^ 4 by ring]
    exact hHkle
  calc Real.sqrt (Work.Spaces.HkSq α 4 (slice g τ))
      ≤ Real.sqrt ((C0 CcN cc clo Cup Ccs * α ^ 2) ^ 2) := Real.sqrt_le_sqrt h2
    _ = C0 CcN cc clo Cup Ccs * α ^ 2 := Real.sqrt_sq (by positivity)

end Work.FTS.StrongGlobal
