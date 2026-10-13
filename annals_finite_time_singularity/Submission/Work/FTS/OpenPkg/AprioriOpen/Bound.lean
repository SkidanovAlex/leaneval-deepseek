/-
# The a-priori bound: the Galerkin energy bootstrap (design §2.3 and §4 L-N5.6–N5.7)

This module contains the centre of node N5:

* `coerAdm_of_galClass` — the profiles of the Galerkin span lie in the coercivity class;
* `energy_deriv_within` — the fake-time derivative of the coefficient energy `∑ₖ cₖ²` along a
  solution of the projected ODE is `2 ∑ₖ cₖ ċₖ` (the exact energy identity, written for the
  within-derivative on `[0,T]` provided by `IsSolOn`);
* `hInit` — the initial energy bound (design L-N5.6), from Bessel's inequality;
* `galerkin_bound` — **the main theorem of the chapter** (design L-N5.7): the coefficients and the
  `ℋ⁴`-norm of every Galerkin solution stay in the a-priori ball, with constants `α₅, C₀`
  independent of `τ, n, T, α`.

The bootstrap is the barrier argument of `Submission/Work/FTS/Apriori/Barrier.lean`: at the level
`Y = clo·C₀²·α⁴` the dissipation `2κC₀²α⁴` dominates the nonlinearity `2Cₙ·Pbd α (C₀α²)` by
`energy_closing`, so the energy can never cross `Y`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.Apriori.Arith
import Submission.Work.FTS.Apriori.Barrier
import Submission.Work.FTS.OpenPkg.AprioriOpen.GalSpanOpen
import Submission.Work.FTS.Galerkin.Projection

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg.AprioriOpen

open Work.FTS.Apriori

open Work.FTS.Nonlin
open Work.FTS.Galerkin (Fn Fam slice galFun galFam galField galRHS coeffOf IsSolOn IsGalFam
  ConvLocUnif ConvPoint Slab muDyn lamDyn dynLin dynRHS prof)

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- **`GalClass` refines `CoerAdm`**: the profiles of the Galerkin span are admissible for the
coercivity estimates (only the order drops from `6` to `5`). -/
theorem coerAdm_of_galClass {α : ℝ} {g : Fn} (h : GalClass α g) : CoerAdm α g :=
  ⟨regQ_mono (k := 6) (by norm_num) h.reg, h.vanish, h.axis, h.l12⟩

/-- **The exact energy identity, differentiated**: along a curve of coefficients satisfying the
projected ODE (in the within-`[0,T]` form of `IsSolOn`), the derivative of `∑ₖ cₖ²` is
`2 ∑ₖ cₖ ċₖ`. -/
theorem energy_deriv_within {α : ℝ} {IP : Fn → Fn → ℝ} {φ : ℕ → Fn} {n : ℕ} {Psi : Fam → Fam}
    {c : ℝ → Fin n → ℝ} {T : ℝ}
    (hc : ∀ τ ∈ Set.Icc 0 T, HasDerivWithinAt (fun s => c s)
      (galField α IP φ n Psi τ (c τ)) (Set.Icc 0 T) τ) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 T) :
    HasDerivWithinAt (fun s => ∑ k : Fin n, (c s k) ^ 2)
      (2 * ∑ k : Fin n, c τ k * galField α IP φ n Psi τ (c τ) k) (Set.Icc 0 T) τ := by
  have hcoord : ∀ k : Fin n, HasDerivWithinAt (fun s => c s k)
      (galField α IP φ n Psi τ (c τ) k) (Set.Icc 0 T) τ :=
    fun k => hasDerivWithinAt_pi.mp (hc τ hτ) k
  have h : HasDerivWithinAt (fun s => ∑ k : Fin n, (c s k) ^ 2)
      (∑ k : Fin n, 2 * (c τ k) ^ (2 - 1) * galField α IP φ n Psi τ (c τ) k)
      (Set.Icc 0 T) τ := by
    have h0 := HasDerivWithinAt.sum (u := (Finset.univ : Finset (Fin n)))
      (fun k _ => (hcoord k).pow 2)
    have hfun : (∑ k : Fin n, (fun s => c s k) ^ 2)
        = fun s => ∑ k : Fin n, (c s k) ^ 2 := by
      funext s
      simp [Finset.sum_apply, Pi.pow_apply]
    rw [hfun] at h0
    exact h0
  have h2 : (∑ k : Fin n, 2 * (c τ k) ^ (2 - 1) * galField α IP φ n Psi τ (c τ) k)
      = 2 * ∑ k : Fin n, c τ k * galField α IP φ n Psi τ (c τ) k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    norm_num
    ring
  rw [h2] at h
  exact h

/-- The a-priori level `Y = clo·C₀²·α⁴` is the square of the a-priori radius
`√clo·C₀·α²`. -/
theorem Rstar_sq {clo C₀ α : ℝ} (hclo : 0 ≤ clo) (hC₀ : 0 ≤ C₀) :
    (Real.sqrt clo * C₀ * α ^ 2) ^ 2 = clo * C₀ ^ 2 * α ^ 4 := by
  rw [mul_pow, mul_pow, Real.sq_sqrt hclo]
  ring

/-- **`hInit`** (design §4 L-N5.6): the projected datum lies in the a-priori ball
`R = √clo·C₀·α²`.  The proof is Bessel's inequality `bessel_galBasis` plus Cauchy–Schwarz for the
inner product and the smallness `|g₀|_{ℋ⁴} ≤ α²`. -/
theorem hInit (IP : ℝ → Fn → Fn → ℝ) {α₂ cc clo Cup Ccs CcN : ℝ}
    (hIP : UnifIP IP α₂ cc clo Cup Ccs) {α : ℝ} (hα : α ∈ Set.Ioc 0 α₂) {g₀ : Fn}
    (hRegQ : RegQ α 4 g₀) (hXn : Xn α g₀ ≤ α ^ 2) {φ : ℕ → Fn} (hφ : GalBasis α IP φ) :
    ∀ n, ∑ k : Fin n, (coeffOf (IP α) g₀ φ n k) ^ 2
      ≤ (Real.sqrt clo * C0 CcN cc clo Cup Ccs * α ^ 2) ^ 2 := by
  have hcc := hIP.pos.2.1
  have hclo := hIP.pos.2.2.1
  have hCup := hIP.pos.2.2.2.1
  have hCcs := hIP.pos.2.2.2.2
  have hαpos : 0 < α := hα.1
  have hC₀ : 0 < C0 CcN cc clo Cup Ccs := C0_pos' hclo hCcs
  have hkey : Ccs < clo * C0 CcN cc clo Cup Ccs ^ 2 :=
    Ccs_lt_lower (CcN := CcN) hcc hclo hCup hCcs
  intro n
  have hb := bessel_galBasis hIP hα hφ hRegQ n
  have hcs := hIP.cs α hα g₀ g₀ hRegQ hRegQ
  have hIPle : IP α g₀ g₀ ≤ Ccs * α ^ 4 := by
    have h1 : IP α g₀ g₀ ≤ |IP α g₀ g₀| := le_abs_self _
    have h2 : Ccs * Xn α g₀ * Xn α g₀ ≤ Ccs * (α ^ 2 * α ^ 2) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul hXn hXn (Work.Spaces.HkNorm_nonneg α 4 g₀)
          (le_of_lt (pow_pos hαpos 2))) hCcs.le
    have h3 : Ccs * (α ^ 2 * α ^ 2) = Ccs * α ^ 4 := by ring
    linarith [h1, hcs, h2, h3]
  refine le_trans hb (le_trans hIPle ?_)
  rw [Rstar_sq hclo.le hC₀.le]
  exact le_of_lt (mul_lt_mul_of_pos_right hkey (pow_pos hαpos 4))

/-- **The a-priori bound (main theorem of node N5)** — design §4 L-N5.7.  There are constants
`α₅, C₀` (independent of `τ, n, T` and `α`) such that, for every `α ∈ (0, α₅]` and every
admissible datum with `|g₀|_{ℋ⁴} ≤ α²`, every solution of the projected Galerkin ODE on `[0,T]`
satisfies `∑ₖ cₖ(τ)² ≤ (√clo·C₀·α²)²` and `|∑ₖ cₖ(τ)φₖ|_{ℋ⁴} ≤ C₀α²` for all `τ ∈ [0,T]`.

The a-priori input is the Galerkin energy inequality `GalEnergyIneq` — the assembly of N2's
coercivity clause with N4's pairing estimate along the exact energy identity
(`galerkin_energy_ineq`, design §4 L-N5.4).  The remaining hypotheses are the design's own data:
the stream-function packages (`Work.FTS.VocabO.StarPkgo`, `Work.FTS.VocabO.EllPkgGo`) and the basis class (`GalBasis`); they are not
used by the bootstrap itself but are the inputs through which the energy inequality is discharged,
and they are kept so that the statement has exactly the shape of design §4 L-N5.7. -/
theorem galerkin_bound_explicit (IP : ℝ → Fn → Fn → ℝ) {α₂ cc clo Cup Ccs Ce Cs CcN α₄ : ℝ}
    (hIP : UnifIP IP α₂ cc clo Cup Ccs) (hCe : 0 < Ce) (hCs : 0 < Cs) (hCcN : 0 < CcN)
    (hα₄ : 0 < α₄) :
    ∀ α : ℝ, 0 < α → α ≤ alpha5 CcN cc clo Cup Ccs α₂ α₄ →
      ∀ (Φs : Fn) (EllSol : Fn → Fn) (φ : ℕ → Fn) (g₀ : Fn),
        Work.FTS.VocabO.StarPkgo α Cs Φs → (∀ g, GalClass α g → Work.FTS.VocabO.EllPkgGo α Ce g (EllSol g)) →
        GalBasis α IP φ → LocData.DataAdm α g₀ → Construction.L12 g₀ 0 = 0 →
        RegQ α 4 g₀ → Xn α g₀ ≤ α ^ 2 →
        GalEnergyIneq IP α cc CcN φ (PsiCan Φs EllSol) g₀ →
        ∀ (n : ℕ) (T : ℝ), 0 ≤ T → ∀ c : ℝ → Fin n → ℝ,
          IsSolOn (galField α (IP α) φ n (PsiCan Φs EllSol)) (coeffOf (IP α) g₀ φ n) T c →
          ∀ τ ∈ Set.Icc 0 T,
            ∑ k : Fin n, (c τ k) ^ 2
                ≤ (Real.sqrt clo * C0 CcN cc clo Cup Ccs * α ^ 2) ^ 2 ∧
            Xn α (galFun φ (c τ)) ≤ C0 CcN cc clo Cup Ccs * α ^ 2 := by
  intro α hαpos hα5 Φs EllSol φ g₀ hStar hEllPkg hGal hData hL12 hRegQ hXn hEnergy
  intro n T hT c hc
  have hcc := hIP.pos.2.1
  have hclo := hIP.pos.2.2.1
  have hCup := hIP.pos.2.2.2.1
  have hCcs := hIP.pos.2.2.2.2
  have hαIoc : α ∈ Set.Ioc 0 α₂ :=
    ⟨hαpos, le_trans hα5 (le_trans alpha5_le_alpha2 le_rfl)⟩
  have hC₀ : 0 < C0 CcN cc clo Cup Ccs := C0_pos hCcN hcc hclo hCup hCcs
  have hα1 : α ≤ 1 / 4 := le_trans hα5 alpha5_le_quarter
  have hgalClass : ∀ ρ : ℝ, GalClass α (galFun φ (c ρ)) := fun ρ => hGal.cls n (c ρ)
  have hcoer : ∀ ρ : ℝ, CoerAdm α (galFun φ (c ρ)) := fun ρ => coerAdm_of_galClass (hgalClass ρ)
  have hiso : Work.FTS.Galerkin.IsIPOrthonormal (IP α) φ :=
    isIPOrthonormal_of_galBasis hIP hαIoc hGal
  set Yr : ℝ := clo * C0 CcN cc clo Cup Ccs ^ 2 * α ^ 4 with hYr
  have hYrpos : 0 < Yr := by
    rw [hYr]
    exact mul_pos (mul_pos hclo (pow_pos hC₀ 2)) (pow_pos hαpos 4)
  -- the energy identity and the initial bound
  have hEgg : ∀ ρ : ℝ, IP α (galFun φ (c ρ)) (galFun φ (c ρ))
      = ∑ k : Fin n, (c ρ k) ^ 2 := fun ρ => hiso.self n (c ρ)
  have h0 : (∑ k : Fin n, (c 0 k) ^ 2) < Yr := by
    have hb := bessel_galBasis hIP hαIoc hGal hRegQ n
    have hcs := hIP.cs α hαIoc g₀ g₀ hRegQ hRegQ
    have hIPle : IP α g₀ g₀ ≤ Ccs * α ^ 4 := by
      have h1 : IP α g₀ g₀ ≤ |IP α g₀ g₀| := le_abs_self _
      have h2 : Ccs * Xn α g₀ * Xn α g₀ ≤ Ccs * (α ^ 2 * α ^ 2) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul hXn hXn (Work.Spaces.HkNorm_nonneg α 4 g₀)
            (le_of_lt (pow_pos hαpos 2))) hCcs.le
      have h3 : Ccs * (α ^ 2 * α ^ 2) = Ccs * α ^ 4 := by ring
      linarith [h1, hcs, h2, h3]
    have h5 : (∑ k : Fin n, (c 0 k) ^ 2) ≤ IP α g₀ g₀ := by
      rw [hc.1]; exact hb
    have h4 : Ccs * α ^ 4
        < clo * C0 CcN cc clo Cup Ccs ^ 2 * α ^ 4 :=
      mul_lt_mul_of_pos_right (Ccs_lt_lower (CcN := CcN) hcc hclo hCup hCcs)
        (pow_pos hαpos 4)
    rw [hYr]
    linarith
  -- the derivative of the energy along the solution
  have hEdot : ∀ ρ ∈ Set.Icc 0 T, HasDerivWithinAt
      (fun s => ∑ k : Fin n, (c s k) ^ 2)
      (2 * ∑ k : Fin n, c ρ k * galField α (IP α) φ n (PsiCan Φs EllSol) ρ (c ρ) k)
      (Set.Icc 0 T) ρ :=
    fun ρ hρ => energy_deriv_within (IP := IP α) (Psi := PsiCan Φs EllSol) hc.2 hρ
  have hcont : ContinuousOn (fun s => ∑ k : Fin n, (c s k) ^ 2) (Set.Icc 0 T) :=
    fun ρ hρ => (hEdot ρ hρ).continuousWithinAt
  -- the barrier hypothesis
  have hneg : ∀ ρ ∈ Set.Ico 0 T,
      (∑ k : Fin n, (c ρ k) ^ 2) = Yr →
      (2 * ∑ k : Fin n, c ρ k * galField α (IP α) φ n (PsiCan Φs EllSol) ρ (c ρ) k) < 0 := by
    intro ρ hρ hρY
    set X : ℝ := Xn α (galFun φ (c ρ)) with hX
    have hXnn : 0 ≤ X := Work.Spaces.HkNorm_nonneg α 4 _
    have hlo := hIP.lo α hαIoc (galFun φ (c ρ)) (hcoer ρ)
    have hup := hIP.up α hαIoc (galFun φ (c ρ)) (hcoer ρ)
    have hEggρ : IP α (galFun φ (c ρ)) (galFun φ (c ρ)) = Yr := by
      rw [hEgg ρ, hρY]
    -- `Cup·HkSq ≥ Yr`, hence `HkSq ≥ Yr/Cup`
    have hHkge : Yr / Cup ≤ Work.Spaces.HkSq α 4 (galFun φ (c ρ)) := by
      rw [div_le_iff₀ hCup]
      rw [hEggρ] at hup
      linarith [hup, mul_comm Cup (Work.Spaces.HkSq α 4 (galFun φ (c ρ)))]
    -- `clo·HkSq ≤ Yr`, hence `X ≤ C₀α²`
    have hHkle : Work.Spaces.HkSq α 4 (galFun φ (c ρ))
        ≤ C0 CcN cc clo Cup Ccs ^ 2 * α ^ 4 := by
      have h1 : clo * Work.Spaces.HkSq α 4 (galFun φ (c ρ))
          ≤ clo * (C0 CcN cc clo Cup Ccs ^ 2 * α ^ 4) := by
        rw [hEggρ, hYr, mul_assoc] at hlo
        exact hlo
      exact le_of_mul_le_mul_left h1 hclo
    have hXle : X ≤ C0 CcN cc clo Cup Ccs * α ^ 2 := by
      rw [hX]
      show Work.Spaces.HkNorm α 4 (galFun φ (c ρ))
        ≤ C0 CcN cc clo Cup Ccs * α ^ 2
      have h2 : Work.Spaces.HkSq α 4 (galFun φ (c ρ))
          ≤ (C0 CcN cc clo Cup Ccs * α ^ 2) ^ 2 := by
        rw [mul_pow, show (α ^ 2) ^ 2 = α ^ 4 by ring]
        exact hHkle
      calc Real.sqrt (Work.Spaces.HkSq α 4 (galFun φ (c ρ)))
          ≤ Real.sqrt ((C0 CcN cc clo Cup Ccs * α ^ 2) ^ 2) := Real.sqrt_le_sqrt h2
        _ = C0 CcN cc clo Cup Ccs * α ^ 2 := Real.sqrt_sq (by positivity)
    -- the smallness under which the pairing estimate applies
    have h7 : Xn α (galFun φ (c ρ)) ≤ α ^ (7 / 4 : ℝ) := by
      rw [show Xn α (galFun φ (c ρ)) = X from hX.symm]
      exact le_trans hXle (C0_mul_sq_le hC₀ hαpos (le_trans hα5 alpha5_le_C0pow))
    -- the energy inequality at the barrier level
    have hineq := hEnergy n T c hc ρ ⟨hρ.1, hρ.2.le⟩ h7
    have hclosing := energy_closing (CcN := CcN) (α := α) (α₂ := α₂) (α₄ := α₄)
      hCcN hcc hclo hCup hCcs hαpos hα5
    have hPbd := Pbd_mono hαpos hXnn hXle
    have h1 : Yr / Cup = (clo / Cup) * C0 CcN cc clo Cup Ccs ^ 2 * α ^ 4 := by
      rw [hYr, div_eq_mul_inv, div_eq_mul_inv]; ring
    have hkappa : cc * ((clo / Cup) * C0 CcN cc clo Cup Ccs ^ 2 * α ^ 4)
        = kappa cc clo Cup * C0 CcN cc clo Cup Ccs ^ 2 * α ^ 4 := by
      rw [kappa, div_eq_mul_inv]; ring
    have h2 : (2 * ∑ k : Fin n, c ρ k * galField α (IP α) φ n (PsiCan Φs EllSol) ρ (c ρ) k)
        ≤ -2 * (kappa cc clo Cup * C0 CcN cc clo Cup Ccs ^ 2 * α ^ 4)
          + 2 * CcN * Pbd α (C0 CcN cc clo Cup Ccs * α ^ 2) := by
      have h3 : -2 * cc * Work.Spaces.HkSq α 4 (galFun φ (c ρ))
          ≤ -2 * (kappa cc clo Cup * C0 CcN cc clo Cup Ccs ^ 2 * α ^ 4) := by
        have h5 : (clo / Cup) * C0 CcN cc clo Cup Ccs ^ 2 * α ^ 4
            ≤ Work.Spaces.HkSq α 4 (galFun φ (c ρ)) := h1 ▸ hHkge
        rw [← hkappa]
        nlinarith [h5, hcc]
      have h4 : 2 * CcN * Pbd α (Xn α (galFun φ (c ρ)))
          ≤ 2 * CcN * Pbd α (C0 CcN cc clo Cup Ccs * α ^ 2) := by
        rw [show Xn α (galFun φ (c ρ)) = X from hX.symm]
        exact mul_le_mul_of_nonneg_left hPbd (by linarith [hCcN.le])
      have h6 := add_le_add h3 h4
      linarith [hineq, h6]
    have h7 := mul_lt_mul_of_pos_left hclosing (by norm_num : (0:ℝ) < 2)
    linarith [h2, h7]
  -- the barrier
  have hbarrier := barrier_within hcont h0 (fun τ hτ => hEdot τ ⟨hτ.1, hτ.2.le⟩) hneg
  intro τ hτ
  have hEτ : (∑ k : Fin n, (c τ k) ^ 2) ≤ Yr := hbarrier τ hτ
  constructor
  · rw [Rstar_sq (le_of_lt hclo) (le_of_lt hC₀)]
    exact hEτ
  · show Work.Spaces.HkNorm α 4 (galFun φ (c τ)) ≤ C0 CcN cc clo Cup Ccs * α ^ 2
    have hlo := hIP.lo α hαIoc (galFun φ (c τ)) (hcoer τ)
    have h1 : clo * Work.Spaces.HkSq α 4 (galFun φ (c τ))
        ≤ clo * (C0 CcN cc clo Cup Ccs ^ 2 * α ^ 4) := by
      have hA : clo * Work.Spaces.HkSq α 4 (galFun φ (c τ)) ≤ Yr := by
        rw [hEgg τ] at hlo
        exact le_trans hlo hEτ
      rwa [hYr, mul_assoc] at hA
    have h2 : Work.Spaces.HkSq α 4 (galFun φ (c τ))
        ≤ C0 CcN cc clo Cup Ccs ^ 2 * α ^ 4 := le_of_mul_le_mul_left h1 hclo
    have h3 : Work.Spaces.HkSq α 4 (galFun φ (c τ))
        ≤ (C0 CcN cc clo Cup Ccs * α ^ 2) ^ 2 := by
      rw [mul_pow, show (α ^ 2) ^ 2 = α ^ 4 by ring]
      exact h2
    calc Real.sqrt (Work.Spaces.HkSq α 4 (galFun φ (c τ)))
        ≤ Real.sqrt ((C0 CcN cc clo Cup Ccs * α ^ 2) ^ 2) := Real.sqrt_le_sqrt h3
      _ = C0 CcN cc clo Cup Ccs * α ^ 2 := Real.sqrt_sq (by positivity)


/-- **The a-priori bound (main theorem of node N5)** — design §4 L-N5.7, in the existential form of
the design, with the constants `α₅ = alpha5 …` and `C₀ = C0 …` exhibited by
`galerkin_bound_explicit`. -/
theorem galerkin_bound (IP : ℝ → Fn → Fn → ℝ) {α₂ cc clo Cup Ccs Ce Cs CcN α₄ : ℝ}
    (hIP : UnifIP IP α₂ cc clo Cup Ccs) (hCe : 0 < Ce) (hCs : 0 < Cs) (hCcN : 0 < CcN)
    (hα₄ : 0 < α₄) :
    ∃ α₅ C₀ : ℝ, 0 < α₅ ∧ 0 < C₀ ∧ ∀ α : ℝ, 0 < α → α ≤ α₅ →
      ∀ (Φs : Fn) (EllSol : Fn → Fn) (φ : ℕ → Fn) (g₀ : Fn),
        Work.FTS.VocabO.StarPkgo α Cs Φs → (∀ g, GalClass α g → Work.FTS.VocabO.EllPkgGo α Ce g (EllSol g)) →
        GalBasis α IP φ → LocData.DataAdm α g₀ → Construction.L12 g₀ 0 = 0 →
        RegQ α 4 g₀ → Xn α g₀ ≤ α ^ 2 →
        GalEnergyIneq IP α cc CcN φ (PsiCan Φs EllSol) g₀ →
        ∀ (n : ℕ) (T : ℝ), 0 ≤ T → ∀ c : ℝ → Fin n → ℝ,
          IsSolOn (galField α (IP α) φ n (PsiCan Φs EllSol)) (coeffOf (IP α) g₀ φ n) T c →
          ∀ τ ∈ Set.Icc 0 T,
            ∑ k : Fin n, (c τ k) ^ 2 ≤ (Real.sqrt clo * C₀ * α ^ 2) ^ 2 ∧
            Xn α (galFun φ (c τ)) ≤ C₀ * α ^ 2 :=
  ⟨alpha5 CcN cc clo Cup Ccs α₂ α₄, C0 CcN cc clo Cup Ccs,
    alpha5_pos hCcN hIP.pos.2.1 hIP.pos.2.2.1 hIP.pos.2.2.2.1 hIP.pos.2.2.2.2 hIP.pos.1 hα₄,
    C0_pos hCcN hIP.pos.2.1 hIP.pos.2.2.1 hIP.pos.2.2.2.1 hIP.pos.2.2.2.2,
    galerkin_bound_explicit IP hIP hCe hCs hCcN hα₄⟩

end Work.FTS.OpenPkg.AprioriOpen
