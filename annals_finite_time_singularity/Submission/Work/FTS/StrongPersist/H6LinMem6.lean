/-
# `Work.FTS.StrongPersist.H6LinMem6` — the `ℋ⁶`-membership of the linear part `-𝓛_Γ^T f`

The linear part of the fake-time equation (`Vocab.linPart`, `L3Defs.linPart_eq`) splits into
three summands,

  `linPart α f = locOp f + Acoef α · Mf f - Bcoef α · K0f f`,

with

* `locOp f = -(𝓛 f) + Transport f` — a *first-order* operator with smooth bounded coefficients;
* `Acoef α · Mf f` — the nonlocal term: the smooth separated coefficient
  `Acoef α = acoef(z)·gamCoef(α,θ)` times the *radial* tail integral
  `Mf f = fun z _ => L₁₂(f)(z)`;
* `Bcoef α · K0f f` — the projector correction: a smooth fixed separated coefficient times the
  *constant* `K0f f = L₁₂(Transport f)(0)`.

This module proves the level-six honesty of the whole expression,

  `HkMem α 7 f → H6Adm α f → HkMem α 6 (linPart α f)`  for `0 < α ≤ 1`,

i.e. the level-six membership `H6LinMem6` consumed by `H6SplitIP6` (the `hsplit` field of the
pairing context `L6Ctx`).

The three summands are handled in the auxiliary modules

* `L6Aux.LinMem6Aux` — the smoothness helpers, the angular majorant `Mth6` (with its
  integrability) and the radial slot sum `SlotSum`, and the finite-smoothness multiplier
  estimate `zmul_finite6`;
* `L6Aux.LinMem6LocOp` — the local summand (`HkMem α 7 f` is spent here: the shifted slots
  `D_z⁶(D_z f)`, `D_θ⁶(D_θ f)` are `ℋ⁷`-slots of `f`);
* `L6Aux.LinMem6Acf` — the nonlocal summand (multiplier step, the separation lemma
  `L6Aux.HkIntegrandSepLeGen` and the `L₁₂`-slot sum `L6Aux.L12SlotSum6`);
* the projector summand and the glue (`HkAddFin`) are below.

The jet bounds for the two radial coefficients and the level-six membership of the projector
coefficient are the delegated bricks `L6Aux.PhiZopBound6`, `L6Aux.ZslotSupBound6` and
`L6Aux.BcoefMem6`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.Defs
import Submission.Work.FTS.StrongPersist.Basic
import Submission.Work.FTS.StrongPersist.L3_lin_mem
import Submission.Work.FTS.StrongPersist.HkAddFin
import Submission.Work.FTS.StrongPersist.L6Aux.LinMem6Aux
import Submission.Work.FTS.StrongPersist.L6Aux.LinMem6LocOp
import Submission.Work.FTS.StrongPersist.L6Aux.LinMem6Acf
import Submission.Work.FTS.StrongPersist.L6Aux.PhiZopBound6
import Submission.Work.FTS.StrongPersist.L6Aux.ZslotSupBound6
import Submission.Work.FTS.StrongPersist.L6Aux.HkIntegrandSepLeGen
import Submission.Work.FTS.StrongPersist.L6Aux.BcoefMem6
import Submission.Work.FTS.StrongPersist.L6Aux.L12SlotSum6

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

open Work.FTS.Galerkin (Fn)
open Work.Spaces (HkMem HkSq HkNorm HkIntegrand)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## §5 The projector summand `Bcoef α · K0f f` -/

/-- The projector summand is in `ℋ⁶`: it is the constant `K0f f` times the fixed smooth
separated coefficient `Bcoef α`. -/
theorem Bcoef_mem6_of {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : Fn}
    (hB : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3)) ∧
      Work.Spaces.HkMem α 6
        (fun z θ => (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3))) :
    Work.Spaces.HkMem α 6 (fun z θ => Bcoef α z θ * K0f f) := by
  have h1 : Work.Spaces.HkMem α 6
      (fun z θ => (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3)) := hB.2
  have h2 := Work.FTS.LocData.HkMem_const_mul α 6 (K0f f) h1
  have hfun : (fun z θ => (K0f f) * ((Work.Spaces.Gam α θ / Work.Spaces.c α)
        * (2 * z ^ 2 / (1 + z) ^ 3))) = fun z θ => Bcoef α z θ * K0f f := by
    funext z θ
    rw [Bcoef_eq_mul, gamCoef, bcoef]
    ring
  rwa [hfun] at h2

/-- The projector summand is `C^∞` on the open quadrant (hence `C⁶`). -/
theorem Bcoef_smoothOpen_of {α : ℝ} {f : Fn}
    (hB : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3))) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => -(Bcoef α z θ * K0f f)) := by
  have h1 : (fun z θ => (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3))
      = fun z θ => Bcoef α z θ := by
    funext z θ
    rw [Bcoef_eq_mul]
    rfl
  rw [h1] at hB
  refine linMem_neg ?_
  have h2 : (fun z θ => Bcoef α z θ * K0f f) = fun z θ => (K0f f) * Bcoef α z θ := by
    funext z θ
    ring
  rw [h2]
  exact linMem_const_mul (K0f f) hB

/-! ## §6 The assembly -/

/-- **The `ℋ⁶`-membership of the linear part.** -/
theorem H6LinMem6 : ∃ α₂ : ℝ, 0 < α₂ ∧
    ∀ α ∈ Set.Ioc 0 α₂, ∀ f : Work.FTS.Galerkin.Fn,
      Work.FTS.StrongPersist.H6Adm α f → Work.Spaces.HkMem α 7 f →
      Work.Spaces.HkMem α 6 (Work.FTS.StrongPersist.linPart α f) := by
  obtain ⟨K₁, hK₁, hK₁b⟩ := Work.FTS.StrongPersist.L6Aux.PhiZopBound6
  obtain ⟨K₂, hK₂, hK₂b⟩ := Work.FTS.StrongPersist.L6Aux.ZslotSupBound6
  obtain ⟨C₂, hC₂, hBc⟩ := Work.FTS.StrongPersist.L6Aux.BcoefMem6
  obtain ⟨C₃, hC₃, hL12⟩ := Work.FTS.StrongPersist.L6Aux.L12SlotSum6
  refine ⟨1, one_pos, ?_⟩
  intro α hαIoc f hf hmem7
  have hα0 : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  have hsm : Work.FTS.EllipticEst.SmoothOpen f := hf.reg.1
  have hmem6 : Work.Spaces.HkMem α 6 f :=
    Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen α (by norm_num) hsm hmem7
  have h0 : Work.Construction.L12 f 0 = 0 := hf.l12
  -- the `acoef`-jet bound in the `Zop`-form of `zmul_finite6`
  have hzb2 : ∀ b ≤ 6, ∀ z ∈ Set.Ioi (0 : ℝ), |Work.Spaces.Zop^[b] acoef z| ≤ K₂ := by
    intro b hb z hz
    have hz' : (0 : ℝ) < z := hz
    have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz'
    have hθ0 : (0 : ℝ) ∈ Work.Spaces.Iθ := ⟨le_refl 0, by linarith [Real.pi_pos]⟩
    have h := hK₂b b hb z hzI 0 hθ0
    have h2 : Work.Spaces.Zop^[b] acoef z
        = Work.Spaces.DzIter b (fun z (_ : ℝ) => acoef z) z 0 :=
      (congrFun (Work.Spaces.Zop_slice b (fun z (_ : ℝ) => acoef z) 0) z).symm
    rw [h2]
    exact h
  -- the radial slot sum of `L₁₂ f`
  have hslot := hL12 α hα0 hα1 f hsm hmem6 h0
  -- the level-six separation lemma, in the `Mth6`/`SlotSum` vocabulary
  have hsep : ∀ {z θ : ℝ}, θ ∈ Work.Spaces.Iθ →
      Work.Spaces.HkIntegrand α 6
          (fun z' θ' => gamCoef α θ' * Work.Construction.L12 f z') z θ
        ≤ Mth6 α θ * SlotSum (fun z => Work.Construction.L12 f z) z := by
    intro z θ hθ
    simpa only [Mth6, SlotSum] using
      (Work.FTS.StrongPersist.L6Aux.HkIntegrandSepLeGen (α := α) (k := 6)
        (C := gamCoef α) (B := fun z => Work.Construction.L12 f z) hθ)
  -- the three memberships
  have hloc : Work.Spaces.HkMem α 6 (locOp f) :=
    LocOp_mem6_of hα0 hK₁.le (fun b hb z hz => hK₁b b hb z (le_of_lt hz)) hsm hmem7
  have hacf : Work.Spaces.HkMem α 6 (fun z θ => Acoef α z θ * Mf f z θ) :=
    Acf_mem6_of hα0 hα1 hK₂.le hzb2 hslot hsep hsm hmem7 h0
  have hproj0 : Work.Spaces.HkMem α 6 (fun z θ => Bcoef α z θ * K0f f) :=
    Bcoef_mem6_of hα0 hα1 ⟨(hBc α hα0 hα1).1, (hBc α hα0 hα1).2.1⟩
  have hproj : Work.Spaces.HkMem α 6 (fun z θ => -(Bcoef α z θ * K0f f)) := by
    have h := Work.FTS.LocData.HkMem_const_mul α 6 (-1) hproj0
    rwa [show (fun z θ => (-1) * (Bcoef α z θ * K0f f))
        = fun z θ => -(Bcoef α z θ * K0f f) from by funext z θ; ring] at h
  -- the finite-order smoothness of the summands
  have h12 : ContDiffOn ℝ 6 (fun z => Work.Construction.L12 f z) (Set.Ioi (0 : ℝ)) :=
    contDiffOn6_L12_of hsm hmem7
  have hloc6 : ContDiffOn ℝ 6 (Function.uncurry (locOp f)) Work.FTS.EllipticEst.Q0 :=
    (locOp_smoothOpen hsm).forall 6
  have hacf6 : ContDiffOn ℝ 6
      (Function.uncurry (fun z θ => Acoef α z θ * Mf f z θ)) Work.FTS.EllipticEst.Q0 :=
    contDiffOn6_Acf h12
  have hproj6 : ContDiffOn ℝ 6
      (Function.uncurry (fun z θ => -(Bcoef α z θ * K0f f))) Work.FTS.EllipticEst.Q0 :=
    (Bcoef_smoothOpen_of (hBc α hα0 hα1).1).forall 6
  have hsum6 : ContDiffOn ℝ 6
      (Function.uncurry (fun z θ => locOp f z θ + Acoef α z θ * Mf f z θ))
      Work.FTS.EllipticEst.Q0 :=
    (hloc6.add hacf6).congr (fun p hp => rfl)
  -- the glue
  have hsum : Work.Spaces.HkMem α 6 (fun z θ => locOp f z θ + Acoef α z θ * Mf f z θ) :=
    (Work.FTS.StrongPersist.HkAddFin hloc6 hacf6 hloc hacf).1
  have hmem : Work.Spaces.HkMem α 6
      (fun z θ => (locOp f z θ + Acoef α z θ * Mf f z θ) + (-(Bcoef α z θ * K0f f))) :=
    (Work.FTS.StrongPersist.HkAddFin hsum6 hproj6 hsum hproj).1
  have hlin : linPart α f = fun z θ => (locOp f z θ + Acoef α z θ * Mf f z θ)
      + (-(Bcoef α z θ * K0f f)) := by
    rw [linPart_eq]
    funext z θ
    ring
  rwa [hlin]

end Work.FTS.StrongPersist
