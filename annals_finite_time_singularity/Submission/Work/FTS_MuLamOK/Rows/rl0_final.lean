import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.Physical.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.Physical

/-- `ℝ³`, definitionally `Work.LWP.R3` and `Work.Cyl.R3`. -/
abbrev R3 : Type := EuclideanSpace ℝ (Fin 3)

/-! ## The clock `τ ↦ t` -/

/-- **The clock of the dynamic rescaling.**  The amplitude `A = A(τ)` of the physical vorticity
solves `A' = -(1+μ)A` in fake time, where the modulation `1+μ` stays in `[1/2,2]`.  The physical
time is `t(τ) = ∫₀^τ A`, the blow-up time is `T = ∫₀^∞ A`, and the reconstruction lives on
`[0,T)`.

The two constants `1/2 ≤ 1+μ ≤ 2` are the paper's `Λ`-bounds of the modulation bootstrap: they are
exactly what makes `A` decay like `e^{-τ/2}` (so that `T < ∞`, i.e. the blow-up is in finite time)
and what makes `A(τ) ≥ (T - t(τ))/2` (so that the vorticity lower bound blows up at the rate
`1/(T-t)`). -/
structure PhysClock where
  /-- the amplitude `A(τ)` of the rescaled solution -/
  A : ℝ → ℝ
  /-- the modulation `μ(τ)` -/
  mu : ℝ → ℝ
  /-- `A > 0` in fake time -/
  hApos : ∀ τ : ℝ, 0 ≤ τ → 0 < A τ
  /-- `A` is continuous on the fake-time half-line -/
  hAcont : ContinuousOn A (Set.Ici (0 : ℝ))
  /-- the modulation ODE `A' = -(1+μ)A` -/
  hAderiv : ∀ τ : ℝ, 0 ≤ τ → HasDerivAt A (-(1 + mu τ) * A τ) τ
  /-- the lower modulation bound `1/2 ≤ 1+μ` -/
  hmu_lo : ∀ τ : ℝ, 0 ≤ τ → 1 ≤ 2 * (1 + mu τ)
  /-- the upper modulation bound `1+μ ≤ 2` -/
  hmu_hi : ∀ τ : ℝ, 0 ≤ τ → 1 + mu τ ≤ 2

namespace PhysClock

/-- The physical time `t(τ) = ∫₀^τ A(s) ds`. -/
noncomputable def t (C : PhysClock) (τ : ℝ) : ℝ := ∫ s in (0 : ℝ)..τ, C.A s

/-- The blow-up time `T = ∫₀^∞ A(s) ds`. -/
noncomputable def T (C : PhysClock) : ℝ := ∫ s in Set.Ici (0 : ℝ), C.A s

@[simp] theorem t_zero (C : PhysClock) : C.t 0 = 0 := by simp [t]

end PhysClock

/-! ## The physical vorticity and velocity -/

/-- **The physical velocity is the Biot–Savart field of the physical vorticity.**  This is the
reconstruction `u = BS ω` of the paper's Introduction; the analytic property that makes it useful
is the Calderón–Zygmund/Schauder estimate for compactly supported Hölder vorticity, proved in
`Work.CoreResiduals.BiotSavart` and packaged as `Work.CoreResiduals.BiotSavartSpaceTime`. -/
noncomputable def physVel (ω : R3 → ℝ → R3) : R3 → ℝ → R3 :=
  fun x t => Work.LWP.biotSavart (fun y => ω y t) x

theorem physVel_apply (ω : R3 → ℝ → R3) (x : R3) (t : ℝ) :
    physVel ω x t = Work.LWP.biotSavart (fun y => ω y t) x := rfl

/-- The slice form of `physVel`. -/
theorem physVel_slice (ω : R3 → ℝ → R3) (t : ℝ) :
    (physVel ω · t) = Work.LWP.biotSavart (fun y => ω y t) := rfl

/-! ## The `BlowupAt` interface (node N0)

This is the object the top-level wiring consumes: a genuinely blowing-up solution of the
incompressible Euler equation on `ℝ³`, with all the structural clauses of `theorem_1` except the
normalisation of the blow-up time.  It contains no hypothesis at or past the blow-up time: all
regularity clauses are on the strips `[0,S]`, `S < T`. -/

/-- **A finite-time blow-up of the incompressible Euler equation at time `T > 0`, of
`C^{1,α}` class with `α`-decaying compactly supported technology.**  The fields are `u` (velocity)
and `p` (pressure); the clauses are, in order: `(p,u)` solves Euler on `[0,T)` with initial datum
`u(·,0)`; the datum is divergence-free; the solution is odd at every time; the datum is `C^{1,α}`;
the datum's vorticity decays as in `theorem_1`; the solution is jointly `C^{1,α}` on every strip
`ℝ³ × [0,S]`, `S < T`; and the vorticity sup-norm dominates `c/(T-t)`. -/
structure BlowupAt (α : ℝ≥0) (T : ℝ) where
  /-- the velocity field -/
  u : R3 → ℝ → R3
  /-- the pressure field -/
  p : R3 → ℝ → ℝ
  /-- the blow-up time is positive -/
  hT : 0 < T
  /-- `(p,u)` solves the incompressible Euler equation on `[0,T)` with datum `u(·,0)` -/
  sol : IsLocalEulerEquationSolution p (u · 0) T u
  /-- the datum is divergence-free -/
  div0 : div (u · 0) = 0
  /-- the solution is odd at every time -/
  odd : ∀ t ∈ Set.Ico 0 T, IsOdd (u · t)
  /-- the datum is `C^{1,α}` -/
  cdh0 : IsContDiffHolder ℝ α (u · 0)
  /-- the datum's vorticity decays like `‖x‖^{-α}` -/
  decay0 : ∃ C : ℝ, 0 < C ∧ ∀ x : R3, ‖vorticity (u · 0) x‖ ≤ C / (‖x‖ ^ (α : ℝ) + 1)
  /-- joint `C^{1,α}` regularity on the strips `ℝ³ × [0,S]`, `S < T` -/
  strip : ∀ S ∈ Set.Ioo 0 T, IsContDiffHolderOn ℝ α u.uncurry (Set.univ ×ˢ Set.Icc 0 S)
  /-- the `c/(T-t)` lower bound on the vorticity sup-norm -/
  lower : ∃ c : ℝ, 0 < c ∧ ∀ t ∈ Set.Ico 0 T, c / (T - t) ≤ Work.LWP.vortLInf u t

/-! ## The div-curl / Liouville input

The one classical analytic fact that the workspace does not yet contain (and that the paper's
reconstruction uses to identify the Biot–Savart field with the stream-function field): a harmonic
vector field of sublinear growth is constant, and hence — if it is odd — zero.  It is stated here
in the form in which the reconstruction consumes it: as a *difference* statement, so that it
applies to two candidate velocities with the same curl. -/



end Work.FTS.Physical
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces.dabsIntLe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces

/-- The `L²`-commutator estimate for a weight `Q` that is comparable to its translates:
if `0 ≤ Q` and `Q (y + p) ≤ e^{Cw(|p₁|+|p₂|)} Q y` together with the reverse inequality
(so that `Q` is "log-Lipschitz" with constant `Cw` in both directions), then for any
`G₁, G₂` with `Q · Gᵢ²` integrable,

`|∫ (Q y − Q (y − p)) G₁ (y − p) G₂ y| ≤ (e^{Cw(|p₁|+|p₂|)} − 1) ‖G₁‖_{L²(Q)} ‖G₂‖_{L²(Q)}`.

The mechanism: pointwise `|Q y − Q (y − p)| ≤ (E−1)·min (Q y) (Q (y − p)) ≤ (E−1)·√(Q y Q (y − p))`
with `E = e^{Cw(|p₁|+|p₂|)}`, then Cauchy–Schwarz against
`√(Q y)|G₂ y|` and `√(Q (y − p))|G₁ (y − p)|`, using translation invariance,
`∫ Q (y − p) G₁ (y − p)² = ∫ Q G₁²`, to remove the shift. -/
theorem dabsIntLe {Q G₁ G₂ : ℝ × ℝ → ℝ} {Cw : ℝ} (hCw : 0 ≤ Cw)
    (hQ0 : ∀ y : ℝ × ℝ, 0 ≤ Q y) (hQm : Measurable Q)
    (hQsh : ∀ y p : ℝ × ℝ, Q (y + p) ≤ Real.exp (Cw * (|p.1| + |p.2|)) * Q y)
    (hQsh' : ∀ y p : ℝ × ℝ, Q y ≤ Real.exp (Cw * (|p.1| + |p.2|)) * Q (y + p))
    (hG1m : Measurable G₁) (hG2m : Measurable G₂)
    (hI1 : MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * G₁ y ^ 2))
    (hI2 : MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * G₂ y ^ 2)) (p : ℝ × ℝ) :
    |∫ y : ℝ × ℝ, (Q y - Q (y - p)) * G₁ (y - p) * G₂ y|
      ≤ (Real.exp (Cw * (|p.1| + |p.2|)) - 1) * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2)
          * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₂ y ^ 2) := by
  set E : ℝ := Real.exp (Cw * (|p.1| + |p.2|)) with hEdef
  have hE1 : 1 ≤ E := by
    rw [hEdef]
    exact Real.one_le_exp (mul_nonneg hCw (add_nonneg (abs_nonneg _) (abs_nonneg _)))
  have hE0 : 0 ≤ E - 1 := by linarith
  -- Pointwise: `|Q y - Q (y - p)| ≤ (E - 1) √(Q y) √(Q (y - p))`.
  have hA : ∀ y : ℝ × ℝ, |(Q y - Q (y - p)) * G₁ (y - p) * G₂ y|
      ≤ (E - 1) * ((Real.sqrt (Q y) * |G₂ y|) * (Real.sqrt (Q (y - p)) * |G₁ (y - p)|)) := by
    intro y
    have hb : Q (y - p) ≤ E * Q y := by
      rw [hEdef]
      simpa [sub_add_cancel] using hQsh' (y - p) p
    have ha : Q y ≤ E * Q (y - p) := by
      rw [hEdef]
      simpa [sub_add_cancel] using hQsh (y - p) p
    have hmin := abs_sub_le_exp_sqrt hE1 (hQ0 y) (hQ0 (y - p)) ha hb
    calc |(Q y - Q (y - p)) * G₁ (y - p) * G₂ y|
        = |Q y - Q (y - p)| * |G₁ (y - p)| * |G₂ y| := by rw [abs_mul, abs_mul]
      _ ≤ ((E - 1) * Real.sqrt (Q y * Q (y - p))) * |G₁ (y - p)| * |G₂ y| := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hmin (abs_nonneg _)) (abs_nonneg _)
      _ = (E - 1) * ((Real.sqrt (Q y) * |G₂ y|) * (Real.sqrt (Q (y - p)) * |G₁ (y - p)|)) := by
            rw [Real.sqrt_mul (hQ0 y)]
            ring
  -- Square integrability of the two C-S factors.
  have hu2 : MeasureTheory.Integrable (fun y : ℝ × ℝ => (Real.sqrt (Q y) * |G₂ y|) ^ 2) := by
    refine hI2.congr (Filter.Eventually.of_forall fun y => ?_)
    show Q y * G₂ y ^ 2 = (Real.sqrt (Q y) * |G₂ y|) ^ 2
    rw [mul_pow, Real.sq_sqrt (hQ0 y), sq_abs]
  have hv2 : MeasureTheory.Integrable
      (fun y : ℝ × ℝ => (Real.sqrt (Q (y - p)) * |G₁ (y - p)|) ^ 2) := by
    refine (hI1.comp_sub_right p).congr (Filter.Eventually.of_forall fun y => ?_)
    show Q (y - p) * G₁ (y - p) ^ 2 = (Real.sqrt (Q (y - p)) * |G₁ (y - p)|) ^ 2
    rw [mul_pow, Real.sq_sqrt (hQ0 (y - p)), sq_abs]
  have hmu : Measurable (fun y : ℝ × ℝ => Real.sqrt (Q y) * |G₂ y|) := hQm.sqrt.mul hG2m.abs
  have hmv : Measurable (fun y : ℝ × ℝ => Real.sqrt (Q (y - p)) * |G₁ (y - p)|) :=
    (hQm.comp (measurable_id.sub measurable_const)).sqrt.mul
      (hG1m.comp (measurable_id.sub measurable_const)).abs
  have hprod : MeasureTheory.Integrable (fun y : ℝ × ℝ =>
      (Real.sqrt (Q y) * |G₂ y|) * (Real.sqrt (Q (y - p)) * |G₁ (y - p)|)) :=
    integrable_mul_of_sq_integrable hmu hmv hu2 hv2
  -- Step 1: take absolute values pointwise.
  have hstep1 : ∫ y : ℝ × ℝ, |(Q y - Q (y - p)) * G₁ (y - p) * G₂ y|
      ≤ (E - 1) * ∫ y : ℝ × ℝ,
          (Real.sqrt (Q y) * |G₂ y|) * (Real.sqrt (Q (y - p)) * |G₁ (y - p)|) := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun y => abs_nonneg _) ?_ ?_
    · exact hprod.const_mul (E - 1)
    · exact Filter.Eventually.of_forall fun y => hA y
  -- Step 2: Cauchy–Schwarz, with all the shifts removed by translation invariance.
  have hCS := integral_mul_le_sqrt_mul_sqrt (μ := MeasureTheory.volume)
      (f := fun y : ℝ × ℝ => Real.sqrt (Q y) * |G₂ y|)
      (g := fun y : ℝ × ℝ => Real.sqrt (Q (y - p)) * |G₁ (y - p)|)
      (fun y => mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))
      (fun y => mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)) hmu hmv hu2 hv2
  have hIntU : ∫ y : ℝ × ℝ, (Real.sqrt (Q y) * |G₂ y|) ^ 2 = ∫ y : ℝ × ℝ, Q y * G₂ y ^ 2 := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show (Real.sqrt (Q y) * |G₂ y|) ^ 2 = Q y * G₂ y ^ 2
    rw [mul_pow, Real.sq_sqrt (hQ0 y), sq_abs]
  have hIntV : ∫ y : ℝ × ℝ, (Real.sqrt (Q (y - p)) * |G₁ (y - p)|) ^ 2
      = ∫ y : ℝ × ℝ, Q y * G₁ y ^ 2 := by
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => (by
      show (Real.sqrt (Q (y - p)) * |G₁ (y - p)|) ^ 2 = Q (y - p) * G₁ (y - p) ^ 2
      rw [mul_pow, Real.sq_sqrt (hQ0 (y - p)), sq_abs]))]
    exact MeasureTheory.integral_sub_right_eq_self (fun x => Q x * G₁ x ^ 2) p
  have hstep2 : ∫ y : ℝ × ℝ, (Real.sqrt (Q y) * |G₂ y|) * (Real.sqrt (Q (y - p)) * |G₁ (y - p)|)
      ≤ Real.sqrt (∫ y : ℝ × ℝ, Q y * G₂ y ^ 2) * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2) := by
    rw [← hIntU, ← hIntV]
    exact hCS
  calc |∫ y : ℝ × ℝ, (Q y - Q (y - p)) * G₁ (y - p) * G₂ y|
      = ‖∫ y : ℝ × ℝ, (Q y - Q (y - p)) * G₁ (y - p) * G₂ y‖ := by rw [Real.norm_eq_abs]
    _ ≤ ∫ y : ℝ × ℝ, ‖(Q y - Q (y - p)) * G₁ (y - p) * G₂ y‖ :=
          MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ y : ℝ × ℝ, |(Q y - Q (y - p)) * G₁ (y - p) * G₂ y| := by
          simp only [Real.norm_eq_abs]
    _ ≤ (E - 1) * ∫ y : ℝ × ℝ,
            (Real.sqrt (Q y) * |G₂ y|) * (Real.sqrt (Q (y - p)) * |G₁ (y - p)|) := hstep1
    _ ≤ (E - 1) * (Real.sqrt (∫ y : ℝ × ℝ, Q y * G₂ y ^ 2) *
            Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2)) :=
          mul_le_mul_of_nonneg_left hstep2 hE0
    _ = (E - 1) * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2)
            * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₂ y ^ 2) := by ring

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces2.conv_joint_integrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `conv_joint_integrable` — joint integrability of the two mollifier-convolution pairings

In the log coordinates `(s, ζ) = (log z, log tan θ)` of `JepsTransfer/Defs.lean` the level-`k`
pairing of the `IP6`-transfer estimate becomes an integral over `(y, p) ∈ (ℝ × ℝ)²` of one of

  `k p * Q y * G₁ (y - p) * G₂ y`   resp.   `k p * Q y * G₁ y * G₂ (y + p)`,

where `k` is the (nonnegative, integrable) mollifier kernel, supported in the box
`|p.1| + |p.2| ≤ 2 ε`, and `Q` is the pulled-back weight, which is only *shift bounded*,
`Q (y + p) ≤ exp (Cw * (|p.1| + |p.2|)) * Q y`.  The two profiles are merely measurable with
`Q G₁²`, `Q G₂²` integrable.

The `(y - p)` pairing is `Pieces.integrable_shifted_pair`, the dominating-function form of the
AM–GM argument: pointwise,

  `|k p Q y G₁ (y-p) G₂ y| ≤ (c/2) k p (Q (y-p) G₁ (y-p)²) + (c/2) k p (Q y G₂ y²)`,

with `c = exp (2 Cw ε)`, and the two summands are integrable by the convolution integrand lemma
and by `Integrable.mul_prod` respectively.

The `(y + p)` pairing is *not* of that shape; it is reduced to it by negating the kernel
(`p ↦ -p`, which preserves integrability, nonnegativity and the support condition) and then
flipping the sign of the `p`-variable in the joint integral.  The flip
`z ↦ (z.1, -z.2)` preserves Lebesgue measure on `(ℝ × ℝ)²` because it is the product of the
identity with `Measure.measurePreserving_neg`, and `MeasurePreserving.integrable_comp` transfers
integrability along it (`integrable_flip_snd` below).

The statement is used as given by the requester; nothing else in the development is affected.
-/

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces2

open MeasureTheory

/-- Flipping the sign of the second coordinate is a measure-preserving map of
`(ℝ × ℝ) × (ℝ × ℝ)` with Lebesgue measure: it is the product of the identity with the negation
of `ℝ × ℝ`. -/
lemma measurePreserving_snd_neg :
    MeasurePreserving (fun z : (ℝ × ℝ) × (ℝ × ℝ) => (z.1, -z.2)) volume volume := by
  rw [MeasureTheory.Measure.volume_eq_prod]
  exact MeasurePreserving.prod (MeasurePreserving.id _) (Measure.measurePreserving_neg _)

/-- Integrability of a joint integrand is invariant under flipping the sign of the second
variable. -/
lemma integrable_flip_snd {F : ℝ × ℝ → ℝ × ℝ → ℝ}
    (h : Integrable (Function.uncurry F) volume) :
    Integrable (Function.uncurry fun y p => F y (-p)) volume := by
  convert measurePreserving_snd_neg.integrable_comp_of_integrable h using 1
  ext z
  rfl

theorem conv_joint_integrable {k Q G₁ G₂ : ℝ × ℝ → ℝ} {Cw ε : ℝ} (hCw : 0 ≤ Cw)
    (hk : MeasureTheory.Integrable k) (hk0 : ∀ p : ℝ × ℝ, 0 ≤ k p)
    (hksupp : ∀ p : ℝ × ℝ, k p ≠ 0 → |p.1| + |p.2| ≤ 2 * ε)
    (hQ0 : ∀ y : ℝ × ℝ, 0 ≤ Q y) (hQm : Measurable Q)
    (hQsh : ∀ y p : ℝ × ℝ, Q (y + p) ≤ Real.exp (Cw * (|p.1| + |p.2|)) * Q y)
    (hG1m : Measurable G₁) (hG2m : Measurable G₂)
    (hI1 : MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * G₁ y ^ 2))
    (hI2 : MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * G₂ y ^ 2)) :
    MeasureTheory.Integrable (Function.uncurry fun (y p : ℝ × ℝ) => k p * Q y * G₁ (y - p) * G₂ y)
      ∧ MeasureTheory.Integrable (Function.uncurry fun (y p : ℝ × ℝ) => k p * Q y * G₁ y * G₂ (y + p)) := by
  -- the `(y - p)` pairing: the AM–GM domination of the sibling module `Pieces`
  have key := Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces.integrable_shifted_pair
    (k := k) (Q := Q) (G := G₁) (H := G₂) hCw hk hk0 hksupp hQ0 hQm hQsh hG1m hG2m hI1 hI2
  constructor
  · -- only the order of the factors differs
    refine key.congr ?_
    filter_upwards with z
    simp only [Function.uncurry]
    ring
  · -- the `(y + p)` pairing: negate the kernel, exchange the two profiles, flip `p ↦ -p`
    have hk' : MeasureTheory.Integrable (fun p : ℝ × ℝ => k (-p)) := hk.comp_neg
    have hk0' : ∀ p : ℝ × ℝ, 0 ≤ k (-p) := fun p => hk0 (-p)
    have hksupp' : ∀ p : ℝ × ℝ, k (-p) ≠ 0 → |p.1| + |p.2| ≤ 2 * ε := by
      intro p hp
      have h := hksupp (-p) hp
      simpa using h
    have key2 := Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces.integrable_shifted_pair
      (k := fun p : ℝ × ℝ => k (-p)) (Q := Q) (G := G₂) (H := G₁)
      hCw hk' hk0' hksupp' hQ0 hQm hQsh hG2m hG1m hI2 hI1
    refine (integrable_flip_snd key2).congr ?_
    filter_upwards with z
    simp only [Function.uncurry, neg_neg, sub_neg_eq_add]
    ring

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces2
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces2.conv_pair_integrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Integrability of the two mollifier–convolution pairings

The kernel `k` is nonnegative, integrable and supported in the box `|p.1| + |p.2| ≤ 2 ε`, and the
weight `Q ≥ 0` is only *shift bounded*, `Q (y + p) ≤ exp (Cw * (|p.1| + |p.2|)) * Q y`.  For such
data the *joint* (in `(y,p)`) integrability of `Q y * k p * G₁ (y - p) * G₂ y` is the content of
`Pieces.integrable_shifted_pair` (an AM–GM together with the convolution lemma
`MeasureTheory.Integrable.convolution_integrand`, with the support of `k` converting the shift
bound into the *constant* `Real.exp (2 * Cw * ε)`).

Here we deduce from it the *marginal* statement: the pairing in which the `p`-integral is carried
out first is again integrable in `y`.  Concretely, since the joint integrand is integrable, its
`s`-fibre integral `y ↦ ∫ p, Q y * k p * G₁ (y - p) * G₂ y` is integrable by Fubini
(`MeasureTheory.Integrable.integral_prod_left`); the constants `Q y` and `G₂ y` may be pulled out
of that fibre integral, turning it into `Q y * (∫ p, k p * G₁ (y - p)) * G₂ y`, and the two
functions are equal everywhere, hence a.e.
-/

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces2

open MeasureTheory

-- the two convolution-integrability hypotheses are not needed for the *marginal* statement
set_option linter.unusedVariables false in
theorem conv_pair_integrable {k Q G₁ G₂ : ℝ × ℝ → ℝ} {Cw ε : ℝ} (hCw : 0 ≤ Cw)
    (hk : MeasureTheory.Integrable k) (hk0 : ∀ p : ℝ × ℝ, 0 ≤ k p)
    (hksupp : ∀ p : ℝ × ℝ, k p ≠ 0 → |p.1| + |p.2| ≤ 2 * ε)
    (hQ0 : ∀ y : ℝ × ℝ, 0 ≤ Q y) (hQm : Measurable Q)
    (hQsh : ∀ y p : ℝ × ℝ, Q (y + p) ≤ Real.exp (Cw * (|p.1| + |p.2|)) * Q y)
    (hG1m : Measurable G₁) (hG2m : Measurable G₂)
    (hconv1 : ∀ y : ℝ × ℝ, MeasureTheory.Integrable (fun p : ℝ × ℝ => k p * G₁ (y - p)))
    (hconv2 : ∀ y : ℝ × ℝ, MeasureTheory.Integrable (fun p : ℝ × ℝ => k p * G₂ (y - p)))
    (hI1 : MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * G₁ y ^ 2))
    (hI2 : MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * G₂ y ^ 2)) :
    MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * (∫ p : ℝ × ℝ, k p * G₁ (y - p)) * G₂ y)
      ∧ MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * G₁ y * (∫ p : ℝ × ℝ, k p * G₂ (y - p))) := by
  -- The common shape: for measurable `A`, `B` with the weighted `L²` bounds `Q A²`, `Q B²`, the
  -- pairing `Q y * B y * (∫ p, k p * A (y - p))` is integrable.
  have key : ∀ (A B : ℝ × ℝ → ℝ), Measurable A → Measurable B →
      MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * A y ^ 2) →
      MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * B y ^ 2) →
      MeasureTheory.Integrable
        (fun y : ℝ × ℝ => Q y * B y * (∫ p : ℝ × ℝ, k p * A (y - p))) := by
    intro A B hAm hBm hIA hIB
    -- joint integrability of `(y, p) ↦ Q y * k p * A (y - p) * B y`
    have hJ : MeasureTheory.Integrable
        (fun z : (ℝ × ℝ) × (ℝ × ℝ) => Q z.1 * k z.2 * A (z.1 - z.2) * B z.1) volume :=
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces.integrable_shifted_pair
        hCw hk hk0 hksupp hQ0 hQm hQsh hAm hBm hIA hIB
    -- Fubini: the fibre integral over `p` is integrable in `y`
    have hI := MeasureTheory.Integrable.integral_prod_left (μ := volume) (ν := volume) hJ
    refine hI.congr ?_
    filter_upwards with y
    -- pull the `p`-independent constants out of the fibre integral
    have hfun : (fun p : ℝ × ℝ => Q y * k p * A (y - p) * B y)
        = fun p => (Q y * B y) * (k p * A (y - p)) := by
      funext p
      ring
    rw [hfun, MeasureTheory.integral_const_mul]
  exact ⟨(key G₁ G₂ hG1m hG2m hI1 hI2).congr (by filter_upwards with y; ring),
    key G₂ G₁ hG2m hG1m hI2 hI1⟩

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces2
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces2.kernel_exp_moment_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The exponential-moment bound for a compactly supported probability kernel

If `k ≥ 0` is a probability density on `ℝ × ℝ` whose support is contained in the `ℓ¹`-ball of
radius `2ε` (`ε ≤ 1`), then the exponential moment

  `∫ k(p) · 2 (e^{Cw |p|₁} − 1) e^{Cw |p|₁}`

(with `|p|₁ = |p.1| + |p.2|`) is bounded by `4 Cw ε e^{4Cw}`, hence by
`100 (Cw + 1) e^{4Cw} ε` (`Cw ≥ 0`).

The point is the elementary inequality `e^u − 1 ≤ u e^u` (`u ≥ 0`), applied on the support of
`k` only: off the support the integrand vanishes, and on it `u = Cw |p|₁ ≤ 2 Cw ε`, so

  `2 (e^u − 1) e^u ≤ 2 u e^{2u} ≤ 4 Cw ε e^{4Cw ε} ≤ 4 Cw ε e^{4Cw}`.

Multiplying by `k ≥ 0` and integrating, `∫ k = 1` turns this into the stated bound.  The purely
elementary pointwise inequality is `Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces2.exp_moment_pt`,
proved in a sibling module and imported here.
-/

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces2

open MeasureTheory Filter

theorem kernel_exp_moment_le {k : ℝ × ℝ → ℝ} {Cw ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hCw : 0 ≤ Cw)
    (hk : MeasureTheory.Integrable k) (hk0 : ∀ p : ℝ × ℝ, 0 ≤ k p)
    (hkmass : ∫ p : ℝ × ℝ, k p = 1)
    (hksupp : ∀ p : ℝ × ℝ, k p ≠ 0 → |p.1| + |p.2| ≤ 2 * ε) :
    (∫ p : ℝ × ℝ, k p * (2 * (Real.exp (Cw * (|p.1| + |p.2|)) - 1)
        * Real.exp (Cw * (|p.1| + |p.2|))))
      ≤ 100 * (Cw + 1) * Real.exp (4 * Cw) * ε := by
  -- The pointwise domination: the kernel vanishes off its support, and on the support the
  -- elementary inequality `exp_moment_pt` applies.
  have hpt : ∀ p : ℝ × ℝ,
      k p * (2 * (Real.exp (Cw * (|p.1| + |p.2|)) - 1)
          * Real.exp (Cw * (|p.1| + |p.2|)))
        ≤ k p * (4 * Cw * ε * Real.exp (4 * Cw)) := by
    intro p
    by_cases hp : k p = 0
    · simp [hp]
    · have hr : |p.1| + |p.2| ≤ 2 * ε := hksupp p hp
      have hr0 : 0 ≤ |p.1| + |p.2| := add_nonneg (abs_nonneg p.1) (abs_nonneg p.2)
      have hu : 0 ≤ Cw * (|p.1| + |p.2|) := mul_nonneg hCw hr0
      have hu2 : Cw * (|p.1| + |p.2|) ≤ 2 * Cw * ε := by nlinarith [hCw, hr]
      exact mul_le_mul_of_nonneg_left
        (exp_moment_pt (Cw := Cw) (ε := ε) (u := Cw * (|p.1| + |p.2|)) hCw hε0 hε1 hu hu2)
        (hk0 p)
  -- The integrand is nonnegative.
  have hnn : 0 ≤ᵐ[volume] (fun p : ℝ × ℝ => k p * (2 * (Real.exp (Cw * (|p.1| + |p.2|)) - 1)
      * Real.exp (Cw * (|p.1| + |p.2|)))) := by
    filter_upwards with p
    have hm : 0 ≤ Cw * (|p.1| + |p.2|) :=
      mul_nonneg hCw (add_nonneg (abs_nonneg p.1) (abs_nonneg p.2))
    have h1 : 0 ≤ Real.exp (Cw * (|p.1| + |p.2|)) - 1 := sub_nonneg.mpr (Real.one_le_exp hm)
    have h2 : 0 ≤ Real.exp (Cw * (|p.1| + |p.2|)) := Real.exp_nonneg _
    exact mul_nonneg (hk0 p) (by positivity)
  have hchain : (∫ p : ℝ × ℝ, k p * (2 * (Real.exp (Cw * (|p.1| + |p.2|)) - 1)
        * Real.exp (Cw * (|p.1| + |p.2|))))
      ≤ ∫ p : ℝ × ℝ, k p * (4 * Cw * ε * Real.exp (4 * Cw)) :=
    integral_mono_of_nonneg hnn (hk.mul_const _) (Eventually.of_forall hpt)
  -- The constant integrand integrates to the constant, by `∫ k = 1`.
  have hconst : (∫ p : ℝ × ℝ, k p * (4 * Cw * ε * Real.exp (4 * Cw)))
      = 4 * Cw * ε * Real.exp (4 * Cw) := by
    rw [integral_mul_const, hkmass, one_mul]
  rw [hconst] at hchain
  refine le_trans hchain ?_
  calc 4 * Cw * ε * Real.exp (4 * Cw) = 4 * Cw * Real.exp (4 * Cw) * ε := by ring
    _ ≤ 100 * (Cw + 1) * Real.exp (4 * Cw) * ε := by
        apply mul_le_mul_of_nonneg_right _ hε0
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        linarith

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces2
end
-- ===== merged: Submission.Work.FTS_MuLamOK.Rows.rl0_final =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_MuLamOK.Rows

/-- The `α`-power appearing in the final arithmetic (`α ^ (-(3/2))`) is the inverse of
`α √α`: the two agree because `α ^ (3/2) = α ^ 1 * α ^ (1/2) = α * √α`. -/
theorem rpow_neg_three_halves (α : ℝ) (hα : 0 < α) :
    α ^ (-(3 / 2 : ℝ)) = (α * Real.sqrt α)⁻¹ := by
  have h32 : α ^ (3 / 2 : ℝ) = α * Real.sqrt α := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hα, Real.rpow_one,
      Real.sqrt_eq_rpow]
  have h1 : α ^ (-(3 / 2 : ℝ)) * (α * Real.sqrt α) = 1 := by
    rw [← h32, ← Real.rpow_add hα, show (-(3 / 2 : ℝ)) + 3 / 2 = 0 by norm_num,
      Real.rpow_zero]
  exact eq_inv_of_mul_eq_one_left h1

/-- **The final arithmetic row of the `N₀` estimate.**

The two coefficients `A₀`, `B₀` of the pointwise bound for `N₀` (see `H6Pair6Aux/Rl0Defs`)
satisfy the fully explicit estimate
`3 √(7 (A₀ X² + π B₀)) ≤ 10⁵ (α² + √α X + α^{-3/2} X²)` on `0 < α ≤ 1`, `X ≥ 0`.

The proof squares the inequality and bounds the left-hand side term by term: from
`A₀ ≤ 90 X²/α² + 16 α²` and `B₀ ≤ 25600 α⁴ + 90000 α² X²` one gets
`63 (A₀X² + πB₀) ≤ 5670 X⁴/α² + 1008 α²X² + 1612800π α⁴ + 5670000π α²X²`, and each of the
four summands is a coefficient times `(X²/(α√α))² = X⁴/α³ ≥ X⁴/α²`, `(√α X)² = αX² ≥ α²X²`
or `(α²)² = α⁴`, so the whole left-hand side is at most
`(1008 + 5670000π) ((α²)² + (√αX)² + (X²/(α√α))²) ≤ (1008 + 5670000π) (α² + √αX + X²/(α√α))²`
with `1008 + 5670000π ≤ 10^10` because `π ≤ 4`. -/
theorem rl0_final {α X : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hX : 0 ≤ X) :
    3 * Real.sqrt (7 * (Work.FTS.StrongPersist.H6Pair6Aux.A₀ α X * X ^ 2
        + Real.pi * Work.FTS.StrongPersist.H6Pair6Aux.B₀ α X))
      ≤ 10 ^ 5 * (α ^ 2 + Real.sqrt α * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2) := by
  have hX2 : 0 ≤ X ^ 2 := sq_nonneg X
  have hX4 : 0 ≤ X ^ 4 := by positivity
  have hs0 : 0 ≤ Real.sqrt α := Real.sqrt_nonneg α
  have hpi0 : 0 ≤ Real.pi := Real.pi_nonneg
  have hpi4 : Real.pi ≤ 4 := le_of_lt Real.pi_lt_four
  have hsq : Real.sqrt α ^ 2 = α := Real.sq_sqrt hα.le
  -- the constant of the estimate
  have hM0 : 0 ≤ (1008 : ℝ) + 5670000 * Real.pi := by nlinarith [hpi0]
  have hM5670 : (5670 : ℝ) ≤ 1008 + 5670000 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hM1612800 : 1612800 * Real.pi ≤ 1008 + 5670000 * Real.pi := by nlinarith [hpi0]
  have hM10 : (1008 : ℝ) + 5670000 * Real.pi ≤ 10 ^ 10 := by nlinarith [hpi4]
  -- ## the two coefficient bounds
  have hL1 : Work.FTS.StrongPersist.H6Pair6Aux.A₀ α X * X ^ 2
      ≤ 90 * (X ^ 4 / α ^ 2) + 16 * (α ^ 2 * X ^ 2) := by
    have h := mul_le_mul_of_nonneg_right
      (Work.FTS.StrongPersist.H6Pair6Aux.A₀_le (X := X) hα hα1) hX2
    have he : (90 * X ^ 2 / α ^ 2 + 16 * α ^ 2) * X ^ 2
        = 90 * (X ^ 4 / α ^ 2) + 16 * (α ^ 2 * X ^ 2) := by ring
    linarith [h, he.le, he.ge]
  have hL2 : Real.pi * Work.FTS.StrongPersist.H6Pair6Aux.B₀ α X
      ≤ 25600 * Real.pi * α ^ 4 + 90000 * Real.pi * (α ^ 2 * X ^ 2) := by
    have h := mul_le_mul_of_nonneg_left
      (Work.FTS.StrongPersist.H6Pair6Aux.B₀_le α X) hpi0
    have he : Real.pi * (25600 * α ^ 4 + 90000 * α ^ 2 * X ^ 2)
        = 25600 * Real.pi * α ^ 4 + 90000 * Real.pi * (α ^ 2 * X ^ 2) := by ring
    linarith [h, he.le, he.ge]
  have hLhi : Work.FTS.StrongPersist.H6Pair6Aux.A₀ α X * X ^ 2
        + Real.pi * Work.FTS.StrongPersist.H6Pair6Aux.B₀ α X
      ≤ 90 * (X ^ 4 / α ^ 2) + 16 * (α ^ 2 * X ^ 2)
        + 25600 * Real.pi * α ^ 4 + 90000 * Real.pi * (α ^ 2 * X ^ 2) := by
    linarith [hL1, hL2]
  -- ## multiply by `63 = 7 * 9`
  have h63 : 63 * (Work.FTS.StrongPersist.H6Pair6Aux.A₀ α X * X ^ 2
        + Real.pi * Work.FTS.StrongPersist.H6Pair6Aux.B₀ α X)
      ≤ 5670 * (X ^ 4 / α ^ 2) + 1008 * (α ^ 2 * X ^ 2)
        + 1612800 * Real.pi * α ^ 4 + 5670000 * Real.pi * (α ^ 2 * X ^ 2) := by
    have h := mul_le_mul_of_nonneg_left hLhi (by norm_num : (0 : ℝ) ≤ 63)
    have he : 63 * (90 * (X ^ 4 / α ^ 2) + 16 * (α ^ 2 * X ^ 2)
          + 25600 * Real.pi * α ^ 4 + 90000 * Real.pi * (α ^ 2 * X ^ 2))
        = 5670 * (X ^ 4 / α ^ 2) + 1008 * (α ^ 2 * X ^ 2)
          + 1612800 * Real.pi * α ^ 4 + 5670000 * Real.pi * (α ^ 2 * X ^ 2) := by ring
    linarith [h, he.le, he.ge]
  -- ## the three profiles: `X⁴/α² ≤ (X²/(α√α))²`, `α²X² ≤ (√αX)²`, `α⁴ = (α²)²`
  have hden : (α * Real.sqrt α) ^ 2 = α ^ 3 := by
    rw [mul_pow, hsq]; ring
  have hr2 : ((α * Real.sqrt α)⁻¹ * X ^ 2) ^ 2 = X ^ 4 / α ^ 3 := by
    rw [mul_pow, inv_pow, hden]; ring
  have hsX : (Real.sqrt α * X) ^ 2 = α * X ^ 2 := by rw [mul_pow, hsq]
  have h32 : α ^ 3 ≤ α ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hα1 (sq_nonneg α)
    nlinarith [h]
  have hc1 : X ^ 4 / α ^ 2 ≤ ((α * Real.sqrt α)⁻¹ * X ^ 2) ^ 2 := by
    rw [hr2]
    exact div_le_div_of_nonneg_left hX4 (by positivity) h32
  have hc2 : α ^ 2 * X ^ 2 ≤ (Real.sqrt α * X) ^ 2 := by
    rw [hsX]
    have h1 : 0 ≤ α * X ^ 2 := mul_nonneg hα.le hX2
    have h2 : α * X ^ 2 * (α - 1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos h1 (sub_nonpos.mpr hα1)
    nlinarith [h2]
  -- ## the four summands
  have hT1 : 5670 * (X ^ 4 / α ^ 2)
      ≤ ((1008 : ℝ) + 5670000 * Real.pi) * ((α * Real.sqrt α)⁻¹ * X ^ 2) ^ 2 := by
    have h1 : 5670 * (X ^ 4 / α ^ 2)
        ≤ ((1008 : ℝ) + 5670000 * Real.pi) * (X ^ 4 / α ^ 2) :=
      mul_le_mul_of_nonneg_right hM5670 (by positivity)
    have h2 : ((1008 : ℝ) + 5670000 * Real.pi) * (X ^ 4 / α ^ 2)
        ≤ ((1008 : ℝ) + 5670000 * Real.pi) * ((α * Real.sqrt α)⁻¹ * X ^ 2) ^ 2 :=
      mul_le_mul_of_nonneg_left hc1 hM0
    linarith [h1, h2]
  have hT24 : 1008 * (α ^ 2 * X ^ 2) + 5670000 * Real.pi * (α ^ 2 * X ^ 2)
      ≤ ((1008 : ℝ) + 5670000 * Real.pi) * (Real.sqrt α * X) ^ 2 := by
    have hfac : 1008 * (α ^ 2 * X ^ 2) + 5670000 * Real.pi * (α ^ 2 * X ^ 2)
        = ((1008 : ℝ) + 5670000 * Real.pi) * (α ^ 2 * X ^ 2) := by ring
    rw [hfac]
    exact mul_le_mul_of_nonneg_left hc2 hM0
  have hT3 : 1612800 * Real.pi * α ^ 4
      ≤ ((1008 : ℝ) + 5670000 * Real.pi) * (α ^ 2) ^ 2 := by
    have he : (α ^ 2) ^ 2 = α ^ 4 := by ring
    rw [he]
    exact mul_le_mul_of_nonneg_right hM1612800 (by positivity)
  -- ## assemble
  have hSsum : 5670 * (X ^ 4 / α ^ 2) + 1008 * (α ^ 2 * X ^ 2)
        + 1612800 * Real.pi * α ^ 4 + 5670000 * Real.pi * (α ^ 2 * X ^ 2)
      ≤ ((1008 : ℝ) + 5670000 * Real.pi)
        * ((α ^ 2) ^ 2 + (Real.sqrt α * X) ^ 2 + ((α * Real.sqrt α)⁻¹ * X ^ 2) ^ 2) := by
    nlinarith [hT1, hT24, hT3]
  have hp0 : 0 ≤ α ^ 2 := by positivity
  have hq0 : 0 ≤ Real.sqrt α * X := mul_nonneg hs0 hX
  have hr0 : 0 ≤ (α * Real.sqrt α)⁻¹ * X ^ 2 :=
    mul_nonneg (inv_nonneg.mpr (mul_nonneg hα.le hs0)) hX2
  have hpqr : (α ^ 2) ^ 2 + (Real.sqrt α * X) ^ 2 + ((α * Real.sqrt α)⁻¹ * X ^ 2) ^ 2
      ≤ (α ^ 2 + Real.sqrt α * X + (α * Real.sqrt α)⁻¹ * X ^ 2) ^ 2 := by
    nlinarith [mul_nonneg hp0 hq0, mul_nonneg hp0 hr0, mul_nonneg hq0 hr0]
  have hS0 : 0 ≤ α ^ 2 + Real.sqrt α * X + (α * Real.sqrt α)⁻¹ * X ^ 2 :=
    add_nonneg (add_nonneg hp0 hq0) hr0
  have hkey : 63 * (Work.FTS.StrongPersist.H6Pair6Aux.A₀ α X * X ^ 2
        + Real.pi * Work.FTS.StrongPersist.H6Pair6Aux.B₀ α X)
      ≤ 10 ^ 10 * (α ^ 2 + Real.sqrt α * X + (α * Real.sqrt α)⁻¹ * X ^ 2) ^ 2 := by
    have hΨ0 : 0 ≤ (α ^ 2 + Real.sqrt α * X + (α * Real.sqrt α)⁻¹ * X ^ 2) ^ 2 :=
      sq_nonneg _
    have h1 : ((1008 : ℝ) + 5670000 * Real.pi)
          * ((α ^ 2) ^ 2 + (Real.sqrt α * X) ^ 2 + ((α * Real.sqrt α)⁻¹ * X ^ 2) ^ 2)
        ≤ ((1008 : ℝ) + 5670000 * Real.pi)
          * (α ^ 2 + Real.sqrt α * X + (α * Real.sqrt α)⁻¹ * X ^ 2) ^ 2 :=
      mul_le_mul_of_nonneg_left hpqr hM0
    have h2 : ((1008 : ℝ) + 5670000 * Real.pi)
          * (α ^ 2 + Real.sqrt α * X + (α * Real.sqrt α)⁻¹ * X ^ 2) ^ 2
        ≤ 10 ^ 10 * (α ^ 2 + Real.sqrt α * X + (α * Real.sqrt α)⁻¹ * X ^ 2) ^ 2 :=
      mul_le_mul_of_nonneg_right hM10 hΨ0
    linarith [h63, hSsum, h1, h2]
  -- ## the square root
  have h63' : 3 * Real.sqrt (7 * (Work.FTS.StrongPersist.H6Pair6Aux.A₀ α X * X ^ 2
        + Real.pi * Work.FTS.StrongPersist.H6Pair6Aux.B₀ α X))
      = Real.sqrt (63 * (Work.FTS.StrongPersist.H6Pair6Aux.A₀ α X * X ^ 2
        + Real.pi * Work.FTS.StrongPersist.H6Pair6Aux.B₀ α X)) := by
    rw [show (63 : ℝ) * (Work.FTS.StrongPersist.H6Pair6Aux.A₀ α X * X ^ 2
          + Real.pi * Work.FTS.StrongPersist.H6Pair6Aux.B₀ α X)
        = 9 * (7 * (Work.FTS.StrongPersist.H6Pair6Aux.A₀ α X * X ^ 2
          + Real.pi * Work.FTS.StrongPersist.H6Pair6Aux.B₀ α X)) by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 9),
      show Real.sqrt 9 = 3 by
        rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  rw [h63', rpow_neg_three_halves α hα]
  refine le_trans (Real.sqrt_le_sqrt hkey) ?_
  have hsq10 : 10 ^ 10 * (α ^ 2 + Real.sqrt α * X + (α * Real.sqrt α)⁻¹ * X ^ 2) ^ 2
      = ((10 : ℝ) ^ 5 * (α ^ 2 + Real.sqrt α * X + (α * Real.sqrt α)⁻¹ * X ^ 2)) ^ 2 := by
    rw [show (10 : ℝ) ^ 10 = ((10 : ℝ) ^ 5) ^ 2 by norm_num]
    ring
  rw [hsq10, Real.sqrt_sq (mul_nonneg (by norm_num) hS0)]

end Work.FTS_MuLamOK.Rows
end
