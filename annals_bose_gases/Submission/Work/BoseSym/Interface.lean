import ChallengeDeps
import Mathlib.Analysis.Convolution
import Submission.Work.BoseSym.Ops
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# BoseSym — the delegation interface

The lemmas delegated by this area are stated in the vocabulary below, so that
they elaborate in a minimal environment (no notation scopes, no `open`):
each wrapper is definitionally transparent.
-/

namespace Work.BoseSym

open MeasureTheory Filter
open BoseGases
open Submission.BoseGases
open scoped Topology Real ContDiff ENNReal NNReal Convolution

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- `C^1` real functions on a normed space. -/
def Smooth1 {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (f : X → ℝ) : Prop :=
  ContDiff ℝ 1 f

/-- `C^∞` (smooth) real functions on a normed space. -/
def Smooth {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (f : X → ℝ) : Prop :=
  ContDiff ℝ ∞ f

/-- The coordinate direction of particle `i` in coordinate `k`. -/
def eDir (N : ℕ) (i : Fin N) (k : Fin 3) : Conf N := Submission.BoseGases.kcDir N i k

/-- Radiality of a one-particle potential (the corpus notion). -/
def IsRadialF (v : E3 → ℝ) : Prop := BoseGases.IsRadial v

/-- `v` is integrable on `ℝ³`. -/
def IsL1 (v : E3 → ℝ) : Prop := MemLp v 1 (MeasureTheory.volume : MeasureTheory.Measure E3)

/-- `f` is integrable on the box. -/
def IntOnBox (N : ℕ) (L : ℝ) (f : Conf N → ℝ) : Prop :=
  IntegrableOn f (box N L) (MeasureTheory.volume : MeasureTheory.Measure (Conf N))

/-- The corpus' Dirichlet trial space (functions smooth on the box, supported
in its interior, nonzero). -/
abbrev BoxState (N : ℕ) (L : ℝ) : Type := BoseGases.CInfty0Box N L

/-- The corpus' symmetric (bosonic) trial space. -/
abbrev SymState (N : ℕ) (L : ℝ) : Type := Submission.BoseGases.SymBox N L

/-- The box ground-state energy (the corpus object). -/
def boxE (N : ℕ) (L : ℝ) (v : E3 → ℝ) : ℝ := Submission.BoseGases.boxEnergy N L v

/-- The symmetric (bosonic) box ground-state energy (the corpus object). -/
def symBoxE (N : ℕ) (L : ℝ) (v : E3 → ℝ) : ℝ := Submission.BoseGases.symBoxEnergy N L v

/-- Almost-everywhere equality of real functions on configuration space. -/
def AEEq (N : ℕ) (f g : Conf N → ℝ) : Prop := ∀ᵐ x ∂(volC N), f x = g x

/-- Almost-everywhere nonnegativity of a real function on configuration space. -/
def AENonneg (N : ℕ) (f : Conf N → ℝ) : Prop := ∀ᵐ x ∂(volC N), 0 ≤ f x

/-- Almost-everywhere measurability on configuration space. -/
def AEMeas (N : ℕ) (f : Conf N → ℝ) : Prop := AEMeasurable f (volC N)

/-- Almost-everywhere measurability of a function on one-particle space. -/
def AEMeas3 (v : E3 → ℝ) : Prop := AEMeasurable v (MeasureTheory.volume : MeasureTheory.Measure E3)

/-- `f` is square integrable on configuration space. -/
def IsL2 (N : ℕ) (f : Conf N → ℝ) : Prop := MemLp f 2 (volC N)

/-- The `L²` element attached to a square integrable function. -/
def toL2 (N : ℕ) (f : Conf N → ℝ) (h : IsL2 N f) : L2 N := MemLp.toLp f h

/-- The `L²` seminorm of a real function, in `ℝ≥0∞`. -/
noncomputable def eLp2 (N : ℕ) (f : Conf N → ℝ) : ℝ≥0∞ := eLpNorm f 2 (volC N)

/-- The `L²` seminorm of the pointwise gradient norm of a real function. -/
noncomputable def gradNorm (N : ℕ) (f : Conf N → ℝ) : ℝ≥0∞ :=
  eLpNorm (fun x => ‖fderiv ℝ f x‖) 2 (volC N)

/-- The real number `δ`, seen in `ℝ≥0∞`. -/
noncomputable def ofRealENN (δ : ℝ) : ℝ≥0∞ := ENNReal.ofReal δ

/-- The integral of a real function on configuration space. -/
noncomputable def intC (N : ℕ) (f : Conf N → ℝ) : ℝ := ∫ x, f x

/-- The integral of a real function over the box `box N L`. -/
noncomputable def intBox (N : ℕ) (L : ℝ) (f : Conf N → ℝ) : ℝ := ∫ x in box N L, f x

/-- The convolution of two real functions on configuration space, with respect
to Lebesgue measure and scalar multiplication. -/
noncomputable def convC (N : ℕ) (f g : Conf N → ℝ) : Conf N → ℝ :=
  convolution f g (ContinuousLinearMap.lsmul ℝ ℝ) (volC N)

/-- Convergence of a sequence in `L²`. -/
def TendstoL2 (N : ℕ) (u : ℕ → L2 N) (v : L2 N) : Prop :=
  Filter.Tendsto u Filter.atTop (nhds v)

/-- Convergence of a sequence of real numbers. -/
def TendstoR (a : ℕ → ℝ) (b : ℝ) : Prop := Filter.Tendsto a Filter.atTop (nhds b)

/-- A real-valued function is Lipschitz with constant `C`. -/
def LipsReal {X : Type*} [PseudoMetricSpace X] (C : ℝ) (f : X → ℝ) : Prop :=
  ∀ x y, |f x - f y| ≤ C * dist x y

/-- A function on configuration space is bounded by `B`. -/
def BddBy (N : ℕ) (f : Conf N → ℝ) (B : ℝ) : Prop := ∀ x, |f x| ≤ B

/-- The symmetrisation average of a real function (the corpus notion). -/
def symAvgF (N : ℕ) (f : Conf N → ℝ) : Conf N → ℝ := Submission.BoseGases.symAvg N f

/-- The truncated box energy: the infimum of the Dirichlet quotient of the
smooth trial states with the pair interaction truncated at level `M`. -/
noncomputable def boxEnergyTrunc (N : ℕ) (L : ℝ) (v : E3 → ℝ) (M : ℝ) : ℝ :=
  ⨅ Ψ : CInfty0Box N L,
    ((∫ x in box N L, ∑ i : Fin N, ∑ k : Fin 3,
        (fderiv ℝ (Ψ : Conf N → ℝ) x (kcDir N i k)) ^ 2)
      + (∫ x in box N L, Vtrunc N v M x * ((Ψ : Conf N → ℝ) x) ^ 2))
    / (∫ x in box N L, ((Ψ : Conf N → ℝ) x) ^ 2)

/-- The truncated symmetric box energy: the same infimum restricted to the
permutation-invariant (bosonic) trial states. -/
noncomputable def symBoxEnergyTrunc (N : ℕ) (L : ℝ) (v : E3 → ℝ) (M : ℝ) : ℝ :=
  ⨅ Ψ : SymBox N L,
    ((∫ x in box N L, ∑ i : Fin N, ∑ k : Fin 3,
        (fderiv ℝ (Ψ : Conf N → ℝ) x (kcDir N i k)) ^ 2)
      + (∫ x in box N L, Vtrunc N v M x * ((Ψ : Conf N → ℝ) x) ^ 2))
    / (∫ x in box N L, ((Ψ : Conf N → ℝ) x) ^ 2)

/-- A permutation-invariant real function (the corpus notion). -/
def PermInv (N : ℕ) (f : Conf N → ℝ) : Prop := Submission.BoseGases.PermInvariant N f

end

end Work.BoseSym
