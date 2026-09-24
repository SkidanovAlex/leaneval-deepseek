import Mathlib
import Submission.Work.Mori.PeriodHom
import Submission.Work.Mori.exists_holomorphic_conjugate_of_conjPeriodHomOf_eq_zero
import Submission.HolomorphicLog

/-!
# The holomorphic "winding substitute" for `∮ (closed form) = 0` on a simply connected surface

ABS (arXiv:2008.12189, §6) show that each complementary component `Z` of their filled compact set
`Kₙ` has **connected** frontier, by exhibiting a closed 1-form `ω` on `X` with `∫_{γ₁} ω = ±1` for a
boundary circle `γ₁`, and invoking "on a simply connected space the integral of a closed 1-form over
a loop is `0`".  This workspace has no de Rham theory, so that last step has to be rebuilt.  The
*holomorphic* replacement is the **period of the harmonic conjugate**:

> a harmonic function `u` on a simply connected complex one-manifold has a *global* holomorphic
> conjugate `u + iu*` (equivalently: the flux `∮ ∗du` vanishes on every loop);

which is the statement of the Poincaré lemma in the form this project can use, and the exact object
`Work.Mori.conjPeriodHomOf` computes.  This module records it, together with its log-theoretic
counterpart and the resulting criterion for the (G1) step.

Everything here is an immediate consequence of the covering-space machinery of
`Submission.Conjugate` (`conjPeriod`, `conjPeriodHom`, `isCoveringMap_fst_conjTopology`) and of
`Work.Mori.exists_holomorphic_conjugate_of_conjPeriodHomOf_eq_zero`.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

noncomputable section

open Filter Set

namespace Work.SimplyConnected.ABS

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **The flux of every loop vanishes when all homomorphisms `π₁ → ℝ` do.**

This is the substitute for "on a simply connected space, `∮_γ ω = 0` for every closed 1-form `ω`":
the conjugate period homomorphism `Work.Mori.conjPeriodHomOf hu x` is an element of
`Additive (FundamentalGroup X x) →+ ℝ`, a subsingleton under the hypothesis (which
`SimplyConnectedSpace X` supplies by typeclass inference), so it is the zero homomorphism. -/
theorem conjPeriodHomOf_eq_zero_of_subsingleton {u : X → ℝ}
    (hu : Submission.HarmonicOnX u Set.univ) (x : X)
    [Subsingleton (Additive (FundamentalGroup X x) →+ ℝ)] :
    Work.Mori.conjPeriodHomOf hu x = 0 :=
  Subsingleton.elim _ _

/-- **Pointwise form of `conjPeriodHomOf_eq_zero_of_subsingleton`.** -/
theorem conjPeriodHomOf_apply_eq_zero_of_subsingleton {u : X → ℝ}
    (hu : Submission.HarmonicOnX u Set.univ) (x : X)
    [Subsingleton (Additive (FundamentalGroup X x) →+ ℝ)]
    (γ : Additive (FundamentalGroup X x)) : Work.Mori.conjPeriodHomOf hu x γ = 0 := by
  have h : Work.Mori.conjPeriodHomOf hu x = 0 := conjPeriodHomOf_eq_zero_of_subsingleton hu x
  simpa using congr_fun (congrArg DFunLike.coe h) γ

/-- **Poincaré lemma for the harmonic conjugate (the (G1) substitute).**

On a complex one-manifold on which every homomorphism `π₁ → ℝ` vanishes — in particular on a
simply connected one — every harmonic function has a **global holomorphic conjugate**: a holomorphic
`F` with `F.re = u`.  Equivalently, the "flux" `∮ ∗du` of `u` vanishes around every loop.

For the ABS argument this is the statement that *replaces* "the integral of a closed 1-form over a
null-homotopic loop is `0`": if a harmonic function on a sub-domain has non-zero flux around a loop,
then that loop is not null-homotopic in the domain of harmonicity, and consequently every
null-homotopy of it (in a bigger ambient space) has to leave that domain. -/
theorem exists_holomorphic_conjugate_of_subsingleton {u : X → ℝ}
    (hu : Submission.HarmonicOnX u Set.univ) (x : X)
    [Subsingleton (Additive (FundamentalGroup X x) →+ ℝ)] :
    ∃ F : X → ℂ, Submission.HolomorphicOnX F Set.univ ∧ ∀ y, (F y).re = u y :=
  Work.Mori.exists_holomorphic_conjugate_of_conjPeriodHomOf_eq_zero hu x
    (conjPeriodHomOf_eq_zero_of_subsingleton hu x)

/-- **Every harmonic function on a simply connected surface has a global holomorphic conjugate.** -/
theorem exists_holomorphic_conjugate_of_simplyConnected [SimplyConnectedSpace X] {u : X → ℝ}
    (hu : Submission.HarmonicOnX u Set.univ) (x : X) :
    ∃ F : X → ℂ, Submission.HolomorphicOnX F Set.univ ∧ ∀ y, (F y).re = u y :=
  exists_holomorphic_conjugate_of_subsingleton hu x

/-- **The logarithmic form of the substitute.**

On a complex one-manifold where every homomorphism `π₁ → ℝ` vanishes, a nowhere vanishing
holomorphic function has a holomorphic logarithm.  This is the *multiplicative* counterpart of the
vanishing of the conjugate period, and the tool used to turn a non-zero "winding" into a
non-null-homotopic loop: if `γ` lifts to a loop through `log f`, then `γ` is null-homotopic. -/
theorem exists_log_of_ne_zero_of_subsingleton (x₀ : X)
    [Subsingleton (Additive (FundamentalGroup X x₀) →+ ℝ)]
    {f : X → ℂ} (hf : Submission.HolomorphicOnX f Set.univ) (hne : ∀ y, f y ≠ 0) :
    ∃ H : X → ℂ, Submission.HolomorphicOnX H Set.univ ∧ ∀ y, f y = Complex.exp (H y) :=
  Submission.HolomorphicOnX.exists_log_of_ne_zero x₀ hf hne

/-- **The logarithmic substitute on a simply connected surface.** -/
theorem exists_log_of_ne_zero_of_simplyConnected [SimplyConnectedSpace X] (x₀ : X)
    {f : X → ℂ} (hf : Submission.HolomorphicOnX f Set.univ) (hne : ∀ y, f y ≠ 0) :
    ∃ H : X → ℂ, Submission.HolomorphicOnX H Set.univ ∧ ∀ y, f y = Complex.exp (H y) :=
  exists_log_of_ne_zero_of_subsingleton x₀ hf hne

end Work.SimplyConnected.ABS
