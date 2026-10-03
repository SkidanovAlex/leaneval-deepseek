import Mathlib
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.ExtremalImports
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.modulusLP_main
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.exists_posHarmonic_logPole_dominating
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.extremal_maximizer_zero_fiber

/-!
# The period interface for the modulus of a logarithmic pole

The target of this file is the *sharpest* known form of the remaining input of
`Work.SimplyConnected.ABS.extremal_maximizer_zero_fiber`: the integrality of the conjugate periods
of a unit-log-pole harmonic function.

The chain proved here is

* `exists_modulus_of_logPole_of_periods` -- a harmonic `E` on `X \ {x₀}` with a *unit* logarithmic
  pole has a holomorphic modulus `Φ` (`‖Φ x‖ = exp (-(E x))` off the pole, simple zero at the pole)
  as soon as **all conjugate periods of `E` are integer multiples of `2π`**.  This is the
  `hasTrivialModulusMonodromy_of_periods` step of `modulusLP_main` plus the pole-order computation
  `poleOrderModulus_of_unitGreen`.

* `periods_of_loopsTrivial` -- the previously used hypothesis `AllLoopsOfPuncturedTrivialInX`
  implies the period condition (this is `greenPeriodHom_two_pi_zmultiples`), so the interface below
  is *weaker* than the one consumed by `extremal_maximizer_zero_fiber_of_loopsTrivial`.

* `extremal_maximizer_zero_fiber_of_periods` -- **the target**, with the single remaining input
  written out: for the Perron envelope `E` of the logarithmic pole (which
  `exists_posHarmonic_logPole_dominating'` *constructs* unconditionally), the conjugate periods are
  multiples of `2π`.

Consequently, under the challenge hypothesis, the target is *equivalent* to the integrality of the
periods of one harmonic function with a unit logarithmic pole.  Moreover the periods are a property
of the *pole class* alone: `Work.SimplyConnected.ABS.greenPeriodHom_eq_of_harmonic_extension`
(`Submission/Work/SimplyConnected/ABS/greenPeriodHom_eq_of_harmonic_extension.lean`) shows that two
harmonic functions on `X \ {x₀}` whose difference extends to a harmonic function on `X` have the
same period homomorphism — so *any* convenient representative of the pole class may be used to
compute them.  This is the form of the problem that
the "winding" route (`Work.SimplyConnected.ABS.windingHom`, `Work/Modulus/PeriodSetup.lean`)
attacks: the period homomorphism `greenPeriodHom hEharm u₀ : π₁(X \ {x₀}) → ℝ` kills the kernel of
`π₁(X \ {x₀}) → π₁(X)` modulo `2πℤ` (`greenPeriodHom_two_pi_zmultiples`), and its `2π`-normalised
residue class is `2π`-times the winding number about the pole, which descends to `π₁(X)` and dies by
the challenge hypothesis.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set Classical

namespace Work.SimplyConnected.ABS

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

open Work.Modulus

/-- **The period condition**: every conjugate period of `E` is an integer multiple of `2π`. -/
def PeriodsAreMultiplesOfTwoPi {z₀ : X} (E : X → ℝ)
    (hEharm : Submission.HarmonicOnX E (Set.univ \ {z₀})) : Prop :=
  ∀ (u₀ : puncturedOpens z₀) (γ : FundamentalGroup (puncturedOpens z₀) u₀),
    ∃ k : ℤ, Work.ModulusLP.greenPeriodHom hEharm u₀ (Additive.ofMul γ) = k * (2 * Real.pi)

/-- **The holomorphic modulus from the integrality of the periods** (decay-free form). -/
theorem exists_modulus_of_logPole_of_periods {z₀ : X} {E : X → ℝ}
    (hEharm : Submission.HarmonicOnX E (Set.univ \ {z₀}))
    (hpole : HasLogPoleOn (Set.univ \ {z₀}) z₀ E)
    (hper : PeriodsAreMultiplesOfTwoPi E hEharm) :
    ∃ Φ : X → ℂ, Submission.HolomorphicOnX Φ Set.univ ∧ Φ z₀ = 0 ∧
      (∀ x : X, x ≠ z₀ → ‖Φ x‖ = Real.exp (-(E x))) ∧ Submission.HasLogPoleAt z₀ Φ := by
  obtain ⟨Φ, hhol, hne, hmod⟩ :=
    Work.ModulusLP.hasTrivialModulusMonodromy_of_periods hEharm hpole hper
  have hp := Work.ModulusLP.poleOrderModulus_of_unitGreen hEharm hpole hhol hne hmod
  exact ⟨Φ, hhol, Submission.phi_zero_of_logPole hhol hp, hmod, hp⟩

/-- **The loop condition implies the period condition** (`greenPeriodHom_two_pi_zmultiples`). -/
theorem periods_of_loopsTrivial {z₀ : X} {E : X → ℝ}
    (hEharm : Submission.HarmonicOnX E (Set.univ \ {z₀}))
    (hpole : HasLogPoleOn (Set.univ \ {z₀}) z₀ E)
    (hloop : Work.Modulus.AllLoopsOfPuncturedTrivialInX (X := X) z₀) :
    PeriodsAreMultiplesOfTwoPi E hEharm :=
  fun u₀ γ => Work.ModulusLP.greenPeriodHom_two_pi_zmultiples hEharm hpole u₀ γ (hloop u₀ γ)

/-- **The target, from the integrality of the periods of the Perron envelope.**

The envelope itself is *constructed* here (`exists_posHarmonic_logPole_dominating'`), so the only
hypothesis of the theorem is the integrality of the periods of the conjugate of that (or any other)
positive harmonic function with a unit logarithmic pole at `x₀`. -/
theorem extremal_maximizer_zero_fiber_of_periods {x₀ : X}
    [Subsingleton (Additive (FundamentalGroup X x₀) →+ ℝ)]
    (hper : ∀ {E : X → ℝ}, (∀ x : X, x ≠ x₀ → 0 < E x) →
      (hEharm : Submission.HarmonicOnX E (Set.univ \ {x₀})) →
      HasLogPoleOn (Set.univ \ {x₀}) x₀ E → PeriodsAreMultiplesOfTwoPi E hEharm)
    {f : X → ℂ}
    (hf : f ∈ Submission.extremalFamily x₀)
    (hmax : ∀ g ∈ Submission.extremalFamily x₀,
      ‖deriv (g ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖ ≤
        ‖deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖)
    (hpos : 0 < ‖deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖) :
    f ⁻¹' {0} = {x₀} := by
  classical
  have hne : ∃ x : X, f x ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hzero : f = fun _ => (0 : ℂ) := funext fun x => hcon x
    have hd : deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) = 0 := by
      have h1 : (f ∘ (chartAt ℂ x₀).symm) = fun _ => (0 : ℂ) := by
        funext w; simp [hzero]
      rw [h1, deriv_const]
    rw [hd, norm_zero] at hpos
    exact lt_irrefl 0 hpos
  have hderivne : deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hpos
    exact lt_irrefl 0 hpos
  have hf0c : (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) = 0 := by
    simp only [Function.comp_apply, (chartAt ℂ x₀).left_inv (mem_chart_source ℂ x₀)]
    exact hf.2.2
  obtain ⟨H, hHana, hHne, hHeq⟩ :=
    exists_simpleZero_factorization (a := (chartAt ℂ x₀) x₀) (hf.1 x₀ (mem_univ x₀)) hf0c hderivne
  obtain ⟨E, hEpos, hEharm, hpole, _hdom⟩ :=
    exists_posHarmonic_logPole_dominating' (x₀ := x₀) hf hne ⟨H, hHana, hHne, hHeq⟩
  obtain ⟨Φ, hΦhol, hΦ0, hΦmod, hΦpole⟩ :=
    exists_modulus_of_logPole_of_periods hEharm hpole (hper hEpos hEharm hpole)
  have hΦfib : {x : X | Φ x = 0} = {x₀} := by
    ext x
    constructor
    · intro hx
      by_contra hxne
      have h1 : ‖Φ x‖ = Real.exp (-(E x)) := hΦmod x hxne
      rw [hx, norm_zero] at h1
      exact Real.exp_ne_zero (-(E x)) h1.symm
    · intro hx
      rw [hx]; exact hΦ0
  exact extremal_maximizer_zero_fiber_of_singleZeroFunction hΦhol hΦfib hΦpole hf hmax hpos

end Work.SimplyConnected.ABS

namespace Work.SimplyConnected.ABS

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **The period condition holds on a simply connected surface.**  Every loop of `X \ {x₀}` is a
loop of `X`, hence null-homotopic, so `greenPeriodHom_two_pi_zmultiples` applies. -/
theorem periods_of_simplyConnected [SimplyConnectedSpace X] {z₀ : X} {E : X → ℝ}
    (hEharm : Submission.HarmonicOnX E (Set.univ \ {z₀}))
    (hpole : HasLogPoleOn (Set.univ \ {z₀}) z₀ E) :
    PeriodsAreMultiplesOfTwoPi E hEharm := by
  haveI : Subsingleton (Additive (FundamentalGroup X z₀) →+ ℝ) := inferInstance
  refine fun u₀ γ => Work.ModulusLP.greenPeriodHom_two_pi_zmultiples hEharm hpole u₀ γ ?_
  exact Subsingleton.elim _ _

/-- **The period condition from the vanishing of the circle-valued characters.**

This is the sharpest form of the topological input of the period condition: it is *strictly weaker*
than the loop condition `AllLoopsOfPuncturedTrivialInX` used below (it only asks that the
period character, which is trivial on the loops null-homotopic in `X`, be trivial on `π₁(X,·)`).
Under the challenge hypothesis `Subsingleton (π₁(X,·) →+ ℝ)` it is *equivalent* to torsion-freeness
of `H₁(X;ℤ) = π₁(X)^{ab}` (`Work.SimplyConnected.subsingleton_hom_addCircle_of_torsionFree`), and
hence in particular follows from the abelian half of Johansson/Stallings.

The proof is the decay-free port
`Work.SimplyConnected.ABS.periodsAreMultiplesOfTwoPi_of_circleCharacter_trivial`
(`periods_of_circleCharacter_trivial.lean`). -/
theorem periods_of_circleCharacterTrivial {z₀ : X} {E : X → ℝ}
    (hEharm : Submission.HarmonicOnX E (Set.univ \ {z₀}))
    (hpole : HasLogPoleOn (Set.univ \ {z₀}) z₀ E)
    (hcirc : ∀ y : X, Subsingleton (Additive (FundamentalGroup X y) →+
      (ℝ ⧸ AddSubgroup.zmultiples (2 * Real.pi)))) :
    PeriodsAreMultiplesOfTwoPi E hEharm :=
  periodsAreMultiplesOfTwoPi_of_circleCharacter_trivial hEharm hpole hcirc

/-- **The period condition from the challenge hypothesis, via the loop condition.** -/
theorem periods_of_loopCondition {z₀ : X} {E : X → ℝ}
    (hEharm : Submission.HarmonicOnX E (Set.univ \ {z₀}))
    (hpole : HasLogPoleOn (Set.univ \ {z₀}) z₀ E)
    (hloop : Work.Modulus.AllLoopsOfPuncturedTrivialInX (X := X) z₀) :
    PeriodsAreMultiplesOfTwoPi E hEharm :=
  periods_of_loopsTrivial hEharm hpole hloop

end Work.SimplyConnected.ABS
