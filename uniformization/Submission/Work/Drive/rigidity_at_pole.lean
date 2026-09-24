import Mathlib
import Submission.Work.Drive.weakcase_deps

/-!
# Rigidity at the pole

`Work.Drive.rigidity_at_pole`: on a Riemann surface `X` on which all conjugate periods are
multiples of `2π` (`Work.Drive.PeriodsHold X`), and for which a positive harmonic function `E` with
a logarithmic pole at `y` exists, the extremal problem at `y` has a *rigid* solution: there is a
Perron envelope `E'` (positive, harmonic off `y`, log pole at `y`) dominating the whole extremal
family `Submission.extremalFamily y`, and a member `f` of the extremal family which attains the
envelope `‖f z‖ = exp (-(E' z))` at every `z ≠ y` and maximises the chart derivative at the pole.

The proof is a three-step assembly of existing workspace results.

* From `hP` and `hEharm`, `hEpole` the *holomorphic modulus* `Φ` of `E` exists
  (`Work.SimplyConnected.ABS.exists_modulus_of_logPole_of_periods`): `Φ` is holomorphic on `X`,
  has a simple zero at `y`, and `‖Φ z‖ = exp (-(E z))` off `y`.  In particular `Φ` is a non-zero
  member of the extremal family at `y`.

* Perron's method, fed with that member, produces the envelope `E'` which dominates the whole
  extremal family at `y` (`Work.SimplyConnected.ABS.exists_posHarmonic_logPole_dominating'`).

* The extremal derivative is attained (`Submission.exists_extremal`), and it is positive because
  the derivative of `Φ` at the pole does not vanish
  (`Submission.phi_deriv_ne_zero_of_logPole`).  The maximiser `f` then attains the envelope `E'`
  by Ahlfors' rigidity in its decay-free form
  (`Work.SimplyConnected.ABS.rigidity_of_maximizer_of_modulus`), whose modulus input is again the
  period hypothesis `hP`, now applied to `E'`.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Work.Drive

theorem rigidity_at_pole {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] (hP : Work.Drive.PeriodsHold X) {y : X}
    {E : X → ℝ} (hEpos : ∀ x : X, x ≠ y → 0 < E x)
    (hEharm : Submission.HarmonicOnX E (Set.univ \ {y}))
    (hEpole : Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {y}) y E) :
    ∃ (E' : X → ℝ) (f : X → ℂ),
      (∀ x : X, x ≠ y → 0 < E' x) ∧
      Submission.HarmonicOnX E' (Set.univ \ {y}) ∧
      Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {y}) y E' ∧
      (∀ g ∈ Submission.extremalFamily y, ∀ z : X, z ≠ y → ‖g z‖ ≤ Real.exp (-(E' z))) ∧
      f ∈ Submission.extremalFamily y ∧
      (∀ z : X, z ≠ y → ‖f z‖ = Real.exp (-(E' z))) ∧
      (0 < ‖deriv (f ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) y)‖) ∧
      (∀ g ∈ Submission.extremalFamily y,
        ‖deriv (g ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) y)‖ ≤
          ‖deriv (f ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) y)‖) := by
  classical
  -- ## Step 1. The holomorphic modulus of `E`, from the period hypothesis.
  obtain ⟨Φ, hΦhol, hΦzero, hΦmod, hΦpole⟩ :=
    Work.SimplyConnected.ABS.exists_modulus_of_logPole_of_periods hEharm hEpole
      (hP y E hEharm hEpole)
  -- ## `Φ` is a non-zero member of the extremal family at `y`.
  have hΦmem : Φ ∈ Submission.extremalFamily y :=
    Work.SimplyConnected.ABS.modulus_mem_extremalFamily' hΦhol hΦpole hEpos hΦmod
  have hΦne : ∃ x : X, Φ x ≠ 0 := by
    obtain ⟨z, hzsrc, hzy⟩ := Work.Modulus.exists_ne_of_mem_nhds (z₀ := y)
      ((chartAt ℂ y).open_source.mem_nhds (mem_chart_source ℂ y))
    refine ⟨z, fun hz0 => ?_⟩
    have h1 : ‖Φ z‖ = Real.exp (-(E z)) := hΦmod z hzy
    rw [hz0, norm_zero] at h1
    exact Real.exp_ne_zero (-(E z)) h1.symm
  -- ## Step 2. Perron's method: the envelope dominating the whole extremal family.
  obtain ⟨E', hE'pos, hE'harm, hE'pole, hE'dom⟩ :=
    Work.SimplyConnected.ABS.exists_posHarmonic_logPole_dominating' hΦmem hΦne hΦpole
  -- ## Step 3. The maximiser of the chart derivative at the pole.
  obtain ⟨f, hf, hfmax⟩ := Submission.exists_extremal (X := X) y
  obtain ⟨ρ, hρ, hρsub⟩ := Submission.exists_chartDisc_radius (X := X) y
  have hbdd : BddAbove (Submission.extremalDerivativeSet y) :=
    Submission.extremalDerivative_bddAbove hρ hρsub
  have hmax : ∀ g ∈ Submission.extremalFamily y,
      ‖deriv (g ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) y)‖ ≤
        ‖deriv (f ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) y)‖ := by
    intro g hg
    rw [hfmax]
    exact le_csSup hbdd ⟨g, hg, rfl⟩
  -- The extremal derivative is positive, because `‖Φ'(y)‖` is.
  have hΦderiv : 0 < ‖deriv (Φ ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) y)‖ :=
    norm_pos_iff.mpr (Submission.phi_deriv_ne_zero_of_logPole hΦpole)
  have hpos : 0 < ‖deriv (f ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) y)‖ := by
    rw [hfmax]
    exact lt_of_lt_of_le hΦderiv (le_csSup hbdd ⟨Φ, hΦmem, rfl⟩)
  -- ## Step 4. Ahlfors' rigidity, decay-free, for the envelope `E'`.
  obtain ⟨Φ', hΦ'hol, -, hΦ'mod, hΦ'pole⟩ :=
    Work.SimplyConnected.ABS.exists_modulus_of_logPole_of_periods hE'harm hE'pole
      (hP y E' hE'harm hE'pole)
  have hrig : ∀ z : X, z ≠ y → ‖f z‖ = Real.exp (-(E' z)) :=
    Work.SimplyConnected.ABS.rigidity_of_maximizer_of_modulus hf hmax hE'pos hE'harm hE'pole
      (fun z hz => hE'dom f hf z hz) ⟨Φ', hΦ'hol, hΦ'pole, hΦ'mod⟩
  exact ⟨E', f, hE'pos, hE'harm, hE'pole, hE'dom, hf, hrig, hpos, hmax⟩

end Work.Drive
