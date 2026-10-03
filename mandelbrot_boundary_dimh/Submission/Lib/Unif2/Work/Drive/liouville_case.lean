import Mathlib
import Submission.Lib.Unif2.Work.Drive.Interfaces
import Submission.Lib.Unif2.Work.Parabolic.Reduction
import Submission.Lib.Unif2.Work.Mori.UnitGreen
import Submission.Lib.Unif2.Work.Drive.boundedHolomorphic_const
import Submission.Lib.Unif2.Work.Drive.singlePoleBounded
import Submission.Lib.Unif2.Work.Drive.exists_matched_evans_of_not_hasWeakGreen
import Submission.Lib.Unif2.Work.Drive.exists_injective_modulus
import Submission.Lib.Unif2.Work.Drive.conclusion_of_injective_holomorphic_plane

/-!
# Area O -- no weak Green function implies `X ≅ ℂ` (the Liouville case)

`Work.Drive.HasWeakGreen X` says that `X` carries a positive harmonic function on `X ∖ {z₀}` with a
*unit* logarithmic pole at `z₀` (no decay at infinity is asked for).  In this case the classical
Ahlfors argument applies (Area W, `Work.Drive.weak_case`).  Here we treat the opposite case, where
`X` admits no such function.

The proof is an assembly of five proved lemmas:

* `Work.Drive.boundedHolomorphic_const` -- `¬ HasWeakGreen X` forces every bounded holomorphic
  function on `X` to be constant (Liouville);
* `Work.Drive.singlePoleBounded` -- at every point `a` there is a harmonic function on `X∖{a}` with
  a *unit* logarithmic pole at `a`, bounded above off a compact set;
* `Work.Drive.exists_matched_evans_of_not_hasWeakGreen` -- under `¬ HasWeakGreen`, two *matched*
  single-pole potentials `Ea`, `Eb` with `Ea - Eb ≤ 1` off a compact set; their difference is the
  pair function `τ` (`pairFunction_of_not_hasWeakGreen` below);
* `Work.Drive.exists_injective_modulus` -- the period condition `hP`, Liouville and the pair function
  produce an injective holomorphic function `X → ℂ` with a single simple zero (the Liouville
  injectivity argument: two preimages of a value `w` would give a bounded holomorphic function
  with a zero, contradiction);
* `Work.Drive.conclusion_of_injective_holomorphic_plane` -- an injective holomorphic function
  `X → ℂ`, parabolicity and `Hom(π₁ X, ℝ) = 0` give the challenge conclusion (via the `√`-trick
  and `Submission.uniformization_of_injective_into_disc`, without using simple connectivity).
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

noncomputable section

open Filter Set Classical

namespace Work.Drive

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- A unit-pole Green function is a weak Green function: it has the same positivity, harmonicity
and unit logarithmic pole; the relative-compactness clause is simply dropped. -/
theorem hasWeakGreen_of_isUnitGreenFunctionAt {z₀ : X} {E : X → ℝ}
    (h : Work.UnitGreen.IsUnitGreenFunctionAt (X := X) z₀ E) : HasWeakGreen X :=
  ⟨z₀, E, h.1.1, h.1.2.1,
    ⟨h.2.choose, h.2.choose_spec.choose, h.2.choose_spec.choose_spec.1,
      fun x hx _ hxne => h.2.choose_spec.choose_spec.2 x hx hxne⟩⟩

/-- **No weak Green function implies parabolicity.**  A unit-pole Green function (in the
relative-compactness sense) is in particular a weak one, so the absence of the latter rules out the
former, and `Work.Mori.isParabolic_of_not_exists_isUnitGreenFunction` turns that into
`Work.Parabolic.IsParabolic`. -/
theorem isParabolic_of_not_hasWeakGreen (hX : ¬ CompactSpace X) (h : ¬ HasWeakGreen X) :
    Work.Parabolic.IsParabolic X :=
  Work.Mori.isParabolic_of_not_exists_isUnitGreenFunction (X := X) hX
    (fun ⟨z₀, E, hE⟩ => h (hasWeakGreen_of_isUnitGreenFunctionAt hE))

/-- **The pair function in the no-weak-Green case**: the difference of two matched Evans
potentials of `Work.Drive.exists_matched_evans_of_not_hasWeakGreen`.

`τ := Ea - Eb` is harmonic off `{a,b}` (the two singularities are at `a`, `b` respectively, and near
each of them the *other* potential is harmonic, hence bounded), has the unit logarithmic pole at `a`
and the opposite one at `b`, and is bounded above off a compact set. -/
theorem pairFunction_of_not_hasWeakGreen (hX : ¬ CompactSpace X) (hO : ¬ HasWeakGreen X)
    {a b : X} (hab : a ≠ b) :
    ∃ τ : X → ℝ,
      Submission.HarmonicOnX τ (Set.univ \ {a, b}) ∧
      Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {a, b}) a τ ∧
      Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {b}) b (fun x => -τ x) ∧
      ∃ K : Set X, IsCompact K ∧ ∀ x ∉ K, τ x ≤ 1 := by
  obtain ⟨Ea, Eb, hEa, hpEa, hEb, hpEb, K, hK, hbound⟩ :=
    Work.Drive.exists_matched_evans_of_not_hasWeakGreen (X := X) hX hab hO
  -- membership bookkeeping for the two punctured sets
  have hmemA : ∀ x : X, x ∈ Set.univ \ {a, b} → x ∈ Set.univ \ {a} := by
    intro x hx
    simp only [Set.mem_sdiff, Set.mem_univ, Set.mem_insert_iff, Set.mem_singleton_iff,
      true_and, not_or] at hx ⊢
    exact hx.1
  have hmemB : ∀ x : X, x ∈ Set.univ \ {a, b} → x ∈ Set.univ \ {b} := by
    intro x hx
    simp only [Set.mem_sdiff, Set.mem_univ, Set.mem_insert_iff, Set.mem_singleton_iff,
      true_and, not_or] at hx ⊢
    exact hx.2
  -- boundedness of a harmonic function near a point
  have hbdd_near : ∀ {f : X → ℝ} {y : X}, Submission.HarmonicOnXAt f y →
      ∃ C : ℝ, ∃ V : Set X, V ∈ 𝓝 y ∧ ∀ x ∈ V, |f x| ≤ C := by
    intro f y hf
    have hcont : ContinuousAt f y := hf.continuousAt
    have h1 : ∀ᶠ x in 𝓝 y, dist (f x) (f y) < 1 :=
      (Metric.tendsto_nhds.mp hcont.tendsto) 1 one_pos
    obtain ⟨V, hV, hVf⟩ := Filter.eventually_iff_exists_mem.mp h1
    refine ⟨|f y| + 1, V, hV, fun x hx => ?_⟩
    have h2 : dist (f x) (f y) < 1 := hVf x hx
    rw [Real.dist_eq] at h2
    have h3 : |f x| ≤ |f y| + |f x - f y| := by
      have h := abs_add_le (f y) (f x - f y)
      have hsub : f y + (f x - f y) = f x := by ring
      rwa [hsub] at h
    have h4 : |f x - f y| ≤ 1 := le_of_lt h2
    linarith
  refine ⟨fun x => Ea x - Eb x, ?_, ?_, ?_, K, hK, hbound⟩
  · -- harmonic off `{a,b}`
    intro x hx
    exact (hEa x (hmemA x hx)).sub (hEb x (hmemB x hx))
  · -- the unit logarithmic pole at `a`
    obtain ⟨C, V, hV, hCV⟩ := hpEa
    obtain ⟨C₂, V₂, hV₂, hC₂⟩ :=
      hbdd_near (f := Eb) (y := a) (hEb a (by simp [Set.mem_sdiff, hab]))
    refine ⟨C + C₂, V ∩ V₂, Filter.inter_mem hV hV₂, ?_⟩
    intro x hxV hxΩ hxne
    have h1 : |Ea x + Real.log ‖(chartAt ℂ a) x - (chartAt ℂ a) a‖| ≤ C :=
      hCV x hxV.1 (hmemA x hxΩ) hxne
    have h2 : |Eb x| ≤ C₂ := hC₂ x hxV.2
    have hsplit : (Ea x - Eb x) + Real.log ‖(chartAt ℂ a) x - (chartAt ℂ a) a‖
        = (Ea x + Real.log ‖(chartAt ℂ a) x - (chartAt ℂ a) a‖) + (-Eb x) := by ring
    rw [hsplit]
    calc |(Ea x + Real.log ‖(chartAt ℂ a) x - (chartAt ℂ a) a‖) + -Eb x|
        ≤ |Ea x + Real.log ‖(chartAt ℂ a) x - (chartAt ℂ a) a‖| + |-Eb x| := abs_add_le _ _
      _ = |Ea x + Real.log ‖(chartAt ℂ a) x - (chartAt ℂ a) a‖| + |Eb x| := by rw [abs_neg]
      _ ≤ C + C₂ := add_le_add h1 h2
  · -- the opposite unit logarithmic pole at `b`
    obtain ⟨C, V, hV, hCV⟩ := hpEb
    obtain ⟨C₂, V₂, hV₂, hC₂⟩ :=
      hbdd_near (f := Ea) (y := b) (hEa b (by simp [Set.mem_sdiff, hab.symm]))
    refine ⟨C + C₂, V ∩ V₂, Filter.inter_mem hV hV₂, ?_⟩
    intro x hxV hxΩ hxne
    have h1 : |Eb x + Real.log ‖(chartAt ℂ b) x - (chartAt ℂ b) b‖| ≤ C :=
      hCV x hxV.1 hxΩ hxne
    have h2 : |Ea x| ≤ C₂ := hC₂ x hxV.2
    have hsplit : -(Ea x - Eb x) + Real.log ‖(chartAt ℂ b) x - (chartAt ℂ b) b‖
        = (Eb x + Real.log ‖(chartAt ℂ b) x - (chartAt ℂ b) b‖) + (-Ea x) := by ring
    rw [hsplit]
    calc |(Eb x + Real.log ‖(chartAt ℂ b) x - (chartAt ℂ b) b‖) + -Ea x|
        ≤ |Eb x + Real.log ‖(chartAt ℂ b) x - (chartAt ℂ b) b‖| + |-Ea x| := abs_add_le _ _
      _ = |Eb x + Real.log ‖(chartAt ℂ b) x - (chartAt ℂ b) b‖| + |Ea x| := by rw [abs_neg]
      _ ≤ C + C₂ := add_le_add h1 h2

/-- **Area O**: with no weak Green function, `X` is biholomorphic to `ℂ`. -/
theorem liouville_case {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    (hX : ¬ CompactSpace X) (x : X) [Subsingleton (Additive (FundamentalGroup X x) →+ ℝ)]
    (hP : Work.Drive.PeriodsHold X) (hO : ¬ Work.Drive.HasWeakGreen X) :
    Work.Drive.Conclusion X := by
  have hpar : Work.Parabolic.IsParabolic X := isParabolic_of_not_hasWeakGreen (X := X) hX hO
  have hbddHolo : ∀ {g : X → ℂ}, Submission.HolomorphicOnX g Set.univ →
      (∃ M : ℝ, ∀ y : X, ‖g y‖ ≤ M) → ∃ c : ℂ, ∀ y : X, g y = c :=
    fun {g} hg hb => boundedHolomorphic_const (X := X) hO hg hb
  have hb : ∀ a : X, ∃ E : X → ℝ, Submission.HarmonicOnX E (Set.univ \ {a}) ∧
      Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {a}) a E ∧
      ∃ K : Set X, IsCompact K ∧ ∀ y ∉ K, E y ≤ 1 :=
    fun a => singlePoleBounded (X := X) hX a
  have hpair : ∀ a b : X, a ≠ b → ∃ τ : X → ℝ,
      Submission.HarmonicOnX τ (Set.univ \ {a, b}) ∧
      Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {a, b}) a τ ∧
      Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {b}) b (fun y => -τ y) ∧
      ∃ K : Set X, IsCompact K ∧ ∀ y ∉ K, τ y ≤ 1 :=
    fun a b hab => pairFunction_of_not_hasWeakGreen (X := X) hX hO hab
  obtain ⟨Φ, hΦ, -, -, hinj⟩ :=
    exists_injective_modulus (X := X) hX hP hbddHolo hb hpair x
  exact conclusion_of_injective_holomorphic_plane (X := X) hX x hpar hΦ hinj

end Work.Drive
