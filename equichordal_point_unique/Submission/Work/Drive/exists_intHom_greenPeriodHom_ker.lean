import Mathlib
import Submission.Work.Drive.Interfaces
import Submission.Work.Drive.MeridianDefs
import Submission.Work.SimplyConnected.ABS.periods_of_circleCharacter_trivial
import Submission.Work.Drive.exists_continuous_singleZero_phase
import Submission.Work.Drive.exists_phase_of_chain_charts
import Submission.Work.Drive.exists_phase_chain_charts
import Submission.Work.Drive.exists_intHom_greenPeriodHom_ker_of_phase_and_matching
import Submission.Work.Drive.greenPeriodHom_eq_windingHom

namespace Work.Drive

/-!
# The periods on the kernel of `π₁(X ∖ {z₀}) → π₁(X)` come from an integer-valued homomorphism

This file owns the target

`Work.Drive.exists_intHom_greenPeriodHom_ker`:

for `X` a connected, second countable, non-compact Riemann surface, `z₀ : X`, `U := X ∖ {z₀}` and
`E : X → ℝ` harmonic on `U` with a *unit* logarithmic pole at `z₀`, the period homomorphism

`P := Work.ModulusLP.greenPeriodHom hEharm u₀ : π₁(U,u₀) →+ ℝ`

of the conjugate differential of `E` is, on the loops that are null-homotopic in `X`, given by a
*single* integer-valued homomorphism `W : π₁(U,u₀) →+ ℤ`:

`inclMapP z₀ u₀ γ = 1 ⟹ P γ = (W γ) · 2π`.

## The route recorded here (the "meridian" route)

Write `j : π₁(U,u₀) → π₁(X,u₀.1)` for the map induced by the inclusion.  Two facts about the
*meridian* of `z₀` give the target, and both are statements of surface topology that are isolated
(and delegated) in the modules

* `Work.Drive.exists_int_hom_extends_meridian` (primitivity of the meridian: every integer-valued
  homomorphism of `π₁(D ∖ {z₀})`, `D` a simply connected disc around `z₀`, extends to
  `π₁(U,·)`);
* `Work.Drive.ker_inclMapP_le_normalClosure_meridian` (the van Kampen kernel statement:
  `ker j` is the normal closure of the image of `π₁(D ∖ {z₀})`);

together with the two facts already in the workspace:

* `Work.ModulusLP.greenPeriodHom_two_pi_zmultiples` — for `γ ∈ ker j`, `P γ ∈ 2πℤ`
  (the unit residue computation at the pole);
* `greenPeriodHom_conj` below — `P` is invariant under conjugation, because it takes values in the
  abelian group `ℝ`.

Indeed, let `k : ker j → ℤ` be the unique integer-valued function with `P n = k n · 2π` (well
defined by the residue computation).  Then `k` is a homomorphism and, being invariant under
conjugation, it is determined by its values on the *generators* of `ker j` as a normal subgroup,
i.e. by the conjugates of the meridian.  The winding homomorphism about `z₀` — the extension of a
generator of `π₁(D ∖ {z₀})` produced by the primitivity statement — takes the value `1` on the
meridian and hence agrees with `k / k(meridian)` on every conjugate of the meridian; the two
homomorphisms therefore agree on `ker j`, and the extension `ᾱ : π₁(U,u₀) →+ ℤ` of the primitivity
statement satisfies `ᾱ|ₖₑᵣ ⱼ = k`: it is the required `W`.

(The remaining bookkeeping is the base-point transport from the point `q ∈ D ∖ {z₀}` at which the
two meridian statements are phrased to the base point `u₀` of the statement; it uses only the
standard `FundamentalGroup` transport along a path and the invariance of `P` proved below.)
-/

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **Uniqueness of the integer** in the period condition: `k · 2π = l · 2π` forces `k = l`. -/
theorem int_eq_of_cast_mul_two_pi_eq {k l : ℤ}
    (h : (k : ℝ) * (2 * Real.pi) = (l : ℝ) * (2 * Real.pi)) : k = l := by
  have h2 : (2 * Real.pi : ℝ) ≠ 0 := by
    have := Real.pi_ne_zero; positivity
  have h0 : ((k : ℝ) - (l : ℝ)) * (2 * Real.pi) = 0 := by rw [sub_mul, h, sub_self]
  have h3 : (k : ℝ) - (l : ℝ) = 0 := by
    rcases mul_eq_zero.mp h0 with h4 | h4
    · exact h4
    · exact absurd h4 h2
  have h4 : (k : ℝ) = (l : ℝ) := sub_eq_zero.mp h3
  exact_mod_cast h4

/-- **The conjugate period homomorphism is invariant under conjugation**, because its values lie in
the abelian group `ℝ`. -/
theorem greenPeriodHom_conj {z₀ : X} {E : X → ℝ}
    (hEharm : Submission.HarmonicOnX E (Set.univ \ {z₀}))
    (u₀ : Work.Modulus.puncturedOpens z₀)
    (δ γ : FundamentalGroup (↥(Work.Modulus.puncturedOpens z₀)) u₀) :
    Work.ModulusLP.greenPeriodHom hEharm u₀ (Additive.ofMul (δ * γ * δ⁻¹))
      = Work.ModulusLP.greenPeriodHom hEharm u₀ (Additive.ofMul γ) := by
  have h1 : (Additive.ofMul (δ * γ * δ⁻¹) : Additive (FundamentalGroup _ u₀))
      = Additive.ofMul δ + Additive.ofMul γ + Additive.ofMul δ⁻¹ := rfl
  have h2 : (Additive.ofMul δ⁻¹ : Additive (FundamentalGroup _ u₀)) = - Additive.ofMul δ := rfl
  rw [h1, map_add, map_add, h2, map_neg]
  ring

/-! ## The integer-valued homomorphism on the kernel of the inclusion -/

/-- **The period of a kernel element is a multiple of `2π`** (the unit residue computation at the
pole, `Work.ModulusLP.greenPeriodHom_two_pi_zmultiples`). -/
theorem kerPeriod_exists {z₀ : X} {E : X → ℝ}
    (hEharm : Submission.HarmonicOnX E (Set.univ \ {z₀}))
    (hpole : Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {z₀}) z₀ E)
    (u₀ : Work.Modulus.puncturedOpens z₀)
    (n : ↥((Work.SimplyConnected.ABS.inclMapP z₀ u₀).ker)) :
    ∃ k : ℤ, Work.ModulusLP.greenPeriodHom hEharm u₀
      (Additive.ofMul ((n : FundamentalGroup (↥(Work.Modulus.puncturedOpens z₀)) u₀))) =
        k * (2 * Real.pi) :=
  Work.ModulusLP.greenPeriodHom_two_pi_zmultiples hEharm hpole u₀
    ((n : FundamentalGroup (↥(Work.Modulus.puncturedOpens z₀)) u₀))
    ((MonoidHom.mem_ker).mp n.2)

/-- **The integer attached to a kernel element** by the period condition. -/
noncomputable def kerPeriodInt {z₀ : X} {E : X → ℝ}
    (hEharm : Submission.HarmonicOnX E (Set.univ \ {z₀}))
    (hpole : Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {z₀}) z₀ E)
    (u₀ : Work.Modulus.puncturedOpens z₀)
    (n : ↥((Work.SimplyConnected.ABS.inclMapP z₀ u₀).ker)) : ℤ :=
  Classical.choose (kerPeriod_exists hEharm hpole u₀ n)

/-- The defining property of `kerPeriodInt`. -/
theorem kerPeriodInt_spec {z₀ : X} {E : X → ℝ}
    (hEharm : Submission.HarmonicOnX E (Set.univ \ {z₀}))
    (hpole : Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {z₀}) z₀ E)
    (u₀ : Work.Modulus.puncturedOpens z₀)
    (n : ↥((Work.SimplyConnected.ABS.inclMapP z₀ u₀).ker)) :
    Work.ModulusLP.greenPeriodHom hEharm u₀
      (Additive.ofMul ((n : FundamentalGroup (↥(Work.Modulus.puncturedOpens z₀)) u₀))) =
        (kerPeriodInt hEharm hpole u₀ n : ℝ) * (2 * Real.pi) :=
  Classical.choose_spec (kerPeriod_exists hEharm hpole u₀ n)

/-- **`kerPeriodInt` is additive**: this is what makes the periods on the kernel the values of a
*single* integer-valued homomorphism. -/
theorem kerPeriodInt_add {z₀ : X} {E : X → ℝ}
    (hEharm : Submission.HarmonicOnX E (Set.univ \ {z₀}))
    (hpole : Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {z₀}) z₀ E)
    (u₀ : Work.Modulus.puncturedOpens z₀)
    (m n : ↥((Work.SimplyConnected.ABS.inclMapP z₀ u₀).ker)) :
    kerPeriodInt hEharm hpole u₀ (m * n)
      = kerPeriodInt hEharm hpole u₀ m + kerPeriodInt hEharm hpole u₀ n := by
  have h2 : (Additive.ofMul (((m * n : ↥((Work.SimplyConnected.ABS.inclMapP z₀ u₀).ker)) :
      FundamentalGroup (↥(Work.Modulus.puncturedOpens z₀)) u₀)) : Additive (FundamentalGroup _ u₀))
      = Additive.ofMul ((m : FundamentalGroup _ u₀))
        + Additive.ofMul ((n : FundamentalGroup _ u₀)) := rfl
  have h3 : Work.ModulusLP.greenPeriodHom hEharm u₀
      (Additive.ofMul (((m * n : ↥((Work.SimplyConnected.ABS.inclMapP z₀ u₀).ker)) :
        FundamentalGroup (↥(Work.Modulus.puncturedOpens z₀)) u₀)))
      = Work.ModulusLP.greenPeriodHom hEharm u₀ (Additive.ofMul ((m : FundamentalGroup _ u₀)))
        + Work.ModulusLP.greenPeriodHom hEharm u₀
            (Additive.ofMul ((n : FundamentalGroup _ u₀))) := by
    rw [h2, map_add]
  have hA := kerPeriodInt_spec (hEharm := hEharm) (hpole := hpole) u₀ (m * n)
  have hB := kerPeriodInt_spec (hEharm := hEharm) (hpole := hpole) u₀ m
  have hC := kerPeriodInt_spec (hEharm := hEharm) (hpole := hpole) u₀ n
  have key : ((kerPeriodInt hEharm hpole u₀ (m * n) : ℝ)
        - ((kerPeriodInt hEharm hpole u₀ m : ℝ) + (kerPeriodInt hEharm hpole u₀ n : ℝ)))
        * (2 * Real.pi) = 0 := by
    rw [sub_mul, ← hA, h3, hB, hC]
    ring
  have h2pi : (2 * Real.pi : ℝ) ≠ 0 := by
    have := Real.pi_ne_zero; positivity
  have hz : (kerPeriodInt hEharm hpole u₀ (m * n) : ℝ)
      - ((kerPeriodInt hEharm hpole u₀ m : ℝ) + (kerPeriodInt hEharm hpole u₀ n : ℝ)) = 0 := by
    rcases mul_eq_zero.mp key with h | h
    · exact h
    · exact absurd h h2pi
  have hcast : (kerPeriodInt hEharm hpole u₀ (m * n) : ℝ)
      = ((kerPeriodInt hEharm hpole u₀ m + kerPeriodInt hEharm hpole u₀ n : ℤ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast hcast

/-- **The period on the kernel as an integer-valued homomorphism.** -/
noncomputable def kerPeriodHom {z₀ : X} {E : X → ℝ}
    (hEharm : Submission.HarmonicOnX E (Set.univ \ {z₀}))
    (hpole : Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {z₀}) z₀ E)
    (u₀ : Work.Modulus.puncturedOpens z₀) :
    Additive ↥((Work.SimplyConnected.ABS.inclMapP z₀ u₀).ker) →+ ℤ where
  toFun a := kerPeriodInt hEharm hpole u₀ (Additive.toMul a)
  map_zero' := by
    show kerPeriodInt hEharm hpole u₀ (Additive.toMul (0 : Additive ↥((Work.SimplyConnected.ABS.inclMapP z₀ u₀).ker))) = 0
    have hone : Additive.toMul (0 : Additive ↥((Work.SimplyConnected.ABS.inclMapP z₀ u₀).ker)) = 1 := rfl
    rw [hone]
    have hspec := kerPeriodInt_spec (hEharm := hEharm) (hpole := hpole) u₀
      (1 : ↥((Work.SimplyConnected.ABS.inclMapP z₀ u₀).ker))
    have h1 : ((1 : ↥((Work.SimplyConnected.ABS.inclMapP z₀ u₀).ker)) :
        FundamentalGroup (↥(Work.Modulus.puncturedOpens z₀)) u₀) = 1 := rfl
    rw [h1] at hspec
    have hz : (Additive.ofMul (1 : FundamentalGroup (↥(Work.Modulus.puncturedOpens z₀)) u₀)
        : Additive (FundamentalGroup _ u₀)) = 0 := rfl
    rw [hz, map_zero] at hspec
    have hcast : (kerPeriodInt hEharm hpole u₀
        (1 : ↥((Work.SimplyConnected.ABS.inclMapP z₀ u₀).ker)) : ℝ) = 0 := by
      have hprod : (kerPeriodInt hEharm hpole u₀
          (1 : ↥((Work.SimplyConnected.ABS.inclMapP z₀ u₀).ker)) : ℝ) * (2 * Real.pi) = 0 :=
        hspec.symm
      have h2pi : (2 * Real.pi : ℝ) ≠ 0 := by
        have := Real.pi_ne_zero; positivity
      rcases mul_eq_zero.mp hprod with h | h
      · exact h
      · exact absurd h h2pi
    exact_mod_cast hcast
  map_add' a b := by
    have h : Additive.toMul (a + b)
        = Additive.toMul a * Additive.toMul b := rfl
    rw [h]
    exact kerPeriodInt_add (hEharm := hEharm) (hpole := hpole) u₀ (Additive.toMul a) (Additive.toMul b)


theorem exists_intHom_greenPeriodHom_ker {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    (hX : ¬ CompactSpace X) {z₀ : X} {E : X → ℝ}
    (hEharm : Submission.HarmonicOnX E (Set.univ \ {z₀}))
    (hpole : Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {z₀}) z₀ E)
    (u₀ : Work.Modulus.puncturedOpens z₀) :
    ∃ W : Additive (FundamentalGroup (↥(Work.Modulus.puncturedOpens z₀)) u₀) →+ ℤ,
      ∀ γ : Additive (FundamentalGroup (↥(Work.Modulus.puncturedOpens z₀)) u₀),
        Work.SimplyConnected.ABS.inclMapP z₀ u₀ (Additive.toMul γ) = 1 →
          Work.ModulusLP.greenPeriodHom hEharm u₀ γ = (W γ : ℝ) * (2 * Real.pi) := by
  refine Work.Drive.exists_intHom_greenPeriodHom_ker_of_phase_and_matching hX hEharm hpole u₀ ?_ ?_
  · -- the global phase with a single simple zero, from the escaping chain of pivots
    obtain ⟨a, c, ρ, hca, ha0, hρ, hchain, hwell, hlf, -, hinj⟩ :=
      Work.Drive.exists_phase_chain_charts hX z₀
    exact Work.Drive.exists_phase_of_chain_charts z₀ a c ρ hca ha0 hρ hchain hwell hlf hinj
  · intro Θ hΘ hΘne hloc u W hW
    exact Work.Drive.greenPeriodHom_eq_windingHom hEharm hpole hΘ hΘne hloc u hW

end Work.Drive
