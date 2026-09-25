import Submission.Work.Tower.AssemblyProP.Interface

/-!
# The target of the class-field-theory program

The single remaining input of the whole project is `∃ C₀, Work.Tower.Shafarevich.H2Estimate C₀`;
`Work.Tower.AssemblyProP.exists_tower_of_H2Estimate` turns it into the statement of
`Work.Interface.exists_tower`.  This file restates that reduction under a short name so that it is
easy to find, and records the arithmetic target in the `T`-split `∅`-form used inside the tower.

See `Submission/Work/CFT/README.md` for the two candidate routes and for the statements that are
*false* (the estimate without maximality, and without the `+|T|` term).
-/

open NumberField
open scoped Classical nonZeroDivisors

namespace Work
namespace CFT

/-- **Shafarevich's relation-rank estimate for the maximal everywhere-unramified pro-`3` group**
(this is the `T = ∅` case of `Work.Tower.Shafarevich.H2Estimate`, isolated because it is what the
classical sources state, and because it is the shape a direct class-field-theoretic proof
produces; the `T`-split version used by the tower follows from it by cutting the Frobenius
elements at `T`). -/
def ShafarevichEstimate (C : ℕ) : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F],
    Module.finrank ℚ F = 3 →
    ∀ (K : Type) [Field K] [NumberField K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K],
      Work.Tower.IsUnramifiedExtension F K → IsPGroup 3 (Gal(K/F)) →
      Work.Tower.Shafarevich.IsMaximalSplittingExtension F K ∅ →
      Module.finrank (ZMod 3) (Work.Tower.Shafarevich.H2Fp 3 (Gal(K/F))) ≤
        Module.finrank (ZMod 3) (Work.Tower.Shafarevich.H1Fp 3 (Gal(K/F))) + C

/-- The whole remaining gap, as a `Prop` so that it can be cited: Shafarevich's estimate for
*some* absolute constant, in the `T`-split form consumed by the tower. -/
def ShafarevichTarget : Prop := ∃ C₀ : ℕ, Work.Tower.Shafarevich.H2Estimate C₀

/-- The final assembly, from the target to the statement of `Work.Interface.exists_tower`. -/
theorem exists_tower_of_target (h : ShafarevichTarget) :
    ∀ (H : ℝ), 0 < H →
    ∃ (t : ℕ) (q : Fin t → ℕ) (C : ℝ), 0 < t ∧ (∀ b, Nat.Prime (q b)) ∧
      Function.Injective q ∧ (∀ b, q b % 4 = 1) ∧ 1 ≤ C ∧
      (H * C * (1 + Real.log C)) ^ 2 < (2 : ℝ) ^ t ∧
      ∀ N : ℕ, ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : IsCMField K),
        N ≤ Module.finrank ℚ K ∧ NumberField.rootDiscr K ≤ C ∧
        (∀ b, Work.Defs.SplitsCompletely (q b) K) :=
  Work.Tower.AssemblyProP.exists_tower_of_H2Estimate h

end CFT
end Work
