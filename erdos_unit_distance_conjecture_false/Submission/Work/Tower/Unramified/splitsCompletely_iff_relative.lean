import Mathlib
import Submission.Work.Tower.Unramified.Basic
import Submission.Work.Defs.Basic
import Submission.Work.Tower.Unramified.SplitsCompletelyNF
import Submission.Work.Tower.Unramified.splitsCompletely_imp_NF
import Submission.Work.Tower.Unramified.splitsCompletely_of_NF
import Submission.Work.Tower.Unramified.splitsCompletelyIn_imp_NF
import Submission.Work.Tower.Unramified.splitsCompletelyIn_of_NF
import Submission.Work.Tower.Unramified.splitsCompletelyNF_imp
import Submission.Work.Tower.Unramified.splitsCompletelyNF_of

/-!
# Complete splitting in a tower of number fields

The main result of this file is `splitsCompletely_iff_relative`: a rational prime `q` splits
completely in `L/ℚ` if and only if it splits completely in `F/ℚ` and every prime `𝔭` of `𝓞 F`
above `q` splits completely in the relative extension `L/F`.

The proof passes through the counting normal forms `SplitsCompletelyNF` and
`SplitsCompletelyInNF` introduced in `Submission/Work/Tower/Unramified/SplitsCompletelyNF.lean`.
-/

open NumberField
open scoped Classical nonZeroDivisors

namespace Work.Tower.Unramified

/-- `Work.Defs.SplitsCompletely` in terms of the counting normal form. -/
theorem splitsCompletely_iff_NF {K : Type*} [Field K] [NumberField K] (q : ℕ) (hq : Nat.Prime q) :
    Work.Defs.SplitsCompletely q K ↔ SplitsCompletelyNF q K :=
  ⟨splitsCompletely_imp_NF q hq, splitsCompletely_of_NF q hq⟩

/-- `Work.Tower.SplitsCompletelyIn` in terms of the counting normal form. -/
theorem splitsCompletelyIn_iff_NF {F L : Type*} [Field F] [Field L] [NumberField F] [NumberField L]
    [Algebra F L] [FiniteDimensional F L] {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsPrime)
    (h0 : 𝔭 ≠ ⊥) :
    Work.Tower.SplitsCompletelyIn F L 𝔭 ↔ SplitsCompletelyInNF F L 𝔭 :=
  ⟨splitsCompletelyIn_imp_NF h𝔭 h0, splitsCompletelyIn_of_NF h𝔭 h0⟩

/-- The counting normal form is local in a tower of number fields: `q` splits completely in
`L` iff it splits completely in `F` and every prime of `𝓞 F` above `q` splits completely in
`L/F`. -/
theorem splitsCompletelyNF_iff {F L : Type*} [Field F] [Field L] [NumberField F] [NumberField L]
    [Algebra F L] [FiniteDimensional F L] (q : ℕ) (hq : Nat.Prime q) :
    SplitsCompletelyNF q L ↔
      SplitsCompletelyNF q F ∧
        ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsPrime → (q : 𝓞 F) ∈ 𝔭 → SplitsCompletelyInNF F L 𝔭 :=
  ⟨splitsCompletelyNF_imp q hq, fun h => splitsCompletelyNF_of q hq h.1 h.2⟩

theorem splitsCompletely_iff_relative {F L : Type*} [Field F] [Field L] [NumberField F]
    [NumberField L] [Algebra F L] [FiniteDimensional F L] (q : ℕ) (hq : Nat.Prime q) :
    Work.Defs.SplitsCompletely q L ↔
      Work.Defs.SplitsCompletely q F ∧
        ∀ (𝔭 : Ideal (NumberField.RingOfIntegers F)), 𝔭.IsPrime →
          (q : NumberField.RingOfIntegers F) ∈ 𝔭 → Work.Tower.SplitsCompletelyIn F L 𝔭 := by
  have hne : ∀ (𝔭 : Ideal (𝓞 F)), (q : 𝓞 F) ∈ 𝔭 → 𝔭 ≠ ⊥ := by
    intro 𝔭 hmem hbot
    have hq0 : (q : 𝓞 F) = 0 := by simpa [hbot] using hmem
    exact hq.ne_zero (Nat.cast_eq_zero.mp hq0)
  constructor
  · intro hL
    obtain ⟨hF, hrel⟩ :=
      (splitsCompletelyNF_iff (F := F) (L := L) q hq).mp
        ((splitsCompletely_iff_NF (K := L) q hq).mp hL)
    refine ⟨(splitsCompletely_iff_NF (K := F) q hq).mpr hF, fun 𝔭 h𝔭 hmem => ?_⟩
    exact (splitsCompletelyIn_iff_NF (F := F) (L := L) h𝔭 (hne 𝔭 hmem)).mpr
      (hrel 𝔭 h𝔭 hmem)
  · rintro ⟨hF, hrel⟩
    refine (splitsCompletely_iff_NF (K := L) q hq).mpr
      ((splitsCompletelyNF_iff (F := F) (L := L) q hq).mpr
        ⟨(splitsCompletely_iff_NF (K := F) q hq).mp hF, fun 𝔭 h𝔭 hmem => ?_⟩)
    exact (splitsCompletelyIn_iff_NF (F := F) (L := L) h𝔭 (hne 𝔭 hmem)).mp
      (hrel 𝔭 h𝔭 hmem)

end Work.Tower.Unramified
