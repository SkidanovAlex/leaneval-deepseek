import Mathlib.NumberTheory.Padics.PadicNumbers
import Submission.Work.Kummer.Defs
import Submission.Work.QuadraticLocalGlobal.grunwald_degree_two
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u

namespace Work.AbsoluteKummer

open scoped Classical

noncomputable section

/-- The group `Kˣ/(Kˣ)²` of square classes of a field `K`. -/
abbrev SqClass (K : Type u) [Field K] := Kˣ ⧸ Work.Kummer.nthPowerSubgroup 2 Kˣ

/-- The localisation map on square classes at a prime `p`: a rational square class is sent to its
class in `ℚ_[p]`. -/
noncomputable def sqClassLocalize (p : ℕ) [Fact p.Prime] : SqClass ℚ →* SqClass ℚ_[p] :=
  QuotientGroup.map (Work.Kummer.nthPowerSubgroup 2 ℚˣ)
    (Work.Kummer.nthPowerSubgroup 2 (ℚ_[p])ˣ) (Units.map (algebraMap ℚ ℚ_[p])) (by
      intro x hx
      obtain ⟨z, hz⟩ := hx
      exact ⟨Units.map (algebraMap ℚ ℚ_[p]) z, by rw [← hz, ← map_pow]⟩)

@[simp] theorem sqClassLocalize_mk (p : ℕ) [Fact p.Prime] (x : ℚˣ) :
    sqClassLocalize p (QuotientGroup.mk' _ x) =
      QuotientGroup.mk' _ (Units.map (algebraMap ℚ ℚ_[p]) x) :=
  QuotientGroup.map_mk' _ _ _ _ x

end

end Work.AbsoluteKummer
