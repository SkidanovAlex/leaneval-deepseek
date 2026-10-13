import Mathlib
import Submission.Work.DSM1p.Basic

namespace Work.DSM1p.Assembly

/-- Over a local ring `A`, a flat `A`-module `B` whose multiple `𝔪 • ⊤` by the maximal
ideal is not everything is faithfully flat: `𝔪` is the unique maximal ideal, so the single
hypothesis discharges every clause of the definition. -/
theorem faithfullyFlat_of_flat_of_maximalIdeal_smul_ne_top {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [IsLocalRing A] [Module.Flat A B]
    (h : IsLocalRing.maximalIdeal A • (⊤ : Submodule A B) ≠ ⊤) :
    Module.FaithfullyFlat A B :=
  ⟨fun m hm => by rw [IsLocalRing.eq_maximalIdeal hm]; exact h⟩

end Work.DSM1p.Assembly
