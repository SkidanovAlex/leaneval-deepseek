import Mathlib
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE7.DimAPI.nullDimLT_basics

namespace Work.CoreStep

open WilkiesDesign WilkiesDesign.E Work.WilE7.MainDesign

/-- `basePr n M z` is `Fin.init` of `projFirst (n+1) M z`: dropping the last coordinate after
projecting to the first `n+1` coordinates is the same as taking the first `n` coordinates. -/
theorem basePr_eq_init_projFirst {n M : ℕ} (z : Fin ((n + 1) + M) → ℝ) :
    basePr n M z = Fin.init (projFirst (n + 1) M z) :=
  funext fun _ => congrArg z (Fin.ext rfl)

theorem nullDimLT_basePr_of_proj {n M K : ℕ} {A : Set (Fin (n + 1) → ℝ)} {B : Set (Fin n → ℝ)}
    {Z : WilkiesDesign.E.SemiPf ((n + 1) + M)}
    (hproj : WilkiesDesign.E.projFirst (n + 1) M '' Z.set =
      A ∩ {y : Fin (n + 1) → ℝ | Fin.init y ∈ B})
    (hnd : Work.WilE7.MainDesign.NullDimLT B K) :
    Work.WilE7.MainDesign.NullDimLT (Work.WilE7.MainDesign.basePr n M '' Z.set) K := by
  refine NullDimLT.mono hnd fun w hw => ?_
  rcases hw with ⟨z, hz, rfl⟩
  have hmem : projFirst (n + 1) M z ∈ A ∩ {y : Fin (n + 1) → ℝ | Fin.init y ∈ B} := by
    rw [← hproj]
    exact ⟨z, hz, rfl⟩
  rw [basePr_eq_init_projFirst]
  exact hmem.2

end Work.CoreStep
