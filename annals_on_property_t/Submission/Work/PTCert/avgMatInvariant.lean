import Mathlib
import Submission.Work.PTCert.Chain

/-! Guidance from the project lead (the requester):

Context: annals_on_property_t. `theorem_1` is reduced (proved, Submission/Work/RouteB/Final.lean) to two
sum-of-squares certificates; Submission/Work/PTCert/ is the kernel-checked certificate pipeline. The
definitions you need are in `Submission/Work/PTCert/Interfaces.lean` (namespace `Submission.PTCert`);
`IsSOS` is `Submission.RouteB.IsSOS` (Submission/Work/RouteB/Symmetrisation.lean: `IsSOS.add`,
`IsSOS.finset_sum`, `IsSOS.map`, `isSOS_of_fintype`; `IsSOS.smul` is used in RouteB/Final.lean).
The star on `MonoidAlgebra ℝ G` is `mapDomain (·⁻¹)` (ChallengeDeps); import
`Submission.Work.RouteB.StarStructure` to get Mathlib's `star_mul`, `star_sum`, `star_smul`, … .
`star (of g) = of g⁻¹` (see Submission/Helpers.lean). Do NOT use `native_decide`. No `decide` on
`MulAut (FreeGroup _)` equalities in bulk (each costs ~0.2 s); prove things generically.
Definitions in `Submission/Work/PTCert/Chain.lean` (also Math.lean, Interfaces.lean).
Prove `AvgMatInvariant`.  From `ConjAction` (f injective, f (act g i) = g f i g⁻¹) derive
`act (g * h) i = act g (act h i)` for g,h ∈ Sg (apply f, use injectivity).  Then
`avgMat … (act h i) (act h j) = Σ_{g∈Sg} U (act (g*h) i) (act (g*h) j)` and reindex `g ↦ g * h`
(a bijection of `Sg` since it is a finite subgroup; `Finset.sum_nbij'` with inverse `g ↦ g * h⁻¹`). ~60 lines.
-/

namespace Work.PTCert

open Submission.PTCert

private lemma act_mul_of_conjAction {G : Type} [Group G] {Sg : Finset G} (hSg : IsFinSubgroup Sg)
    {ι : Type} {f : ι → G} {act : G → ι → ι} (hCA : ConjAction Sg f act)
    {g : G} (hg : g ∈ Sg) {h : G} (hh : h ∈ Sg) (k : ι) :
    act (g * h) k = act g (act h k) := by
  obtain ⟨hf, hact⟩ := hCA
  have hmul := hSg.2.1
  exact hf (by
    rw [hact (g * h) (hmul g hg h hh) k, hact g hg (act h k), hact h hh k]
    group)

theorem avgMatInvariant : AvgMatInvariant := by
  intro G _ Sg hSg ι f act hCA U h hh i j
  have hmul : ∀ s ∈ Sg, ∀ t ∈ Sg, s * t ∈ Sg := hSg.2.1
  have hinv : ∀ s ∈ Sg, s⁻¹ ∈ Sg := hSg.2.2
  calc avgMat Sg act U (act h i) (act h j)
      = ∑ g ∈ Sg, U (act (g * h) i) (act (g * h) j) := by
        simp only [avgMat, Matrix.of_apply]
        refine Finset.sum_congr rfl (fun g hg => ?_)
        rw [← act_mul_of_conjAction hSg hCA hg hh i,
            ← act_mul_of_conjAction hSg hCA hg hh j]
    _ = ∑ g ∈ Sg, U (act g i) (act g j) := by
        refine Finset.sum_nbij' (fun g => g * h) (fun g => g * h⁻¹) ?_ ?_ ?_ ?_ ?_
        · intro a ha; exact hmul a ha h hh
        · intro a ha; exact hmul a ha h⁻¹ (hinv h hh)
        · intro a _; group
        · intro a _; group
        · intro a _; rfl
    _ = avgMat Sg act U i j := by simp only [avgMat, Matrix.of_apply]

end Work.PTCert
