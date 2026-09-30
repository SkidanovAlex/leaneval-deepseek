import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.Pi6.K2Z.bd
import Submission.Work.StemsB.isSerreFibration_evalOne
import Submission.Work.StemsB.contractible_pathSpace
import Submission.Work.Cohomology.contractible
import Submission.Work.Stems.Engine.C2EvenRange
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# `K2Z` — the geometric input of the `K(ℤ,2)` forcing argument

For a based space `(X,x₀)` the *path–loop fibration* `evalOne X x₀ : PathSpace X x₀ → X` has
contractible total space and fibre the loop space `ΩX = Path x₀ x₀`; it is a Serre fibration.  This
file records the elementary transfers that the `K(ℤ,2)` computation needs:

* `finrank_coh_zero_of_pathConnected` — `H⁰(Y;𝕜) ≅ 𝕜` for path-connected `Y`;
* `isZero_coh_of_homeomorph`, `finrank_coh_of_homeomorph` — transfer of vanishing and of dimension
  along a homeomorphism (through homotopy invariance of singular cohomology);
* `fibre_pathFibre_*` — the elementary facts about the fibre of `evalOne`.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace Work.Pi6

noncomputable section

/-- `H⁰` of a path-connected space is one-dimensional. -/
theorem finrank_coh_zero_of_pathConnected (𝕜 : Type) [Field 𝕜] (Y : Type) [TopologicalSpace Y]
    [PathConnectedSpace Y] : Module.finrank 𝕜 (Coh 𝕜 Y 0) = 1 := by
  obtain ⟨e⟩ := Work.Cohomology.singularCohomology_zero 𝕜 (TopCat.of Y)
  rw [e.toLinearEquiv.finrank_eq]
  simp

/-- Vanishing of a cohomology group transfers across a homeomorphism. -/
theorem isZero_coh_of_homeomorph {𝕜 : Type} [Field 𝕜] {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) (n : ℕ) (h : CategoryTheory.Limits.IsZero (Coh 𝕜 Y n)) :
    CategoryTheory.Limits.IsZero (Coh 𝕜 X n) := by
  have h1 : CategoryTheory.IsIso (Work.Cohomology.singularCohomologyMap 𝕜 (TopCat.of Y)
      (TopCat.of X) (TopCat.ofHom (e.symm : C(Y, X))) n) :=
    Work.Cohomology.homotopyEquiv 𝕜 (TopCat.of Y) (TopCat.of X) (TopCat.ofHom (e.symm : C(Y, X)))
      (TopCat.ofHom (e : C(X, Y)))
      (Homeomorph.toHomotopyEquiv e.symm).left_inv.some
      (Homeomorph.toHomotopyEquiv e.symm).right_inv.some n
  exact CategoryTheory.Limits.IsZero.of_iso h
    (CategoryTheory.asIso (Work.Cohomology.singularCohomologyMap 𝕜 (TopCat.of Y) (TopCat.of X)
      (TopCat.ofHom (e.symm : C(Y, X))) n))

/-- The dimension of a cohomology group transfers across a homeomorphism. -/
theorem finrank_coh_of_homeomorph {𝕜 : Type} [Field 𝕜] {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) (n : ℕ) :
    Module.finrank 𝕜 (Coh 𝕜 X n) = Module.finrank 𝕜 (Coh 𝕜 Y n) := by
  have h1 : CategoryTheory.IsIso (Work.Cohomology.singularCohomologyMap 𝕜 (TopCat.of Y)
      (TopCat.of X) (TopCat.ofHom (e.symm : C(Y, X))) n) :=
    Work.Cohomology.homotopyEquiv 𝕜 (TopCat.of Y) (TopCat.of X) (TopCat.ofHom (e.symm : C(Y, X)))
      (TopCat.ofHom (e : C(X, Y)))
      (Homeomorph.toHomotopyEquiv e.symm).left_inv.some
      (Homeomorph.toHomotopyEquiv e.symm).right_inv.some n
  rw [(CategoryTheory.asIso (Work.Cohomology.singularCohomologyMap 𝕜 (TopCat.of Y) (TopCat.of X)
      (TopCat.ofHom (e.symm : C(Y, X))) n)).toLinearEquiv.finrank_eq]

end

end Work.Pi6
