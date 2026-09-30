import Mathlib
import Submission.Work.SSSR.Serre.E2dEngine
import Submission.Work.SSSR.StemsB.SphLoopRelPair
import Submission.Work.SSSR.Serre.nonempty_homology_iso_of_isZero_relChains
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

open Work.Serre
variable {R : Type} [CommRing R] [Nontrivial R]

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits AlgebraicTopology
namespace Work.SSSR.Serre

noncomputable section

/-- **The pair of the total space with the fibre over a point has vanishing relative homology**,
for a contraction of the base onto that point fixing it: the form with the ambient space `X`
itself. -/
theorem isZero_relChains_fibre_of_contraction {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z]
    (q : C(X, Z)) (hq : Work.SSSR.StemsB.IsSerreFibration q) (z₀ : Z)
    (c : C(Z × unitInterval, Z)) (hc0 : ∀ z, c (z, 0) = z) (hc1 : ∀ z, c (z, 1) = z₀)
    (hcz : ∀ t, c (z₀, t) = z₀) (m : ℕ) :
    IsZero ((Work.SSSR.Cohomology.relChains R (TopCat.of X) {x : X | q x = z₀}).homology m) := by
  have h := isZero_relChains_preimage_singleton (R := R) q hq z₀ c hc0 hc1 hcz m
  -- transport along the canonical homeomorphism `↥(q ⁻¹' univ) ≃ₜ X`
  have hAB : ∀ x : ↥(q ⁻¹' (Set.univ : Set Z)),
      x ∈ {y : ↥(q ⁻¹' (Set.univ : Set Z)) | (y : X) ∈ q ⁻¹' ({z₀} : Set Z)} ↔
        (Homeomorph.Set.univ X) x ∈ {y : X | q y = z₀} := by
    intro x
    show q (x : X) ∈ ({z₀} : Set Z) ↔ q ((x : ↥(Set.univ : Set X)) : X) = z₀
    simp
  obtain ⟨e⟩ := Work.SSSR.StemsB.nonempty_relChains_homology_iso_of_homeomorph (R := R)
    (X := TopCat.of ↥(q ⁻¹' (Set.univ : Set Z))) (Y := TopCat.of X)
    (Homeomorph.Set.univ X)
    {y : ↥(q ⁻¹' (Set.univ : Set Z)) | (y : X) ∈ q ⁻¹' ({z₀} : Set Z)}
    {y : X | q y = z₀} hAB m
  exact IsZero.of_iso h e.symm

end

end Work.SSSR.Serre
