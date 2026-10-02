import Submission.Work.StemsB.FibrewiseTrivIso
import Submission.Work.Cohomology.MVCohomology

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The cohomological consequence of the fibrewise triviality over a disc

A fibrewise triviality `FibrewiseTrivial p W d₀` (`SerreSphereDefs.lean`) is, by definition, a
homotopy equivalence `p ⁻¹' W ≃ W × p ⁻¹' {d₀}` whose homotopies preserve the base coordinate.  This
file reads that data as a genuine `ContinuousMap.HomotopyEquiv` and takes its consequence on singular
cohomology: when `W` is contractible, restriction to the fibre

  `H^n(p ⁻¹' W) ≅ H^n(p ⁻¹' {d₀})`

is an isomorphism.  This is the first of the two identifications that turn the long exact sequence
of the pair `(E, E|_W)` into the Wang sequence (`WangSequence.lean`); the map `γ` of that file is
`Work.StemsB.cohomologyIso_fibreTriv`.
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

set_option linter.unusedVariables false

namespace Work.StemsB

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- **The trivialisation of a fibrewise triviality is a homotopy equivalence.** -/
def fibTrivHomotopyEquiv (p : C(E, B)) (W : Set B) (d₀ : ↥W) (hT : FibrewiseTrivial p W d₀) :
    ContinuousMap.HomotopyEquiv ↥(p ⁻¹' W) (↥W × ↥(p ⁻¹' {d₀.1})) where
  toFun := fibTrivΦ p W d₀ hT
  invFun := fibTrivΨ p W d₀ hT
  left_inv := ⟨(ContinuousMap.Homotopy.mk
      ⟨fun z => fibTrivH p W d₀ hT (z.2, z.1),
        (fibTrivH p W d₀ hT).continuous.comp (by fun_prop)⟩
      (fun x => fibTrivH_zero p W d₀ hT x)
      (fun x => fibTrivH_one p W d₀ hT x)).symm⟩
  right_inv := ⟨(ContinuousMap.Homotopy.mk
      ⟨fun z => fibTrivK p W d₀ hT (z.2, z.1),
        (fibTrivK p W d₀ hT).continuous.comp (by fun_prop)⟩
      (fun x => fibTrivK_zero p W d₀ hT x)
      (fun x => fibTrivK_one p W d₀ hT x)).symm⟩

/-- **A contraction of the base of a product makes the second projection a homotopy equivalence**:
if `c` contracts `W` to the point `w₀`, then `W × F → F` is a homotopy equivalence. -/
def prodSndHomotopyEquiv (F : Type) [TopologicalSpace F] (W : Type) [TopologicalSpace W]
    (w₀ : W) (c : C(W × unitInterval, W)) (hc0 : ∀ w, c (w, 0) = w)
    (hc1 : ∀ w, c (w, 1) = w₀) : ContinuousMap.HomotopyEquiv (W × F) F where
  toFun := ContinuousMap.snd
  invFun := ContinuousMap.prodMk (ContinuousMap.const F w₀) (ContinuousMap.id F)
  left_inv := ⟨(ContinuousMap.Homotopy.mk
      ⟨fun z => (c (z.2.1, z.1), z.2.2), by fun_prop⟩
      (fun x => by simp [hc0])
      (fun x => by simp [hc1])).symm⟩
  right_inv := by
    have h : ContinuousMap.snd.comp (ContinuousMap.prodMk (ContinuousMap.const F w₀)
        (ContinuousMap.id F)) = ContinuousMap.id F := by
      ext a
      rfl
    rw [h]

/-- **Restriction to the fibre is an isomorphism in cohomology** when the fibration is fibrewise
trivial over a contractible `W`. -/
theorem nonempty_singularCohomology_iso_fibreTriv (p : C(E, B)) (W : Set B) (d₀ : ↥W)
    (hT : FibrewiseTrivial p W d₀) (w₀ : ↥W) (c : C(↥W × unitInterval, ↥W))
    (hc0 : ∀ w, c (w, 0) = w) (hc1 : ∀ w, c (w, 1) = w₀) (n : ℕ) :
    Nonempty (Work.Cohomology.singularCohomology ℤ n (TopCat.of ↥(p ⁻¹' W)) ≅
      Work.Cohomology.singularCohomology ℤ n (TopCat.of ↥(p ⁻¹' {d₀.1}))) := by
  obtain ⟨e₁⟩ := Work.Cohomology.cohomologyIso_of_homotopyEquiv (fibTrivHomotopyEquiv p W d₀ hT) n
  obtain ⟨e₂⟩ := Work.Cohomology.cohomologyIso_of_homotopyEquiv
    (prodSndHomotopyEquiv ↥(p ⁻¹' {d₀.1}) ↥W w₀ c hc0 hc1) n
  exact ⟨e₁ ≪≫ e₂⟩

end

end Work.StemsB
