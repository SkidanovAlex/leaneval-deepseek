import Mathlib
import Submission.Work.DSEQ0.eulerCharDefs
import Submission.Work.DSF1.Cech.cechAffineCover_quasiIso
import Submission.Work.DSF1.Cech.CechSetup

/-!
# The affine cover of `Spec Γ(X, W)` pulled back along `IsAffineOpen.fromSpec`

For an affine open `W` of a scheme `X`, the open immersion `hW.fromSpec : Spec Γ(X,W) ⟶ X`
has range `W`, and for a family `U` of opens of `X` with `W ≤ ⨆ U` the family
`V i := hW.fromSpec ⁻¹ᵁ (W ⊓ U i)` consists of affine opens of `Spec Γ(X,W)` covering it,
so that `Work.DSF1.Cech.cechAffineCover_quasiIso` applies to it.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace Work.DSEQ0

open CategoryTheory AlgebraicGeometry Limits Opposite

universe u

variable {X : AlgebraicGeometry.Scheme.{u}} {W : X.Opens}

/-- The open immersion `Spec Γ(X, W) ⟶ X` attached to the affine open `W`. -/
noncomputable abbrev curryFromSpec (hW : AlgebraicGeometry.IsAffineOpen W) :
    AlgebraicGeometry.Spec (CommRingCat.of (X.presheaf.obj (Opposite.op W))) ⟶ X :=
  hW.fromSpec

@[simp]
lemma curryFromSpec_opensRange (hW : AlgebraicGeometry.IsAffineOpen W) :
    (curryFromSpec hW).opensRange = W :=
  hW.opensRange_fromSpec

/-- The pulled-back family on `Spec Γ(X, W)`. -/
noncomputable def curryPullback (hW : AlgebraicGeometry.IsAffineOpen W) {ι : Type u}
    (U : ι → X.Opens) : ι → (AlgebraicGeometry.Spec
      (CommRingCat.of (X.presheaf.obj (Opposite.op W)))).Opens :=
  fun i => hW.fromSpec ⁻¹ᵁ (W ⊓ U i)

lemma curryPullback_apply (hW : AlgebraicGeometry.IsAffineOpen W) {ι : Type u}
    (U : ι → X.Opens) (i : ι) :
    curryPullback hW U i = hW.fromSpec ⁻¹ᵁ (W ⊓ U i) := rfl

/-- The members of the pulled-back family are affine when the `W ⊓ U i` are. -/
theorem isAffineOpen_curryPullback (hW : AlgebraicGeometry.IsAffineOpen W) {ι : Type u}
    (U : ι → X.Opens) (hinf : ∀ (n : ℕ) (y : Fin (n + 1) → ι),
      AlgebraicGeometry.IsAffineOpen (W ⊓ ⨅ a, U (y a))) (i : ι) :
    AlgebraicGeometry.IsAffineOpen (curryPullback hW U i) := by
  have h0 : AlgebraicGeometry.IsAffineOpen (W ⊓ U i) := by
    simpa using hinf 0 (fun _ : Fin 1 => i)
  have hmem : W ⊓ U i ≤ (hW.fromSpec).opensRange := by
    rw [hW.opensRange_fromSpec]; exact inf_le_left
  exact h0.preimage_of_isOpenImmersion hW.fromSpec hmem

/-- The pulled-back family covers `Spec Γ(X, W)`. -/
theorem iSup_curryPullback (hW : AlgebraicGeometry.IsAffineOpen W) {ι : Type u}
    (U : ι → X.Opens) (hle : W ≤ ⨆ i, U i) :
    sSup (Set.range (curryPullback hW U)) = ⊤ := by
  have hsup : (⨆ i, curryPullback hW U i) = ⊤ := by
    refine le_antisymm le_top ?_
    intro x _
    have hxW : hW.fromSpec x ∈ W :=
      Set.mem_of_mem_of_subset (Set.mem_range_self (f := hW.fromSpec) x)
        (le_of_eq hW.range_fromSpec)
    obtain ⟨i, hi⟩ : ∃ i, hW.fromSpec x ∈ U i :=
      TopologicalSpace.Opens.mem_iSup.mp (hle hxW)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, ⟨hxW, hi⟩⟩
  rw [sSup_range]
  exact hsup

end Work.DSEQ0
