import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Unramified.nonempty_reciprocityLaw_of_symbolTower
import Submission.NK.LocalReciprocityLubinTate.Unramified.existenceTheorem_of_symbolTower
import Submission.NK.LocalCFT.Reduction.nonempty_artinReciprocity_of_reciprocityLaw

/-!
# The boundary theorem for a general nonarchimedean local field, from a symbol tower

The chapter constructs the canonical Lubin–Tate symbol tower for `F = 𝔭.adicCompletion K`
(`NK.LocalReciprocityLubinTate.Unramified.nonempty_symbolTower_adicCompletion`), because the
unramified levels of the tower come from the number-field theory of the workspace's commons.  This
file records the *general* `F` form of the boundary theorem: given a symbol tower over any
nonarchimedean local field `F` (with a residue cardinality and a uniformiser `π`), Hasse's norm
correspondence, the norm-compatibility of the Artin symbol, the covering of `F^{ab}` by the two-
parameter family, the unboundedness in divisibility of the exponents `a`, and the cofinality of the
higher unit filtration, the canonical local reciprocity datum exists.

Every hypothesis except the three *classical* ones (`NormCorrespondence`, `NormInKernel`, and the form
of the structure instance) is a theorem of this chapter: the reciprocity law
(`nonempty_reciprocityLaw_of_symbolTower`), the existence theorem
(`existenceTheorem_of_symbolTower`) and the norm index theorem (`NK.LocalArtin.NormIndex`, an extra
hypothesis only because for a general `F` it is the classical Herbrand-quotient computation).

## Main result

* `NK.LocalReciprocityLubinTate.artinReciprocity_of_symbolTower`.
-/

open scoped Classical

namespace NK.LocalReciprocityLubinTate

universe u v

/-- **The local Artin reciprocity datum for a general nonarchimedean local field**, from a
Lubin–Tate symbol tower and the two classical residues. -/
theorem artinReciprocity_of_symbolTower {F : Type u} {F' : Type v} [Field F] [Field F']
    [Algebra F F'] [IsGalois F F'] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {π : Fˣ} {a : ℕ → ℕ}
    (T : NK.LocalReciprocityLubinTate.LubinTateSymbolTower F F' π a
      (NK.LocalReciprocityLubinTate.higherUnits F) (NK.LocalReciprocityLubinTate.residueCard F))
    (hcorr : NK.LocalReciprocityLubinTate.NormCorrespondence F F')
    (hidx : NK.LocalArtin.NormIndex F F')
    (hnk : NK.LocalReciprocityLubinTate.NormInKernel F F' π a
      (NK.LocalReciprocityLubinTate.residueCard F) T)
    (hcover : ∀ (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
      [FiniteDimensional F L] [Normal F L]
      (_ : ∀ σ τ : ↥L ≃ₐ[F] ↥L, σ * τ = τ * σ), ∃ m n : ℕ, L ≤ T.level m n)
    (hgrow : ∀ d : ℕ, d ≠ 0 → ∃ m : ℕ, d ∣ a m)
    (hcof : ∀ M : Subgroup Fˣ, M.FiniteIndex → ∃ n : ℕ, higherUnits F n ≤ M) :
    Nonempty (NK.LocalCFT.ArtinReciprocity F F') := by
  classical
  obtain ⟨hlaw⟩ :=
    NK.LocalReciprocityLubinTate.Unramified.nonempty_reciprocityLaw_of_symbolTower
      T hcorr hidx hnk hcover
  exact NK.LocalCFT.Reduction.nonempty_artinReciprocity_of_reciprocityLaw hlaw
    (NK.LocalReciprocityLubinTate.Unramified.existenceTheorem_of_symbolTower T.toLubinTateTowerGen
      hgrow hcof)

end NK.LocalReciprocityLubinTate
