import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Unramified.adicResidual
import Submission.NK.LocalReciprocityLubinTate.Unramified.exists_level_ge_of_towerCover
import Submission.NK.LocalReciprocityLubinTate.Unramified.nonempty_reciprocityLaw_of_symbolTower
import Submission.NK.LocalReciprocityLubinTate.Unramified.existenceTheorem_of_symbolTower

/-!
# Artin reciprocity from a *covering* form of the norm correspondence

`NK.LocalReciprocityLubinTate.Unramified.nonempty_reciprocityLaw_of_symbolTower` produces the
compatible reciprocity law `NK.LocalCFT.ReciprocityLaw F F'` from a Lubin–Tate symbol tower,
the norm index theorem, the annihilation of norms (`NormInKernel`), and the *covering* hypothesis
that every finite abelian level of `F^{ab}` is contained in a level of the tower.  It carries the
norm-subgroup correspondence `NormCorrespondence F F'` as an extra hypothesis, but — as its own
docstring records — does **not** use it: the level isomorphisms are pinned down by counting
(`NormIndex`), by the annihilation of norms, and by the covering hypothesis.

This file removes that unused hypothesis, and derives the boundary theorem in the form in which the
covering hypothesis is stated *directly* as a statement about norm groups: if the norm group of a
tower level is contained in the norm group of a finite abelian level `L`, then `L` is contained in
that tower level.  This is the "Normensatz" restricted to the tower levels, and it is exactly the
form in which the caller of the local theory supplies it.

## Main results

* `NK.LocalReciprocityLubinTate.Unramified.nonempty_reciprocityLaw_of_symbolTower_noNormCorrespondence`;
* `NK.LocalReciprocityLubinTate.Unramified.artinReciprocity_adicCompletion_of_towerCover`.
-/

open scoped Classical

namespace NK.LocalReciprocityLubinTate.Unramified

universe u v

/-- **The reciprocity law from a Lubin–Tate symbol tower, with the unused norm-correspondence
hypothesis dropped.**

Same statement as `NK.LocalReciprocityLubinTate.Unramified.nonempty_reciprocityLaw_of_symbolTower`
with the hypothesis `NormCorrespondence F F'` removed: the covering hypothesis alone turns the level
symbols into a compatible family of level isomorphisms `Fˣ ⧸ N_{L/F} Lˣ ≃* Gal(L/F)`. -/
theorem nonempty_reciprocityLaw_of_symbolTower_noNormCorrespondence
    {F : Type u} {F' : Type v} [Field F] [Field F'] [Algebra F F'] [IsGalois F F']
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {π : Fˣ} {a : ℕ → ℕ}
    (T : NK.LocalReciprocityLubinTate.LubinTateSymbolTower F F' π a
      (NK.LocalReciprocityLubinTate.higherUnits F)
      (NK.LocalReciprocityLubinTate.residueCard F))
    (hidx : NK.LocalArtin.NormIndex F F')
    (hnk : NK.LocalReciprocityLubinTate.NormInKernel F F' π a
      (NK.LocalReciprocityLubinTate.residueCard F) T)
    (hcover : ∀ (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
      [FiniteDimensional F L] [Normal F L]
      (_ : ∀ σ τ : ↥L ≃ₐ[F] ↥L, σ * τ = τ * σ), ∃ m n : ℕ, L ≤ T.level m n) :
    Nonempty (NK.LocalCFT.ReciprocityLaw F F') := by
  have hcov : SymbolTower.LevelCovered T := hcover
  exact ⟨{ levelEquiv := fun L _ _ hcomm =>
              SymbolTower.levelEquiv (π := π) (a := a)
                (q := NK.LocalReciprocityLubinTate.residueCard F) T hcov L hcomm hnk hidx
           compat := fun L₁ L₂ _ _ _ _ h₁ h₂ h x =>
              SymbolTower.levelEquiv_compat (π := π) (a := a)
                (q := NK.LocalReciprocityLubinTate.residueCard F) T hcov hnk hidx
                L₁ L₂ h₁ h₂ h x }⟩

/-- **The boundary theorem of the chapter, from the covering form of the norm correspondence.**

Given

* a uniformiser `π` of `F = 𝔭.adicCompletion K`, and
* the *covering* hypothesis: for every finite abelian level `L` of `F^{ab}`, if the norm group of
  the tower level `E_{m,n}` is contained in the norm group of `L`, then `L ≤ E_{m,n}`
  (the "Normensatz" restricted to the tower levels),
* the annihilation of norms by the canonical Artin symbols of the tower (`NormInKernel`),

there is the canonical local Artin reciprocity datum for `F ⊆ SeparableClosure F`.

Everything else is a theorem of this chapter: the Lubin–Tate symbol tower of the uniformiser
(`adicSymbolTower`), the norm index theorem (`NormIndex.normIndex_adicCompletion`), the existence
theorem (`existenceTheorem_of_symbolTower`), and the assembly of the compatible level isomorphisms
into the reciprocity law (`nonempty_reciprocityLaw_of_symbolTower_noNormCorrespondence`), whence
`NK.LocalCFT.Reduction.nonempty_artinReciprocity_of_reciprocityLaw` produces the datum. -/
theorem artinReciprocity_adicCompletion_of_towerCover {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {π : (Q.adicCompletion K)ˣ}
    (hπ : NK.LocalReciprocityLubinTate.IsUniformizer (Q.adicCompletion K) (π : Q.adicCompletion K))
    (hcov : ∀ (m n : ℕ)
      (L : IntermediateField (Q.adicCompletion K)
        (NK.LocalReciprocity.maxAbelianSubext (Q.adicCompletion K)
          (SeparableClosure (Q.adicCompletion K))))
      [FiniteDimensional (Q.adicCompletion K) L] [Normal (Q.adicCompletion K) L],
      NK.LocalReciprocity.normGroup (Q.adicCompletion K)
          ↥((NK.LocalReciprocityLubinTate.adicSymbolTower K Q hπ).level m n) ≤
        NK.LocalReciprocity.normGroup (Q.adicCompletion K) ↥L →
      L ≤ (NK.LocalReciprocityLubinTate.adicSymbolTower K Q hπ).level m n)
    (hnk : NK.LocalReciprocityLubinTate.NormInKernel (Q.adicCompletion K)
      (SeparableClosure (Q.adicCompletion K)) π (fun m : ℕ => Nat.factorial (m + 1))
      (NK.LocalReciprocityLubinTate.residueCard (Q.adicCompletion K))
      (NK.LocalReciprocityLubinTate.adicSymbolTower K Q hπ)) :
    Nonempty (NK.LocalCFT.ArtinReciprocity (Q.adicCompletion K)
      (SeparableClosure (Q.adicCompletion K))) := by
  classical
  -- the tower and the degree sequence of the unramified part
  let T := NK.LocalReciprocityLubinTate.adicSymbolTower K Q hπ
  -- `(m+1)!` is unbounded in divisibility
  have hgrow : ∀ d : ℕ, d ≠ 0 → ∃ m : ℕ, d ∣ Nat.factorial (m + 1) :=
    fun d hd => ⟨d - 1, Nat.dvd_factorial (Nat.pos_of_ne_zero hd) (by omega)⟩
  -- the covering hypothesis in the form used by the reciprocity law
  have hcover : ∀ (L : IntermediateField (Q.adicCompletion K)
        (NK.LocalReciprocity.maxAbelianSubext (Q.adicCompletion K)
          (SeparableClosure (Q.adicCompletion K))))
      [FiniteDimensional (Q.adicCompletion K) L] [Normal (Q.adicCompletion K) L]
      (_ : ∀ σ τ : ↥L ≃ₐ[Q.adicCompletion K] ↥L, σ * τ = τ * σ),
      ∃ m n : ℕ, L ≤ T.level m n := by
    intro L hfd hnorm hcomm
    exact NK.LocalReciprocityLubinTate.Unramified.exists_level_ge_of_towerCover Q hπ
      (a := fun m : ℕ => Nat.factorial (m + 1)) hgrow T.toLubinTateTowerGen
      (fun m n L' _ _ h => hcov m n L' h) L hcomm
  -- the norm index theorem at the completion
  have hidx : NK.LocalArtin.NormIndex (Q.adicCompletion K)
      (SeparableClosure (Q.adicCompletion K)) :=
    NK.LocalReciprocityLubinTate.NormIndex.normIndex_adicCompletion Q
  -- the compatible reciprocity law
  obtain ⟨hlaw⟩ := nonempty_reciprocityLaw_of_symbolTower_noNormCorrespondence
    (π := π) (a := fun m : ℕ => Nat.factorial (m + 1)) T hidx hnk hcover
  -- the existence theorem
  have hex : NK.LocalCFT.ExistenceTheorem (Q.adicCompletion K)
      (SeparableClosure (Q.adicCompletion K)) :=
    existenceTheorem_of_symbolTower (π := π) (a := fun m : ℕ => Nat.factorial (m + 1))
      T.toLubinTateTowerGen hgrow
      (fun M hM => NK.LocalReciprocityLubinTate.Units.higherUnits_cofinal
        (Q.adicCompletion K) M hM)
  exact NK.LocalCFT.Reduction.nonempty_artinReciprocity_of_reciprocityLaw hlaw hex

end NK.LocalReciprocityLubinTate.Unramified
