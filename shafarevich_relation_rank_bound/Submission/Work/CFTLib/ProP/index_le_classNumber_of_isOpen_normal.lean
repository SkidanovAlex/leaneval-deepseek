import Mathlib
import Submission.Work.CFTLib.ProP.maxUnramifiedAux

namespace Work.CFTLib.ProP

/-!
# The index of an open normal subgroup of `Gal(F^{un,p}/F)` with abelian quotient

Let `F` be a number field, `p` a prime and `G = Gal(F^{un,p}/F)` the Galois group of the maximal
everywhere-unramified pro-`p` extension of `F`.  For an open normal subgroup `N ≤ G` whose
quotient `G ⧸ N` is **abelian**, the index `[G : N]` is bounded by the class number `h_F`.

Indeed, `N` being open and normal corresponds, under the infinite Galois correspondence
(`Work.CFTLib.ProP.quotient_fixedField`), to the finite Galois subextension `K = N^†` of
`F^{un,p}/F`, with `G ⧸ N ≃* Gal(K/F)`.  The hypothesis that `G ⧸ N` is abelian therefore says
that `K/F` is an abelian extension; by `Work.CFTLib.ProP.isUnramified_isPGroup_of_le_max` it is
everywhere unramified; and `CFTLib.UnramifiedAbelianDegreeLe` (`hab`) gives

`[K : F] ≤ Nat.card (ClassGroup (𝓞 F))`.

Since `N.index = Nat.card (G ⧸ N) = Nat.card (Gal(K/F)) = [K : F]`
(`Subgroup.index`, `Nat.card_congr`, `IsGalois.card_aut_eq_finrank`), the claim follows.
-/

open NumberField

theorem index_le_classNumber_of_isOpen_normal (F : Type) [Field F] [NumberField F] (p : ℕ)
    [Fact (Nat.Prime p)] (hab : CFTLib.UnramifiedAbelianDegreeLe)
    (N : Subgroup (Work.CFTLib.ProP.GG F p)) [N.Normal]
    (hopen : IsOpen (N : Set (Work.CFTLib.ProP.GG F p)))
    (hcomm : ∀ a b : (Work.CFTLib.ProP.GG F p) ⧸ N, a * b = b * a) :
    N.index ≤ Nat.card (ClassGroup (NumberField.RingOfIntegers F)) := by
  -- `F^{un,p}/F` is Galois.
  haveI hgalE : IsGalois F ↥(E F p) := isGalois_maximalUnramifiedProPF F p
  -- The fixed field `K` of `N` is a finite Galois subextension of `F^{un,p}/F`.
  have hfd : FiniteDimensional F ↥(IntermediateField.fixedField N) :=
    fixedField_finiteDimensional (F := F) (p := p) hgalE hopen
  have hgalK : IsGalois F ↥(IntermediateField.fixedField N) :=
    fixedField_isGalois (F := F) (p := p) hgalE (inferInstance : N.Normal) hopen
  haveI := hfd
  haveI := hgalK
  haveI hnfK : NumberField ↥(IntermediateField.fixedField N) :=
    NumberField.of_module_finite F _
  -- The Galois correspondence identifies `G ⧸ N` with `Gal(K/F)`.
  obtain ⟨e⟩ := quotient_fixedField (F := F) (p := p) hgalE (inferInstance : N.Normal) hopen
  -- `K/F` is abelian, transported along `e`.
  have hcommK :
      ∀ a b : ↥(IntermediateField.fixedField N) ≃ₐ[F] ↥(IntermediateField.fixedField N),
        a * b = b * a := by
    intro a b
    have h := hcomm (e.symm a) (e.symm b)
    calc a * b = e (e.symm a) * e (e.symm b) := by simp
      _ = e (e.symm a * e.symm b) := (map_mul e _ _).symm
      _ = e (e.symm b * e.symm a) := by rw [h]
      _ = e (e.symm b) * e (e.symm a) := map_mul e _ _
      _ = b * a := by simp
  -- `K/F` is everywhere unramified.
  obtain ⟨hunr, -⟩ := isUnramified_isPGroup_of_le_max F p (IntermediateField.fixedField N)
  -- The index is the degree `[K : F]`.
  have hidx : N.index =
      Nat.card (↥(IntermediateField.fixedField N) ≃ₐ[F] ↥(IntermediateField.fixedField N)) := by
    rw [Subgroup.index]
    exact Nat.card_congr e.toEquiv
  rw [hidx, IsGalois.card_aut_eq_finrank]
  -- Apply the class-field-theoretic input to `K/F`.
  exact hab F ↥(IntermediateField.fixedField N) hcommK hunr

end Work.CFTLib.ProP
