import Mathlib.NumberTheory.NumberField.Basic
import Submission.Work.SSGRoute.PTDefsOmega
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.E7cOmega

/-- **The stabiliser of a place only depends on the place below.**  For a finite Galois extension
`L / k` and an intermediate field `k ≤ K ≤ L`, two places `w'`, `w''` of `L` lying over the same
place `w` of `K` have stabilisers in `Gal(L/k)` of the same cardinality.

Indeed `Gal(L/K) ⊆ Gal(L/k)` acts transitively on the places of `L` above `w`
(`NK.GlobalCFT.Inclusion.globalCFT_exists_smul_eq_of_liesOver`), so some `τ : Gal(L/K)` maps `w'`
to `w''`; the stabilisers of two points in one orbit are conjugate, hence have the same
cardinality. -/
theorem card_stab_eq_of_liesOver {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional k L] [IsGalois k L]
    (w : NK.GlobalCFT.Place K) (w' w'' : NK.GlobalCFT.Place L)
    (h' : NK.GlobalCFT.Place.LiesOver w' w) (h'' : NK.GlobalCFT.Place.LiesOver w'' w) :
    Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) w')
      = Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) w'') := by
  haveI : FiniteDimensional K L := FiniteDimensional.right k K L
  haveI : IsGalois K L := IsGalois.tower_top_of_isGalois k K L
  -- `Gal(L/K)` is transitive on the places of `L` above `w`.
  obtain ⟨τ, hτ⟩ :=
    NK.GlobalCFT.Inclusion.globalCFT_exists_smul_eq_of_liesOver (K := K) (L := L) h' h''
  -- Regard `τ` as an element of `Gal(L/k)`.
  let τ' : L ≃ₐ[k] L := AlgEquiv.restrictScalars k τ
  have hτ' : τ' • w' = w'' := by
    have hsmul : (AlgEquiv.restrictScalars k τ) • w' = τ • w' := rfl
    rw [hsmul]; exact hτ
  -- Stabilisers of two points in a common orbit have the same cardinality.
  have hb : w'' = τ' • w' := hτ'.symm
  exact Nat.card_congr
    (MulAction.stabilizerEquivStabilizer (G := L ≃ₐ[k] L) (g := τ') hb).toEquiv

end Work.SSGRoute.E7cOmega
