import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Submission.Work.SSGRoute.ZDataTwo.FiniteReciprocity
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZDataTwo

/-- **The complex-place half of the archimedean sign conditions.**  The containment
`Work.SSGRoute.ZDataTwo.isLocalNorm_of_notMem_of_finite_unramified` (and with it the product formula
restricted to `T`, `badSet_subset_and_even`) carries the local-norm condition at the archimedean
places outside `T` as an explicit hypothesis `hinf`.  At a *complex* place that hypothesis is free:
there `K_w = ℂ = L_{w'}`, so the local extension is trivial and its norm map is the identity — every
element of `Kˣ` is a local norm.  Discharging `hinf` at the complex places reduces the archimedean
side of the `p = 2` reciprocity clause to the *real* places, where the condition is the sign condition
supplied by `Work.SSGRoute.ZDataTwo.archPair_two_kummer_eq_zero_iff`.

(The ingredients are already in the workspace and in the import closure: the lift
`NK.CFTLib.IdeleHasse.exists_liesOver_infinite`, complexity upstairs
`InfinitePlace.LiesOver.isComplex_of_isComplex_under`, and
`NK.NUV2.ArtinBridge.localNormInfinite_range_eq_top_of_complex_complex` — the same three moves as the
`inl`/complex branch of `Work.HilbertSymbolGeneral.isLocalNorm_iff_localNormSubgroup`.) -/
theorem isLocalNorm_ofInfinite_of_isComplex
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (w : NumberField.InfinitePlace K) (hw : NumberField.InfinitePlace.IsComplex w) (x : Kˣ) :
    NK.NUV2.LC.IsLocalNorm K L x (NK.GlobalCFT.Place.ofInfinite w) := by
  -- Lift the complex place `w` of `K` to a place `w'` of `L`.
  obtain ⟨w', hw'⟩ := NK.CFTLib.IdeleHasse.exists_liesOver_infinite (K := K) (L := L) w
  haveI : w'.LiesOver w := hw'
  -- It is again complex, and at a complex place the local norm on units is surjective.
  have htop : (NK.GlobalCFT.Place.localNormInfinite (K := K) (L := L) w' w).range = ⊤ :=
    NK.NUV2.ArtinBridge.localNormInfinite_range_eq_top_of_complex_complex hw
      (NumberField.InfinitePlace.LiesOver.isComplex_of_isComplex_under w' hw)
  -- So every local unit is a local norm, in particular the image of `x`.
  exact ⟨w', hw', htop ▸ Subgroup.mem_top _⟩

end Work.SSGRoute.ZDataTwo
