import Mathlib
import Submission.Work.SSGRoute.HRecNKImports
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Per-place data for the cyclic level construction

The target `Work.SSGRoute.CycLevel.oddLayerOmega` asks for a cyclic `q`-power level `M/k`
in which *every* finite place of a given finite set `S` has large local degree.  The
mathematical content splits into

* a **per-place** construction, producing for a single finite place `v` a cyclic `q`-power
  level over `k` in which `v` has *full* local degree (`LevelData` below, delegated to
  `Work.SSGRoute.CycLevel.exists_single_place_level`), and
* a **composition** argument: inside the compositum of the per-place levels one cuts out a
  cyclic quotient of order `q ^ e` which is still surjective on every per-place decomposition
  group (`Work.SSGRoute.CycLevel.exists_cyclic_level_of_place_data`).

This file contains only the bundled data type used to state both halves; it proves nothing.
-/

open scoped NumberField

namespace Work.SSGRoute.CycLevel

/-- **Per-place data.** A finite `k`-level `M ⊆ AlgebraicClosure k`, Galois and cyclic over `k`
of `q`-power order `q ^ a` with `q ^ e ∣ q ^ a`, in which every place of `M` above the finite
place `v` has *full* local degree: its stabiliser is all of `Gal(M/k)`.  (In particular the
order of that stabiliser is `Nat.card Gal(M/k) = q ^ a`, hence divisible by `q ^ e`.)

The exact degree is not part of the data: any `q`-power order divisible by `q ^ e` is allowed,
because the composition step cuts the compositum down to a cyclic quotient of order exactly
`q ^ e` on which each per-place decomposition group is still surjective. -/
structure LevelData (k : Type) [Field k] [NumberField k] (q e : ℕ)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k)) where
  /-- the level -/
  M : IntermediateField k (AlgebraicClosure k)
  fd : FiniteDimensional k M
  nf : NumberField M
  gal : IsGalois k M
  /-- `M/k` is cyclic -/
  cyc : IsCyclic (M ≃ₐ[k] M)
  /-- of `q`-power order -/
  qpow : ∃ a : ℕ, Nat.card (M ≃ₐ[k] M) = q ^ a
  /-- the order is divisible by `q ^ e` -/
  dvd : q ^ e ∣ Nat.card (M ≃ₐ[k] M)
  /-- every place above `v` has *full* local degree -/
  fullLocal : ∀ w : NK.GlobalCFT.Place M,
    NK.GlobalCFT.Place.LiesOver w (NK.GlobalCFT.Place.ofFinite v) →
      Nat.card (MulAction.stabilizer (M ≃ₐ[k] M) w) = Nat.card (M ≃ₐ[k] M)

attribute [instance] LevelData.fd LevelData.nf LevelData.gal

end Work.SSGRoute.CycLevel
