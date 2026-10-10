import Mathlib.FieldTheory.Galois.Basic
import Submission.NK.LocalArtin.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace NK.LocalArtin.Reduction

open scoped Classical

/-- **The reciprocity map from the kernel condition and the norm index theorem.**

Let `F` be a field with Galois extension `F'`.  Suppose

* `K : KernelCondition F F'` — there is a single homomorphism `K.artin : Fˣ →* Gal(F^{ab}/F)` whose
  restriction to every finite abelian Galois level `L ≤ F^{ab}` has kernel exactly the norm group
  `N_{L/F} Lˣ` (no surjectivity demanded), and
* `hN : NormIndex F F'` — at every such level the norm group has index `[L : F]` in `Fˣ`.

Then `K.artin` is a `ReciprocityMap`: the level maps `Fˣ → Gal(L/F)` are automatically *surjective*,
because they factor through an injection `Fˣ ⧸ N_{L/F} Lˣ ↪ Gal(L/F)` between finite groups of the
same cardinality `[L : F]` (`Nat.card (Gal(L/F)) = [L : F]` is `IsGalois.card_aut_eq_finrank`).

This isolates the two halves of the reciprocity law — "the Artin symbol has the right kernel" and
"the norm group has the right index" — and proves that the surjectivity of the Artin map, a
statement about every element of every finite Galois group being an Artin symbol, is *free* from
them. -/
theorem kernelCondition_toReciprocityMap {F : Type*} {F' : Type*} [Field F] [Field F']
    [Algebra F F'] [IsGalois F F'] (K : NK.LocalArtin.KernelCondition F F')
    (hN : NK.LocalArtin.NormIndex F F') : Nonempty (NK.LocalArtin.ReciprocityMap F F') := by
  refine ⟨{ artin := K.artin, isLevelIso := ?_ }⟩
  intro L hfd hnorm hcomm
  haveI : FiniteDimensional F L := hfd
  haveI : Normal F L := hnorm
  -- The two pieces of data at the level `L`: the kernel is the norm group (`K`), and the
  -- norm group has index `[L : F]` (`hN`).
  refine ⟨?_, K.ker_level L hcomm⟩
  -- Write `f` for the Artin map at the level `L`, `Fˣ →* Gal(L/F)`.
  set f : Fˣ →* (↥L ≃ₐ[F] ↥L) := (NK.LocalArtin.levelRestrict L).comp K.artin
  have hker : f.ker = NK.LocalArtin.normGroup F ↥L := K.ker_level L hcomm
  -- Counting: the image of `f` and the whole Galois group have the same cardinality, because
  -- `Nat.card (f.range) = f.ker.index = (normGroup F L).index = [L : F] = Nat.card Gal(L/F)`.
  have hcard : Nat.card f.range = Nat.card (↥L ≃ₐ[F] ↥L) := by
    rw [← Subgroup.index_ker f, hker, hN L, IsGalois.card_aut_eq_finrank F ↥L]
  have hne : Nat.card (↥L ≃ₐ[F] ↥L) ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
  have hne' : Nat.card f.range ≠ 0 := by rw [hcard]; exact hne
  -- The subgroup index of the image is therefore `1`, i.e. `f` is surjective.
  have hmul : Nat.card f.range * f.range.index = Nat.card f.range := by
    rw [Subgroup.card_mul_index f.range, hcard]
  have hidx : f.range.index = 1 :=
    Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne') (by simpa using hmul)
  rw [← MonoidHom.range_eq_top]
  exact Subgroup.index_eq_one.mp hidx

end NK.LocalArtin.Reduction
