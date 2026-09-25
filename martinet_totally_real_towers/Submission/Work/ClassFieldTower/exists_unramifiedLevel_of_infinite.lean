import Mathlib
import Submission.Work.ClassFieldTower.Defs

namespace Work.ClassFieldTower

open scoped NumberField

set_option linter.style.haveILetI false

/-- **Every infinite unramified pro-`p` tower has finite levels of arbitrarily large degree
with the same root discriminant.**

If the maximal unramified pro-`p` extension `M = F_∅` of a number field `F` has infinite
Galois group `G_∅ = Gal(F_∅/F)`, then for every bound `N` there is a finite Galois
subextension `L/F` of `F_∅` with

* `[L : F] ≥ N`,
* trivial relative different `𝒟_{L/F} = 1` (so `L/F` is unramified everywhere, in
  particular at the infinite places), and
* `rootDiscr L = rootDiscr F`.

The last two are the defining features of a *tower* of unramified extensions: a level with
big degree and unchanged root discriminant.  The level is produced by the
infinite-Galois-group lemma `Commons.FieldTheory.Galois.exists_finite_galois_finrank_ge_of_infinite_gal`
(applied to the normal closure of a finite subextension of large degree), unramifiedness
is the field `MaximalUnramifiedProP.unramified` of the universal object, and invariance of
the root discriminant is `Commons.NumberTheory.NumberField.rootDiscr_eq_of_different_eq_top`. -/
theorem exists_unramifiedLevel_of_infinite {F : Type} [Field F] [NumberField F] {p : ℕ}
    [Fact p.Prime] (M : MaximalUnramifiedProP.{0} F p) (hinf : Infinite (galoisGroup M)) (N : ℕ) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra F L) (_ : FiniteDimensional F L)
      (_ : IsGalois F L),
      N ≤ Module.finrank F L ∧
      differentIdeal (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers L) = ⊤ ∧
      NumberField.rootDiscr L = NumberField.rootDiscr F := by
  obtain ⟨L, hfd, hgal, hN⟩ :=
    Commons.FieldTheory.Galois.exists_finite_galois_finrank_ge_of_infinite_gal
      (F := F) (K := M.K) hinf N
  haveI : FiniteDimensional F ↥L := hfd
  haveI : IsGalois F ↥L := hgal
  haveI : NumberField ↥L := NumberField.of_module_finite F ↥L
  have hunr : differentIdeal (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers ↥L) = ⊤ :=
    M.unramified L hfd hgal
  exact ⟨↥L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    hN, hunr,
    Commons.NumberTheory.NumberField.rootDiscr_eq_of_different_eq_top hunr⟩

end Work.ClassFieldTower
