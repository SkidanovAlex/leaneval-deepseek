import Mathlib
import Submission.NK.HassePrinciple.MuLevelMap
import Submission.NK.HassePrinciple.KummerLevel
import Submission.NK.HassePrinciple.kummerLevel_naturality
import Submission.NK.HassePrinciple.UnitsLevel
import Submission.NK.NUV2.ABHN.unitsLevelMap_injective

set_option linter.unusedVariables false

namespace NK.NUV2.LC.RouteB

open CategoryTheory

/-- **The `μ_p` transition morphism does not kill a class whose Kummer image is nonzero.**

Let `h : L ≤ L'` be an inclusion of finite Galois levels and let `a ∈ H²(LevelGroup V L, μ_p(L))`
be a class whose image under the Kummer morphism `kummerLevel p V L` is nonzero.  If

* `unitsLevelMap V h : H²(LevelGroup V L, Lˣ) → H²(LevelGroup V L', L'ˣ)` is injective, and
* `kummerLevel p V L' : H²(LevelGroup V L', μ_p(L')) → H²(LevelGroup V L', L'ˣ)` is injective,

then `a` is not killed by the transition morphism `muLevelMap p V h` of the `μ_p` level system.

The proof is the naturality square of the Kummer morphism
(`NK.HassePrinciple.kummerLevel_naturality`):

`kummerLevel p V L ≫ unitsLevelMap V h = muLevelMap p V h ≫ kummerLevel p V L'`.

Indeed, if `muLevelMap p V h a = 0`, then chasing `a` around the square gives
`unitsLevelMap V h (kummerLevel p V L a) = kummerLevel p V L' 0 = 0 = unitsLevelMap V h 0`,
whence `kummerLevel p V L a = 0` by injectivity of `unitsLevelMap V h`, contradicting `ha`. -/
theorem muLevelMap_ne_zero_of_kummerLevel_ne_zero
    (p : ℕ) {K K' : Type} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    (V : Subgroup Gal(K'/K)) {L L' : FiniteGaloisIntermediateField K K'} (h : L ≤ L')
    (hkl : Function.Injective (NK.HassePrinciple.kummerLevel p V L'))
    (hunits : Function.Injective (NK.HassePrinciple.unitsLevelMap V h))
    (a : NK.HassePrinciple.MuLevelH2 p V L)
    (ha : (NK.HassePrinciple.kummerLevel p V L) a ≠ 0) :
    (NK.HassePrinciple.muLevelMap p V h) a ≠ 0 := by
  intro hzero
  apply ha
  -- Injectivity of the units-level transition map: it suffices to compare the two images of `a`.
  refine hunits ?_
  -- The naturality square of the Kummer morphism, evaluated at `a`.
  have hnat := NK.HassePrinciple.kummerLevel_naturality (K := K) (K' := K') p V h
  have h1 : (NK.HassePrinciple.unitsLevelMap V h) ((NK.HassePrinciple.kummerLevel p V L) a)
      = (NK.HassePrinciple.kummerLevel p V L') ((NK.HassePrinciple.muLevelMap p V h) a) := by
    have := congrArg (fun f => f a) hnat
    rwa [ModuleCat.comp_apply, ModuleCat.comp_apply] at this
  rw [h1, hzero, map_zero]
  exact (map_zero _).symm

end NK.NUV2.LC.RouteB
