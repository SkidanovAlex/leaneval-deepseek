import Mathlib
import Submission.Work.MotV5.Defs
import Submission.Work.MotV.Defs
import Submission.Work.MotK.KleinData
import Submission.Work.MotV5.as_minpoly_four
import Submission.Work.MotV5.kleinCoord_not_all_one

/-!
# `bridge_as`: the Artin–Schreier bridge of the characteristic-5 branch

Target of this file: `Work.MotV5.bridge_as` (node **P6** / **BR_AS** of the design
`Submission/Work/MotV5/_stmt.lean`), the characteristic-`5` companion of
`Work.MotV.bridge`:

for good Klein data `D` over a field `𝕜` of characteristic `5`, a smooth Klein point
(`a² - ab - b² ≠ 0`) and an Artin–Schreier class `g ∈ K = 𝕜(t)`, the AS twist field
`F = asTwistField D g` satisfies

  `ASUnramified 𝕜 F X g`,

i.e. at every valuation of `F` trivial on `𝕜` at which the parameter `t` has a pole, the class
`g` is congruent to a value `u⁵ - u` of the Artin–Schreier map modulo the valuation ring.

## The proof

Let `W = asRoot g ∈ Kb 𝕜 ⊆ Om D = K̄(E)`, so that `W⁵ - W = g`, and let
`y_j = asTwCoord D g j ∈ F` be the twisted Klein coordinates (`F = adjoin K (range asTwCoord)`,
so each `y_j` lies in `F` by construction).

1. **A degree-`≤ 4` relation for `W` over `F`.**  The interpolation identity `hid` at `i = 0`
   reads `asCoord W (asTwCoord D g) 0 = κ₀/κ₀ = 1`, i.e.

   `Q(W) = 0`,  `Q = ∑_{j<5} y_j Z^j - 1 ∈ F[Z]`,  `Q.natDegree ≤ 4`.

   `Q ≠ 0`: otherwise `∑_j C(y_j) Z^j = 1` in `F[Z]`, and evaluating at `W + i` gives
   `asCoord W (asTwCoord D g) i = 1` for *every* `i`, i.e. `κ_i/κ₀ = 1` for every `i`; then
   `kleinP a b κ 0 = κ₀²(a² - ab - b²) = 0` contradicts `hsm` — this is
   `Work.MotV5.kleinCoord_not_all_one`.

2. **The Artin–Schreier dichotomy.**  `Work.MotV5.as_minpoly_four` (`as_minpoly_four.lean`):
   if `w⁵ - w = c` and a *nonzero* polynomial of degree `≤ 4` over the base kills `w`, then
   `w` is a base-field element.  Its proof is the classical one: the minimal polynomial of `w`
   divides `X⁵ - X - C c` and has degree `≤ 4`; if `c` were not of the form `b⁵ - b` then
   `X⁵ - X - C c` would be irreducible (`Work.TorsorExistence.ArtinSchreier.irreducible_X_pow_five_sub_X_sub_C`),
   forcing the minimal polynomial to have degree `5`.  So `c = b⁵ - b`, and then `w - b` is a
   root of `X⁵ - X = ∏_{i<5}(X - i)`, i.e. one of `0, 1, 2, 3, 4`.

3. Applying (2) with `w = W`, `c = algebraMap (RatFunc 𝕜) F g` gives `W ∈ F`, and then `u = W`
   satisfies `u⁵ - u = g` *exactly*, so `ASUnramified` is immediate: the element in question is
   `0`, whose valuation is `0 ≤ 1`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.MotV5

open Polynomial

theorem bridge_as (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : D.Good) (hNC : Work.MotV5.KleinData.Nonconstant D)
    (hsm : D.a ^ 2 - D.a * D.b - D.b ^ 2 ≠ 0) (g : RatFunc 𝕜)
    (hid : ∀ i : Fin 5,
      Work.MotV.asCoord (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (Work.MotV5.asRoot g))
          (Work.MotV5.asTwCoord D g) i
        = Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i / Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0) :
    Work.MotV5.ASUnramified 𝕜 ↥(Work.MotV5.asTwistField D g)
      (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistField D g) RatFunc.X)
      (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistField D g) g) := by
  let F : IntermediateField (RatFunc 𝕜) (Work.MotV.Om D) := Work.MotV5.asTwistField D g
  haveI : CharP ↥F 5 :=
    charP_of_injective_algebraMap (RingHom.injective (algebraMap (RatFunc 𝕜) ↥F)) 5
  let W : Work.MotV.Om D := algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (Work.MotV5.asRoot g)
  -- the twisted Klein coordinates, viewed as elements of the twist field
  let y : Fin 5 → ↥F := fun j => ⟨Work.MotV5.asTwCoord D g j,
      IntermediateField.subset_adjoin _ _ (Set.mem_range_self j)⟩
  -- the degree-`≤ 4` polynomial killing `W`
  let Q : Polynomial ↥F := (∑ j : Fin 5, Polynomial.C (y j) * Polynomial.X ^ (j : ℕ))
    - Polynomial.C 1
  -- `W⁵ - W = c` in the twist field
  have hwas : W ^ 5 - W = algebraMap (RatFunc 𝕜) (Work.MotV.Om D) g := by
    simp only [W, ← map_pow, ← map_sub]
    rw [Work.MotV5.asRoot_spec]
    exact IsScalarTower.algebraMap_apply (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (Work.MotV.Om D) g
  have hw : W ^ 5 - W = algebraMap ↥F (Work.MotV.Om D) (algebraMap (RatFunc 𝕜) ↥F g) := by
    rw [hwas, ← IsScalarTower.algebraMap_apply (RatFunc 𝕜) ↥F (Work.MotV.Om D)]
  -- the interpolation identity at `i = 0` reads `Q(W) = 0`
  have hQw : Polynomial.aeval W Q = 0 := by
    simp only [Q, map_sub, map_sum, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
    have h1 : (∑ x : Fin 5, (algebraMap (↥F) (Work.MotV.Om D)) (y x) * W ^ (x:ℕ))
        = Work.MotV.asCoord W (Work.MotV5.asTwCoord D g) 0 := by
      simp [Work.MotV.asCoord, y]
    rw [h1, hid 0, div_self (hD.coord0_ne (Work.MotV.Kb 𝕜)), map_one, sub_self]
  have hQdeg : Q.natDegree ≤ 4 := by
    simp only [Q]
    rw [Fin.sum_univ_five]
    compute_degree
  -- `Q ≠ 0`, since `Q = 0` would force every Klein ratio to be `1`
  have hQne : Q ≠ 0 := by
    intro h0
    apply kleinCoord_not_all_one 𝕜 D hD hsm
    intro i
    rw [← hid i]
    have hR : (∑ j : Fin 5, Polynomial.C (y j) * Polynomial.X ^ (j:ℕ)) = 1 := by
      have h : (∑ j : Fin 5, Polynomial.C (y j) * Polynomial.X ^ (j:ℕ)) - Polynomial.C 1 = 0 :=
        h0
      have := sub_eq_zero.mp h
      simpa using this
    have haev : Work.MotV.asCoord W (Work.MotV5.asTwCoord D g) i
        = Polynomial.aeval (W + ((i:ℕ) : Work.MotV.Om D))
            (∑ j : Fin 5, Polynomial.C (y j) * Polynomial.X ^ (j:ℕ)) := by
      simp [Work.MotV.asCoord, y, Polynomial.aeval_def]
    rw [haev, hR, map_one]
  -- the Artin–Schreier dichotomy puts `W` inside the twist field
  have hW : W ∈ Work.MotV5.asTwistField D g := by
    obtain ⟨a, ha⟩ := as_minpoly_four W (algebraMap (RatFunc 𝕜) ↥F g) hw Q hQne hQdeg hQw
    rw [← ha]
    exact a.2
  -- finally `u = W` solves `u⁵ - u = g` exactly
  intro v hv hvt
  refine ⟨⟨W, hW⟩, ?_⟩
  have hrel : (algebraMap (RatFunc 𝕜) ↥F g : ↥F) = (⟨W, hW⟩ : ↥F) ^ 5 - ⟨W, hW⟩ := by
    apply Subtype.ext
    show algebraMap (RatFunc 𝕜) (Work.MotV.Om D) g = W ^ 5 - W
    rw [hwas]
  rw [hrel, sub_self, map_zero]
  exact zero_le_one' _

end Work.MotV5
