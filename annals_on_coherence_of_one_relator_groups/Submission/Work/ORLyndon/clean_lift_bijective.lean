import Mathlib
import Submission.Work.ORLyndon.lyndonIndependence_eps_zero
import Submission.Work.ORLyndon.Fox
import Submission.Work.OROneRel.Interface

/-!
# A "clean at `x`" pair of free-group endomorphisms is an automorphism with Fox Jacobian `δ_x`

Let `g g' : α → F(α)` be two maps of the generators, both fixing `x` (`g x = g' x = of x`) and
mutually inverse on the generators different from `x` (`F(g')(g y) = of y` and `F(g)(g' y) = of y`
for `y ≠ x`, where `F(g) = FreeGroup.lift g`).  Then `F(g') ∘ F(g) = id` and `F(g) ∘ F(g') = id`,
because a homomorphism of free groups is determined by its values on the generators; hence `F(g)`
is bijective.

If, in addition, `g y` involves no `x` for every `y ≠ x` (the map is *clean at `x`*), then the
`x`-component of the Fox vector of `F(g) (of q)` is the Kronecker delta `δ_{q,x}`: for `q = x`
this is `∂(of x)/∂x = 1`, and for `q ≠ x` the Fox derivative vanishes on words avoiding `x`
(`Work.ORLyndon.foxD_eq_zero_of_notMem_relatorLetters`).

This is exactly the input needed by `Work.ORLyndon.annAt_singleton_of_clean_lift` (the clean
transfer of the singleton `annAt` statements along a clean automorphism).
-/

namespace Work.ORLyndon

universe u v

theorem clean_lift_bijective {α : Type u} [DecidableEq α] {K : Type v} [Field K] (x : α)
    (g g' : α → FreeGroup α)
    (hgx : g x = FreeGroup.of x) (hg'x : g' x = FreeGroup.of x)
    (hgE : ∀ y : α, y ≠ x → x ∉ Work.OROneRel.relatorLetters (g y))
    (hinv1 : ∀ y : α, y ≠ x → FreeGroup.lift g' (g y) = FreeGroup.of y)
    (hinv2 : ∀ y : α, y ≠ x → FreeGroup.lift g (g' y) = FreeGroup.of y) :
    Function.Injective (FreeGroup.lift g) ∧ Function.Surjective (FreeGroup.lift g) ∧
      (∀ q : α, Work.ORLyndon.foxD (K := K) x ((FreeGroup.lift g) (FreeGroup.of q)) =
        if q = x then 1 else 0) := by
  -- The two composites are the identity on the generators `of z`, `z : α`.
  have hgen1 : ∀ z : α,
      FreeGroup.lift g' (FreeGroup.lift g (FreeGroup.of z)) = FreeGroup.of z := by
    intro z
    rw [FreeGroup.lift_apply_of]
    rcases eq_or_ne z x with hz | hz
    · subst hz
      rw [hgx, FreeGroup.lift_apply_of, hg'x]
    · exact hinv1 z hz
  have hgen2 : ∀ z : α,
      FreeGroup.lift g (FreeGroup.lift g' (FreeGroup.of z)) = FreeGroup.of z := by
    intro z
    rw [FreeGroup.lift_apply_of]
    rcases eq_or_ne z x with hz | hz
    · subst hz
      rw [hg'x, FreeGroup.lift_apply_of, hgx]
    · exact hinv2 z hz
  -- A free-group homomorphism fixing all generators is the identity.
  have hleft : ∀ a : FreeGroup α, FreeGroup.lift g' (FreeGroup.lift g a) = a := by
    intro a
    induction a using FreeGroup.induction_on with
    | one => rw [map_one, map_one]
    | of z => exact hgen1 z
    | inv_of z ih => rw [map_inv, map_inv, ih]
    | mul a b iha ihb => rw [map_mul, map_mul, iha, ihb]
  have hright : ∀ a : FreeGroup α, FreeGroup.lift g (FreeGroup.lift g' a) = a := by
    intro a
    induction a using FreeGroup.induction_on with
    | one => rw [map_one, map_one]
    | of z => exact hgen2 z
    | inv_of z ih => rw [map_inv, map_inv, ih]
    | mul a b iha ihb => rw [map_mul, map_mul, iha, ihb]
  refine ⟨?_, ?_, ?_⟩
  · intro a b hab
    rw [← hleft a, ← hleft b, hab]
  · intro b
    exact ⟨FreeGroup.lift g' b, hright b⟩
  · intro q
    rw [FreeGroup.lift_apply_of]
    rcases eq_or_ne q x with hq | hq
    · subst hq
      rw [hgx, Work.ORLyndon.foxD_of, if_pos rfl]
    · rw [if_neg hq]
      exact Work.ORLyndon.foxD_eq_zero_of_notMem_relatorLetters (K := K) x (g q) (hgE q hq)

end Work.ORLyndon
