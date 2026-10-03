import Mathlib
import Submission.Work.ORLyndon.nielsenTransfer
import Submission.Work.ORLyndon.lift_eq_self_of_toWord
import Submission.Work.ORLyndon.foxD_shear_lift_of

/-!
# The `x`-shear `z ↦ (z = x ? of x * u₀ : of z)` is an automorphism of the free group

For a generator `x` of the free group `F(α)` and a word `u₀` **not involving** `x`, the endomorphism

`ψ : F(α) →* F(α)`,   `ψ (of x) = of x * u₀`,   `ψ (of z) = of z`  for `z ≠ x`,

is a Nielsen transformation, hence an automorphism of `F(α)`: the analogous shear with `u₀`
replaced by `u₀⁻¹` is a two-sided inverse.  Indeed both maps fix `u₀` (it involves no `x`), so

* `ψ' (ψ (of x)) = ψ' (of x * u₀) = (of x * u₀⁻¹) * u₀ = of x`, and `ψ (ψ' (of x)) = of x` as well;
* on every other generator both composites are the identity by definition.

Consequently the `x`-component of the Fox vector is unchanged by the shear:
`∂(ψ (of q))/∂x = if q = x then 1 else 0`.  This is what allows one to transport the
Lyndon--Cohen Fox vector of a relator along the shear: the shear is an automorphism whose Fox
Jacobian in the letter `x` is the delta at `x`.

## Main results

* `Work.ORLyndon.lift_eq_self_of_relatorLetters` — a free-group endomorphism which fixes the
  generators occurring in `w` fixes `w`;
* `Work.ORLyndon.shear_lift_bijective` — the shear is injective, surjective, and has
  Fox derivative `δ_{q,x}` at `x`.

## Dependencies

The auxiliary facts `Work.ORLyndon.lift_eq_self_of_toWord` (a `FreeGroup.lift` fixing the letters of
a word is the identity on it) and `Work.ORLyndon.foxD_shear_lift_of` (the Fox derivative of the
shear on generators) are proved in separate modules.
-/

namespace Work.ORLyndon

universe u v

/-- **A free-group endomorphism fixing the letters of a word fixes the word.**  If `g` sends every
generator `z ≠ x` to `of z` and `x` is not a letter of `w`, then `FreeGroup.lift g w = w`.

This is the form in which the shear is used below: the shear is the identity on any word avoiding
`x`, and `u₀` avoids `x` by hypothesis. -/
theorem lift_eq_self_of_relatorLetters {α : Type u} [DecidableEq α] {x : α}
    {g : α → FreeGroup α} {w : FreeGroup α}
    (hg : ∀ z : α, z ≠ x → g z = FreeGroup.of z)
    (hw : x ∉ Work.OROneRel.relatorLetters w) : FreeGroup.lift g w = w := by
  -- `relatorLetters w` is `toWord w` for the *classical* decidable equality; `toWord` does not
  -- depend on the instance, so `FreeGroup.toWord w` is contained in it.
  refine lift_eq_self_of_toWord (f := g) fun c hc => hg c.1 fun hcx => hw (hcx ▸ ?_)
  rw [Work.OROneRel.relatorLetters]
  exact ⟨c.2, by
    rw [← Work.ORLyndon.toWord_eq_of_decEq (inferInstance : DecidableEq α) (Classical.decEq α) w]
    exact hc⟩

/-- **The `x`-shear is an automorphism of the free group, with Fox derivative `δ_{q,x}` in the
letter `x`.**  For `x : α` and `u₀ : FreeGroup α` with `x ∉ relatorLetters u₀`, the endomorphism
`of x ↦ of x * u₀`, `of z ↦ of z` (`z ≠ x`) is injective and surjective, and its Fox derivative in
the letter `x` at the image of the generator `q` is `1` if `q = x` and `0` otherwise. -/
theorem shear_lift_bijective {α : Type u} [DecidableEq α] {K : Type v} [Field K]
    (x : α) (u₀ : FreeGroup α) (hx : x ∉ Work.OROneRel.relatorLetters u₀) :
    Function.Injective (FreeGroup.lift (fun z : α => if z = x then FreeGroup.of x * u₀ else FreeGroup.of z))
    ∧ Function.Surjective (FreeGroup.lift (fun z : α => if z = x then FreeGroup.of x * u₀ else FreeGroup.of z))
    ∧ (∀ q : α, Work.ORLyndon.foxD (K := K) x
        ((FreeGroup.lift (fun z : α => if z = x then FreeGroup.of x * u₀ else FreeGroup.of z))
          (FreeGroup.of q)) = if q = x then 1 else 0) := by
  -- The shear and the inverse shear.
  set ψ : FreeGroup α →* FreeGroup α :=
    FreeGroup.lift (fun z : α => if z = x then FreeGroup.of x * u₀ else FreeGroup.of z) with hψ
  set ψ' : FreeGroup α →* FreeGroup α :=
    FreeGroup.lift (fun z : α => if z = x then FreeGroup.of x * u₀⁻¹ else FreeGroup.of z) with hψ'
  -- The two lifts on generators.
  have hψ_of : ∀ z : α, ψ (FreeGroup.of z) =
      if z = x then FreeGroup.of x * u₀ else FreeGroup.of z :=
    fun z => FreeGroup.lift_apply_of
  have hψ'_of : ∀ z : α, ψ' (FreeGroup.of z) =
      if z = x then FreeGroup.of x * u₀⁻¹ else FreeGroup.of z :=
    fun z => FreeGroup.lift_apply_of
  -- Both shears fix `u₀`.
  have hψu : ψ u₀ = u₀ := by
    rw [hψ]
    exact lift_eq_self_of_relatorLetters (x := x) (w := u₀) (fun z hz => if_neg hz) hx
  have hψ'u : ψ' u₀ = u₀ := by
    rw [hψ']
    exact lift_eq_self_of_relatorLetters (x := x) (w := u₀) (fun z hz => if_neg hz) hx
  -- `ψ' ∘ ψ = id` on generators, whence everywhere.
  have hleft : ∀ a : FreeGroup α, ψ' (ψ a) = a := by
    have hfun : (fun z : α => ψ' (ψ (FreeGroup.of z))) = FreeGroup.of := by
      funext z
      rcases eq_or_ne z x with hz | hz
      · have s1 : ψ' (ψ (FreeGroup.of z)) = ψ' (FreeGroup.of x * u₀) := by
          rw [hψ_of z, if_pos hz]
        have s2 : ψ' (FreeGroup.of x * u₀) = ψ' (FreeGroup.of x) * ψ' u₀ := map_mul ψ' _ _
        have s3 : ψ' (FreeGroup.of x) * ψ' u₀ = (FreeGroup.of x * u₀⁻¹) * u₀ := by
          rw [hψ'_of x, if_pos rfl, hψ'u]
        exact s1.trans (s2.trans (s3.trans (by rw [mul_assoc, inv_mul_cancel, mul_one, hz])))
      · rw [hψ_of z, if_neg hz, hψ'_of z, if_neg hz]
    intro a
    have key := FreeGroup.lift_unique (f := fun z : α => ψ' (ψ (FreeGroup.of z))) (ψ'.comp ψ)
      (fun z => rfl) (x := a)
    rw [hfun, FreeGroup.lift_of_apply] at key
    exact key
  -- `ψ ∘ ψ' = id` on generators, whence everywhere.
  have hright : ∀ a : FreeGroup α, ψ (ψ' a) = a := by
    have hfun : (fun z : α => ψ (ψ' (FreeGroup.of z))) = FreeGroup.of := by
      funext z
      rcases eq_or_ne z x with hz | hz
      · have s1 : ψ (ψ' (FreeGroup.of z)) = ψ (FreeGroup.of x * u₀⁻¹) := by
          rw [hψ'_of z, if_pos hz]
        have s2 : ψ (FreeGroup.of x * u₀⁻¹) = ψ (FreeGroup.of x) * ψ u₀⁻¹ := map_mul ψ _ _
        have s3 : ψ (FreeGroup.of x) * ψ u₀⁻¹ = (FreeGroup.of x * u₀) * u₀⁻¹ := by
          rw [hψ_of x, if_pos rfl, map_inv, hψu]
        exact s1.trans (s2.trans (s3.trans (by rw [mul_assoc, mul_inv_cancel, mul_one, hz])))
      · rw [hψ'_of z, if_neg hz, hψ_of z, if_neg hz]
    intro a
    have key := FreeGroup.lift_unique (f := fun z : α => ψ (ψ' (FreeGroup.of z))) (ψ.comp ψ')
      (fun z => rfl) (x := a)
    rw [hfun, FreeGroup.lift_of_apply] at key
    exact key
  refine ⟨?_, ?_, ?_⟩
  · intro a b hab
    rw [← hleft a, ← hleft b, hab]
  · intro b
    exact ⟨ψ' b, hright b⟩
  · intro q
    rw [hψ]
    exact foxD_shear_lift_of x u₀ hx q

end Work.ORLyndon
