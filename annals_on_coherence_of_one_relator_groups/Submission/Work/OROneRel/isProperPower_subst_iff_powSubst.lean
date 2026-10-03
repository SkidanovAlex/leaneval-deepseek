import Mathlib
import Submission.Work.OROneRel.HNNStep
import Submission.Work.OROneRel.psiSubstDefs

/-!
# `subst t x p q` is the Nielsen substitution `t ↦ t ^ p` followed by an automorphism

The Magnus/Putman substitution `subst t x p q` of Case 2 of the Freiheitssatz sends
`t ↦ t ^ p`, `x ↦ x * t ^ (-q)` and fixes every other generator, while the Nielsen substitution
`powSubst t p` sends `t ↦ t ^ p` and fixes everything else.  The two are related by

`subst t x p q = (subst t x 1 q).comp (powSubst t p)`,

i.e. one first substitutes `t ↦ t ^ p` and then applies the automorphism `x ↦ x * t ^ (-q)` of
`F β` (which fixes `t`).  Since being a proper power is a property invariant under bijective
homomorphisms (`f (u ^ k) = (f u) ^ k`, and a left inverse of `f` recovers a root from a root of the
image), this gives

`IsProperPower (subst t x p q T) ↔ IsProperPower (powSubst t p T)`

for every `T : F β`.  Both directions only need the *left inverse* identity
`(subst t x 1 (-q)).comp (subst t x 1 q) = id`.

## Main results

* `ips_subst_comp_powSubst` -- the decomposition of `subst` above;
* `ips_subst_one_leftInverse` -- `subst t x 1 (-q)` is a left inverse of `subst t x 1 q`;
* `isProperPower_subst_iff_powSubst` -- the equivalence of the proper-power property.
-/

namespace Work.OROneRel

/-! ### The values of `subst` on the generators -/

/-- `subst t x p q` sends the generator `t` to `t ^ p`. -/
theorem ips_subst_of_t {β : Type*} (t x : β) (p q : ℤ) :
    subst t x p q (FreeGroup.of t) = FreeGroup.of t ^ p := by
  rw [subst, FreeGroup.lift_apply_of]; simp [substFun]

/-- `subst t x p q` sends the generator `x` to `x * t ^ (-q)` (for `x ≠ t`). -/
theorem ips_subst_of_x {β : Type*} {t x : β} (hxt : x ≠ t) (p q : ℤ) :
    subst t x p q (FreeGroup.of x) = FreeGroup.of x * FreeGroup.of t ^ (-q) := by
  rw [subst, FreeGroup.lift_apply_of]; simp [substFun, hxt]

/-- `subst t x p q` fixes the generators different from `t` and `x`. -/
theorem ips_subst_of_ne {β : Type*} {t x a : β} (hat : a ≠ t) (hax : a ≠ x) (p q : ℤ) :
    subst t x p q (FreeGroup.of a) = FreeGroup.of a := by
  rw [subst, FreeGroup.lift_apply_of]; simp [substFun, hat, hax]

/-! ### The two structural identities -/

/-- `subst t x p q` is the Nielsen substitution `t ↦ t ^ p` followed by the automorphism
`x ↦ x * t ^ (-q)` (which fixes `t`).  Both maps are homomorphisms, so it suffices to check the
identity on the generators of `F β`. -/
theorem ips_subst_comp_powSubst {β : Type*} {t x : β} (hxt : x ≠ t) (p q : ℤ) :
    subst t x p q = (subst t x 1 q).comp (powSubst t p) := by
  apply FreeGroup.ext_hom
  intro a
  rw [MonoidHom.comp_apply]
  by_cases ha : a = t
  · subst ha
    simp only [powSubst_of_eq, ips_subst_of_t, map_zpow, zpow_one]
  · rw [powSubst_of_ne ha]
    by_cases hb : a = x
    · subst hb
      rw [ips_subst_of_x hxt, ips_subst_of_x hxt]
    · rw [ips_subst_of_ne ha hb, ips_subst_of_ne ha hb]

/-- `subst t x 1 (-q)` is a left inverse of `subst t x 1 q`: the latter is the Nielsen
transformation `x ↦ x * t ^ (-q)` of `F β`, whose inverse is `x ↦ x * t ^ q`.  Again it suffices to
check the identity on generators. -/
theorem ips_subst_one_leftInverse {β : Type*} {t x : β} (hxt : x ≠ t) (q : ℤ) :
    (subst t x 1 (-q)).comp (subst t x 1 q) = MonoidHom.id (FreeGroup β) := by
  apply FreeGroup.ext_hom
  intro a
  rw [MonoidHom.comp_apply, MonoidHom.id_apply]
  by_cases ha : a = t
  · subst ha
    simp only [ips_subst_of_t, zpow_one]
  · by_cases hb : a = x
    · subst hb
      simp only [ips_subst_of_x hxt, ips_subst_of_t, map_mul, map_zpow]
      group
    · rw [ips_subst_of_ne ha hb, ips_subst_of_ne ha hb]

/-! ### The proper-power equivalence -/

/-- **Being a proper power is unaffected by the substitution `subst t x p q` beyond the factor
`t ↦ t ^ p`.**  Indeed `subst t x p q = (subst t x 1 q).comp (powSubst t p)`, and
`subst t x 1 q` is a bijective endomorphism of the free group `F β` (with inverse
`subst t x 1 (-q)`); a bijective homomorphism carries `k`-th powers to `k`-th powers and, via its
left inverse, recovers a root from a root of the image. -/
theorem isProperPower_subst_iff_powSubst {β : Type*} (T : FreeGroup β) {t x : β} (hxt : x ≠ t) (p q : ℤ) :
    Work.OROneRel.IsProperPower (Work.OROneRel.subst t x p q T) ↔
      Work.OROneRel.IsProperPower (Work.OROneRel.powSubst t p T) := by
  have hcomp := ips_subst_comp_powSubst (β := β) hxt p q
  have hinv := ips_subst_one_leftInverse (β := β) hxt q
  have h1 : subst t x p q T = subst t x 1 q (powSubst t p T) := by
    rw [hcomp]; rfl
  have h2 : ∀ W : FreeGroup β, subst t x 1 (-q) (subst t x 1 q W) = W := by
    intro W
    have := DFunLike.congr_fun hinv W
    simpa using this
  constructor
  · intro h
    rw [h1] at h
    obtain ⟨u, k, hk, hk'⟩ := h
    refine ⟨subst t x 1 (-q) u, k, hk, ?_⟩
    rw [← h2 (powSubst t p T), hk', map_pow]
  · intro h
    rw [h1]
    obtain ⟨u, k, hk, hk'⟩ := h
    exact ⟨subst t x 1 q u, k, hk, by rw [hk', map_pow]⟩

end Work.OROneRel
