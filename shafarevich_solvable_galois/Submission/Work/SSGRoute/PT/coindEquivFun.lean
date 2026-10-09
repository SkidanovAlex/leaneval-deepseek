import Mathlib
import Submission.Work.SSGRoute.PT.ClassFormation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The coinduced module `Coind^G_U M` as functions on the left cosets `G ⧸ U`

For a group `G`, a subgroup `U ≤ G` and a `DistribMulAction U M` on an additive commutative
group `M`, the coinduced module is

`Coind G U M = { f : G → M // ∀ g u, f (g * u) = u⁻¹ • f g }`

(the module `Hom_{ℤU}(ℤG, M)` written additively, where `U` acts on `ℤG` by right
translations).

Every `f ∈ Coind G U M` is *determined* by its values on a set of representatives of the left
cosets `G ⧸ U`: if `g = s * u` with `s = out (mk g)` the chosen representative of the coset
`gU` and `u ∈ U`, then `f g = u⁻¹ • f s`.  Conversely, arbitrary values on the coset space can
be extended in exactly one way.  Consequently the additive group of the coinduced module is
isomorphic to the additive group of *all* functions `G ⧸ U → M`; this is the content of
`coindEquivFun` below.

Since `G ⧸ U` is only a `G`-set (and not a group when `U` is not normal) and the isomorphism is
built from an arbitrary choice of coset representatives, it is not `G`-equivariant; it is an
isomorphism of additive groups only.  That is all the Shapiro/dévissage arguments need, for
they use it to compare *dimensions* of cohomology groups.

## Main results

* `Coind.rep` and `Coind.rep_spec`: the `U`-coordinate of `g` relative to the chosen coset
  representative `(mk g).out`, i.e. the element `h ∈ U` with `(mk g).out = g * h`.
* `Coind.toFun` and `Coind.ofFun`: the two directions of the isomorphism.
* `Coind.addEquivFun`: the additive equivalence `Coind G U M ≃+ (G ⧸ U → M)`.
* `coindEquivFun`: its `Nonempty` form, i.e. existence of such an additive equivalence.
-/

namespace Work.SSGRoute.PT

open QuotientGroup

noncomputable section

variable (G : Type*) [Group G] (U : Subgroup G) (M : Type*) [AddCommGroup M]
  [DistribMulAction U M]

namespace Coind

/-- The `U`-coordinate of `g` with respect to the chosen representative `(mk g).out` of the left
coset `gU`: the element `h ∈ U` with `(mk g).out = g * h`.  (Such an `h` exists because
`mk ((mk g).out) = mk g`.) -/
def rep (g : G) : U := Classical.choose (QuotientGroup.mk_out_eq_mul U g)

theorem rep_spec (g : G) :
    (QuotientGroup.mk g : G ⧸ U).out = g * (rep G U g : G) :=
  Classical.choose_spec (QuotientGroup.mk_out_eq_mul U g)

/-- A coinduced function is constant along `U`-multiples only up to the twist
`f (g * u) = u⁻¹ • f g`; correspondingly an element of `Coind G U M` is determined by its values
on the chosen representatives of the left cosets.  This is the forward map of the additive
equivalence `Coind.addEquivFun`. -/
def toFun (f : Coind G U M) : (G ⧸ U) → M := fun q => f q.out

/-- Conversely, a function on the coset space `G ⧸ U` defines an element of `Coind G U M` by
`f g = u⁻¹ • φ (gU)`, where `g = s * u` with `s = (mk g).out`; in terms of `Coind.rep` this is
`f g = rep g • φ (gU)`.  This is the inverse of `Coind.toFun`. -/
def ofFun (φ : (G ⧸ U) → M) : Coind G U M :=
  ⟨fun g => rep G U g • φ (QuotientGroup.mk g), by
    -- the defining cocycle relation: `f (g * v) = v⁻¹ • f g` for `v : U`
    intro g v
    have hk : (QuotientGroup.mk (g * (v : G)) : G ⧸ U) = QuotientGroup.mk g :=
      QuotientGroup.mk_mul_of_mem g v.2
    have h1 := rep_spec G U (g * (v : G))
    have h2 := rep_spec G U g
    rw [hk] at h1
    -- both `(mk g).out` and `g * (rep g)` are the representative of the same coset
    have hcancel : (v : G) * (rep G U (g * (v : G)) : G) = (rep G U g : G) := by
      have h := h1.symm.trans h2
      rw [mul_assoc] at h
      exact mul_left_cancel h
    have hrep : rep G U (g * (v : G)) = v⁻¹ * rep G U g := by
      refine Subtype.ext ?_
      rw [← inv_mul_cancel_left (v : G) ((rep G U (g * (v : G))) : G), hcancel]
      simp
    show rep G U (g * (v : G)) • φ (QuotientGroup.mk (g * (v : G))) =
      v⁻¹ • (rep G U g • φ (QuotientGroup.mk g))
    rw [hk, hrep, mul_smul]⟩

@[simp] theorem toFun_apply (f : Coind G U M) (q : G ⧸ U) :
    toFun G U M f q = f q.out := rfl

@[simp] theorem ofFun_apply (φ : (G ⧸ U) → M) (g : G) :
    ofFun G U M φ g = rep G U g • φ (QuotientGroup.mk g) := rfl

/-- `Coind.toFun` and `Coind.ofFun` are mutually inverse; hence the coinduced module is
additively isomorphic to the functions on `G ⧸ U`. -/
def addEquivFun : Coind G U M ≃+ ((G ⧸ U) → M) where
  toFun := toFun G U M
  invFun := ofFun G U M
  left_inv f := by
    -- `f g = rep g • f (mk g).out`, so `f` is recovered from `f ∘ out`
    refine Subtype.ext (funext fun g => ?_)
    show rep G U g • (toFun G U M f) (QuotientGroup.mk g) = f g
    rw [toFun_apply, rep_spec G U g, Coind.coe_mul]
    exact smul_inv_smul _ _
  right_inv φ := by
    funext q
    show ofFun G U M φ q.out = φ q
    -- on a chosen representative the `U`-coordinate is trivial
    have hrep1 : rep G U q.out = 1 := by
      refine Subtype.ext ?_
      have hspec := rep_spec G U q.out
      rw [QuotientGroup.out_eq'] at hspec
      have h : (Quotient.out q) * (1 : G) =
          (Quotient.out q) * (rep G U (Quotient.out q) : G) := by
        rw [mul_one]
        exact hspec
      exact (mul_left_cancel h).symm
    rw [ofFun_apply, hrep1, QuotientGroup.out_eq']
    exact one_smul _ _
  map_add' f h := by
    funext q
    rfl

end Coind

end

/-- **The coinduced module is the module of functions on the left cosets.**  For any group `G`,
subgroup `U ≤ G` and `U`-module `M` (written additively), the additive group of the coinduced
module `Coind G U M = { f : G → M // ∀ g u, f (g * u) = u⁻¹ • f g }` is isomorphic to the
additive group of all functions `G ⧸ U → M`: an element is determined by its values on the
chosen representatives of the left cosets, and conversely any function on `G ⧸ U` extends
uniquely. -/
theorem coindEquivFun (G : Type*) [Group G] (U : Subgroup G) (M : Type*) [AddCommGroup M]
    [DistribMulAction U M] :
    Nonempty (Work.SSGRoute.PT.Coind G U M ≃+ ((G ⧸ U) → M)) :=
  ⟨Coind.addEquivFun G U M⟩

end Work.SSGRoute.PT
