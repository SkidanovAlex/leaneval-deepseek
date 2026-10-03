/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hughes-free rank functions and the N5 interface

Following [JZLA20, §3.3] we define the Hughes-free property for Sylvester rank functions on group
algebras and for epic division `K[G]`-rings, and we record the interface (the "N5 interface" of the
route design) consisting of the analytic input: a positive definite ∗-regular ring `U` with an
epic ∗-homomorphism from `K[G]` and a faithful Hughes-free rank function.
-/
import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank
import Submission.Work.ORHughesFree.Epic
import Submission.Work.ORHughesFree.StarRegular
import Submission.Work.ORHughesFree.NaturalExtension
import Submission.Work.ORHughesFree.DivisionClosure

set_option autoImplicit false

universe u

namespace Work.ORHughesFree

/-- A group is **locally indicable** if every finitely generated subgroup is either trivial or
admits a surjection onto `ℤ` ([JZLA20, §1]). -/
class LocallyIndicable (G : Type u) [Group G] : Prop where
  /-- every finitely generated non-trivial subgroup surjects onto `ℤ` -/
  surj_z : ∀ H : Subgroup G, H.FG → H ≠ ⊥ → ∃ f : H →* Multiplicative ℤ,
    Function.Surjective f

/-- The data of a decomposition `H = N ⋊ ⟨t⟩` with `H/N ≅ ℤ`, exhibited as an isomorphism
`K[H] ≅ K[N][t^{±1}; τ]` between the group algebra of `H` and the skew Laurent polynomial ring
over the group algebra of `N` ([JZLA20, §3.3]).

The two inclusions `K[N] →+* K[H]` and `K[H] →+* K[G]` are **not** fields: they are the canonical
maps induced by the subgroup inclusions `N ≤ H ≤ G` (`SkewLaurentDecomp.inclN`,
`SkewLaurentDecomp.inclH` below).  This is essential for `IsHughesFreeRank` to be the paper's
condition — if `inclN`/`inclH` were free data, replacing `inclH` by a character of `K[H]` with
`χ t = 1` would violate `IsNaturalExtension` for *every* rank function (see
`HughesFree/not_isHughesFreeRank_of_skewLaurentDecomp.lean` in the git history), making the
hypothesis unsatisfiable.

The field `iso_single` records that the isomorphism is the **canonical** one on the coefficient
copy of `K[N]`.  This is *also* essential: without it, one may compose `iso` with a ring
automorphism of `K[N][t^{±1};τ]` which moves the variable `t` into `K[N]` — e.g. for
`G = H = ℤ²`, `N = ⟨y⟩`, the isomorphism `K[y^{±1}][t^{±1}] ≅ K[x^{±1},y^{±1}]` with
`y ↦ xy` and `t ↦ y` — and then `d.t` lies in the image of `K[N]`, which makes the
linear-independence clause of `IsHughesFreeDivisionRing` (and the natural-extension condition of
`IsHughesFreeRank`) **false for every target ring**: with `u := φ (d.t)` a unit whose inverse lies
in `D_{N,D}`, the relation `1 - u⁻¹·u = 0` is a non-trivial linear dependence. -/
structure SkewLaurentDecomp (K : Type u) [Field K] (G : Type u) [Group G] (H : Subgroup G)
    (N : Subgroup H) [MulSemiringAction (Multiplicative ℤ) (MonoidAlgebra K N)] where
  /-- The isomorphism exhibiting `K[H]` as a skew Laurent polynomial ring over `K[N]`. -/
  iso : SkewMonoidAlgebra (MonoidAlgebra K N) (Multiplicative ℤ) ≃+* MonoidAlgebra K H
  /-- The image of the variable `t` in `K[H]`, i.e. the generator of `H` modulo `N`. -/
  t : (MonoidAlgebra K H)ˣ
  /-- `t` is the image of the variable of the skew Laurent polynomial ring. -/
  iso_t : iso skewLaurentT = (t : MonoidAlgebra K H)
  /-- `iso` is the canonical map on the coefficient ring `K[N]`. -/
  iso_single : ∀ b : MonoidAlgebra K N,
    iso (SkewMonoidAlgebra.single (1 : Multiplicative ℤ) b) =
      MonoidAlgebra.mapDomainRingHom K (Subgroup.subtype N) b

namespace SkewLaurentDecomp

variable {K : Type u} [Field K] {G : Type u} [Group G] {H : Subgroup G} {N : Subgroup H}
  [MulSemiringAction (Multiplicative ℤ) (MonoidAlgebra K N)]

/-- The canonical inclusion `K[N] →+* K[H]` induced by `N ≤ H`. -/
noncomputable def inclN (_d : SkewLaurentDecomp K G H N) :
    MonoidAlgebra K N →+* MonoidAlgebra K H :=
  MonoidAlgebra.mapDomainRingHom K (Subgroup.subtype N)

/-- The canonical inclusion `K[H] →+* K[G]` induced by `H ≤ G`. -/
noncomputable def inclH (_d : SkewLaurentDecomp K G H N) :
    MonoidAlgebra K H →+* MonoidAlgebra K G :=
  MonoidAlgebra.mapDomainRingHom K (Subgroup.subtype H)

end SkewLaurentDecomp

/-- A Sylvester rank function `rk` on `K[G]` is **Hughes-free** if for every finitely generated
subgroup `H ≤ G`, every normal `N ⊴ H` with `H/N ≅ ℤ` and every skew Laurent decomposition
`K[H] ≅ K[N][t^{±1}; τ]`, the restriction of `rk` to `K[H]` is the natural extension of its
restriction to `K[N]` ([JZLA20, §3.3]). -/
def IsHughesFreeRank {K : Type u} [Field K] {G : Type u} [Group G]
    (rk : SylvesterRank (MonoidAlgebra K G)) : Prop :=
  ∀ (H : Subgroup G) (N : Subgroup H) [MulSemiringAction (Multiplicative ℤ) (MonoidAlgebra K N)]
    (d : SkewLaurentDecomp K G H N),
    IsNaturalExtension
      (SylvesterRank.pullback d.inclN (SylvesterRank.pullback d.inclH rk))
      (SylvesterRank.pullback d.iso.toRingHom (SylvesterRank.pullback d.inclH rk))

/-- A **Hughes-free epic division `K[G]`-ring**: a division ring `D` with an epic ring homomorphism
`φ : K[G] →+* D`, such that for every finitely generated `H ≤ G`, normal `N ⊴ H` with `H/N ≅ ℤ`
and skew Laurent decomposition, the powers of the generator `t` are linearly independent over the
division closure of `K[N]` in `D` ([JZLA20, §3.3]). -/
def IsHughesFreeDivisionRing (K : Type u) [Field K] (G : Type u) [Group G]
    (D : Type u) [Ring D] (hD : IsDivisionRing D) (φ : MonoidAlgebra K G →+* D) : Prop :=
  IsEpic φ ∧
  ∀ (H : Subgroup G) (N : Subgroup H) [MulSemiringAction (Multiplicative ℤ) (MonoidAlgebra K N)]
    (d : SkewLaurentDecomp K G H N)
    (n : ℕ) (c : Fin (n + 1) → D),
      (∀ i, c i ∈ (divisionClosure (Set.range fun x : MonoidAlgebra K N =>
          φ (d.inclH (d.inclN x))) : Subring D)) →
      (∑ i, c i * φ (d.inclH (((d.t : (MonoidAlgebra K H)ˣ) ^ ((i : ℤ)) :
        (MonoidAlgebra K H)ˣ) : MonoidAlgebra K H))) = 0 → ∀ i, c i = 0

/-- The **N5 interface** of the route design: a positive definite ∗-regular ring `U` together with
an epic ∗-homomorphism `φ : K[G] →+* U` and a faithful Hughes-free Sylvester rank function `rk` on
`U`.  This is the analytic input on which the JZLA20 algebraic engine runs. -/
structure StarRegularEnvelope (K : Type u) [Field K] (G : Type u) [Group G] (U : Type u)
    [Ring U] [StarRing U] [IsStarRegular U] (hposDef : IsPositiveDefiniteStarRegular U) where
  /-- The ∗-homomorphism from the group algebra. -/
  φ : MonoidAlgebra K G →+* U
  /-- The involution `(λg)∗ = λ̄ g⁻¹` of the group algebra, recorded as data (Mathlib does not
  currently provide a `StarRing` instance for `MonoidAlgebra`). -/
  starK : MonoidAlgebra K G → MonoidAlgebra K G
  /-- `φ` intertwines the involution of `K[G]` with the involution of `U`. -/
  map_star : ∀ x : MonoidAlgebra K G, φ (starK x) = star (φ x)
  /-- `φ` is epic. -/
  epic : IsEpic φ
  /-- A Sylvester rank function on `U`. -/
  rk : SylvesterRank U
  /-- `rk` is faithful. -/
  faithful : rk.IsFaithful
  /-- `rk` is Hughes-free as a rank function on `K[G]`. -/
  hughesFree : IsHughesFreeRank (rk.pullback φ)

end Work.ORHughesFree
