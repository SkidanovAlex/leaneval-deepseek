import Mathlib
import Submission.Work.SignatureBordism.Numbers
import Submission.Work.SignatureBordism.Rationalisation
import Submission.Work.Projective.Generators
import Submission.Work.SignatureBordism.Bordism

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Attaching the numbers of `ℂP⁴` and `ℂP²` to an `SSet` model: the cochain interface

`Work.Projective.Generators`, `Work.Projective.Chern` and `Work.Projective.Product` compute the
numbers `(σ, p₁², p₂) = (1, 25, 10)`, `(1, 18, 9)` and `(1, 3)` of `ℂP⁴`, `ℂP² × ℂP²` and `ℂP²`
*in the abstract cohomology ring* `ℤ[h]/(h^{n+1})` (`Work.Projective.CPRing n`).  To use them for
an actual `SSet` model of the manifold — for instance the model
`TopCat.toSSet.obj (TopCat.of (CP 4))` of `Work.Projective.Model` — one has to identify the
cohomology ring of that model with `ℤ[h]/(h^{n+1})`, i.e. produce the class `h ∈ H²`, the
fundamental class `c ∈ H₈`, the Pontryagin classes `p₁ = 5 h²`, `p₂ = 10 h⁴` and the pairings
`⟨h² ⌣ h², c⟩ = ⟨h⁴, c⟩ = 1`, `H⁴ = ℤ⟨h²⟩`.

This module records that data as a `structure` (`Work.Projective.CP4Model`,
`Work.Projective.CP2Model`) in the vocabulary of the workspace's cochain model
(`Work.Cohomology.chainC`, `cochainC`, `cupH'`, `kronH`, `interForm`) and **derives the generator
checks** from it — the analogue, for the generator side, of
`Work.SignatureBordism.NumbersInSpan8` on the consumer side:

* `Work.Projective.CP4Model.sigma`, `….p1SqNumber`, `….p2Number` — the numbers `1`, `25`, `10` for
  any `SSet` model carrying the data;
* `Work.Projective.CP4Model.hirzebruchEight` — the dimension-`8` Hirzebruch identity
  `Work.SignatureBordism.HirzebruchEightManifold X c p₁ p₂` for such a model;
* `Work.Projective.CP2Model.p1Number`, `….hirzebruchFour` — the dimension-`4` counterpart.

The one thing this module does *not* do (and which is the remaining gap of the chapter) is
*produce* the data for a concrete `SSet` — i.e. compute `H^*(ℂP⁴;ℤ)` in the singular cochain model
of the workspace.  That is a (large) Mayer–Vietoris computation, exactly parallel to the
computation of `H^*(D(ξ) ∪ D⁸;ℤ)` in `Submission/Work/Cohomology/`; the abstract ring and its
Chern/Pontryagin calculus are in `Work.Projective.Ring`/`Chern`/`Product`.
-/

open scoped BigOperators

namespace Work.Projective

open Work.Cohomology Work.SignatureBordism

noncomputable section

/-! ## The dimension-`8` generator `ℂP⁴` -/

/-- **The data attaching the cohomology ring of `ℂP⁴` to an `SSet` model `X`**: the hyperplane
class `h ∈ H²`, the fundamental class `c ∈ H⁸`, the Pontryagin classes `p₁ = 5h² ∈ H⁴`,
`p₂ = 10h⁴ ∈ H⁸`, the fact that `H⁴ = ℤ⟨h²⟩`, and the pairings `⟨h² ⌣ h², c⟩ = 1`,
`⟨h⁴, c⟩ = 1`. -/
structure CP4Model (X : SSet) where
  /-- the hyperplane class `h ∈ H²(ℂP⁴;ℤ)` -/
  h : (cochainC ℤ X).homology 2
  /-- the fundamental class `c ∈ H₈(ℂP⁴;ℤ)` -/
  c : (chainC ℤ X).homology 8
  /-- the first Pontryagin class `p₁(TℂP⁴) ∈ H⁴` -/
  p₁ : (cochainC ℤ X).homology 4
  /-- the second Pontryagin class `p₂(TℂP⁴) ∈ H⁸` -/
  p₂ : (cochainC ℤ X).homology 8
  /-- `H⁴(ℂP⁴;ℤ) = ℤ⟨h²⟩` -/
  h2_span : Submodule.span ℤ {cupH' ℤ X 2 2 h h} = ⊤
  /-- `⟨h² ⌣ h², [ℂP⁴]⟩ = 1`: Poincaré duality in the middle degree -/
  h2_self : interForm ℤ X 4 4 c (cupH' ℤ X 2 2 h h) (cupH' ℤ X 2 2 h h) = 1
  /-- `p₁(TℂP⁴) = 5 h²` (`c₁ = 5h`, `c₂ = 10h²`) -/
  p₁_eq : p₁ = (5 : ℤ) • cupH' ℤ X 2 2 h h
  /-- `p₂(TℂP⁴) = 10 h⁴` -/
  p₂_eq : p₂ = (10 : ℤ) • (cupH' ℤ X 6 2 (cupH' ℤ X 4 2 (cupH' ℤ X 2 2 h h) h) h)
  /-- `⟨h⁴, [ℂP⁴]⟩ = 1` -/
  h4_top : kronH ℤ X 8 (cupH' ℤ X 6 2 (cupH' ℤ X 4 2 (cupH' ℤ X 2 2 h h) h) h) c = 1

/-- **The signature of an `SSet` model of `ℂP⁴` is `1`.** -/
theorem CP4Model.sigma (X : SSet) (M : CP4Model X) :
    Work.SignatureBordism.sigma 4 X M.c = 1 :=
  Work.SignatureBordism.sigma_eq_one_of_span_singleton 4 X M.c _ M.h2_span M.h2_self

/-- **The `p₁²`-number of an `SSet` model of `ℂP⁴` is `25`.** -/
theorem CP4Model.p1SqNumber (X : SSet) (M : CP4Model X) :
    Work.SignatureBordism.p₁SqNumber X M.c M.p₁ = 25 := by
  rw [Work.SignatureBordism.p₁SqNumber_eq_sq X M.c _ M.p₁ M.p₁_eq M.h2_self]
  norm_num

/-- **The `p₂`-number of an `SSet` model of `ℂP⁴` is `10`.** -/
theorem CP4Model.p2Number (X : SSet) (M : CP4Model X) :
    Work.SignatureBordism.p₂Number X M.c M.p₂ = 10 := by
  rw [Work.SignatureBordism.p₂Number, M.p₂_eq, map_zsmul, LinearMap.smul_apply, smul_eq_mul,
    M.h4_top]
  norm_num

/-- **The dimension-`8` Hirzebruch identity for an `SSet` model of `ℂP⁴`**: the numbers
`(σ, p₁², p₂) = (1, 25, 10)` satisfy `45σ = 7p₂ - p₁²`. -/
theorem CP4Model.hirzebruchEight (X : SSet) (M : CP4Model X) :
    Work.SignatureBordism.HirzebruchEightManifold X M.c M.p₁ M.p₂ := by
  rw [Work.SignatureBordism.HirzebruchEightManifold, Work.SignatureBordism.HirzebruchEight,
    CP4Model.sigma X M, CP4Model.p1SqNumber X M, CP4Model.p2Number X M]
  norm_num

/-! ## The dimension-`4` generator `ℂP²` -/

/-- **The data attaching the cohomology ring of `ℂP²` to an `SSet` model `X`**: the hyperplane class
`h ∈ H²`, the fundamental class `c ∈ H⁴`, the first Pontryagin class `p₁ = 3h ∈ H⁴`, the fact that
`H² = ℤ⟨h⟩` and the pairing `⟨h ⌣ h, c⟩ = 1`. -/
structure CP2Model (X : SSet) where
  /-- the hyperplane class `h ∈ H²(ℂP²;ℤ)` -/
  h : (cochainC ℤ X).homology 2
  /-- the fundamental class `c ∈ H₄(ℂP²;ℤ)` -/
  c : (chainC ℤ X).homology 4
  /-- the first Pontryagin class `p₁(TℂP²) ∈ H⁴` -/
  p₁ : (cochainC ℤ X).homology 4
  /-- `H²(ℂP²;ℤ) = ℤ⟨h⟩` -/
  h_span : Submodule.span ℤ {h} = ⊤
  /-- `p₁(TℂP²) = 3 h²` (`c₁ = 3h`, `c₂ = 3h²`) -/
  p₁_eq : p₁ = (3 : ℤ) • cupH' ℤ X 2 2 h h
  /-- `⟨h ⌣ h, [ℂP²]⟩ = 1`: the middle self-intersection -/
  h_self : kronH ℤ X 4 (cupH' ℤ X 2 2 h h) c = 1

/-- **The signature of an `SSet` model of `ℂP²` is `1`.** -/
theorem CP2Model.sigma (X : SSet) (M : CP2Model X) :
    Work.SignatureBordism.sigma 2 X M.c = 1 :=
  Work.SignatureBordism.sigma_eq_one_of_span_singleton 2 X M.c M.h M.h_span M.h_self

/-- **The `p₁`-number of an `SSet` model of `ℂP²` is `3`.** -/
theorem CP2Model.p1Number (X : SSet) (M : CP2Model X) :
    Work.SignatureBordism.p₁Number X M.c M.p₁ = 3 := by
  rw [Work.SignatureBordism.p₁Number, M.p₁_eq, map_zsmul, LinearMap.smul_apply, smul_eq_mul,
    M.h_self]
  norm_num

/-- **The dimension-`4` Hirzebruch identity for an `SSet` model of `ℂP²`**: `p₁ = 3σ`. -/
theorem CP2Model.hirzebruchFour (X : SSet) (M : CP2Model X) :
    Work.SignatureBordism.HirzebruchFourManifold X M.c M.p₁ := by
  rw [Work.SignatureBordism.HirzebruchFourManifold, Work.SignatureBordism.HirzebruchFour,
    CP2Model.sigma X M, CP2Model.p1Number X M]
  norm_num

/-- **The numbers of a `CP4Model` are the triple `(1, 25, 10)`** in the `ℚ`-tuple form
`Work.SignatureBordism.cp4Tuple` consumed by the bordism reduction. -/
theorem CP4Model.tuple (X : SSet) (M : CP4Model X) :
    ((Work.SignatureBordism.sigma 4 X M.c : ℚ),
      (Work.SignatureBordism.p₁SqNumber X M.c M.p₁ : ℚ),
      (Work.SignatureBordism.p₂Number X M.c M.p₂ : ℚ)) = cp4Tuple := by
  rw [CP4Model.sigma X M, CP4Model.p1SqNumber X M, CP4Model.p2Number X M]
  norm_num [cp4Tuple]

/-- **The numbers of a `CP4Model` lie in the span of the two generators of `Ω^SO_8 ⊗ ℚ`** — indeed
they *are* the first generator. -/
theorem CP4Model.numbersInSpan (X : SSet) (M : CP4Model X) :
    ((Work.SignatureBordism.sigma 4 X M.c : ℚ),
      (Work.SignatureBordism.p₁SqNumber X M.c M.p₁ : ℚ),
      (Work.SignatureBordism.p₂Number X M.c M.p₂ : ℚ))
      ∈ Submodule.span ℚ ({cp4Tuple, cp2cp2Tuple} : Set (ℚ × ℚ × ℚ)) :=
  Submodule.subset_span (by rw [CP4Model.tuple X M]; exact Set.mem_insert_iff.mpr (Or.inl rfl))

/-- **The manifold-level dimension-`8` Hirzebruch identity for a `CP4Model`.** -/
theorem CP4Model.hirzebruchEightManifold (X : SSet) (M : CP4Model X) :
    Work.SignatureBordism.HirzebruchEightManifold X M.c M.p₁ M.p₂ :=
  CP4Model.hirzebruchEight X M

/-- **The numbers of a `CP2Model` are the pair `(1, 3)`** in the `ℚ`-tuple form
`Work.SignatureBordism.cp2Tuple`. -/
theorem CP2Model.tuple (X : SSet) (M : CP2Model X) :
    ((Work.SignatureBordism.sigma 2 X M.c : ℚ),
      (Work.SignatureBordism.p₁Number X M.c M.p₁ : ℚ)) = cp2Tuple := by
  rw [CP2Model.sigma X M, CP2Model.p1Number X M]
  norm_num [cp2Tuple]

/-- **The numbers of a `CP2Model` lie in the span of `(1,3)`** — indeed they *are* `(1,3)`. -/
theorem CP2Model.numbersInSpan (X : SSet) (M : CP2Model X) :
    ((Work.SignatureBordism.sigma 2 X M.c : ℚ),
      (Work.SignatureBordism.p₁Number X M.c M.p₁ : ℚ))
      ∈ Submodule.span ℚ ({cp2Tuple} : Set (ℚ × ℚ)) :=
  Submodule.subset_span (by rw [CP2Model.tuple X M]; rfl)

/-- **The manifold-level dimension-`4` Hirzebruch identity for a `CP2Model`.** -/
theorem CP2Model.hirzebruchFourManifold (X : SSet) (M : CP2Model X) :
    Work.SignatureBordism.HirzebruchFourManifold X M.c M.p₁ :=
  CP2Model.hirzebruchFour X M

end

end Work.Projective
