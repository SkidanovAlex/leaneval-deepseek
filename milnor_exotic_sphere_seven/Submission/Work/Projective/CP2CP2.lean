import Mathlib
import Submission.Work.Projective.CP2CP2Ring
import Submission.Work.Projective.cp2cp2_sigma
import Submission.Work.SignatureBordism.Bordism

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The numbers of `ℂP² × ℂP²` from its Künneth ring

`Submission/Work/Projective/CP2CP2Ring.lean` records the Künneth ring of `ℂP² × ℂP²` as the
structure `Work.Projective.CP2CP2Model`; `Submission/Work/Projective/cp2cp2_sigma.lean` derives the
signature `σ(ℂP² × ℂP²) = 1` from it.  This module completes the generator check:

* `Work.Projective.CP2CP2Model.sigma` — `σ = 1`;
* `Work.Projective.CP2CP2Model.p1SqNumber` — `p₁² = 18`;
* `Work.Projective.CP2CP2Model.p2Number` — `p₂ = 9`;
* `Work.Projective.CP2CP2Model.hirzebruchEight` — the dimension-`8` Hirzebruch identity
  `45 σ = 7p₂ - p₁²`, i.e. `45·1 = 7·9 - 18 = 45`;
* `Work.Projective.CP2CP2Model.hirzebruchEightManifold` — the same in the
  `Work.SignatureBordism.HirzebruchEightManifold` form;
* `Work.Projective.CP2CP2Model.tuple` — the triple `(σ, p₁², p₂) = (1, 18, 9)` equals
  `Work.SignatureBordism.cp2cp2Tuple`, the second generator of `Ω^SO_8 ⊗ ℚ`.

The same numbers are computed *abstractly*, in the truncated polynomial ring
`Work.Projective.CPRing 2 ⊗ Work.Projective.CPRing 2`, in
`Submission/Work/Projective/Product.lean` (`Work.Projective.p1SqNumberProd_eq = 18`,
`Work.Projective.p2NumberProd_eq = 9`, `Work.Projective.hirzebruchEight_cp2cp2`,
`Work.Projective.cp2cp2Tuple_eq`); the present module is the `SSet`-level statement, i.e. the
generator check *attached to a manifold model* `X` rather than to the abstract ring.

The interface is not inhabited by a concrete `SSet` in this workspace: the identification
`H^*(X) ≅ ℤ[a,b]/(a³,b³)` for `X = toSSet.obj (ℂP² × ℂP²)` is the Künneth theorem for the cup
product, which the workspace does not have (no Eilenberg–Zilber comparison and no Künneth formula
for the cohomology ring of a product of simplicial sets — the Künneth computations that do exist,
`Work.Cohomology.homology_prod_sphere`, are for products of *spheres* and only at the level of
homology).  See `README.md` §4 for the exact statement that is missing.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Work.Projective

open CategoryTheory Limits Work.Cohomology Work.SignatureBordism

noncomputable section

variable {X : SSet}

/-- **The signature of `ℂP² × ℂP²` is `1`**, from the Künneth ring data
(`Submission/Work/Projective/cp2cp2_sigma.lean`). -/
theorem CP2CP2Model.sigma (M : CP2CP2Model X) :
    Work.SignatureBordism.sigma 4 X M.c = 1 :=
  cp2cp2_sigma M

/-- **The `p₁²`-number of `ℂP² × ℂP²` is `18`**: with `p₁ = 3(a² + b²)`,
`⟨p₁ ⌣ p₁, c⟩ = 9·(⟨a² ⌣ a², c⟩ + ⟨a² ⌣ b², c⟩ + ⟨b² ⌣ a², c⟩ + ⟨b² ⌣ b², c⟩)
= 9·(0 + 1 + 1 + 0) = 18`. -/
theorem CP2CP2Model.p1SqNumber (M : CP2CP2Model X) :
    Work.SignatureBordism.p₁SqNumber X M.c M.p₁ = 18 := by
  show interForm ℤ X 4 4 M.c M.p₁ M.p₁ = 18
  rw [M.p₁_eq]
  simp only [map_zsmul, map_add, LinearMap.smul_apply, LinearMap.add_apply,
    M.int_a2a2, M.int_a2b2, M.int_b2a2, M.int_b2b2, smul_eq_mul]
  norm_num

/-- **The `p₂`-number of `ℂP² × ℂP²` is `9`**: `p₂ = 9·a²b²` and `⟨a²b², c⟩ = 1`. -/
theorem CP2CP2Model.p2Number (M : CP2CP2Model X) :
    Work.SignatureBordism.p₂Number X M.c M.p₂ = 9 := by
  have h : ((kronH ℤ X 8) (kTop X (kSq X M.a) (kSq X M.b))) M.c = 1 := M.int_a2b2
  show ((kronH ℤ X 8) M.p₂) M.c = 9
  rw [M.p₂_eq, map_zsmul, LinearMap.smul_apply, h, smul_eq_mul]
  norm_num

/-- **The dimension-`8` Hirzebruch identity for `ℂP² × ℂP²`**: `45·σ = 7·p₂ - p₁²`, i.e.
`45·1 = 7·9 - 18`. -/
theorem CP2CP2Model.hirzebruchEight (M : CP2CP2Model X) :
    HirzebruchEight (Work.SignatureBordism.sigma 4 X M.c)
      (Work.SignatureBordism.p₁SqNumber X M.c M.p₁)
      (Work.SignatureBordism.p₂Number X M.c M.p₂) := by
  rw [HirzebruchEight, M.sigma, M.p1SqNumber, M.p2Number]
  norm_num

/-- **The dimension-`8` Hirzebruch identity for `ℂP² × ℂP²`**, in the `HirzebruchEightManifold`
form used by the bordism chapter. -/
theorem CP2CP2Model.hirzebruchEightManifold (M : CP2CP2Model X) :
    HirzebruchEightManifold X M.c M.p₁ M.p₂ :=
  M.hirzebruchEight

/-- **The numbers of `ℂP² × ℂP²` are `(σ, p₁², p₂) = (1, 18, 9)`** — the second generator of
`Ω^SO_8 ⊗ ℚ`, in the `ℚ`-tuple form consumed by the bordism reduction. -/
theorem CP2CP2Model.tuple (M : CP2CP2Model X) :
    ((Work.SignatureBordism.sigma 4 X M.c : ℚ),
      (Work.SignatureBordism.p₁SqNumber X M.c M.p₁ : ℚ),
      (Work.SignatureBordism.p₂Number X M.c M.p₂ : ℚ)) = cp2cp2Tuple := by
  rw [M.sigma, M.p1SqNumber, M.p2Number]
  norm_num [cp2cp2Tuple]

/-- **The Hirzebruch functional vanishes on the numbers of `ℂP² × ℂP²`.** -/
theorem CP2CP2Model.hirzebruchFunctional (M : CP2CP2Model X) :
    hirzebruchFunctional8
      (Work.SignatureBordism.sigma 4 X M.c,
        (Work.SignatureBordism.p₁SqNumber X M.c M.p₁ : ℚ),
        (Work.SignatureBordism.p₂Number X M.c M.p₂ : ℚ)) = 0 := by
  rw [M.sigma, M.p1SqNumber, M.p2Number]
  norm_num [hirzebruchFunctional8]

/-- **The numbers of `ℂP² × ℂP²` lie in the span of the two generators of `Ω^SO_8 ⊗ ℚ`** — indeed
they *are* the second generator. -/
theorem CP2CP2Model.numbersInSpan (M : CP2CP2Model X) :
    ((Work.SignatureBordism.sigma 4 X M.c : ℚ),
      (Work.SignatureBordism.p₁SqNumber X M.c M.p₁ : ℚ),
      (Work.SignatureBordism.p₂Number X M.c M.p₂ : ℚ)) ∈ Submodule.span ℚ {cp4Tuple, cp2cp2Tuple} :=
  Submodule.subset_span (by rw [M.tuple]; exact Set.mem_insert_iff.mpr (Or.inr rfl))

end

end Work.Projective
