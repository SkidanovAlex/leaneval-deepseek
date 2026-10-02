import Mathlib
import Submission.Work.Gen.LineTensor
import Submission.Work.Thom.chernClass
import Submission.Work.Thom.chernClass_comap
import Submission.Work.Thom.trivialChern
import Submission.Work.Thom.Gysin
import Submission.Work.Thom.Indicator
import Submission.Work.Whitney.SectionStability
import Submission.Work.Whitney.nonempty_bundleIso_sumEps_whitneySum
import Submission.Work.Whitney.Cup
import Submission.Work.Cohomology.CupRing
import Submission.Work.Cohomology.exists_smul_oneH

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The `LineBundles` chapter: additivity of `c₁` under the tensor product of line bundles

This chapter proves

  `c₁(L₁ ⊗ L₂) = c₁(L₁) + c₁(L₂)`

for complex **line** bundles given as gluing data
(`VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι`) over an arbitrary topological base, where
`c₁ = Work.Thom.chernClass 1 1` is the first Chern class of the Thom chapter and
`⊗ = Work.Gen.tensorLine` is the tensor product of line-bundle cores.

By the determinant trick (`Work.Gen.chernClass_one_whitneySum_eq_tensorLine`, i.e.
`c₁(L₁ ⊕ L₂) = c₁(L₁ ⊗ L₂)`) this is equivalent to the degree-`1` part of the Whitney sum formula
`c₁(L₁ ⊕ L₂) = c₁(L₁) + c₁(L₂)`.

The route taken here is the **Gysin/divisibility route** (no Künneth, no Leray–Hirsch, no
partition of unity, no paracompactness):

1. `Divisibility` — for line bundles `L, M` over `B`, the class `c₁(L ⊗ M) - c₁(M)` is a multiple
   of `c₁(L)` by an element of `H⁰(B;ℤ)`.  Proof: over the punctured total space `X` of the
   realification of `L`, the pullback of `L` acquires a nowhere-zero (tautological) section, hence is
   trivial, so `π^*(c₁(L ⊗ M)) = π^*(c₁(M))`; the Gysin exactness
   `Work.Thom.gysin_exact_at_base` computes `ker π^* = range (· ∪ e(L_ℝ))` and
   `Work.Thom.chernClass_one_top` identifies `e(L_ℝ)` with `c₁(L)`.
2. `Connected` — over a **path connected** base, the `H⁰`-witness is a single integer
   (`Work.Cohomology.exists_smul_oneH`), and pulling the relation for `L, M` back to `B × B` together
   with the slice `B × {b} ↪ B × B` and the diagonal pins it to `1`.
3. `Patching` — a class in `H^n(B;ℤ)` whose restriction to every path component of `B` vanishes is
   zero (`Work.Cohomology.equalizer`-free route: the singular cochain complex of a space is the
   direct sum of those of its path components, so a cocycle all of whose components are coboundaries
   is a coboundary).
4. Assembly: over each path component the theorem is the connected case, and `Patching` upgrades the
   component-wise statement to the global one.

## Conventions

* `Work.LineBundles.LineCore B ι` is the type of complex line bundle cores
  (`VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι`);
* `Work.LineBundles.c1 L` is `Work.Thom.chernClass 1 1 L ∈ H²(B;ℤ)`;
* `Work.LineBundles.cup₀₂ B` is the graded cup product `H⁰(B;ℤ) →ₗ H²(B;ℤ) →ₗ H²(B;ℤ)`, packaged
  as `Work.Whitney.cupChern 0 1` (so that the degree bookkeeping is built in and both sides of the
  main identity live in the same module `Coh ℤ (2*1) B = H²(B;ℤ)`).
-/

namespace Work.LineBundles

open Work.TangentClasses Work.Thom

noncomputable section

/-! ## Conventions -/

/-- A complex line bundle over `B`, as gluing data over the cover `ι`. -/
abbrev LineCore (B : Type) [TopologicalSpace B] (ι : Type) : Type _ :=
  VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι

/-- The trivial complex line bundle over `B`. -/
abbrev trivLine (B : Type) [TopologicalSpace B] (ι : Type) [Inhabited ι] : LineCore B ι :=
  trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι

/-- The first Chern class `c₁(L) ∈ H²(B;ℤ)` of a complex line bundle. -/
abbrev c1 {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι] (L : LineCore B ι) :
    Work.Thom.Coh ℤ (2 * 1) B :=
  Work.Thom.chernClass 1 1 L

/-- The graded cup product `H⁰(B;ℤ) →ₗ[ℤ] H²(B;ℤ) →ₗ[ℤ] H²(B;ℤ)`: `Work.Whitney.cupChern 0 1`. -/
def cup₀₂ (B : Type) [TopologicalSpace B] :=
  Work.Whitney.cupChern (B := B) 0 1

/-- The computation rule for `cup₀₂`: it is the cup product of a degree-`0` with a degree-`2`
class. -/
theorem cup₀₂_apply {B : Type} [TopologicalSpace B] (x : Work.Thom.Coh ℤ 0 B)
    (y : Work.Thom.Coh ℤ 2 B) :
    cup₀₂ B x y = Work.Whitney.cupChern (B := B) 0 1 x y := rfl

/-! ## The path components, as subspaces -/

/-- The **path component** of `B` corresponding to a `π₀`-class `c`: the subspace of points whose
`0`-simplex lies in the class `c`. -/
def pathComp (B : Type) [TopologicalSpace B]
    (c : SSet.π₀ (TopCat.toSSet.obj (TopCat.of B))) : Set B :=
  {x : B | SSet.π₀.mk ((TopCat.toSSetObj₀Equiv (X := TopCat.of B)).symm x) = c}

/-- The inclusion of a path component into the ambient space. -/
def pathCompIncl (B : Type) [TopologicalSpace B]
    (c : SSet.π₀ (TopCat.toSSet.obj (TopCat.of B))) : C(↥(pathComp B c), B) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-! ## The two inputs of the chapter -/

/-- **The divisibility lemma.**  For complex line bundles `L`, `M` over an arbitrary topological
base `B`, the class `c₁(L ⊗ M) - c₁(M)` is a multiple of `c₁(L)` by a class in `H⁰(B;ℤ)`. -/
def Divisibility : Prop :=
  ∀ {B : Type} [TopologicalSpace B] {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (L : LineCore B ι₁) (M : LineCore B ι₂),
    ∃ x : Work.Thom.Coh ℤ 0 B,
      c1 (Work.Gen.tensorLine L M) = c1 M + cup₀₂ B x (c1 L)

/-- **The component patching.**  A cohomology class in degree `n` whose restriction to every path
component of the base vanishes is zero. -/
def Patching (n : ℕ) : Prop :=
  ∀ {B : Type} [TopologicalSpace B] (δ : Work.Thom.Coh ℤ n B),
    (∀ c : SSet.π₀ (TopCat.toSSet.obj (TopCat.of B)),
      (Work.Thom.CohMap (pathCompIncl B c) ℤ n).hom δ = 0) → δ = 0

/-! ## Elementary consequences -/

/-- The first Chern class of the trivial line bundle vanishes. -/
theorem c1_trivLine {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι] [Inhabited ι] :
    c1 (trivLine B ι) = 0 :=
  Work.Thom.chernClass_trivial (m := 1) (j := 1) (B := B) (by norm_num)

end

end Work.LineBundles
