import Mathlib
import Submission.Work.Kunneth.Chapter
import Submission.Work.LerayHirsch.Chapter
import Submission.Work.Kunneth.zetaBridgeDefs
import Submission.Work.Kunneth.PointDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# The assembly of the trivial-bundle Leray–Hirsch: definitions

Let `B` be a topological space, `m : ℕ`, `Zb = ε^m` the trivial complex bundle of rank `m` over
`B`, `Pb = P(Zb)` its projectivisation, `Qb = P(ε^m over the point)` and
`hMap : Pb → B × Qb` the map `x ↦ (projMap Zb x, qTriv m B x)` (a homeomorphism).

This file collects the objects the assembly of `Work.LerayHirsch.LerayHirschFull Zb` uses:

* `crTerm`/`crFam` — the space-level family map `(x_i) ↦ Σ_i π₁^*x_i ⌣ π₂^*(ζ^i)` on `B × Qb`
  (even degrees), and their odd counterparts `crTermOdd`/`crFamOdd`;
* `sqTerm`/`sqFam` — the same family, but built from the *simplicial* cross product
  `Work.Kunneth.crossH` on `sProd (ssB B) (ssB Qb)`, together with the comparison map
  `pullIso` induced by the monoidal isomorphism `Sing (X × Y) ≅ Sing X ⊗ Sing Y`;
* `thetaTerm`/`theta` and `thetaTermOdd`/`thetaOdd` — the "diagonal" family maps into
  `Work.Kunneth.kunnethTarget`, whose bijectivity is the Künneth collapse of the point factor.
-/

namespace Work.Kunneth.Asm

open CategoryTheory Work.TangentClasses Work.Thom

open scoped LinearAlgebra.Projectivization MonoidalCategory TensorProduct

noncomputable section

/-- The trivial complex bundle of rank `m` over `B`. -/
abbrev Zb (m : ℕ) (B : Type) [TopologicalSpace B] :
    VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) PUnit :=
  trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) PUnit

/-- The projectivisation of the trivial bundle over `B`. -/
abbrev Pb (m : ℕ) (B : Type) [TopologicalSpace B] : Type :=
  Work.LerayHirsch.ProjSpace (Zb m B)

/-- The projectivisation of the trivial bundle over the point: `ℂP^{m-1}` (empty for `m = 0`). -/
abbrev Qb (m : ℕ) : Type :=
  Work.LerayHirsch.ProjSpace (Work.LerayHirsch.trivCore m)

/-- The singular simplicial set of a space, so that `Coh ℤ n B = (cochainC ℤ (ssB B)).homology n`. -/
abbrev ssB (B : Type) [TopologicalSpace B] : SSet := Work.Whitney.ssB B

/-- The first projection `B × Qb → B`. -/
def pi1 (m : ℕ) (B : Type) [TopologicalSpace B] : C(B × Qb m, B) :=
  ⟨Prod.fst, continuous_fst⟩

/-- The second projection `B × Qb → Qb`. -/
def pi2 (m : ℕ) (B : Type) [TopologicalSpace B] : C(B × Qb m, Qb m) :=
  ⟨Prod.snd, continuous_snd⟩

/-- **The comparison map `Pb → B × Qb`**: the projection of the projectivisation together with the
class of the fibre coordinate.  It is a homeomorphism (`Work.Kunneth.Asm.nonempty_homeo_hMap`). -/
def hMap (m : ℕ) (B : Type) [TopologicalSpace B] : C(Pb m B, B × Qb m) :=
  (Work.LerayHirsch.projMap (Zb m B)).prodMk (Work.Kunneth.qTriv m B)

/-- `ζ` of the trivial bundle over the point, `ζ = c₁(ℓ(ε^m over pt)) ∈ H²(ℂP^{m-1})`. -/
abbrev zetaPt (m : ℕ) : Coh ℤ 2 (Qb m) := Work.LerayHirsch.zeta (Work.LerayHirsch.trivCore m)

/-- `ζ` of the trivial bundle over `B`. -/
abbrev zetaB (m : ℕ) (B : Type) [TopologicalSpace B] : Coh ℤ 2 (Pb m B) :=
  Work.LerayHirsch.zeta (Zb m B)

/-- The `i`-th summand of the space-level family map, in even total degree `2k`:
`π₁^*x ⌣ π₂^*(ζ^i)`, transported to degree `2k`. -/
def crTerm (m : ℕ) (B : Type) [TopologicalSpace B] (k : ℕ)
    (i : {i : Fin m // (i : ℕ) ≤ k}) (x : Coh ℤ (2 * (k - (i : ℕ))) B) :
    Coh ℤ (2 * k) (B × Qb m) :=
  cohTransport (by omega)
    (Work.Whitney.cupChern (k - (i : ℕ)) (i : ℕ)
      ((CohMap (pi1 m B) ℤ (2 * (k - (i : ℕ)))).hom x)
      ((CohMap (pi2 m B) ℤ (2 * (i : ℕ))).hom
        (Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore m) (i : ℕ))))

/-- **The space-level family map in even degrees**: `(x_i) ↦ Σ_i π₁^*x_i ⌣ π₂^*(ζ^i)`. -/
def crFam (m : ℕ) (B : Type) [TopologicalSpace B] (k : ℕ)
    (xf : (i : {i : Fin m // (i : ℕ) ≤ k}) → Coh ℤ (2 * (k - (i : ℕ))) B) :
    Coh ℤ (2 * k) (B × Qb m) :=
  ∑ i, crTerm m B k i (xf i)

/-- The `i`-th summand of the space-level family map, in odd total degree `2k+1`:
`π₁^*x ⌣ π₂^*(ζ^i)`, transported to degree `2k+1`. -/
def crTermOdd (m : ℕ) (B : Type) [TopologicalSpace B] (k : ℕ)
    (i : {i : Fin m // (i : ℕ) ≤ k}) (x : Coh ℤ (2 * k + 1 - 2 * (i : ℕ)) B) :
    Coh ℤ (2 * k + 1) (B × Qb m) :=
  cohTransport (by omega)
    (Work.Cohomology.cupH' ℤ (ssB (B × Qb m)) (2 * k + 1 - 2 * (i : ℕ)) (2 * (i : ℕ))
      ((CohMap (pi1 m B) ℤ (2 * k + 1 - 2 * (i : ℕ))).hom x)
      ((CohMap (pi2 m B) ℤ (2 * (i : ℕ))).hom
        (Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore m) (i : ℕ))))

/-- **The space-level family map in odd degrees**: `(x_i) ↦ Σ_i π₁^*x_i ⌣ π₂^*(ζ^i)`. -/
def crFamOdd (m : ℕ) (B : Type) [TopologicalSpace B] (k : ℕ)
    (xf : (i : {i : Fin m // (i : ℕ) ≤ k}) → Coh ℤ (2 * k + 1 - 2 * (i : ℕ)) B) :
    Coh ℤ (2 * k + 1) (B × Qb m) :=
  ∑ i, crTermOdd m B k i (xf i)

/-! ## The simplicial side: the cross product family and the monoidal comparison -/

/-- The monoidal comparison `Sing (B × Qb) ⟶ Sing B ⊗ Sing Qb` (the inverse of the comparison
`Sing B ⊗ Sing Qb ⟶ Sing (B × Qb)`).  It is compatible with the two projections: composing with
the `SSet`-projections `fst`/`snd` gives the maps induced by `π₁`/`π₂`. -/
def iota (m : ℕ) (B : Type) [TopologicalSpace B] :
    ssB (B × Qb m) ⟶ Work.Kunneth.sProd (ssB B) (ssB (Qb m)) :=
  (Work.Kunneth.singProdIso (TopCat.of B) (TopCat.of (Qb m))).hom

/-- **The pullback along the monoidal comparison** `H^n(Sing B ⊗ Sing Qb) → H^n(B × Qb)`. -/
def pullIso (m : ℕ) (B : Type) [TopologicalSpace B] (n : ℕ) :
    ↥((Work.Cohomology.cochainC ℤ (Work.Kunneth.sProd (ssB B) (ssB (Qb m)))).homology n)
      →ₗ[ℤ] Coh ℤ n (B × Qb m) :=
  Work.Kunneth.pullbackH (ssB (B × Qb m)) (Work.Kunneth.sProd (ssB B) (ssB (Qb m)))
    (iota m B) n

/-- The `i`-th summand of the family map, built from the simplicial cross product and transported
to degree `2k`. -/
def sqTerm (m : ℕ) (B : Type) [TopologicalSpace B] (k : ℕ)
    (i : {i : Fin m // (i : ℕ) ≤ k}) (x : Coh ℤ (2 * (k - (i : ℕ))) B) :
    ↥((Work.Cohomology.cochainC ℤ
      (Work.Kunneth.sProd (ssB B) (ssB (Qb m)))).homology (2 * k)) :=
  (by omega : 2 * (k - (i : ℕ)) + 2 * (i : ℕ) = 2 * k) ▸
    (Work.Kunneth.crossH (ssB B) (ssB (Qb m)) (2 * (k - (i : ℕ))) (2 * (i : ℕ)) x
      (Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore m) (i : ℕ)))

/-- **The family map built from the simplicial cross product** (even degrees). -/
def sqFam (m : ℕ) (B : Type) [TopologicalSpace B] (k : ℕ)
    (xf : (i : {i : Fin m // (i : ℕ) ≤ k}) → Coh ℤ (2 * (k - (i : ℕ))) B) :
    ↥((Work.Cohomology.cochainC ℤ
      (Work.Kunneth.sProd (ssB B) (ssB (Qb m)))).homology (2 * k)) :=
  ∑ i, sqTerm m B k i (xf i)

/-- The `i`-th summand of the family map built from the simplicial cross product, transported to
odd degree `2k+1`. -/
def sqTermOdd (m : ℕ) (B : Type) [TopologicalSpace B] (k : ℕ)
    (i : {i : Fin m // (i : ℕ) ≤ k}) (x : Coh ℤ (2 * k + 1 - 2 * (i : ℕ)) B) :
    ↥((Work.Cohomology.cochainC ℤ
      (Work.Kunneth.sProd (ssB B) (ssB (Qb m)))).homology (2 * k + 1)) :=
  (by omega : 2 * k + 1 - 2 * (i : ℕ) + 2 * (i : ℕ) = 2 * k + 1) ▸
    (Work.Kunneth.crossH (ssB B) (ssB (Qb m)) (2 * k + 1 - 2 * (i : ℕ)) (2 * (i : ℕ)) x
      (Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore m) (i : ℕ)))

/-- **The family map built from the simplicial cross product** (odd degrees). -/
def sqFamOdd (m : ℕ) (B : Type) [TopologicalSpace B] (k : ℕ)
    (xf : (i : {i : Fin m // (i : ℕ) ≤ k}) → Coh ℤ (2 * k + 1 - 2 * (i : ℕ)) B) :
    ↥((Work.Cohomology.cochainC ℤ
      (Work.Kunneth.sProd (ssB B) (ssB (Qb m)))).homology (2 * k + 1)) :=
  ∑ i, sqTermOdd m B k i (xf i)

/-! ## The Künneth collapse of the point factor -/

/-- The dependent family of Künneth summands `(p,q) ↦ H^p(X) ⊗ H^q(Y)` over the bidegree index
type `tpIdx n`. -/
noncomputable abbrev ks (X Y : SSet) (n : ℕ) : Work.Kunneth.tpIdx n → Type _ :=
  fun rs => Work.Kunneth.cohomSummand X Y rs.1.1 rs.1.2

/-- **The element of the Künneth target supported at a single bidegree.** -/
noncomputable def kSingle (X Y : SSet) (n : ℕ) (pq : Work.Kunneth.tpIdx n)
    (x : ks X Y n pq) : ↥(Work.Kunneth.kunnethTarget X Y n) :=
  fun rs => if h : rs = pq then h ▸ x else 0

theorem kSingle_self (X Y : SSet) (n : ℕ) (pq : Work.Kunneth.tpIdx n) (x : ks X Y n pq) :
    kSingle X Y n pq x pq = x := by
  rw [kSingle]; exact dif_pos rfl

theorem kSingle_of_ne (X Y : SSet) (n : ℕ) {pq rs : Work.Kunneth.tpIdx n} (h : rs ≠ pq)
    (x : ks X Y n pq) : kSingle X Y n pq x rs = 0 := by
  rw [kSingle]; exact dif_neg h

/-- The `i`-th summand of the "diagonal" family map into the Künneth target: the element supported
at the bidegree `(2(k-i), 2i)` with value `x ⊗ ζ^i`. -/
def thetaTerm (m : ℕ) (B : Type) [TopologicalSpace B] (k : ℕ)
    (i : {i : Fin m // (i : ℕ) ≤ k}) (x : Coh ℤ (2 * (k - (i : ℕ))) B) :
    ↥(Work.Kunneth.kunnethTarget (ssB B) (ssB (Qb m)) (2 * k)) :=
  kSingle (ssB B) (ssB (Qb m)) (2 * k)
    ⟨(2 * (k - (i : ℕ)), 2 * (i : ℕ)), by have := i.2; omega⟩
    (x ⊗ₜ[ℤ] Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore m) (i : ℕ))

/-- **The "diagonal" family map into the Künneth target** (even degrees). -/
def theta (m : ℕ) (B : Type) [TopologicalSpace B] (k : ℕ)
    (xf : (i : {i : Fin m // (i : ℕ) ≤ k}) → Coh ℤ (2 * (k - (i : ℕ))) B) :
    ↥(Work.Kunneth.kunnethTarget (ssB B) (ssB (Qb m)) (2 * k)) :=
  ∑ i, thetaTerm m B k i (xf i)

/-- The `i`-th summand of the "diagonal" family map, in odd degrees. -/
def thetaTermOdd (m : ℕ) (B : Type) [TopologicalSpace B] (k : ℕ)
    (i : {i : Fin m // (i : ℕ) ≤ k}) (x : Coh ℤ (2 * k + 1 - 2 * (i : ℕ)) B) :
    ↥(Work.Kunneth.kunnethTarget (ssB B) (ssB (Qb m)) (2 * k + 1)) :=
  kSingle (ssB B) (ssB (Qb m)) (2 * k + 1)
    ⟨(2 * k + 1 - 2 * (i : ℕ), 2 * (i : ℕ)), by have := i.2; omega⟩
    (x ⊗ₜ[ℤ] Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore m) (i : ℕ))

/-- **The "diagonal" family map into the Künneth target** (odd degrees). -/
def thetaOdd (m : ℕ) (B : Type) [TopologicalSpace B] (k : ℕ)
    (xf : (i : {i : Fin m // (i : ℕ) ≤ k}) → Coh ℤ (2 * k + 1 - 2 * (i : ℕ)) B) :
    ↥(Work.Kunneth.kunnethTarget (ssB B) (ssB (Qb m)) (2 * k + 1)) :=
  ∑ i, thetaTermOdd m B k i (xf i)

end

end Work.Kunneth.Asm
