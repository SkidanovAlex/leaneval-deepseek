import Mathlib
import Submission.Work.ThomBordism.Grassmann.Model
import Submission.Work.ThomBordism.Grassmann.ThomTarget
import Submission.Work.ThomBordism.Grassmann.Torsion.thomSpaceCohomologyIso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The rational cohomology of the Thom **space** in low degrees (item 2, space half)

Item 2 of the chapter states `H^{k+j}(T;ℚ)` for `j ≤ 8` (vanishing in `j ∈ lowDegrees`, and the
classes `p₁(γ)²⌣U`, `p₂(γ)⌣U` as a basis in degree `k+8`), where `T = Th γ`.  The *pair*-level
statement (`ThomPairCohomology`, `thomPairCohomology_of_lowDegree`) is proved; the passage from the
pair to the space is the excision/good-pair comparison
`Work.ThomBordism.Grassmann.Torsion.thomSpaceCohomologyIso` (proved), which is a *non-canonical*
`Nonempty` statement, so the comparison is fixed here once and for all as
`thomSpaceIso` (a `Classical.choice`), and the classes and the basis map of the space are the
transports of those of the pair.

## Main declarations

* `thomSpaceIso` — the canonical comparison `H^n(Dγ,Sγ;ℤ) ≅ H^n(Th γ;ℤ)`;
* `thomSpaceP1SqU`, `thomSpaceP2U` — `p₁(γ)²⌣U` and `p₂(γ)⌣U` in `H^{k+8}(Th γ;ℤ)`;
* `thomSpaceBasisMap` — `(a,b) ↦ a • p₁(γ)²⌣U + b • p₂(γ)⌣U`, rationally;
* `ThomSpaceCohomology` — the target `Prop`: the vanishing in low degrees and the bijectivity of
  `thomSpaceBasisMap` (the "basis `p₁²U, p₂U`" of item 2).
-/

open scoped Topology TensorProduct
open Work.TangentClasses

namespace Work.ThomBordism.Grassmann

noncomputable section

/-- **The canonical comparison `H^n(Dγ, Sγ;ℤ) ≅ H^n(Th γ;ℤ)`** (§4ter, `thomSpaceCohomologyIso`),
fixed as a `Classical.choice`. -/
noncomputable def thomSpaceIso (k m n : ℕ) (hn : 1 ≤ n) :
    Work.Thom.OpenThom (tautologicalBundle k m) n ≃ₗ[ℤ]
      (Work.Cohomology.cochainC ℤ (sset (TautologicalThomSpace k m))).homology n :=
  (Classical.choice (Torsion.thomSpaceCohomologyIso k m n hn)).symm

/-- `p₁(γ)² ⌣ U ∈ H^{k+8}(Th γ;ℤ)`: the transport of `p₁(γ)² ⌣ U` along the canonical comparison
`thomSpaceIso` (in the index convention `8 + k` of `thomBasisMap`). -/
noncomputable def thomSpaceP1SqU (k m : ℕ)
    (U : Work.Thom.ThomClass (tautologicalBundle k m) k) :
    (Work.Cohomology.cochainC ℤ (sset (TautologicalThomSpace k m))).homology (8 + k) :=
  (thomSpaceIso k m (8 + k) (by omega))
    (Work.Thom.thomMap (tautologicalBundle k m) k U.τ 8 (p1Sq k m))

/-- `p₂(γ) ⌣ U ∈ H^{k+8}(Th γ;ℤ)`: the transport of `p₂(γ) ⌣ U` along the canonical comparison. -/
noncomputable def thomSpaceP2U (k m : ℕ)
    (U : Work.Thom.ThomClass (tautologicalBundle k m) k) :
    (Work.Cohomology.cochainC ℤ (sset (TautologicalThomSpace k m))).homology (8 + k) :=
  (thomSpaceIso k m (8 + k) (by omega))
    (Work.Thom.thomMap (tautologicalBundle k m) k U.τ 8 (p2 k m))

/-- **The rationalised basis map of the Thom space**: `(a,b) ↦ a • p₁(γ)²⌣U + b • p₂(γ)⌣U`. -/
noncomputable def thomSpaceBasisMap (k m : ℕ)
    (U : Work.Thom.ThomClass (tautologicalBundle k m) k) :
    ℚ × ℚ → Work.SignatureBordism.ratCohomology (8 + k) (sset (TautologicalThomSpace k m)) :=
  fun p => p.1 • ((1 : ℚ) ⊗ₜ[ℤ] (thomSpaceP1SqU k m U))
    + p.2 • ((1 : ℚ) ⊗ₜ[ℤ] (thomSpaceP2U k m U))

/-- **The rational cohomology of the Thom space in low degrees and the basis `p₁²U`, `p₂U`.**

This is item 2's space-level statement: `H^{k+j}(Th γ;ℚ) = 0` for `j ∈ {1,2,3,5,6,7}` and the two
classes `p₁(γ)²⌣U`, `p₂(γ)⌣U` form a basis of `H^{k+8}(Th γ;ℚ)`. -/
def ThomSpaceCohomology (k m : ℕ)
    (U : Work.Thom.ThomClass (tautologicalBundle k m) k) : Prop :=
  (∀ j ∈ lowDegrees,
      Subsingleton (Work.SignatureBordism.ratCohomology (k + j)
        (sset (TautologicalThomSpace k m)))) ∧
    Function.Bijective (thomSpaceBasisMap k m U)

end

end Work.ThomBordism.Grassmann
