/-
# `ELAssembly.Derived.AssemblyFields` — the derived fields of `NestData.ofInputs`

This file collects, in the vocabulary of the bundle `Work.ELAssembly.AssemblyInputs`, the facts
that the bundle's certificate `cert` no longer has to carry:

* `Work.ELAssembly.cut_mem_of_inputs` — the cut points lie in the arms of the tripod, and
  `Work.ELAssembly.cut_ne_of_inputs` — they are pairwise distinct;
* `Work.ELAssembly.D_adm_of_inputs` — the three-pair lists are admissible;
* `Work.ELAssembly.b2_mem_D_of_inputs` — `b₂` lies in every level of the nest at `b₂`;
* `Work.ELAssembly.Dnest_sub_of_inputs` — that nest is decreasing;
* `Work.ELAssembly.Qp_disj_of_inputs` — the pair curves of the `z₁`-nest are pairwise disjoint
  (from the two-ray portraits of all levels, `Work.ELAssembly.Qp_portrait`, whose inputs are the
  bundle's portrait `hzero`, the orbit-portrait count of the flower and the certificate
  arithmetic `Qp_y_shift`/`base_shift_of`).

With `Work.ELAssembly.Dnest_cl_of` (the strict nesting at level `1`) the certificate
`CertGeometry` is now *empty*: the structure has been deleted and `AssemblyInputs` carries no
certificate field at all (see `NOTES.md` §0.5/§0.6).
-/
import Mathlib
import Submission.Work.ELAssembly.Inputs
import Submission.Work.ELAssembly.Derived.Fields
import Submission.Work.ELAssembly.Derived.QpDisj
import Submission.Work.ELAssembly.Qp_portrait
import Submission.Work.ELAssembly.portraitCount_of_flowerData

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false

noncomputable section

namespace Work.ELAssembly

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

variable {c : ℂ} {d : Work.EL.RootParabolic c} {fl : Work.ELNest.FlowerData c d.z₁}

/-- **The cut points of the bundle lie in the arms of the tripod** (the fields
`CertGeometry.cutA_mem`/`cutB_mem`/`cutC_mem`, derived). -/
theorem cut_mem_of_inputs (A : AssemblyInputs c d fl) :
    (∀ n : ℕ, ((NestPairs.ofChains (chainInputs_of d A.hzero)).Za n).y
        ∈ Work.EL.Tripod.armA A.T) ∧
    (∀ n : ℕ, ((NestPairs.ofChains (chainInputs_of d A.hzero)).Zb n).y
        ∈ Work.EL.Tripod.armB A.T) ∧
    (∀ n : ℕ, ((NestPairs.ofChains (chainInputs_of d A.hzero)).Zc n).y
        ∈ Work.EL.Tripod.armC A.T) :=
  cut_mem_of d (NestPairs.ofChains (chainInputs_of d A.hzero)) A.T

/-- **The cut points of the bundle are pairwise distinct**. -/
theorem cut_ne_of_inputs (A : AssemblyInputs c d fl) :
    (∀ n : ℕ, ((NestPairs.ofChains (chainInputs_of d A.hzero)).Za n).y
        ≠ ((NestPairs.ofChains (chainInputs_of d A.hzero)).Zb n).y) ∧
    (∀ n : ℕ, ((NestPairs.ofChains (chainInputs_of d A.hzero)).Zb n).y
        ≠ ((NestPairs.ofChains (chainInputs_of d A.hzero)).Zc n).y) ∧
    (∀ n : ℕ, ((NestPairs.ofChains (chainInputs_of d A.hzero)).Zc n).y
        ≠ ((NestPairs.ofChains (chainInputs_of d A.hzero)).Za n).y) :=
  cut_ne_of d (NestPairs.ofChains (chainInputs_of d A.hzero)) A.T

/-- **The three-pair lists of the bundle are admissible**. -/
theorem D_adm_of_inputs (A : AssemblyInputs c d fl) :
    ∀ n : ℕ, Work.EL.PolyAdmissible
      [(NestPairs.ofChains (chainInputs_of d A.hzero)).Za n,
       (NestPairs.ofChains (chainInputs_of d A.hzero)).Zb n,
       (NestPairs.ofChains (chainInputs_of d A.hzero)).Zc n] :=
  D_adm_of' d (NestPairs.ofChains (chainInputs_of d A.hzero)) A.T

/-- **`b₂` lies in every level of the nest at `b₂`** (the field `CertGeometry.b2_mem_D`,
derived). -/
theorem b2_mem_D_of_inputs (A : AssemblyInputs c d fl) :
    ∀ n : ℕ, A.T.y ∈ Work.EL.polyRegion
      [(NestPairs.ofChains (chainInputs_of d A.hzero)).Za n,
       (NestPairs.ofChains (chainInputs_of d A.hzero)).Zb n,
       (NestPairs.ofChains (chainInputs_of d A.hzero)).Zc n]
      (Work.ELNest.Dlev A.L n) :=
  b2_mem_D_of d (NestPairs.ofChains (chainInputs_of d A.hzero)) A.T A.hL

/-- **The nest at `b₂` is decreasing** (the field `CertGeometry.Dnest_sub`, derived). -/
theorem Dnest_sub_of_inputs (A : AssemblyInputs c d fl) :
    ∀ n : ℕ, Work.EL.polyRegion
        [(NestPairs.ofChains (chainInputs_of d A.hzero)).Za (n + 1),
         (NestPairs.ofChains (chainInputs_of d A.hzero)).Zb (n + 1),
         (NestPairs.ofChains (chainInputs_of d A.hzero)).Zc (n + 1)]
        (Work.ELNest.Dlev A.L (n + 1))
      ⊆ Work.EL.polyRegion
        [(NestPairs.ofChains (chainInputs_of d A.hzero)).Za n,
         (NestPairs.ofChains (chainInputs_of d A.hzero)).Zb n,
         (NestPairs.ofChains (chainInputs_of d A.hzero)).Zc n]
        (Work.ELNest.Dlev A.L n) :=
  Dnest_sub_of' d (NestPairs.ofChains (chainInputs_of d A.hzero)) A.T A.hL

/-- **The exact orbit portrait at every level of the `z₁`-nest**, from the bundle. -/
theorem Qp_portrait_of_inputs (A : AssemblyInputs c d fl) (n : ℕ) :
    ∀ θ : ℝ, θ ∈ Set.Ico 0 1 →
      (Work.EL.LandsN d.hN θ ((NestPairs.ofChains (chainInputs_of d A.hzero)).Qp n).y ↔
        θ = Work.ELNest.bAng n ∨ θ = Work.ELNest.bAng' n) :=
  Qp_portrait d (NestPairs.ofChains (chainInputs_of d A.hzero))
    (portraitCount_of_flowerData d fl)
    (cycle_lands d A.hzero (portraitCount_of_flowerData d fl) 4 (by norm_num))
    (Qp_y_shift d (NestPairs.ofChains (chainInputs_of d A.hzero)))
    (base_shift_of d (NestPairs.ofChains (chainInputs_of d A.hzero))) n

/-- **The pair curves of the `z₁`-nest are pairwise disjoint** (the field
`CertGeometry.Qp_disj`, derived). -/
theorem Qp_disj_of_inputs (A : AssemblyInputs c d fl) :
    ∀ m n : ℕ, m ≠ n →
      Disjoint (Work.EL.pairCurve ((NestPairs.ofChains (chainInputs_of d A.hzero)).Qp m))
        (Work.EL.pairCurve ((NestPairs.ofChains (chainInputs_of d A.hzero)).Qp n)) :=
  fun _ _ hmn => Qp_pairCurve_disjoint_of_portrait
    (NestPairs.ofChains (chainInputs_of d A.hzero))
    (fun k θ hθ => Qp_portrait_of_inputs A k θ hθ) hmn

end Work.ELAssembly
