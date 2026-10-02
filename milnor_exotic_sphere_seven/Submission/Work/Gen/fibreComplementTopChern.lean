import Mathlib
import Submission.Work.Gen.CruxDefs
import Submission.Work.LerayHirsch.fibreQuotientComparison
import Submission.Work.Thom.chernClass_homeo

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Gen

open Work.TangentClasses Work.Thom

open scoped LinearAlgebra.Projectivization

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι]

/-- **Bookkeeping reduction.**  If the given complement `Q` of the tautological line bundle,
restricted to the fibre over `b`, is isomorphic to the restriction of the tautological *quotient*
`Work.LerayHirsch.quotientBundle Z` (a "canonical complement"), then the fibre-restriction of its
top Chern class is the universal multiple `modelK n` of the fibre's `ζⁿ`.

The proof is bookkeeping: naturality of the Chern classes, the comparison
`Work.LerayHirsch.fibreQuotientComparison`, the definition `Work.Gen.modelK_spec` of `modelK` and the
restriction `Work.LerayHirsch.CohMap_fibreIncl_zetaPow` of the powers of `ζ` to a fibre. -/
theorem fibreComplementTopChern_of_iso (n : ℕ) (hn : 1 ≤ n)
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (n + 1))) ι)
    (Q : VectorBundleCore ℂ (Work.LerayHirsch.ProjSpace Z) (EuclideanSpace ℂ (Fin n))
          (ι × Fin (n + 1)))
    (b : B)
    (h : Nonempty (BundleIso (bundleComap Q (Work.LerayHirsch.fibreIncl Z b))
                  (Work.LerayHirsch.qL Z b))) :
    (ModuleCat.Hom.hom (CohMap (Work.LerayHirsch.fibreIncl Z b) ℤ (2 * n)))
        (Work.Thom.chernClass n n Q)
      = Work.Gen.modelK n • (ModuleCat.Hom.hom
          (CohMap (Work.LerayHirsch.fibreIncl Z b) ℤ (2 * n)))
          (Work.LerayHirsch.zetaPow Z n) := by
  -- Step 1: pull the Chern class back to the fibre
  rw [← Work.Thom.chernClass_comap (m := n) (j := n) Q (Work.LerayHirsch.fibreIncl Z b)]
  -- Step 2: replace `Q` by the tautological quotient on the fibre
  obtain ⟨e⟩ := h
  rw [Work.Thom.chernClass_BundleIso _ _ e]
  -- unfold `qL`
  rw [show Work.LerayHirsch.qL Z b
        = bundleComap (Work.LerayHirsch.quotientBundle Z) (Work.LerayHirsch.fibreIncl Z b)
      from rfl]
  -- Step 3: the tautological quotient on a fibre is the model tautological quotient
  obtain ⟨e₂⟩ := Work.LerayHirsch.fibreQuotientComparison Z b
  rw [Work.Thom.chernClass_BundleIso _ _ e₂]
  -- unfold `fibreIdent`
  rw [show (bundleComap (Work.LerayHirsch.quotientBundle (Work.LerayHirsch.trivCore (n + 1)))
        ((Work.LerayHirsch.projUniv (n + 1)).comp (Work.LerayHirsch.projClassFibre Z b)))
        = bundleComap (Work.LerayHirsch.quotientBundle (Work.LerayHirsch.trivCore (n + 1)))
            (Work.Gen.fibreIdent Z b)
      from rfl]
  -- Step 4: naturality of the Chern classes for the trivial bundle
  rw [Work.Thom.chernClass_comap (m := n) (j := n)
      (Work.LerayHirsch.quotientBundle (Work.LerayHirsch.trivCore (n + 1)))
      (Work.Gen.fibreIdent Z b)]
  -- Step 5: `modelK` is defined so that this holds for the model quotient
  rw [Work.Gen.modelK_spec n, map_zsmul]
  -- Step 6: the restriction of the powers of `ζ` to the fibre
  exact congrArg (fun x => Work.Gen.modelK n • x)
    (Work.LerayHirsch.CohMap_fibreIncl_zetaPow Z b n).symm

end

end Work.Gen
