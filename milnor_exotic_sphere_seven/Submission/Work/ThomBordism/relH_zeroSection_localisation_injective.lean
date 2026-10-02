import Mathlib
import Submission.Work.ThomBordism.Interface
import Submission.Work.ThomBordism.localGenDefs
import Submission.Work.ThomBordism.localGenAux
import Submission.Work.ThomBordism.compactZero_free
import Submission.Work.ThomBordism.isCoordBall_restrict_iso_free
import Submission.Work.ThomBordism.chartedSpaceTotalSpace
import Submission.Work.ThomBordism.relHZeroSectionAux
import Submission.Work.ThomBordism.relHmap_eq_zero_of_eq_zero_at
import Submission.Work.Tubular.PuncturedDiscPair.t2Space_sphSub

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Injectivity of the localisation at a point of the zero section

For a real bundle `Z` over a closed oriented `8`-manifold `V` (with connected `V`, `k ≥ 1`) the
top relative homology `H_{k+8}(E, E∖0)` of the Thom pair localises injectively at any point of the
zero section:
`β ∈ H_{k+8}(E, E∖σV)` with `β` mapping to `0` in `H_{k+8}(E, E∖{p})` for one `p ∈ σV` is `0`.

The zero section is homeomorphic to the compact path-connected `V`, hence compact and
preconnected; the localisation at a point is locally constant in the point (the restriction out of
a coordinate ball is an isomorphism), so it vanishes at every point of the zero section
(`Work.ThomBordism.relHmap_eq_zero_of_eq_zero_at`), and then `Work.ThomBordism.compactZero_free`
(Hatcher 3.27(a)) applies.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.ThomBordism

noncomputable section

theorem relH_zeroSection_localisation_injective {V : Work.ThomBordism.Man8} {k : ℕ} {ι : Type}
    {hk : 1 ≤ k}
    (Z : Work.TangentClasses.RealBundle V.pt (Fin k → ℝ) ι) [PathConnectedSpace V.pt]
    (x : V.pt)
    (β : Work.ThomBordism.RelH (TopCat.of Z.TotalSpace) (k + 8)
      (Set.range (Work.Thom.zeroSection Z)))
    (hβ : Work.ThomBordism.RelHmap (TopCat.of Z.TotalSpace) (k + 8)
      (Set.singleton_subset_iff.mpr (Set.mem_range_self x)) β = 0) : β = 0 := by
  classical
  -- the total space is Hausdorff and carries the trivialising charts of the bundle
  haveI hT2 : T2Space Z.TotalSpace := Work.Tubular.PuncturedDiscPair.t2Space_totalSpace Z
  let Ψ : EuclideanSpace ℝ (Fin (k + 8)) ≃ₜ (EuclideanSpace ℝ (Fin 8) × (Fin k → ℝ)) :=
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr (Nat.add_comm k 8))).toHomeomorph).trans
      (((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 8) (m := k)).toHomeomorph).trans
        (Homeomorph.prodCongr (Homeomorph.refl _)
          (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin k => ℝ)).toHomeomorph))
  haveI hCh : ChartedSpace (EuclideanSpace ℝ (Fin (k + 8))) Z.TotalSpace :=
    bundleChartedSpace Z Ψ
  -- the zero section is compact (the base does) and preconnected (the base is path connected)
  have hAc : IsCompact (Set.range (Work.Thom.zeroSection Z)) :=
    isCompact_range (Work.Thom.zeroSection Z).continuous
  have hpre : IsPreconnected (Set.range (Work.Thom.zeroSection Z)) :=
    isPreconnected_range (Work.Thom.zeroSection Z).continuous
  -- the local class vanishes at every point of the zero section
  have hall := relHmap_eq_zero_of_eq_zero_at (n := k + 8) (by omega) hAc hpre β
    (Set.mem_range_self x) hβ
  exact compactZero_free (by omega) hAc β (fun y hy => hall y hy)

end

end Work.ThomBordism
