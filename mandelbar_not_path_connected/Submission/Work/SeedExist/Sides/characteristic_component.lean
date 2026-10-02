import Mathlib
import Submission.Work.SeedExist.Setup
import Submission.Work.SeedExist.Pairs
import Submission.Work.Normal.All
import Submission.Work.FQC.transfer_parabolic_aux
import Submission.Work.ELRig.Defs
import Submission.Work.Final.RootArc
import Submission.Work.ELPull.tantibar_openMap
import Submission.Work.SeedExist.Sides.mapsTo_seed_U
import Submission.Work.SeedExist.Sides.notMem_interior_of_flower

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Function Set
open scoped Topology

set_option linter.unusedVariables false

noncomputable section

namespace Work.SeedExist.Sides

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## 1. The fixed point of the flower at the seed

The parabolic flower `fl` couples `F c = (T_c)^[10]` with the antiholomorphic square root
`g = (T_c)^[5]`.  The repelling coordinate `Ψ` (whose field `Ψ_anti` reads
`Ψ (w̄ + 1/2) = g (Ψ w)`) has `Ψ w → z₁` as `Re w → -∞`; evaluating the anticommutation on the
real axis and passing to the limit gives `g z₁ = z₁`. -/

theorem Tantibar_five_fix_of_flower {c z₁ : ℂ}
    (fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.EL.F c) ((Tantibar c)^[5]) z₁) :
    (Tantibar c)^[5] z₁ = z₁ := by
  set g : ℂ → ℂ := (Tantibar c)^[5] with hg
  have hcont : Continuous g := by
    have htan : Continuous (Tantibar c) := by
      have hfun : (Tantibar c) = fun z : ℂ => star z ^ 2 + c := rfl
      rw [hfun]; fun_prop
    rw [hg]; exact htan.iterate 5
  -- on the real axis, `Ψ_anti` says `Ψ t = g (Ψ (t - 1/2))`
  have hreal : ∀ t : ℝ, fl.Ψ (t : ℂ) = g (fl.Ψ ((t - 1 / 2 : ℝ) : ℂ)) := by
    intro t
    have h := fl.Ψ_anti (((t - 1 / 2 : ℝ)) : ℂ)
    simpa using h
  -- `Ψ` converges to `z₁` along the real axis
  have hΨ : Tendsto (fun t : ℝ => fl.Ψ (t : ℂ)) atBot (nhds z₁) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨R, hR⟩ := fl.Ψ_small ε hε
    filter_upwards [eventually_lt_atBot (-R)] with b hb
    have hlt : ((b : ℂ)).re < -R := by simpa using hb
    have := (hR (b : ℂ) hlt).2
    simpa [dist_eq_norm] using this
  have hshift : Tendsto (fun t : ℝ => t - 1 / 2) atBot atBot := by
    rw [tendsto_atBot]
    intro b
    filter_upwards [eventually_lt_atBot (b + 1 / 2)] with t ht
    linarith
  have h1 : Tendsto (fun t : ℝ => g (fl.Ψ ((t - 1 / 2 : ℝ) : ℂ))) atBot (nhds (g z₁)) :=
    (hcont.tendsto z₁).comp (hΨ.comp hshift)
  have h2 : Tendsto (fun t : ℝ => fl.Ψ (t : ℂ)) atBot (nhds (g z₁)) :=
    h1.congr' (Eventually.of_forall fun t => (hreal t).symm)
  exact (tendsto_nhds_unique hΨ h2).symm

/-- The centre of the flower is fixed by the second return map `F c = (T_c)^[10]`. -/
theorem F_fix_of_flower {c z₁ : ℂ}
    (fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.EL.F c) ((Tantibar c)^[5]) z₁) :
    Work.EL.F c z₁ = z₁ :=
  Work.Final.Tantibar_five_fix (Tantibar_five_fix_of_flower fl)

/-! ## 2. The characteristic component lies in the wake side -/

/-- **The characteristic component avoids the pair curve.**  The two rays of the pair lie off
`K c` and `z₁ ∉ interior (K c)`; hence `U c ⊆ interior (K c)` avoids the curve, and — being
connected and containing `c ∈ wakeSide` — it lies in the wake side. -/
theorem subset_wakeSide_of_notMem_interior {c z₁ : ℂ} {φ : ℂ → ℂ}
    (hN : Work.EL.DynB c φ) (hz : z₁ ∉ interior (Work.EL.K c))
    (hc : c ∈ Work.SeedExist.wakeSide hN z₁ 0) :
    Work.SeedExist.U c ⊆ Work.SeedExist.wakeSide hN z₁ 0 := by
  by_cases hcint : c ∈ interior (Work.EL.K c)
  · have hcU : c ∈ Work.SeedExist.U c := mem_connectedComponentIn hcint
    have hpre : IsPreconnected (Work.SeedExist.U c) := isPreconnected_connectedComponentIn
    have hcomp : Work.SeedExist.U c ⊆
        connectedComponentIn (Work.EL.RawPair.curve hN (Work.SeedExist.alphaPair c z₁ 0))ᶜ c := by
      refine IsPreconnected.subset_connectedComponentIn hpre hcU ?_
      intro z hzU
      rw [Set.mem_compl_iff]
      intro hzC
      have hzK : z ∈ Work.EL.K c := interior_subset (connectedComponentIn_subset _ _ hzU)
      rw [Work.EL.RawPair.curve] at hzC
      simp only [Set.mem_union, Set.mem_singleton_iff] at hzC
      rcases hzC with (h | h) | h
      · exact (Work.EL.paramRay_subset_compl hN _ h) hzK
      · have hzU' : z ∈ interior (Work.EL.K c) := connectedComponentIn_subset _ _ hzU
        rw [show (Work.SeedExist.alphaPair c z₁ 0).y = z₁ from rfl] at h
        rw [h] at hzU'
        exact hz hzU'
      · exact (Work.EL.paramRay_subset_compl hN _ h) hzK
    have hS : Work.SeedExist.wakeSide hN z₁ 0 =
        connectedComponentIn (Work.EL.RawPair.curve hN (Work.SeedExist.alphaPair c z₁ 0))ᶜ c := by
      rw [show Work.SeedExist.wakeSide hN z₁ 0 =
          Work.EL.RawPair.sideThrough hN (Work.SeedExist.alphaPair c z₁ 0)
            (Work.EL.wakeLo 0) (Work.EL.wakeHi 0) from rfl]
      exact connectedComponentIn_eq hc
    rw [hS]
    exact hcomp
  · rw [Work.SeedExist.U, connectedComponentIn_eq_empty hcint]
    exact Set.empty_subset _



/-! ## 3. The characteristic component -/

/-- **The characteristic component of the critical value at the root seed.** -/
theorem characteristic_component {c : ℂ} (hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c))
    (hJ : Work.Top.JordanForm) {z₁ : ℂ}
    (fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.FSeed.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) z₁)
    (hfat : Work.SeedExist.FatouCritInBasin c z₁ fl.Pg)
    (hcS0 : c ∈ Work.SeedExist.wakeSide hN z₁ 0)
    (hW5 : ∀ j : ℕ, 1 ≤ j → j ≤ 4 → (LeanEval.ComplexAnalysis.Tantibar c)^[j] z₁ ∈ Work.SeedExist.Snear hN z₁)
    (hg : (LeanEval.ComplexAnalysis.Tantibar c)^[5] z₁ = z₁)
    (hex : ∀ j : ℕ, 0 < j → j < 5 → (LeanEval.ComplexAnalysis.Tantibar c)^[j] z₁ ≠ z₁) :
    Work.SeedExist.U c ⊆ Work.SeedExist.wakeSide hN z₁ 0 ∧
      Set.MapsTo ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) (Work.SeedExist.U c) (Work.SeedExist.U c) ∧
      Set.MapsTo ((LeanEval.ComplexAnalysis.Tantibar c)^[4]) (Work.SeedExist.U c) (Work.SeedExist.U₀ c) := by
  have hfix : Work.EL.F c z₁ = z₁ := F_fix_of_flower fl
  have hz : z₁ ∉ interior (Work.EL.K c) := notMem_interior_of_flower fl hfix
  have hmap := mapsTo_seed_U fl hfat
  exact ⟨subset_wakeSide_of_notMem_interior hN hz hcS0, hmap.1, hmap.2⟩

end Work.SeedExist.Sides
