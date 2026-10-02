import Mathlib
import Submission.Work.ELAssembly.Defs
import Submission.Work.ELAssembly.Instantiate
import Submission.Work.ELNest.Defs
import Submission.Work.SeedDyn.PortraitCount.portraitCount_of_ne_zero
import Submission.Work.SeedDyn.PortraitCount.noRayAtCritValue_of_flower
import Submission.Work.ELRig.Pa_subset_K
import Submission.Work.ELPull.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELAssembly

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)
open Filter

/-! ## The critical-value portrait count from the `ELNest` flower datum

`Work.SeedDyn.PortraitCount.noRayAtCritValue_of_flower` (and hence
`Work.PortraitCount.portraitCount_of_flower`) uses only three fields of the Leau--Fatou flower:

* `fl.Pa` and `fl.isOpen_Pa` -- the petal is open;
* `fl.tendsto_Pa` -- the `F c`-orbit of a point of `Pa` converges to `z₁`, whence `Pa ⊆ K c`.

The datum actually carried by the assembly is `Work.ELNest.FlowerData c z₁`, which is the
*specialised* form of `Work.FatouCoord.ParabolicFlower (F c) (G c) z₁` obtained by
`Work.ELNest.FlowerData.ofFatouCoord`: it drops `Ψ_diff` and the antiholomorphy of the chart,
which the nest arguments never use.  The two lemmas below re-run the argument on this datum. -/

/-- **The attracting petal lies in the filled Julia set**, from the specialised flower datum.
Identical to `Work.ELRig.Pa_subset_K`, but reading `fl.tendsto_Pa` off a
`Work.ELNest.FlowerData` (whose `F` is `Work.EL.F` up to definitional unfolding). -/
theorem Pa_subset_K_of_flowerData {c z₁ : ℂ} (fl : Work.ELNest.FlowerData c z₁) :
    fl.Pa ⊆ Work.EL.K c := by
  intro z hz
  have hiter : ∀ n : ℕ, (Work.ELNest.F c)^[n] z = (Tantibar c)^[10 * n] z := by
    intro n
    rw [Work.ELNest.F_eq_tantibar, Function.iterate_mul]
  have hsub : Tendsto (fun n : ℕ => (Tantibar c)^[10 * n] z) atTop (nhds z₁) :=
    Tendsto.congr' (Eventually.of_forall fun n => hiter n) (fl.tendsto_Pa z hz)
  exact Work.ELRig.boundedOrbit_of_tendsto_iterate_mul (by norm_num) hsub

/-- **No external ray lands at the critical value**, from the specialised flower datum.
Because `Pa ⊆ K c` is open and `(F c)^[N] c ∈ Pa` for some `N`, a whole neighbourhood of `c` is
mapped into `K c`; backward invariance of `K c` (`boundedOrbit_of_iterate_Tantibar`) then gives
`c ∈ interior (K c)`, while a landing point of a ray is never an interior point of `K c`
(`landsN_notMem_interior`). -/
theorem noRayAtCritValue_of_flowerData {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.ELNest.FlowerData c d.z₁)
    (henter : ∃ N : ℕ, (Work.ELNest.F c)^[N] c ∈ fl.Pa) :
    ∀ θ : ℝ, ¬ Work.EL.LandsN d.hN θ c := by
  have hPaK : fl.Pa ⊆ Work.EL.K c := Pa_subset_K_of_flowerData fl
  have hcint : c ∈ interior (Work.EL.K c) := by
    obtain ⟨N, hNmem⟩ := henter
    have hcont : Continuous ((Work.ELNest.F c)^[N]) := (Work.ELNest.continuous_F c).iterate N
    have hopen : IsOpen (((Work.ELNest.F c)^[N]) ⁻¹' fl.Pa) := fl.isOpen_Pa.preimage hcont
    refine interior_maximal ?_ hopen hNmem
    intro z hz
    have hPK : Work.ParamRays.BoundedOrbit c ((Work.ELNest.F c)^[N] z) := hPaK hz
    have he : (Work.ELNest.F c)^[N] z = (Tantibar c)^[10 * N] z := by
      rw [Work.ELNest.F_eq_tantibar, Function.iterate_mul]
    have hb : Work.ParamRays.BoundedOrbit c ((Tantibar c)^[10 * N] z) := he ▸ hPK
    exact Work.SeedDyn.PortraitCount.boundedOrbit_of_iterate_Tantibar hb
  intro θ hland
  exact Work.SeedDyn.PortraitCount.landsN_notMem_interior d.hN hland hcint

-- Shell: `namespace Work.ELAssembly` (area `Submission/Work/ELAssembly/`).
/-- **The orbit-portrait count from the `ELNest` flower datum.**  `Work.SeedDyn`'s
`portraitCount_of_flower` derives `Work.ELPull.PortraitCount (Work.ELAssembly.hNcanOf d)` from a
`Work.FatouCoord.ParabolicFlower` whose petal is entered by the critical orbit; the nest's flower
`Work.ELNest.FlowerData` (`Pa`, `isOpen_Pa`, `tendsto_Pa`, `enters_Pa` with `F c = (Tsq c)^[5]`)
carries precisely what that proof uses (rerun the ~50-line argument: petal ⊆ `K c` from
`tendsto_Pa`, `c ∈ interior (K c)`, no ray lands at `c`, then `portraitCount_of_ne_zero` away from
`0`), so the count can be obtained from it directly.  The entry hypothesis is
`fl.enters_Pa c d.crit.1 d.crit.2 : ∃ N, (F c)^[N] c ∈ fl.Pa`.  Consequence: the portrait count
is *derived* from the bundle's flower (`AssemblyInputs.fl`). -/
theorem portraitCount_of_flowerData {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.ELNest.FlowerData c d.z₁) :
    Work.ELPull.PortraitCount (hNcanOf d) := by
  -- no ray lands at the critical value, in the `ELPull` vocabulary of the adapted Böttcher data
  have hnrcEL : ∀ θ : ℝ, ¬ Work.EL.LandsN d.hN θ c :=
    noRayAtCritValue_of_flowerData d fl (fl.enters_Pa c d.crit.1 d.crit.2)
  have hnrc : ∀ θ : ℝ, ¬ Work.ELPull.LandsN (Work.PortraitCount.elDynB d) θ c := fun θ h =>
    hnrcEL θ ((Work.PortraitCount.landsN_elDynB d θ c).mp h)
  -- `hNcanOf d` is by definition the adapted Böttcher datum of `SeedDyn`
  exact Work.PortraitCount.portraitCount_of_noRayAtCritValue (Work.PortraitCount.elDynB d) hnrc

end Work.ELAssembly
