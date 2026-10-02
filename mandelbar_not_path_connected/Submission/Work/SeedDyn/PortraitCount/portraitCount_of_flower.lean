import Mathlib
import Submission.Work.SeedDyn.Defs
import Submission.Work.SeedDyn.PortraitCount.portraitCount_of_ne_zero
import Submission.Work.SeedDyn.PortraitCount.noRayAtCritValue_of_flower
import Submission.Work.ELPull.Defs
import Submission.Work.ELRig.Pa_subset_K
import Submission.Work.ELPull.pb1

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedDyn.PortraitCount

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)
open Filter

/-! ## The orbit-portrait count at a root-parabolic parameter whose critical orbit enters the petal

The orbit-portrait count `Work.ELPull.PortraitCount hN` asserts that whenever `y'` is a
`Tantibar c`-preimage of a point `y` at which exactly two external rays land, the angle-doubling
map `T` is injective on the angles of the rays landing at `y'`.

The unique preimage at which this can conceivably fail is the critical point `y' = 0`, whose
image is the critical value `c`.  There the hypothesis that `y = c` carries *two* rays is
contradicted by the flower datum `fl` and the entry hypothesis `henter`: because the critical
orbit enters the attracting petal `Pa ⊆ K c`, a whole neighbourhood of `c` is mapped into
`K c`, so `c` is an interior point of the filled Julia set, while no landing point of an
external ray is.  Off the critical point the count is exactly
`portraitCount_of_ne_zero` (which needs no flower: it uses only the local injectivity of
`Tantibar c` away from `0`). -/

/-- **A landing point is not an interior point of `K c`.**  The ray points of level `t > 1` all
lie outside `K c` (`NakaneData.rayPt_notMem`), and they converge to the landing point, so the
landing point lies in the closure of `(K c)ᶜ = (interior (K c))ᶜ`.

This is the `Work.ELPull` counterpart of `Work.SeedDyn.PortraitCount.landsN_notMem_interior`
(the two differ only in which Böttcher coordinate the Nakane datum carries). -/
theorem landsN_notMem_interior_pull {c : ℂ} (hN : Work.ELPull.DynB c)
    {θ : ℝ} {y : ℂ} (hland : Work.ELPull.LandsN hN θ y) :
    y ∉ interior (Work.ELPull.K c) := by
  have hcl : y ∈ closure ((Work.ELPull.K c)ᶜ) :=
    mem_closure_of_tendsto hland (by
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact hN.rayPt_notMem ht)
  intro hint
  obtain ⟨w, hw⟩ := mem_closure_iff.mp hcl (interior (Work.ELPull.K c)) isOpen_interior hint
  exact hw.2 (interior_subset hw.1)

/-- **No external ray lands at the critical value `c`.**  The attracting petal is contained in
the filled Julia set (`fl.Pa ⊆ K c`, from the convergence of the `F c`-orbit inside `Pa`), and
`Pa` is open; since some iterate of `F c` maps `c` into `Pa`, a neighbourhood of `c` is mapped
into `K c`, and backward invariance of `K c` (`boundedOrbit_of_iterate_Tantibar`) puts that
neighbourhood into `K c` itself.  Hence `c ∈ interior (K c)`, and a landing point is never an
interior point of `K c`. -/
theorem noRayAtCritValue_of_flower_pull {c z₁ : ℂ} (hN : Work.ELPull.DynB c)
    (fl : Work.FatouCoord.ParabolicFlower (Work.ELPull.F c) ((Tantibar c)^[5]) z₁)
    (henter : ∃ N : ℕ, (Work.ELPull.F c)^[N] c ∈ fl.Pa) :
    ∀ θ : ℝ, ¬ Work.ELPull.LandsN hN θ c := by
  -- the petal lies in the filled Julia set
  have hPaK : fl.Pa ⊆ Work.ELPull.K c := by
    intro z hz
    have hiter : ∀ n : ℕ, (Work.ELPull.F c)^[n] z = (Tantibar c)^[10 * n] z := by
      intro n
      rw [Work.ELPull.F_eq_iterate, Function.iterate_mul]
    have hsub : Tendsto (fun n : ℕ => (Tantibar c)^[10 * n] z) atTop (nhds z₁) :=
      Tendsto.congr' (Eventually.of_forall fun n => hiter n) (fl.tendsto_Pa z hz)
    exact Work.ELRig.boundedOrbit_of_tendsto_iterate_mul (by norm_num) hsub
  -- hence the critical value is an interior point of the filled Julia set
  have hcint : c ∈ interior (Work.ELPull.K c) := by
    obtain ⟨N, hNmem⟩ := henter
    have hTsq : Continuous (Work.Landing.Tsq c) := by
      rw [show Work.Landing.Tsq c = fun z => (z ^ 2 + star c) ^ 2 + c from rfl]
      fun_prop
    have hcont : Continuous ((Work.ELPull.F c)^[N]) := by
      rw [Work.ELPull.F]
      exact (hTsq.iterate 5).iterate N
    have hopen : IsOpen (((Work.ELPull.F c)^[N]) ⁻¹' fl.Pa) := fl.isOpen_Pa.preimage hcont
    refine interior_maximal ?_ hopen hNmem
    intro z hz
    have hPK : Work.ParamRays.BoundedOrbit c ((Work.ELPull.F c)^[N] z) := hPaK hz
    have he : (Work.ELPull.F c)^[N] z = (Tantibar c)^[10 * N] z := by
      rw [Work.ELPull.F_eq_iterate, Function.iterate_mul]
    have hb : Work.ParamRays.BoundedOrbit c ((Tantibar c)^[10 * N] z) := he ▸ hPK
    exact boundedOrbit_of_iterate_Tantibar hb
  intro θ hland
  exact landsN_notMem_interior_pull hN hland hcint

/-- **The orbit-portrait count at a parabolic parameter whose critical orbit enters the petal.**

Given a Leau–Fatou flower `fl` at the parabolic point `z₁` of `F c = (Tantibar c)^[10]` whose
attracting petal is entered by the critical orbit (`henter`), the dynamical orbit portrait of
`Tantibar c` satisfies the count `Work.ELPull.PortraitCount`: at every preimage `y'` of a
two-ray point `y`, at most one ray per ray of `y` lands at `y'`.

Indeed, for `y' ≠ 0` this is the local injectivity of `Tantibar c` off the critical point
(`portraitCount_of_ne_zero`), while for `y' = 0` one has `y = c`, and `c` carries *no* ray at
all by `noRayAtCritValue_of_flower_pull`, so the hypothesis that `y` carries two rays is
vacuous. -/
theorem portraitCount_of_flower {c z₁ : ℂ} (hN : Work.ELPull.DynB c)
    (fl : Work.FatouCoord.ParabolicFlower (Work.ELPull.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) z₁)
    (henter : ∃ N : ℕ, (Work.ELPull.F c)^[N] c ∈ fl.Pa) :
    Work.ELPull.PortraitCount hN := by
  have hnrc : ∀ θ : ℝ, ¬ Work.ELPull.LandsN hN θ c :=
    noRayAtCritValue_of_flower_pull hN fl henter
  intro y y' hyy' htwo θ' θ'' h' h'' l' l'' hT
  by_cases hy' : y' = 0
  · -- the critical point: its image is the critical value `c`, at which no ray lands
    exfalso
    obtain ⟨u, v, hu, hv, huv, hspec⟩ := htwo
    have hyc : y = c := by
      rw [← hyy', hy']
      simp [LeanEval.ComplexAnalysis.Tantibar]
    have hland : Work.ELPull.LandsN hN u c := hyc ▸ (hspec u hu).mpr (Or.inl rfl)
    exact hnrc u hland
  · -- off the critical point: local injectivity of `Tantibar c`
    exact Work.SeedDyn.PortraitCount.portraitCount_of_ne_zero hN
      (Work.ELPull.isDynBottcher_dynPhiOf_of_dynB' hN) hy' h' h'' l' l'' hT

end Work.SeedDyn.PortraitCount
