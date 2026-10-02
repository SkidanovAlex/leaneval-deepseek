import Mathlib
import Submission.Work.SeedExist.Setup
import Submission.Work.SeedExist.Pairs
import Submission.Work.ELTop.pairSides_decomposition
import Submission.Work.ELTop.isOpen_pairSide
import Submission.Work.ELRig.Defs
import Submission.Work.Final.RootArc

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedExist.Fatou

open Classical Filter Function Set
open scoped Topology

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- `Tantibar c` is continuous (it is the antiholomorphic polynomial `z ↦ (conj z)^2 + c`). -/
theorem continuous_tantibar_memPg (c : ℂ) : Continuous (Tantibar c) := by
  rw [show Tantibar c = fun z : ℂ => (starRingEnd ℂ) z ^ 2 + c from rfl]
  continuity

/-- The wake side at level `0` is the *far side* of the root pair `{α₁, α₂}` at `z₁`. -/
theorem wakeSide_zero_eq_pairSide {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) (z₁ : ℂ)
    (h1 : Work.EL.LandsN hN Work.EL.alpha1 z₁) (h2 : Work.EL.LandsN hN Work.EL.alpha2 z₁) :
    Work.SeedExist.wakeSide hN z₁ 0 = Work.EL.pairSide (Work.EL.alphaPair hN z₁ h1 h2) := by
  have hα : Work.EL.alpha1 ≤ Work.EL.alpha2 := by norm_num [Work.EL.alpha1, Work.EL.alpha2]
  simp only [Work.SeedExist.wakeSide, Work.SeedExist.alphaPair, Work.EL.alphaPair,
    Work.EL.pairSide, Work.EL.pairSideThroughArc, Work.EL.alphaPairRaw,
    Function.iterate_zero_apply, Work.SeedExist.wakeLo_zero, Work.SeedExist.wakeHi_zero]
  rw [min_eq_left hα, max_eq_right hα]

/-- The near side `Snear` is the *near side* of the root pair `{α₁, α₂}` at `z₁`. -/
theorem Snear_eq_pairSideNear {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) (z₁ : ℂ)
    (h1 : Work.EL.LandsN hN Work.EL.alpha1 z₁) (h2 : Work.EL.LandsN hN Work.EL.alpha2 z₁) :
    Work.SeedExist.Snear hN z₁ = Work.EL.pairSideNear (Work.EL.alphaPair hN z₁ h1 h2) := by
  have hα : Work.EL.alpha1 ≤ Work.EL.alpha2 := by norm_num [Work.EL.alpha1, Work.EL.alpha2]
  simp only [Work.SeedExist.Snear, Work.SeedExist.alphaPair, Work.EL.alphaPair,
    Work.EL.pairSideNear, Work.EL.pairSideThroughArc, Work.EL.alphaPairRaw,
    Function.iterate_zero_apply, Work.SeedExist.wakeLo_zero, Work.SeedExist.wakeHi_zero]
  rw [min_eq_left hα, max_eq_right hα]

theorem mem_Pg_of_fatou {c : ℂ} (hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c))
    (hJ : Work.Top.JordanForm) {z₁ : ℂ}
    (fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.FSeed.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) z₁)
    (hfat : Work.SeedExist.FatouCritInBasin c z₁ fl.Pg)
    (h1 : Work.Landing.landsAt c Work.EL.alpha1 z₁)
    (h2 : Work.Landing.landsAt c Work.EL.alpha2 z₁)
    (hg : (LeanEval.ComplexAnalysis.Tantibar c)^[5] z₁ = z₁)
    (hex : ∀ j : ℕ, 0 < j → j < 5 → (LeanEval.ComplexAnalysis.Tantibar c)^[j] z₁ ≠ z₁)
    (hcU : c ∈ Work.SeedExist.U c)
    (hU : Set.MapsTo ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) (Work.SeedExist.U c) (Work.SeedExist.U c))
    (hUS0 : Work.SeedExist.U c ⊆ Work.SeedExist.wakeSide hN z₁ 0)
    (hW5 : ∀ j : ℕ, 1 ≤ j → j ≤ 4 → (LeanEval.ComplexAnalysis.Tantibar c)^[j] z₁ ∈ Work.SeedExist.Snear hN z₁) :
    ∃ N : ℕ, (Work.FSeed.F c)^[N] c ∈ fl.Pg := by
  -- the Böttcher data and the two root rays in `Work.EL`'s vocabulary
  have hφ : Work.ParamRays.IsDynBottcher c (Work.ParamRays.dynPhiOf c) :=
    Work.ELPull.isDynBottcher_dynPhiOf_of_dynB' hN
  have L1 : Work.EL.LandsN hN Work.EL.alpha1 z₁ :=
    (Work.ELTop.landsN_iff_landsAt hN hφ Work.EL.alpha1 z₁).mpr h1
  have L2 : Work.EL.LandsN hN Work.EL.alpha2 z₁ :=
    (Work.ELTop.landsN_iff_landsAt hN hφ Work.EL.alpha2 z₁).mpr h2
  -- the critical orbit stays in the characteristic component `U c`, hence in the wake side
  have hFU : Set.MapsTo (Work.FSeed.F c) (Work.SeedExist.U c) (Work.SeedExist.U c) := by
    have hgg : (LeanEval.ComplexAnalysis.Tantibar c)^[5] ∘ (LeanEval.ComplexAnalysis.Tantibar c)^[5]
        = Work.FSeed.F c := by
      rw [Work.Final.Tantibar_five_comp_self]; exact Work.SeedExist.el_F_eq c
    rw [← hgg]
    exact hU.comp hU
  have hmemU : ∀ n : ℕ, (Work.FSeed.F c)^[n] c ∈ Work.SeedExist.U c :=
    fun n => Work.FatouCoord.mapsTo_iterate_of_mapsTo hFU n hcU
  -- the entry datum of Fatou's theorem
  obtain ⟨N, j, hj5, hmem⟩ := hfat.2
  rcases hmem with ⟨x, hxP, hxeq⟩
  -- `F c = (T_c)^10`, so the `T_c`-iterates commute with the `F c`-iterates
  have hFten : Work.FSeed.F c = (LeanEval.ComplexAnalysis.Tantibar c)^[10] := by
    funext z
    exact (Work.FSeed.Tantibar_iterate_ten c z).symm
  have hFpow : ∀ m : ℕ, (Work.FSeed.F c)^[m] = (LeanEval.ComplexAnalysis.Tantibar c)^[10 * m] := by
    intro m
    rw [hFten, ← Function.iterate_mul]
  have hcomm : ∀ (m : ℕ) (y : ℂ),
      (Work.FSeed.F c)^[m] ((LeanEval.ComplexAnalysis.Tantibar c)^[j] y)
        = (LeanEval.ComplexAnalysis.Tantibar c)^[j] ((Work.FSeed.F c)^[m] y) := by
    intro m y
    rw [hFpow m, ← Function.iterate_add_apply (LeanEval.ComplexAnalysis.Tantibar c) (10 * m) j y,
      ← Function.iterate_add_apply (LeanEval.ComplexAnalysis.Tantibar c) j (10 * m) y,
      show 10 * m + j = j + 10 * m from by omega]
  -- the critical orbit of `F c` converges to the `j`-th point of the parabolic cycle
  have hlim1 : Tendsto (fun m : ℕ => (LeanEval.ComplexAnalysis.Tantibar c)^[j]
      ((Work.FSeed.F c)^[m] x)) atTop
      (nhds ((LeanEval.ComplexAnalysis.Tantibar c)^[j] z₁)) :=
    (((continuous_tantibar_memPg c).iterate j).tendsto z₁).comp (fl.tendsto_Pg hxP)
  have hlim2 : Tendsto (fun m : ℕ => (Work.FSeed.F c)^[m]
      ((LeanEval.ComplexAnalysis.Tantibar c)^[j] x)) atTop
      (nhds ((LeanEval.ComplexAnalysis.Tantibar c)^[j] z₁)) := by
    have hfun : (fun m : ℕ => (Work.FSeed.F c)^[m] ((LeanEval.ComplexAnalysis.Tantibar c)^[j] x))
        = fun m : ℕ => (LeanEval.ComplexAnalysis.Tantibar c)^[j] ((Work.FSeed.F c)^[m] x) :=
      funext (fun m => hcomm m x)
    rw [hfun]; exact hlim1
  have hlim3 : Tendsto (fun m : ℕ => (Work.FSeed.F c)^[m] ((Work.FSeed.F c)^[N] c)) atTop
      (nhds ((LeanEval.ComplexAnalysis.Tantibar c)^[j] z₁)) := by
    have hfun : (fun m : ℕ => (Work.FSeed.F c)^[m] ((LeanEval.ComplexAnalysis.Tantibar c)^[j] x))
        = fun m : ℕ => (Work.FSeed.F c)^[m] ((Work.FSeed.F c)^[N] c) := by
      funext m; rw [hxeq]
    rwa [hfun] at hlim2
  have hlim4 : Tendsto (fun m : ℕ => (Work.FSeed.F c)^[m + N] c) atTop
      (nhds ((LeanEval.ComplexAnalysis.Tantibar c)^[j] z₁)) := by
    have hfun : (fun m : ℕ => (Work.FSeed.F c)^[m] ((Work.FSeed.F c)^[N] c))
        = fun m : ℕ => (Work.FSeed.F c)^[m + N] c := by
      funext m; rw [Function.iterate_add_apply]
    rwa [hfun] at hlim3
  have hlim : Tendsto (fun n : ℕ => (Work.FSeed.F c)^[n] c) atTop
      (nhds ((LeanEval.ComplexAnalysis.Tantibar c)^[j] z₁)) :=
    (Filter.tendsto_add_atTop_iff_nat N).mp hlim4
  -- hence the `j`-th cycle point lies in the closure of the wake side
  have hcl : (LeanEval.ComplexAnalysis.Tantibar c)^[j] z₁ ∈
      closure (Work.SeedExist.wakeSide hN z₁ 0) :=
    mem_closure_of_tendsto hlim
      (Filter.Eventually.of_forall (fun n => hUS0 (hmemU n)))
  -- the two sides of the root pair are disjoint; the near side is open, so it misses
  -- the closure of the far side
  have hnd : Work.EL.arcLen (Work.EL.alphaPair hN z₁ L1 L2).a
      (Work.EL.alphaPair hN z₁ L1 L2).b ≠ 0 := by
    show Work.EL.arcLen Work.EL.alpha1 Work.EL.alpha2 ≠ 0
    rw [Work.EL.arcLen,
      show Work.EL.alpha2 - Work.EL.alpha1 = 33 / 1023 by
        norm_num [Work.EL.alpha1, Work.EL.alpha2]]
    norm_num [Int.fract]
  have hdisj := (Work.ELTop.pairSides_decomposition hN hJ (Work.EL.alphaPair hN z₁ L1 L2) hnd).2.1
  have hnear_open : IsOpen (Work.EL.pairSideNear (Work.EL.alphaPair hN z₁ L1 L2)) :=
    (Work.ELTop.isOpen_pairSide hN (Work.EL.alphaPair hN z₁ L1 L2)).2
  have hcl_sub : closure (Work.EL.pairSide (Work.EL.alphaPair hN z₁ L1 L2)) ⊆
      (Work.EL.pairSideNear (Work.EL.alphaPair hN z₁ L1 L2))ᶜ :=
    closure_minimal (fun y hy hy' => Set.disjoint_left.mp hdisj hy hy') hnear_open.isClosed_compl
  -- conclude: `j = 0`
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  · refine ⟨N, ?_⟩
    rw [hj0] at hxeq
    rw [← hxeq]
    simpa using hxP
  · exfalso
    have hSnear : (LeanEval.ComplexAnalysis.Tantibar c)^[j] z₁ ∈ Work.SeedExist.Snear hN z₁ :=
      hW5 j hjpos (by omega)
    rw [Snear_eq_pairSideNear hN z₁ L1 L2] at hSnear
    rw [wakeSide_zero_eq_pairSide hN z₁ L1 L2] at hcl
    exact (hcl_sub hcl) hSnear

end Work.SeedExist.Fatou
