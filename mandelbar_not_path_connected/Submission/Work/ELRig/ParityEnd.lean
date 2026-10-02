/-
# ELRig — the assembled `equatorLeak` by the crossing-parity route

This is the entry point of the area: `Work.EL.equatorLeak_parity` is the contract's
`equatorLeak`, with the sibling-area bundles `nest` (ELNest) and `tr` (ELNest/ELPull) as the only
inputs beyond the contract's `(hJ) (d) (fl)`.

It is assembled from

* `Work.ELRig.exists_analytic_rayCylLift` — R-a2 (i)/(ii) *with* the regularity: a `RayCylLift`
  whose first lift is real-analytic on each period (the analyticity input of
  `Work.ELRig.odd_transversal_level`);
* `Work.ELRig.exists_side_flip` — the side flip at a transversal crossing, packaged here as
  `Work.ELRig.FlipHyp` (`flipHyp_of_jordan`);
* `Work.ELRig.htail_of_flip` (`ParityMain.lean`) — R-a3 by crossing parity;
* `Work.ELRig.rigidity` — R-f, and hence the contradiction.
-/
import Mathlib
import Submission.Work.ELRig.ParityMain
import Submission.Work.ELRig.exists_side_flip

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

noncomputable section

namespace Work.ELRig

open Work.EL
open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- **The side flip, packaged.**  `Work.ELRig.exists_side_flip` (which uses the local angle-side
lemma at the lift, the local biholomorphy of `Ψ` there, and the Jordan curve theorem `hJ`) is
exactly the hypothesis `FlipHyp` consumed by `Work.ELRig.htail_of_flip`. -/
theorem flipHyp_of_jordan {c : ℂ} (hJ : Work.Top.JordanForm) (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁)
    (P : Work.EL.CoPair d.hN) (hPa : P.a = Work.EL.alpha1) (hPb : P.b = Work.EL.alpha2)
    (hPy : P.y = d.z₁) (hside : Work.EL.PairSides d.hN P) (L : RayCylLift d fl) :
    FlipHyp fl P L :=
  fun x₀ hx₀ s hs hcross => exists_side_flip hJ d fl P hPa hPb hPy hside L hx₀ hs hcross

/-- **R-a3 for an analytic lift.** -/
theorem htail_of_analytic {c : ℂ} (hJ : Work.Top.JordanForm) (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁)
    (nest : Work.EL.Z1Nest d.hN d.z₁ fl.Pa)
    (L : RayCylLift d fl)
    (han : ∀ n : ℤ, AnalyticOn ℝ (fun s : ℝ => L.γ₁ s) (Set.Ioo (n : ℝ) ((n : ℝ) + 1)))
    (hE : ∀ x : ℝ, fl.Ψ (x : ℂ) ∈ Work.EL.K c) :
    ∃ R' : ℝ, ∀ x : ℝ, x < -R' → fl.Ψ (x : ℂ) ∈ Work.EL.pairSideNear nest.P0 :=
  htail_of_flip d fl nest L han
    (flipHyp_of_jordan hJ d fl nest.P0 nest.P0_spec.1 nest.P0_spec.2.1 nest.P0_spec.2.2
      nest.sides_P0 L) hE

end Work.ELRig

namespace Work.EL

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- **The contract's `equatorLeak`, by the crossing-parity route.**

Beyond the contract's `(hJ) (d) (fl)` the only inputs are the two sibling-area bundles: the nest
`nest : Z1Nest` at the parabolic point (ELNest N1–N4, `SP`, and ELPull's wake) and the tripod data
`tr : B2Data` at the branch point `b₂` (ELNest N3–N5, ELPull P5/P6/C7, ELTop T8).  R-a2 (the two
`1`-periodic lifts, their analyticity and the identification of the `Ψ`-preimages of the pair
curve) and R-a3 (`equatorTail_mem_near`, by crossing parity) are *proved* in this area, and R-d
(`reach`) and R-f (`rigidity`) then follow. -/
theorem equatorLeak_parity (hJ : Work.Top.JordanForm) {c : ℂ} (d : RootParabolic c)
    (fl : ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁)
    (nest : Z1Nest d.hN d.z₁ fl.Pa)
    (tr : B2Data d.hN d.z₁) :
    ∃ x : ℝ, fl.Ψ (x : ℂ) ∉ K c := by
  by_contra h
  simp only [not_exists, not_not] at h
  obtain ⟨L, han⟩ := Work.ELRig.exists_analytic_rayCylLift d fl
    (by rw [← nest.P0_spec.2.2, ← nest.P0_spec.1]; exact nest.P0.lands_a)
    (by rw [← nest.P0_spec.2.2, ← nest.P0_spec.2.1]; exact nest.P0.lands_b)
  obtain ⟨R₀, hR₀R, hγ⟩ := L.hγtail
  exact Work.ELRig.rigidity (c := c) d fl nest hγ
    (Work.ELRig.htail_of_analytic hJ d fl nest L han h) tr h

/-- **R-d (`reach`) by the crossing-parity route** — the same inputs, and no lift data. -/
theorem reach_parity (hJ : Work.Top.JordanForm) {c : ℂ} (d : RootParabolic c)
    (fl : ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁)
    (nest : Z1Nest d.hN d.z₁ fl.Pa)
    (tr : B2Data d.hN d.z₁)
    (hE : ∀ x : ℝ, fl.Ψ (x : ℂ) ∈ K c) :
    ∃ u : ℂ, u ∈ equator fl ∧ F c u = (Tantibar c)^[4] d.z₁ ∧ F c u ∈ equator fl ∧
      tr.b₂ ∈ equator fl ∧ F c tr.b₂ = tr.b₂ := by
  obtain ⟨L, han⟩ := Work.ELRig.exists_analytic_rayCylLift d fl
    (by rw [← nest.P0_spec.2.2, ← nest.P0_spec.1]; exact nest.P0.lands_a)
    (by rw [← nest.P0_spec.2.2, ← nest.P0_spec.2.1]; exact nest.P0.lands_b)
  obtain ⟨R₀, hR₀R, hγ⟩ := L.hγtail
  exact Work.ELRig.reach d fl nest hγ
    (Work.ELRig.htail_of_analytic hJ d fl nest L han hE) tr hE

end Work.EL

end
