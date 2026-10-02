/-
# ELRig — the main theorem of the equator-curve rigidity (`equatorLeak`)

`NOTES_LEAD_mandelbar_EL_F_contracts.md` §6 (ELRig) asks for

```lean
theorem equatorLeak (hJ : Work.Top.JordanForm) (d : RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁) :
    ∃ x : ℝ, fl.Ψ x ∉ K c
```

i.e. the single residual input of the EL argument is the sibling-area data (`nest`, `tr`), with
**no** lift data: R-a2 (the two periodic lift curves and their two-sidedness) and R-a3 (the
equator tail lies in the near side of the `α`-pair) are *derived* in ELRig.

The chain assembled here is

* `Work.ELRig.exists_rayCylLift` — R-a2 (i), (ii): the two `1`-periodic lifts with `TailId`
  (proved from `exists_liftCurvesV3` and the flower);
* a separation input for those two curves, in one of two equivalent forms:
  - `hmono : StrictMono (Re ∘ γ₁)` — the two curves are graphs over the real axis; this implies
    the topology `Work.EL.LiftSides` by `Work.ELRig.exists_liftSides_of_cylGraph`; or
  - `lift : Work.EL.LiftSides …` directly (`Work.EL.equatorLeak_of_cylLiftSides`);
* `Work.ELRig.equatorTail_mem_near_of_liftSides` — R-a3 from the topology;
* `Work.ELRig.rigidity` — R-f, `False` from `E ⊆ K` and R-a3.

So the fully assembled theorem below has the contract's shape **up to the single separation input**;
see `NOTES.md` §7 for the precise state of that input (it is *not* derivable from the continuity,
injectivity and periodicity of the two lifts — counterexample in §6.1 — and the graph property is
the natural sufficient condition; the Jordan-curve route through `ζ = exp(2πiw)` and
`Work.Top.JordanForm` gives each curve's two sides but not the three-region exhaustion).
-/
import Submission.Work.ELRig.EquatorLeak
import Submission.Work.ELRig.CylLift
import Submission.Work.ELRig.CylSides
import Submission.Work.ELRig.exists_rayCylLift

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

namespace Work.EL

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- A `RayCylLift` reaches the petal, so the petal is nonempty. -/
theorem Pa_nonempty_of_liftSides {c : ℂ} {d : Work.EL.RootParabolic c}
    {fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁}
    (L : Work.ELRig.RayCylLift d fl) {R₀ : ℝ}
    (lift : LiftSides d.hN d.z₁ L.γ₁ L.γ₂ L.R R₀)
    (hγ : ∀ w : ℂ, w.re < -R₀ → R₀ < |w.im| → fl.Ψ w ∈ fl.Pa) : fl.Pa.Nonempty := by
  obtain ⟨w, hwU, hwim⟩ := lift.top_mem_U
  refine ⟨fl.Ψ w, hγ w ?_ (lt_of_lt_of_le hwim (le_abs_self w.im))⟩
  have h1 : w.re < -L.R := lift.U_sub hwU
  have h2 : -L.R < -R₀ := by linarith [lift.hRR₀]
  linarith

/-- **R-a3 at the `α`-pair of the nest**, from the two-sidedness structure of the lift pair. -/
theorem htail_of_cylLiftSides {c : ℂ} (d : RootParabolic c)
    (fl : ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁)
    (nest : Z1Nest d.hN d.z₁ fl.Pa)
    (L : Work.ELRig.RayCylLift d fl) {R₀ : ℝ}
    (lift : LiftSides d.hN d.z₁ L.γ₁ L.γ₂ L.R R₀)
    (hγ : ∀ w : ℂ, w.re < -R₀ → R₀ < |w.im| → fl.Ψ w ∈ fl.Pa)
    (hE : ∀ x : ℝ, fl.Ψ (x : ℂ) ∈ K c) :
    ∃ R' : ℝ, ∀ x : ℝ, x < -R' → fl.Ψ (x : ℂ) ∈ pairSideNear nest.P0 :=
  Work.ELRig.equatorTail_mem_near_of_liftSides d fl nest.P0 nest.P0_spec.2.2 nest.P0_spec.1
    nest.P0_spec.2.1 nest.sides_P0 L lift hγ nest.Pa_far
    (Pa_nonempty_of_liftSides L lift hγ) hE

/-- **The contract's `equatorLeak`, up to the two-sidedness of the lift pair.**

The only inputs beyond the contract's `(hJ) (d) (fl)` are the sibling-area bundles `nest`
(ELNest) and `tr` (ELNest/ELPull), the lift data `L` of R-a2 (`exists_rayCylLift`, proved), the
far-left petal statement `hγ` for one level `R₀` (an immediate consequence of the flower's
`Ψ_ends`, and carried by `L.hγtail` for the level below `L.R`), and the separation structure
`lift : LiftSides …` for `L` at the level `R₀`; everything else — R-a3, R-d, R-f — is derived. -/
theorem equatorLeak_of_cylLiftSides (hJ : Work.Top.JordanForm) {c : ℂ} (d : RootParabolic c)
    (fl : ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁)
    (nest : Z1Nest d.hN d.z₁ fl.Pa)
    (tr : B2Data d.hN d.z₁)
    (L : Work.ELRig.RayCylLift d fl) {R₀ : ℝ}
    (lift : LiftSides d.hN d.z₁ L.γ₁ L.γ₂ L.R R₀)
    (hγ : ∀ w : ℂ, w.re < -R₀ → R₀ < |w.im| → fl.Ψ w ∈ fl.Pa) :
    ∃ x : ℝ, fl.Ψ (x : ℂ) ∉ K c := by
  by_contra h
  simp only [not_exists, not_not] at h
  exact Work.ELRig.rigidity (c := c) d fl nest hγ
    (htail_of_cylLiftSides d fl nest L lift hγ h) tr h

/-- **The contract's `equatorLeak`, up to the graph property of the lifts.**

Here the separation input is the single statement that the first lift is a graph over the real
axis, `StrictMono (fun s => (L.γ₁ s).re)`; by the anti-symmetry `γ₂ s = conj (γ₁ s) + ½` this is
the same statement for the second lift, and `Work.ELRig.exists_liftSides_of_cylGraph` turns it
into the two-sidedness structure of the previous theorem (at the petal level recorded in
`L.hγtail`, so that no level has to be chosen by the caller). -/
theorem equatorLeak_of_cylGraph (hJ : Work.Top.JordanForm) {c : ℂ} (d : RootParabolic c)
    (fl : ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁)
    (nest : Z1Nest d.hN d.z₁ fl.Pa)
    (tr : B2Data d.hN d.z₁)
    (L : Work.ELRig.RayCylLift d fl)
    (hmono : StrictMono fun s : ℝ => (L.γ₁ s).re) :
    ∃ x : ℝ, fl.Ψ (x : ℂ) ∉ K c := by
  by_contra h
  simp only [not_exists, not_not] at h
  obtain ⟨R₀, hR₀R, hγ⟩ := L.hγtail
  obtain ⟨lift⟩ := Work.ELRig.exists_liftSides_of_cylGraph L hR₀R hmono h
  exact Work.ELRig.rigidity (c := c) d fl nest hγ
    (htail_of_cylLiftSides d fl nest L lift hγ h) tr h

/-! ## `reach` and `rigidity` under the same residual

The two consumers of R-a3 are `reach` (R-d) and `rigidity` (R-f), both of which take `htail` as an
explicit hypothesis.  The wrappers below supply it from the separation input, so that the whole
area has a single residual (`hmono`, or the structure `LiftSides`). -/

/-- **R-d (`reach`) from the same residual as the main theorem** (graph property form). -/
theorem reach_of_cylGraph {c : ℂ} (d : RootParabolic c)
    (fl : ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁)
    (nest : Z1Nest d.hN d.z₁ fl.Pa)
    (tr : B2Data d.hN d.z₁)
    (L : Work.ELRig.RayCylLift d fl)
    (hmono : StrictMono fun s : ℝ => (L.γ₁ s).re)
    (hE : ∀ x : ℝ, fl.Ψ (x : ℂ) ∈ K c) :
    ∃ u : ℂ, u ∈ Work.EL.equator fl ∧
      F c u = (Tantibar c)^[4] d.z₁ ∧ F c u ∈ Work.EL.equator fl ∧
      tr.b₂ ∈ Work.EL.equator fl ∧ F c tr.b₂ = tr.b₂ := by
  obtain ⟨R₀, hR₀R, hγ⟩ := L.hγtail
  obtain ⟨lift⟩ := Work.ELRig.exists_liftSides_of_cylGraph L hR₀R hmono hE
  exact Work.ELRig.reach d fl nest hγ (htail_of_cylLiftSides d fl nest L lift hγ hE) tr hE

/-- **R-f (`rigidity`) from the same residual as the main theorem** (graph property form). -/
theorem rigidity_of_cylGraph {c : ℂ} (d : RootParabolic c)
    (fl : ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁)
    (nest : Z1Nest d.hN d.z₁ fl.Pa)
    (tr : B2Data d.hN d.z₁)
    (L : Work.ELRig.RayCylLift d fl)
    (hmono : StrictMono fun s : ℝ => (L.γ₁ s).re)
    (hE : ∀ x : ℝ, fl.Ψ (x : ℂ) ∈ K c) : False := by
  obtain ⟨R₀, hR₀R, hγ⟩ := L.hγtail
  obtain ⟨lift⟩ := Work.ELRig.exists_liftSides_of_cylGraph L hR₀R hmono hE
  exact Work.ELRig.rigidity (c := c) d fl nest hγ
    (htail_of_cylLiftSides d fl nest L lift hγ hE) tr hE

/-- **R-f (`rigidity`) from the two-sidedness structure.** -/
theorem rigidity_of_cylLiftSides {c : ℂ} (d : RootParabolic c)
    (fl : ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁)
    (nest : Z1Nest d.hN d.z₁ fl.Pa)
    (tr : B2Data d.hN d.z₁)
    (L : Work.ELRig.RayCylLift d fl) {R₀ : ℝ}
    (lift : LiftSides d.hN d.z₁ L.γ₁ L.γ₂ L.R R₀)
    (hγ : ∀ w : ℂ, w.re < -R₀ → R₀ < |w.im| → fl.Ψ w ∈ fl.Pa)
    (hE : ∀ x : ℝ, fl.Ψ (x : ℂ) ∈ K c) : False :=
  Work.ELRig.rigidity (c := c) d fl nest hγ
    (htail_of_cylLiftSides d fl nest L lift hγ hE) tr hE

/-- **The contract's `equatorLeak` from R-a3 itself.**

This is the weakest form of the residual: the equator tail lies in the near side of the
`α`-pair, stated exactly as the two consumers `reach` and `rigidity` use it (and as `Z1Nest`,
`B2Data` package the sibling areas' outputs).  It is the form in which the residual is *certainly*
true — the geometric content of `NOTES_LEAD_mandelbar_EL.md` §2 (R-a) — and the two theorems above
reduce it to the structural statements `LiftSides` and the graph property. -/
theorem equatorLeak_of_htail (hJ : Work.Top.JordanForm) {c : ℂ} (d : RootParabolic c)
    (fl : ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁)
    (nest : Z1Nest d.hN d.z₁ fl.Pa)
    (tr : B2Data d.hN d.z₁)
    {R₀ : ℝ} (hγ : ∀ w : ℂ, w.re < -R₀ → R₀ < |w.im| → fl.Ψ w ∈ fl.Pa)
    (htail : ∃ R' : ℝ, ∀ x : ℝ, x < -R' → fl.Ψ (x : ℂ) ∈ pairSideNear nest.P0) :
    ∃ x : ℝ, fl.Ψ (x : ℂ) ∉ K c := by
  by_contra h
  simp only [not_exists, not_not] at h
  exact Work.ELRig.rigidity (c := c) d fl nest hγ htail tr h

end Work.EL

end
