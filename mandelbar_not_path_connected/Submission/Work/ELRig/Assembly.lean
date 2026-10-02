/-
# ELRig — assembling the hypotheses: R-a3 at the `α`-pair of the nest

`Work.EL.equatorLeak` needs, besides `d : RootParabolic c`, the flower `fl`, the nest `nest`,
the lift data `L` and the tripod data `tr`, the hypothesis `htail` — the output of R-a3 for the
`α`-pair of the nest.  This file removes that from the caller's path:

* `exists_level_avoid` : the level beyond which `Ψ` misses `z₁` (this is `fl.Ψ_small`);
* `htail_of_nest` : R-a3 instantiated at the `α`-pair `nest.P0`, producing `htail` from the lift
  data `L`, the plane topology `lift` and the contradiction hypothesis `E ⊆ K c`.
-/
import Submission.Work.ELRig.Inputs
import Submission.Work.ELRig.Flower
import Submission.Work.ELRig.Arm
import Submission.Work.ELRig.RayLift
import Submission.Work.ELRig.rayTail_lift
import Submission.Work.ELRig.RayLift
import Submission.Work.ELRig.exists_liftCurvesV3
import Submission.Work.ELRig.equatorTail_mem_near

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

/-- The flower's **avoidance level**: beyond it, `Ψ` misses the parabolic point `z₁`.  This is
`fl.Ψ_small`, and it is the model for the `hzne` field of the lift data `Work.ELRig.RayLift`. -/
theorem exists_level_avoid {c : ℂ} {z₁ : ℂ}
    (fl : ParabolicFlower (F c) ((Tantibar c)^[5]) z₁) :
    ∃ Rstar : ℝ, ∀ w : ℂ, w.re < -Rstar → fl.Ψ w ≠ z₁ := by
  obtain ⟨R, hR⟩ := fl.Ψ_small 1 one_pos
  exact ⟨R, fun w hw => (hR w hw).1⟩

/-- **R-a3 at the `α`-pair of the nest**: the equator tail below the level of the lift lies in the
near side of `nest.P0`.  This produces the `htail` hypothesis of `equatorLeak`. -/
theorem htail_of_nest {c : ℂ} (d : RootParabolic c)
    (fl : ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁)
    (nest : Z1Nest d.hN d.z₁ fl.Pa)
    (L : Work.ELRig.RayLift d fl)
    (hE : ∀ x : ℝ, fl.Ψ (x : ℂ) ∈ K c) :
    ∃ R' : ℝ, ∀ x : ℝ, x < -R' → fl.Ψ (x : ℂ) ∈ pairSideNear nest.P0 := by
  have lift : LiftSides d.hN d.z₁ L.γ₁ L.γ₂ L.R L.R₀ := L.liftSidesOf hE
  have hne : fl.Pa.Nonempty := by
    obtain ⟨w, hwU, hwim⟩ := lift.top_mem_U
    refine ⟨fl.Ψ w, L.pa_ends w ?_ ?_⟩
    · have h1 : w.re < -L.R := lift.U_sub hwU
      have h2 : -L.R < -L.R₀ := by linarith [lift.hRR₀]
      linarith
    · exact lt_of_lt_of_le hwim (le_abs_self w.im)
  exact Work.ELRig.equatorTail_mem_near d fl nest.P0 nest.P0_spec.2.2 nest.P0_spec.1
    nest.P0_spec.2.1 nest.sides_P0 L nest.Pa_far hne hE

/-! ## Assembling R-a2 from the residual strand statement

The theorems below turn the `RayLift` hypothesis of `Work.EL.equatorLeak` into a *consequence* of
the single residual statement `Work.ELRig.RayStrand` (R-a2's "the two root rays meet the repelling
half plane in a single level-transversal arc"), using `exists_liftCurvesV3` for the curves and the
flower's `Ψ_inj`, `Ψ_small`, `Ψ_ends` for the levels.  `equatorLeak_of_strand` is the contract's
`equatorLeak (hJ) (d) (fl)` with the sibling inputs `nest`, `tr` and the named residual. -/

/-- **R-a2 for every level, from the residual strand statement.**  The two landing hypotheses of
the root portrait (available from `nest.P0`), the flower, and the residual input
`hstrand : ∀ R, RayStrand d fl R` produce the whole lift data `RayLift d fl`; the levels `R`, `R₀`
are chosen inside from the flower's `Ψ_inj`, `Ψ_small`, `Ψ_ends`. -/
theorem exists_rayLift {c : ℂ} (d : RootParabolic c)
    (fl : ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁)
    (h₁ : LandsN d.hN alpha1 d.z₁) (h₂ : LandsN d.hN alpha2 d.z₁)
    (hstrand : ∀ R : ℝ, Work.ELRig.RayStrand d fl R) : Nonempty (Work.ELRig.RayLift d fl) := by
  obtain ⟨Ri, hRi⟩ := fl.Ψ_inj
  obtain ⟨Rs, hRs⟩ := fl.Ψ_small 1 one_pos
  obtain ⟨Re, hRe⟩ := fl.Ψ_ends
  set R₀ : ℝ := max Re 0 + 1 with hR₀def
  set R : ℝ := max (max Ri Rs) R₀ + 1 with hRdef
  have hRiR : Ri ≤ R := by
    rw [hRdef]
    have h1 : (max Ri Rs : ℝ) ≤ max (max Ri Rs) R₀ := le_max_left _ _
    have h2 : Ri ≤ max Ri Rs := le_max_left _ _
    linarith
  have hRsR : Rs ≤ R := by
    rw [hRdef]
    have h1 : (max Ri Rs : ℝ) ≤ max (max Ri Rs) R₀ := le_max_left _ _
    have h2 : Rs ≤ max Ri Rs := le_max_right _ _
    linarith
  have hReR₀ : Re ≤ R₀ := by
    rw [hR₀def]
    have h : Re ≤ max Re 0 := le_max_left _ _
    linarith
  have hR₀R : R₀ < R := by
    rw [hRdef]
    have h1 : R₀ ≤ (max (max Ri Rs) R₀ : ℝ) := le_max_right _ _
    linarith
  have hinj : Set.InjOn fl.Ψ {w : ℂ | w.re < -R} :=
    hRi.mono fun w hw => lt_of_lt_of_le hw (by linarith : -R ≤ -Ri)
  have hzne : ∀ w : ℂ, w.re < -R → fl.Ψ w ≠ d.z₁ :=
    fun w hw => (hRs w (lt_of_lt_of_le hw (by linarith : -R ≤ -Rs))).1
  have pa_ends : ∀ w : ℂ, w.re < -R₀ → R₀ < |w.im| → fl.Ψ w ∈ fl.Pa :=
    fun w hw him => hRe w (lt_of_lt_of_le hw (by linarith : -R₀ ≤ -Re))
      (lt_of_le_of_lt hReR₀ him)
  obtain ⟨γ₁, γ₂, τ, t₀, -, hτmono, hτ1, hΨ₁, hanti, hcont₁, hcont₂, -, -, hper₁, hper₂, -,
    -, -, -⟩ :=
    Work.ELRig.exists_liftCurvesV3 d fl h₁ h₂ (le_refl R) hinj
  exact ⟨{ γ₁ := γ₁, γ₂ := γ₂, τ := τ, R := R, R₀ := R₀, hRR₀ := hR₀R, hτmono := hτmono,
            hτ1 := hτ1, hΨ₁ := hΨ₁, cont₁ := hcont₁, cont₂ := hcont₂, per₁ := hper₁,
            per₂ := hper₂, anti := hanti, hinj := hinj, strand := hstrand R, hzne := hzne,
            pa_ends := pa_ends }⟩

end Work.EL
