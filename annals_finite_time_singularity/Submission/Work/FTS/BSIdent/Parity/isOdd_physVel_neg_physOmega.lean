/-
# Oddness of the Biot–Savart velocity of the *negated* physical vorticity

The requested lemma is the negated sibling of
`Work.FTS.Physical.RegPkg.isOdd_physVort_swirlShape`: for `τ` in the strip `[0,S]` of a
`Work.FTS.Regularity.RegPkg α S A B g`, the *negated* physical vorticity slice

  `x ↦ −physVort α A B g x τ = −A(τ)⁻¹ · profile (3α) (g·τ) (ρ(x)^{3α}/B(τ)) (θ(x)) · e_θ(x)`

is a swirl `e_θ`-field whose angular scalar is *odd* in `θ` (the profile `profile p g z ·` is the
odd extension of `F_* + g`, `Work.ConstructionInstance.profile_odd`, using the vanishing of `g` at
`θ = 0`).  Oddness of an `e_θ`-swirl field is the parity class `IsOddVorticity`, Biot–Savart of a
swirl field is axisymmetric without swirl, and the two together give the full oddness
`FiniteTimeSingularity.IsOdd` of the velocity
(`Work.FTS.Physical.BiotSavart.isOdd_physVel_of_swirlShape`, whose proof chains
`Work.ConstructionInstance.isOddVorticity_smul_eTheta`,
`Work.ConstructionInstance.isAxiNoSwirl_biotSavart` and
`Work.SolutionDelivery.isOdd_biotSavart_of_axiNoSwirl`).

Since the extra sign only multiplies the swirl scalar by `−1` (which preserves both oddness in the
angle and the reflection parity class), the proof is the one of `isOdd_physVort_swirlShape` with the
scalar negated.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.FTS.BSIdent.Defs
import Submission.Work.FTS.Physical.BiotSavart.isOdd_physVel_of_swirlShape

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSIdent.Parity

open Work.FTS.Regularity

/-- **Oddness of the Biot–Savart velocity of the negated `RegPkg` vorticity slice.** -/
theorem isOdd_physVel_neg_physOmega {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : Work.FTS.Regularity.RegPkg α S A B g) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) S) :
    FiniteTimeSingularity.IsOdd
      (Work.LWP.biotSavart (fun y => -(Work.FTS.Regularity.physVort α A B g y τ))) := by
  have hp : pExp α ≠ 0 := ne_of_gt (pExp_pos h.hα)
  have hg0 : ∀ z : ℝ, gSlice g τ z 0 = 0 := fun z => (h.hvt τ hτ).1 z
  refine Work.FTS.Physical.BiotSavart.isOdd_physVel_of_swirlShape
    (W := fun ρ θ => -((A τ)⁻¹ * Work.ConstructionInstance.profile (pExp α) (gSlice g τ)
      (ρ ^ pExp α / B τ) θ))
    (ω := fun y _ => -(physVort α A B g y τ)) (t := 0) ?_ ?_
  · intro x
    rw [physVort_apply, Work.ConstructionInstance.omegaSz_apply, ← smul_assoc, neg_smul]
    simp only [smul_eq_mul]
  · intro ρ θ
    rw [Work.ConstructionInstance.profile_odd hp hg0 (ρ ^ pExp α / B τ) θ]
    ring

end Work.FTS.BSIdent.Parity
