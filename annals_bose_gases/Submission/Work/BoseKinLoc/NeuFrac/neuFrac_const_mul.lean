import Mathlib.Tactic.Have
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Submission.Work.BoseKinLoc.NeuFrac.neuFracTrialVal_const_mul
import Submission.Work.BoseKinLoc.NeuFrac.neuFrac_zero_fun
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.NeuFrac.neuFrac_const_mul` — `neuFrac` is `2`-homogeneous

`neuFrac ℓ a² u ϕ` (`Work.BoseKinLoc.Defs`, FS `eq:DefT`'s first term) is the box
Neumann-resolvent fraction of `ϕ`, written as the Dirichlet-principle infimum

`neuFrac ℓ a² u ϕ = inf_g [ ‖ϕ‖²_Λ − 2a²⟨ϕ,g⟩_Λ + a²(‖∇g‖²_Λ + a²‖g‖²_Λ) ]`,  `Λ = Λ(u)`,

over globally `C^∞` compactly supported trials `g`.  The trial functional
(`neuFracTrialVal ℓ a² u ψ g`, `Work.BoseKinLoc.NeuFrac.neuFrac_add_const_L2`) is **exactly
`2`-homogeneous** in the pair `(ψ, g)`:

`neuFracTrialVal ℓ a² u (c·ψ) (c·g) = c² · neuFracTrialVal ℓ a² u ψ g`

(`Work.BoseKinLoc.NeuFrac.neuFracTrialVal_const_mul`): the pointwise identities
`(cψ)² = c²ψ²`, `(cψ)(cg) = c²ψg`, `(cg)² = c²g²`, `∂(cg) = c·∂g` together with the
*unconditional* linearity of the Bochner integral `MeasureTheory.integral_const_mul` — the
junk value of a non-integrable integral being `0` on both sides, the junk convention is itself
`2`-homogeneous.  For `c ≠ 0` the map `g ↦ c·g` is a bijection of the admissible trial class,
so the trial **sets** of `ϕ` and of `c·ϕ` are related by the scaling `y ↦ c²y` of `ℝ`:

`S_{cϕ} = c² • S_ϕ   (c ≠ 0)`.

Since `y ↦ c²y` is an order isomorphism of `ℝ` (`c² > 0`), the infima correspond:
`Real.sInf_smul_of_nonneg` gives `sInf (c² • S) = c² • sInf S`, and it delivers this for *every*
`S` — including the case in which `S` is not bounded below, where `sInf` is the junk value `0`
(`Real.sInf_of_not_bddBelow`) on both sides, again consistent with the homogeneity.

The degenerate case `c = 0` is the one place where `0 ≤ a²` is needed.  Both sides are `0`:
the right trivially, the left because at the zero state the trial values are
`a²(Σ_k∫_Λ(∂_k g)² + a²∫_Λ g²) ≥ 0` and `0` is attained by the zero trial
(`Work.BoseKinLoc.NeuFrac.neuFrac_zero_fun`).

No smoothness, support or integrability hypothesis is imposed on the state `ϕ`.

## Contents

* `neuFrac_const_mul` — the target.  It is assembled from the two verified pieces
  `Work.BoseKinLoc.NeuFrac.neuFracTrialVal_const_mul` (the exact `2`-homogeneity of the trial
  functional) and `Work.BoseKinLoc.NeuFrac.neuFrac_zero_fun` (`neuFrac ℓ a² u 0 = 0` for
  `0 ≤ a²`), proved in the sibling modules of this directory.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal Pointwise

namespace Work.BoseKinLoc.NeuFrac

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

theorem neuFrac_const_mul {ℓ a2 c : ℝ} (ha2 : 0 ≤ a2) (u : EuclideanSpace ℝ (Fin 3)) (ϕ : EuclideanSpace ℝ (Fin 3) → ℝ) :
    Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => c * ϕ z) = c ^ 2 * Work.BoseKinLoc.neuFrac ℓ a2 u ϕ := by
  rcases eq_or_ne c 0 with hc0 | hcne
  · -- degenerate case `c = 0`: both sides vanish, using `0 ≤ a²`
    subst hc0
    have hfun : (fun z : EuclideanSpace ℝ (Fin 3) => (0 : ℝ) * ϕ z) = fun _ => (0 : ℝ) := by
      funext z
      rw [zero_mul]
    rw [hfun, neuFrac_zero_fun ha2 u]
    ring
  · -- `c ≠ 0`: `g ↦ c·g` is a bijection of the trial class, so the trial sets are `c²`-scaled
    have hset : {y : ℝ | ∃ g : EuclideanSpace ℝ (Fin 3) → ℝ,
          ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
            y = neuFracTrialVal ℓ a2 u (fun z => c * ϕ z) g}
        = c ^ 2 • {y : ℝ | ∃ g : EuclideanSpace ℝ (Fin 3) → ℝ,
          ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
            y = neuFracTrialVal ℓ a2 u ϕ g} := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_smul_set]
      constructor
      · -- `z = tv (cϕ) h` gives `z = c² · tv ϕ (c⁻¹·h)`
        rintro ⟨h, hhd, hhcs, hz⟩
        set g₀ : EuclideanSpace ℝ (Fin 3) → ℝ := fun z => c⁻¹ * h z with hg₀
        have hhd' : ContDiff ℝ ∞ g₀ := by
          rw [hg₀]
          exact contDiff_const.mul hhd
        have hcs' : HasCompactSupport g₀ := by
          rw [hg₀]
          have h := hhcs.comp_left (g := fun x : ℝ => c⁻¹ * x) (by simp)
          simpa [Function.comp_def] using h
        refine ⟨neuFracTrialVal ℓ a2 u ϕ g₀, ⟨g₀, hhd', hcs', rfl⟩, ?_⟩
        have hA := neuFracTrialVal_const_mul (ℓ := ℓ) (a2 := a2) (c := c) (u := u)
          (ψ := ϕ) (g := g₀) hhd'
        have hAh : (fun z => c * g₀ z) = h := by
          funext z
          simp only [hg₀, ← mul_assoc, mul_inv_cancel₀ hcne, one_mul]
        rw [hAh] at hA
        rw [smul_eq_mul, hz]
        exact hA.symm
      · -- `z = c² · tv ϕ g` gives `z = tv (cϕ) (c·g)`
        rintro ⟨y, ⟨g, hgd, hgcs, rfl⟩, hy⟩
        have hcs' : HasCompactSupport (fun z : EuclideanSpace ℝ (Fin 3) => c * g z) := by
          have h := hgcs.comp_left (g := fun x : ℝ => c * x) (by simp)
          simpa [Function.comp_def] using h
        refine ⟨fun z => c * g z, contDiff_const.mul hgd, hcs', ?_⟩
        rw [← hy, smul_eq_mul]
        exact (neuFracTrialVal_const_mul (ℓ := ℓ) (a2 := a2) (c := c) (u := u)
          (ψ := ϕ) (g := g) hgd).symm
    rw [neuFrac_eq_sInf, neuFrac_eq_sInf, hset,
      Real.sInf_smul_of_nonneg (a := c ^ 2) (sq_nonneg c), smul_eq_mul]

end Work.BoseKinLoc.NeuFrac
