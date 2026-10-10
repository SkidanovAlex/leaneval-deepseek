import Mathlib
import Submission.Work.MotV5.ASTwistData
import Submission.Work.MotV5.base_preserved_AS
import Submission.Work.MotV5.hurwitz_AS_ratFunc
import Submission.Work.MotV.Defs
import Submission.Work.MotV5.Nodes.bridge_AS
import Submission.Work.MotV5.RigAS.constantsOnly_K_AS
import Submission.Work.MotV5.RigAS.constantsOnly_transfer_AS

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV5.Nodes

open Work.MotV

/-- **The standing hypotheses force `σ ^ 5 = 1` on the constants.**

`asTwistAction D τ σS = σS ∘ τ` acts on the image of `Kb 𝕜` exactly by `σ` (this is the content of
the proved `Work.MotV5.sigma_apply_eq_of_mem_fix`: `σS` is `Kb 𝕜`-linear, so it fixes the image of
the constants, and `hτ` reads off `σ`).  Hence `h5 : (asTwistAction D τ σS) ^ 5 = 1` gives
`σ ^ 5 = 1` on all of `Kb 𝕜`. -/
theorem sigma_pow_five_eq_one {𝕜 : Type} [Field 𝕜] {D : Work.MotV.KleinData 𝕜}
    (τ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (σ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜)
    (hτ : ∀ c : Work.MotV.Kb 𝕜, τ (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) c)
      = algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (σ c))
    (h5 : (Work.MotV5.asTwistAction D τ σS) ^ 5 = 1) : σ ^ 5 = 1 := by
  have hstep : ∀ x : Work.MotV.Kb 𝕜,
      Work.MotV5.asTwistAction D τ σS (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) x)
        = algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (σ x) := by
    intro x
    rw [Work.MotV5.asTwistAction, AlgEquiv.trans_apply, hτ x]
    exact AlgEquiv.commutes σS (σ x)
  have hpow : ∀ (n : ℕ) (x : Work.MotV.Kb 𝕜),
      ((Work.MotV5.asTwistAction D τ σS) ^ n) (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) x)
        = algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) ((σ ^ n) x) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ m ih =>
        intro x
        rw [pow_succ, AlgEquiv.mul_apply, hstep x, ih, pow_succ, ← AlgEquiv.mul_apply]
  ext c
  have h : ((Work.MotV5.asTwistAction D τ σS) ^ 5)
      (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) c)
      = algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) c := by rw [h5]; rfl
  rw [hpow 5 c] at h
  exact FaithfulSMul.algebraMap_injective (Work.MotV.Kb 𝕜) (Work.MotV.Om D) h

/-- **The Artin–Schreier generator is nontrivial**: `hσ` moves `asRoot g` by `1`. -/
theorem sigma_ne_one {𝕜 : Type} [Field 𝕜] {D : Work.MotV.KleinData 𝕜} (g : RatFunc 𝕜)
    (σ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜)
    (hσ : σ (Work.MotV5.asRoot g) = Work.MotV5.asRoot g + 1) : σ ≠ 1 := by
  intro h
  have h1 : Work.MotV5.asRoot g + 1 = Work.MotV5.asRoot g := by
    rw [← hσ, h]; rfl
  have h2 : (1 : Work.MotV.Kb 𝕜) = 0 :=
    add_left_cancel (show Work.MotV5.asRoot g + 1 = Work.MotV5.asRoot g + 0 by simpa using h1)
  exact one_ne_zero h2

/-- **Node CO_AS (constants-only)**, revised after review.  For `g = fAS 𝕜 = t³ + t` or
`g = 2 • fAS 𝕜`, every `𝕜`-embedding of the corrected twist field `F = asTwistFieldTrue D g τ σS`
into a rational function field `RatFunc M` has image contained in the constants `M`.

The hypotheses are bundled in `Work.MotV5.ASTwistData` (`Submission/Work/MotV5/ASTwistData.lean`):
`τ` is the coefficient action of `σ` and fixes `K(E)`, `σ` is the AS generator, `σS` is a genuine
projective fifth-torsion shift, and the twisted action has order `5`, is nontrivial and preserves
`L(E)`.  Without them (e.g. `σS = 1`, or a `τ` differing from the coefficient action on `K(E)`) the
field collapses to the ruled field `K(E)`, for which `ConstantsOnly` is false — this was the
reviewers' counterexample.

**Route** (the characteristic-`5` analogue of `Work.MotV.constantsOnly_twist`), now carried out in
two proved halves.

* **The local half (BR_AS ⟹ `ι t ∈ M`).**  Let `ι : F →ₐ[𝕜] RatFunc M`, `M̄` an algebraic closure
  of `M` and `ῑ : F →ₐ[𝕜] RatFunc M̄` its extension.  By node BR_AS
  (`Work.MotV5.Nodes.bridge_AS`, proved) the class of `g` is unramified at every valuation of `F`
  at which `t` has a pole; `Work.MotV5.AssKlein.localSol_of_asUnramified` pushes this along `ῑ` and
  `Work.MotV5.hurwitz_AS_ratFunc` (node H1_AS, proved) gives `ῑ t = c` for a constant `c : M̄`;
  descent along `RatFunc M ↪ RatFunc M̄` gives `ι t ∈ M`.  Then `M` inherits a `K = RatFunc 𝕜`-algebra
  structure with `X ↦ ι t`.  This is `Work.MotV5.RigAS.constantsOnly_transfer_AS`.
* **The `K`-linear half.**  With that structure, `ι` is a `K`-algebra map, and
  `Work.MotV5.RigAS.constantsOnly_K_AS` (proved) gives `ι x ∈ M` for every `x`.

The `K`-linear half is itself obtained from the proved descent engine
`Work.MotC.constantsOnly_of_descent`, applied to the *finite Galois* base change
`asF D f₁ f₂ g τ σS = (asTwistFieldTrue D g τ σS).comap (asIota D f₁ f₂)` over
`asL2 f₁ f₂ = K⟮asRoot f₁, asRoot f₂⟯` (`f₁ = fAS 𝕜`, `f₂ = 2 • fAS 𝕜`), whose two inputs —
linear disjointness (`Work.MotV5.LamAS.asF_linearDisjoint`) and `asF ⊔ asLImageM = ⊤`
(`Work.MotV5.LamAS.asF_transfer`) — are proved in the `LamAS` chapter.  This supersedes the earlier
route through the twisted Klein equations, which is no longer needed. -/
theorem constantsOnly_AS (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) (g : RatFunc 𝕜)
    (hg : g = Work.MotV.fAS 𝕜 ∨ g = 2 • Work.MotV.fAS 𝕜)
    (τ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (σ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜)
    (h : Work.MotV5.ASTwistData 𝕜 D g τ σS σ) :
    Work.MotV.ConstantsOnly 𝕜 ↥(Work.MotV5.asTwistFieldTrue D g τ σS) :=
  Work.MotV5.RigAS.constantsOnly_transfer_AS 𝕜 D hD g hg τ σS σ h
    (Work.MotV5.Nodes.bridge_AS 𝕜 D hD g hg τ σS σ h)
    (Work.MotV5.RigAS.constantsOnly_K_AS 𝕜 D hD g hg τ σS σ h)

end Work.MotV5.Nodes
