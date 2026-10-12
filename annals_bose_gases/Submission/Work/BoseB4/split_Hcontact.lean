import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.l2Space
import Submission.Work.BoseB4.K2ndDefs
import Submission.Work.BoseB4.a0d_sq_comp_a0_sq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.split_Hcontact` — the contact term of `eq:HLambdaSecond` under `split`

The contact row of FS `eq:HLambdaSecond` is the mode-lattice word

    `Hcontact D = ½ℓ⁻³(ĝ(0)+ĝ_ω(0)) · (a₀†)²a₀²`,

and `Work.BoseB4.K2ndDefs` records the corresponding complex-spectator operator
`KHC2 D + KHC1 D + KHC0 D` (the three `c`-number slots of the anti-normal form of
`(a₀†)²a₀²`).  This file proves that these two agree under the
`⟨condensate | excited⟩` split of the mode lattice:

    `split (Hcontact D x) = (monoOp 2 2 (KHC2 D) + monoOp 1 1 (KHC1 D)
                              + monoOp 0 0 (KHC0 D)) (split x)`.

It is the contact row of the row-by-row verification that
`Work.BoseB4.K2ndC` is the image of FS `eq:HLambdaSecond` (without `Q̃₃`) under
`split`; the companions are `split_Hkin`, `split_Hgap`, `split_HgapH`,
`split_Hmu`, `split_HW`, `split_Hbog`, `split_Hchi`, `split_HchiOm`, `split_Hnn`.

## Proof

Three steps.

1. *The mode-lattice word.*  `Hcontact D` is `cHC D` times the composite
   `L = cre m 0 ∘ cre m 0 ∘ ann m 0 ∘ ann m 0` (`hHc`, definitional, `i3` and
   `cHC` being the scalar data of `K2ndDefs`).

2. *Transport by `split`.*  `split ∘ ann m 0 = a0 ∘ split` (`Split_ann_zero`) and
   `split ∘ cre m 0 = a0d ∘ split` (`Split_cre_zero`), hence

       `split (L y) = ((a0d ∘ a0d) ∘ (a0 ∘ a0)) (split y)`

   for every mode-lattice state `y` (`hsplit`).

3. *Anti-normal ordering of the condensate word.*  Wick's identity
   `a0d_sq_comp_a0_sq` (`(a₀†)²a₀² = a₀²(a₀†)² − 4 a₀a₀† + 2`, from the CCR
   `[a₀,a₀†] = 1`) rewrites `(a0d ∘ a0d) ∘ (a0 ∘ a0)` into
   `monoOp 2 2 1 − 4 monoOp 1 1 1 + 2 monoOp 0 0 1` (the `lift 1 = 1` reduction of
   `monoOp _ _ 1`), which, after distributing the scalar `cHC D` and matching
   `(-(4·c))` and `2·c` against the coefficients of `KHC1 D` and `KHC0 D` and the
   real/complex scalar coercion, is the stated right-hand side.
-/

noncomputable section

open scoped lp BigOperators

namespace Work.BoseB4

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem split_Hcontact {m : ℕ} [NeZero m] (D : Work.BoseB4.H2ndData m) (x : Work.BoseB4.RealFock m) :
    Work.BoseB4.split (Work.BoseB4.Hcontact D x)
      = (Work.BoseB4.monoOp 2 2 (Work.BoseB4.KHC2 D)
          + Work.BoseB4.monoOp 1 1 (Work.BoseB4.KHC1 D)
          + Work.BoseB4.monoOp 0 0 (Work.BoseB4.KHC0 D)) (Work.BoseB4.split x) := by
  -- the scalar data of `K2ndDefs` unfold to the coefficient of `Hcontact`
  have hHc : Hcontact D
      = (cHC D) • ((cre m 0).comp ((cre m 0).comp ((ann m 0).comp (ann m 0)))) := by
    rw [Hcontact, cHC, i3]
  -- the four-fold word of `(cre m 0)`/`(ann m 0)` under `split`
  have hsplit : ∀ y : RealFock m,
      split ((cre m 0).comp ((cre m 0).comp ((ann m 0).comp (ann m 0))) y)
        = ((a0d.comp a0d).comp (a0.comp a0)) (split y) := by
    intro y
    have hann : ∀ z : RealFock m, split (ann m 0 z) = a0 (split z) := by
      intro z
      have h := LinearMap.congr_fun (Split_ann_zero (m := m)) z
      simpa [LinearMap.comp_apply, LinearMap.restrictScalars_apply] using h
    have hcre : ∀ z : RealFock m, split (cre m 0 z) = a0d (split z) := by
      intro z
      have h := LinearMap.congr_fun (Split_cre_zero (m := m)) z
      simpa [LinearMap.comp_apply, LinearMap.restrictScalars_apply] using h
    simp only [LinearMap.comp_apply, hann, hcre]
  -- `lift` of the identity is the identity, so `monoOp _ _ 1` has no spectator operator
  have hlift : lift (1 : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
      = (1 : FockCore (cfock (Excited m)) →ₗ[ℂ] FockCore (cfock (Excited m))) := by
    ext x n
    simp
  have hm2 : monoOp 2 2 (1 : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
      = (a0.comp a0).comp (a0d.comp a0d) := by
    rw [monoOp, hlift]
    ext x
    simp
  have hm1 : monoOp 1 1 (1 : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
      = a0.comp a0d := by
    rw [monoOp, hlift]
    ext x
    simp
  have hm0 : monoOp 0 0 (1 : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
      = (1 : FockCore (cfock (Excited m)) →ₗ[ℂ] FockCore (cfock (Excited m))) := by
    rw [monoOp, hlift]
    ext x
    simp
  -- the scalar identities matching `KHC1 D`, `KHC0 D` with `−4` and `2`
  have hc1 : (((-(4 * cHC D) : ℝ) : ℂ)) = -(((cHC D : ℝ) : ℂ) * 4) := by
    push_cast
    ring
  have hc2 : (((2 * cHC D : ℝ) : ℂ)) = (((cHC D : ℝ) : ℂ)) * 2 := by
    push_cast
    ring
  -- Wick's identity in the `monoOp` slots
  have hOp : (monoOp 2 2 (KHC2 D) + monoOp 1 1 (KHC1 D) + monoOp 0 0 (KHC0 D) :
      FockCore (cfock (Excited m)) →ₗ[ℂ] FockCore (cfock (Excited m)))
      = ((cHC D : ℝ) : ℂ) • ((a0d.comp a0d).comp (a0.comp a0)) := by
    simp only [KHC2, KHC1, KHC0, monoOp_smul]
    rw [hm2, hm1, hm0]
    rw [a0d_sq_comp_a0_sq (E := cfock (Excited m))]
    simp only [smul_add, smul_smul, hc1, hc2, sub_eq_add_neg]
    rw [smul_neg, smul_smul, ← neg_smul]
  calc split (Hcontact D x)
      = (cHC D) • split ((cre m 0).comp ((cre m 0).comp ((ann m 0).comp (ann m 0))) x) := by
          rw [hHc, LinearMap.smul_apply, LinearMap.map_smul]
    _ = (cHC D) • (((a0d.comp a0d).comp (a0.comp a0)) (split x)) := by rw [hsplit]
    _ = ((((cHC D : ℝ) : ℂ) • ((a0d.comp a0d).comp (a0.comp a0))) (split x)) := by
          rw [LinearMap.smul_apply]
          exact RCLike.real_smul_eq_coe_smul (K := ℂ) (cHC D)
            (((a0d.comp a0d).comp (a0.comp a0)) (split x))
    _ = (monoOp 2 2 (KHC2 D) + monoOp 1 1 (KHC1 D) + monoOp 0 0 (KHC0 D)) (split x) := by
          rw [hOp]

end Work.BoseB4
