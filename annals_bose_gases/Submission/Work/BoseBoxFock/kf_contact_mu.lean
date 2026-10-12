import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.l2Space
import Submission.Work.BoseBoxFock.KafzHonest
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.kf_contact_mu`

The **contact row** `(a₀†)²a₀²` and the **chemical-potential row** `a₀†a₀` of the
`thm:Kafz` dictionary (`Submission/Work/BoseBoxFock/KafzHonest.lean`, §6–7 and the
row table of `KAFZ_HONEST_ROUTE.md`), assembled into the single combined statement
used by the honest-model assembly:

    split (c₁ • crePow 2 (annPow 2 x) + c₂ • crePow 1 (annPow 1 x))
      = (c₁ • (monoOp 2 2 1 − 4 monoOp 1 1 1 + 2 monoOp 0 0 1)
          + c₂ • (monoOp 1 1 1 − monoOp 0 0 1)) (split x).

The two summands are exactly the anti-normal (Wick) expansions of the condensate
words

    (a₀†)²a₀² = a₀²(a₀†)² − 4 a₀a₀† + 2,      a₀†a₀ = a₀a₀† − 1

(FS `eq:subst-z`, rows `|z|⁴ − 4|z|² + 2` and `|z|² − 1`).

## Proof

* the **contact** row is `Work.BoseBoxFock.split_sandwich_mono` with `p = q = 2`
  and spectator word the identity (`lift 1 = 1`), which reduces it to the binomial
  sum `∑_{k≤2} (−1)^k k! C(2,k)² • monoOp (2−k) (2−k) 1`; evaluating the three
  terms gives `monoOp 2 2 1 − 4 • monoOp 1 1 1 + 2 • monoOp 0 0 1`
  (equivalently `Work.BoseB4.a0dpow_comp_lift_comp_a0pow`);
* the **chemical-potential** row is the pointwise form of the CCR reordering
  `a₀†a₀ = a₀a₀† − 1` (`Work.BoseB4.ccr` as in `a0_a0d_apply`), together with
  `monoOp 1 1 1 = a₀ ∘ a₀†` and `monoOp 0 0 1 = 1` (`Work.BoseB4.split_Hmu_monoOp11`
  / `split_Hmu_monoOp00`);
* the two rows are added and scaled: `split` is `ℝ`-linear (`map_add`, `map_smul`)
  and `monoOp` is additive/`ℂ`-homogeneous in its spectator slot, so the applied
  sum of the two linear maps is `LinearMap.add_apply` + `LinearMap.smul_apply`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseBoxFock

open Work.BoseB4

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-- **The contact row** `(a₀†)²a₀²` under `split`: the Wick expansion
`monoOp 2 2 1 − 4 • monoOp 1 1 1 + 2 • monoOp 0 0 1` (the spectator word is the
identity, `lift 1 = 1`). -/
private lemma split_crePow_two_annPow_two {m : ℕ} [NeZero m] (x : RealFock m) :
    split (crePow (m := m) 2 (annPow (m := m) 2 x))
      = ((monoOp 2 2 (1 : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
          - (4 : ℂ) • monoOp 1 1 (1 : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
          + (2 : ℂ) • monoOp 0 0 (1 : cfock (Excited m) →ₗ[ℂ] cfock (Excited m)))
          (split x)) := by
  -- the general sandwich with the identity spectator word, `p = q = 2`
  have h := split_sandwich_mono (m := m) 2 2
    (1 : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (LinearMap.id : RealFock m →ₗ[ℝ] RealFock m) (by intro y; rw [lift_one]; rfl) x
  simp only [LinearMap.id_apply] at h
  rw [h]
  congr 1
  -- evaluate the three-term binomial sum
  norm_num [Finset.sum_range_succ]
  rw [sub_eq_add_neg]
  congr 1
  exact neg_smul (4 : ℂ) (monoOp 1 1 (1 : cfock (Excited m) →ₗ[ℂ] cfock (Excited m)))

/-- **The chemical-potential row** `a₀†a₀` under `split`: the Wick expansion
`monoOp 1 1 1 − monoOp 0 0 1`. -/
private lemma split_crePow_one_annPow_one {m : ℕ} [NeZero m] (x : RealFock m) :
    split (crePow (m := m) 1 (annPow (m := m) 1 x))
      = ((monoOp 1 1 (1 : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
          - monoOp 0 0 (1 : cfock (Excited m) →ₗ[ℂ] cfock (Excited m)))
          (split x)) := by
  -- `a₀†a₀ = a₀a₀† − 1` pointwise (the CCR solved for `a₀†`),
  -- `monoOp 1 1 1 = a₀ ∘ a₀†` and `monoOp 0 0 1 = 1`.
  have hsub : ∀ y : FockCore (cfock (Excited m)),
      a0d (a0 y) = ((monoOp 1 1 (1 : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
          - monoOp 0 0 (1 : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))) y) := by
    intro y
    have h := a0_a0d_apply (m := m) y
    rw [LinearMap.sub_apply, split_Hmu_monoOp11, split_Hmu_monoOp00, LinearMap.comp_apply,
      Module.End.one_apply]
    rw [h]
    abel
  calc split (crePow (m := m) 1 (annPow (m := m) 1 x))
      = a0d (a0 (split x)) := by
        rw [crePow_one, annPow_one, split_cre_zero, split_ann_zero]
    _ = ((monoOp 1 1 (1 : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
          - monoOp 0 0 (1 : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))) (split x)) :=
        hsub (split x)

theorem kf_contact_mu {m : ℕ} [NeZero m] (c1 c2 : ℝ) (x : Work.BoseB4.RealFock m) :
    Work.BoseB4.split ((c1 • (Work.BoseBoxFock.crePow (m := m) 2 (Work.BoseBoxFock.annPow (m := m) 2 x)))
      + (c2 • (Work.BoseBoxFock.crePow (m := m) 1 (Work.BoseBoxFock.annPow (m := m) 1 x))))
      = (((c1 : ℂ) • (Work.BoseB4.monoOp 2 2 (1 : Work.BoseB4.cfock (Work.BoseB4.Excited m) →ₗ[ℂ] Work.BoseB4.cfock (Work.BoseB4.Excited m))
            - (4 : ℂ) • Work.BoseB4.monoOp 1 1 (1 : Work.BoseB4.cfock (Work.BoseB4.Excited m) →ₗ[ℂ] Work.BoseB4.cfock (Work.BoseB4.Excited m))
            + (2 : ℂ) • Work.BoseB4.monoOp 0 0 (1 : Work.BoseB4.cfock (Work.BoseB4.Excited m) →ₗ[ℂ] Work.BoseB4.cfock (Work.BoseB4.Excited m))))
        + (c2 : ℂ) • (Work.BoseB4.monoOp 1 1 (1 : Work.BoseB4.cfock (Work.BoseB4.Excited m) →ₗ[ℂ] Work.BoseB4.cfock (Work.BoseB4.Excited m))
            - Work.BoseB4.monoOp 0 0 (1 : Work.BoseB4.cfock (Work.BoseB4.Excited m) →ₗ[ℂ] Work.BoseB4.cfock (Work.BoseB4.Excited m))))
        (Work.BoseB4.split x) := by
  have h2 := split_crePow_two_annPow_two (m := m) x
  have h1 := split_crePow_one_annPow_one (m := m) x
  rw [map_add]
  rw [map_smul, map_smul]
  rw [h2, h1]
  -- the remaining identity is purely definitional: `LinearMap.add_apply`,
  -- `LinearMap.smul_apply` (both pointwise) and `(r : ℝ) • v = (r : ℂ) • v`
  rfl

end Work.BoseBoxFock
