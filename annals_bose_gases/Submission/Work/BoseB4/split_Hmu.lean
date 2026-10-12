import Mathlib
import Submission.Work.BoseB4.K2ndDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.split_Hmu` — the `−μĝ(0)a₀†a₀` row under the ⟨condensate | excited⟩ split

FS `eq:HLambdaSecond` carries the chemical-potential row `Hmu D = c·n₀` with
`c = −μĝ(0)` and `n₀ = a₀†a₀ = cre m 0 ∘ ann m 0` the number operator of the
condensate mode of the mode lattice.  Under the split
`Work.BoseB4.split : RealFock m →ₗ[ℝ] FockCore (cfock (Excited m))` of
`Work.BoseB4.Split` it becomes the anti-normal spectator operator

    `monoOp 1 1 (Kmu1 D) + monoOp 0 0 (Kmu0 D)`

with `Kmu1 D = c • 1` and `Kmu0 D = (−c) • 1` on the spectator space.  The reason
is the canonical commutation relation `Work.BoseB4.ccr` `a₀a₀† = a₀†a₀ + 1`:
the reordering `a₀†a₀ = a₀a₀† − 1` of the Wick expansion
`Work.BoseB4.a0dpow_comp_lift_comp_a0pow` has the `(1,1)` slot `a₀a₀†` with the
coefficient `c` and the `(0,0)` slot with the coefficient `−c`.

The proof is a computation on the basis vectors, using the condensate dictionary
`Split_cre_zero` (`cre m 0 ↔ a0d`) and `Split_ann_zero` (`ann m 0 ↔ a0`), the
identification `lift 1 = 1` of the identity spectator operator, and `ccr`.
-/

noncomputable section

open scoped lp BigOperators

namespace Work.BoseB4

set_option autoImplicit false

set_option maxHeartbeats 1000000

variable {m : ℕ} [NeZero m]

/-! ## The condensate ladder of the mode lattice under `split` -/

/-- The lattice creation of the condensate mode is the abstract `a0d` under the split. -/
lemma split_Hmu_condensate_cre (v : RealFock m) : split (cre m 0 v) = a0d (split v) := by
  have h := congrArg (fun f => f v) (Split_cre_zero (m := m))
  simpa [LinearMap.comp_apply] using h

/-- The lattice annihilation of the condensate mode is the abstract `a0` under the split. -/
lemma split_Hmu_condensate_ann (v : RealFock m) : split (ann m 0 v) = a0 (split v) := by
  have h := congrArg (fun f => f v) (Split_ann_zero (m := m))
  simpa [LinearMap.comp_apply] using h

/-! ## The `(1,1)` and `(0,0)` anti-normal monomials with the identity spectator -/

/-- `lift 1 = 1`: the identity spectator operator lifts to the identity. -/
lemma split_Hmu_lift_one : lift (1 : cfock (Excited m) →ₗ[ℂ] cfock (Excited m)) = 1 := by
  ext Ψ n; simp

/-- `monoOp 1 1 1 = a₀ ∘ a₀†`. -/
lemma split_Hmu_monoOp11 : monoOp 1 1 (1 : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    = (a0 : FockCore (cfock (Excited m)) →ₗ[ℂ] FockCore (cfock (Excited m))).comp a0d := by
  ext Ψ n; simp [monoOp]

/-- `monoOp 0 0 1 = 1`. -/
lemma split_Hmu_monoOp00 : monoOp 0 0 (1 : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    = (1 : FockCore (cfock (Excited m)) →ₗ[ℂ] FockCore (cfock (Excited m))) := by
  rw [monoOp_zero_zero, split_Hmu_lift_one]

/-- The pointwise commutation relation `a₀(a₀†v) = a₀†(a₀v) + v` on the core. -/
lemma split_Hmu_a0a0d (v : FockCore (cfock (Excited m))) :
    (a0 : FockCore (cfock (Excited m)) →ₗ[ℂ] FockCore (cfock (Excited m))) (a0d v)
      = a0d (a0 v) + v := by
  have h := LinearMap.congr_fun (ccr (E := cfock (Excited m))) v
  simpa [LinearMap.comp_apply, LinearMap.add_apply] using h

/-! ## The general form -/

/-- For any real scalar `c`, the row `c·n₀ = c·(cre m 0 ∘ ann m 0)` — i.e. `Hmu`
for `c = −μĝ(0)` — corresponds under `split` to
`c·monoOp 1 1 1 + (−c)·monoOp 0 0 1`, the anti-normal expansion of `c·a₀†a₀`. -/
theorem split_Hmu_general (c : ℝ) (x : RealFock m) :
    split ((c • ((cre m 0).comp (ann m 0))) x)
      = (monoOp 1 1 ((c : ℂ) • (1 : cfock (Excited m) →ₗ[ℂ] cfock (Excited m)))
          + monoOp 0 0 (((-c : ℝ) : ℂ) • (1 : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))))
        (split x) := by
  have hL : split ((c • ((cre m 0).comp (ann m 0))) x)
      = (c : ℂ) • (a0d (a0 (split x))) := by
    rw [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.map_smul,
        split_Hmu_condensate_cre, split_Hmu_condensate_ann]
    rfl
  rw [hL, LinearMap.add_apply]
  have h1 : (monoOp 1 1 ((c : ℂ) • (1 : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))))
      (split x) = (c : ℂ) • (a0 (a0d (split x))) := by
    rw [monoOp_smul, split_Hmu_monoOp11]
    rfl
  have h0 : (monoOp 0 0 (((-c : ℝ) : ℂ) • (1 : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))))
      (split x) = (((-c : ℝ) : ℂ)) • (split x) := by
    rw [monoOp_smul, split_Hmu_monoOp00]
    rfl
  rw [h1, h0, split_Hmu_a0a0d, Complex.ofReal_neg,
    neg_smul (M := FockCore (cfock (Excited m))), smul_add (M := ℂ) (A := FockCore (cfock (Excited m)))]
  abel

/-! ## The FS row `−μĝ(0)a₀†a₀` -/

theorem split_Hmu {m : ℕ} [NeZero m] (D : Work.BoseB4.H2ndData m) (x : Work.BoseB4.RealFock m) :
    Work.BoseB4.split (Work.BoseB4.Hmu D x)
      = (Work.BoseB4.monoOp 1 1 (Work.BoseB4.Kmu1 D)
          + Work.BoseB4.monoOp 0 0 (Work.BoseB4.Kmu0 D)) (Work.BoseB4.split x) := by
  have h := split_Hmu_general (m := m) (-(D.mu * D.g0)) x
  simpa only [Hmu, cMu, Kmu1, Kmu0] using h

end Work.BoseB4
