/-
Copyright: subproject `Submission/Work/SeedCertNum/` of `mandelbar_not_path_connected`.

# The repelling petal of the parabolic point: vocabulary

`NOTES_LEAD_mandelbar_noncusp.md` §2.5 works with the Fatou coordinate of the (simple) parabolic
point `z₁` of `F = (T_c)^[10]`, whose quadratic coefficient is `A = F''(z₁)/2`:

  `w(u) = -1/(A u)`,  `u = z - z₁`,

so that `w(F z) = w(z) + 1 + o(1)` and the repelling petals are `Re w < -R`.

* `fatouW z₁ A z` — the Fatou coordinate (a function of `z`, with the pole at `z = z₁`);
* `petal z₁ A R` — the repelling petal of depth `R`, `{z | Re (fatouW z₁ A z) < -R}` (with
  `z = z₁` excluded; note `fatouW` is `0` at the pole because `1/0 = 0` in `ℂ`, and `0 < -R` is
  false, so the exclusion is automatic for `R > 0` — it is stated explicitly anyway).

The two lemmas that make the petal into a *trap* for the ray are `petal_P1` and `petal_P2`
(`Submission/Work/SeedCertNum/petal_P1.lean`, `petal_P2.lean`); their numerical hypotheses
`(C1)`, `(C2)` are the constants certified by items A3 and E-E of the contract.
-/
import ChallengeDeps

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCert

/-- The Fatou coordinate `w(u) = -1/(A u)` at the parabolic point `z₁` with quadratic coefficient
`A`: `fatouW z₁ A z = -1/(A (z - z₁))`. -/
noncomputable def fatouW (z₁ A z : ℂ) : ℂ := -1 / (A * (z - z₁))

/-- The repelling petal of depth `R`: the points with `Re (fatouW z₁ A z) < -R`. -/
def petal (z₁ A : ℂ) (R : ℝ) : Set ℂ :=
  {z : ℂ | z ≠ z₁ ∧ (fatouW z₁ A z).re < -R}

@[simp] theorem mem_petal {z₁ A z : ℂ} {R : ℝ} :
    z ∈ petal z₁ A R ↔ z ≠ z₁ ∧ (fatouW z₁ A z).re < -R := Iff.rfl

end Work.SeedCert
