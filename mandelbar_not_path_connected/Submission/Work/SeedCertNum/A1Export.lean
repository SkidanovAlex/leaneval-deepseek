/-
Copyright: subproject `Submission/Work/SeedCertNum/` of `mandelbar_not_path_connected`.

# The A1/A3 exports for the seed

The interface of the `SeedCertNum` area to the seed: the certified point `(z₁, c_b)`, its
`Mandelbar` membership (given the classical Fatou input), the fact that `z₁` lies in the exported
box, and the simplicity of the parabolic point.

## Main results

* `z1_mem`, `cb_re`, `cb_im_mem` — location of the certified point;
* `cb_mem_Mandelbar` — `c_b ∈ Mandelbar` given `Work.FatouParabolic.FatouParabolicInput`;
* `explicitRootSeed_core` — the `NonCuspRootLimit` core, minus the landing clauses.
-/
import Mathlib
import Submission.Work.SeedCertNum.A1
import Submission.Work.SeedCertNum.A3
import Submission.Work.SeedCertNum.mem_Mandelbar_of_parabolic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCert

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

noncomputable section

theorem z1_mem : z1 ∈ krawData.Xz.toSet := krawU_z_mem

theorem cb_im_mem : krawU.2.2 ∈ krawData.Xt.toSet := krawU_t_mem

/-- The real part of the certified parameter, exactly. -/
theorem cb_re : cb.re = (-1293728561597 / 2 ^ 40 : ℝ) := by
  have h : cb.re = krawData.x₀.toReal := by simp [cb, cOf_apply]
  rw [h, show krawData.x₀ = dy (-1293728561597) 40 from rfl]
  norm_num [dy, Dya.toReal]

/-- The certified parameter lies in the mandelbar, given the classical Fatou input. -/
theorem cb_mem_Mandelbar (hfat : Work.FatouParabolic.FatouParabolicInput) : cb ∈ Mandelbar :=
  Work.SeedCertNum.mem_Mandelbar_of_parabolic hfat g_fix mult_one

/-- **The core of the seed supplied by this area**: an explicit parameter `c_b` of the mandelbar
whose second return map has a *simple* parabolic fixed point of *exact period* `5` at `z₁` — the
`NonCuspRootLimit` clauses minus the two landing statements (which are the ray area's business). -/
theorem explicitRootSeed_core (hfat : Work.FatouParabolic.FatouParabolicInput) :
    ∃ c z₁ : ℂ, c ∈ Mandelbar ∧ (Tantibar c)^[5] z₁ = z₁ ∧
      (∀ j : ℕ, 0 < j → j < 5 → (Tantibar c)^[j] z₁ ≠ z₁) ∧
      Work.Landing.multiplier2 c 5 z₁ = 1 ∧
      iteratedDeriv 2 (Work.FSeed.F c) z₁ ≠ 0 :=
  ⟨cb, z1, cb_mem_Mandelbar hfat, g_fix, exact_period, mult_one, iteratedDeriv2_ne_zero⟩

end

end Work.SeedCert
