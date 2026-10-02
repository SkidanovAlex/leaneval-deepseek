/-
Copyright: subproject `Submission/Work/SeedCertNum/` of `mandelbar_not_path_connected`.

# The instantiated petal lemmas (item E-E, final form)

`petal_P1` and `petal_P2` instantiated at the certified point: the Taylor model
`ee_taylor`, the constants `ee_petal_constants`, and `Aquad_mem`/`Aquad_normsq_bounds` discharge
every hypothesis.  This is the object the ray area consumes.
-/
import Mathlib
import Submission.Work.SeedCertNum.EE
import Submission.Work.SeedCertNum.Petal
import Submission.Work.SeedCertNum.petal_P1
import Submission.Work.SeedCertNum.petal_P2

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCert

open LeanEval.ComplexAnalysis (Tantibar)

noncomputable section

/-- The Taylor error of the model: `E u = F (z₁+u) - z₁ - u - A u²`. -/
def Eerr (u : ℂ) : ℂ := Work.FSeed.F cb (z1 + u) - z1 - u - Aquad * u ^ 2

theorem Mee_nonneg : 0 ≤ Mee := by rw [Mee_eq]; norm_num

theorem Eerr_model (u : ℂ) :
    Work.FSeed.F cb (z1 + u) = z1 + u + Aquad * u ^ 2 + Eerr u := by
  simp only [Eerr]; ring

/-- **`petal_P1` at the certified point**: the sphere `‖u‖ = ρ₁` is mapped out of the petal. -/
theorem petal_P1_instance :
    ∀ u : ℂ, ‖u‖ = rho1.toReal → Work.FSeed.F cb (z1 + u) ∉ petal z1 Aquad Rpetal := by
  obtain ⟨hA, hρ1, hδ, hρρ, -, hsmall, hC1, hC2⟩ := ee_petal_constants
  refine Work.SeedCertNum.petal_P1 (F := Work.FSeed.F cb) (E := Eerr) (z₁ := z1) (A := Aquad)
    (M := Mee) (ρ₁ := rho1.toReal) (ρ₂ := rho2.toReal) (δ := deltap) (R := Rpetal)
    hA Mee_nonneg hρ1 hρρ hδ hsmall (fun u _ => Eerr_model u)
    (fun u hu => ee_taylor hu) hC1 ?_
  rw [Rpetal]
  exact hC2

/-- **`petal_P2` at the certified point**: the petal is backward invariant under `F`, with drift
`δ`. -/
theorem petal_P2_instance :
    ∀ z : ℂ, z ∈ Metric.ball z1 rho1.toReal → Work.FSeed.F cb z ∈ petal z1 Aquad Rpetal →
      z ∈ petal z1 Aquad Rpetal ∧
        (fatouW z1 Aquad z).re ≤ (fatouW z1 Aquad (Work.FSeed.F cb z)).re - deltap := by
  obtain ⟨hA, hρ1, hδ, hρρ, -, hsmall, hC1, hC2⟩ := ee_petal_constants
  refine Work.SeedCertNum.petal_P2 (F := Work.FSeed.F cb) (E := Eerr) (z₁ := z1) (A := Aquad)
    (M := Mee) (ρ₁ := rho1.toReal) (ρ₂ := rho2.toReal) (δ := deltap) (R := Rpetal)
    hA Mee_nonneg hρ1 hρρ hδ hsmall (fun u _ => Eerr_model u)
    (fun u hu => ee_taylor hu) hC1 ?_
  rw [Rpetal]
  exact hC2

end

end Work.SeedCert
