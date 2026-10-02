/-
Copyright: subproject `Submission/Work/SeedCertNum/` of `mandelbar_not_path_connected`.

# The instantiated petal lemmas at the **ray area's** constants (`R = 4`)

`petal_P1` and `petal_P2` instantiated at the certified point with the `R = 4` constants of
`Submission/Work/SeedCertNum/EEConst4.lean`, using the sharper Taylor model `ee_taylor4` from
`Submission/Work/SeedCertNum/EESplit.lean` (`M = Mee4 = 566667`, `ρ₁ = 1/2724`, `ρ₂ = 2^-11`,
`R = 4`, `δ = 1/32`).  The `(C1)`, `(C2)` inequalities are `ee_petal_constants4`.

These are the objects the ray area `SeedCertRay` consumes, in the shape its
`landsAt_alphas_data` / `landsN_of_petal_of_isDynBottcher` ask for (`R = 4`, closed ball).
-/
import Mathlib
import Submission.Work.SeedCertNum.EESplit
import Submission.Work.SeedCertNum.EEConst4
import Submission.Work.SeedCertNum.EEInstance
import Submission.Work.SeedCertNum.Petal
import Submission.Work.SeedCertNum.petal_P1
import Submission.Work.SeedCertNum.petal_P2_closed

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCert

open LeanEval.ComplexAnalysis (Tantibar)

noncomputable section

theorem Mee4_nonneg : 0 ≤ Mee4 := by rw [Mee4_eq]; norm_num

/-- **`petal_P1` at the certified point, `R = 4`**: the sphere `‖u‖ = ρ₁` is mapped out of the
petal. -/
theorem petal_P1_instance4 :
    ∀ u : ℂ, ‖u‖ = rho1R4 → Work.FSeed.F cb (z1 + u) ∉ petal z1 Aquad RpetalR4 := by
  obtain ⟨hA, hρ1, hδ, hρρ, -, hsmall, hC1, hC2⟩ := ee_petal_constants4
  refine Work.SeedCertNum.petal_P1 (F := Work.FSeed.F cb) (E := Eerr) (z₁ := z1) (A := Aquad)
    (M := Mee4) (ρ₁ := rho1R4) (ρ₂ := rho2.toReal) (δ := deltapR4) (R := RpetalR4)
    hA Mee4_nonneg hρ1 (by simpa [rho2R4] using hρρ) hδ hsmall (fun u _ => Eerr_model u)
    (fun u hu => ee_taylor4 hu) hC1 ?_
  rw [RpetalR4]
  exact hC2

/-- **`petal_P2` at the certified point, `R = 4`, closed ball**: the petal is backward invariant
under `F`, with drift `δ`. -/
theorem petal_P2_instance4 :
    ∀ z : ℂ, ‖z - z1‖ ≤ rho1R4 → Work.FSeed.F cb z ∈ petal z1 Aquad RpetalR4 →
      z ∈ petal z1 Aquad RpetalR4 ∧
        (fatouW z1 Aquad z).re ≤ (fatouW z1 Aquad (Work.FSeed.F cb z)).re - deltapR4 := by
  obtain ⟨hA, hρ1, hδ, hρρ, -, hsmall, hC1, hC2⟩ := ee_petal_constants4
  refine Work.SeedCertNum.petal_P2_closed (F := Work.FSeed.F cb) (E := Eerr) (z₁ := z1)
    (A := Aquad) (M := Mee4) (ρ₁ := rho1R4) (ρ₂ := rho2.toReal) (δ := deltapR4) (R := RpetalR4)
    hA Mee4_nonneg hρ1 (by simpa [rho2R4] using hρρ) hδ hsmall (fun u _ => Eerr_model u)
    (fun u hu => ee_taylor4 hu) hC1 ?_
  rw [RpetalR4]
  exact hC2

/-- **The petal data the ray area needs**, packaged: the drift `δ`, the radius `ρ₁`, the depth
`R = 4`, `A ≠ 0`, the ball datum `1 ≤ R‖A‖ρ₁` (`Petal ⊆ closedBall z₁ ρ₁`), and the two petal
facts. -/
theorem ee_petal4_data :
    Aquad ≠ 0 ∧ 0 < rho1R4 ∧ 0 < deltapR4 ∧ 1 ≤ RpetalR4 * ‖Aquad‖ * rho1R4 ∧
    (∀ u : ℂ, ‖u‖ = rho1R4 → Work.FSeed.F cb (z1 + u) ∉ petal z1 Aquad RpetalR4) ∧
    (∀ z : ℂ, ‖z - z1‖ ≤ rho1R4 → Work.FSeed.F cb z ∈ petal z1 Aquad RpetalR4 →
      z ∈ petal z1 Aquad RpetalR4 ∧
        (fatouW z1 Aquad z).re ≤ (fatouW z1 Aquad (Work.FSeed.F cb z)).re - deltapR4) := by
  obtain ⟨hA, hρ1, hδ, -, hRQ, -, -, -⟩ := ee_petal_constants4
  exact ⟨hA, hρ1, hδ, hRQ, petal_P1_instance4, petal_P2_instance4⟩

end

end Work.SeedCert
