import Mathlib
import Submission.Work.Drive.trigRelation_trivial
import Submission.Work.Drive.jetF_zero_of_coeff
import Submission.Work.Drive.coeff_zero_of_jetFc
import Submission.Work.Drive.jetDefs
import Submission.Work.Drive.jets_independent
import Submission.Work.Drive.scalar_surjective_of_independent
import Submission.Work.Drive.space_surjective_of_scalar

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

noncomputable section

/-- **The nine trigonometric functions of degree ≤ 4 realise arbitrary values and first
derivatives at three pairwise distinct parameters of `[0, 2π)`.**

`trigBasis : Fin 9 → ℝ → ℝ` is `(1, cos t, sin t, cos 2t, sin 2t, cos 3t, sin 3t, cos 4t,
sin 4t)` and `trigBasisD` its derivative (`knotPerturbDefs.lean`).

Reusable pieces already in the workspace:
* `Work.Drive.jetCoeff`, `jetF`, `jetFc`, `jetExp`, `jetTarget`, `spaceCoord`, `spaceOfFun`
  (`Submission/Work/Drive/jetDefs.lean`);
* `Work.Drive.jetF_zero_of_coeff` (`jetF_zero_of_coeff.lean`): a vanishing linear combination
  of the six functionals gives `jetF p q r α β γ δ ε ζ k = 0` for every `|k| ≤ 4`;
* `Work.Drive.coeff_zero_of_jetFc` (`coeff_zero_of_jetFc.lean`): for `p,q,r ∈ [0,2π)`
  pairwise distinct those equations force all six coefficients to vanish — i.e. the six
  functionals `x ↦ ∑ j, jetCoeff p q r i j * x j` on `Fin 9 → ℝ` are linearly independent.

Route for this lemma: linear independence of the six functionals on `Fin 9 → ℝ` gives that
the scalar map `(Fin 9 → ℝ) → (Fin 6 → ℝ)`, `x ↦ (∑ j, jetCoeff p q r i j * x j)_i`, is
surjective (finite-dimensional duality: a linear functional vanishing on its range would
give a nontrivial linear relation).  Tensorising with `Space = ℝ³` — via the coordinates
`spaceCoord k` and their section `spaceOfFun` — turns a scalar preimage into a preimage in
`Fin 9 → Space`; the six target values are packaged by `jetTarget`.

Note: `Submission/Work/Drive/exists_coeff_jets.lean` contains this same statement proved by the
same route; the present proof is self-contained in this file. -/
theorem jets_surjective (p q r : ℝ) (hp : p ∈ Set.Ico 0 (2 * Real.pi))
    (hq : q ∈ Set.Ico 0 (2 * Real.pi)) (hr : r ∈ Set.Ico 0 (2 * Real.pi))
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (xp xq xr yp yq yr : LeanEval.KnotTheory.Quadrisecant.Space) :
    ∃ c : Fin 9 → LeanEval.KnotTheory.Quadrisecant.Space,
      (∑ j : Fin 9, (Work.Drive.trigBasis j p) • c j) = xp ∧
      (∑ j : Fin 9, (Work.Drive.trigBasisD j p) • c j) = yp ∧
      (∑ j : Fin 9, (Work.Drive.trigBasis j q) • c j) = xq ∧
      (∑ j : Fin 9, (Work.Drive.trigBasisD j q) • c j) = yq ∧
      (∑ j : Fin 9, (Work.Drive.trigBasis j r) • c j) = xr ∧
      (∑ j : Fin 9, (Work.Drive.trigBasisD j r) • c j) = yr := by
  -- the six jet functionals are linearly independent on the coefficient space
  have hind : ∀ c : Fin 6 → ℝ, (∀ j : Fin 9, ∑ i : Fin 6, c i * jetCoeff p q r i j = 0) → c = 0 := by
    intro c hc
    have h6 : ∀ j : Fin 9, (c 0) * trigBasis j p + (c 1) * trigBasisD j p + (c 2) * trigBasis j q
        + (c 3) * trigBasisD j q + (c 4) * trigBasis j r + (c 5) * trigBasisD j r = 0 := by
      intro j
      have h := hc j
      rw [sum_six] at h
      simpa [jetCoeff] using h
    obtain ⟨h0, h1, h2, h3, h4, h5⟩ :=
      jets_independent p q r hp hq hr hpq hpr hqr (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) h6
    funext i
    fin_cases i <;> assumption
  -- hence the scalar jets can be prescribed, and hence the `Space`-valued ones
  have hsurj := fun A : Fin 6 → Space => space_surjective_of_scalar (ℓ := jetCoeff p q r)
    (scalar_surjective_of_independent (ℓ := jetCoeff p q r) hind) A
  obtain ⟨c, hc⟩ := hsurj (jetTarget xp yp xq yq xr yr)
  exact ⟨c, by simpa [jetCoeff, jetTarget] using hc 0,
    by simpa [jetCoeff, jetTarget] using hc 1,
    by simpa [jetCoeff, jetTarget] using hc 2,
    by simpa [jetCoeff, jetTarget] using hc 3,
    by simpa [jetCoeff, jetTarget] using hc 4,
    by simpa [jetCoeff, jetTarget] using hc 5⟩

end

end Work.Drive
