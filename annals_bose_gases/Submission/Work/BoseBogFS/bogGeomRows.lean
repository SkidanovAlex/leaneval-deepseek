import ChallengeDeps
import Submission.Work.BoseBogFS.BogFSCompare
import Submission.Work.BoseBogFS.honestFsCutoffRows
import Submission.Work.BoseBogFS.honestFsSupp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.bogGeomRows` — the geometric regime of the Bogoliubov rows

The Bogoliubov comparison rows (`BogFSCompare`, `bogKAP_of_rows`, …) are all
stated under the three *geometric* hypotheses

* `0 < ℓ` (the box side is a genuine length),
* `R ≤ ℓ · chiR0` (the interaction radius fits inside the `χ⋆χ ≥ 1/2` ball, FS's
  large-box condition),
* `R / ℓ ≤ chiTR1` and `chiTC (R/ℓ)² ≤ 1/2` (the support-radius condition and the
  quadratic-boundedness condition of the `χ⋆χ` Taylor expansion).

Here `ℓ = Work.BoseFixR.ell v μ = sideAt μ (a v)` blows up like
`a (μa³)^{-163/323}` as the diluteness `μa³ ↓ 0`, while `R`, `chiR0`,
`chiTR1 ≥ 0` and `chiTC ≥ 0` are fixed constants.  Since `Adm v ε₀ μ` only
constrains the diluteness from above (`μ (a v)³ ≤ ε₀`), all four conditions hold
*on the whole admissible region* for a single small enough `ε₀` — the statement
proved here.

The content is entirely in the already-proved regime theorem
`Work.BoseBogFS.existsAdmRegime` (`Submission/Work/BoseBogFS/existsAdmRegime.lean`),
which produces the common threshold `ε₀` for the three display conditions; the
strict positivity `0 < ℓ` is then read off from
`R ≤ ℓ · chiR0` together with `0 < R` and `0 < chiR0`.  The clause
`CloseCondFS v μ ρ` plays no role: the geometry is independent of the state
label `ρ`.
-/

namespace Work.BoseBogFS

/-- **The geometric regime of the Bogoliubov chapter, at a common threshold.**
For every interaction radius `R > 0` and every potential `v` with positive
scattering length there is `ε₀ > 0` such that at every admissible chemical
potential `μ` (`0 < μ`, `μ (a v)³ ≤ ε₀`, `ParamsOK …`) the box side
`ℓ = Work.BoseFixR.ell v μ` is positive, dominates `R / chiR0`, keeps
`R / ℓ ≤ chiTR1`, and makes `chiTC (R/ℓ)² ≤ 1/2`. -/
theorem bogGeomRows {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ}
    (hR : 0 < R) (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → ∀ ρ : ℝ,
      Work.BoseBoxFock.CloseCondFS v μ ρ →
      0 < Work.BoseFixR.ell v μ ∧
      R ≤ Work.BoseFixR.ell v μ * Submission.BoseGases.chiR0 ∧
      R / Work.BoseFixR.ell v μ ≤ Work.BoseBogFS.chiTR1 ∧
      Work.BoseBogFS.chiTC * (R / Work.BoseFixR.ell v μ) ^ 2 ≤ 1 / 2 := by
  -- the common threshold for the three display conditions
  obtain ⟨ε₀, hε₀pos, hreg⟩ := existsAdmRegime (v := v) (R := R)
    (C := chiTC) (r₁ := chiTR1) hR hav chiTC_nonneg chiTR1_pos
  refine ⟨ε₀, hε₀pos, fun μ hμ ρ _hρ => ⟨?_, ?_, ?_, ?_⟩⟩
  · -- `0 < ℓ` from `R ≤ ℓ · chiR0`, `0 < R`, `0 < chiR0`
    have hpos : 0 < Work.BoseFixR.ell v μ * Submission.BoseGases.chiR0 :=
      lt_of_lt_of_le hR (hreg μ hμ).1
    exact pos_of_mul_pos_left hpos Submission.BoseGases.chiR0_pos.le
  · exact (hreg μ hμ).1
  · exact (hreg μ hμ).2.1
  · exact (hreg μ hμ).2.2

end Work.BoseBogFS
