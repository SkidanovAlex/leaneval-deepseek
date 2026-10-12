import ChallengeDeps
import Submission.Work.BoseB1Cube.denseAliveAssembly
import Submission.Work.BoseFixB1S.PerBoxGapAbsorbB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB1Cube

/-- **The coefficient gate of BRIEF `cubeAliveLedger.md` §2d item 1** — the last unproved row of the
`hgap` slot of `Work.BoseB1Cube.denseAliveWindow_bud`.

`Work.BoseFixB1.bGapCoeff v μ` is *definitionally* `tbGapCoeff (bSide v μ * bD v μ) (paramsAt μ (a v)).eT`,
so this is the **coefficient-level twin of `gapAbsorbB1`** (which gives only the `ν`-weighted
`KgD·μ·a·ν ≤ tbGapCoeff`): for every prescribed fixed `KgD ≥ 0` one may shrink the free `ε₀` of `Adm`
so that the coefficient itself dominates `KgD·μ·(a v)`, uniformly in `μ`.

**This is the only remaining input of item 1**: with it, `Work.BoseB1Cube.hgap_of_gate`
(`cubeLedgerHgapDiv.lean`, PROVED) turns it into the `hgap` slot of `denseAliveWindow_bud` at
`bg := sbKinCube/ν` — using only `sbKinCube = bGapCoeff·ν + cubeSpectral` and `cubeSpectral ≥ 0`.
The `Q = 0` sanity check (`sbKinCube ≥ 0` at `ν = 0`) is why the *bare* row `tbGapCoeff ≤ sbKinCube`
was the wrong target and this coefficient gate the right one — see §2d.

**Reviewers' guidance (both passed it; use it):** reviewer 1 verified by actually running Lean that
with `import Submission.Work.BoseFixB1S.PerBoxGapAbsorbB1` (or `…BoseFixB1.tbGapCoeffGate`) it is a
few-line corollary (`KgD = 0` via `tbGapCoeff_nonneg` + `(adm_eT_bounds hAdm).1`; `KgD > 0` via
`tbGapCoeffGate`/`PerBoxGapAbsorbB1` then `simp`/`linarith`) — so **do not re-derive** the private
`coef_absorb` arithmetic; the proof is already *inside* `gapAbsorbB1` as its `hcoef` step.  Reviewer 2
pins the shape: `bGapCoeff v μ = ½·tbPiFactor·t^{1279/4}·(a v)⁻²` with `t = μ(a v)³`
(`tbGapCoeff_sideAt_eq`), so the claim reduces to `KgD ≤ ½·tbPiFactor·t^{−13/1292}` — monotone in
`t ≤ ε₀`, giving an explicit `ε₀`.  `hav` is unused (`Adm` already gives `0 < a v`).  The two
`tbGapCoeff` arguments agree only up to `mul_comm` — expect one `mul_comm` rewrite. -/
theorem bGapCoeff_gate {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hav : 0 < _root_.BoseGases.a v)
    (KgD : ℝ) (hKgD : 0 ≤ KgD) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      KgD * (μ * (_root_.BoseGases.a v)) ≤ Work.BoseFixB1.bGapCoeff v μ := by
  -- `PerBoxGapAbsorbB1` is the `ν`-free arithmetic gate at an explicit `a v > 0`:
  -- `KgD·μ·(a v) ≤ tbGapCoeff (d·ℓ) ε_T`.  It carries the whole `coef_absorb` computation
  -- (monotonicity of `t ↦ t^{-13/1292}` against the explicit threshold `ε₀`), and it accepts
  -- `KgD = 0` (where the right-hand side is a nonnegative coefficient, not a `ν`-weighted form).
  obtain ⟨ε₀, hε₀, hmain⟩ := Work.BoseFixB1S.PerBoxGapAbsorbB1 (v := v) hav KgD hKgD
  refine ⟨ε₀, hε₀, fun μ hAdm => ?_⟩
  have h := hmain μ hAdm
  -- `bGapCoeff v μ` is `tbGapCoeff (sideAt μ (a v) * (paramsAt μ (a v)).d) ·` — the two factors
  -- of the small-box side are in the other order than in `PerBoxGapAbsorbB1`.
  have harg : Work.BoseFixB1.bGapCoeff v μ
      = Work.SmallBoxTBWord.tbGapCoeff
          ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
            * Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT := by
    show Work.SmallBoxTBWord.tbGapCoeff
        (Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ)
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT = _
    rw [Work.BoseFixB1.bSide, Work.BoseFixB1.bD,
      mul_comm (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))]
  rw [harg, show KgD * (μ * _root_.BoseGases.a v) = KgD * μ * _root_.BoseGases.a v by ring]
  exact h

end Work.BoseB1Cube
