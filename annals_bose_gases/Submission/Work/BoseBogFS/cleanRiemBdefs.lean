import ChallengeDeps
import Submission.Work.BoseBogFS.BogFSCompare
import Submission.Work.BoseBogFS.CellExcessAux
import Submission.Work.BoseBogFS.honestFsCore
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.cleanRiemBdefs` — the per-cell majorant `bogBfun` of the clean Riemann row

This module **fixes the vocabulary** of the per-cell majorant used to prove
`Work.BoseBogFS.cleanFun_tsum_le_integral`.  See
`Submission/Work/BoseBogFS/FINDING_cleanFun_tsum_session18.md` §§1–2 for the design.

Everything is in the *scaled* variables `t = k/√P`, `P = ρ·a v`:

* `bogMesh v ρ μ = δ = (2π/ℓ)/√(ρ·a v)` — the scaled mesh, `tSca v ρ μ n = lpt δ n`;
* `bogRLo/bogRHi` — the two radii of the ball of radius `δ√3/2` about `lpt δ n`;
* `bogULo/bogUHi` — `τ_s` at those radii (so `u_lo ≤ τ_s(x) ≤ u_hi` on the cell);
* `bogVN` — `β_s` at the lattice point; `bogOscK` — the oscillation bound for `β_s`
  (`betaSc_sub_le`);
* `bogBsmall` — the small-region (τ-ball) majorant `o + Bhi²/(2 r_lo²) − Blo²/(2 r_hi²)`;
* `bogBbig` — the big-region majorant
  `U·V²/(W_lo S_lo) + 4 o V (3κ r_hi + 2V)/(r_lo² Mv) + V²(1/(2r_lo²) − 1/(2r_hi²))`;
* `bogBfun` — the assembled majorant, `0` at the origin cell (which is discharged separately by
  the PROVED `origin_cell_excess_le`).

The two per-cell bounds are delegated as `Work.BoseBogFS.psiSc_lpt_tauBall_cell_le`
(small region) and `Work.BoseBogFS.psiSc_lpt_big_cell_le` (big region); the present module is
definitions only.
-/

noncomputable section

open scoped Real Topology BigOperators

namespace Work.BoseBogFS

open _root_.BoseGases Work.UBB Work.BoseFixR

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The scaled mesh and the cell radii -/

/-- The scaled mesh `δ = (2π/ℓ)/√(ρ·a v)`. -/
def bogMesh (v : E3 → ℝ) (ρ μ : ℝ) : ℝ :=
  (2 * Real.pi / ell v μ) / Real.sqrt (ρ * a v)

/-- Half the space diagonal of a `δ`-cell: `Δ = δ√3/2`. -/
def bogHalf (v : E3 → ℝ) (ρ μ : ℝ) : ℝ :=
  bogMesh v ρ μ * Real.sqrt 3 / 2

/-- The lower edge radius of the cell of `n`. -/
def bogRLo (v : E3 → ℝ) (ρ μ : ℝ) (n : Fin 3 → ℤ) : ℝ :=
  ‖lpt (bogMesh v ρ μ) n‖ - bogHalf v ρ μ

/-- The upper edge radius of the cell of `n`. -/
def bogRHi (v : E3 → ℝ) (ρ μ : ℝ) (n : Fin 3 → ℤ) : ℝ :=
  ‖lpt (bogMesh v ρ μ) n‖ + bogHalf v ρ μ

/-- `τ_s` at the lower edge radius of the cell of `n`. -/
def bogULo (v : E3 → ℝ) (ρ μ : ℝ) (n : Fin 3 → ℤ) : ℝ :=
  tauScRad v ρ μ (bogRLo v ρ μ n)

/-- `τ_s` at the upper edge radius of the cell of `n`. -/
def bogUHi (v : E3 → ℝ) (ρ μ : ℝ) (n : Fin 3 → ℤ) : ℝ :=
  tauScRad v ρ μ (bogRHi v ρ μ n)

/-- `β_s` at the lattice point of the cell of `n`. -/
def bogVN (v : E3 → ℝ) (h : ScatSol v) (ρ μ : ℝ) (n : Fin 3 → ℤ) : ℝ :=
  betaSc v h ρ μ (lpt (bogMesh v ρ μ) n)

/-! ## 2. The auxiliary constants and envelopes -/

/-- The cell-oscillation bound for `β_s` with free constant `K`
(`betaSc_sub_le` supplies a universal `K`):
`K(1+R)³√(ρ/a)·Δ/(1+√(ρa)·r_lo)`. -/
def bogOscK (K R ρ av Δ rlo : ℝ) : ℝ :=
  K * (1 + R) ^ 3 * Real.sqrt (ρ / av) * Δ / (1 + Real.sqrt (ρ * av) * rlo)

/-- The lower envelope of the `v`-derivative's denominator:
`Mv = u_lo + W_lo + 2 v_lo`, `W_lo = √(u_lo² + 2 u_lo v_lo)`. -/
def bogMv (ulo vlo : ℝ) : ℝ :=
  ulo + Real.sqrt (ulo ^ 2 + 2 * ulo * vlo) + 2 * vlo

/-- The small-region threshold `N₀ = 2c₁ + 5Δ`: for `r_lo ≤ N₀` the cell is handled by
`bogBsmall` (`u` may be `0` there and the exact-`u`-derivative bound degenerates). -/
def bogSmallThr (v : E3 → ℝ) (ρ μ : ℝ) : ℝ :=
  2 * bogC1 v ρ μ + 5 * bogHalf v ρ μ

/-- The `χ⋆χ` Taylor deficit `δ_χ = 16π·chiTC·(R/ℓ)²` at the box scale. -/
def bogDeltaChi (v : E3 → ℝ) (R μ : ℝ) : ℝ :=
  16 * Real.pi * chiTC * (R / ell v μ) ^ 2

/-! ## 3. The two per-cell majorants -/

/-- **The small-region majorant**: on the τ-ball (`τ_s ≡ 0` there) `ψ = β − β²/(2‖t‖²)`, so with
`|β| ≤ Bhi` on the cell and `Blo ≤ β(t_n)`,
`ψ(t_n) − ⨍_{cell} ψ ≤ o + Bhi²/(2 r_lo²) − Blo²/(2 r_hi²)`. -/
def bogBsmall (v : E3 → ℝ) (h : ScatSol v) (R ρ μ Ko : ℝ) (n : Fin 3 → ℤ) : ℝ :=
  bogOscK Ko R ρ (a v) (bogHalf v ρ μ) (bogRLo v ρ μ n)
    + (8 * Real.pi + bogDeltaChi v R μ + 3 * bogEta v R ρ * bogRHi v ρ μ n) ^ 2
        / (2 * (bogRLo v ρ μ n) ^ 2)
    - (4 * Real.pi - bogDeltaChi v R μ) ^ 2 / (2 * (bogRHi v ρ μ n) ^ 2)

/-- **The big-region majorant**: with `u_lo > 0` (so `W_lo, S_lo, Mv > 0`) the
cancellation-preserving three-term bound of FINDING session 18 §2. -/
def bogBbig (v : E3 → ℝ) (h : ScatSol v) (R ρ μ Ko : ℝ) (n : Fin 3 → ℤ) : ℝ :=
  let rlo := bogRLo v ρ μ n
  let rhi := bogRHi v ρ μ n
  let ulo := bogULo v ρ μ n
  let uhi := bogUHi v ρ μ n
  let o := bogOscK Ko R ρ (a v) (bogHalf v ρ μ) rlo
  let vlo := bogVN v h ρ μ n - o
  let vhi := bogVN v h ρ μ n + o
  let V := max |vlo| |vhi|
  let W := Real.sqrt (ulo ^ 2 + 2 * ulo * vlo)
  let U := max 0 (Work.BoseB6.fsTau ((Work.BoseBox.paramsAt μ (a v)).eT) (bogC1 v ρ μ) (bogC2 v ρ μ) rhi
    - ((1 - (Work.BoseBox.paramsAt μ (a v)).eT) * (max 0 (rlo - 2 * bogC1 v ρ μ)) ^ 2
        + (Work.BoseBox.paramsAt μ (a v)).eT * (max 0 (rlo - 2 * bogC2 v ρ μ)) ^ 2))
  U * V ^ 2 / ((ulo + vlo + W) * W)
    + 4 * o * V * (3 * bogKappa v ρ μ * rhi + 2 * V) / (rlo ^ 2 * bogMv ulo vlo)
    + V ^ 2 * (1 / (2 * rlo ^ 2) - 1 / (2 * rhi ^ 2))

/-- **The assembled per-cell majorant** of the clean Riemann row: `0` on the origin cell (handled
by `origin_cell_excess_le`), `bogBsmall` on the small region and `bogBbig` elsewhere. -/
def bogBfun (v : E3 → ℝ) (h : ScatSol v) (R ρ μ Ko : ℝ) (n : Fin 3 → ℤ) : ℝ :=
  if n = 0 then 0
  else if bogRLo v ρ μ n ≤ bogSmallThr v ρ μ then bogBsmall v h R ρ μ Ko n
  else bogBbig v h R ρ μ Ko n

end Work.BoseBogFS
