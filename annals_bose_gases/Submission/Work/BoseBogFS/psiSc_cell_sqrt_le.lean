import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseBogFS.CleanRiem
import Submission.Work.BoseBogFS.ZPCleanDefs
import Submission.Work.BoseBogFS.cellPhi_beta_le
import Submission.Work.BoseBogFS.cellPhi_tau_le
import Submission.Work.BoseBogFS.radialPair_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

set_option autoImplicit false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The per-cell `√`-difference bound of the scaled clean bracket `psiSc`.**

With `t = tSca v ρ μ n` the lattice point of the label `n` and `x` a second point of the same
cell (`‖x - t‖ ≤ Δ`), suppose the scaled kinetic symbol and pairing coefficient of the two
points lie in the windows `[u_lo,u_hi]` and `[v_lo,v_hi]`, that the radius of both lies in
`[r_lo,r_hi]` with `r_lo > 0`, and that the pairing coefficient oscillates by at most `o` on
the cell (`hosc`).  Then

  `psiSc t - psiSc x ≤ (u_hi-u_lo) + √((u_hi-u_lo)(2u_hi + 2V)) + o + √(2ou_hi)`
  `                + o·V/r_lo² + V²(1/(2r_lo²) - 1/(2r_hi²))`,  `V = max |v_lo| |v_hi|`.

The three terms of the first line are the `τ`-increment, the `β`-increment (through the
elementary `√B - √A ≤ √(B-A)`) and the radial `1/r²`-difference; no sign hypothesis on the
pairing coefficient is needed, because the *junk* convention `√y = 0` for `y < 0` makes the
degenerate branches consistent (`cellSplitDefs`). -/
theorem psiSc_cell_sqrt_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {ρ μ : ℝ} (n : Fin 3 → ℤ) {x : EuclideanSpace ℝ (Fin 3)}
    {Δ o u_lo u_hi v_lo v_hi r_lo r_hi : ℝ}
    (hΔ : 0 < Δ) (ho : 0 ≤ o) (hx : ‖x - Work.BoseBogFS.tSca v ρ μ n‖ ≤ Δ)
    (hosc : ∀ y : EuclideanSpace ℝ (Fin 3), ‖y - Work.BoseBogFS.tSca v ρ μ n‖ ≤ Δ →
      |Work.BoseBogFS.betaSc v h ρ μ y - Work.BoseBogFS.betaSc v h ρ μ (Work.BoseBogFS.tSca v ρ μ n)| ≤ o)
    (hu0 : 0 ≤ u_lo)
    (hu_lo : u_lo ≤ Work.BoseBogFS.tauSc v ρ μ x)
    (hu_hi : Work.BoseBogFS.tauSc v ρ μ x ≤ u_hi)
    (hu_lo' : u_lo ≤ Work.BoseBogFS.tauSc v ρ μ (Work.BoseBogFS.tSca v ρ μ n))
    (hu_hi' : Work.BoseBogFS.tauSc v ρ μ (Work.BoseBogFS.tSca v ρ μ n) ≤ u_hi)
    (hv_lo : v_lo ≤ Work.BoseBogFS.betaSc v h ρ μ x)
    (hv_hi : Work.BoseBogFS.betaSc v h ρ μ x ≤ v_hi)
    (hv_lo' : v_lo ≤ Work.BoseBogFS.betaSc v h ρ μ (Work.BoseBogFS.tSca v ρ μ n))
    (hv_hi' : Work.BoseBogFS.betaSc v h ρ μ (Work.BoseBogFS.tSca v ρ μ n) ≤ v_hi)
    (hr_lo : r_lo ≤ ‖x‖) (hr_hi : ‖x‖ ≤ r_hi)
    (hr_lo' : r_lo ≤ ‖Work.BoseBogFS.tSca v ρ μ n‖)
    (hr_hi' : ‖Work.BoseBogFS.tSca v ρ μ n‖ ≤ r_hi) (hr0 : 0 < r_lo) :
    Work.BoseBogFS.psiSc v h ρ μ (Work.BoseBogFS.tSca v ρ μ n) - Work.BoseBogFS.psiSc v h ρ μ x
      ≤ (u_hi - u_lo)
        + Real.sqrt ((u_hi - u_lo) * (2 * u_hi + 2 * max |v_lo| |v_hi|))
        + o + Real.sqrt (2 * o * u_hi)
        + o * (max |v_lo| |v_hi|) / r_lo ^ 2
        + (max |v_lo| |v_hi|) ^ 2 * (1 / (2 * r_lo ^ 2) - 1 / (2 * r_hi ^ 2)) := by
  set V := max |v_lo| |v_hi| with hVdef
  -- `psiSc` is `gFun` at the scaled data
  have hpsi : ∀ t : E3, Work.BoseBogFS.psiSc v h ρ μ t
      = Work.BoseB6Est.gFun (Work.BoseBogFS.tauSc v ρ μ t)
          (Work.BoseBogFS.betaSc v h ρ μ t) ‖t‖ := fun t => by
    rw [Work.BoseBogFS.psiSc, Work.BoseB6.bogZeroPoint, Work.BoseB6Est.gFun]
  -- the `β`-oscillation hypothesis, oriented as `β_n - β_x`
  have hbosc : |Work.BoseBogFS.betaSc v h ρ μ (Work.BoseBogFS.tSca v ρ μ n)
      - Work.BoseBogFS.betaSc v h ρ μ x| ≤ o := by
    rw [abs_sub_comm]
    exact hosc x hx
  -- `|β| ≤ V` at both points
  have hbtV : |Work.BoseBogFS.betaSc v h ρ μ (Work.BoseBogFS.tSca v ρ μ n)| ≤ V := by
    rw [abs_le]
    constructor
    · exact le_trans (neg_le_neg (le_max_left |v_lo| |v_hi|))
        (le_trans (neg_abs_le v_lo) hv_lo')
    · exact le_trans hv_hi'
        (le_trans (le_abs_self v_hi) (le_max_right |v_lo| |v_hi|))
  have hbxV : |Work.BoseBogFS.betaSc v h ρ μ x| ≤ V := by
    rw [abs_le]
    constructor
    · exact le_trans (neg_le_neg (le_max_left |v_lo| |v_hi|))
        (le_trans (neg_abs_le v_lo) hv_lo)
    · exact le_trans hv_hi
        (le_trans (le_abs_self v_hi) (le_max_right |v_lo| |v_hi|))
  have hτx0 : 0 ≤ Work.BoseBogFS.tauSc v ρ μ x := le_trans hu0 hu_lo
  -- the three independent pieces
  have h1 := cellPhi_tau_le (τ := Work.BoseBogFS.tauSc v ρ μ (Work.BoseBogFS.tSca v ρ μ n))
    (τ' := Work.BoseBogFS.tauSc v ρ μ x)
    (b := Work.BoseBogFS.betaSc v h ρ μ (Work.BoseBogFS.tSca v ρ μ n))
    (u_lo := u_lo) (u_hi := u_hi) (V := V) hu0 hu_lo' hu_hi' hu_lo hu_hi hbtV
  have h2 := cellPhi_beta_le (τ := Work.BoseBogFS.tauSc v ρ μ x)
    (b := Work.BoseBogFS.betaSc v h ρ μ (Work.BoseBogFS.tSca v ρ μ n))
    (b' := Work.BoseBogFS.betaSc v h ρ μ x) (o := o) (u_hi := u_hi) (V := V)
    hτx0 hu_hi hbtV hbxV hbosc
  have h3 := radialPair_le (b := Work.BoseBogFS.betaSc v h ρ μ (Work.BoseBogFS.tSca v ρ μ n))
    (b' := Work.BoseBogFS.betaSc v h ρ μ x) (o := o) (V := V) (r_lo := r_lo) (r_hi := r_hi)
    (r := ‖Work.BoseBogFS.tSca v ρ μ n‖) (r' := ‖x‖) hr0 hr_lo' hr_hi' hr_lo hr_hi hbtV hbxV hbosc
  -- the exact decomposition of the two-point oscillation
  have hdec : Work.BoseBogFS.psiSc v h ρ μ (Work.BoseBogFS.tSca v ρ μ n)
        - Work.BoseBogFS.psiSc v h ρ μ x
      = (cellPhi (Work.BoseBogFS.tauSc v ρ μ (Work.BoseBogFS.tSca v ρ μ n))
            (Work.BoseBogFS.betaSc v h ρ μ (Work.BoseBogFS.tSca v ρ μ n))
          - cellPhi (Work.BoseBogFS.tauSc v ρ μ x)
            (Work.BoseBogFS.betaSc v h ρ μ (Work.BoseBogFS.tSca v ρ μ n)))
        + (cellPhi (Work.BoseBogFS.tauSc v ρ μ x)
            (Work.BoseBogFS.betaSc v h ρ μ (Work.BoseBogFS.tSca v ρ μ n))
          - cellPhi (Work.BoseBogFS.tauSc v ρ μ x)
            (Work.BoseBogFS.betaSc v h ρ μ x))
        + (-((Work.BoseBogFS.betaSc v h ρ μ (Work.BoseBogFS.tSca v ρ μ n)) ^ 2
              / (2 * ‖Work.BoseBogFS.tSca v ρ μ n‖ ^ 2))
            + (Work.BoseBogFS.betaSc v h ρ μ x) ^ 2 / (2 * ‖x‖ ^ 2)) := by
    rw [hpsi (Work.BoseBogFS.tSca v ρ μ n), hpsi x, gFun_eq_cellPhi, gFun_eq_cellPhi]
    ring
  linarith [hdec, h1, h2, h3]

end Work.BoseBogFS
