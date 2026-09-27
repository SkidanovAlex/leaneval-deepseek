import Mathlib
import Submission.Work.EQ.CycleDefs
import Submission.Work.EQ.fan_estimates
import Submission.Work.EQ.germC_facts

namespace Work.EQ

/-- The fan recursion in the form needed here: for `i < ε.length`, the fan of `ε.drop i` is the
backward branch `invBranch a ε[i]` applied to the fan of `ε.drop (i+1)` at the scaled argument.
Immediate from `List.drop_eq_getElem_cons` and the defining equation of `fan`. -/
private theorem fan_drop_getElem_cons {a : ℝ} {h : ℂ → ℂ} {ε : List Bool} {i : ℕ}
    (hi : i < ε.length) (u : ℂ) :
    fan a h (ε.drop i) u =
      invBranch a ε[i] (fan a h (ε.drop (i + 1)) (((eqLam a : ℝ) : ℂ) * u)) := by
  rw [List.drop_eq_getElem_cons hi]
  rfl

/-- If `‖z‖ < min δf ρ * λ^N` with `λ = eqLam a ∈ (0,1)`, then for every `j ≥ 0` the argument
`Λ^j z` still lies in the disc of radius `δf` (`Λ = ((eqLam a : ℝ) : ℂ)`). -/
private theorem norm_zpow_mul_lt_of_lt_min_mul_pow {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    {δf ρ : ℝ} (hδf : 0 < δf) {N : ℕ} {z : ℂ}
    (hz : ‖z‖ < min δf ρ * (eqLam a) ^ N) {j : ℤ} (hj : 0 ≤ j) :
    ‖(((eqLam a : ℝ) : ℂ) ^ j * z)‖ < δf := by
  have hlam0 : 0 < eqLam a := eqLam_pos' ha0 ha1
  have hlam1 : eqLam a < 1 := eqLam_lt_one' ha0 ha1
  have hzδ : ‖z‖ < δf := by
    have h2 : (eqLam a) ^ N ≤ 1 := pow_le_one₀ hlam0.le hlam1.le
    have h3 : (0 : ℝ) ≤ (eqLam a) ^ N := pow_nonneg hlam0.le N
    have h4 : min δf ρ * (eqLam a) ^ N ≤ δf := by
      calc min δf ρ * (eqLam a) ^ N ≤ δf * (eqLam a) ^ N :=
            mul_le_mul_of_nonneg_right (min_le_left _ _) h3
        _ ≤ δf * 1 := mul_le_mul_of_nonneg_left h2 hδf.le
        _ = δf := mul_one _
    linarith
  have hnorm : ‖(((eqLam a : ℝ) : ℂ) ^ j)‖ ≤ 1 := by
    rw [norm_zpow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam0,
      ← Int.toNat_of_nonneg hj, zpow_natCast]
    exact pow_le_one₀ hlam0.le hlam1.le
  calc ‖(((eqLam a : ℝ) : ℂ) ^ j * z)‖ ≤ ‖(((eqLam a : ℝ) : ℂ) ^ j)‖ * ‖z‖ :=
        norm_mul_le _ _
    _ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg z)
    _ = ‖z‖ := one_mul _
    _ < δf := hzδ

/-- **The candidate chain satisfies the equichordal relation across the window `0 ≤ n < N`**
(the stable-fan recursion of the word `ε`).

`Work.EQ.candChain` (Submission/Work/EQ/CycleDefs.lean) has
`P n = fan a h (ε.drop n.toNat) (Λ^n z)` for `0 ≤ n` (where `Λ = ((eqLam a : ℝ) : ℂ)`; for
`n.toNat > N` the drop is `[]` and `fan [] = germC`, so the formula still holds), and
`P (n+1)` is the same formula at `n+1`.  Since `n.toNat < N = ε.length`,
`ε.drop n.toNat = ε[n.toNat] :: ε.drop (n.toNat+1)`, so the defining recursion of `fan`
(`fan_cons`) gives `P n = invBranch a ε[n.toNat] (P (n+1))`, and `eqRelC_invBranch`
(`bsq (subO1 a (P (n+1))) ≠ 0`) gives `EqRelC a (P n) (P (n+1))`.  The radicand is nonzero because
`FanGood` (`Work.EQ.fan_induction`, fan_estimates.lean) gives it positive real part at the point
`P (n+1) = fan a h (ε.drop (n+1).toNat) (Λ^{(n+1).toNat} z)`, whose argument satisfies
`‖Λ^{(n+1).toNat} z‖ < δf` (from `hz`, since `λ = eqLam a ∈ (0,1)`; note the estimate
`‖Λ^k z‖ < min δf ρ` holds for *every* `k : ℕ`).  Only `ha0`, `ha1`, `hε`, `hδf`, `hFG`, `hz`,
`hn0`, `hnN` are needed; `hδf` follows from `hz` (`min δf ρ * λ^N > 0`). -/
theorem eqRelC_candChain_fanRegion {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ}
    {N : ℕ} {ε η s : List Bool} (hε : ε.length = N) {C : ℂ} {Ke Lam Q δf ρ : ℝ}
    (hδf : 0 < δf)
    (hFG : ∀ (ε' : List Bool) (v : ℂ), ‖v‖ < δf → FanGood a h Ke Lam Q ε' v)
    {z : ℂ} (hz : ‖z‖ < min δf ρ * (eqLam a) ^ N)
    {n : ℤ} (hn0 : 0 ≤ n) (hnN : n < (N : ℤ)) :
    EqRelC a ((candChain a h ε η s N C z).1 n)
      ((candChain a h ε η s N C z).1 (n + 1)) := by
  have hlam0 : 0 < eqLam a := eqLam_pos' ha0 ha1
  -- the value of the chain on the fan window
  have hval : ∀ j : ℤ, 0 ≤ j → j.toNat ≤ N →
      (candChain a h ε η s N C z).1 j =
        fan a h (ε.drop j.toNat) (((eqLam a : ℝ) : ℂ) ^ j * z) := by
    intro j hj0 hjN
    simp only [candChain]
    rw [ite_eq_left hj0, ite_eq_left hjN]
  -- index arithmetic
  have hk1N : n.toNat ≤ N := by
    have h1 : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn0
    omega
  have hk2N : (n + 1).toNat ≤ N := by omega
  have hk2 : (n + 1).toNat = n.toNat + 1 := by omega
  have hk1lt : n.toNat < ε.length := by
    have h1 : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn0
    omega
  -- the two endpoints
  have hPn : (candChain a h ε η s N C z).1 n =
      fan a h (ε.drop n.toNat) (((eqLam a : ℝ) : ℂ) ^ n * z) := hval n hn0 hk1N
  have hPn1 : (candChain a h ε η s N C z).1 (n + 1) =
      fan a h (ε.drop (n.toNat + 1)) (((eqLam a : ℝ) : ℂ) ^ (n + 1) * z) := by
    rw [hval (n + 1) (by omega) hk2N, hk2]
  -- the radicand at the point `n+1` is nonzero: `FanGood` puts it in the right half plane
  have hbsq : bsq (subO1 a (fan a h (ε.drop (n.toNat + 1))
      (((eqLam a : ℝ) : ℂ) ^ (n + 1) * z))) ≠ 0 := by
    have hmem : ‖(((eqLam a : ℝ) : ℂ) ^ (n + 1) * z)‖ < δf :=
      norm_zpow_mul_lt_of_lt_min_mul_pow ha0 ha1 hδf hz (by omega)
    have hpos := (hFG (ε.drop (n.toNat + 1)) (((eqLam a : ℝ) : ℂ) ^ (n + 1) * z)
      hmem).2.2.2.2
    have heq : bsq (subO1 a (fan a h (ε.drop (n.toNat + 1))
        (((eqLam a : ℝ) : ℂ) ^ (n + 1) * z))) =
        ((fan a h (ε.drop (n.toNat + 1))
            (((eqLam a : ℝ) : ℂ) ^ (n + 1) * z)).1 + (a / 2 : ℂ)) ^ 2
          + (fan a h (ε.drop (n.toNat + 1))
            (((eqLam a : ℝ) : ℂ) ^ (n + 1) * z)).2 ^ 2 := by
      simp only [bsq, subO1]
      push_cast
      ring
    intro h0
    rw [heq] at h0
    rw [h0] at hpos
    simp at hpos
  -- the fan recursion
  rw [hPn, hPn1, fan_drop_getElem_cons hk1lt (((eqLam a : ℝ) : ℂ) ^ n * z)]
  have hLne : (((eqLam a : ℝ) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hlam0)
  have harg : (((eqLam a : ℝ) : ℂ) * ((((eqLam a : ℝ) : ℂ)) ^ n * z))
      = (((eqLam a : ℝ) : ℂ)) ^ (n + 1) * z := by
    rw [zpow_add₀ hLne n 1, zpow_one]
    ring
  rw [harg]
  exact eqRelC_invBranch ε[n.toNat] hbsq

end Work.EQ
