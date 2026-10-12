import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseK15.Derive
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseK15.A_ge_and_AB_of_taurad` — `𝒜 ≥ |k|²/2` and `|ℬ| ≤ 𝒜/2` on `P_H^q`

`Work.BoseB7A.Defs.A_ge` and the `P_H^q` half of FS `eq:BoverA` are the two
plane-wave positivity rows of the `Q3Kernel` interface.  Both are consequences
of a single *lower bound on the kinetic symbol*,

    `‖k‖²/2 + 3ρ_zK₀a ≤ τ(k)`   for `‖k‖ ≥ (4K_Ha)⁻¹`,

which is FS's `arith_tau_ge` (delegated, `Submission/Work/BoseK15/arith_tau_ge.lean`,
the content of FS `def:tau` plus `eq:Close` and `eq:DefLille`).  The lemma here
takes that lower bound as the **hypothesis** `htaurad` (so that it is usable
before `arith_tau_ge`'s parameter thresholds are invoked) and derives:

* `𝒜(k) = τ(k) + ρ_zŴ₁(k) ≥ ‖k‖²/2 + 2ρ_zK₀a ≥ ‖k‖²/2`, using the potential
  bound `|Ŵ₁| ≤ K₀a` (`K15Input.W1_le`) — the `3ρ_zK₀a` of the hypothesis
  absorbs the worst case `ρ_zŴ₁ ≥ -ρ_zK₀a` and still leaves the slack `2ρ_zK₀a`;
* `2|ℬ(k)| = 2ρ_z|Ŵ₁(k)| ≤ 2ρ_zK₀a ≤ 𝒜(k)`, the same margin.

Both rows are read off the single estimate `K15Input.A_lower_of_taurad`, which
records exactly the slack `2ρ_zK₀a`.

The only side condition used is `ρ_z ≥ 0` (a hypothesis here — FS's `eq:Close`
supplies it for the honest instance).  Note that `K₀ ≥ 1 > 0` and `a = aScat ≥ 0`
are *consequences* of `K15Input` (`K₀_one`, and `W1_le` at the origin:
`0 ≤ |Ŵ₁(0)| ≤ K₀a`); `K15Input.aScat_nonneg` isolates the second of these.

## Note on imports

This module deliberately imports only `Submission.Work.BoseK15.Defs` (plus
Mathlib): everything it uses about FS's data is a *field* of `K15Input`, and in
particular the pointwise `Ŵ₁`-bound is re-derived here (`W1_le_mode`) rather than
taken from the structural module `Derive`, so that the two positivity rows do not
depend on the `χ̂`/label-arithmetic bookkeeping.
-/

noncomputable section

open scoped BigOperators Pointwise
open MeasureTheory Classical

namespace Work.BoseK15

open Work.BoseB7 Work.BoseB7A

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
variable {F : Work.BoseB7.FockData Mode} {T : Work.BoseB7A.TildeData F}
variable {E : Work.BoseB7.Q3Env Mode} {K₀ : ℝ}

/-- FS `eq:W1-g` at the modes: `|Ŵ₁(k)| ≤ K₀a`. -/
theorem K15Input.W1_le_mode (h : K15Input K₀ F T E) (k : Mode) :
    |E.W1 k| ≤ K₀ * E.aScat := h.W1_le_holds k

/-- **The scattering length is nonnegative**, from `K15Input.W1_le` at the
origin: `0 ≤ |Ŵ₁(0)| ≤ K₀a`, and `K₀ ≥ 1 > 0` (`K15Input.K₀_one`). -/
lemma K15Input.aScat_nonneg (h : K15Input K₀ F T E) : 0 ≤ E.aScat :=
  h.aScat_pos.le

/-- **The kinetic lower bound that both rows of the `P_H^q` positivity rest on.**

At a mode `q ∈ P_H^q` the hypothesis `htaurad` gives `τ(q) ≥ ‖k_q‖²/2 + 3ρ_zK₀a`,
and `|Ŵ₁(q)| ≤ K₀a` costs at most `ρ_zK₀a` of that; what survives is

    `𝒜(q) = τ(q) + ρ_zŴ₁(q) ≥ ‖k_q‖²/2 + 2ρ_zK₀a`,

i.e. the plane-wave kinetic energy `‖k_q‖²/2` *plus* a strictly positive slack
`2ρ_zK₀a` (when `ρ_z > 0`). -/
theorem K15Input.A_lower_of_taurad (h : K15Input K₀ F T E) (hrho : 0 ≤ E.rho)
    (htaurad : ∀ r : ℝ, 1 / (4 * E.KH * E.aScat) ≤ r →
      r ^ 2 / 2 + 3 * E.rho * K₀ * E.aScat
        ≤ (1 - E.eT) * max (r - (2 * E.s * E.ell)⁻¹) 0 ^ 2
          + E.eT * max (r - (2 * E.d * E.s * E.ell)⁻¹) 0 ^ 2)
    (q : Mode) (hq : F.PHq E.KH E.aScat q) :
    ‖F.kmom q‖ ^ 2 / 2 + 2 * E.rho * K₀ * E.aScat ≤ E.A q := by
  have hK0 : 0 ≤ K₀ := le_of_lt (lt_of_lt_of_le zero_lt_one h.K₀_one)
  have hprod : 0 ≤ E.rho * (K₀ * E.aScat) :=
    mul_nonneg hrho (mul_nonneg hK0 h.aScat_nonneg)
  -- `htaurad` identifies `E.tau q` with FS's `def:tau` at `‖k_q‖`
  have hr : 1 / (4 * E.KH * E.aScat) ≤ ‖F.kmom q‖ := hq
  have htau : ‖F.kmom q‖ ^ 2 / 2 + 3 * E.rho * K₀ * E.aScat ≤ E.tau q := by
    rw [h.tau_eq q, ← h.kmom_eq q]
    exact htaurad ‖F.kmom q‖ hr
  -- the potential costs at most `ρ_zK₀a`
  have hW1 : -(K₀ * E.aScat) ≤ E.W1 q := (abs_le.mp (h.W1_le_mode q)).1
  have hb : E.rho * (-(K₀ * E.aScat)) ≤ E.rho * E.W1 q :=
    mul_le_mul_of_nonneg_left hW1 hrho
  rw [h.A_eq q]
  nlinarith [htau, hb, hprod]

/-- **FS `eq:BoverA` on `P_H^q` and `A_ge` on `P_H^q`**, from the kinetic lower
bound `htaurad`.

* `‖k_q‖²/2 ≤ 𝒜(q)`: the two-dimensional plane-wave energy is dominated by the
  Bogoliubov diagonal `𝒜` on the region `P_H^q = {|q| ≥ ¼K_H⁻¹a⁻¹}` where the
  kinetic symbol is large (this is the `A_ge` row of `Q3Kernel`).
* `2|ℬ(q)| ≤ 𝒜(q)`: the squeezing parameter `α(q) = h(ℬ/𝒜)` is then well defined
  (this is the `P_H^q` form of FS `eq:BoverA`, read by `alphaCoef_eq_h`). -/
theorem A_ge_and_AB_of_taurad {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {F : Work.BoseB7.FockData Mode} {T : Work.BoseB7A.TildeData F} {E : Work.BoseB7.Q3Env Mode}
    {K₀ : ℝ} (h : Work.BoseK15.K15Input K₀ F T E) (hrho : 0 ≤ E.rho)
    (htaurad : ∀ r : ℝ, 1 / (4 * E.KH * E.aScat) ≤ r →
      r ^ 2 / 2 + 3 * E.rho * K₀ * E.aScat
        ≤ (1 - E.eT) * max (r - (2 * E.s * E.ell)⁻¹) 0 ^ 2
          + E.eT * max (r - (2 * E.d * E.s * E.ell)⁻¹) 0 ^ 2) :
    (∀ q : Mode, F.PHq E.KH E.aScat q → ‖F.kmom q‖ ^ 2 / 2 ≤ E.A q) ∧
    (∀ q : Mode, F.PHq E.KH E.aScat q → 2 * |E.B q| ≤ E.A q) := by
  have hK0 : 0 ≤ K₀ := le_of_lt (lt_of_lt_of_le zero_lt_one h.K₀_one)
  have hprod : 0 ≤ E.rho * (K₀ * E.aScat) :=
    mul_nonneg hrho (mul_nonneg hK0 h.aScat_nonneg)
  have key : ∀ q : Mode, F.PHq E.KH E.aScat q →
      ‖F.kmom q‖ ^ 2 / 2 + 2 * E.rho * K₀ * E.aScat ≤ E.A q :=
    fun q hq => h.A_lower_of_taurad hrho htaurad q hq
  refine ⟨fun q hq => ?_, fun q hq => ?_⟩
  · have hk := key q hq
    nlinarith [hprod]
  · have hk := key q hq
    have hB : E.B q = E.rho * E.W1 q := h.B_eq q
    have hW1abs : |E.W1 q| ≤ K₀ * E.aScat := h.W1_le_mode q
    have h1 : |E.B q| = E.rho * |E.W1 q| := by rw [hB, abs_mul, abs_of_nonneg hrho]
    have h2 : E.rho * |E.W1 q| ≤ E.rho * (K₀ * E.aScat) :=
      mul_le_mul_of_nonneg_left hW1abs hrho
    have h3 : 0 ≤ ‖F.kmom q‖ ^ 2 / 2 := by positivity
    rw [h1]
    nlinarith [hk, h2, h3, hprod]

end Work.BoseK15
