import Mathlib
import Submission.Work.RPB.B5.LagData
import Submission.Work.RPV.Defs
import Submission.Work.RPB.Defs
import Submission.Work.RPV.VBasic
import Submission.Work.RPB.B2.chordSurf_period_swap
import Submission.Work.RPB.B5.chartChain
import Submission.Work.RPB.B5.iteratedDeriv_eq_of_eqOn_Ioo_left
import Submission.Work.RPB.B5.iteratedDeriv_eq_of_eqOn_Ioo_right

/-!
# B5: the junction `x = 0` of the assembled family

The assembled family `ℓ τ (x,t) = lagPt W Γc Ac rho τ x t` is the "base" half
`x ↦ W τ t (rho τ x t)` for `x ≤ 0` and its `τ_π`-image
`x ↦ tau π (W τ (t-π) (rho τ (-x) (t-π)))` for `x ≥ 0`.  At the middle chord `x = 0` the two
branches have to meet to first order; this file proves exactly that:

`iteratedDeriv k (x ↦ W τ t (rho τ x t)) 0
   = iteratedDeriv k (x ↦ tau π (W τ (t-π) (rho τ (-x) (t-π)))) 0`  for `k = 0, 1`.

The proof is the one sketched in `Submission/Work/RPB/B5/B5_PLAN.lean`:

* on the *left* of `0` (`x ∈ (-δ, 0)`, with `δ` from the hypothesis `hrhonearδ`) the
  reparametrisation is the explicit quadratic `rho τ x t = (π/2 (1 + x/√2))²`, so the base branch
  agrees there with the single smooth expression
  `x ↦ chordSurf CI.c a τ t (π/2 (1 + x/√2))` (`hWchord`, valid because `0 < π/2 (1+x/√2) ≤ π/2`);
* on the *right* of `0` (`x ∈ (0, δ)`) the reflected branch agrees with the *same* expression: the
  inner radius is `π/2 (1 - x/√2) = π - π/2 (1 + x/√2)` and `chordSurf_period_swap` turns
  `tau π (chordSurf τ (t-π) (π - r))` into `chordSurf τ t r`;
* all three functions are `C⁸` at `0` (the chart `W` is `C⁸` in `ρ` on the box — here at the
  interior level `ρ = π²/4 < ρ₀` — and `x ↦ rho τ x t` is `C⁸` too), so the one-sided agreement
  upgrades to equality of the `k`-jets at `0` by
  `iteratedDeriv_eq_of_eqOn_Ioo_left` / `iteratedDeriv_eq_of_eqOn_Ioo_right`.

## Layout

* `contDiffAt_chartSlice_zero`: `x ↦ W τ t (rho τ x t)` is `C⁸` at `0` (for `τ ∈ [0,1]`).
* `contDiff_tau_phase`: `tau θ` is `C⁸` (for fixed `θ`).
* `lagData_junction_zero`: the junction statement.
-/

open RectangularPegProblem
open Manifold Complex Real
open scoped Topology ContDiff

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

/-- **Smoothness of the chart slice at `x = 0`.**  For `τ ∈ [0,1]` and any `t`, the map
`x ↦ W τ t (rho τ x t)` is `C⁸` at `x = 0`.

`W` is only known to be `C⁸` on the box `Icc 0 1 × univ × Ioo (-ρ₀) ρ₀` (the `τ`-direction is only
one-sided there), but the curve `x ↦ (τ, (t, rho τ x t))` moves in the `ρ`-direction only, which is
interior to the box at the value `rho τ 0 t = π²/4 < ρ₀`; the within-set chain rule therefore
applies.  The two-sided neighbourhood of `0` on which `rho` stays in the box is obtained from
continuity of `rho` at `0`. -/
theorem contDiffAt_chartSlice_zero (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (D : Work.RPB.B5.LagData CI a) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (t : ℝ) :
    ContDiffAt ℝ 8 (fun x : ℝ => D.W τ t (D.rho τ x t)) 0 := by
  have hpi : (0 : ℝ) < Real.pi ^ 2 / 4 := by positivity
  have hρ : ContDiff ℝ 8 (fun x : ℝ => D.rho τ x t) :=
    D.hrhosm.comp (contDiff_const.prodMk (contDiff_id.prodMk contDiff_const))
  have hΦ : ContDiffAt ℝ 8 (fun x : ℝ => ((τ, (t, D.rho τ x t)) : ℝ × (ℝ × ℝ))) 0 :=
    (contDiffAt_const.prodMk (contDiffAt_const.prodMk hρ.contDiffAt))
  have hs : (fun x : ℝ => D.rho τ x t) ⁻¹' Set.Ioo (-D.ρ₀) D.ρ₀ ∈ 𝓝 (0 : ℝ) := by
    refine hρ.continuous.continuousAt.preimage_mem_nhds ?_
    rw [D.hrho0 τ hτ t]
    exact isOpen_Ioo.mem_nhds ⟨by linarith [D.hρ₀, hpi], by linarith [D.hπρ₀]⟩
  have hmem : ((τ, (t, D.rho τ 0 t)) : ℝ × (ℝ × ℝ)) ∈
      Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-D.ρ₀) D.ρ₀ := by
    rw [D.hrho0 τ hτ t]
    exact ⟨hτ, trivial, by linarith [D.hρ₀, hpi], D.hπρ₀⟩
  have hmap : Set.MapsTo (fun x : ℝ => ((τ, (t, D.rho τ x t)) : ℝ × (ℝ × ℝ)))
      ((fun x : ℝ => D.rho τ x t) ⁻¹' Set.Ioo (-D.ρ₀) D.ρ₀)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-D.ρ₀) D.ρ₀) := by
    intro x hx
    exact ⟨hτ, trivial, hx⟩
  exact (ContDiffWithinAt.comp 0 (D.hWsm.contDiffWithinAt hmem) hΦ.contDiffWithinAt
    hmap).contDiffAt hs

/-- `tau θ` is smooth (for fixed `θ`). -/
theorem contDiff_tau_phase (θ : ℝ) : ContDiff ℝ 8 (Work.RPV.tau θ) := by
  unfold Work.RPV.tau
  fun_prop

theorem lagData_junction_zero (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a) (D : Work.RPB.B5.LagData CI a) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
      (iteratedDeriv 0 (fun x : ℝ => D.W τ t (D.rho τ x t)) 0
        = iteratedDeriv 0 (fun x : ℝ =>
            Work.RPV.tau Real.pi (D.W τ (t - Real.pi) (D.rho τ (-x) (t - Real.pi)))) 0) ∧
      (iteratedDeriv 1 (fun x : ℝ => D.W τ t (D.rho τ x t)) 0
        = iteratedDeriv 1 (fun x : ℝ =>
            Work.RPV.tau Real.pi (D.W τ (t - Real.pi) (D.rho τ (-x) (t - Real.pi)))) 0) := by
  intro τ hτ t
  obtain ⟨δ, hδpos, hδ14, _hδκ, _hnear_sqrt2, hnear0⟩ := D.hrhonearδ
  -- the two-sided smoothness of the three functions at `0`
  have hF8 : ContDiffAt ℝ 8 (fun x : ℝ => D.W τ t (D.rho τ x t)) 0 :=
    contDiffAt_chartSlice_zero CI a D hτ t
  have hG8 : ContDiffAt ℝ 8 (fun x : ℝ =>
      Work.RPV.tau Real.pi (D.W τ (t - Real.pi) (D.rho τ (-x) (t - Real.pi)))) 0 := by
    have h1 : ContDiffAt ℝ 8 (fun y : ℝ => D.W τ (t - Real.pi) (D.rho τ y (t - Real.pi))) 0 :=
      contDiffAt_chartSlice_zero CI a D hτ (t - Real.pi)
    have h2 : ContDiffAt ℝ 8 (fun x : ℝ => -x) 0 := by fun_prop
    have h3 : ContDiffAt ℝ 8
        (fun x : ℝ => D.W τ (t - Real.pi) (D.rho τ (-x) (t - Real.pi))) 0 :=
      ContDiffAt.comp (f := fun x : ℝ => -x)
        (g := fun y : ℝ => D.W τ (t - Real.pi) (D.rho τ y (t - Real.pi))) 0
        (by simpa using h1) h2
    exact (contDiff_tau_phase Real.pi).contDiffAt.comp 0 h3
  have hA8 : ContDiffAt ℝ 8 (fun x : ℝ =>
      Work.RPB.chordSurf CI.c a τ t (Real.pi / 2 * (1 + x / Real.sqrt 2))) 0 := by
    have hr : (Real.pi / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) Real.pi :=
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    have hcs := Work.RPB.B5.chordSurf_pair_contDiffAt CI a ha (t := t) hτ hr
    have hcs' : ContDiffAt ℝ 8 (fun z : ℝ × ℝ => Work.RPB.chordSurf CI.c a τ z.1 z.2)
        (t, Real.pi / 2 * (1 + 0 / Real.sqrt 2)) := by simpa using hcs
    have hrf : ContDiffAt ℝ 8 (fun x : ℝ => (t, Real.pi / 2 * (1 + x / Real.sqrt 2))) 0 := by
      fun_prop
    exact hcs'.comp 0 hrf
  -- the one-sided agreement with the single chord expression
  have hFagree : ∀ x ∈ Set.Ioo (0 - δ) 0, D.W τ t (D.rho τ x t)
      = Work.RPB.chordSurf CI.c a τ t (Real.pi / 2 * (1 + x / Real.sqrt 2)) := by
    intro x hx
    have hxδ : -δ < x := by linarith [hx.1]
    have hx4 : -(1 : ℝ) / 4 < x := by linarith [hx.1, hδ14]
    rw [hnear0 τ hτ x ⟨le_of_lt hxδ, hx.2.le⟩ t]
    have hsq : Real.pi ^ 2 / 4 * (1 + x / Real.sqrt 2) ^ 2
        = (Real.pi / 2 * (1 + x / Real.sqrt 2)) ^ 2 := by ring
    rw [hsq]
    have hpos : 0 < Real.pi / 2 * (1 + x / Real.sqrt 2) := by
      have h2 : (1 : ℝ) / 4 < Real.sqrt 2 := by
        have h := Real.one_lt_sqrt_two; linarith
      have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos_of_pos (by norm_num)
      have hrw : 1 + x / Real.sqrt 2 = (Real.sqrt 2 + x) / Real.sqrt 2 := by field_simp
      have h3 : 0 < 1 + x / Real.sqrt 2 := by rw [hrw]; exact div_pos (by linarith) hs2
      positivity
    have hle : Real.pi / 2 * (1 + x / Real.sqrt 2) ≤ Real.pi / 2 := by
      have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos_of_pos (by norm_num)
      have h1 : x / Real.sqrt 2 ≤ 0 := div_nonpos_of_nonpos_of_nonneg hx.2.le hs2.le
      have := Real.pi_pos
      nlinarith [h1]
    exact D.hWchord τ hτ t _ ⟨hpos, hle⟩
  have hGagree : ∀ x ∈ Set.Ioo (0 : ℝ) (0 + δ),
      Work.RPV.tau Real.pi (D.W τ (t - Real.pi) (D.rho τ (-x) (t - Real.pi)))
        = Work.RPB.chordSurf CI.c a τ t (Real.pi / 2 * (1 + x / Real.sqrt 2)) := by
    intro x hx
    have hxm : -x ∈ Set.Icc (-δ) 0 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
    rw [hnear0 τ hτ (-x) hxm (t - Real.pi)]
    have hsq : Real.pi ^ 2 / 4 * (1 + (-x) / Real.sqrt 2) ^ 2
        = (Real.pi / 2 * (1 - x / Real.sqrt 2)) ^ 2 := by ring
    rw [hsq]
    have hpos : 0 < Real.pi / 2 * (1 - x / Real.sqrt 2) := by
      have hx4 : x < Real.sqrt 2 := by
        have h := Real.one_lt_sqrt_two; linarith [hx.2, hδ14]
      have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos_of_pos (by norm_num)
      have hrw : 1 - x / Real.sqrt 2 = (Real.sqrt 2 - x) / Real.sqrt 2 := by field_simp
      have h3 : 0 < 1 - x / Real.sqrt 2 := by rw [hrw]; exact div_pos (by linarith) hs2
      positivity
    have hle : Real.pi / 2 * (1 - x / Real.sqrt 2) ≤ Real.pi / 2 := by
      have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos_of_pos (by norm_num)
      have h1 : 0 ≤ x / Real.sqrt 2 := div_nonneg hx.1.le hs2.le
      have := Real.pi_pos
      nlinarith [h1]
    rw [D.hWchord τ hτ (t - Real.pi) _ ⟨hpos, hle⟩]
    have hswap := (Work.RPB.B2.chordSurf_period_swap CI a ha).2 τ hτ (t - Real.pi) _
        ⟨hpos, by linarith [Real.pi_pos]⟩
    rw [show t - Real.pi + Real.pi = t by ring] at hswap
    have hpi : Real.pi - Real.pi / 2 * (1 - x / Real.sqrt 2)
        = Real.pi / 2 * (1 + x / Real.sqrt 2) := by ring
    rw [hpi] at hswap
    exact hswap.symm
  -- both sides have the same `k`-jets as the single chord expression
  have key : ∀ k : ℕ, k ≤ 8 →
      iteratedDeriv k (fun x : ℝ => D.W τ t (D.rho τ x t)) 0
        = iteratedDeriv k (fun x : ℝ =>
            Work.RPV.tau Real.pi (D.W τ (t - Real.pi) (D.rho τ (-x) (t - Real.pi)))) 0 := by
    intro k hk
    rw [iteratedDeriv_eq_of_eqOn_Ioo_left hδpos (n := 8) hF8 hA8 hFagree hk,
      iteratedDeriv_eq_of_eqOn_Ioo_right hδpos (n := 8) hG8 hA8 hGagree hk]
  exact ⟨key 0 (by norm_num), key 1 (by norm_num)⟩

end Work.RPB.B5
