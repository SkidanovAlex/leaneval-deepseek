/-
# `Work.GATE2.Escape.escape_of_robust` — the robustness of the shifted leak

Area **GATE2**, residual 3 (SHIFTED ESCAPE).  Given

* a *robustness* datum `hrob`: near `c₀` the repelling coordinate `Ψ` of the flower maps the
  closed disc `closedBall x r` a positive distance away from the filled Julia sets `K c`;
* the *tracked exit* `hExit` of PARIMPL's transit data, refined in the integer: for every
  parameter `c` in the implosion side `Nm` near `c₀` and every integer `k` with
  `Re (trans c) + k < -1`, some point of the orbit of the critical value has repelling
  coordinate `trans c + k` up to any prescribed `η`;

and given that the second return map `Ft c` is the tenth iterate `F c = (T_c)^{10}` of the
antiholomorphic quadratic, the leak disc of level `x` is *escapable*: a parameter `c` is outside
the mandelbar as soon as the integer `k` puts `trans c + k` within `r / 2` of `x`.

The exit used is `Work.GATE2.ExitTrackedLoc` (the *bounded-window* exit), not the refutable
`Work.GATE2.ExitTracked`; the window bound is *automatic* here: `Re (trans c + k) ≥ x.re − r/2`,
and the exit is taken at the (existentially chosen by the caller) level `X := −(x.re − r/2) + 1`.

The proof is the design's one-liner: such a `k` has `Re (trans c + k) < x.re + r/2 < -1`, so the
tracked exit produces an orbit point `Ψ u` with `u ∈ closedBall x r`; robustness then puts `Ψ u`
*outside* the filled Julia set; but `Ψ u` is a point of the critical orbit
(`(F c)^[n] c = T_c^[10n + 1] 0`), and an unbounded point of a bounded orbit forces the whole
orbit to be unbounded — i.e. `c ∉ Mandelbar`.
-/
import Mathlib
import Submission.Work.GATE2.Defs
import Submission.Work.ParamRays.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.GATE2.Escape

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)
open Work.ParamRays

/-- `Ψ u = (Ft c)^[n] c` is a point of the critical orbit of `T_c`, tracked in the integer.

Precisely: if `Ft c = F c = (T_c)^{10}`, then `(Ft c)^[n] c = orbit c 0 (10 * n + 1)`. -/
theorem orbit_of_F_iterate {c : ℂ} {Ft : ℂ → ℂ → ℂ} (hFt : Ft c = Work.EL.F c) (n : ℕ) :
    (Ft c)^[n] c = orbit c 0 (10 * n + 1) := by
  have h01 : orbit c 0 1 = c := by simp [orbit, Tantibar]
  rw [hFt, Work.EL.F_eq_tantibar, (Function.iterate_mul (Tantibar c) 10 n).symm]
  have h1 : orbit c 0 (10 * n + 1) = orbit c (orbit c 0 1) (10 * n) := by
    rw [show 10 * n + 1 = 1 + 10 * n by ring, orbit_add]
  rw [h1, h01]
  rfl

/-- A point of the critical orbit lying outside the filled Julia set forces the parameter out of
the mandelbar. -/
theorem notMem_mandelbar_of_orbit_notMem_K {c : ℂ} {j : ℕ}
    (h : orbit c 0 j ∉ Work.EL.K c) : c ∉ Mandelbar := by
  intro hc
  have hb : BoundedOrbit c 0 := (mem_mandelbar_iff_bounded c).mp hc
  exact h (hb.shift j)

theorem escape_of_robust {c₀ : ℂ} {Nm : Set ℂ} {trans : ℂ → ℂ} {Ft : ℂ → ℂ → ℂ} {Ψ : ℂ → ℂ}
    {x : ℂ} {r : ℝ} (hr : 0 < r) (hcont : Continuous Ψ) (hFt : ∀ c, Ft c = Work.EL.F c)
    (hx : x.re + r / 2 < -1)
    (hrob : ∃ ρ : ℝ, 0 < ρ ∧ ∀ c ∈ Metric.ball c₀ ρ, ∀ y : ℂ,
      (∃ z ∈ Metric.closedBall x r, dist y (Ψ z) ≤ ρ) → y ∉ Work.EL.K c)
    (hExit : Work.GATE2.ExitTrackedLoc c₀ Nm trans Ft Ψ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ c ∈ Nm ∩ Metric.ball c₀ ρ, ∀ k : ℤ,
      dist (trans c + (k : ℂ)) x < r / 2 → c ∉ LeanEval.ComplexAnalysis.Mandelbar := by
  obtain ⟨ρr, hρr, hrob'⟩ := hrob
  -- the exit level of the bounded window: from `dist (trans c + k) x < r/2` the real part of the
  -- lattice point is `≥ x.re − r/2 = −X`, i.e. inside the window
  -- `−X ≤ Re (trans c + k) < −1` with `X := −(x.re − r/2) + 1`.
  have hX : 1 < -(x.re - r / 2) + 1 := by
    have : 0 < r / 2 := by linarith
    linarith
  obtain ⟨ρe, hρe, hexit⟩ :=
    hExit (-(x.re - r / 2) + 1) (min (r / 2) ρr) hX (lt_min (by linarith) hρr)
  refine ⟨min ρr ρe, lt_min hρr hρe, ?_⟩
  intro c hc k hk
  rw [Set.mem_inter_iff, Metric.mem_ball] at hc
  obtain ⟨hcNm, hcball⟩ := hc
  have hcr : dist c c₀ < ρr := lt_of_lt_of_le hcball (min_le_left _ _)
  have hce : dist c c₀ < ρe := lt_of_lt_of_le hcball (min_le_right _ _)
  -- the lattice point lies in the leak disc
  have hmem : trans c + (k : ℂ) ∈ Metric.closedBall x r := by
    rw [Metric.mem_closedBall]; linarith [hk]
  -- and in the exit window
  have hwin : -(-(x.re - r / 2) + 1) ≤ (trans c + (k : ℂ)).re := by
    have h1 : x.re - (trans c + (k : ℂ)).re ≤ dist x (trans c + (k : ℂ)) := by
      rw [Complex.dist_eq]
      simpa [Complex.sub_re] using Complex.re_le_norm (x - (trans c + (k : ℂ)))
    have h2 : dist x (trans c + (k : ℂ)) < r / 2 := by rwa [dist_comm]
    linarith
  have hkre : (trans c + (k : ℂ)).re < -1 := by
    have h1 : (trans c + (k : ℂ)).re - x.re ≤ dist (trans c + (k : ℂ)) x := by
      rw [Complex.dist_eq]
      simpa [Complex.sub_re] using Complex.re_le_norm ((trans c + (k : ℂ)) - x)
    linarith
  obtain ⟨n, hn⟩ := hexit c ⟨hcNm, hce⟩ k hwin hkre
  -- the orbit point is within `ρr` of `Ψ` of a point of the leak disc: robustness applies.
  have hK : (Ft c)^[n] c ∉ Work.EL.K c :=
    hrob' c hcr ((Ft c)^[n] c) ⟨trans c + (k : ℂ), hmem,
      le_trans (by simpa [dist_eq_norm] using hn) (min_le_right _ _)⟩
  rw [orbit_of_F_iterate (hFt c) n] at hK
  exact notMem_mandelbar_of_orbit_notMem_K hK

end Work.GATE2.Escape
