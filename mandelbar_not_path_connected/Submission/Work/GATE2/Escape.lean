/-
# GATE2 — residual 3: the SHIFTED ESCAPE (`trans_escape` for the `ι b`-tongue)

PARIMPL's `Work.PARIMPL.LeakData` carries the equatorial leak of §1.4 of the design:

* `leak : Ψ x* ∉ K c₀` — the leak point of the equator (`Work.EL.equatorLeak`);
* `deep : ∀ y ∈ closedBall (x* - j₀) r₀, 0 < G_{c₀} (Ψ y)` — the leak disc is *deep* in the
  escaping region, and
* `robust` — **(I2)**: for parameters `c` near `c₀` everything close to `Ψ '' closedBall (x*-j₀) r₀`
  is outside `K c`;
* `escape` — **`trans_escape`**: a parameter of `Nm` whose *transit coordinate* lands on the leak
  lattice `x* - j₀ + ℤ` is outside the mandelbar.

The GATE bridge (`Submission/Work/GATE/Bridge/transitData_of_PARIMPL.lean`) needs the same
statement for the **half-integer** translate `x* - j₀ + 1/2` — the `ι b`-tongue, i.e. the leak of
the `ι`-image of the leak point — and takes it as the hypothesis `hescape_iota`.  This module
*proves* it, from PARIMPL's own leak data and the `ι`-symmetry

`Ψ (w̄ + 1/2) = (T_c)^5 (Ψ w)`   (Hubbard–Schleicher Lemma 2.3, `ParabolicFlower.Ψ_anti`),

as the design asks ("derived from PARIMPL's `trans_escape`/`LeakData` via the translation
`x ↦ x + 1/2` symmetry of the antiholomorphic Écalle cylinder").

The two ingredients are

* `deep_half` — the half-shifted leak disc is deep in the escaping region at `c₀`: the `ι`-symmetry
  converts a point of the half-shifted disc into a point of the *unit*-shifted disc, and the filled
  Julia set is completely invariant under `T_c`;
* `robust_of_deep` — its robustness for nearby parameters, from NAKANE's joint continuity of the
  Green function (`Work.PARIMPL.GreenEscapeOpen`, which is `Work.NAKANE.continuous_greenFun`) via
  PARIMPL's `Work.PARIMPL.robust_of_greenOpen`.

Together with the *tracked* transit exit (`ExitTracked`, PARIMPL's `TransitData.exit` refined in
the integer) the escape follows from the elementary
`Work.GATE2.Escape.escape_of_robust`: the orbit point at the tracked exit lies within `r₀/2` of the
leak level, hence inside the leak disc, hence — by the robustness — outside `K_{c}`, and a
parameter whose critical orbit leaves the filled Julia set is outside the mandelbar.

Two consequences are recorded: the `ι b`-case (`escape_iota`, in the exact form the GATE bridge
uses), and — as a check of the same machinery — the original `b`-case `escape_b`, i.e. PARIMPL's own
`LeakData.escape` field, *derived* rather than assumed.

The *only* input beyond the sibling data is the depth condition on the leak level,
`Re (x* - j₀) + r₀/2 < -1`: the design's fallback "choose `j₀` larger" (`the leak set of the
coordinate `Ψ` is invariant under integer shifts, so the level can be taken arbitrarily deep).
-/
import Submission.Work.GATE2.Defs
import Submission.Work.GATE2.Escape.escape_of_robust
import Submission.Work.GATE2.Escape.disc_half_shift
import Submission.Work.PARIMPL.robust_of_greenOpen
import Submission.Work.Final.equatorLeak_shift

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set Metric
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.GATE2.Escape

open LeanEval.ComplexAnalysis (Mandelbar Tantibar)

/-! ## The `ι`-symmetry moves the leak disc by a half -/

/-- **The unit-shifted leak disc is a leak disc.**  `Ψ (y + 1) = F c (Ψ y)` and the filled Julia
set is forward invariant, so a leak disc at level `x` shifts to one at level `x + 1`. -/
theorem leak_shift_one {c : ℂ} {z₁ : ℂ}
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) z₁) {x r : ℝ}
    (h : ∀ y ∈ Metric.closedBall ((x : ℝ) : ℂ) r, fl.Ψ y ∉ Work.EL.K c) :
    ∀ y ∈ Metric.closedBall (((x + 1 : ℝ)) : ℂ) r, fl.Ψ y ∉ Work.EL.K c := by
  intro y hy
  have hy' : y - 1 ∈ Metric.closedBall ((x : ℝ) : ℂ) r := by
    rw [Metric.mem_closedBall, dist_eq_norm] at hy ⊢
    have h1 : y - 1 - ((x : ℝ) : ℂ) = y - (((x + 1 : ℝ)) : ℂ) := by push_cast; ring
    rw [h1]; exact hy
  have h2 : fl.Ψ y = (Tantibar c)^[10] (fl.Ψ (y - 1)) := by
    have h4 := fl.Ψ_shift (y - 1)
    have hy1 : (y - 1) + 1 = y := by ring
    rw [hy1] at h4
    exact h4.trans (congrFun (Work.EL.F_eq_tantibar c) (fl.Ψ (y - 1)))
  rw [h2]
  exact Work.Final.notMem_K_iterate (h _ hy') 10

/-- **The half-shifted leak disc is a leak disc.**  The `ι`-symmetry `Ψ (w̄ + 1/2) = g (Ψ w)`
conjugates the half-shift of the coordinate to the antiholomorphic square root `g = (T_c)^5`; since
the filled Julia set is completely invariant under `g`, `Ψ` of the half-shifted disc avoids `K c`
as soon as the unit-shifted disc does. -/
theorem leak_half {c : ℂ} {z₁ : ℂ}
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) z₁) {x r : ℝ}
    (h : ∀ y ∈ Metric.closedBall (((x + 1 : ℝ)) : ℂ) r, fl.Ψ y ∉ Work.EL.K c) :
    ∀ y ∈ Metric.closedBall (((x + 1 / 2 : ℝ)) : ℂ) r, fl.Ψ y ∉ Work.EL.K c :=
  disc_half_shift fl h

/-- **The half-shifted leak disc is deep in the escaping region at `c₀`.**  From PARIMPL's `deep`
(at the leak level `x* - j₀`) to the Green positivity of the half-integer translate. -/
theorem deep_half {c : ℂ} {z₁ : ℂ}
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) z₁) {x r : ℝ}
    (hdeep : ∀ y ∈ Metric.closedBall ((x : ℝ) : ℂ) r, 0 < Work.Bottcher.green c (fl.Ψ y)) :
    ∀ y ∈ Metric.closedBall (((x + 1 / 2 : ℝ)) : ℂ) r, 0 < Work.Bottcher.green c (fl.Ψ y) := by
  have hK : ∀ y ∈ Metric.closedBall ((x : ℝ) : ℂ) r, fl.Ψ y ∉ Work.EL.K c :=
    fun y hy => Work.PARIMPL.notMem_K_of_green_pos (hdeep y hy)
  refine fun y hy => Work.PARIMPL.green_pos_of_notMem_K ?_
  exact leak_half fl (leak_shift_one fl hK) y hy

/-! ## Robustness of the leak disc for nearby parameters -/

/-- **The robustness (I2) of a leak disc at a prescribed real level**, from NAKANE's joint
continuity of the Green function (PARIMPL's `GreenEscapeOpen`).
This is `Work.PARIMPL.robust_of_greenOpen` at the level `x` (i.e. `xstar = x`, `j₀ = 0`). -/
theorem robust_of_deep {c₀ : ℂ} {Ψ : ℂ → ℂ} (hΨ : Continuous Ψ)
    (hG : Work.PARIMPL.GreenEscapeOpen) {x r : ℝ} (hr : 0 < r)
    (hdeep : ∀ z ∈ Metric.closedBall ((x : ℝ) : ℂ) r, 0 < Work.Bottcher.green c₀ (Ψ z)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ c ∈ Metric.ball c₀ ρ, ∀ y : ℂ,
      (∃ z ∈ Metric.closedBall ((x : ℝ) : ℂ) r, dist y (Ψ z) ≤ ρ) →
        y ∉ Work.EL.K c := by
  obtain ⟨ρ, hρ, hρ'⟩ := Work.PARIMPL.robust_of_greenOpen (xstar := x) (j₀ := 0) hΨ hG hr
    (fun z hz => hdeep z (by simpa using hz))
  exact ⟨ρ, hρ, fun c hc y hy => hρ' c hc y (by
    obtain ⟨z, hz, hzy⟩ := hy
    exact ⟨z, by simpa using hz, hzy⟩)⟩

/-! ## The escape -/

/-- **The escape from the leak disc, in the `distZ` form.**  A parameter of the implosion side
whose transit coordinate lands within `r/2` of the leak level modulo `ℤ` is outside the mandelbar.
This is `Work.GATE2.Escape.escape_of_robust` composed with the extraction of the integer from
`distZ` (`Work.GATE2.exists_dist_lt_of_distZ_lt`). -/
theorem escape_distZ {c₀ : ℂ} {Nm : Set ℂ} {trans : ℂ → ℂ} {Ft : ℂ → ℂ → ℂ} {Ψ : ℂ → ℂ}
    {x : ℂ} {r : ℝ} (hr : 0 < r) (hcont : Continuous Ψ) (hFt : ∀ c, Ft c = Work.EL.F c)
    (hx : x.re + r / 2 < -1)
    (hrob : ∃ ρ : ℝ, 0 < ρ ∧ ∀ c ∈ Metric.ball c₀ ρ, ∀ y : ℂ,
      (∃ z ∈ Metric.closedBall x r, dist y (Ψ z) ≤ ρ) → y ∉ Work.EL.K c)
    (hExit : ExitTrackedLoc c₀ Nm trans Ft Ψ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ c ∈ Nm ∩ Metric.ball c₀ ρ,
      Work.PARIMPL.distZ (trans c) x < r / 2 → c ∉ Mandelbar := by
  obtain ⟨ρ, hρ, hρ'⟩ := escape_of_robust (c₀ := c₀) (Nm := Nm) hr hcont hFt hx hrob hExit
  refine ⟨ρ, hρ, fun c hc hd => ?_⟩
  obtain ⟨k, hk⟩ := exists_dist_lt_of_distZ_lt hd
  exact hρ' c hc k hk

/-- **Residual 3: the shifted `trans_escape` in the exact form of the GATE bridge.**  For the
half-integer translate `x* - j₀ + 1/2` of the leak lattice: a parameter of `Nm` near `c₀` whose
transit coordinate lands on the shifted lattice is outside the mandelbar.

The hypotheses are PARIMPL's leak data (`xstar`, `j₀`, `r₀`, `deep`), NAKANE's joint Green
continuity, the flower's `Ψ` (continuous, `Ψ_anti`) and two depth conditions: the leak level must
be deep enough that the tracked exit applies (`hx1`, `hx2`) — the design's "choose `j₀` larger". -/
theorem escape_iota {c₀ : ℂ} {Nm : Set ℂ} {trans : ℂ → ℂ} {Ft : ℂ → ℂ → ℂ} {Ψ : ℂ → ℂ}
    {z₁ : ℂ} (fl : Work.EL.ParabolicFlower (Work.EL.F c₀) ((Tantibar c₀)^[5]) z₁)
    (hΨ : Continuous Ψ) (hΨeq : ∀ w : ℂ, Ψ w = fl.Ψ w)
    (hG : Work.PARIMPL.GreenEscapeOpen)
    {xstar : ℝ} {j₀ : ℤ} {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hdeep : ∀ y ∈ Metric.closedBall (((xstar - (j₀ : ℝ)) : ℝ) : ℂ) r₀,
      0 < Work.Bottcher.green c₀ (fl.Ψ y))
    (hFt : ∀ c, Ft c = Work.EL.F c)
    (hx : (((xstar - (j₀ : ℝ) + 1 / 2 : ℝ)) : ℂ).re + r₀ / 2 < -1)
    (hExit : ExitTrackedLoc c₀ Nm trans Ft Ψ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ c ∈ Nm ∩ Metric.ball c₀ ρ,
      Work.PARIMPL.distZ (trans c) (((xstar - (j₀ : ℝ) + 1 / 2 : ℝ)) : ℂ) < r₀ / 2 →
        c ∉ Mandelbar := by
  have hdeep' : ∀ y ∈ Metric.closedBall (((xstar - (j₀ : ℝ) + 1 / 2 : ℝ)) : ℂ) r₀,
      0 < Work.Bottcher.green c₀ (fl.Ψ y) :=
    deep_half fl hdeep
  have hrob : ∃ ρ : ℝ, 0 < ρ ∧ ∀ c ∈ Metric.ball c₀ ρ, ∀ y : ℂ,
      (∃ z ∈ Metric.closedBall (((xstar - (j₀ : ℝ) + 1 / 2 : ℝ)) : ℂ) r₀,
        dist y (Ψ z) ≤ ρ) → y ∉ Work.EL.K c := by
    have hcontΨ : Continuous fl.Ψ := hΨ.congr fun w => hΨeq w
    obtain ⟨ρ, hρ, hρ'⟩ := robust_of_deep (c₀ := c₀) (Ψ := fl.Ψ) hcontΨ hG hr₀ hdeep'
    refine ⟨ρ, hρ, fun c hc y hy => hρ' c hc y ?_⟩
    obtain ⟨z, hz, hzy⟩ := hy
    exact ⟨z, hz, by rwa [hΨeq z] at hzy⟩
  exact escape_distZ (c₀ := c₀) (Nm := Nm) hr₀ hΨ hFt hx hrob hExit

/-- **The original `b`-tongue escape, derived** (PARIMPL's `LeakData.escape` field): the same
machinery at the unshifted level `x* - j₀`. -/
theorem escape_b {c₀ : ℂ} {Nm : Set ℂ} {trans : ℂ → ℂ} {Ft : ℂ → ℂ → ℂ} {Ψ : ℂ → ℂ}
    {z₁ : ℂ} (fl : Work.EL.ParabolicFlower (Work.EL.F c₀) ((Tantibar c₀)^[5]) z₁)
    (hΨ : Continuous Ψ) (hΨeq : ∀ w : ℂ, Ψ w = fl.Ψ w)
    (hG : Work.PARIMPL.GreenEscapeOpen)
    {xstar : ℝ} {j₀ : ℤ} {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hdeep : ∀ y ∈ Metric.closedBall (((xstar - (j₀ : ℝ)) : ℝ) : ℂ) r₀,
      0 < Work.Bottcher.green c₀ (fl.Ψ y))
    (hFt : ∀ c, Ft c = Work.EL.F c)
    (hx : (((xstar - (j₀ : ℝ) : ℝ)) : ℂ).re + r₀ / 2 < -1)
    (hExit : ExitTrackedLoc c₀ Nm trans Ft Ψ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ c ∈ Nm ∩ Metric.ball c₀ ρ,
      Work.PARIMPL.distZ (trans c) (((xstar - (j₀ : ℝ) : ℝ)) : ℂ) < r₀ / 2 →
        c ∉ Mandelbar := by
  have hrob : ∃ ρ : ℝ, 0 < ρ ∧ ∀ c ∈ Metric.ball c₀ ρ, ∀ y : ℂ,
      (∃ z ∈ Metric.closedBall (((xstar - (j₀ : ℝ) : ℝ)) : ℂ) r₀,
        dist y (Ψ z) ≤ ρ) → y ∉ Work.EL.K c := by
    have hcontΨ : Continuous fl.Ψ := hΨ.congr fun w => hΨeq w
    obtain ⟨ρ, hρ, hρ'⟩ := robust_of_deep (c₀ := c₀) (Ψ := fl.Ψ) hcontΨ hG hr₀ hdeep
    refine ⟨ρ, hρ, fun c hc y hy => hρ' c hc y ?_⟩
    obtain ⟨z, hz, hzy⟩ := hy
    exact ⟨z, hz, by rwa [hΨeq z] at hzy⟩
  exact escape_distZ (c₀ := c₀) (Nm := Nm) hr₀ hΨ hFt hx hrob hExit

/-! ## The escape in GATE's tongue form (the fields of `Work.GATE.TransitData`) -/

/-- **The `ι b`-tongue escape**, in the form of GATE's `Work.GATE.TransitData.escape_iota`. -/
theorem escape_iota_tongue {c₀ : ℂ} {Nm : Set ℂ} {trans : ℂ → ℂ} {Ft : ℂ → ℂ → ℂ} {Ψ : ℂ → ℂ}
    {z₁ : ℂ} (fl : Work.EL.ParabolicFlower (Work.EL.F c₀) ((Tantibar c₀)^[5]) z₁)
    (hΨ : Continuous Ψ) (hΨeq : ∀ w : ℂ, Ψ w = fl.Ψ w)
    (hG : Work.PARIMPL.GreenEscapeOpen)
    {xstar : ℝ} {j₀ : ℤ} {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hdeep : ∀ y ∈ Metric.closedBall (((xstar - (j₀ : ℝ)) : ℝ) : ℂ) r₀,
      0 < Work.Bottcher.green c₀ (fl.Ψ y))
    (hFt : ∀ c, Ft c = Work.EL.F c)
    (hx : (((xstar - (j₀ : ℝ) + 1 / 2 : ℝ)) : ℂ).re + r₀ / 2 < -1)
    (hExit : ExitTrackedLoc c₀ Nm trans Ft Ψ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ c ∈ Nm ∩ Metric.ball c₀ ρ,
      Work.GATE.iotaTongue trans (xstar - (j₀ : ℝ)) r₀ c → c ∉ Mandelbar := by
  obtain ⟨ρ, hρ, hρ'⟩ := escape_iota (c₀ := c₀) (Nm := Nm) fl hΨ hΨeq hG hr₀ hdeep hFt hx hExit
  exact ⟨ρ, hρ, fun c hc ht => hρ' c hc (distZ_lt_of_iotaTongue ht)⟩

/-- **The `b`-tongue escape**, in the form of GATE's `Work.GATE.TransitData.escape_b`. -/
theorem escape_b_tongue {c₀ : ℂ} {Nm : Set ℂ} {trans : ℂ → ℂ} {Ft : ℂ → ℂ → ℂ} {Ψ : ℂ → ℂ}
    {z₁ : ℂ} (fl : Work.EL.ParabolicFlower (Work.EL.F c₀) ((Tantibar c₀)^[5]) z₁)
    (hΨ : Continuous Ψ) (hΨeq : ∀ w : ℂ, Ψ w = fl.Ψ w)
    (hG : Work.PARIMPL.GreenEscapeOpen)
    {xstar : ℝ} {j₀ : ℤ} {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hdeep : ∀ y ∈ Metric.closedBall (((xstar - (j₀ : ℝ)) : ℝ) : ℂ) r₀,
      0 < Work.Bottcher.green c₀ (fl.Ψ y))
    (hFt : ∀ c, Ft c = Work.EL.F c)
    (hx : (((xstar - (j₀ : ℝ) : ℝ)) : ℂ).re + r₀ / 2 < -1)
    (hExit : ExitTrackedLoc c₀ Nm trans Ft Ψ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ c ∈ Nm ∩ Metric.ball c₀ ρ,
      Work.GATE.bTongue trans (xstar - (j₀ : ℝ)) r₀ c → c ∉ Mandelbar := by
  obtain ⟨ρ, hρ, hρ'⟩ := escape_b (c₀ := c₀) (Nm := Nm) fl hΨ hΨeq hG hr₀ hdeep hFt hx hExit
  exact ⟨ρ, hρ, fun c hc ht => hρ' c hc (distZ_lt_of_bTongue ht)⟩

end Work.GATE2.Escape

end
