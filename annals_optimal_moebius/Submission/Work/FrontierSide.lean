import Submission.Work.FrontierA0

open OptimalMoebius Topology ContDiff
open Filter
open scoped BigOperators Matrix Topology Metric

set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# Direction constancy along a frontier arc (Target (A), local step)

Let `e₁, e₂` be degenerate frontier points of `C = flatComponent f p`
with half-disk data `(wᵢ, ρᵢ)` (`z ∈ C ⟺ signedLineFunc eᵢ wᵢ z < 0`
inside `B(eᵢ,ρᵢ)`).  If `e₂` lies within the half-disk of `e₁`
(`‖e₂ − e₁‖ < ρ₁`), then the frontier directions agree:
`w₁ = w₂ ∨ w₁ = -w₂`.  Proof chain:

1. `e₂ ∈ L(e₁)`: `φ_{w₁}(e₂) = 0`.  Indeed `e₂ ∈ frontier C ⊆ closure C`
   with `C` strictly in `{φ_{w₁} < 0}` (half-disk), so `φ_{w₁}(e₂) ≤ 0`;
   if `φ_{w₁}(e₂) < 0` then `e₂ ∈ C` (half-disk), contradicting
   `e₂ ∉ interior C = C` (frontier, `C` open).
2. A small ball `O := B(e₂, ρ₂')` inside both `B(e₁,ρ₁)` and `B(e₂,ρ₂)`
   has `C ∩ O = {φ_{w₁} < 0} ∩ O = {φ_{w₂} < 0} ∩ O`.  Since
   `φ_{w₁}(e₂) = 0`, the shifted functional
   `ψ(x) := signedLineFunc e₂ w₁ x` equals `φ_{w₁}` everywhere
   (`signedLineFunc_shift`), so on `O` the two BASE-`e₂` functionals of
   `w₁` and `w₂` have the same strict sign.
3. If `w₁ ∦ w₂`, the two lines through `e₂` cross:
   `crossing_opposite_sign_point` gives `y ∈ O` where the two functionals
   take OPPOSITE strict signs — contradicting step 2.  Hence
   `w₁ = w₂ ∨ w₁ = -w₂`: the frontier direction is constant across the
   overlap (locally constant along the arc).
* **`chain_frontier_directions_parallel`** — the finite-link heart of
   Target (A): along any finite overlapping chain of half-disks at
   frontier points (`‖eᵢ₊₁ − eᵢ‖ < ρᵢ`), the endpoint directions agree up
   to sign (`w₀ = ±wₙ`).  Proof: induction on the number of links; each
   step composes `adjacent_frontier_directions_parallel` with the
   inductive hypothesis through `sign_trans` (parallelity is transitive).
   An infinite/connected arc then follows by the same overlap argument
   (each arc point covered by its own half-disk, direction constant on
   overlaps), which is the remaining step of Target (A).

Build: `lake build Submission.Work.FrontierSide` rc=0, zero sorry.
-/

noncomputable section
namespace Submission.PaperBand

/-- **Crossing lines give opposite-sign sector points**: for two unit
directions `u ∦ v` and any radius `r > 0`, the ball around `e` contains a
point where the two signed line functionals (with the same base `e`) take
OPPOSITE strict signs.  The point is `e + δ·(u + v)` with
`δ = r/(2(‖u+v‖+1))`: `det2 (u+v) u = -det2 u v` and
`det2 (u+v) v = det2 u v`, opposite signs (nonzero because `u ∦ v`). -/
lemma crossing_opposite_sign_point {e u v : ℝ²} {r : ℝ} (hr : 0 < r)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hpar : ¬ (u = v ∨ u = -v)) :
    ∃ y : ℝ², ‖y - e‖ < r ∧
      ((signedLineFunc e u y < 0 ∧ 0 < signedLineFunc e v y) ∨
        (signedLineFunc e v y < 0 ∧ 0 < signedLineFunc e u y)) := by
  have hD : det2 u v ≠ 0 := by
    intro hD0
    exact hpar (unit_eq_or_neg_of_det2_eq_zero hu hv hD0)
  let d : ℝ² := u + v
  have hdu : det2 d u = -det2 u v := by
    dsimp [d]
    rw [det2_add_left, det2_self, det2_antisymm]
    ring
  have hdv : det2 d v = det2 u v := by
    dsimp [d]
    rw [det2_add_left, det2_self]
    ring
  let δ : ℝ := r / (2 * (‖d‖ + 1))
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  let y : ℝ² := e + δ • d
  have hvec : (e + δ • d) - e = δ • d := by abel
  have hsmul : ‖δ • d‖ = δ * ‖d‖ := by
    rw [norm_smul]
    rw [Real.norm_eq_abs]
    rw [abs_of_nonneg (le_of_lt hδ)]
  have hδb : δ * ‖d‖ < r := by
    dsimp [δ]
    have hden : 0 < 2 * (‖d‖ + 1) := by positivity
    have hm : (r / (2 * (‖d‖ + 1))) * ‖d‖ = (r * ‖d‖) / (2 * (‖d‖ + 1)) := by ring
    rw [hm]
    rw [div_lt_iff₀ hden]
    have hbig : ‖d‖ < 2 * (‖d‖ + 1) := by nlinarith [norm_nonneg d]
    have hmain : r * ‖d‖ < r * (2 * (‖d‖ + 1)) := mul_lt_mul_of_pos_left hbig hr
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmain
  have hnorm : ‖y - e‖ < r := by
    rw [hvec, hsmul]
    exact hδb
  have hfu : signedLineFunc e u y = -(δ * det2 u v) := by
    dsimp [y]
    rw [signedLineFunc_add_smul e u e d δ]
    rw [signedLineFunc_self]
    rw [hdu]
    ring
  have hfv : signedLineFunc e v y = δ * det2 u v := by
    dsimp [y]
    rw [signedLineFunc_add_smul e v e d δ]
    rw [signedLineFunc_self]
    rw [hdv]
    ring
  by_cases hDpos : 0 < det2 u v
  · refine ⟨y, hnorm, Or.inl ⟨?_, ?_⟩⟩
    · rw [hfu]
      have hpos : 0 < δ * det2 u v := mul_pos hδ hDpos
      linarith
    · rw [hfv]
      exact mul_pos hδ hDpos
  · have hDneg : det2 u v < 0 := lt_of_le_of_ne (le_of_not_gt hDpos) hD
    refine ⟨y, hnorm, Or.inr ⟨?_, ?_⟩⟩
    · rw [hfv]
      exact mul_neg_of_pos_of_neg hδ hDneg
    · rw [hfu]
      have h1 : δ * det2 u v < 0 := mul_neg_of_pos_of_neg hδ hDneg
      linarith

/-- **Adjacent frontier points have parallel half-disk directions** (the
local propagation step of Target (A)): two degenerate frontier points
`e₁, e₂` of the flat component `C` with half-disk data `(wᵢ, ρᵢ)` and
`e₂` inside `e₁`'s half-disk have `w₁ = w₂ ∨ w₁ = -w₂` — the frontier
direction is constant across the overlap. -/
theorem adjacent_frontier_directions_parallel {f : ℝ² → ℝ³} {p e₁ e₂ : ℝ²}
    (he₂F : e₂ ∈ frontier (flatComponent f p))
    {w₁ : ℝ²} {ρ₁ : ℝ} (hw₁ : ‖w₁‖ = 1) (hρ₁ : 0 < ρ₁)
    (heq₁ : ∀ z : ℝ², z ∈ Metric.ball e₁ ρ₁ →
      (z ∈ flatComponent f p ↔ signedLineFunc e₁ w₁ z < 0))
    {w₂ : ℝ²} {ρ₂ : ℝ} (hw₂ : ‖w₂‖ = 1) (hρ₂ : 0 < ρ₂)
    (heq₂ : ∀ z : ℝ², z ∈ Metric.ball e₂ ρ₂ →
      (z ∈ flatComponent f p ↔ signedLineFunc e₂ w₂ z < 0))
    (hdist : ‖e₂ - e₁‖ < ρ₁) :
    w₁ = w₂ ∨ w₁ = -w₂ := by
  have hρm : 0 < ρ₁ - ‖e₂ - e₁‖ := by linarith
  have he₂cl : e₂ ∈ closure (flatComponent f p) := by
    rw [frontier] at he₂F
    exact he₂F.1
  have hCopen : IsOpen (flatComponent f p) := isOpen_flatComponent f p
  -- φ_{w₁}(e₂) = 0
  have hφ₁e₂ : signedLineFunc e₁ w₁ e₂ = 0 := by
    have hsub : (flatComponent f p ∩ Metric.ball e₁ ρ₁) ⊆
        {x : ℝ² | signedLineFunc e₁ w₁ x < 0} := by
      intro x hx
      exact (heq₁ x hx.2).1 hx.1
    have hcl : e₂ ∈ closure (flatComponent f p ∩ Metric.ball e₁ ρ₁) := by
      rw [Metric.mem_closure_iff]
      intro ε hε
      have hδ : 0 < min ε ((ρ₁ - ‖e₂ - e₁‖) / 2) := lt_min hε (by positivity)
      rcases Metric.mem_closure_iff.mp he₂cl (min ε ((ρ₁ - ‖e₂ - e₁‖) / 2)) hδ with ⟨c, hcC, hcd⟩
      refine ⟨c, ⟨hcC, ?_⟩, ?_⟩
      · rw [Metric.mem_ball]
        have h₂ : dist c e₂ < (ρ₁ - ‖e₂ - e₁‖) / 2 :=
          lt_of_lt_of_le (by simpa [dist_comm] using hcd) (min_le_right ε ((ρ₁ - ‖e₂ - e₁‖) / 2))
        have h₃ : dist e₂ e₁ = ‖e₂ - e₁‖ := by rw [dist_eq_norm]
        calc
          dist c e₁ ≤ dist c e₂ + dist e₂ e₁ := dist_triangle c e₂ e₁
          _ < ρ₁ := by
            rw [h₃]
            nlinarith
      · exact lt_of_lt_of_le hcd (min_le_left ε ((ρ₁ - ‖e₂ - e₁‖) / 2))
    have hle : signedLineFunc e₁ w₁ e₂ ≤ 0 :=
      closure_lt_le (continuous_signedLineFunc e₁ w₁) hcl hsub
    by_contra hφne
    have hφlt : signedLineFunc e₁ w₁ e₂ < 0 := lt_of_le_of_ne hle hφne
    have he₂ball : e₂ ∈ Metric.ball e₁ ρ₁ := by
      rw [Metric.mem_ball, dist_eq_norm]
      exact hdist
    have he₂C : e₂ ∈ flatComponent f p := (heq₁ e₂ he₂ball).2 hφlt
    rw [frontier] at he₂F
    apply he₂F.2
    rw [IsOpen.interior_eq hCopen]
    exact he₂C
  -- the overlap ball O := B(e₂, ρ₂') inside both half-disks
  let ρ₂' : ℝ := min ρ₂ ((ρ₁ - ‖e₂ - e₁‖) / 2)
  have hρ₂' : 0 < ρ₂' := by
    dsimp [ρ₂']
    exact lt_min hρ₂ (by positivity)
  have hO₁ : Metric.ball e₂ ρ₂' ⊆ Metric.ball e₁ ρ₁ := by
    intro x hx
    rw [Metric.mem_ball] at hx ⊢
    have h₂ : dist x e₂ < (ρ₁ - ‖e₂ - e₁‖) / 2 :=
      lt_of_lt_of_le hx (min_le_right ρ₂ ((ρ₁ - ‖e₂ - e₁‖) / 2))
    have h₃ : dist e₂ e₁ = ‖e₂ - e₁‖ := by rw [dist_eq_norm]
    calc
      dist x e₁ ≤ dist x e₂ + dist e₂ e₁ := dist_triangle x e₂ e₁
      _ < ρ₁ := by
        rw [h₃]
        nlinarith
  have hO₂ : Metric.ball e₂ ρ₂' ⊆ Metric.ball e₂ ρ₂ := by
    intro x hx
    rw [Metric.mem_ball] at hx ⊢
    exact lt_of_lt_of_le hx (min_le_left ρ₂ ((ρ₁ - ‖e₂ - e₁‖) / 2))
  -- shift: the functional of w₁ with base e₂ equals φ_{w₁}
  have hshift : ∀ y : ℝ², signedLineFunc e₂ w₁ y = signedLineFunc e₁ w₁ y := by
    intro y
    have hs := signedLineFunc_shift e₁ e₂ w₁ y
    rw [hs, hφ₁e₂]
    ring
  -- on O the two base-e₂ functionals have the same strict sign
  have hiff : ∀ y : ℝ², y ∈ Metric.ball e₂ ρ₂' →
      (signedLineFunc e₂ w₁ y < 0 ↔ signedLineFunc e₂ w₂ y < 0) := by
    intro y hy
    have hy₁ : y ∈ Metric.ball e₁ ρ₁ := hO₁ hy
    have hy₂ : y ∈ Metric.ball e₂ ρ₂ := hO₂ hy
    have hc₁ : (signedLineFunc e₁ w₁ y < 0 ↔ y ∈ flatComponent f p) := (heq₁ y hy₁).symm
    have hc₂ : (signedLineFunc e₂ w₂ y < 0 ↔ y ∈ flatComponent f p) := (heq₂ y hy₂).symm
    rw [hshift y]
    exact hc₁.trans hc₂.symm
  -- if the directions were not parallel, a crossing sector point contradicts hiff
  by_contra hpar
  rcases crossing_opposite_sign_point (e := e₂) (r := ρ₂') hρ₂' hw₁ hw₂ hpar with ⟨y, hy, hcase⟩
  have hyball : y ∈ Metric.ball e₂ ρ₂' := by
    rw [Metric.mem_ball, dist_eq_norm]
    exact hy
  have hiffy := hiff y hyball
  rcases hcase with hc | hc
  · have hφ₂lt : signedLineFunc e₂ w₂ y < 0 := hiffy.1 hc.1
    linarith
  · have hφ₁lt : signedLineFunc e₂ w₁ y < 0 := hiffy.2 hc.1
    linarith


/-- **Finite overlap chain: directions agree up to sign (Target (A),
finite-link heart)**: let `e₀, e₁, …, eₙ` be frontier points of
`C = flatComponent f p` (`eᵢ ∈ stripInterior`), each with half-disk data
`(wᵢ, ρᵢ)` (`z ∈ C ⟺ signedLineFunc (eᵢ) (wᵢ) z < 0` inside
`B(eᵢ,ρᵢ)`, `wᵢ` unit, `ρᵢ > 0`), and suppose consecutive half-disks
overlap: `‖eᵢ₊₁ − eᵢ‖ < ρᵢ` for every `i`.  Then the directions of any
two endpoints are equal up to sign: `w₀ = wₙ ∨ w₀ = -wₙ`.  Proof:
induction on `n`; the induction step composes the overlap-link
(`adjacent_frontier_directions_parallel` between `eₘ` and `eₘ₊₁`) with
the inductive hypothesis via `sign_trans` (parallelity is transitive:
`u = ±v` and `v = ±w` give `u = ±w`). -/
theorem chain_frontier_directions_parallel {f : ℝ² → ℝ³} {p : ℝ²}
    {e : ℕ → ℝ²} {w : ℕ → ℝ²} {ρ : ℕ → ℝ}
    (heS : ∀ i : ℕ, e i ∈ stripInterior)
    (heF : ∀ i : ℕ, e i ∈ frontier (flatComponent f p))
    (hw : ∀ i : ℕ, ‖w i‖ = 1) (hρ : ∀ i : ℕ, 0 < ρ i)
    (heq : ∀ (i : ℕ) (z : ℝ²), z ∈ Metric.ball (e i) (ρ i) →
      (z ∈ flatComponent f p ↔ signedLineFunc (e i) (w i) z < 0))
    (hov : ∀ i : ℕ, ‖e (i + 1) - e i‖ < ρ i) :
    ∀ n : ℕ, w 0 = w n ∨ w 0 = - w n := by
  intro n
  induction n with
  | zero =>
      left
      rfl
  | succ m ih =>
      have hm : w m = w (m + 1) ∨ w m = - w (m + 1) :=
        adjacent_frontier_directions_parallel (e₁ := e m) (e₂ := e (m + 1))
          (heF (m + 1)) (hw m) (hρ m) (heq m) (hw (m + 1)) (hρ (m + 1))
          (heq (m + 1)) (hov m)
      exact sign_trans ih hm

end Submission.PaperBand
