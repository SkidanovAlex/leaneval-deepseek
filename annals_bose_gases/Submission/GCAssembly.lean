import ChallengeDeps
import Submission.GCPressure
import Submission.Rhs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The grand-canonical (pressure) interface — the corpus-native form of the
Fournais--Solovej LHY-Background bound

The Fournais--Solovej proof of Theorem LHY (our `theorem_1_2`) does **not**
prove finite-box canonical two-term bounds: their `e(ρ) ≥ e₀(μ) + 8πaρμ`
(eq:CompareGC, μ := ρ) is a *thermodynamic* statement, obtained by inserting
the canonical ground state into the grand-canonical operator `H − 8πaμN`.
This module makes the same reduction with the corpus's own grand-canonical
objects:

    gcDensity v μ ρmax L  := gcBox v μ ρmax L / L³        (box gc energy density)
    gcPressure v ρmax μ   := lim_{L→∞} gcDensity v μ ρmax L   (the pressure)

The corpus already knows (`boxEnergy_ge_gcBox_add`) that every admissible
`N`-particle box energy dominates the grand-canonical value:
`gcBox + μN ≤ boxEnergy N L`, i.e. `boxDensity ≥ gcDensity + μ·(N/L³)`.
Since along the joint filter `N/L³ → ρ` and `gcDensity(μ,·) → gcPressure μ`,
passing to the limit (Layer 2 convergence `hconv`) gives the thermodynamic
CompareGC inequality

    gcPressure v ρmax μ + μ·ρ ≤ e ρ v        (`e_ge_gcPressure_add`)

for every `0 ≤ μ` and `0 < ρ < ρmax`.  Choosing `μ := 8πa·ρ` (the FS
chemical-potential coefficient) and invoking an eventual pressure-level
Lee--Huang--Yang bound (`hpres`, the corpus-native LHY-Background) yields the
second conjunct of `theorem_1_2` (`theorem_1_2_of_gcPressure`).

This is the *exact* interface for the Fournais--Solovej box analysis: the
remaining deep content is a lower bound on `gcPressure v ρmax (8πaρ)` of the
shape `−4πaρ²(1 − (128/15√π)√(ρa³) + C(ρa³)^{1/2+η₀})` (their Theorem
LHY-Background, obtained from Theorem LHY-Box by CompareBoxEnergy), which is
the natural grand-canonical object on which the μ-renormalized small-box
machinery (potsplit Q0..Q4, a priori bounds, Bogoliubov, 3Q control) acts.
-/

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Along the joint filter the gc energy density of the box (a function of the
side length only) converges to the pressure. -/
lemma gcDensity_tendsto_jointFilter {v : ℝ³ → ℝ} {μ ρmax : ℝ} (hμ : 0 ≤ μ)
    (hρmax : 0 ≤ ρmax) {R : ℝ} (hR : 0 ≤ R) (hv : 0 ≤ v) (hv1 : MemLp v 1)
    (hsupp : tsupport v ⊆ ball (0 : ℝ³) R) (ρ : ℝ) :
    Tendsto (fun p : ℝ × ℕ => gcDensity v μ ρmax p.1) (jointFilter ρ)
      (𝓝 (gcPressure v ρmax μ)) := by
  have htop : Tendsto (fun L : ℝ => gcDensity v μ ρmax L) atTop
      (𝓝 (gcPressure v ρmax μ)) :=
    gcDensity_tendsto_pressure (v := v) (μ := μ) (ρmax := ρmax) (R := R)
      hμ hρmax hR hv hv1 hsupp
  have hfst : Tendsto (Prod.fst : ℝ × ℕ → ℝ) (atTop.comap Prod.fst) atTop :=
    Filter.tendsto_comap
  have hcomp : Tendsto (fun p : ℝ × ℕ => gcDensity v μ ρmax p.1)
      (atTop.comap Prod.fst) (𝓝 (gcPressure v ρmax μ)) :=
    htop.comp hfst
  exact hcomp.mono_left inf_le_left

/-- Along the joint filter, every particle number is admissible for the
truncation `ρmax` (eventually `N ≤ ρmax·L³`). -/
lemma eventually_gcAdmissible {ρ ρmax : ℝ} (hρ : 0 < ρ) (hρmax0 : 0 < ρmax)
    (hρlt : ρ < ρmax) : ∀ᶠ p : ℝ × ℕ in jointFilter ρ, gcAdmissible ρmax p.1 p.2 := by
  have ht : Tendsto (fun p : ℝ × ℕ => (p.2 : ℝ) / p.1 ^ 3) (jointFilter ρ) (𝓝 ρ) :=
    tendsto_density ρ
  have hδ : 0 < ρmax - ρ := sub_pos.mpr hρlt
  have hev : ∀ᶠ p : ℝ × ℕ in jointFilter ρ, |(p.2 : ℝ) / p.1 ^ 3 - ρ| < ρmax - ρ :=
    ht.eventually (Metric.ball_mem_nhds ρ hδ)
  filter_upwards [hev, eventually_pos_L ρ (le_of_lt hρ)] with p hp hpos
  dsimp [gcAdmissible]
  have hlt : (p.2 : ℝ) / p.1 ^ 3 < ρmax := by
    have hx := abs_lt.mp (by simpa using hp)
    linarith
  have hL3 : 0 < p.1 ^ 3 := pow_pos hpos 3
  have hn : (p.2 : ℝ) = ((p.2 : ℝ) / p.1 ^ 3) * p.1 ^ 3 := by
    field_simp [ne_of_gt hpos]
  rw [hn]
  exact le_of_lt (mul_lt_mul_of_pos_right hlt hL3)

/-- Per-box: the canonical box-energy density dominates the gc density plus
`μ` times the particle density (for admissible `N`). -/
lemma boxDensity_ge_gcDensity_add {v : ℝ³ → ℝ} (hv : 0 ≤ v) {μ ρmax : ℝ}
    (hμ : 0 ≤ μ) (hρmax : 0 ≤ ρmax) {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hNad : gcAdmissible ρmax L N) :
    gcDensity v μ ρmax L + μ * ((N : ℝ) / L ^ 3) ≤ boxDensity v (L, N) := by
  have hb := boxEnergy_ge_gcBox_add (v := v) (μ := μ) (ρmax := ρmax) (L := L)
    hμ hρmax hL hv hNad
  have hL3 : 0 < L ^ 3 := pow_pos hL 3
  -- hb : gcBox + μN ≤ boxEnergy ; divide by L³
  have hdiv : (gcBox v μ ρmax L + μ * (N : ℝ)) / L ^ 3 ≤ boxEnergy N L v / L ^ 3 :=
    div_le_div_of_nonneg_right hb (pow_nonneg hL.le 3)
  have hrew : gcDensity v μ ρmax L + μ * ((N : ℝ) / L ^ 3) =
      (gcBox v μ ρmax L + μ * (N : ℝ)) / L ^ 3 := by
    unfold gcDensity
    field_simp [ne_of_gt hL3]
  have hbox : boxDensity v (L, N) = boxEnergy N L v / L ^ 3 := by
    unfold boxDensity
    field_simp [ne_of_gt hL3]
  rw [hrew, hbox]
  exact hdiv

/-- **The thermodynamic CompareGC inequality**: for every `0 ≤ μ` and
`0 < ρ < ρmax`, if the canonical box densities converge along the joint filter
(Layer 2), then `e ρ v ≥ gcPressure v ρmax μ + μ·ρ`. -/
lemma e_ge_gcPressure_add {v : ℝ³ → ℝ} {ρ μ ρmax : ℝ} (hρ : 0 < ρ)
    (hρmax0 : 0 < ρmax) (hρlt : ρ < ρmax) (hμ : 0 ≤ μ) (hv : 0 ≤ v)
    (hv1 : MemLp v 1) {R : ℝ} (hR : 0 ≤ R) (hsupp : tsupport v ⊆ ball (0 : ℝ³) R)
    {x : ℝ} (hx : Tendsto (boxDensity v) (jointFilter ρ) (𝓝 x)) :
    gcPressure v ρmax μ + μ * ρ ≤ e ρ v := by
  haveI : (jointFilter ρ).NeBot := jointFilter_neBot (le_of_lt hρ)
  let p0 : ℝ := gcPressure v ρmax μ
  -- Convergence pieces
  have hg : Tendsto (fun q : ℝ × ℕ => gcDensity v μ ρmax q.1) (jointFilter ρ) (𝓝 p0) := by
    simpa [p0] using gcDensity_tendsto_jointFilter (v := v) (μ := μ) (ρmax := ρmax)
      hμ hρmax0.le hR hv hv1 hsupp ρ
  have hd : Tendsto (fun q : ℝ × ℕ => (q.2 : ℝ) / q.1 ^ 3) (jointFilter ρ) (𝓝 ρ) :=
    tendsto_density ρ
  have ht2 : Tendsto (fun q : ℝ × ℕ => μ * (ρ - (q.2 : ℝ) / q.1 ^ 3)) (jointFilter ρ) (𝓝 (μ * (ρ - ρ))) := by
    have hc : Tendsto (fun _ : ℝ × ℕ => μ) (jointFilter ρ) (𝓝 μ) := tendsto_const_nhds
    exact hc.mul (tendsto_const_nhds.sub hd)
  have ht2' : Tendsto (fun q : ℝ × ℕ => μ * (ρ - (q.2 : ℝ) / q.1 ^ 3)) (jointFilter ρ) (𝓝 0) := by
    simpa using ht2
  have herr : Tendsto (fun q : ℝ × ℕ => p0 - gcDensity v μ ρmax q.1) (jointFilter ρ) (𝓝 0) := by
    have hc : Tendsto (fun _ : ℝ × ℕ => p0) (jointFilter ρ) (𝓝 p0) := tendsto_const_nhds
    simpa using hc.sub hg
  have hsum : Tendsto (fun q : ℝ × ℕ =>
      boxDensity v q + (p0 - gcDensity v μ ρmax q.1) + μ * (ρ - (q.2 : ℝ) / q.1 ^ 3))
      (jointFilter ρ) (𝓝 (x + 0 + 0)) := (hx.add herr).add ht2'
  -- Per-box comparison, eventually
  have hgoal : ∀ᶠ q : ℝ × ℕ in jointFilter ρ,
      p0 + μ * ρ ≤ boxDensity v q + (p0 - gcDensity v μ ρmax q.1) +
        μ * (ρ - (q.2 : ℝ) / q.1 ^ 3) := by
    filter_upwards [eventually_gcAdmissible (ρ := ρ) (ρmax := ρmax) hρ hρmax0 hρlt,
      eventually_pos_L ρ (le_of_lt hρ)] with q hqad hqpos
    have hb := boxDensity_ge_gcDensity_add (v := v) (μ := μ) (ρmax := ρmax)
      (L := q.1) (N := q.2) hv hμ hρmax0.le hqpos hqad
    nlinarith [hb]
  have hsum' : Tendsto (fun q : ℝ × ℕ =>
      boxDensity v q + (p0 - gcDensity v μ ρmax q.1) + μ * (ρ - (q.2 : ℝ) / q.1 ^ 3))
      (jointFilter ρ) (𝓝 x) := by
    simpa using hsum
  have hBx : p0 + μ * ρ ≤ x := ge_of_tendsto hsum' hgoal
  have heq : e ρ v = x := e_eq_tendsto_boxEnergy (le_of_lt hρ) hx
  simpa [p0, heq] using hBx

end BoseGases

end Submission
