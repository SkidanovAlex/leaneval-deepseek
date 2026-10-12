import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Submission.Layer2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Layer 2 — the classical interface (thermodynamic limit = Legendre transform)

Ingredient 1 (`gcExcess_witness_aux`, `Submission.Excess`) is what the
machine-verified chain consumes (`Closure2.gcSup_upper_of_excess` +
`GCPressure.eventually_hconv_of_gcSup_upper`, assembled in
`Layer2.layer2_hconv_of_excess`).  This module provides the bridge *in the
other direction*: it shows that Ingredient 1 follows from the natural
*classical* statement of the thermodynamic limit — namely that the canonical
diagonal energy density converges to the Legendre transform of the pressure,

    diag v ρ L := E(⌊ρL³⌋,L)/L³  ⟶  gcSup v ρmax ρ = sup_{μ ≥ 0} (p(μ) + μρ).

Indeed, if `diag(ρ,·) → x` with `x ≤ gcSup(ρ)` (the equality `x = gcSup(ρ)`
then follows automatically from `GCPressure.diagLiminf_ge_gcSup`), then for
every `ε > 0` one may pick `μ̄ ≥ 0` with `p(μ̄)+μ̄ρ ≥ gcSup(ρ) − ε/2`, and the
convergences of `diag`, of the grand-canonical density `gcDensity(μ̄,·) → p(μ̄)`
and of the floor density `⌊ρL³⌋/L³ → ρ` give, eventually in `L`,

    (E(⌊ρL³⌋,L) − gcBox(μ̄,ρmax,L) − μ̄·⌊ρL³⌋)/L³  ≤  ε,

i.e. `gcExcess_witness_aux v ρmax ρ`.

The upshot (theorem `layer2_hconv_of_diag_tendsto_gcSup`): the whole of
Layer 2 reduces to the single classical input

    ∀ ρ ∈ (0,ρmax):  diag v ρ L ⟶ gcSup v ρmax ρ   as L → ∞

(the existence of the thermodynamic limit and its identification with the
grand-canonical Legendre envelope — the T = 0 equivalence of ensembles).
-/

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Witness form implies the value-level form: if eventually some `μ ≥ 0`
satisfies `diag ρ L − ε ≤ gcCanonValue μ L`, then the canonical gap is
eventually `≤ ε·L³` (multiply by `L³ > 0`). -/
lemma gcExcess_witness_aux_of_witness {v : ℝ³ → ℝ} {ρ ρmax : ℝ}
    (hw : gcExcess_witness v ρmax ρ) : gcExcess_witness_aux v ρmax ρ := by
  intro ε hε
  filter_upwards [hw ε hε, eventually_ge_atTop (1 : ℝ)] with L hwL hL1
  have hLpos : 0 < L := by linarith
  have hL3 : L ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt hLpos)
  rcases hwL with ⟨μ, hμ, hle⟩
  refine ⟨μ, hμ, ?_⟩
  -- gcCanonGap / L³ = diag − gcCanonValue ≤ ε, then multiply by L³
  have hEq : gcCanonGap v ρmax ρ μ L / L ^ 3 = diag v ρ L - gcCanonValue v ρmax ρ μ L := by
    dsimp [gcCanonGap, gcCanonValue, gcDensity, diag]
    have h : (boxEnergy (Nat.floor (ρ * L ^ 3)) L v - gcBox v μ ρmax L - μ * (Nat.floor (ρ * L ^ 3) : ℝ)) / L ^ 3 =
        boxEnergy (Nat.floor (ρ * L ^ 3)) L v / L ^ 3 - gcBox v μ ρmax L / L ^ 3 - μ * ((Nat.floor (ρ * L ^ 3) : ℝ) / L ^ 3) := by
      field_simp [hL3]
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h
  have hd : gcCanonGap v ρmax ρ μ L / L ^ 3 ≤ ε := by
    rw [hEq]
    linarith
  have hmul : (gcCanonGap v ρmax ρ μ L / L ^ 3) * L ^ 3 ≤ ε * L ^ 3 :=
    mul_le_mul_of_nonneg_right hd (le_of_lt (pow_pos hLpos 3))
  have hcancel : (gcCanonGap v ρmax ρ μ L / L ^ 3) * L ^ 3 = gcCanonGap v ρmax ρ μ L := by
    field_simp [hL3]
  rwa [hcancel] at hmul

/-- Supremum approximation: for every `η > 0` there is `μ ≥ 0` with
`gcSup(ρ) − η ≤ p(μ) + μ·ρ`. -/
lemma gcSup_approx {v : ℝ³ → ℝ} {ρ ρmax η : ℝ} (hη : 0 < η) :
    ∃ μ : ℝ, 0 ≤ μ ∧ gcSup v ρmax ρ - η ≤ gcPressure v ρmax μ + μ * ρ := by
  by_contra hnot
  push Not at hnot
  have hub : ∀ y : ℝ, y ∈ gcSupSet v ρmax ρ → y ≤ gcSup v ρmax ρ - η := by
    intro y hy
    rcases hy with ⟨μ, hμ, rfl⟩
    exact le_of_lt (hnot μ hμ)
  have hsle : sSup (gcSupSet v ρmax ρ) ≤ gcSup v ρmax ρ - η := by
    apply csSup_le (gcSupSet_nonempty v ρmax ρ)
    exact hub
  have : gcSup v ρmax ρ ≤ gcSup v ρmax ρ - η := by
    simpa [gcSup] using hsle
  linarith

/-- The grand-canonical value at `μ` converges: `gcCanonValue(μ,L) → p(μ)+μρ`. -/
lemma tendsto_gcCanonValue {v : ℝ³ → ℝ} {ρ ρmax μ R : ℝ} (hμ : 0 ≤ μ)
    (hρmax : 0 ≤ ρmax) (hρ0 : 0 ≤ ρ) (hR : 0 ≤ R) (hv : 0 ≤ v)
    (hv1 : MemLp v 1) (hsupp : tsupport v ⊆ ball (0 : ℝ³) R) :
    Tendsto (fun L : ℝ => gcCanonValue v ρmax ρ μ L) atTop
      (𝓝 (gcPressure v ρmax μ + μ * ρ)) := by
  have hden := gcDensity_tendsto_pressure (v := v) (μ := μ) (ρmax := ρmax) (R := R)
    hμ hρmax hR hv hv1 hsupp
  have hr := tendsto_rhoL (ρ := ρ) hρ0
  have hmain := hden.add (hr.const_mul μ)
  -- hmain : Tendsto (fun L => gcDensity v μ ρmax L + μ * rhoL ρ L) (𝓝 (p + μ·ρ))
  -- gcCanonValue v ρmax ρ μ L = gcDensity v μ ρmax L + μ * rhoL ρ L
  simpa [gcCanonValue, rhoL] using hmain

/-- Ingredient 1 at density `ρ` follows from convergence of the diagonal to a
value no larger than the Legendre supremum:
`diag(ρ,·) → x` with `x ≤ gcSup(ρ)`  ⟹  `gcExcess_witness_aux v ρmax ρ`. -/
theorem haux_of_diag_tendsto_le {v : ℝ³ → ℝ} {ρ ρmax x : ℝ} (hv : 0 ≤ v)
    (hv1 : MemLp v 1) (hρmax : 0 ≤ ρmax) (hρ0 : 0 ≤ ρ)
    {R : ℝ} (hR : 0 ≤ R) (hsupp : tsupport v ⊆ ball (0 : ℝ³) R)
    (hlim : Tendsto (fun L : ℝ => diag v ρ L) atTop (𝓝 x))
    (hle : x ≤ gcSup v ρmax ρ) : gcExcess_witness_aux v ρmax ρ := by
  apply gcExcess_witness_aux_of_witness
  intro ε hε
  have hη : 0 < ε / 2 := by positivity
  rcases gcSup_approx (v := v) (ρ := ρ) (ρmax := ρmax) (η := ε / 2) hη with ⟨m0, hm0, hm0le⟩
  have hval := tendsto_gcCanonValue (v := v) (ρ := ρ) (ρmax := ρmax) (μ := m0) (R := R)
    hm0 hρmax hρ0 hR hv hv1 hsupp
  let β : ℝ := gcPressure v ρmax m0 + m0 * ρ - x
  let g : ℝ → ℝ := fun L => gcCanonValue v ρmax ρ m0 L - diag v ρ L
  have hg : Tendsto g atTop (𝓝 β) := by
    dsimp [g, β]
    exact hval.sub hlim
  have hβ : -ε / 2 ≤ β := by
    dsimp [β]
    have hα : gcSup v ρmax ρ - ε / 2 ≤ gcPressure v ρmax m0 + m0 * ρ := hm0le
    nlinarith
  have hclose : ∀ᶠ L : ℝ in atTop, |g L - β| < ε / 2 := by
    have hb : Metric.ball β (ε / 2) ∈ 𝓝 β := Metric.ball_mem_nhds β hη
    have hpre : ∀ᶠ L in atTop, g L ∈ Metric.ball β (ε / 2) := hg hb
    filter_upwards [hpre] with L hL
    exact Metric.mem_ball.mp hL
  -- eventually diag v ρ L - ε ≤ gcCanonValue v ρmax ρ m0 L
  have hev : ∀ᶠ L : ℝ in atTop, diag v ρ L - ε ≤ gcCanonValue v ρmax ρ m0 L := by
    filter_upwards [hclose, eventually_ge_atTop (1 : ℝ)] with L hc hL1
    have hgt : -ε < g L := by
      have hc' : β - ε / 2 < g L := by
        have habs := abs_lt.mp hc   -- |g L - β| < ε/2
        nlinarith
      nlinarith [hβ, hc']
    dsimp [g] at hgt
    nlinarith
  exact hev.mono (fun L hL => ⟨m0, hm0, hL⟩)

/-- The classical identity form: if the diagonal converges to the Legendre
supremum itself, Ingredient 1 holds at `ρ`. -/
theorem haux_of_diag_tendsto_gcSup {v : ℝ³ → ℝ} {ρ ρmax : ℝ} (hv : 0 ≤ v)
    (hv1 : MemLp v 1) (hρmax : 0 < ρmax) (hρ0 : 0 < ρ)
    {R : ℝ} (hR : 0 ≤ R) (hsupp : tsupport v ⊆ ball (0 : ℝ³) R)
    (hlim : Tendsto (fun L : ℝ => diag v ρ L) atTop (𝓝 (gcSup v ρmax ρ))) :
    gcExcess_witness_aux v ρmax ρ := by
  exact haux_of_diag_tendsto_le (v := v) (ρ := ρ) (ρmax := ρmax) (x := gcSup v ρmax ρ)
    hv hv1 hρmax.le hρ0.le hR hsupp hlim le_rfl

/-- **The classical interface of Layer 2.**  If the thermodynamic limit exists
and equals the Legendre supremum of the grand-canonical pressure at every
density of `(0,ρmax)` — the statement `diag v ρ L → gcSup v ρmax ρ` — then the
box-energy densities converge along the joint filter at every small density
(the `hconv` hypothesis of `Endgame.lhy_bound_of_convergence_and_box`). -/
theorem layer2_hconv_of_diag_tendsto_gcSup {v : ℝ³ → ℝ} (hv : 0 ≤ v)
    (hv1 : MemLp v 1) {R : ℝ} (hR : 0 ≤ R) (hsupp : tsupport v ⊆ ball (0 : ℝ³) R)
    {ρmax : ℝ} (hρmax : 0 < ρmax)
    (hconv : ∀ ρ : ℝ, 0 < ρ → ρ < ρmax →
      Tendsto (fun L : ℝ => diag v ρ L) atTop (𝓝 (gcSup v ρmax ρ))) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∃ x : ℝ, Tendsto (boxDensity v) (jointFilter ρ) (𝓝 x) := by
  apply layer2_hconv_of_excess (v := v) (ρmax := ρmax) hv hv1 hR hsupp hρmax
  intro ρ hρ0 hρlt
  exact haux_of_diag_tendsto_gcSup (v := v) (ρ := ρ) (ρmax := ρmax)
    hv hv1 hρmax hρ0 hR hsupp (hconv ρ hρ0 hρlt)


/-- The converse direction: Ingredient 1 on `(0,ρmax)` forces the diagonal to
converge to the Legendre supremum (composition of
`Closure2.gcSup_upper_of_excess` with
`GCPressure.diag_tendsto_of_gcSup_upper`).  Together with
`layer2_hconv_of_diag_tendsto_gcSup` this shows that Layer 2 is *equivalent*
to the classical statement `diag v ρ L → gcSup v ρmax ρ` on `(0,ρmax)`. -/
theorem diag_tendsto_gcSup_of_excess {v : ℝ³ → ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1)
    {R : ℝ} (hR : 0 ≤ R) (hsupp : tsupport v ⊆ ball (0 : ℝ³) R) {ρmax : ℝ}
    (hρmax : 0 < ρmax) (haux : ∀ ρ : ℝ, 0 < ρ → ρ < ρmax → gcExcess_witness_aux v ρmax ρ) :
    ∀ ρ : ℝ, 0 < ρ → ρ < ρmax →
      Tendsto (fun L : ℝ => diag v ρ L) atTop (𝓝 (gcSup v ρmax ρ)) := by
  have hupper := gcSup_upper_of_excess (v := v) (ρmax := ρmax) hv hv1 hR hsupp hρmax haux
  intro ρ hρ0 hρlt
  exact diag_tendsto_of_gcSup_upper (v := v) (ρ := ρ) (ρmax := ρmax) hv hv1 hρmax.le hR hsupp
    hρ0 hρlt hupper

end BoseGases

end Submission
