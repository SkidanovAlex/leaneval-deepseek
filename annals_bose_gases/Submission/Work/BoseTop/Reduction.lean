import ChallengeDeps
import Submission.GCAssembly
import Submission.MargLipschitz
import Submission.Work.BoseTop.Pressure
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseTop` — the top reduction (`HBoxG` ⟹ the challenge theorem)

Audit 2026-10-03, nodes `R0` + `G`.  This module replaces the corpus `hpres`
gap by its two machine-checked branches and derives the challenge statement
from the single finite-volume target `Work.BoseTop.HBoxG`:

* `hpres_of_HBoxG` — the pressure-level LHY-Background bound (the old `hpres`)
  from `HBoxG v η₀ Cw` with `0 < η < η₀`, `0 ≤ Cw` and any `K > 0`:

    * if `a v = 0`, `Submission.BoseGases.hpres_of_av_zero` (no box input);
    * if `a v > 0`, `Submission.BoseGases.hpres_of_gcTwoTerm` with the
      coefficient absorption `Cw·(ρa³)^{η₀−η} ≤ K` from
      `Submission.BoseGases.eventually_absorp`;

* `Work.BoseTop.theorem_1_2_of_HBoxG` — **the deliverable**: the challenge
  statement (with `η := 1/2000`, coefficient `1`) from `HBoxGTarget v` and
  `0 ≤ a v`, with the corpus Layer-2 convergence
  (`liminf_continuous_hcont` + `eventually_hconv_of_liminf_continuous`) and
  the canonical-vs-grand-canonical inequality
  (`Submission.BoseGases.e_ge_gcPressure_add`) supplying everything else;

* the variants `theorem_1_2_of_HBoxG_param` (arbitrary `η`, `K`),
  `theorem_1_2_of_HBoxGSym` (symmetric target plus the bosonic reduction).

Nothing here is conditional on the corpus `hpres` or on the dead coupled-word
bundles; the only research input is `HBoxGTarget`.
-/

noncomputable section

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
open Submission.BoseGases
set_option autoImplicit false

namespace Work.BoseTop

open Filter Metric MeasureTheory
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## The pressure-level LHY-Background bound from the finite-volume target -/

/-- The old corpus `hpres` from the finite-volume finite-`L` target `HBoxG`
(FS `thm:LHY-Background` from `thm:LHY-Box`).  The exponent of the target must
strictly exceed the exponent of the conclusion (`η < η₀`), so that the target
coefficient `Cw` can be absorbed into the conclusion coefficient `K`
(`Cw·(ρa³)^{η₀−η} ≤ K` eventually). -/
theorem hpres_of_HBoxG {v : ℝ³ → ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1) {R : ℝ} (hR : 0 ≤ R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R) (hav : 0 ≤ a v)
    {η η₀ Cw K : ℝ} (hη : 0 < η) (hηlt : η < η₀) (hCw : 0 ≤ Cw) (hK : 0 < K)
    (hG : HBoxG v η₀ Cw) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∃ ρmax : ℝ, 0 < ρmax ∧ ρ < ρmax ∧
      lhyRhs (a v) K (1 / 2 + η) ρ ≤ gcPressure v ρmax (8 * π * a v * ρ) + 8 * π * a v * ρ * ρ := by
  by_cases hav0 : a v = 0
  · exact hpres_of_av_zero (v := v) hv hv1 hR hv_supp hav0
  · have hA : 0 < a v := lt_of_le_of_ne hav (Ne.symm hav0)
    exact hpres_of_gcTwoTerm (v := v) hv hv1 hR hv_supp hA (lt_trans hη hηlt) hη hηlt
      hCw hK hG (eventually_absorp hCw hK hA (by linarith))

/-! ## The challenge statement from the target -/

/-- **The deliverable of the area**: the challenge statement (Theorem 1.2 with
`η := 1/2000` and coefficient `1`), conditional only on the finite-volume
target `HBoxGTarget v` and on `0 ≤ a v` (supplied by the corpus as
`Submission.BoseGases.av_nonneg`, which needs radiality).  The extra
hypotheses `hv_nonneg`, `hv_memL1`, `hR`, `hv_supp` are those of the challenge
statement; they are needed for the Layer-2 thermodynamic-limit convergence.

The constants are written out (`1/2000` and coefficient `1`) so that the caller
gets exactly the challenge shape: with `Submission.BoseGases.η = 1/2000` and
`Submission.BoseGases.𝓒 _ _ = 1` a single `simpa [Submission.BoseGases.η,
Submission.BoseGases.𝓒]` converts between this conclusion and the challenge's. -/
theorem theorem_1_2_of_HBoxG (v : ℝ³ → ℝ) (hv_nonneg : 0 ≤ v) (hv_memL1 : MemLp v 1)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R) (hav : 0 ≤ a v)
    (hG : HBoxGTarget v) :
    0 < etaBose ∧ ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
      e ρ v ≥ 4 * π * ρ ^ 2 * a v *
        (1 + (128 / (15 * √π)) * √(ρ * a v ^ 3) - 1 * (ρ * a v ^ 3) ^ (1 / 2 + etaBose)) := by
  rcases hG with ⟨η₀, Cw, hη₀gt, _hη₀le, hCw, hG⟩
  constructor
  · exact etaBose_pos
  · -- Layer 2: the thermodynamic-limit convergence of the box densities along
    -- the joint filter (hypothesis-free in the corpus).
    have hcont : ∃ ρmax : ℝ, 0 < ρmax ∧
        ∀ ρ' : ℝ, 0 < ρ' → ρ' < ρmax → ContinuousAt (diagLiminf v) ρ' :=
      liminf_continuous_hcont (v := v) hv_nonneg hv_memL1
    rcases hcont with ⟨ρ₀, hρ₀, hcontρ⟩
    have hconv : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∃ x : ℝ,
        Tendsto (boxDensity v) (jointFilter ρ) (𝓝 x) :=
      eventually_hconv_of_liminf_continuous (v := v) hv_nonneg hv_memL1 hR.le hv_supp
        hρ₀ hcontρ
    -- The pressure-level bound, from the finite-volume target.
    have hpres : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∃ ρmax : ℝ, 0 < ρmax ∧ ρ < ρmax ∧
        lhyRhs (a v) 1 (1 / 2 + etaBose) ρ ≤
          gcPressure v ρmax (8 * π * a v * ρ) + 8 * π * a v * ρ * ρ :=
      hpres_of_HBoxG (v := v) hv_nonneg hv_memL1 hR.le hv_supp hav
        (η := etaBose) (η₀ := η₀) (Cw := Cw) (K := 1)
        etaBose_pos hη₀gt hCw (by norm_num) hG
    filter_upwards [self_mem_nhdsWithin, hconv, hpres] with ρ hρpos hconvρ hpresρ
    rcases hpresρ with ⟨ρmax, hρmax0, hρlt, hp⟩
    rcases hconvρ with ⟨x, hx⟩
    have hρ0 : 0 < ρ := hρpos
    have hμ : 0 ≤ 8 * π * a v * ρ := mul_nonneg (mul_nonneg (by positivity) hav) hρ0.le
    have hgc : gcPressure v ρmax (8 * π * a v * ρ) + 8 * π * a v * ρ * ρ ≤ e ρ v :=
      e_ge_gcPressure_add (v := v) (ρ := ρ) (μ := 8 * π * a v * ρ) (ρmax := ρmax)
        hρ0 hρmax0 hρlt hμ hv_nonneg hv_memL1 hR.le hv_supp hx
    have hRhs : lhyRhs (a v) 1 (1 / 2 + etaBose) ρ ≤ e ρ v := le_trans hp hgc
    simpa only [lhyRhs, etaBose] using hRhs

/-- Parameter-level form of the top reduction: arbitrary error exponent `η` and
arbitrary positive coefficient `K` (`K := 𝓒 (𝓡 v) (R / a v)` in the
challenge). -/
theorem theorem_1_2_of_HBoxG_param (v : ℝ³ → ℝ) (hv_nonneg : 0 ≤ v) (hv_memL1 : MemLp v 1)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R) (hav : 0 ≤ a v)
    {η K : ℝ} (hη : 0 < η) (hK : 0 < K) (hηle : η ≤ etaBose)
    (hG : ∃ η₀ Cw : ℝ, η < η₀ ∧ 0 ≤ Cw ∧ HBoxG v η₀ Cw) :
    0 < η ∧ ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
      e ρ v ≥ 4 * π * ρ ^ 2 * a v *
        (1 + (128 / (15 * √π)) * √(ρ * a v ^ 3) - K * (ρ * a v ^ 3) ^ (1 / 2 + η)) := by
  rcases hG with ⟨η₀, Cw, hηlt, hCw, hG⟩
  constructor
  · exact hη
  · have hcont : ∃ ρmax : ℝ, 0 < ρmax ∧
        ∀ ρ' : ℝ, 0 < ρ' → ρ' < ρmax → ContinuousAt (diagLiminf v) ρ' :=
      liminf_continuous_hcont (v := v) hv_nonneg hv_memL1
    rcases hcont with ⟨ρ₀, hρ₀, hcontρ⟩
    have hconv : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∃ x : ℝ,
        Tendsto (boxDensity v) (jointFilter ρ) (𝓝 x) :=
      eventually_hconv_of_liminf_continuous (v := v) hv_nonneg hv_memL1 hR.le hv_supp
        hρ₀ hcontρ
    have hpres : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∃ ρmax : ℝ, 0 < ρmax ∧ ρ < ρmax ∧
        lhyRhs (a v) K (1 / 2 + η) ρ ≤
          gcPressure v ρmax (8 * π * a v * ρ) + 8 * π * a v * ρ * ρ :=
      hpres_of_HBoxG (v := v) hv_nonneg hv_memL1 hR.le hv_supp hav
        (η := η) (η₀ := η₀) (Cw := Cw) (K := K) hη hηlt hCw hK hG
    filter_upwards [self_mem_nhdsWithin, hconv, hpres] with ρ hρpos hconvρ hpresρ
    rcases hpresρ with ⟨ρmax, hρmax0, hρlt, hp⟩
    rcases hconvρ with ⟨x, hx⟩
    have hρ0 : 0 < ρ := hρpos
    have hμ : 0 ≤ 8 * π * a v * ρ := mul_nonneg (mul_nonneg (by positivity) hav) hρ0.le
    have hgc : gcPressure v ρmax (8 * π * a v * ρ) + 8 * π * a v * ρ * ρ ≤ e ρ v :=
      e_ge_gcPressure_add (v := v) (ρ := ρ) (μ := 8 * π * a v * ρ) (ρmax := ρmax)
        hρ0 hρmax0 hρlt hμ hv_nonneg hv_memL1 hR.le hv_supp hx
    have hRhs : lhyRhs (a v) K (1 / 2 + η) ρ ≤ e ρ v := le_trans hp hgc
    simpa only [lhyRhs] using hRhs

/-- Top reduction from the *symmetric-sector* target plus the bosonic reduction
(node `S`): the C/B nodes of the audit produce the bound for symmetric trial
states, and `symBoxReduction` transfers it to the corpus all-functions
object. -/
theorem theorem_1_2_of_HBoxGSym (v : ℝ³ → ℝ) (hv_nonneg : 0 ≤ v) (hv_memL1 : MemLp v 1)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R) (hav : 0 ≤ a v)
    (hred : symBoxReduction v) (hG : HBoxGSymTarget v) :
    0 < etaBose ∧ ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
      e ρ v ≥ 4 * π * ρ ^ 2 * a v *
        (1 + (128 / (15 * √π)) * √(ρ * a v ^ 3) - 1 * (ρ * a v ^ 3) ^ (1 / 2 + etaBose)) :=
  theorem_1_2_of_HBoxG v hv_nonneg hv_memL1 hR hv_supp hav
    (HBoxGTarget_of_HBoxGSymTarget hv_nonneg hred hav hG)

/-- **Top reduction from the pressure-level target** (`Work.BoseTop.HBoxGp`, the
recommended one: FS `thm:LHY-Background`, immune to the localisation volume
factor).  Same conclusion as `theorem_1_2_of_HBoxG`, from the strictly weaker
hypothesis `HBoxGpTarget`. -/
theorem theorem_1_2_of_HBoxGp (v : ℝ³ → ℝ) (hv_nonneg : 0 ≤ v) (hv_memL1 : MemLp v 1)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R) (hav : 0 ≤ a v)
    (hG : HBoxGpTarget v) :
    0 < etaBose ∧ ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
      e ρ v ≥ 4 * π * ρ ^ 2 * a v *
        (1 + (128 / (15 * √π)) * √(ρ * a v ^ 3) - 1 * (ρ * a v ^ 3) ^ (1 / 2 + etaBose)) := by
  rcases hG with ⟨η₀, Cw, hη₀gt, _hη₀le, hCw, hG⟩
  constructor
  · exact etaBose_pos
  · have hcont : ∃ ρmax : ℝ, 0 < ρmax ∧
        ∀ ρ' : ℝ, 0 < ρ' → ρ' < ρmax → ContinuousAt (diagLiminf v) ρ' :=
      liminf_continuous_hcont (v := v) hv_nonneg hv_memL1
    rcases hcont with ⟨ρ₀, hρ₀, hcontρ⟩
    have hconv : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∃ x : ℝ,
        Tendsto (boxDensity v) (jointFilter ρ) (𝓝 x) :=
      eventually_hconv_of_liminf_continuous (v := v) hv_nonneg hv_memL1 hR.le hv_supp
        hρ₀ hcontρ
    have hpres : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∃ ρmax : ℝ, 0 < ρmax ∧ ρ < ρmax ∧
        lhyRhs (a v) 1 (1 / 2 + etaBose) ρ ≤
          gcPressure v ρmax (8 * π * a v * ρ) + 8 * π * a v * ρ * ρ :=
      hpres_of_HBoxGp (v := v) hv_nonneg hv_memL1 hR.le hv_supp hav
        (η := etaBose) (η₀ := η₀) (Cw := Cw) (K := 1)
        etaBose_pos hη₀gt hCw (by norm_num) hG
    filter_upwards [self_mem_nhdsWithin, hconv, hpres] with ρ hρpos hconvρ hpresρ
    rcases hpresρ with ⟨ρmax, hρmax0, hρlt, hp⟩
    rcases hconvρ with ⟨x, hx⟩
    have hρ0 : 0 < ρ := hρpos
    have hμ : 0 ≤ 8 * π * a v * ρ := mul_nonneg (mul_nonneg (by positivity) hav) hρ0.le
    have hgc : gcPressure v ρmax (8 * π * a v * ρ) + 8 * π * a v * ρ * ρ ≤ e ρ v :=
      e_ge_gcPressure_add (v := v) (ρ := ρ) (μ := 8 * π * a v * ρ) (ρmax := ρmax)
        hρ0 hρmax0 hρlt hμ hv_nonneg hv_memL1 hR.le hv_supp hx
    have hRhs : lhyRhs (a v) 1 (1 / 2 + etaBose) ρ ≤ e ρ v := le_trans hp hgc
    simpa only [lhyRhs, etaBose] using hRhs

end Work.BoseTop
