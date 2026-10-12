import ChallengeDeps
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.SboxEB
import Submission.Work.SboxHomogeneity
import Submission.Work.SharpPerState
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# First downstream consumer of the SharpPerState per-state family

`Submission/Work/SharpPerState.lean` (the machine-checked count-universal
per-state small-box bounds: `per_state_sharp`, `per_state_sharp_u`,
`qLHS_sharp(_u)`, `gap_absorb_sharp`, `cS2_count_bound`) is imported by
NOTHING downstream — this module is its first consumer, at the `eB`
(small-box ground energy, `SboxEB`) level, where
`sboxE N s μ (wPairC s v) (wPairC s (g0 v h)) Φ := kinWord N s Φ +
qLHSword(N,s,μ,wPairC s v, wPairC s (g0 v h)) Φ` is exactly the object
`per_state_sharp` bounds.

Session-156 verdict said the w₁-line route's per-state bound is dominated by
`per_state_sharp` (no `qOneMass`/`Corr` penalties at all) and that the
genuine next link is a module consuming the per-state family.  This module:

  1. `per_state_sharp_sbox` — `per_state_sharp` instantiated on NORMALISED
     `CSBox` states (`∫Φ² = 1`): the `sboxE`-form of the per-state bound,
     all-Φ (this is the literal "import + first instantiation");
  2. `normalised_count_lower` — the state-INDEPENDENT corollary for
     normalised states: dropping the nonneg `(cS1−μs³−½)²`-square and
     bounding the mass blocks by the counts (`cS1 ≤ N̂`, `cnPlus ≤ N̂`,
     `cS2 ≤ N̂²` at `∫Φ²=1`):
       sboxE Ψ ≥ −4πaμ²s³(1+1/(2μs³))² − (4C₂+25C₁)·N̂²/s³ − 3μC₁·N̂ .

What the `eB`-level extension DEMANDS (recorded in the doc of
`eB_per_state_bridge_statement`, typeset): to pass from normalised states to
the `eB := ⨅_{Φ∈CSBox} sboxE(Φ)/∫Φ²` infimum one needs the quadratic
homogeneity of `sboxE`, `cS1`, `cS2`, `cnPlus` under pointwise scaling
(`X(c·Φ) = c²·X(Φ)`), so that `sboxE(Φ)/∫Φ² = sboxE(Φ/√∫Φ²)` and the
infimum over all `CSBox` equals the infimum over normalised states.  That
scaling library is the next work item.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false
set_option linter.unusedVariables false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **`per_state_sharp` on a normalised CSBox state**: for `Ψ : CSBox N s`
with `∫Ψ² = 1`, the small-box energy `sboxE` at the chosen kernels is at
least the cS1-repulsion main term minus the μ²-block and the C₁/C₂ mass
blocks.  This is the literal instantiation of `per_state_sharp` in the `eB`
context (its conclusion, with `sboxE := kinWord + qLHSword` unfolded). -/
theorem per_state_sharp_sbox {N : ℕ} {s R μ : ℝ} {v : ℝ³ → ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hs : 0 < s) (hRs : R ≤ s * chiR0) (hμ : 0 < μ) (Ψ : CSBox N s)
    (hnorm : (∫ x in abox N s, ((Ψ : X N → ℝ) x) ^ 2) = 1) :
    (4 * π * (a v) / s ^ 3) * (cS1 s (Ψ : X N → ℝ) - μ * s ^ 3 - (1 / 2 : ℝ)) ^ 2
      - (4 * π * (a v)) * μ ^ 2 * s ^ 3 * (1 + 1 / (2 * μ * s ^ 3)) ^ 2
      - (fsqC2 (a v)) * (s ^ 3)⁻¹ * (3 * ((N : ℝ) * cnPlus s (Ψ : X N → ℝ)) + cS2 s (Ψ : X N → ℝ))
      - (fsqC1 (a v)) * (s ^ 3)⁻¹ * (7 * cS2 s (Ψ : X N → ℝ) + 18 * ((N : ℝ) * cnPlus s (Ψ : X N → ℝ)))
      - μ * (fsqC1 (a v)) * (cS1 s (Ψ : X N → ℝ) + 2 * cnPlus s (Ψ : X N → ℝ))
    ≤ sboxE N s μ (wPairC s v) (wPairC s (g0 v h)) (Ψ : X N → ℝ) := by
  have hΦc : Continuous (Ψ : X N → ℝ) := Ψ.contDiff.continuous
  have hb := per_state_sharp (N := N) (ℓ := s) (μ := μ) hs hμ hv_nonneg hvrad hv_memL1
    hR hv_supp h hRs (Φ := (Ψ : X N → ℝ)) hΦc hnorm
  simpa [sboxE] using hb

/-- **State-independent count lower bound for normalised states**: for every
normalised `CSBox` state, dropping the nonneg repulsion square and bounding
the mass blocks by the counts (`cS1 ≤ N̂`, `cnPlus ≤ N̂`, `cS2 ≤ N̂²` at
`∫Ψ² = 1`) gives the state-independent bound

    sboxE Ψ ≥ −4πaμ²s³(1+1/(2μs³))² − (4·C₂+25·C₁)·N̂²/s³ − 3μ·C₁·N̂ .

(Crude — no window, no a-priori — but it is the first genuine downstream
theorem USING `per_state_sharp`'s conclusion, and the model for the
windowed sharp versions to come.) -/
theorem normalised_count_lower {N : ℕ} {s R μ : ℝ} {v : ℝ³ → ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hs : 0 < s) (hRs : R ≤ s * chiR0) (hμ : 0 < μ) (Ψ : CSBox N s)
    (hnorm : (∫ x in abox N s, ((Ψ : X N → ℝ) x) ^ 2) = 1) :
    - (4 * π * (a v)) * μ ^ 2 * s ^ 3 * (1 + 1 / (2 * μ * s ^ 3)) ^ 2
      - (4 * (fsqC2 (a v)) + 25 * (fsqC1 (a v))) * (s ^ 3)⁻¹ * ((N : ℝ) ^ 2)
      - 3 * μ * (fsqC1 (a v)) * (N : ℝ)
    ≤ sboxE N s μ (wPairC s v) (wPairC s (g0 v h)) (Ψ : X N → ℝ) := by
  let Φ : X N → ℝ := Ψ
  have hΦc : Continuous Φ := Ψ.contDiff.continuous
  have hb := per_state_sharp_sbox hR hv_nonneg hvrad hv_memL1 hv_supp h hs hRs hμ Ψ hnorm
  -- count bounds at normalisation
  have hC1n : cS1 s Φ ≤ (N : ℝ) := by
    have h1 := cS1_le_norm_sq hs hΦc
    simpa [Φ, hnorm] using h1
  have hnp : 0 ≤ cnPlus s Φ := cnPlus_nonneg
  have hnpN : cnPlus s Φ ≤ (N : ℝ) := by
    have hS := cS1_eq_nat_sub_cnPlus hs hΦc hnorm
    have hSnn : 0 ≤ cS1 s Φ := cS1_nonneg
    nlinarith
  have hC2 : cS2 s Φ ≤ (N : ℝ) ^ 2 := by
    simpa [Φ] using (cS2_count_bound hs hΦc hnorm)
  have hav : 0 ≤ a v := (av_bounds_weak hR hv_nonneg hvrad hv_supp h).1
  have hC1nn : 0 ≤ fsqC1 (a v) := by dsimp [fsqC1]; positivity
  have hC2nn : 0 ≤ fsqC2 (a v) := by dsimp [fsqC2]; positivity
  have hsq : 0 ≤ (4 * π * (a v) / s ^ 3) * (cS1 s Φ - μ * s ^ 3 - (1 / 2 : ℝ)) ^ 2 := by
    have hc : 0 ≤ 4 * π * (a v) / s ^ 3 := by
      exact div_nonneg (by positivity : (0 : ℝ) ≤ 4 * π * (a v)) (by positivity : (0 : ℝ) ≤ s ^ 3)
    exact mul_nonneg hc (sq_nonneg _)
  -- bound the three mass blocks
  have hA1 : - (fsqC2 (a v)) * (s ^ 3)⁻¹ * (3 * ((N : ℝ) * cnPlus s Φ) + cS2 s Φ)
      ≥ - (fsqC2 (a v)) * (s ^ 3)⁻¹ * (4 * (N : ℝ) ^ 2) := by
    have hpos : 0 ≤ (fsqC2 (a v)) * (s ^ 3)⁻¹ := by
      exact mul_nonneg hC2nn (inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ s ^ 3))
    have hbnd : 3 * ((N : ℝ) * cnPlus s Φ) + cS2 s Φ ≤ 4 * (N : ℝ) ^ 2 := by
      have hNn : 0 ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le N
      nlinarith
    nlinarith
  have hA2 : - (fsqC1 (a v)) * (s ^ 3)⁻¹ * (7 * cS2 s Φ + 18 * ((N : ℝ) * cnPlus s Φ))
      ≥ - (fsqC1 (a v)) * (s ^ 3)⁻¹ * (25 * (N : ℝ) ^ 2) := by
    have hpos : 0 ≤ (fsqC1 (a v)) * (s ^ 3)⁻¹ := by
      exact mul_nonneg hC1nn (inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ s ^ 3))
    have hbnd : 7 * cS2 s Φ + 18 * ((N : ℝ) * cnPlus s Φ) ≤ 25 * (N : ℝ) ^ 2 := by
      have hNn : 0 ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le N
      nlinarith
    nlinarith
  have hA3 : - μ * (fsqC1 (a v)) * (cS1 s Φ + 2 * cnPlus s Φ)
      ≥ - 3 * μ * (fsqC1 (a v)) * (N : ℝ) := by
    have hpos : 0 ≤ μ * (fsqC1 (a v)) := by positivity
    have hbnd : cS1 s Φ + 2 * cnPlus s Φ ≤ 3 * (N : ℝ) := by nlinarith
    nlinarith
  nlinarith [hb, hsq, hA1, hA2, hA3]

/-- **The `qLHSword`-only crude count bound (the potential-side extraction)** —
`qLHS_sharp` with the nonnegative repulsion square dropped and the mass blocks
bounded by the counts (`cS1 ≤ N̂`, `cnPlus ≤ N̂`, `cS2 ≤ N̂²`) at a normalised
state:

    qLHSword Φ ≥ −4π(av)μ²s³(1+1/(2μs³))² − (4C₂+25C₁)·s⁻³·N̂² − 3μC₁·N̂ .

This is the *stronger sibling* of `normalised_count_lower` (which bounds
`sboxE = kinWord + qLHSword`, and so needs the kinetic term to be dropped
implicitly): here NO kinetic word appears on either side.  It is exactly the
extraction a faithful (`Door 4`) energy needs on the potential side, since
`diagWEnergy = cgap·cnPlus + pDiagForm + qLHSword ≥ qLHSword` whenever
`cgap ≥ 0` — see `Work.DLRepoint.diagWeBAt_ge_count_lower`, the re-pointed
sibling of `eB_ge_count_lower`, which lives in the `Work.DLRepoint` chapter
(this module cannot import it: `Work.DLRepoint` is downstream of
`Submission.Work.EBPerState`). -/
theorem qLHSword_ge_count_lower {N : ℕ} {s R μ : ℝ} {v : ℝ³ → ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hs : 0 < s) (hRs : R ≤ s * chiR0) (hμ : 0 < μ) (Ψ : CSBox N s)
    (hnorm : (∫ x in abox N s, ((Ψ : X N → ℝ) x) ^ 2) = 1) :
    - (4 * π * (a v)) * μ ^ 2 * s ^ 3 * (1 + 1 / (2 * μ * s ^ 3)) ^ 2
      - (4 * (fsqC2 (a v)) + 25 * (fsqC1 (a v))) * (s ^ 3)⁻¹ * ((N : ℝ) ^ 2)
      - 3 * μ * (fsqC1 (a v)) * (N : ℝ)
    ≤ qLHSword (N := N) s μ (wPairC s v) (wPairC s (g0 v h)) (Ψ : X N → ℝ) := by
  let Φ : X N → ℝ := Ψ
  have hΦc : Continuous Φ := Ψ.contDiff.continuous
  have hnorm' : (∫ x in abox N s, (Φ x) ^ 2) = 1 := hnorm
  have hb := qLHS_sharp (N := N) (ℓ := s) (μ := μ) hs hμ hv_nonneg hvrad hv_memL1
    hR hv_supp h hRs (Φ := Φ) hΦc hnorm'
  have hav : 0 ≤ a v := (av_bounds_weak hR hv_nonneg hvrad hv_supp h).1
  have hC1n : cS1 s Φ ≤ (N : ℝ) := by
    have h := cS1_le_norm_sq (N := N) hs hΦc (Φ := Φ)
    rw [hnorm', mul_one] at h
    exact h
  have hnp : 0 ≤ cnPlus s Φ := cnPlus_nonneg
  have hnpN : cnPlus s Φ ≤ (N : ℝ) := by
    have hS := cS1_eq_nat_sub_cnPlus hs hΦc hnorm'
    have hSnn : 0 ≤ cS1 s Φ := cS1_nonneg
    nlinarith
  have hC2 : cS2 s Φ ≤ (N : ℝ) ^ 2 := by
    simpa using (cS2_count_bound hs hΦc hnorm')
  have hC1nn : 0 ≤ fsqC1 (a v) := by dsimp [fsqC1]; positivity
  have hC2nn : 0 ≤ fsqC2 (a v) := by dsimp [fsqC2]; positivity
  have hsq : 0 ≤ (4 * π * (a v) / s ^ 3) * (cS1 s Φ - μ * s ^ 3 - (1 / 2 : ℝ)) ^ 2 := by
    have hc : 0 ≤ 4 * π * (a v) / s ^ 3 :=
      div_nonneg (by positivity : (0 : ℝ) ≤ 4 * π * (a v)) (by positivity : (0 : ℝ) ≤ s ^ 3)
    exact mul_nonneg hc (sq_nonneg _)
  have hA1 : - (fsqC2 (a v)) * (s ^ 3)⁻¹ * (3 * ((N : ℝ) * cnPlus s Φ) + cS2 s Φ)
      ≥ - (fsqC2 (a v)) * (s ^ 3)⁻¹ * (4 * (N : ℝ) ^ 2) := by
    have hpos : 0 ≤ (fsqC2 (a v)) * (s ^ 3)⁻¹ :=
      mul_nonneg hC2nn (inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ s ^ 3))
    have hbnd : 3 * ((N : ℝ) * cnPlus s Φ) + cS2 s Φ ≤ 4 * (N : ℝ) ^ 2 := by
      have hNn : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
      nlinarith
    nlinarith
  have hA2 : - (fsqC1 (a v)) * (s ^ 3)⁻¹ * (7 * cS2 s Φ + 18 * ((N : ℝ) * cnPlus s Φ))
      ≥ - (fsqC1 (a v)) * (s ^ 3)⁻¹ * (25 * (N : ℝ) ^ 2) := by
    have hpos : 0 ≤ (fsqC1 (a v)) * (s ^ 3)⁻¹ :=
      mul_nonneg hC1nn (inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ s ^ 3))
    have hbnd : 7 * cS2 s Φ + 18 * ((N : ℝ) * cnPlus s Φ) ≤ 25 * (N : ℝ) ^ 2 := by
      have hNn : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
      nlinarith
    nlinarith
  have hA3 : - μ * (fsqC1 (a v)) * (cS1 s Φ + 2 * cnPlus s Φ)
      ≥ - 3 * μ * (fsqC1 (a v)) * (N : ℝ) := by
    have hpos : 0 ≤ μ * (fsqC1 (a v)) := by positivity
    have hbnd : cS1 s Φ + 2 * cnPlus s Φ ≤ 3 * (N : ℝ) := by nlinarith
    nlinarith
  nlinarith [hb, hsq, hA1, hA2, hA3]

/-- **Typeset `eB`-bridge statement (record)**: passing from normalised
states to the `eB`-infimum needs the quadratic homogeneity of `sboxE`,
`cS1`, `cS2`, `cnPlus` under pointwise scaling (`X(c·Φ) = c²·X(Φ)`), so
that `sboxE(Φ)/∫Φ² = sboxE(Φ/√∫Φ²)`; then
`eB ≥ −4πaμ²s³(1+1/(2μs³))² − (4C₂+25C₁)N̂²/s³ − 3μC₁N̂` follows from
`normalised_count_lower` by taking the infimum over normalised states (the
infimum over all `CSBox` equals that over normalised ones by homogeneity).
The homogeneity library is the next work item. -/
def eB_per_state_bridge_statement {N : ℕ} {s R μ : ℝ} {v : ℝ³ → ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hs : 0 < s) (hRs : R ≤ s * chiR0) (hμ : 0 < μ) : Prop :=
  - (4 * π * (a v)) * μ ^ 2 * s ^ 3 * (1 + 1 / (2 * μ * s ^ 3)) ^ 2
      - (4 * (fsqC2 (a v)) + 25 * (fsqC1 (a v))) * (s ^ 3)⁻¹ * ((N : ℝ) ^ 2)
      - 3 * μ * (fsqC1 (a v)) * (N : ℝ)
    ≤ eB N s μ v h

lemma abox_integral_sq_smul {N : ℕ} (s : ℝ) (Φ : X N → ℝ) (c : ℝ) :
    (∫ x in abox N s, ((c • Φ) x) ^ 2) = (c ^ 2) * (∫ x in abox N s, (Φ x) ^ 2) := by
  have hpt : ∀ x : X N, ((c • Φ) x) ^ 2 = (c ^ 2) * (Φ x) ^ 2 := by
    intro x
    simp [Pi.smul_apply, smul_eq_mul]
    ring
  calc
    (∫ x in abox N s, ((c • Φ) x) ^ 2)
        = (∫ x in abox N s, (c ^ 2) * (Φ x) ^ 2) := by
            apply integral_congr_ae
            exact ae_of_all _ hpt
    _ = (c ^ 2) * (∫ x in abox N s, (Φ x) ^ 2) := by
            simpa using (MeasureTheory.integral_const_mul (μ := (volume : Measure (X N)).restrict (abox N s))
              (r := c ^ 2) (f := fun x : X N => (Φ x) ^ 2))

/-- **The eB-infimum bound from `per_state_sharp`**: every `CSBox` state Φ
(not necessarily normalised) has `sboxE(Φ)/∫Φ² ≥ B₀` — normalise
`Ψ := (√I)⁻¹ • Φ` (quadratic homogeneity `sboxE_smul` + counts) and apply
`normalised_count_lower` — hence the infimum satisfies `B₀ ≤ eB`:

    eB ≥ −4πaμ²s³(1+1/(2μs³))² − (4C₂+25C₁)·N̂²/s³ − 3μC₁·N̂ . -/
theorem eB_ge_count_lower {N : ℕ} {s R μ : ℝ} {v : ℝ³ → ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hs : 0 < s) (hRs : R ≤ s * chiR0) (hμ : 0 < μ) :
    - (4 * π * (a v)) * μ ^ 2 * s ^ 3 * (1 + 1 / (2 * μ * s ^ 3)) ^ 2
      - (4 * (fsqC2 (a v)) + 25 * (fsqC1 (a v))) * (s ^ 3)⁻¹ * ((N : ℝ) ^ 2)
      - 3 * μ * (fsqC1 (a v)) * (N : ℝ)
    ≤ eB N s μ v h := by
  let B₀ : ℝ := - (4 * π * (a v)) * μ ^ 2 * s ^ 3 * (1 + 1 / (2 * μ * s ^ 3)) ^ 2
      - (4 * (fsqC2 (a v)) + 25 * (fsqC1 (a v))) * (s ^ 3)⁻¹ * ((N : ℝ) ^ 2)
      - 3 * μ * (fsqC1 (a v)) * (N : ℝ)
  have hper : ∀ Φ : CSBox N s,
      B₀ ≤ (sboxE N s μ (wPairC s v) (wPairC s (g0 v h)) (Φ : X N → ℝ)) /
        (∫ x in abox N s, ((Φ : X N → ℝ) x) ^ 2) := by
    intro Φ
    let Ph : X N → ℝ := Φ
    let I : ℝ := ∫ x in abox N s, ((Ph) x) ^ 2
    let c : ℝ := (Real.sqrt I)⁻¹
    have hIpos : 0 < I := by simpa [I, Ph] using Φ.sq_pos
    have hIne : I ≠ 0 := ne_of_gt hIpos
    have hsqrt0 : 0 < Real.sqrt I := Real.sqrt_pos.mpr hIpos
    have hc2 : c ^ 2 = I⁻¹ := by
      dsimp [c]
      have hs : (Real.sqrt I) ^ 2 = I := Real.sq_sqrt (le_of_lt hIpos)
      calc
        ((Real.sqrt I)⁻¹) ^ 2 = ((Real.sqrt I) ^ 2)⁻¹ := by rw [← inv_pow]
        _ = I⁻¹ := by rw [hs]
    have hcne : c ≠ 0 := by
      dsimp [c]
      exact inv_ne_zero (ne_of_gt hsqrt0)
    -- the normalised state Ψ := c • Ph
    have hΨs : ContDiff ℝ ∞ (c • Ph) := Φ.contDiff.const_smul c
    have hΨne : c • Ph ≠ 0 := smul_ne_zero hcne Φ.nezero
    have hnorm1 : (∫ x in abox N s, ((c • Ph) x) ^ 2) = 1 := by
      rw [abox_integral_sq_smul]
      rw [hc2]
      field_simp [hIne]
      simp [I]
    have hΨpos : 0 < ∫ x in abox N s, ((c • Ph) x) ^ 2 := by
      rw [hnorm1]
      norm_num
    let Ψ : CSBox N s := CSBox.ofFun hΨs hΨne hΨpos
    have hnormΨ : (∫ x in abox N s, ((Ψ : X N → ℝ) x) ^ 2) = 1 := by
      change (∫ x in abox N s, ((c • Ph) x) ^ 2) = 1
      exact hnorm1
    have hmain := normalised_count_lower hR hv_nonneg hvrad hv_memL1 hv_supp h hs hRs hμ Ψ hnormΨ
    -- hmain : B₀ ≤ sboxE(Ψ)
    have hE : sboxE N s μ (wPairC s v) (wPairC s (g0 v h)) (c • Ph)
        = sboxE N s μ (wPairC s v) (wPairC s (g0 v h)) Ph / I := by
      have hsmul := sboxE_smul (N := N) (s := s) (μ := μ) (w := wPairC s v) (w1 := wPairC s (g0 v h))
        (Φ := Ph) Φ.contDiff c
      -- hsmul : sboxE(c•Ph) = c²·sboxE Ph
      rw [hsmul, hc2]
      field_simp [hIne]
    calc
      B₀ ≤ sboxE N s μ (wPairC s v) (wPairC s (g0 v h)) (Ψ : X N → ℝ) := by
            change B₀ ≤ sboxE N s μ (wPairC s v) (wPairC s (g0 v h)) (c • Ph)
            exact hmain
      _ = sboxE N s μ (wPairC s v) (wPairC s (g0 v h)) Ph / I := by
            change sboxE N s μ (wPairC s v) (wPairC s (g0 v h)) (c • Ph)
                = sboxE N s μ (wPairC s v) (wPairC s (g0 v h)) Ph / I
            exact hE
      _ = (sboxE N s μ (wPairC s v) (wPairC s (g0 v h)) (Φ : X N → ℝ)) /
            (∫ x in abox N s, ((Φ : X N → ℝ) x) ^ 2) := by
            rfl
  have hne : Nonempty (CSBox N s) := nonempty_CSBox N hs
  rw [eB]
  apply le_ciInf (ι := CSBox N s)
  exact hper

end BoseGases

end Submission
