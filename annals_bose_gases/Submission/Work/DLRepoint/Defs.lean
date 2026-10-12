import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BlockBound4.BlockBound
import Submission.Work.SmallBoxTwoArm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.DLRepoint` — the DL re-point (Door 4's faithful energy)

This chapter executes the *re-point* of the downstream chain
(`SmallBoxDLBound`, `EBPerState`, the UBB assembly) onto **Door 4**'s faithful
energy `Work.BlockBound4.diagWeBAt`, in the sense of
`Submission/Work/BlockBound4/README.md` §4.

## What is re-pointed, and what remains

The DL bound (`Submission.BoseGases.smallbox_dl_energy_bound`, FS
`thm:smallbox`) is FS's per-small-box lower bound for the *shifted* energy
`ℋ_B(μ)` at chemical potential `μ`, for **every** particle count `N` (there is
no density window in FS's theorem).  Its proof is FS's **two-arm split**
(`final_v2.tex` ll. 3988–4063):

* choose `n′` in the group window `[C_n μ|B|, (C_n+1)μ|B|)` and write
  `N = m·n′ + n″` (`n″ < n′`); the many-body energy is *superadditive* in this
  decomposition (`e_B(N,μ) ≥ m·e_B(n′,μ) + e_B(n″,μ)`);
* the `m` groups of `n′` particles contribute the POSITIVE linear term
  `(1/18)·μ·(n′/|B|)·∬w_{1,B}` (FS's `eq:simpleaprioribog` chain: the sharp/
  simple per-group bound `e_B(n′) ≥ (1/9)(μ − n′/|B|)²∬w_{1,B}`, then the
  elementary `(1/9)(μ−u)² ≥ (1/18)μu` for `u ≥ 2μ`);
* the single remainder group contributes the *tight block* shape
  `(¼(n″/|B| − μ)² − ½μ²)·∬w_{1,B} − errors` (FS's `eq:refinedaprioribog`
  chain);
* FS's final convexity (`SmallBoxConvexity`, `SmallBoxTwoArm`) turns the sum
  into the theorem's density term `c·(x−μ)²/(1+x/μ)`.

In the corpus these two per-group bounds are **the faithful block bound**
`Work.BlockBound4.diagW_block_bound` (PROVED, unconditional, at the faithful
word `diagWWord = cgap·cnPlus + pDiagForm s (fsKinCoeff c₀)`) applied at the
two group counts — with the one honest caveat, recorded here in Lean, that

  *the tight block bound (constant `272π + 40`, density window `≤ 9μ`) does
  NOT imply the `m`-arm's per-group bound `(1/9)(μ−u)²∬w₁ ≤ e_B(n′)`: the
  block bound subtracts `(272π+40)·μ²a s³·Γ`, which at the group window
  `u ∈ [2μ,3μ)` dwarfs the linear target `(1/18)μu·8πa s³`.*

Hence the `m`-arm's per-group input (`MGroupInput`, FS's
`eq:simpleaprioribog`) is carried as a NAMED field of the DL bundle; the
remainder arm is *derived* from the delivered `diagW_block_bound` (no rung),
and all the arithmetic, the superadditivity and the convexity are PROVED here.

## Interface (what a caller imports)

`import Submission.Work.DLRepoint.All` (namespace `Work.DLRepoint`):

| name | meaning |
|---|---|
| `D4Regime s μ R0 K_B Ct c₀ cgap v n` | the count-`n` regime fields of the faithful block bundle (`hbox`, `hη`, `hbracket`, `hcorrreg`, `hcgap`) |
| `d4Regime_mono` | the regime transport in the count (`n ≤ n′`) |
| `mkBlockData` | assembles `Work.SmallBoxA0.KinPBoxData` from the standing data `+ n + D4Regime` |
| `d4_block_bound_at` | the **delivered** faithful block bound at a window count (from `diagW_block_bound`) |
| `MGroupInput s μ v h c₀ cgap` | FS's simple per-group bound at the group window (the named `m`-arm input) |
| `m_arm_linear` | `MGroupInput → (1/18)μu·8πa s³ ≤ e_B(u)`, `u ≥ 2μ` |
| `diagWeBAt_zero_nonneg` | `0 ≤ diagWeBAt 0 …` (the empty box) |
| `d4_dl_bound_of_groups` | the two-arm assembly: from the per-group inputs at the split counts, FS's DL shape |
| `diagWeBAt_ge_crude` | the faithful crude count bound (`EBPerState`'s re-point) |
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.DLRepoint

open Submission BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- **The error shape of the DL bound** (FS's `Γ` with the regime range `R`):
`(R/s)² + K_B³(μ(a v)³)^{1/2}`.  This is `Work.SmallBoxA0.kinPGamma` with the
range slot, i.e. `Work.BlockBound4.d4Gamma` evaluated at `R` — the DL bundle
uses the regime range `R ≥ R0`, so `d4Gamma R0 ≤ d4Gamma R` and the block
bound's error is dominated by the DL error term. -/
noncomputable def d4GammaWith (R s K_B μ : ℝ) (v : ℝ³ → ℝ) : ℝ :=
  (R / s) ^ 2 + K_B ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)

lemma d4GammaWith_eq (R s K_B μ : ℝ) (v : ℝ³ → ℝ) :
    d4GammaWith R s K_B μ v = Work.SmallBoxA0.kinPGamma R s K_B μ v := rfl

lemma d4Gamma_le_d4GammaWith {R0 R s K_B μ : ℝ} {v : ℝ³ → ℝ}
    (hR0 : 0 ≤ R0) (hR0R : R0 ≤ R) (hs : 0 < s) :
    Work.BlockBound4.d4Gamma R0 s K_B μ v ≤ d4GammaWith R s K_B μ v := by
  have hs2 : 0 < s ^ 2 := by positivity
  have hsq : (R0 / s) ^ 2 ≤ (R / s) ^ 2 := by
    have h1 : R0 / s ≤ R / s := by
      exact div_le_div_of_nonneg_right hR0R (le_of_lt hs)
    have h2 : 0 ≤ R0 / s := div_nonneg hR0 (le_of_lt hs)
    nlinarith
  unfold Work.BlockBound4.d4Gamma Work.SmallBoxA0.kinPGamma d4GammaWith
  linarith

/-- **The count-dependent regime fields of the faithful block bundle**
`Work.SmallBoxA0.KinPBoxData` (all the fields that depend on the particle
count).  Carrying them for every window count is FS's
`eq:appdellsassumption` read as a *parameter* regime; the transport in the
count is `d4Regime_mono`. -/
structure D4Regime (s μ R0 K_B Ct c₀ cgap : ℝ) (v : ℝ³ → ℝ) (n : ℕ) : Prop where
  /-- the `n₊`-coefficient fits the `ε_T`-gap constant (`KinPBoxData.hbox`). -/
  hbox : Work.SmallBoxA0.totNCoeff s μ v + Work.SmallBoxA0.kinPBogErr Ct n s v ≤ cgap
  /-- the Bogoliubov loss factor is dominated by `Γ` (`KinPBoxData.hη`). -/
  hη : (1 / 2) * |Work.SmallBoxA0.kinPeta Ct R0 s c₀ v| * (8 * π * (a v))
        * (((((n + 1 : ℕ) : ℝ)) + 1) ^ 2) * (s ^ 3)⁻¹
      ≤ μ ^ 2 * (a v) * s ^ 3 * Work.SmallBoxA0.kinPGamma R0 s K_B μ v + μ * (a v)
  /-- D1's error bracket fits the `(av)μ` budget (`KinPBoxData.hbracket`). -/
  hbracket : Work.SmallBoxA0.kinPBracket Ct n s c₀ v ≤ (88 * π + 39) * (a v) * μ
  /-- the AM–GM constant of the `Corr` residue fits `(av)μs⁴` (`KinPBoxData.hcorrreg`). -/
  hcorrreg : 4 * ((32 * π * chiSup ^ 2 * ((((n + 1 : ℕ) : ℝ)) + 1)) * (a v)) ^ 2
      * (((n + 1 : ℕ) : ℝ)) ≤ π * (a v) * μ * s ^ 4
  /-- the `ε_T`-gap constant dominates the box kinetic gap (`KinPBoxData.hcgap`). -/
  hcgap : 1 / (36 * s ^ 2) ≤ cgap
  /-- the `χ`-version of the healing-length condition (`KinPBoxData.hchi`,
  count-independent; used by the fully-excited `cS1 = 0` branch). -/
  hchi : (μ * (a v) * s ^ 2) * (1600 + 1850 * chiSup ^ 2) ≤ 1

/-- **The faithful block bundle at a given count, built from the standing data
and the count-`n` regime.**  This is the object `diagW_block_bound` consumes. -/
def mkBlockData (s μ R0 K_B Ct c₀ cgap : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (n : ℕ)
    (hs : 0 < s) (hμ : 0 < μ) (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_memL1 : MemLp v 1) (hR0 : 0 < R0) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R0)
    (hRs : R0 ≤ s * chiR0) (hμs : 1 ≤ μ * s ^ 3) (hKB : 0 < K_B)
    (hCt : 0 ≤ Ct) (hc0 : 0 < c₀) (hav : 0 < a v) (hdil : 2 * c₀ * (a v) ≤ 1)
    (hWfin : MeasureTheory.Integrable (fun q : ℝ³ × ℝ³ =>
      wScaled s (g0 v h) q.1 * wScaled s (g0 v h) q.2 * (‖q.1 - q.2‖ : ℝ)⁻¹))
    (hNewton : ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : ℝ³,
        ((FourierTransform.fourier (fun x : ℝ³ => (wScaled s (g0 v h) x : ℂ))
            (((2 * Real.pi)⁻¹) • q)).re) ^ 2 / ‖q‖ ^ 2
      ≤ 2 * (1 + 6 * Ct * (R0 / s) ^ 2) * g0w0Mass (v := v) h)
    (hD : g0w0Mass (v := v) h ≤ 8 * π * (a v))
    (hwin : ((((n + 1 : ℕ) : ℝ))) / s ^ 3 ≤ 9 * μ)
    (reg : D4Regime s μ R0 K_B Ct c₀ cgap v n) : Work.SmallBoxA0.KinPBoxData :=
  { n := n, s := s, μ := μ, R0 := R0, K_B := K_B, Ct := Ct, c₀ := c₀, cgap := cgap
    v := v, h := h
    hs := hs, hμ := hμ, hv_nonneg := hv_nonneg, hvrad := hvrad, hv_memL1 := hv_memL1
    hR0 := hR0, hv_supp := hv_supp, hRs := hRs, hμs := hμs, hKB := hKB
    hCt := hCt, hc0 := hc0, hav := hav, hdil := hdil, hWfin := hWfin, hNewton := hNewton
    hwin := hwin, hD := hD
    hbox := reg.hbox, hη := reg.hη, hbracket := reg.hbracket
    hcorrreg := reg.hcorrreg, hcgap := reg.hcgap, hchi := reg.hchi }

/-- **The delivered faithful block bound at a window count** (`BlockBound.lean`'s
unconditional `diagW_block_bound`, restated at the chapter's vocabulary).  This
is the *remainder arm* of the DL bound: no rung, no kernel-`L²` input, and no
density window beyond `(n+1)/s³ ≤ 9μ`.

(The standing data are the theorem's parameters; the DL bound's *uniform* `∃C`
comes from calling `Work.BlockBound4.diagW_block_bound` itself, whose `∃C` sits
outside its `∀ DiagWBoxData` — see `SmallBoxDLBound.lean`.) -/
theorem d4_block_bound_at (s μ R0 K_B Ct c₀ cgap : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hs : 0 < s) (hμ : 0 < μ) (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_memL1 : MemLp v 1) (hR0 : 0 < R0) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R0)
    (hRs : R0 ≤ s * chiR0) (hμs : 1 ≤ μ * s ^ 3) (hKB : 0 < K_B)
    (hCt : 0 ≤ Ct) (hc0 : 0 < c₀) (hav : 0 < a v) (hdil : 2 * c₀ * (a v) ≤ 1)
    (hWfin : MeasureTheory.Integrable (fun q : ℝ³ × ℝ³ =>
      wScaled s (g0 v h) q.1 * wScaled s (g0 v h) q.2 * (‖q.1 - q.2‖ : ℝ)⁻¹))
    (hNewton : ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : ℝ³,
        ((FourierTransform.fourier (fun x : ℝ³ => (wScaled s (g0 v h) x : ℂ))
            (((2 * Real.pi)⁻¹) • q)).re) ^ 2 / ‖q‖ ^ 2
      ≤ 2 * (1 + 6 * Ct * (R0 / s) ^ 2) * g0w0Mass (v := v) h)
    (hD : g0w0Mass (v := v) h ≤ 8 * π * (a v)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ)
      (hwin : ((((n + 1 : ℕ) : ℝ))) / s ^ 3 ≤ 9 * μ)
      (reg : D4Regime s μ R0 K_B Ct c₀ cgap v n),
      ((1 / 4 : ℝ) * (((((n + 1 : ℕ) : ℝ)) / s ^ 3) - μ) ^ 2 - (1 / 2 : ℝ) * μ ^ 2)
            * (8 * π * (a v) * s ^ 3)
        - C * μ ^ 2 * (a v) * s ^ 3 * Work.BlockBound4.d4Gamma R0 s K_B μ v
        - C * μ * (a v)
      ≤ Work.BlockBound4.diagWeBAt (n + 1) s μ v h c₀ cgap := by
  obtain ⟨C, hC0, hblk⟩ := Work.BlockBound4.diagW_block_bound
  exact ⟨C, hC0, fun n hwin reg => hblk (mkBlockData s μ R0 K_B Ct c₀ cgap v h n hs hμ
    hv_nonneg hvrad hv_memL1 hR0 hv_supp hRs hμs hKB hCt hc0 hav hdil hWfin hNewton hD
    hwin reg)⟩

end Work.DLRepoint
