import ChallengeDeps
import Submission.Work.BoseBox.Windows
import Submission.Work.BoseBox.lhyBox_of_av_neg
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBox.q3windowWeak` — the weak a-priori particle bound (FS §5, `eq:apriorinn+`)

## The route (and why it is *not* the suggested ε-decomposition)

The suggested route in the statement's docstring (the pointwise four-term decomposition
`Φ = PᵢPⱼΦ + PᵢQⱼΦ + QᵢPⱼΦ + QᵢQⱼΦ` with an ε-split) is **not valid as it stands**: the
`QᵢQⱼ` mass `Σ_p∫(Q_iQ_jΦ)²w` is *not* controlled by `n₊` (the requested statement
`Work.BoseBox.q3qqMass` was refuted by a child prover with an explicit counterexample — see
`Submission/Work/BoseBox/q3qqMass.lean`), and with the remaining crude bounds (kernel-`L^∞` or
`L²`) the errors beat the mean field at the healing-length box (the `ℓ³`-factors do not cancel).
The statement here is nevertheless TRUE (it is FS's theorem; the constant state at `n ≈ μℓ³` is
a low state) and the valid route is FS's own:

1. **The potential side** (`Work.BoseBox.q3potChainNoWin`): the sharp `eq:Q0n0`/`eq:Q1n0` chain,
   window-free, keeping the `A₂` Bogoliubov pairing exact:
   `qLHSword ≥ ½(8π(a v)+D)ℓ⁻³(cS1²−cS1) − 8π(a v)μ·cS1 + q4PairWord − …residues…`.
2. **The pairing** (`Work.BlockBound4.diagW_lm_appbogolubov_explicitC`, PROVED): the faithful
   diagonal p-space word plus `q4PairWord` dominates `−½(1+η)D·n(n+1)ℓ⁻³ − …errors…`, its mass
   coefficient `D = g0w0Mass` being exactly the `∬w₂`-excess of the `q₀`-term, and its kinetic
   payment being `pDiagForm s (fsKinCoeff c₀)` with `c₀` the Bogoliubov momentum cutoff.
3. **The kinetic bridge** (`Work.BoseBox.q3kinDiagBridge`): FS's word `kinForm` dominates
   `pDiagForm ℓ (fsKinCoeff (dsℓ)⁻¹)` (the τ-symbol `(1−ε_T)[r−(2sℓ)⁻¹]₊² + ε_T[r−(2dsℓ)⁻¹]₊²`
   dominates `[r−(dsℓ)⁻¹]₊²` pointwise), so step 2 applies to the corpus's word.
4. **The residues**: `qOneMass ≤ C₁n₊` (corpus `qOneMass_le_fsqC1_mul_cnPlus`), `Corr`
   sub-quadratic in `n` (`Work.BoseBox.q3corrCrudeBound`), plus the D1-diag error terms and the
   `hWfin`/`hNewton` data (`Work.BoseBox.q3NewtonData`).
5. **Coercivity arithmetic**: `½(8πσ+D)ℓ⁻³cS1²` against the pairing's `½(1+η)D n²ℓ⁻³` leaves the
   net quadratic coefficient `2πσ(1−2η) > 0` (for `η < 1/2`, achievable by taking ε₀ small
   because `η = C(R/ℓ)(1+Cc₀σ) + Cc₀σ → 0`), while the errors are linear in `n` (with `𝓜 ≤ μℓ³`
   from the FS parameters) or sub-quadratic in `n` — giving `n ≤ Cw(μℓ³ + 𝓜 + 1)`.


## Piece status (this file's worker)

### The rung to use: the SIMPLE Bogoliubov payment (NOT the refined one!)

The corpus's refined `lm:appbogolubov` (`Work.BlockBound4.diagW_lm_appbogolubov_explicitC`)
gives `pDiagForm + q4PairWord ≥ −½(1+η)D·n(n+1)/ℓ³ − (quartic-in-n errors) − …`; its
**quartic** error `C σ⁴c₀⁻³(n/ℓ³)⁴ℓ³` makes the coercivity fail for *large* `n`, so it gives no
particle bound (correct as a statement, useless here — this is why the SmallBoxA0/DL chapters
carry it only *under* the density window `n/ℓ³ ≤ 9μ`).

The rung this file uses is FS's **`eq:simpleaprioribog` at the faithful word**, whose error is
*linear* in the count — in the corpus, `Work.MGroupInput.SimpleA2Two E₁ E₂ s c₀ v h`:
```
∀ N Φ, ContDiff Φ → ∫_{abox (N+1) s}Φ² = 1 →
  −½((1+1/20)·g0w0Mass + (1/20)·(a v))·d4MassCoeff (N+1) s
    − E₁(a v)(N+1) − E₂(a v)((N+2)/s³)cnPlus s Φ ≤ pDiagForm s (fsKinCoeff c₀) Φ + q4PairWord Φ
```
i.e. `−½((21/20)D + σ/20)·n(n+1)/ℓ³ − E₁σn − E₂σ((n+1)/ℓ³)n₊` for `n = N+1` particles, plus its
small-`E₁` refinement `SimpleA2Small` (`∀ε>0 ∃E₁ ≤ ε ∃E₂ ≥ 0, SimpleA2Two E₁ E₂ …`) and the
PROVED theorem `Work.MGroupInput.simpleA2Small_of_large_box` (for every large enough box side
`ℓ` and every `c₀` with `σc₀ ≤ 10⁻⁹`).  `Submission.Work.MGroupInput.Residual` explains exactly
why the refined form cannot be used and this one can.

### LANDED pieces (sorry-free — import and use)

* `Submission.Work.BoseBox.q3potChainNoWin` — the window-free sharp potential chain (normalised `Φ`).
* `Submission.Work.BoseBox.q3corrCrudeBound` — `|Corr| ≤ C₁·N·√(N·n₊)·√(∫Φ²)`, `C₁ = chiSup²2·8πσ`.
* `Submission.Work.BoseBox.q3scaleBundle` — homogeneity `X(c•Φ) = c²X(Φ)` for
  `cS1,cS2,cnPlus,norm2N,qLHSword,q4PairWord,qOneMass,Corr` (the normalisation step).
* `Submission.Work.BoseBox.q3NewtonData` — the `hWfin`/`hNewton` data (only needed for the
  *refined* rung; harmless, keep for reference).
* In this file: `q3_ell_pos`, `q3_sigma_pos`, `q3_bigM_le_mu_ell_cube`, `q3_JC_sqrt_le`,
  `lhyC_pos`.
* In the corpus: `Work.MGroupInput.simpleA2Small_of_large_box` (the rung),
  `Submission.Work.MGroupInput.SimpleA2Two/SimpleA2Small`, `qOneMass_le_fsqC1_mul_cnPlus`,
  `cS1_eq_nat_sub_cnPlus` (`CSBox.cS1 + n₊ = n·norm2`), `Submission.Work.BoseBox.q3LHSNonpos`
  (or `Work.BoseKinLoc.Word.kinFormB_nonneg`) for `kinForm ≥ 0`.

### PENDING: `Work.BoseBox.q3kinDiagBridge`

`kinForm n ℓ d s ε_T b 0 Φ ≥ pDiagForm ℓ (fsKinCoeff ((dsℓ)⁻¹)) Φ` for
`tsupport Φ ⊆ abox n ℓ`, `0 < d ≤ 1`, `0 ≤ ε_T ≤ 1` (the τ-symbol `(1−ε_T)[r−(2sℓ)⁻¹]₊² +
ε_T[r−(2dsℓ)⁻¹]₊²` dominates `[r−(dsℓ)⁻¹]₊²`; the other three pieces of `𝒯_0` are ≥ 0).

### REMAINING ASSEMBLY (in order)

1. Parameters at `(μ, σ = a v)`: `σ>0` (`q3_sigma_pos`), `ℓ>0` (`q3_ell_pos`),
   `𝓜 ≤ μℓ³` (`q3_bigM_le_mu_ell_cube`, needs `t = μσ³ ≤ 1`), `J√t ≤ 1/2` (`q3_JC_sqrt_le`,
   needs `t ≤ 1/(4J²)`); take `ε₀` small enough for these plus `ℓ ≥ ℓ₀` (the rung's threshold)
   and `σ·(dsℓ)⁻¹ ≤ 10⁻⁹` (the rung's diluteness) — both are `ℓ → ∞` statements provable from
   `mu_ell_cube_fsParams` (`μℓ³ = t^{-166/323} → ∞`).
2. `IsLow` + `kinForm ≥ 0` gives `qLHSword Φ ≤ ℓ³Θ·norm2 ≤ 0` (since `J√t ≤ 1/2` makes `Θ ≤ 0`).
3. Normalise: `nb := ∫_{abox n ℓ}Φ² > 0` (`CSBox.sq_pos`), `Ψ x := (1/√nb)·Φ x`; the scaling
   bundle turns the chain's `Ψ`-statement into the `(1/nb)`-multiple of the `Φ`-statement, and
   `cnPlus ℓ Ψ = (cnPlus ℓ Φ)/nb ≤ 𝓜`; `cS1 ℓ Ψ + cnPlus ℓ Ψ = n`.
   If `cS1 ℓ Ψ = 0` then `n = n₊ ≤ 𝓜` and the conclusion is immediate.
4. Apply `q3potChainNoWin` to `Ψ` and `SimpleA2Two` (via `simpleA2Small_of_large_box`) at
   `s := ℓ`, `c₀ := (dsℓ)⁻¹`, `N := n − 1` (so `N+1 = n`), then the bridge to replace
   `pDiagForm` by `kinForm` (the box-quantity/`kinForm ≥ 0` remark handles non-box-supported
   states: on those `kinForm`'s Bochner integral is `0` while the *box* quantities are unchanged).
5. Absorb: the `n₊`-terms (`qOneMass ≤ C₁n₊`, the chain's `n₊-blocks`, `E₂σ((n+1)/ℓ³)n₊`) are
   `≤ (const)·σμ·n` using `n₊ ≤ 𝓜 ≤ μℓ³`; the `Corr` term is `2C₁N^{3/2}√𝓜ℓ⁻³`; the net
   quadratic coefficient is `2πσ + D/2 − ½((21/20)D + σ/20) ≥ (9/5)πσ − σ/40 > 0`.
6. Conclude `n ≤ Cw(μℓ³ + 𝓜 + 1)` by the division-by-`n^{3/2}` argument:
   `C₀√n ≤ 2C₁√𝓜 + (linear coefficient)/√n + (constant)/n^{3/2}` gives
   `n ≤ max(A/C₀, (4C₁√𝓜/C₀ + …)²) ≤ Cw(μℓ³+𝓜+1)`.
## Status of this file

The parameter facts are proved (`q3_sigma_pos`, `q3_ell_pos`, `q3_bigM_le_mu_ell_cube`,
`q3_JC_sqrt_le`, `lhyC_pos`).  The final assembly (`q3windowWeak`) is written against the four
delegated pieces
`Submission.Work.BoseBox.{q3potChainNoWin,q3kinDiagBridge,q3corrCrudeBound,q3NewtonData}`.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory

namespace Work.BoseBox

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## 1. The parameter facts -/

/-- **The box side is positive.**  `0 < R ≤ ℓ·chiR0` forces `ℓ > 0` (no parameter input). -/
lemma q3_ell_pos {R ℓ : ℝ} (hR : 0 < R) (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) :
    0 < ℓ := by
  have hchi : 0 < Submission.BoseGases.chiR0 := Submission.BoseGases.chiR0_pos
  by_contra h
  push_neg at h
  have : ℓ * Submission.BoseGases.chiR0 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hchi.le
  linarith

/-- **The scattering length is positive** under the target's hypotheses: `a v ≤ 0` would force
the box side `sideAt μ (a v) = 0` (`Work.BoseBox.sideAt_eq_zero_of_av_neg` for `a v < 0`,
`Real.zero_rpow` for `a v = 0`), contradicting `0 < R ≤ ℓ·chiR0`. -/
lemma q3_sigma_pos {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ ℓ R : ℝ} (hμ : 0 < μ)
    (hR : 0 < R) (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0)
    (hside : ℓ = sideAt μ (_root_.BoseGases.a v)) : 0 < _root_.BoseGases.a v := by
  by_contra hcon
  push_neg at hcon
  rcases lt_or_eq_of_le hcon with hlt | heq
  · have h0 : ℓ = 0 := by
      rw [hside]
      exact sideAt_eq_zero_of_av_neg (μ := μ) hμ (hav := hlt)
    rw [h0] at hRℓ
    linarith [Submission.BoseGases.chiR0_pos]
  · have h1 : (μ * (0 : ℝ)) ^ (-(1 / 2 : ℝ)) = 0 := by
      rw [mul_zero]
      exact Real.zero_rpow (by norm_num)
    have h2 : sideAt μ (0 : ℝ) = 0 := by
      simp only [sideAt, boxSide, mul_zero]
      rw [Real.zero_rpow (by norm_num : (-(1 / 2 : ℝ)) ≠ 0), mul_zero]
    have h3 : ℓ = 0 := by rw [hside, heq, h2]
    rw [h3] at hRℓ
    linarith [Submission.BoseGases.chiR0_pos]

/-- **The matrix window is inside the particle window**: `𝓜 ≤ μℓ³` for `0 < μ(a v)³ ≤ 1`
(FS `con:M<<n` at the concrete parameters; `𝓜 = (μσ³)^{-327/1292}`, `μℓ³ = (μσ³)^{-166/323}`). -/
lemma q3_bigM_le_mu_ell_cube {μ σ : ℝ} (hμ : 0 < μ) (hσ : 0 < σ) (ht : μ * σ ^ 3 ≤ 1) :
    bigM (paramsAt μ σ) σ μ ≤ μ * sideAt μ σ ^ 3 := by
  have htpos : 0 < μ * σ ^ 3 := by positivity
  have hM : bigM (paramsAt μ σ) σ μ = fsXp (μ * σ ^ 3) (-(327 / 4)) := bigM_paramsAt hμ hσ
  have hell : μ * sideAt μ σ ^ 3 = (μ * σ ^ 3) ^ (-(166 / 323 : ℝ)) := by
    rw [sideAt, paramsAt]
    exact mu_ell_cube_fsParams (μ := μ) (a := σ) hμ hσ
  have h1 : fsXp (μ * σ ^ 3) (-(327 / 4)) ≤ fsXp (μ * σ ^ 3) (-166) :=
    fsXp_le_fsXp htpos ht (by norm_num)
  have h2 : fsXp (μ * σ ^ 3) (-166) = (μ * σ ^ 3) ^ (-(166 / 323 : ℝ)) := by
    dsimp [fsXp]
    congr 1
    norm_num
  rw [hM, hell]
  rwa [h2] at h1

/-- **The a-priori `J`-term is at most `1/2`** at diluteness `t = μσ³ ≤ 1/(4J²)` (with `0 < J`,
which holds since `lhyC ≤ J` and `lhyC = 128/(15√π) > 0`): this makes the low threshold
`ℓ³Θ = −4πμ²σℓ³(1−J√t)` nonpositive. -/
lemma q3_JC_sqrt_le {J t : ℝ} (hJ : 0 < J) (ht : 0 < t) (htl : t ≤ 1 / (4 * J ^ 2)) :
    J * Real.sqrt t ≤ 1 / 2 := by
  have hJ2 : 0 < 4 * J ^ 2 := by positivity
  have h1 : Real.sqrt t ≤ 1 / (2 * J) := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have h2 : ((1 / (2 * J)) ^ 2) = 1 / (4 * J ^ 2) := by field_simp; ring
    rw [h2]
    exact htl
  calc J * Real.sqrt t ≤ J * (1 / (2 * J)) := mul_le_mul_of_nonneg_left h1 hJ.le
    _ = 1 / 2 := by field_simp

/-- `lhyC = 128/(15√π) > 0`, hence `J > 0` under `hJ : lhyC ≤ J`. -/
lemma lhyC_pos : 0 < Work.UBB.lhyC := by
  unfold Work.UBB.lhyC
  have h : (0:ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  positivity

/-- **The weak a-priori particle bound (FS §5 `thm:aprioribounds`, first conjunct, qualitative form).**

For every *low* box state (`Work.BoseBox.IsLow`, FS `eq:aprioriPsi`) whose excited count is
bounded by the matrix window `𝓜 = bigM (paramsAt μ (a v)) (a v) μ` (the `m = 1` instance of
`Work.BoseBox.SpectralNPlusLe`, FS `eq:LocalizedNPlus`), the particle number is bounded by a
*constant* times `μℓ³ + 𝓜 + 1`, at small diluteness — the particle window of FS
`eq:apriorinn+`, with a free constant instead of the sharp one.

This is all the `3Q` node `Work.BoseBox.q3Splitting` needs: its Cauchy–Schwarz bound on
`q3word` is linear in the particle number, and `ℓ^{-3}·n·n₊` is dominated by the
`lem:Q3-splitting2` error `K_H^{-3/2}K_M^{1/2}‖Φ‖²` as soon as `n ≲ μℓ³ + 𝓜`.

SUGGESTED ROUTE (constants are free; take `Cw` large and `ε₀` small — e.g. `ε₀ = 1` — and
absorb every numerical factor).  Write `ℓ = sideAt μ (a v)`, `t = μ(a v)³`, `σ = a v`.
The hypothesis `R ≤ ℓ·chiR0` with `R > 0` gives `ℓ > 0` and `σ > 0`
(`Submission/Work/BoseBox/lhyBox_of_av_neg`: `σ ≤ 0 ⟹ ℓ = 0`), hence `0 < t` and the
positivity of every `fsParams` entry (`fsXp_pos`); `Work.BoseBox.tKinWord_nonneg` gives
`0 ≤ tKinWord`, so `IsLow` (`Work.BoseBox.lowLevel`, `Work.UBB.theta_ge_lambda`) yields

  `qLHSword n ℓ μ P.d P.s P.eT P.b (wLoc ℓ v 0) (wLoc ℓ (g0 v h) 0) Φ ≤ -4πμ²σℓ³(1+ε)·‖Φ‖²`

(`Theta (a v) J μ = -4πμ²(a v)(1 - J√(μ(a v)³))`, `J√t ≤ 1` for `t ≤ 1`).  Bound the potential
word below as follows (this is the whole content; the mean-field bound for the condensate):

1. `(1/2)Σ_{i≠j}∫Φ²·w(v)(xᵢ,xⱼ) ≥ (1-ε)(1/2)Σ_{i≠j}∫(PᵢPⱼΦ)²·w(v)(xᵢ,xⱼ) - (3/ε)·[the PQ/QP/QQ
   masses]`, using the pointwise decomposition `Φ = PᵢPⱼΦ + PᵢQⱼΦ + QᵢPⱼΦ + QᵢQⱼΦ`
   (`aP`+`aQ` = 1 per slot, `aP_sub`/`aP_comm`), `(a+b+c+d)² ≥ (1-ε)a² - (1/ε)(b+c+d)²`,
   `w = wPairC ℓ v ≥ 0` (`wPairC_nonneg`) and `(b+c+d)² ≤ 3(b²+c²+d²)`.
2. The "other masses" are `≤ C_v·ℓ^{-3}·N·cnPlus` with `C_v := chiSup²·2·∫v`: the PQ/QP
   families via `Submission.QCrossD.masssum_PQ_abs_le` / `masssum_Qsw_abs_le` (generic in the
   numerator `h`, instantiate `h := v` with the fibre bound
   `Submission.KernelFibreBound.fibre_acube_abs_le`, `Integrable v` from `hv1`, support from
   `hv_supp`, evenness `radial_even hvrad`) together with `Submission.PotAppM2.pairSum_B_le`
   / `pairSum_Q_swap_le`; the QQ family via the same peel
   (`Submission.PotAppPeel.peel_sq_kernel_le` applied to `Ψ := aQ ℓ p.1 Φ` resp.
   `Ψ := aQ ℓ p.1 (aP ℓ p.2 Φ)`, both constant in one of the two slots) after
   `aQ i (aQ j Φ) = aQ i Φ - aQ i (aP j Φ)`.
3. `(1/2)Σ_{i≠j}∫(PᵢPⱼΦ)²·w(v)(xᵢ,xⱼ) ≥ (1/2)ℓ^{-3}(8πσ)·cS2 ℓ Φ - 8πσμ·cS1 ℓ Φ`:
   `Submission.PotApp.peel_sq_wPair_abs_le`-free, use `Submission.AeValue.q0_expect_ae` with
   `w₁ := wPairC ℓ (g0 v h)` and `w₂ := wPairC ℓ v` (both integrable on `acube ℓ ×ˢ acube ℓ`;
   `kernel_double_integral` for the double integral `∬wPairC ℓ v = ℓ³∫v ≥ ℓ³·8πσ` using
   `ScatKernelChosen.g0_integral` and `v = g₀ + v·w₀` pointwise), the fibre nonnegativity
   `Submission.Work.Q3Q4Peel.w1Fibre_nonneg`, and `cS2`/`cS1` from `CentredSector`.
4. `cS2 ℓ Φ ≥ (N:ℝ)²/36·norm2N` for `N ≥ 4`, `3𝓜 ≤ N` (available as
   `Submission.Work.BoseBox.q3cS2Lower`), else `N ≤ 4 + 3𝓜`;
   `cS1 ℓ Φ ≤ N·norm2N` (`CentredSector.cS1_le_norm_sq`), and the `-μΣᵢ∫Φ²·w₁Fibre` term
   `≥ -μ·C₁·N·norm2N` with `C₁ := chiSup²·2·8πσ`
   (`Submission.QCrossD.w1abs_fibre_acube_abs_le_used`).
5. Combine: `(1-ε)(1/2)8πσ·N²/36/ℓ³ - (C/ε)ℓ^{-3}N𝓜 - (C₁+8πσ)μN ≤ -4πμ²σℓ³(1+ε)`, complete the
   square in `N`, and use `𝓜 ≤ μℓ³` (`Windows.nPlusWindow_le_bigM`-style nesting / `Con_Mlln`
   from `ParamsOK`) and `t ≤ ε₀` to conclude `N ≤ Cw(μℓ³ + 𝓜 + 1)`. -/
theorem q3windowWeak {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    {J : ℝ} (hJ : Work.UBB.lhyC ≤ J) :
    ∃ Cw ε₀ : ℝ, 0 ≤ Cw ∧ 0 < ε₀ ∧
      ∀ μ : ℝ, 0 < μ → μ * (_root_.BoseGases.a v) ^ 3 ≤ ε₀ →
        Work.BoseBox.ParamsOK (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v))
          (μ * (_root_.BoseGases.a v) ^ 3) →
        J ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 →
        R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * Submission.BoseGases.chiR0 →
        ∀ n : ℕ, ∀ Φ : Submission.BoseGases.CSBox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
          Work.BoseBox.IsLow (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)) μ v h J n Φ →
          Submission.BoseGases.cnPlus (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Φ : Submission.BoseGases.X n → ℝ)
            ≤ Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)) (_root_.BoseGases.a v) μ
              * Work.BoseBox.norm2N n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Φ : Submission.BoseGases.X n → ℝ) →
          (n : ℝ) ≤ Cw * (μ * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3
            + Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)) (_root_.BoseGases.a v) μ + 1) := by
  sorry

end Work.BoseBox
