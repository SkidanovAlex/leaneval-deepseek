import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.BoseB6.PairGround
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.unusedVariables false

/-!
# Node B6 — FS §10 `thm:BogHamDiag`: the multi-mode Bogoliubov diagonalisation

FS §10 defines the quadratic Bogoliubov Hamiltonian

    𝒦^Bog = ½(2π)⁻³ℓ³ ∫ [ 𝒜(k)(a_k†a_k + a_{−k}†a_{−k}) + ℬ(k)(a_k†a_{−k}† + a_k a_{−k})
                          + 𝒞(k)(a_k† + a_{−k}† + a_k + a_{−k}) ] dk

with `𝒜(k) = τ(k) + ρ_zŴ₁(k)`, `ℬ(k) = ρ_zŴ₁(k)`, `𝒞(k) = ℓ⁻³(ρ_z−μ)Ŵ₁(0)χ̂_Λ(k)z`
(`eq:BogHamPositive-1`).  Three ingredients must be combined:

* the **mode decomposition** `𝒦^Bog = ½Σ_k q_k` over one representative per pair
  `(k,−k)`, together with the per-pair *ground* inequality `eq:BogIneq` — this is
  the second-quantisation interface of node **B4** (`decomp`), the per-pair
  inequality being node B6's `Work.BoseB6.pairForm_ground` (the corpus's
  `Submission.Fock2ModeShift.fms_ground_estimate`);
* the **zero-point sum**, compared with the model lattice sum of node B6's
  lattice chapter up to the `I₂` mass term and the FS error `ε` (`hzero`);
* the **`𝒞`-sum** bound (`hkappa`), FS's `(ρ_z−μ)²(ĝ(0)/2)ℓ³(1+C(μa³)R²/a²)`.

`sum_pairGround_le` is the finite-sum step; `bogHamDiag_fs_display` is FS's display

    ⟨Φ,𝒦^BogΦ⟩ ≥ −(ĝω(0)/2)ρ_z²ℓ³ + 4π·(128/(15√π))·ρ_z²a√(ρ_z a³)ℓ³ − (errors)

with `eq:BogHamDiag`'s and `lem:BogIntegral`'s two big terms written literally.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB6

/-- **B4's interface for FS §10 `thm:BogHamDiag`.**

`ι` indexes one representative per mode pair `(k,−k)` of the box; `A`, `B`, `Ccoef`
are FS's `𝒜(k)`, `ℬ(k)`, `𝒞(k)`; `q k` is the value at the state of the pair form
`½[𝒜(a_k†a_k + a_{−k}†a_{−k}) + ℬ(a_k†a_{−k}† + a_ka_{−k}) + 𝒞(a_k†+a_{−k}†+a_k+a_{−k})]`;
`Kbog` is the value of `𝒦^Bog` at the same state.  `decomp` is the asserted mode
decomposition (B4), `pairGround` the per-pair Bogoliubov inequality (`eq:BogIneq`,
node B6's `Work.BoseB6.pairForm_ground`). -/
structure BogHamInterface (ι : Type*) [Fintype ι] where
  /-- the value of `𝒦^Bog` at the state (FS `eq:BogHamPositive-1`). -/
  Kbog : ℝ
  /-- FS's `𝒜(k) = τ(k) + ρ_zŴ₁(k)`. -/
  A : ι → ℝ
  /-- FS's `ℬ(k) = ρ_zŴ₁(k)`. -/
  B : ι → ℝ
  /-- FS's `𝒞(k)`. -/
  Ccoef : ι → ℝ
  /-- the value of the mode pair form of `k`. -/
  q : ι → ℝ
  /-- `𝒜(k) > 0`. -/
  Apos : ∀ k, 0 < A k
  /-- `|ℬ(k)| ≤ 𝒜(k)`. -/
  Bsmall : ∀ k, |B k| ≤ A k
  /-- `𝒜(k)+ℬ(k) > 0` (FS: `|ℬ| < 𝒜` or `ℬ = 𝒜`). -/
  AplusB : ∀ k, 0 < A k + B k
  /-- the mode decomposition `𝒦^Bog = ½Σ_k q_k` (B4). -/
  decomp : Kbog = ∑ k, (1 / 2) * q k
  /-- the per-pair Bogoliubov inequality (`eq:BogIneq`). -/
  pairGround : ∀ k, -(bogZeroPoint (A k) (B k) + bogKappaErr (A k) (B k) (Ccoef k)) ≤ q k

variable {ι : Type*} [Fintype ι]

/-- **The finite-sum step of FS `thm:BogHamDiag`**: the mode decomposition plus
the per-pair Bogoliubov inequalities give the zero-point bound
`𝒦^Bog ≥ −½Σ_k[(𝒜_k−√(𝒜_k²−ℬ_k²)) + 2𝒞_k²/(𝒜_k+ℬ_k)]`. -/
theorem sum_pairGround_le (I : BogHamInterface ι) :
    -(1 / 2) * ((∑ k, bogZeroPoint (I.A k) (I.B k)) +
        (∑ k, bogKappaErr (I.A k) (I.B k) (I.Ccoef k))) ≤ I.Kbog := by
  rw [I.decomp, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  have h := I.pairGround k
  linarith

/-- **FS `eq:BogHamDiag` + `lem:BogIntegral`.**  Given B4's mode decomposition
and per-pair inequalities (`I`), the zero-point comparison `hzero` and the
`𝒞`-sum bound `hkappa`, the box Bogoliubov Hamiltonian is bounded below by

  `4π·lhySharp·ρ_z²a√(ρ_z a³)ℓ³ − ½·scal·latticeMeshErr − ½(Mass + Ezero + Ekappa)`,

where `scal = (2π)⁻³ℓ³ρ_z²a√(ρ_z a³)` is the FS prefactor of the zero-point term.
`hconst` is the numerical identity `½(2π)⁻³·lhyValue(8π) = 4π·lhySharp`
(`Work.BoseB6.lhyValue_eight_pi`). -/
theorem bogHamDiag_fs (I : BogHamInterface ι) {ρz a ℓ Mass Ezero Ekappa : ℝ} {n : ℕ}
    (hn : 1 ≤ n) (hρz : 0 < ρz) (ha : 0 < a) (hℓ : 0 < ℓ)
    (hconst : (1 / 2) * (((2 * Real.pi) ^ 3)⁻¹) * lhyValue (8 * Real.pi) =
      4 * Real.pi * lhySharp)
    (hmesh : |(meshD n) ^ 3 * latticeSum (8 * Real.pi) n + lhyValue (8 * Real.pi)| ≤
      latticeMeshErr (8 * Real.pi) n)
    (hzero : (∑ k, bogZeroPoint (I.A k) (I.B k)) ≤
      (((2 * Real.pi) ^ 3)⁻¹) * ℓ ^ 3 * (ρz ^ 2 * a * Real.sqrt (ρz * a ^ 3)) *
          ((meshD n) ^ 3 * latticeSum (8 * Real.pi) n)
        + Mass + Ezero)
    (hkappa : (∑ k, bogKappaErr (I.A k) (I.B k) (I.Ccoef k)) ≤ Ekappa) :
    4 * Real.pi * lhySharp * (ρz ^ 2 * a * Real.sqrt (ρz * a ^ 3)) * ℓ ^ 3
      - (1 / 2) * (((2 * Real.pi) ^ 3)⁻¹) * ℓ ^ 3 * (ρz ^ 2 * a * Real.sqrt (ρz * a ^ 3)) *
          latticeMeshErr (8 * Real.pi) n
      - (1 / 2) * (Mass + Ezero + Ekappa) ≤ I.Kbog := by
  set scal := (((2 * Real.pi) ^ 3)⁻¹) * ℓ ^ 3 * (ρz ^ 2 * a * Real.sqrt (ρz * a ^ 3)) with hscal
  have hscalnn : 0 ≤ scal := by
    rw [hscal]
    have h1 : (0 : ℝ) ≤ ((2 * Real.pi) ^ 3)⁻¹ := by positivity
    have h2 : (0 : ℝ) ≤ ℓ ^ 3 := by positivity
    have h3 : 0 ≤ ρz ^ 2 * a * Real.sqrt (ρz * a ^ 3) := by
      have h : 0 ≤ ρz * a ^ 3 := by positivity
      exact mul_nonneg (mul_nonneg (sq_nonneg ρz) ha.le) (Real.sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg h1 h2) h3
  have hL := abs_le.mp hmesh
  have h1 : scal * ((meshD n) ^ 3 * latticeSum (8 * Real.pi) n) ≤
      -scal * lhyValue (8 * Real.pi) + scal * latticeMeshErr (8 * Real.pi) n := by
    have h2 : (meshD n) ^ 3 * latticeSum (8 * Real.pi) n ≤
        -lhyValue (8 * Real.pi) + latticeMeshErr (8 * Real.pi) n := by linarith [hL.2]
    calc scal * ((meshD n) ^ 3 * latticeSum (8 * Real.pi) n)
        ≤ scal * (-lhyValue (8 * Real.pi) + latticeMeshErr (8 * Real.pi) n) :=
          mul_le_mul_of_nonneg_left h2 hscalnn
      _ = -scal * lhyValue (8 * Real.pi) + scal * latticeMeshErr (8 * Real.pi) n := by ring
  have hconst' : (1 / 2) * scal * lhyValue (8 * Real.pi) =
      4 * Real.pi * lhySharp * (ρz ^ 2 * a * Real.sqrt (ρz * a ^ 3)) * ℓ ^ 3 := by
    rw [hscal]
    have h := hconst
    linear_combination (ρz ^ 2 * a * Real.sqrt (ρz * a ^ 3) * ℓ ^ 3) * h
  have h2 := sum_pairGround_le I
  nlinarith [h1, h2, hzero, hkappa, hconst', hscalnn]

/-- **FS's `eq:BogHamDiag` + `lem:BogIntegral` display**, with the three error
terms instantiated at their FS values: `Mass = ℓ³ρ_z²ĝω(0)` (the `I₂` mass
term), `Ekappa = (ρ_z−μ)²ĝ(0)ℓ³(1+C(μa³)R²/a²)` (the `𝒞`-sum) and
`Ezero = 2C·ε·ρ_z²a√(ρ_z a³)ℓ³` (`ε = lhyEps a R ε_T K_ℓ s d μ`, the
`eq:LebesgueError-Total` error of `lem:BogIntegral`). -/
theorem bogHamDiag_fs_display (I : BogHamInterface ι) {ρz μ a ℓ R Kl s d εT C ĝω0 : ℝ}
    {n : ℕ} (hn : 1 ≤ n) (hρz : 0 < ρz) (ha : 0 < a) (hℓ : 0 < ℓ)
    (hconst : (1 / 2) * (((2 * Real.pi) ^ 3)⁻¹) * lhyValue (8 * Real.pi) =
      4 * Real.pi * lhySharp)
    (hmesh : |(meshD n) ^ 3 * latticeSum (8 * Real.pi) n + lhyValue (8 * Real.pi)| ≤
      latticeMeshErr (8 * Real.pi) n)
    (hzero : (∑ k, bogZeroPoint (I.A k) (I.B k)) ≤
      (((2 * Real.pi) ^ 3)⁻¹) * ℓ ^ 3 * (ρz ^ 2 * a * Real.sqrt (ρz * a ^ 3)) *
          ((meshD n) ^ 3 * latticeSum (8 * Real.pi) n)
        + ℓ ^ 3 * ρz ^ 2 * ĝω0 + 2 * C * lhyEps a R εT Kl s d μ * ρz ^ 2 * a *
            Real.sqrt (ρz * a ^ 3) * ℓ ^ 3)
    (hkappa : (∑ k, bogKappaErr (I.A k) (I.B k) (I.Ccoef k)) ≤
      (ρz - μ) ^ 2 * ĝω0 * ℓ ^ 3 * (1 + C * (μ * a ^ 3) * (R ^ 2 / a ^ 2))) :
    -(ĝω0 / 2) * ρz ^ 2 * ℓ ^ 3
      + 4 * Real.pi * lhySharp * (ρz ^ 2 * a * Real.sqrt (ρz * a ^ 3)) * ℓ ^ 3
      - C * lhyEps a R εT Kl s d μ * ρz ^ 2 * a * Real.sqrt (ρz * a ^ 3) * ℓ ^ 3
      - (1 / 2) * (((2 * Real.pi) ^ 3)⁻¹) * ℓ ^ 3 * (ρz ^ 2 * a * Real.sqrt (ρz * a ^ 3)) *
          latticeMeshErr (8 * Real.pi) n
      - (ρz - μ) ^ 2 * (ĝω0 / 2) * ℓ ^ 3 * (1 + C * (μ * a ^ 3) * (R ^ 2 / a ^ 2))
      ≤ I.Kbog := by
  have h := bogHamDiag_fs I hn hρz ha hℓ hconst hmesh hzero hkappa
  linarith

end Work.BoseB6
