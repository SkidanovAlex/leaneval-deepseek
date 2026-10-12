import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.BoseB6.BogIntegral
import Submission.Work.BoseB6.FsTauDiffLarge
import Submission.Work.BoseB6.FsTauUpperLarge
import Submission.Work.BoseB6.I1_small_ball_bound
import Submission.Work.BoseB6.Lattice
import Submission.Work.BoseB6.Sanity
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Node B6-est — FS §10 at FS's parameters: definitions

This chapter (`Work.BoseB6Est`) removes the three remaining hypotheses of node
B6 (`Submission/Work/BoseB6/`, FS §10) *at FS's own parameters*: the `I₁`
estimate of `lem:BogIntegral` (`eq:LebesgueError` + `eq:Logarithm`), the
zero-point lattice comparison `hzero` and the `𝒞`-sum bound `hkappa` of
`thm:BogHamDiag`.  It is the "estimation" half of node B6: B6 delivered the
algebra (Bogoliubov diagonalisation, the value `128/(15√π)` of the model
integral, the lattice Riemann estimate), this chapter delivers the estimates at
FS's `μ`-fixed, `ℓ = K_ℓ(μa)^{-1/2}`, particle-number-free parameters.

## FS's objects, in this chapter's vocabulary

FS's §10 quadratic Hamiltonian uses (`eq:BogHamPositive-1`)

  `𝒜(k) = τ(k) + ρ_z Ŵ₁(k)`,  `ℬ(k) = ρ_z Ŵ₁(k)`,
  `𝒞(k) = ℓ⁻³(ρ_z−μ)Ŵ₁(0) χ̂_Λ(k) z`,

with `τ` FS's truncated kinetic symbol and `Ŵ₁(0) = 8πa`.  In the scaled
variables `k = √(ρ_z a) t` (`lem:BogIntegral`) one has

  `𝒜 = ρ_z a (τ̃(t) + β(t))`,  `ℬ = ρ_z a β(t)`,  `β(t) = a⁻¹ Ŵ₁(√(ρ_z a) t)`,
  `τ̃ = fsTau ε_T c₁ c₂`,

with `β(0) = 8π`, `0 ≤ β ≤ B`, `|β(t) − 8π| ≤ η|t|` and `β = 0` beyond the
kernel's momentum cutoff `T`.  We bundle the kernel data in the structure
`FsKernel`, which is the *node-B6* interface `Work.BoseB6.ScaledKernel` with the
closeness hypothesis restricted to the support `[0,T]` (see
`FsKernel.ofScaled`): the quantitative estimates below need `β` close to `8π`
*on the mode range*, and the restriction to `[0,T]` is what makes the FS regime
(`ηT` small, `T` large) consistent with `β` vanishing beyond the cutoff.

The definitions here are used by every other module of the chapter:

* `fsA`, `fsB`, `fsC` — FS's `𝒜, ℬ, 𝒞` at a mode position;
* `zpSum`, `kappaSum` — FS's zero-point sum `Σ_k (𝒜_k − √(𝒜_k²−ℬ_k²))` and
  `𝒞`-sum `Σ_k 2𝒞_k²/(𝒜_k+ℬ_k)`;
* `fsI1` — the scaled Bogoliubov zero-point integral `I₁` of `lem:BogIntegral`;
* `fsI2` — the mass integral `∫ β(t)²/(2t²) dt` (`eq:I2-integral`);
* `fsG0`, `fsGω0` — FS's `ĝ(0)`, `ĝω(0)`;
* `fsMass` — the mass term `ℓ³ρ_z²ĝω(0)` of FS's `eq:BogIntegral` display.

## Conventions

* Positions of the mode lattice live in `Fin 3 → ℝ` and are measured with
  `Submission.BoseGases.eucNorm3` (the corpus's `ℝ³`-norm), exactly as in
  `Work.BoseBox.LatticeModel`; `∫` is Lebesgue measure on `Fin 3 → ℝ`.
* `χh t` denotes FS's `χ̂_Λ(√(ρ_z a) t)` (the localisation already in scaled
  variables), and `chiM` denotes `‖χ_Λ‖²_{L²} = ∫ χ_Λ²`.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators

namespace Work.BoseB6Est

open Submission.BoseGases

local notation "ℝ³" => Fin 3 → ℝ

/-- The Euclidean norm of `Work.BoseBox` on `Fin 3 → ℝ`. -/
abbrev nrm (t : ℝ³) : ℝ := Submission.BoseGases.eucNorm3 t

/-! ## 1. The kernel interface -/

/-- **FS's scaled Bogoliubov kernel** `β(t) = a⁻¹Ŵ₁(√(ρ_z a) t)` (node B6's
`Work.BoseB6.ScaledKernel`, with the closeness hypothesis required only on the
support `[0,T]`):

* `β ≥ 0` (`Ŵ₁ ≥ 0`), `β ≤ B` (FS `eq:WSestimate`);
* `|β(r) − 8π| ≤ η r` for `0 ≤ r ≤ T` (the χ-Taylor bound, interpolated);
* `β(r) = 0` for `r > T` (the kernel's momentum cutoff).

`β(0) = 8π` is a consequence (`FsKernel.beta_zero`). -/
structure FsKernel where
  /-- `β(t) = a⁻¹Ŵ₁(√(ρ_z a) t)`. -/
  β : ℝ → ℝ
  /-- a bound `β ≤ B`. -/
  B : ℝ
  /-- the closeness parameter of `|β(r) − 8π| ≤ η r`. -/
  η : ℝ
  /-- the momentum cutoff of the kernel, `β(r) = 0` for `r > T`. -/
  T : ℝ
  Bnn : 0 ≤ B
  ηnn : 0 ≤ η
  Tnn : 0 ≤ T
  /-- measurability of `β` (so that the Bochner integrals of `fsI1`, `fsI2` are
  the genuine ones; node B6's `ScaledKernel` omits this field). -/
  meas : Measurable β
  /-- `Ŵ₁ ≥ 0` gives `β ≥ 0`. -/
  nonneg : ∀ r, 0 ≤ β r
  /-- FS `eq:WSestimate`: `β ≤ B`. -/
  bound : ∀ r, β r ≤ B
  /-- `|Ŵ₁(k) − Ŵ₁(0)| ≤ Ca(kR)²` in scaled variables, on the mode range. -/
  close : ∀ r, 0 ≤ r → r ≤ T → |β r - 8 * Real.pi| ≤ η * r
  /-- the kernel's momentum cutoff. -/
  support : ∀ r, T < r → β r = 0

/-- Node B6's interface `Work.BoseB6.ScaledKernel` is an instance: its global
closeness hypothesis restricts to `[0,T]` (and measurability is supplied
separately). -/
def FsKernel.ofScaled (K : Work.BoseB6.ScaledKernel) (hmeas : Measurable K.β) : FsKernel where
  β := K.β
  B := K.B
  η := K.η
  T := K.T
  Bnn := K.Bnn
  ηnn := K.ηnn
  Tnn := K.Tnn
  meas := hmeas
  nonneg := K.nonneg
  bound := K.bound
  close := fun r hr _ => K.close r hr
  support := K.support

/-- **`β(0) = 8π`** (FS `Ŵ₁(0) = ∫Ŵ₁ = 8πa`). -/
theorem FsKernel.beta_zero (K : FsKernel) : K.β 0 = 8 * Real.pi := by
  have h := K.close 0 le_rfl K.Tnn
  simp only [mul_zero, abs_le] at h
  linarith [h.1, h.2]

lemma FsKernel.beta_nonneg (K : FsKernel) (r : ℝ) : 0 ≤ K.β r := K.nonneg r

/-- On the support, `β` is bounded below by `8π − ηT`. -/
lemma FsKernel.beta_ge (K : FsKernel) {r : ℝ} (h0 : 0 ≤ r) (hr : r ≤ K.T) :
    8 * Real.pi - K.η * K.T ≤ K.β r := by
  have h := (abs_le.mp (K.close r h0 hr)).1
  have : K.η * r ≤ K.η * K.T := mul_le_mul_of_nonneg_left hr K.ηnn
  linarith

/-! ## 1b. Elementary facts about FS's `τ̃` -/

/-- `fsTau ≥ 0` for `0 ≤ ε_T ≤ 1`. -/
lemma fsTau_nonneg {εT c1 c2 r : ℝ} (hε0 : 0 ≤ εT) (hε1 : εT ≤ 1)
    (ht : 0 ≤ r) : 0 ≤ Work.BoseB6.fsTau εT c1 c2 r := by
  have h0 : 0 ≤ 1 - εT := by linarith
  have h1 : 0 ≤ (1 - εT) * (max (|r| - c1) 0) ^ 2 := mul_nonneg h0 (sq_nonneg _)
  have h2 : 0 ≤ εT * (max (|r| - c2) 0) ^ 2 := mul_nonneg hε0 (sq_nonneg _)
  simp only [Work.BoseB6.fsTau]
  linarith

/-! ## 2. The mode family -/

/-- The position of the mode with multi-index `k` on the mesh-`δ` centred
lattice, `δ = meshD n = 2π/(n+1)`, `gridD n = (n+1)²` points per coordinate. -/
def modePos (n : ℕ) (k : Fin 3 → Fin (Work.BoseB6.gridD n)) : ℝ³ :=
  Work.BoseBox.latticeCenter (Work.BoseB6.meshD n) (Work.BoseB6.gridD n) k

/-- The mode index type of the mesh-`n` lattice. -/
abbrev modeIdx (n : ℕ) := Fin 3 → Fin (Work.BoseB6.gridD n)

/-- FS's `𝒜(k) = τ(k) + ρ_zŴ₁(k)` in scaled variables:
`𝒜 = ρ_z a (τ̃(t) + β(t))`. -/
def fsA (ρz a : ℝ) (K : FsKernel) (εT c1 c2 : ℝ) (t : ℝ³) : ℝ :=
  ρz * a * (Work.BoseB6.fsTau εT c1 c2 (nrm t) + K.β (nrm t))

/-- FS's `ℬ(k) = ρ_zŴ₁(k)` in scaled variables: `ℬ = ρ_z a β(t)`. -/
def fsB (ρz a : ℝ) (K : FsKernel) (t : ℝ³) : ℝ := ρz * a * K.β (nrm t)

/-- FS's `𝒞(k) = ℓ⁻³(ρ_z−μ)Ŵ₁(0)χ̂_Λ(k)z` in scaled variables:
`𝒞 = ℓ⁻³(ρ_z−μ)(8πa)χh(t)z`, with `χh t = χ̂_Λ(√(ρ_z a) t)`. -/
def fsC (ℓ ρz μ a z : ℝ) (χh : ℝ³ → ℝ) (t : ℝ³) : ℝ :=
  (ℓ ^ 3)⁻¹ * (ρz - μ) * (8 * Real.pi * a) * χh t * z

/-- The summand of FS's zero-point sum in scaled variables, `𝒜_k/ρ_z a`:
`(τ̃+β) − √((τ̃+β)²−β²)`. -/
def cleanBracket (K : FsKernel) (εT c1 c2 : ℝ) (t : ℝ³) : ℝ :=
  (Work.BoseB6.fsTau εT c1 c2 (nrm t) + K.β (nrm t))
    - Real.sqrt ((Work.BoseB6.fsTau εT c1 c2 (nrm t) + K.β (nrm t)) ^ 2
        - (K.β (nrm t)) ^ 2)

/-- FS's zero-point sum `Σ_k (𝒜_k − √(𝒜_k²−ℬ_k²))`. -/
def zpSum (n : ℕ) (ρz a : ℝ) (K : FsKernel) (εT c1 c2 : ℝ) : ℝ :=
  ∑ k : modeIdx n, Work.BoseB6.bogZeroPoint (fsA ρz a K εT c1 c2 (modePos n k))
    (fsB ρz a K (modePos n k))

/-- The pointwise reduction of FS's zero point: for `P = ρ_z a ≥ 0`, `τ, β ≥ 0`,
`bogZeroPoint (P(τ+β)) (Pβ) = P·((τ+β) − √((τ+β)²−β²))`. -/
lemma bogZeroPoint_fs {P τ b : ℝ} (hP : 0 ≤ P) (hτ : 0 ≤ τ) (hb : 0 ≤ b) :
    Work.BoseB6.bogZeroPoint (P * (τ + b)) (P * b)
      = P * ((τ + b) - Real.sqrt ((τ + b) ^ 2 - b ^ 2)) := by
  have hZ : 0 ≤ (τ + b) ^ 2 - b ^ 2 := by nlinarith
  have hsq : (P * (τ + b)) ^ 2 - (P * b) ^ 2 = P ^ 2 * ((τ + b) ^ 2 - b ^ 2) := by ring
  rw [Work.BoseB6.bogZeroPoint, hsq, Real.sqrt_mul (sq_nonneg P) _, Real.sqrt_sq hP]
  ring

/-- `zpSum` is `ρ_z a` times the unscaled bracket sum. -/
theorem zpSum_eq (n : ℕ) {ρz a : ℝ} (K : FsKernel) {εT c1 c2 : ℝ}
    (hP : 0 ≤ ρz * a) (hε0 : 0 ≤ εT) (hε1 : εT ≤ 1) :
    zpSum n ρz a K εT c1 c2
      = ρz * a * ∑ k : modeIdx n, cleanBracket K εT c1 c2 (modePos n k) := by
  rw [zpSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [cleanBracket, fsA, fsB]
  exact bogZeroPoint_fs hP (fsTau_nonneg hε0 hε1 (eucNorm3_nonneg _)) (K.nonneg _)

/-- FS's `𝒞`-sum `Σ_k 2𝒞_k²/(𝒜_k+ℬ_k)`. -/
def kappaSum (n : ℕ) (ρz a ℓ μ z : ℝ) (K : FsKernel) (εT c1 c2 : ℝ)
    (χh : ℝ³ → ℝ) : ℝ :=
  ∑ k : modeIdx n,
    Work.BoseB6.bogKappaErr (fsA ρz a K εT c1 c2 (modePos n k)) (fsB ρz a K (modePos n k))
      (fsC ℓ ρz μ a z χh (modePos n k))

/-- The unscaled sum `Σ_k χh(t_k)²` (FS's `Σ_k |χ̂_Λ(k)|²`, in scaled
variables), appearing in the `𝒞`-sum bound. -/
def chiSqSum (n : ℕ) (χh : ℝ³ → ℝ) : ℝ :=
  ∑ k : modeIdx n, (χh (modePos n k)) ^ 2

/-! ## 3. The scaled integrals of `lem:BogIntegral` -/

/-- **FS's `I₁` integrand** (`lem:BogIntegral`):
`α − √(α²−β²) − β²/(2t²)` with `α = τ̃ + β`. -/
def fsI1Integrand (K : FsKernel) (εT c1 c2 : ℝ) (t : ℝ³) : ℝ :=
  cleanBracket K εT c1 c2 t - (K.β (nrm t)) ^ 2 / (2 * (nrm t) ^ 2)

/-- **FS's `I₁`** (`lem:BogIntegral`), the regularised scaled Bogoliubov
zero-point integral `∫ [α − √(α²−β²) − β²/(2t²)] dt` in the variables
`k = √(ρ_z a) t`, whose model value (`β = 8π`, `τ̃ = t²`) is
`−lhyValue (8π) = −64π⁴·128/(15√π)`. -/
def fsI1 (K : FsKernel) (εT c1 c2 : ℝ) : ℝ :=
  ∫ t : ℝ³, fsI1Integrand K εT c1 c2 t

/-- **FS's mass integral** `∫ β(t)²/(2t²) dt` (`eq:I2-integral`), the second
summand of `eq:LHYIntegral1`. -/
def fsI2 (K : FsKernel) : ℝ :=
  ∫ t : ℝ³, (K.β (nrm t)) ^ 2 / (2 * (nrm t) ^ 2)

/-- FS's `ĝω(0) = (2π)⁻³∫Ŵ₁(k)²/(2k²)dk`, the mass coefficient of the
`eq:BogIntegral` display, in terms of the scaled kernel:
`ĝω(0) = (2π)⁻³ a²√(ρ_z a)·∫β(t)²/(2t²)dt`. -/
def fsGω0 (ρz a : ℝ) (K : FsKernel) : ℝ :=
  a ^ 2 * Real.sqrt (ρz * a) * fsI2 K / (2 * Real.pi) ^ 3

/-- **The mass term** `ℓ³ρ_z²ĝω(0)` of FS's `eq:BogIntegral` display (the
`I₂`-integral term, FS's second line). -/
def fsMass (ρz a ℓ : ℝ) (K : FsKernel) : ℝ := ℓ ^ 3 * ρz ^ 2 * fsGω0 ρz a K

/-- FS's `ĝ(0)`: the coefficient fixed by `𝒞(k) = ℓ⁻³(ρ_z−μ)Ŵ₁(0)χ̂_Λ(k)z`
together with `‖χ_Λ‖²_{L²} = chiM`, so that the `𝒞`-sum bound of
`thm:BogHamDiag` reads `(ρ_z−μ)²(ĝ(0)/2)ℓ³(1+…)`.  Concretely
`ĝ(0) = Ŵ₁(0) z² chiM /(ρ_z ℓ³)` with `Ŵ₁(0) = 8πa`. -/
def fsG0 (ρz a ℓ z chiM : ℝ) : ℝ := 8 * Real.pi * a * z ^ 2 * chiM / (ρz * ℓ ^ 3)

/-- The `𝒞`-sum error term of `thm:BogHamDiag`:
`(ρ_z−μ)²(ĝ(0)/2)ℓ³(1+δ)`. -/
def fsEkappa (ρz a ℓ μ z chiM δ : ℝ) : ℝ :=
  (ρz - μ) ^ 2 * (fsG0 ρz a ℓ z chiM / 2) * ℓ ^ 3 * (1 + δ)

/-- The explicit error of the lattice-Riemann comparison `zpRiem`
(the mesh-`δ` lattice sum of the clean bracket against its integral), as
produced by `Work.BoseB6Est.zpRiem`. -/
def zpRiemErr (n : ℕ) (K : FsKernel) (c2 : ℝ) : ℝ :=
  10 ^ 4 * (1 + K.B) ^ 2 * (1 + |Real.log (K.T / c2)|) + 10 ^ 4 * ((n : ℝ) + 1) ^ 3

/-! ## 4. Elementary API -/

/-- `fsTau ≤ r²` (`eq:tautilde-Est`'s first bound). -/
lemma fsTau_le_sq {εT c1 c2 r : ℝ} (hε0 : 0 ≤ εT) (hε1 : εT ≤ 1 / 2)
    (hc1 : 0 ≤ c1) (hc12 : c1 ≤ c2) (ht : 0 ≤ r) :
    Work.BoseB6.fsTau εT c1 c2 r ≤ r ^ 2 := by
  obtain ⟨-, hle, -⟩ := Work.BoseB6.fsTau_bounds (εT := εT) (c1 := c1) (c2 := c2)
    hε0 hε1 hc1 hc12 ht
  exact hle

/-- `fsTau > 0` above the cutoff `c₁` (for `0 ≤ ε_T < 1`). -/
lemma fsTau_pos {εT c1 c2 r : ℝ} (hε0 : 0 ≤ εT) (hε1 : εT < 1) (hc1 : 0 ≤ c1)
    (hcr : c1 < r) :
    0 < Work.BoseB6.fsTau εT c1 c2 r := by
  have hr0 : 0 < r := lt_of_le_of_lt hc1 hcr
  have h1 : 0 < max (|r| - c1) 0 := by
    rw [lt_max_iff]
    left
    rw [abs_of_pos hr0]
    linarith
  have hm : 0 < 1 - εT := by linarith
  have h2 : 0 ≤ εT * (max (|r| - c2) 0) ^ 2 := mul_nonneg hε0 (sq_nonneg _)
  have h3 : 0 < (1 - εT) * (max (|r| - c1) 0) ^ 2 := mul_pos hm (pow_pos h1 2)
  simp only [Work.BoseB6.fsTau]
  linarith

/-- `𝒜 > 0`: `ρ_z a (τ̃ + β) > 0` for `ρ_z a > 0`, `0 ≤ ε_T < 1`, `c₁ ≤ c₂ < T`
and `ηT < 8π`.  (Either `r ≤ T`, where `β ≥ 8π − ηT > 0`, or `r > T > c₂`, where
`τ̃ > 0`.) -/
lemma fsA_pos {ρz a : ℝ} (K : FsKernel) (hρa : 0 < ρz * a)
    {εT c1 c2 : ℝ} (hε0 : 0 ≤ εT) (hε1 : εT < 1) (hc1 : 0 ≤ c1) (hc12 : c1 ≤ c2)
    (hηT : K.η * K.T < 8 * Real.pi) (hTc : c1 < K.T) (t : ℝ³) :
    0 < fsA ρz a K εT c1 c2 t := by
  have hr : 0 ≤ nrm t := eucNorm3_nonneg t
  have key : 0 < Work.BoseB6.fsTau εT c1 c2 (nrm t) + K.β (nrm t) := by
    rcases lt_or_ge (nrm t) K.T with hT | hT
    · have h := (abs_le.mp (K.close _ hr hT.le)).1
      have h2 : K.η * nrm t < 8 * Real.pi :=
        lt_of_le_of_lt (mul_le_mul_of_nonneg_left hT.le K.ηnn) hηT
      have h3 : 0 ≤ Work.BoseB6.fsTau εT c1 c2 (nrm t) := fsTau_nonneg hε0 hε1.le hr
      have h4 : 0 ≤ K.β (nrm t) := K.nonneg _
      linarith
    · have hpos : 0 < Work.BoseB6.fsTau εT c1 c2 (nrm t) :=
        fsTau_pos hε0 hε1 hc1 (lt_of_lt_of_le hTc hT)
      linarith [K.nonneg (nrm t)]
  exact mul_pos hρa key

/-- `ℬ ≥ 0`. -/
lemma fsB_nonneg {ρz a : ℝ} (K : FsKernel) (hρz : 0 ≤ ρz) (ha : 0 ≤ a) (t : ℝ³) :
    0 ≤ fsB ρz a K t := mul_nonneg (mul_nonneg hρz ha) (K.nonneg _)

/-- `|ℬ| ≤ 𝒜` (needed for the pair Bogoliubov inequality). -/
lemma fsB_abs_le_fsA {ρz a : ℝ} (K : FsKernel) {εT c1 c2 : ℝ} (hε0 : 0 ≤ εT)
    (hε1 : εT ≤ 1) (hρz : 0 ≤ ρz) (ha : 0 ≤ a) (t : ℝ³) :
    |fsB ρz a K t| ≤ fsA ρz a K εT c1 c2 t := by
  have hr : 0 ≤ nrm t := eucNorm3_nonneg t
  have hτ : 0 ≤ Work.BoseB6.fsTau εT c1 c2 (nrm t) := fsTau_nonneg hε0 hε1 hr
  have hb : 0 ≤ K.β (nrm t) := K.nonneg _
  have hρa : 0 ≤ ρz * a := mul_nonneg hρz ha
  rw [fsB, fsA, abs_of_nonneg (mul_nonneg hρa hb)]
  exact mul_le_mul_of_nonneg_left (by linarith) hρa

/-- `𝒜 + ℬ = ρ_z a (τ̃ + 2β)`. -/
lemma fsA_add_fsB (ρz a : ℝ) (K : FsKernel) (εT c1 c2 : ℝ) (t : ℝ³) :
    fsA ρz a K εT c1 c2 t + fsB ρz a K t
      = ρz * a * (Work.BoseB6.fsTau εT c1 c2 (nrm t) + 2 * K.β (nrm t)) := by
  rw [fsA, fsB]; ring

end Work.BoseB6Est
