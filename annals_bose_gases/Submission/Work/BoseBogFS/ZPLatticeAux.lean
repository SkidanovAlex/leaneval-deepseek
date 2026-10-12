import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBogFS.ZPLatticeDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.ZPLatticeAux` — the honest kinematic data of `ZPLatticeRow`

The definitions and the elementary pointwise layer used by both the target file
`Submission/Work/BoseBogFS/ZPLatticeRowHolds.lean` and the two analytic rows
`ZPMassLatticeRow` / `ZPCleanDeficitRow` delegated from it.  Nothing here is
`sorry`-tainted.

The target: the `N`-free zero-point row `Work.BoseBogFS.ZPLatticeRow` (FS
`lem:BogIntegral`, `Papers/fournais_solovej/final_v2.tex`, on the full lattice
`(2π/ℓ)ℤ³` with no cut-off and no cube, in finite-set form), i.e. the theorem
`Work.BoseBogFS.ZPLatticeRowHolds` below.

## The design (FS's own split)

With `τ = tauSm` at FS's parameters, `c = ρ·Ŵ₁(k)` and the dual-lattice momenta
`k_n = ℓ⁻¹ • vec n = 2πn/ℓ`, the summand of `ZPLatticeRow` is `½·𝒵(τ+c, c)` where
`𝒵(𝒜,ℬ) = 𝒜 − √(𝒜²−ℬ²)`.  FS's `eq:LHYIntegral1` splits it as

  `½·𝒵(τ+c,c) = ½·[𝒵(τ+c,c) − c²/(2‖k‖²)] + c²/(4‖k‖²)`,

a *clean* part (= the `I₁` integrand of `eq:SplitIntegrals`, whose integral in the
scaled variables is `−lhyValue(8π) + ε` by `eq:LebesgueError` + `eq:Logarithm`) plus
a *mass* part `c²/(4‖k‖²)` whose lattice sum is a Riemann sum of
`(2π)⁻³ℓ³∫Ŵ₁(p)²/(4‖p‖²)dp`, which by FS's `eq:I2-integral` differs from
`½ℓ³ρ²Ŵ₁ω(0)` by a relative `O((R/ℓ)²)`.

The two analytic inputs of the reduction (Section 3) are therefore

* `ZPMassLatticeRow` — the sharp lattice-Coulomb comparison
  `Σ_{n≠0}Ŵ(k_n)²/(4‖k_n‖²) ≤ (2π)⁻³ℓ³∫Ŵ²/(4‖p‖²) + C·ℓ²(∫W)²`.
  The corpus's proved `Work.BoseRowsFS.honest_lattice_W1sq_le_uniform` carries the
  constant `10⁸(1+R)⁵` and loses a further factor `ℓ/R`; that does *not* fit the
  `errBracket` budget, which needs the mass sum compared to `½ℓ³ρ²Ŵ₁ω(0)` to a
  *relative* accuracy `O(R/ℓ) = O((R/a)X^{163})` against a budget of
  `O((R/a)X^{161.7})`.  Thus the sharp row is exactly the natural Riemann error;
  it is the design's D5 item `latticeCoulomb_approx`.
* `ZPCleanDeficitRow` — FS's `I₁ ≤ −lhyValue(8π) + ε` at the honest datum and on
  the lattice.  The scaled mesh is `2π/K_ℓ = 2πX^{3/2}`, so the discretisation error
  is `O(X^{3/2})·LHY`, well inside the budget `errBracket ⊇ X^{1/5}·LHY`.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseBogFS

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseBoxFix Work.BoseFixR

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The honest kinematic data -/

/-- The honest truncated kinetic symbol `τ` at FS's parameters, as a function of the
physical momentum `k`. -/
def tauAt (v : ℝ³ → ℝ) (μ : ℝ) (k : ℝ³) : ℝ :=
  Work.BoseBoxFock.tauSm (paramsAt μ (a v)).eT (paramsAt μ (a v)).s (paramsAt μ (a v)).d (ell v μ) k

/-- The honest one-body kernel `W₁ = W(1−ω)` at the box scale `ℓ(μ)`. -/
def W1At (v : ℝ³ → ℝ) (h : ScatSol v) (μ : ℝ) : ℝ³ → ℝ := W1fun v h (ell v μ)

/-- The honest mass kernel `W₁ω`. -/
def W1ωAt (v : ℝ³ → ℝ) (h : ScatSol v) (μ : ℝ) : ℝ³ → ℝ := W1omegaFun v h (ell v μ)

/-- The honest momentum of a lattice label: `k_n = ℓ⁻¹ • vec n = 2πn/ℓ`. -/
def kAt (v : ℝ³ → ℝ) (μ : ℝ) (n : Fin 3 → ℤ) : ℝ³ := (ell v μ)⁻¹ • Work.BoseB4.vec n

/-- The pairing coefficient `c = ρ·Ŵ₁(k)` at `(μ,ρ)`. -/
def cAt (v : ℝ³ → ℝ) (h : ScatSol v) (ρ μ : ℝ) (k : ℝ³) : ℝ :=
  ρ * chat (W1At v h μ) k

/-- **The zero-point summand** `½·𝒵(τ+c, c)` at the label `n`. -/
def zpTerm (v : ℝ³ → ℝ) (h : ScatSol v) (ρ μ : ℝ) (n : Fin 3 → ℤ) : ℝ :=
  (1 / 2) * Work.BoseB6.bogZeroPoint (tauAt v μ (kAt v μ n) + cAt v h ρ μ (kAt v μ n))
    (cAt v h ρ μ (kAt v μ n))

/-- **FS's clean part** (`eq:LHYIntegral1`, the `I₁` integrand):
`𝒵(τ+c,c) − c²/(2‖k‖²)`. -/
def cleanTerm (v : ℝ³ → ℝ) (h : ScatSol v) (ρ μ : ℝ) (n : Fin 3 → ℤ) : ℝ :=
  Work.BoseB6.bogZeroPoint (tauAt v μ (kAt v μ n) + cAt v h ρ μ (kAt v μ n))
      (cAt v h ρ μ (kAt v μ n))
    - (cAt v h ρ μ (kAt v μ n)) ^ 2 / (2 * ‖kAt v μ n‖ ^ 2)

/-- **FS's mass part** `c²/(4‖k‖²)`. -/
def massTerm (v : ℝ³ → ℝ) (h : ScatSol v) (ρ μ : ℝ) (n : Fin 3 → ℤ) : ℝ :=
  (cAt v h ρ μ (kAt v μ n)) ^ 2 / (4 * ‖kAt v μ n‖ ^ 2)

/-! ## 2. The elementary pointwise layer -/

/-- `tauAt` is nonnegative at FS's parameters (`0 ≤ e_T ≤ 1` and the profile
lower bound `(r−2)₊² ≤ τ̃(r)`). -/
lemma tauAt_nonneg {v : ℝ³ → ℝ} {μ : ℝ}
    (heT0 : 0 ≤ (paramsAt μ (a v)).eT) (heT1 : (paramsAt μ (a v)).eT ≤ 1) (k : ℝ³) :
    0 ≤ tauAt v μ k := by
  rw [tauAt, Work.BoseBoxFock.tauSm]
  have h1 : 0 ≤ Work.BoseBoxFock.tauProf
      (‖k‖ / (2 * (paramsAt μ (a v)).s * ell v μ)⁻¹) :=
    Work.BoseBoxFock.tauProf_nonneg _
  have h2 : 0 ≤ Work.BoseBoxFock.tauProf
      (‖k‖ / (2 * (paramsAt μ (a v)).d * (paramsAt μ (a v)).s * ell v μ)⁻¹) :=
    Work.BoseBoxFock.tauProf_nonneg _
  have h3 : 0 ≤ (1 - (paramsAt μ (a v)).eT) := by linarith
  have h4 : 0 ≤ ((2 * (paramsAt μ (a v)).s * ell v μ)⁻¹) ^ 2 := sq_nonneg _
  have h5 : 0 ≤ ((2 * (paramsAt μ (a v)).d * (paramsAt μ (a v)).s * ell v μ)⁻¹) ^ 2 :=
    sq_nonneg _
  have h6 : 0 ≤ (1 - (paramsAt μ (a v)).eT)
      * ((2 * (paramsAt μ (a v)).s * ell v μ)⁻¹) ^ 2
      * Work.BoseBoxFock.tauProf (‖k‖ / (2 * (paramsAt μ (a v)).s * ell v μ)⁻¹) :=
    mul_nonneg (mul_nonneg h3 h4) h1
  have h7 : 0 ≤ (paramsAt μ (a v)).eT
      * ((2 * (paramsAt μ (a v)).d * (paramsAt μ (a v)).s * ell v μ)⁻¹) ^ 2
      * Work.BoseBoxFock.tauProf
          (‖k‖ / (2 * (paramsAt μ (a v)).d * (paramsAt μ (a v)).s * ell v μ)⁻¹) :=
    mul_nonneg (mul_nonneg heT0 h5) h2
  linarith

/-- **`τ(k) ≤ ‖k‖²`**: the truncated symbol is dominated by the free kinetic energy
(the profile bound `τ̃(r) ≤ (r−1)₊²` of the pin, `Work.BoseBoxFock.bf3a_fibre`). -/
lemma tauAt_le_sq {v : ℝ³ → ℝ} {μ : ℝ}
    (hs : 0 < (paramsAt μ (a v)).s) (hd : 0 < (paramsAt μ (a v)).d)
    (heT0 : 0 ≤ (paramsAt μ (a v)).eT) (heT1 : (paramsAt μ (a v)).eT ≤ 1)
    (hℓ : 0 < ell v μ) (k : ℝ³) : tauAt v μ k ≤ ‖k‖ ^ 2 := by
  rw [tauAt, Work.BoseBoxFock.tauSm]
  set s := (paramsAt μ (a v)).s
  set d := (paramsAt μ (a v)).d
  set eT := (paramsAt μ (a v)).eT
  set L := ell v μ
  have hc1 : 0 < (2 * s * L)⁻¹ := by positivity
  have hc2 : 0 < (2 * d * s * L)⁻¹ := by positivity
  have h1 := Work.BoseBoxFock.mul_tauProf_le_fsKinCoeff (c := (2 * s * L)⁻¹) hc1
    (r := ‖k‖)
  have h2 := Work.BoseBoxFock.mul_tauProf_le_fsKinCoeff (c := (2 * d * s * L)⁻¹) hc2
    (r := ‖k‖)
  have h3 : Submission.BoseGases.fsKinCoeff (2 * s * L)⁻¹ ‖k‖ ≤ ‖k‖ ^ 2 := by
    rw [Submission.BoseGases.fsKinCoeff]
    have hb : max (‖k‖ - (2 * s * L)⁻¹) 0 ≤ ‖k‖ :=
      max_le (by linarith) (norm_nonneg k)
    have h0 : 0 ≤ max (‖k‖ - (2 * s * L)⁻¹) 0 := le_max_right _ _
    nlinarith [hb, h0, norm_nonneg k]
  have h4 : Submission.BoseGases.fsKinCoeff (2 * d * s * L)⁻¹ ‖k‖ ≤ ‖k‖ ^ 2 := by
    rw [Submission.BoseGases.fsKinCoeff]
    have hb : max (‖k‖ - (2 * d * s * L)⁻¹) 0 ≤ ‖k‖ :=
      max_le (by linarith) (norm_nonneg k)
    have h0 : 0 ≤ max (‖k‖ - (2 * d * s * L)⁻¹) 0 := le_max_right _ _
    nlinarith [hb, h0, norm_nonneg k]
  have h5 : (1 - eT) * ((2 * s * L)⁻¹) ^ 2 * Work.BoseBoxFock.tauProf (‖k‖ / (2 * s * L)⁻¹)
      ≤ (1 - eT) * ‖k‖ ^ 2 := by
    have hnn : 0 ≤ (1 - eT) := by linarith
    have h := mul_le_mul_of_nonneg_left (le_trans h1 h3) hnn
    calc (1 - eT) * ((2 * s * L)⁻¹) ^ 2 * Work.BoseBoxFock.tauProf (‖k‖ / (2 * s * L)⁻¹)
        = (1 - eT) * (((2 * s * L)⁻¹) ^ 2
            * Work.BoseBoxFock.tauProf (‖k‖ / (2 * s * L)⁻¹)) := by ring
      _ ≤ (1 - eT) * ‖k‖ ^ 2 := h
  have h6 : eT * ((2 * d * s * L)⁻¹) ^ 2
        * Work.BoseBoxFock.tauProf (‖k‖ / (2 * d * s * L)⁻¹)
      ≤ eT * ‖k‖ ^ 2 := by
    have h := mul_le_mul_of_nonneg_left (le_trans h2 h4) heT0
    calc eT * ((2 * d * s * L)⁻¹) ^ 2
          * Work.BoseBoxFock.tauProf (‖k‖ / (2 * d * s * L)⁻¹)
        = eT * (((2 * d * s * L)⁻¹) ^ 2
            * Work.BoseBoxFock.tauProf (‖k‖ / (2 * d * s * L)⁻¹)) := by ring
      _ ≤ eT * ‖k‖ ^ 2 := h
  calc (1 - eT) * ((2 * s * L)⁻¹) ^ 2 * Work.BoseBoxFock.tauProf (‖k‖ / (2 * s * L)⁻¹)
        + eT * ((2 * d * s * L)⁻¹) ^ 2
          * Work.BoseBoxFock.tauProf (‖k‖ / (2 * d * s * L)⁻¹)
      ≤ (1 - eT) * ‖k‖ ^ 2 + eT * ‖k‖ ^ 2 := add_le_add h5 h6
    _ = ‖k‖ ^ 2 := by ring

/-- **FS's split of the summand** (`eq:LHYIntegral1`): the zero-point summand is
one half of the clean part plus the mass part. -/
lemma zpTerm_eq (v : ℝ³ → ℝ) (h : ScatSol v) (ρ μ : ℝ) (n : Fin 3 → ℤ) :
    zpTerm v h ρ μ n = (1 / 2) * cleanTerm v h ρ μ n + massTerm v h ρ μ n := by
  rw [zpTerm, cleanTerm, massTerm, Work.BoseB6.bogZeroPoint]
  have hsq : (tauAt v μ (kAt v μ n) + cAt v h ρ μ (kAt v μ n)) ^ 2
      - (cAt v h ρ μ (kAt v μ n)) ^ 2
      = tauAt v μ (kAt v μ n) ^ 2
        + 2 * tauAt v μ (kAt v μ n) * cAt v h ρ μ (kAt v μ n) := by ring
  rw [hsq]; ring

/-- The summand is nonnegative (`0 ≤ τ` and `0 ≤ c`). -/
lemma zpTerm_nonneg {v : ℝ³ → ℝ} {h : ScatSol v} {ρ μ : ℝ} {n : Fin 3 → ℤ}
    (hτ : 0 ≤ tauAt v μ (kAt v μ n)) (hc : 0 ≤ cAt v h ρ μ (kAt v μ n)) :
    0 ≤ zpTerm v h ρ μ n := by
  have hA : 0 ≤ tauAt v μ (kAt v μ n) + cAt v h ρ μ (kAt v μ n) := by linarith
  have hB : |cAt v h ρ μ (kAt v μ n)| ≤ tauAt v μ (kAt v μ n) + cAt v h ρ μ (kAt v μ n) := by
    rw [abs_of_nonneg hc]; linarith
  have h := Work.BoseB6.bogZeroPoint_nonneg hA hB
  rw [zpTerm]
  linarith

/-- **The summand is nonnegative when `2|c| ≤ τ`.**  This is the far-field half of the
positivity of the honest zero point: with `t = τ`, `c = ρŴ₁(k_n)`,
`(t+c)² - c² = t² + 2tc ≥ t(t - 2|c|) ≥ 0` and `t + c ≥ t - |c| ≥ |c|`. -/
lemma zpTerm_nonneg_of_two_abs_le {v : ℝ³ → ℝ} {h : ScatSol v} {ρ μ : ℝ} {n : Fin 3 → ℤ}
    (hτ : 0 ≤ tauAt v μ (kAt v μ n))
    (h2c : 2 * |cAt v h ρ μ (kAt v μ n)| ≤ tauAt v μ (kAt v μ n)) :
    0 ≤ zpTerm v h ρ μ n := by
  set t := tauAt v μ (kAt v μ n) with ht
  set c := cAt v h ρ μ (kAt v μ n) with hc
  have hA0 : 0 ≤ t + c := by
    have := neg_abs_le c
    linarith
  have hB : |c| ≤ t + c := by
    rw [abs_le]
    constructor
    · have := neg_abs_le c; linarith
    · have := le_abs_self c; linarith
  have hz := Work.BoseB6.bogZeroPoint_nonneg hA0 hB
  rw [zpTerm]
  have : (0 : ℝ) ≤ (1 / 2) * Work.BoseB6.bogZeroPoint (t + c) c := by linarith
  simpa only [ht, hc] using this

/-- **Monotonicity of the partial sums** when every summand is nonnegative: enlarging the
finite set can only increase the sum.  This is the step that lets the two analytic rows
(stated for sets containing the low-momentum ball) be applied to an arbitrary finite `S`. -/
lemma finset_sum_le_of_subset_of_nonneg {ι : Type*} [DecidableEq ι] {f : ι → ℝ}
    {S T : Finset ι} (hST : S ⊆ T) (h : ∀ i ∈ T, 0 ≤ f i) :
    ∑ i ∈ S, f i ≤ ∑ i ∈ T, f i := by
  have hsplit : ∑ i ∈ T, f i = ∑ i ∈ S, f i + ∑ i ∈ T \ S, f i := by
    rw [← Finset.sum_sdiff hST]
    ring
  have htail : 0 ≤ ∑ i ∈ T \ S, f i :=
    Finset.sum_nonneg (fun i hi => h i (Finset.mem_sdiff.mp hi).1)
  linarith

/-! ## 3. The enlargement set of the assembly -/

/-- The set of lattice labels whose momentum lies in the closed ball of radius `Lam`: the set
that the deficit row `ZPCleanDeficitRow` requires `S` to contain. -/
def zBall (v : ℝ³ → ℝ) (μ Lam : ℝ) : Set (Fin 3 → ℤ) := {n | n ≠ 0 ∧ ‖kAt v μ n‖ ≤ Lam}

/-- Membership in `zBall` unfolded. -/
@[simp] lemma mem_zBall {v : ℝ³ → ℝ} {μ Lam : ℝ} {n : Fin 3 → ℤ} :
    n ∈ zBall v μ Lam ↔ n ≠ 0 ∧ ‖kAt v μ n‖ ≤ Lam := Iff.rfl

/-- The `zBall` condition in the exact shape of the deficit row's hypothesis. -/
lemma zBall_imp_of_subset {v : ℝ³ → ℝ} {μ Lam : ℝ} {S : Finset (Fin 3 → ℤ)}
    (h : ∀ n : Fin 3 → ℤ, n ≠ 0 → ‖kAt v μ n‖ ≤ Lam → n ∈ S) :
    ∀ n ∈ zBall v μ Lam, n ∈ S := by
  intro n hn
  exact h n hn.1 hn.2

/-! ## 4. The explicit diluteness thresholds of the mass step

The mass step (`ZPMassStep`) compares the sharp row's absolute error
`C'·ρ²ℓ²(∫W₁)²` with the budget `C·errBracket = C·μ²aℓ³√(dil)·errSlot`,
`errSlot ≥ dil^{1/1615}`.  With `ℓ = a·(μa³)^{−163/323}`, the ratio is
`K·(dil)^{3/646}` against `C·(dil)^{1/1615}` because `(ℓ√(dil))⁻¹ = a⁻¹(dil)^{3/646}`.  Since
`3/646 = 1/1615 + 13/3230`, a *single* explicit threshold `dil ≤ (C/K)^{3230/13}` suffices. -/

/-- **The threshold lemma for the `X^{−3/646}`-type ratio.**  If `0 < t ≤ (c/K)^{3230/13}` then
`K·t^{3/646} ≤ c·t^{1/1615}`.  (`3/646 = 1/1615 + 13/3230`, so the exponent gap is `13/3230`.) -/
lemma rpow_three_646_threshold {c K t : ℝ} (hK : 0 < K) (hc : 0 ≤ c) (ht : 0 < t)
    (h : t ≤ (c / K) ^ (3230 / 13 : ℝ)) :
    K * t ^ (3 / 646 : ℝ) ≤ c * t ^ (1 / 1615 : ℝ) := by
  have hbase : 0 ≤ c / K := div_nonneg hc hK.le
  have h1 : t ^ (13 / 3230 : ℝ) ≤ c / K := by
    refine le_trans (Real.rpow_le_rpow ht.le h (by norm_num)) ?_
    rw [← Real.rpow_mul hbase]
    norm_num
  have hsplit : t ^ (3 / 646 : ℝ) = t ^ (1 / 1615 : ℝ) * t ^ (13 / 3230 : ℝ) := by
    rw [← Real.rpow_add ht]
    norm_num
  have hpos : 0 ≤ t ^ (1 / 1615 : ℝ) := Real.rpow_nonneg ht.le _
  calc K * t ^ (3 / 646 : ℝ)
      = t ^ (1 / 1615 : ℝ) * (K * t ^ (13 / 3230 : ℝ)) := by rw [hsplit]; ring
    _ ≤ t ^ (1 / 1615 : ℝ) * (K * (c / K)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hK.le) hpos
    _ = c * t ^ (1 / 1615 : ℝ) := by field_simp

/-- **The arithmetic core of the honest mass step.**  With `t := μa³`, `ℓ = a·t^{−163/323}`,
`ρ² ≤ 4μ²`, `M = ∫W₁ ≤ 16πa` and the explicit threshold `t^{13/3230} ≤ C₁/(1024π²C')`, the mass
row's absolute error `C'·ρ²ℓ²M²` is dominated by the `t^{1/1615}` slot of `errBracket`:

`C'·ρ²ℓ²M² ≤ C₁·μ²aℓ³√t·t^{1/1615}`.

This is the whole arithmetic content of `ZPMassStep`: the sharp row's error and the `E₁`–`E₂`
discrepancy both have the shape `C'ρ²ℓ²(∫W₁)²`, so their constants simply add.  The exponent
identity used is `326/323 = 489/323 − 1/2 − 1/1615 − 13/3230`. -/
lemma massStep_arith {μ a ρ ℓ M C₁ C' : ℝ} (hC' : 0 ≤ C') (hC₁ : 0 ≤ C₁)
    (hμ : 0 < μ) (ha : 0 < a) (hρ : 0 ≤ ρ) (hρ2 : ρ ^ 2 ≤ 4 * μ ^ 2)
    (hM0 : 0 ≤ M) (hM1 : M ≤ 16 * Real.pi * a)
    (hℓ : ℓ = a * (μ * a ^ 3) ^ (-(163 / 323) : ℝ))
    (hthr : (μ * a ^ 3) ^ (13 / 3230 : ℝ) ≤ C₁ / (1024 * Real.pi ^ 2 * C')) :
    C' * ρ ^ 2 * ℓ ^ 2 * M ^ 2
      ≤ C₁ * (μ ^ 2 * a * ℓ ^ 3 * Real.sqrt (μ * a ^ 3) * (μ * a ^ 3) ^ (1 / 1615 : ℝ)) := by
  have ht : 0 < μ * a ^ 3 := by positivity
  have h16 : (0 : ℝ) ≤ 16 * Real.pi * a := by positivity
  have hM2 : M ^ 2 ≤ (16 * Real.pi * a) ^ 2 := pow_le_pow_left₀ hM0 hM1 2
  have hρM : ρ ^ 2 * M ^ 2 ≤ 4 * μ ^ 2 * (16 * Real.pi * a) ^ 2 :=
    mul_le_mul hρ2 hM2 (sq_nonneg M) (by positivity)
  have hℓ2 : ℓ ^ 2 = a ^ 2 * (μ * a ^ 3) ^ (-(326 / 323) : ℝ) := by
    rw [hℓ, mul_pow, ← Real.rpow_natCast ((μ * a ^ 3) ^ (-(163 / 323) : ℝ)) 2,
      ← Real.rpow_mul ht.le]
    norm_num
  have hℓ3 : ℓ ^ 3 = a ^ 3 * (μ * a ^ 3) ^ (-(489 / 323) : ℝ) := by
    rw [hℓ, mul_pow, ← Real.rpow_natCast ((μ * a ^ 3) ^ (-(163 / 323) : ℝ)) 3,
      ← Real.rpow_mul ht.le]
    norm_num
  have hsqrt : Real.sqrt (μ * a ^ 3) = (μ * a ^ 3) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
  have hpow1 : (μ * a ^ 3) ^ (-(326 / 323) : ℝ)
      = (μ * a ^ 3) ^ (-(489 / 323) : ℝ) * (μ * a ^ 3) ^ (1 / 2 : ℝ)
        * (μ * a ^ 3) ^ (1 / 1615 : ℝ) * (μ * a ^ 3) ^ (13 / 3230 : ℝ) := by
    rw [← Real.rpow_add ht, ← Real.rpow_add ht, ← Real.rpow_add ht]
    congr 1
    norm_num
  have hnonneg : (0 : ℝ) ≤ μ ^ 2 * a ^ 4 * ((μ * a ^ 3) ^ (-(489 / 323) : ℝ)
      * (μ * a ^ 3) ^ (1 / 2 : ℝ) * (μ * a ^ 3) ^ (1 / 1615 : ℝ)) := by positivity
  calc C' * ρ ^ 2 * ℓ ^ 2 * M ^ 2
      = C' * ℓ ^ 2 * (ρ ^ 2 * M ^ 2) := by ring
    _ ≤ C' * ℓ ^ 2 * (4 * μ ^ 2 * (16 * Real.pi * a) ^ 2) :=
        mul_le_mul_of_nonneg_left hρM (by positivity)
    _ = 1024 * Real.pi ^ 2 * C' * μ ^ 2 * a ^ 2 * ℓ ^ 2 := by ring
    _ = 1024 * Real.pi ^ 2 * C' * μ ^ 2 * a ^ 4 * (μ * a ^ 3) ^ (-(326 / 323) : ℝ) := by
        rw [hℓ2]; ring
    _ = (1024 * Real.pi ^ 2 * C' * (μ * a ^ 3) ^ (13 / 3230 : ℝ))
          * (μ ^ 2 * a ^ 4 * ((μ * a ^ 3) ^ (-(489 / 323) : ℝ)
              * (μ * a ^ 3) ^ (1 / 2 : ℝ) * (μ * a ^ 3) ^ (1 / 1615 : ℝ))) := by
        rw [hpow1]; ring
    _ ≤ C₁ * (μ ^ 2 * a ^ 4 * ((μ * a ^ 3) ^ (-(489 / 323) : ℝ)
            * (μ * a ^ 3) ^ (1 / 2 : ℝ) * (μ * a ^ 3) ^ (1 / 1615 : ℝ))) := by
        rcases eq_or_lt_of_le hC' with h0 | hpos
        · rw [← h0]
          simp only [mul_zero, zero_mul]
          exact mul_nonneg hC₁ hnonneg
        · have hden : 0 < 1024 * Real.pi ^ 2 * C' := by positivity
          have hkey : 1024 * Real.pi ^ 2 * C' * (μ * a ^ 3) ^ (13 / 3230 : ℝ) ≤ C₁ := by
            have h := (le_div_iff₀ hden).mp hthr
            linarith [h]
          exact mul_le_mul_of_nonneg_right hkey hnonneg
    _ = C₁ * (μ ^ 2 * a * ℓ ^ 3 * Real.sqrt (μ * a ^ 3) * (μ * a ^ 3) ^ (1 / 1615 : ℝ)) := by
        rw [hℓ3, hsqrt]; ring

/-- **`massStep_arith` with a denominator that is always positive.**  The threshold hypothesis is
`t^{13/3230} ≤ C₁/(1024π²C' + 1)`, which (i) never divides by zero and (ii) is automatic from
`t ≤ 1` when `C₁ = 1024π²C' + 1`.  The degenerate case `C' = 0` is handled inside. -/
lemma massStep_arith' {μ a ρ ℓ M C₁ C' : ℝ} (hC' : 0 ≤ C') (hC₁ : 0 ≤ C₁)
    (hμ : 0 < μ) (ha : 0 < a) (hℓ0 : 0 ≤ ℓ) (hρ : 0 ≤ ρ) (hρ2 : ρ ^ 2 ≤ 4 * μ ^ 2)
    (hM0 : 0 ≤ M) (hM1 : M ≤ 16 * Real.pi * a)
    (hℓ : ℓ = a * (μ * a ^ 3) ^ (-(163 / 323) : ℝ))
    (hthr : (μ * a ^ 3) ^ (13 / 3230 : ℝ) ≤ C₁ / (1024 * Real.pi ^ 2 * C' + 1)) :
    C' * ρ ^ 2 * ℓ ^ 2 * M ^ 2
      ≤ C₁ * (μ ^ 2 * a * ℓ ^ 3 * Real.sqrt (μ * a ^ 3) * (μ * a ^ 3) ^ (1 / 1615 : ℝ)) := by
  rcases eq_or_lt_of_le hC' with h0 | hpos
  · rw [← h0]
    simp only [zero_mul]
    exact mul_nonneg hC₁ (by positivity)
  · refine massStep_arith hC' hC₁ hμ ha hρ hρ2 hM0 hM1 hℓ ?_
    have hden : 0 < 1024 * Real.pi ^ 2 * C' + 1 := by positivity
    have h1 : (μ * a ^ 3) ^ (13 / 3230 : ℝ) * (1024 * Real.pi ^ 2 * C' + 1) ≤ C₁ :=
      (le_div_iff₀ hden).mp hthr
    rw [le_div_iff₀ (by positivity : 0 < 1024 * Real.pi ^ 2 * C')]
    nlinarith [h1, Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ μ * a ^ 3) (13 / 3230 : ℝ)]

end Work.BoseBogFS
