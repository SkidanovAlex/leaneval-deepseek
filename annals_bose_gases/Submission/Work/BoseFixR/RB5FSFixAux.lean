import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixR.RB5FSArith2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `RB5FSFixAux.lean` — the far-leg assembly vocabulary (FS §9 at the honest family)

Auxiliary module of `Submission/Work/BoseFixR/RB5FSHonestFix.lean`.

Contents:

* the two slot lemmas of the assembly `KzOpFS_qw_decomp` already proved in
  `Submission/Work/BoseFixR/RB5FSHonest.lean` (`honest_view_basics`, `nPlus_slot`,
  `cnum_slot`, `gap_slot`, `KzOpFS_qw_decomp`) — copied verbatim here so that this
  development does not import the (still `sorry`-bearing) far-leg modules;
* `epsFar`, FS `eq:ChoiceEpsilon`'s `ε = √(𝓜/((μ+ρ)ℓ³))`;
* `farEnv`, the ε-split environment `τ ↦ (1−ε)τ + ρε^{−1/2}a` of FS's proof of
  `lem:Roughbounds` (the pair form used for the Bogoliubov diagonalisation).

-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseFixR

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox
open Work.BoseBoxFix Work.BoseBoxFock Work.BoseB7 Work.BoseB7A

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 0. FS `eq:ChoiceEpsilon`, and the `ε`-split of the Bogoliubov quadratic -/

/-- **FS `eq:ChoiceEpsilon`**: the optimisation parameter
`ε = √(𝓜/((μ+ρ)ℓ³))` of `lem:Roughbounds`. -/
noncomputable def epsFar (v : ℝ³ → ℝ) (μ ρ : ℝ) : ℝ :=
  Real.sqrt (bigMV v μ / ((ρ + μ) * ell v μ ^ 3))

/-- **The ε-split pair form.**  FS's proof of `eq:Rough2` replaces the kinetic symbol
`τ(k)` of the pair quadratic by `(1−ε)τ(k) + ρε^{-1/2}a`, so that the diagonal
`𝒜₁(k) = (1−ε)τ(k) + ρε^{-1/2}a + ρŴ₁(k)` is strictly positive and dominates
`ℬ(k) = ρŴ₁(k)` (because `|ℬ|/𝒜₁ ≤ 16π√ε`).  The difference
`τ − ((1−ε)τ + ρε^{-1/2}a) = ετ − ρε^{-1/2}a` is the `n₊`-term controlled by FS
`eq:Rough0`. -/
noncomputable def farEnv {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (E : Q3Env Mode) (v : ℝ³ → ℝ) (μ ρ : ℝ) : Q3Env Mode :=
  { E with
    tau := fun k => (1 - epsFar v μ ρ) * E.tau k
      + ρ * (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * a v
    A := fun k => (1 - epsFar v μ ρ) * E.tau k
      + ρ * (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * a v + ρ * E.W1 k
    B := fun k => ρ * E.W1 k }

/-! ## 0b. FS `eq:BogHamPositive-1`'s pair form, and the `ε`-split of `KzBogFS` -/

/-- FS `eq:BogHamPositive-1`'s per-mode pair quadratic at the density `ρ`
(`𝒜_k = τ_k + ρŴ₁(k)`, `ℬ_k = ρŴ₁(k)`, `𝒞_k = (ρ−μ)Ŵ₁(0)χ̂_kz`), written through
`KzEnvAt E ρ` so that it is definitionally the `k`-th summand of `KzBogFS`. -/
noncomputable def pairOpFar {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : FockData Mode) (E : Q3Env Mode) (ρ : ℝ) (k : Mode) : F.H →ₗ[ℝ] F.H :=
  ((KzEnvAt E ρ).A k) • (F.nOp k + F.nOp (-k))
    + ((KzEnvAt E ρ).B k) • (F.a k ∘ₗ F.a (-k) + F.aDag k ∘ₗ F.aDag (-k))
    + ((ρ - E.mu) * E.W1 0 * E.hatChi k * (KzEnvAt E ρ).z) •
        (F.a k + F.aDag k + F.a (-k) + F.aDag (-k))

/-- FS's `𝒞_k = (ρ−μ)Ŵ₁(0)χ̂_kz` at the density `ρ` (the `c`-number coefficient of the
pair form). -/
noncomputable def cCoefFar {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] (E : Q3Env Mode) (ρ : ℝ) (k : Mode) : ℝ :=
  (ρ - E.mu) * E.W1 0 * E.hatChi k * (KzEnvAt E ρ).z

/-- FS's `𝒜₁(k) = (1−ε)τ(k) + ρε^{-1/2}a + ρŴ₁(k)`: the strictly positive diagonal of
the `ε`-split pair form (the `k`-th summand of `KzBogFS` at `farEnv E v μ ρ`). -/
noncomputable def farA {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] (E : Q3Env Mode) (v : ℝ³ → ℝ) (μ ρ : ℝ) (k : Mode) : ℝ :=
  (KzEnvAt (farEnv E v μ ρ) ρ).A k

/-- The `κ`-error sum and the zero-point sum of the `ε`-split pair form. -/
noncomputable def farZPSum {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] (F : FockData Mode) (E : Q3Env Mode) (v : ℝ³ → ℝ) (μ ρ : ℝ) : ℝ :=
  ∑ k : Mode, (1 / 2) *
    (Work.BoseB6.bogZeroPoint (farA E v μ ρ k) ((KzEnvAt (farEnv E v μ ρ) ρ).B k)
      + Work.BoseB6.bogKappaErr (farA E v μ ρ k) ((KzEnvAt (farEnv E v μ ρ) ρ).B k)
          (cCoefFar E ρ k))

/-- The zero-point `+ κ` sum `Σ_k ½(𝒵_k + κ_k)` of the pair form at the datum `(E, ρ)`
(with `𝒜_k = (KzEnvAt E ρ).A k`, …).  This is the scalar that FS `eq:Rough2` compares with
the mass `½ρ²ℓ³ĝω(0)`. -/
noncomputable def zpSumOf {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] (E : Q3Env Mode) (ρ : ℝ) : ℝ :=
  ∑ k : Mode, (1 / 2) *
    (Work.BoseB6.bogZeroPoint ((KzEnvAt E ρ).A k) ((KzEnvAt E ρ).B k)
      + Work.BoseB6.bogKappaErr ((KzEnvAt E ρ).A k) ((KzEnvAt E ρ).B k) (cCoefFar E ρ k))

/-! ## 1. The slots already proved in `RB5FSHonest.lean` (copied verbatim) -/

/-- **The basic data of a view of the honest family**: the `c`-number pin, the three scalar
pins, positivity of the gap coefficient `b` (from the gate's `b₀`), of `𝓜` (from the
parameter view), of `Ŵ₁ω(0)` (the gate's `W1omega0_nonneg`, instantiated at `ρ = μ`, which is
always `CloseCond`), and the positivity of `ℓ`, `d` and `ε_T`. -/
lemma honest_view_basics {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v}
    {fc fu : LowCut} {HM : ∀ μ : ℝ, HonestModes v μ} {μ : ℝ}
    (hview : (HonestBoxFam v h fc fu HM μ).viewFS v h μ) :
    (HonestBoxFam v h fc fu HM μ).gHat0 = 8 * Real.pi * a v
    ∧ (HonestBoxFam v h fc fu HM μ).E.mu = μ
    ∧ (HonestBoxFam v h fc fu HM μ).E.ell = ell v μ
    ∧ (HonestBoxFam v h fc fu HM μ).E.bigM = bigMV v μ
    ∧ 0 < (HonestBoxFam v h fc fu HM μ).E.b
    ∧ 0 ≤ (HonestBoxFam v h fc fu HM μ).E.bigM
    ∧ 0 ≤ (HonestBoxFam v h fc fu HM μ).E.W1omega0
    ∧ 0 < (HonestBoxFam v h fc fu HM μ).E.ell
    ∧ 0 < (HonestBoxFam v h fc fu HM μ).E.d
    ∧ 0 ≤ (HonestBoxFam v h fc fu HM μ).E.eT := by
  unfold KzDatum.viewFS RViewFS at hview
  obtain ⟨hFSP, hmu, haSc, hell, hbigM, hb, hd, hs, heT, -, hg0, -, -, -, -, -, -, -, -, -, -,
    -, hKK⟩ := hview
  obtain ⟨K₀, b₀, hK0, hb0, hb0b, hker⟩ := hKK
  have hFSPv : FSParamsView (HonestBoxFam v h fc fu HM μ).E := Classical.choice hFSP
  have hav' : 0 < a v := by rw [← haSc]; exact hFSPv.a_pos
  have hμpos : 0 < μ := by
    have h1 : 0 < (HonestBoxFam v h fc fu HM μ).E.mu
        * (HonestBoxFam v h fc fu HM μ).E.aScat ^ 3 := by
      rw [hFSPv.mu_eq]
      exact hFSPv.t_pos
    rw [hmu, haSc] at h1
    exact pos_of_mul_pos_left h1 (by positivity)
  have hdils : 0 < dil v μ := by unfold dil; positivity
  have hKlpos : 0 < (paramsAt μ (a v)).Kl := by
    simp only [paramsAt, fsParams]
    exact fsXp_pos hdils
  -- `F9` interface fix (one line): `RViewFS`'s gate conjunct now demands `CloseCondFS` at the
  -- *corrected* (smaller) threshold, and `|μ - μ| = 0` satisfies either threshold.  The bridge
  -- `Work.BoseBoxFock.closeCondFS_self` proves exactly this; we inline it to avoid a new import.
  have hclose : CloseCondFS v μ μ := by
    unfold CloseCondFS closeThresholdFS
    rw [sub_self, abs_zero]
    exact div_nonneg (mul_nonneg hμpos.le (Real.rpow_nonneg hKlpos.le _)) (by positivity)
  have hgate := hker μ hclose
  have hdpos : 0 < (HonestBoxFam v h fc fu HM μ).E.d := by
    rw [hd]
    simp only [paramsAt, fsParams]
    exact fsXp_pos hdils
  have heTnn : 0 ≤ (HonestBoxFam v h fc fu HM μ).E.eT := by
    rw [heT]
    simp only [paramsAt, fsParams]
    exact le_of_lt (fsXp_pos hdils)
  have hellpos : 0 < (HonestBoxFam v h fc fu HM μ).E.ell := by
    rw [hell, ell, sideAt, boxSide]
    refine mul_pos ?_ (Real.rpow_pos_of_pos (by positivity) _)
    simp only [paramsAt, fsParams]
    exact fsXp_pos hdils
  exact ⟨hg0, hmu, hell, by rw [hbigM]; rfl, lt_of_lt_of_le hb0 hb0b,
    by rw [hbigM]; exact le_trans zero_le_one hFSPv.one_le_bigM, hgate.W1omega0_nonneg,
    hellpos, hdpos, heTnn⟩

/-- **The `n₊`-slot at a view-satisfying datum.**  `((ρ−μ)Ŵ₁(0))·Σ_k n_k` is bounded below
by `−|ρ−μ|·16πa·16𝓜‖f‖²`: the view's Bessel conjunct (`Cn ≤ 16`) composed with the window
bounds `⟨Σ_k n_k⟩ ≤ 16𝓜‖f‖²`, and `|Ŵ₁(0)| ≤ 16πa`. -/
lemma nPlus_slot {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {μ : ℝ}
    (D : KzDatum) (hav : 0 < a v) (hview : D.viewFS v h μ)
    (hW10 : |D.E.W1 0| ≤ 16 * Real.pi * a v) (hM : 0 ≤ D.E.bigM)
    (ρ : ℝ) (f : D.F.H) (hf : D.T.NWindow D.E.bigM f) :
    -(|ρ - μ| * (16 * Real.pi * a v) * (16 * D.E.bigM)) * D.F.normSq f
      ≤ D.F.qw f (((ρ - μ) * D.E.W1 0) • ∑ k : D.Mode, D.F.nOp k) := by
  unfold KzDatum.viewFS RViewFS at hview
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hBessel, -⟩ := hview
  obtain ⟨Cn, hCn0, hCn16, hCn⟩ := hBessel
  have hTN : D.F.bp (D.T.N f) f ≤ D.E.bigM * D.F.normSq f :=
    NWindow_bp_N_le D.F D.T hM hf
  have hnsq : 0 ≤ D.F.normSq f := D.F.normSq_nonneg f
  have hB : D.F.qw f (∑ k : D.Mode, D.F.nOp k) ≤ Cn * D.E.bigM * D.F.normSq f := by
    have h2 : Cn * D.F.bp (D.T.N f) f ≤ Cn * (D.E.bigM * D.F.normSq f) :=
      mul_le_mul_of_nonneg_left hTN hCn0
    calc D.F.qw f (∑ k : D.Mode, D.F.nOp k)
        = D.F.bp ((∑ k : D.Mode, D.F.nOp k) f) f := rfl
      _ ≤ Cn * D.F.bp (D.T.N f) f := hCn f
      _ ≤ Cn * (D.E.bigM * D.F.normSq f) := h2
      _ = Cn * D.E.bigM * D.F.normSq f := by ring
  have hQnn : 0 ≤ D.F.qw f (∑ k : D.Mode, D.F.nOp k) := by
    have hsplit : D.F.qw f (∑ k : D.Mode, D.F.nOp k)
        = ∑ k : D.Mode, D.F.bp (D.F.a k f) (D.F.a k f) := by
      simp only [FockData.qw, map_sum, LinearMap.sum_apply, FockData.nOp,
        LinearMap.comp_apply]
      exact Finset.sum_congr rfl (fun k _ => by rw [FockData.aDag_adjoint])
    rw [hsplit]
    exact Finset.sum_nonneg fun k _ => D.F.bp_nonneg _
  rw [FockData.qw_smul]
  set c : ℝ := (ρ - μ) * D.E.W1 0 with hcdef
  set Q : ℝ := D.F.qw f (∑ k : D.Mode, D.F.nOp k) with hQdef
  set K : ℝ := |ρ - μ| * (16 * Real.pi * a v) * (16 * D.E.bigM) with hKdef
  have h16 : 0 ≤ 16 * Real.pi * a v := by positivity
  have hKnn : 0 ≤ K := by
    rw [hKdef]
    exact mul_nonneg (mul_nonneg (abs_nonneg _) h16) (mul_nonneg (by norm_num) hM)
  rcases lt_trichotomy c 0 with hlt | heq | hgt
  · have h1 : c * (Cn * D.E.bigM * D.F.normSq f) ≤ c * Q := by
      rw [hQdef]
      exact mul_le_mul_of_nonpos_left hB (le_of_lt hlt)
    have hnegc : -(c) = |ρ - μ| * |D.E.W1 0| := by
      rw [← abs_of_neg hlt, hcdef, abs_mul]
    have hprod : -(c) * Cn ≤ |ρ - μ| * (16 * Real.pi * a v) * 16 := by
      have hs1 : |ρ - μ| * |D.E.W1 0| * Cn ≤ |ρ - μ| * (16 * Real.pi * a v) * Cn :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hW10 (abs_nonneg _)) hCn0
      have hs2 : |ρ - μ| * (16 * Real.pi * a v) * Cn ≤ |ρ - μ| * (16 * Real.pi * a v) * 16 :=
        mul_le_mul_of_nonneg_left hCn16 (mul_nonneg (abs_nonneg _) h16)
      rw [hnegc]
      linarith
    have h2 : -(K) ≤ c * (Cn * D.E.bigM) := by
      rw [hKdef]
      nlinarith [hprod, hM, Real.pi_pos.le, le_of_lt hav, abs_nonneg (ρ - μ),
        abs_nonneg (D.E.W1 0), hCn0]
    have h3 : -(K) * D.F.normSq f ≤ c * (Cn * D.E.bigM * D.F.normSq f) := by
      nlinarith [h2, hnsq]
    linarith
  · rw [heq, zero_mul]
    have : 0 ≤ K * D.F.normSq f := mul_nonneg hKnn hnsq
    linarith
  · have h1 : 0 ≤ c * Q := mul_nonneg (le_of_lt hgt) (by rw [hQdef]; exact hQnn)
    have : 0 ≤ K * D.F.normSq f := mul_nonneg hKnn hnsq
    linarith

/-- **The `c`-number slot.**  `ℓ³(−½μ²ĝ(0) + ½(ρ−μ)²ĝ(0) + ½ρ²Ŵ₁ω(0))` is at least
`−4πμ²aℓ³ + 4πa(ρ−μ)²ℓ³`: `ĝ(0) = 8πa v`, the two `⅛π`'s cancel, and `½ρ²ℓ³Ŵ₁ω(0) ≥ 0`. -/
lemma cnum_slot {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {μ ρ : ℝ}
    (D : KzDatum) (hav : 0 < a v) (hge : D.gHat0 = 8 * Real.pi * a v)
    (hmuE : D.E.mu = μ) (hellE : D.E.ell = ell v μ) (hW1o0 : 0 ≤ D.E.W1omega0)
    (hell : 0 ≤ ell v μ) (f : D.F.H) :
    (-4 * Real.pi * μ ^ 2 * a v * ell v μ ^ 3
        + 4 * Real.pi * a v * (ρ - μ) ^ 2 * ell v μ ^ 3) * D.F.normSq f
      ≤ (D.E.ell ^ 3 * (-(1 / 2) * D.E.mu ^ 2 * D.gHat0
            + (1 / 2) * (ρ - D.E.mu) ^ 2 * D.gHat0
            + (1 / 2) * ρ ^ 2 * D.E.W1omega0)) * D.F.normSq f := by
  rw [hge, hmuE, hellE]
  have hnsq : 0 ≤ D.F.normSq f := D.F.normSq_nonneg f
  have hρ2 : 0 ≤ ρ ^ 2 * ell v μ ^ 3 * D.E.W1omega0 :=
    mul_nonneg (mul_nonneg (sq_nonneg ρ) (pow_nonneg hell 3)) hW1o0
  nlinarith [hnsq, hρ2, Real.pi_pos]

/-- **The `c`-number slot, massless form.**  The *split* `c`-number
`ℓ³(−½μ²ĝ(0) + ½(ρ−μ)²ĝ(0))` (the mass `½ρ²ℓ³Ŵ₁ω(0)` removed) is exactly
`(−4πμ²aℓ³ + 4πa(ρ−μ)²ℓ³)` once `ĝ(0) = 8πa v`.  This is the form the far-leg assembly needs:
the residual slot `FarResid` carries the mass `+½ρ²ℓ³Ŵ₁ω(0)` *inside* its lower bound, and the
mass must therefore not also be counted in the `c`-number slot. -/
lemma cnum_slot_split {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {μ ρ : ℝ}
    (D : KzDatum) (hav : 0 < a v) (hge : D.gHat0 = 8 * Real.pi * a v)
    (hmuE : D.E.mu = μ) (hellE : D.E.ell = ell v μ) (f : D.F.H) :
    (-4 * Real.pi * μ ^ 2 * a v * ell v μ ^ 3
        + 4 * Real.pi * a v * (ρ - μ) ^ 2 * ell v μ ^ 3) * D.F.normSq f
      ≤ (D.E.ell ^ 3 * (-(1 / 2) * D.E.mu ^ 2 * D.gHat0
            + (1 / 2) * (ρ - D.E.mu) ^ 2 * D.gHat0)) * D.F.normSq f := by
  rw [hge, hmuE, hellE]
  have hnsq : 0 ≤ D.F.normSq f := D.F.normSq_nonneg f
  nlinarith [hnsq, Real.pi_pos]

/-- **The gap slot.**  `(b/2ℓ²)n₊ + (ε_Tb/(2d²ℓ²))n₊^H ≥ 0`: both number operators are
nonnegative and both coefficients are nonnegative (the gate gives `b ≥ b₀ > 0`). -/
lemma gap_slot {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {μ : ℝ}
    (D : KzDatum) (hb : 0 < D.E.b) (hℓ : 0 < D.E.ell) (hd : 0 < D.E.d) (heT : 0 ≤ D.E.eT)
    (f : D.F.H) :
    0 ≤ (D.E.b / (2 * D.E.ell ^ 2)) * D.F.qw f D.T.N
        + (D.E.eT * D.E.b / (2 * D.E.d ^ 2 * D.E.ell ^ 2)) * D.F.qw f D.T.NH := by
  have h1 : 0 ≤ D.E.b / (2 * D.E.ell ^ 2) := by positivity
  have h2 : 0 ≤ D.E.eT * D.E.b / (2 * D.E.d ^ 2 * D.E.ell ^ 2) := by positivity
  have h3 : 0 ≤ D.F.qw f D.T.N := by
    rw [FockData.qw]
    exact D.T.N_nonneg f
  have h4 : 0 ≤ D.F.qw f D.T.NH := by
    rw [FockData.qw]
    exact D.T.NH_nonneg f
  exact add_nonneg (mul_nonneg h1 h3) (mul_nonneg h2 h4)

/-- **The decomposition of `KzOpFS`.**  Expanding `qw` over the eight summands of
`KzOpFS`. -/
lemma KzOpFS_qw_decomp {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) (gHat0 ρ : ℝ) (f : F.H) :
    F.qw f (KzOpFS F T E gHat0 ρ)
      = (E.b / (2 * E.ell ^ 2)) * F.qw f T.N
        + (E.eT * E.b / (2 * E.d ^ 2 * E.ell ^ 2)) * F.qw f T.NH
        + (E.ell ^ 3 * (-(1 / 2) * E.mu ^ 2 * gHat0
            + (1 / 2) * (ρ - E.mu) ^ 2 * gHat0
            + (1 / 2) * ρ ^ 2 * E.W1omega0)) * F.normSq f
        + F.qw f (KzBogFS F E ρ)
        + (((ρ - E.mu) * E.W1 0) * F.qw f (∑ k : Mode, F.nOp k))
        + F.qw f (T.linOpT (KzEnvAt E ρ))
        + F.qw f (F.Q2ex (KzEnvAt E ρ))
        + F.qw f (T.Q3T (KzEnvAt E ρ)) := by
  have hq1 : F.qw f (1 : F.H →ₗ[ℝ] F.H) = F.normSq f := by
    simp [FockData.qw, FockData.normSq]
  simp only [KzOpFS, FockData.qw_add, FockData.qw_smul]
  rw [hq1]
  try ring_nf

end Work.BoseFixR
