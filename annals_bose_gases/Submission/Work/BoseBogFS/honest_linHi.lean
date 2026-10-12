import ChallengeDeps
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseBogFS.linHi_form_le
import Submission.Work.BoseBoxFock.honest_RHi_hatChi_sq_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.honest_linHi`

The `𝒞`-term of FS `eq:BogHamPositive-1` on the region `RHi = {|k| ≥ ½K_L√(μa)}`,
bounded directly (frame bound on window states): the single sum
`Σ_{k ∈ RHi} ½𝒞_k(a_k + a_k† + a_{-k} + a_{-k}†)` has quadratic form at most
`C·errBracket·‖f‖²`.

The proof is split into independent pieces:

* `linHi_form_le` (delegated) — the Fock-form Cauchy–Schwarz step
  `|⟨(Σ_{k∈S}½c_k(a_k+a_k†+a_{-k}+a_{-k}†))f, f⟩| ≤ 2√(Σ_{k∈S}c_k²)√(Σ_{k∈S}‖a_kf‖²)√‖f‖²`
  for negation-invariant `S` and even `c`;
* the Bessel/window row `Σ_k‖a_kf‖² ≤ 16𝓜‖f‖²` (`Work.BoseBogFS.sum_normSq_a_le`);
* `honest_RHi_hatChi_sq_le` (delegated) — the χ̂-decay sum
  `Σ_{k∈RHi}χ̂(k)² ≤ 128·Cchi²·2¹⁰¹·X¹²¹²`, from `lem:DecaychiHat` and the dyadic
  lattice tail sum (`K_ℓK_L = X^{-12}`);
* the arithmetic (`closeThresholdFS_eq`, `mu_ell_cube_eq`, `mul_a_le_errBracket`,
  `linHi_arith`).
-/

noncomputable section

open scoped Real BigOperators

namespace Work.BoseBogFS

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseBoxFix Work.BoseFixR

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 0. Elementary `fsXp`-arithmetic -/

/-- `√(fsXp t c) = fsXp t (c/2)`. -/
lemma fsXp_sqrt {t c : ℝ} (ht : 0 < t) :
    Real.sqrt (Work.BoseBox.fsXp t c) = Work.BoseBox.fsXp t (c / 2) := by
  rw [Real.sqrt_eq_rpow, Work.BoseBox.fsXp, Work.BoseBox.fsXp, ← Real.rpow_mul ht.le]
  congr 1
  ring

/-- `1 ≤ fsXp t c` for `c ≤ 0` and `0 < t ≤ 1` (the monomial `t^{c/323}` is at least `1`). -/
lemma one_le_fsXp_of_nonpos {t c : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hc : c ≤ 0) :
    1 ≤ Work.BoseBox.fsXp t c := by
  have h1 : Work.BoseBox.fsXp t (-c) ≤ 1 := Work.BoseBox.fsXp_le_one ht ht1 (by linarith)
  have h2 : 0 < Work.BoseBox.fsXp t (-c) := Work.BoseBox.fsXp_pos ht
  have h3 : Work.BoseBox.fsXp t c = (Work.BoseBox.fsXp t (-c))⁻¹ := by
    rw [Work.BoseBox.fsXp_inv ht, neg_neg]
  rw [h3]
  exact (one_le_inv₀ h2).mpr h1

/-! ## 1. The close threshold and `μℓ³` in `X`-form -/

/-- `closeThresholdFS v μ = μX³/(2¹⁴π)`: the `F9` threshold is `μK_ℓ^{-2}/(2¹⁴π)` and
`K_ℓ^{-2} = (X^{-3/2})^{-2} = X³`. -/
lemma closeThresholdFS_eq {v : ℝ³ → ℝ} {μ : ℝ} (hμ : 0 < μ) (hav : 0 < a v) :
    Work.BoseBoxFock.closeThresholdFS v μ
      = μ * Work.BoseBox.fsXp (dil v μ) 3 / ((2 : ℝ) ^ 14 * Real.pi) := by
  have ht0 : 0 ≤ dil v μ := (mul_pos hμ (pow_pos hav 3)).le
  have hKl : (Work.BoseBox.paramsAt μ (a v)).Kl = Work.BoseBox.fsXp (dil v μ) (-(3 / 2)) :=
    rfl
  unfold Work.BoseBoxFock.closeThresholdFS
  rw [hKl, Work.BoseBox.fsXp_rpow ht0 (-(3 / 2)) (-(2 : ℝ)), Work.BoseBox.fsXp,
    Work.BoseBox.fsXp]
  norm_num

/-- `μℓ³ = X^{-166}`: `ℓ = K_ℓ(μa)^{-1/2} = a(μa³)^{-163/323}`, so
`μℓ³ = (μa³)^{1-489/323} = X^{-166}`. -/
lemma mu_ell_cube_eq {v : ℝ³ → ℝ} {μ : ℝ} (hμ : 0 < μ) (hav : 0 < a v) :
    μ * (ell v μ) ^ 3 = Work.BoseBox.fsXp (dil v μ) (-166) := by
  have h := Work.BoseBox.mu_ell_cube_fsParams (a := a v) hμ hav
  simpa only [Work.BoseFixR.ell, Work.BoseBox.sideAt, Work.BoseBox.paramsAt,
    Work.BoseBox.fsXp, Work.BoseFixR.dil, neg_div] using h

/-! ## 2. The error bracket dominates `μ·a v` -/

/-- `μ·a v ≤ errBracket v R μ`: the bracket `μ²aℓ³√t·(X² + …)` is at least
`μ²aℓ³√t·X² = μa·X^{-166}·X^{161.5}·X² = μaX^{-2.5} ≥ μa`. -/
lemma mul_a_le_errBracket {v : ℝ³ → ℝ} {μ R : ℝ} (hμ : 0 < μ) (hav : 0 < a v)
    (hR : 0 < R) (hX : fsX v μ ≤ 1) :
    μ * a v ≤ errBracket v R μ := by
  have ht0 : 0 < dil v μ := mul_pos hμ (pow_pos hav 3)
  have ht1 : dil v μ ≤ 1 := by
    rw [Work.BoseFixR.fsX, Work.BoseBox.fsXp] at hX
    by_contra hc
    push Not at hc
    have : (1 : ℝ) < (dil v μ) ^ ((1 : ℝ) / 323) :=
      Real.one_lt_rpow hc (by norm_num)
    linarith
  have hsqrt : Real.sqrt (dil v μ) = Work.BoseBox.fsXp (dil v μ) (323 / 2) := by
    rw [Real.sqrt_eq_rpow, Work.BoseB7.rpow_eq_fsXp (c := 1 / 2) ht0.le]
    congr 1
    norm_num
  have hmue : μ * (ell v μ) ^ 3 = Work.BoseBox.fsXp (dil v μ) (-166) := mu_ell_cube_eq hμ hav
  have hX2 : fsX v μ ^ 2 = Work.BoseBox.fsXp (dil v μ) 2 := by
    rw [Work.BoseFixR.fsX, Work.BoseBox.fsXp_pow ht0.le 1 2]
    norm_num
  have hone : 1 ≤ Work.BoseBox.fsXp (dil v μ) (-(5 / 2)) :=
    one_le_fsXp_of_nonpos ht0 ht1 (by norm_num)
  have hprod : Work.BoseBox.fsXp (dil v μ) (-166)
      * Work.BoseBox.fsXp (dil v μ) (323 / 2) * Work.BoseBox.fsXp (dil v μ) 2
      = Work.BoseBox.fsXp (dil v μ) (-(5 / 2)) := by
    rw [Work.BoseBox.fsXp_mul ht0, Work.BoseBox.fsXp_mul ht0]
    congr 1
    norm_num
  have hab : 0 ≤ μ * a v := (mul_pos hμ hav).le
  have hell : 0 < ell v μ := by
    rw [Work.BoseFixR.ell_eq]
    exact Work.BoseBox.sideAt_pos hμ hav
  have hbracket : 0 ≤ fsX v μ ^ 2 + (R / a v) ^ 2 * Real.sqrt (dil v μ) + errExp v μ := by
    have h1 : 0 ≤ fsX v μ ^ 2 := sq_nonneg _
    have h2 : 0 ≤ (R / a v) ^ 2 * Real.sqrt (dil v μ) := by positivity
    have h3 : 0 ≤ errExp v μ := Real.rpow_nonneg ht0.le _
    linarith
  have hb2 : 0 ≤ (R / a v) ^ 2 * Real.sqrt (dil v μ) := by positivity
  have hb3 : 0 ≤ errExp v μ := Real.rpow_nonneg ht0.le _
  have hmain : μ * a v ≤ μ ^ 2 * a v * (ell v μ) ^ 3 * Real.sqrt (dil v μ) * fsX v μ ^ 2 := by
    have hred : μ ^ 2 * a v * (ell v μ) ^ 3 * Real.sqrt (dil v μ) * fsX v μ ^ 2
        = (μ * a v) * (Work.BoseBox.fsXp (dil v μ) (-166)
            * Work.BoseBox.fsXp (dil v μ) (323 / 2) * Work.BoseBox.fsXp (dil v μ) 2) := by
      rw [show μ ^ 2 * a v * (ell v μ) ^ 3 * Real.sqrt (dil v μ) * fsX v μ ^ 2
          = (μ * a v) * (μ * (ell v μ) ^ 3) * Real.sqrt (dil v μ) * fsX v μ ^ 2 by ring]
      rw [hmue, hsqrt, hX2]
      ring
    rw [hred, hprod]
    exact le_mul_of_one_le_right hab hone
  unfold errBracket
  simp only [Work.BoseFixR.ell3]
  have hstep : μ ^ 2 * a v * (ell v μ) ^ 3 * Real.sqrt (dil v μ) * fsX v μ ^ 2
      ≤ μ ^ 2 * a v * (ell v μ) ^ 3 * Real.sqrt (dil v μ)
        * (fsX v μ ^ 2 + (R / a v) ^ 2 * Real.sqrt (dil v μ) + errExp v μ) := by
    have h4 : 0 ≤ μ ^ 2 * a v * (ell v μ) ^ 3 * Real.sqrt (dil v μ) := by positivity
    exact mul_le_mul_of_nonneg_left (by linarith [hb2, hb3]) h4
  linarith [hmain, hstep]

/-! ## 3. The final arithmetic -/

/-- **The final arithmetic.**  From `Σc² ≤ 2⁸⁹Cchi²(μa)²X¹⁰⁵²` and `𝓜 = X^{-327/4}`, the
frame-bound output is at most `2⁴⁸·Cchi·μ·a`:

`8√(Σc²)√𝓜 ≤ 8·(√(2⁸⁹)Cchi μa X⁵²⁶)·X^{-327/8} = 2⁴⁸Cchi μa X^{3881/8} ≤ 2⁴⁸Cchi μa`. -/
lemma linHi_arith {t μ a Cchi S2 : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hμ : 0 < μ) (ha : 0 < a)
    (hCchi : 0 ≤ Cchi) (hS2nn : 0 ≤ S2)
    (hS2 : S2 ≤ (2 : ℝ) ^ 89 * Cchi ^ 2 * μ ^ 2 * a ^ 2 * Work.BoseBox.fsXp t 1052) :
    8 * Real.sqrt S2 * Real.sqrt (Work.BoseBox.fsXp t (-(327 / 4)))
      ≤ ((2 : ℝ) ^ 48 * Cchi + 1) * (μ * a) := by
  have hsq : (2 : ℝ) ^ 89 ≤ ((2 : ℝ) ^ 45) ^ 2 := by norm_num
  have hbase : (2 : ℝ) ^ 89 * Cchi ^ 2 * μ ^ 2 * a ^ 2 ≤ ((2 : ℝ) ^ 45 * Cchi * μ * a) ^ 2 := by
    have h1 : (2 : ℝ) ^ 89 * Cchi ^ 2 * μ ^ 2 * a ^ 2
        ≤ ((2 : ℝ) ^ 45) ^ 2 * Cchi ^ 2 * μ ^ 2 * a ^ 2 := by
      have h2 : 0 ≤ Cchi ^ 2 * μ ^ 2 * a ^ 2 := by positivity
      nlinarith [hsq, h2]
    have h3 : ((2 : ℝ) ^ 45) ^ 2 * Cchi ^ 2 * μ ^ 2 * a ^ 2 = ((2 : ℝ) ^ 45 * Cchi * μ * a) ^ 2 := by
      ring
    linarith
  have h45 : (0 : ℝ) ≤ (2 : ℝ) ^ 45 * Cchi * μ * a := by positivity
  have hsA : Real.sqrt ((2 : ℝ) ^ 89 * Cchi ^ 2 * μ ^ 2 * a ^ 2)
      ≤ (2 : ℝ) ^ 45 * Cchi * μ * a := by
    calc Real.sqrt ((2 : ℝ) ^ 89 * Cchi ^ 2 * μ ^ 2 * a ^ 2)
        ≤ Real.sqrt (((2 : ℝ) ^ 45 * Cchi * μ * a) ^ 2) := Real.sqrt_le_sqrt hbase
      _ = (2 : ℝ) ^ 45 * Cchi * μ * a := Real.sqrt_sq h45
  have hsF : Real.sqrt (Work.BoseBox.fsXp t 1052) = Work.BoseBox.fsXp t 526 := by
    rw [fsXp_sqrt ht]
    norm_num
  have hsM : Real.sqrt (Work.BoseBox.fsXp t (-(327 / 4))) = Work.BoseBox.fsXp t (-(327 / 8)) := by
    rw [fsXp_sqrt ht]
    norm_num
  have hfac : Real.sqrt ((2 : ℝ) ^ 89 * Cchi ^ 2 * μ ^ 2 * a ^ 2 * Work.BoseBox.fsXp t 1052)
      ≤ (2 : ℝ) ^ 45 * Cchi * μ * a * Work.BoseBox.fsXp t 526 := by
    have hnn : 0 ≤ (2 : ℝ) ^ 89 * Cchi ^ 2 * μ ^ 2 * a ^ 2 :=
      mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) 89) (sq_nonneg _))
        (sq_nonneg _)) (sq_nonneg _)
    rw [Real.sqrt_mul hnn, hsF]
    exact mul_le_mul_of_nonneg_right hsA (Work.BoseBox.fsXp_pos ht).le
  have hpow : Work.BoseBox.fsXp t 526 * Work.BoseBox.fsXp t (-(327 / 8))
      = Work.BoseBox.fsXp t (3881 / 8) := by
    rw [Work.BoseBox.fsXp_mul ht]
    congr 1
    norm_num
  have hle1 : Work.BoseBox.fsXp t (3881 / 8) ≤ 1 :=
    Work.BoseBox.fsXp_le_one ht ht1 (by norm_num)
  calc 8 * Real.sqrt S2 * Real.sqrt (Work.BoseBox.fsXp t (-(327 / 4)))
      ≤ 8 * Real.sqrt ((2 : ℝ) ^ 89 * Cchi ^ 2 * μ ^ 2 * a ^ 2 * Work.BoseBox.fsXp t 1052)
          * Real.sqrt (Work.BoseBox.fsXp t (-(327 / 4))) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hS2) (by norm_num))
          (Real.sqrt_nonneg _)
    _ = 8 * Real.sqrt ((2 : ℝ) ^ 89 * Cchi ^ 2 * μ ^ 2 * a ^ 2 * Work.BoseBox.fsXp t 1052)
          * Work.BoseBox.fsXp t (-(327 / 8)) := by rw [hsM]
    _ ≤ 8 * ((2 : ℝ) ^ 45 * Cchi * μ * a * Work.BoseBox.fsXp t 526)
          * Work.BoseBox.fsXp t (-(327 / 8)) := by
        have h0 : 0 ≤ Work.BoseBox.fsXp t (-(327 / 8)) := (Work.BoseBox.fsXp_pos ht).le
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfac (by norm_num)) h0
    _ = 8 * (2 : ℝ) ^ 45 * Cchi * μ * a
          * (Work.BoseBox.fsXp t 526 * Work.BoseBox.fsXp t (-(327 / 8))) := by ring
    _ = 8 * (2 : ℝ) ^ 45 * Cchi * μ * a * Work.BoseBox.fsXp t (3881 / 8) := by rw [hpow]
    _ ≤ 8 * (2 : ℝ) ^ 45 * Cchi * μ * a * 1 := by
        have h0 : 0 ≤ 8 * (2 : ℝ) ^ 45 * Cchi * μ * a := by positivity
        exact mul_le_mul_of_nonneg_left hle1 h0
    _ = (2 : ℝ) ^ 48 * Cchi * (μ * a) := by ring
    _ ≤ ((2 : ℝ) ^ 48 * Cchi + 1) * (μ * a) := by
        have h0 : 0 ≤ μ * a := (mul_pos hμ ha).le
        nlinarith [h0]

/-! ## 4. Two more elementary pieces -/

/-- Monotonicity of a product of four nonnegative factors. -/
lemma mul_le_mul4 {a1 a2 a3 a4 b1 b2 b3 b4 : ℝ} (h1 : a1 ≤ b1) (h2 : a2 ≤ b2)
    (h3 : a3 ≤ b3) (h4 : a4 ≤ b4) (ha2 : 0 ≤ a2) (ha3 : 0 ≤ a3) (ha4 : 0 ≤ a4)
    (hb1 : 0 ≤ b1) (hb2 : 0 ≤ b2) (hb3 : 0 ≤ b3) :
    a1 * a2 * a3 * a4 ≤ b1 * b2 * b3 * b4 := by
  have h12 : a1 * a2 ≤ b1 * b2 := mul_le_mul h1 h2 ha2 hb1
  have h123 : a1 * a2 * a3 ≤ b1 * b2 * b3 := mul_le_mul h12 h3 ha3 (by positivity)
  have h1230 : 0 ≤ b1 * b2 * b3 := by positivity
  exact mul_le_mul h123 h4 ha4 h1230

/-- The diluteness bound `t ≤ 2^{-323/12}` is `X^{-12}/2 ≥ 1` with `X = (μa³)^{1/323}`. -/
lemma one_le_fsX_neg12 {t : ℝ} (ht : 0 < t) (ht12 : t ≤ (2 : ℝ) ^ (-(323 / 12 : ℝ))) :
    1 ≤ (Work.BoseBox.fsXp t 1) ^ (-(12 : ℝ)) / 2 := by
  have hpow : Work.BoseBox.fsXp t 12 ≤ 1 / 2 := by
    have h1 : t ^ ((12 : ℝ) / 323) ≤ ((2 : ℝ) ^ (-(323 / 12 : ℝ))) ^ ((12 : ℝ) / 323) :=
      Real.rpow_le_rpow ht.le ht12 (by norm_num)
    have h2 : ((2 : ℝ) ^ (-(323 / 12 : ℝ))) ^ ((12 : ℝ) / 323) = 1 / 2 := by
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    have h3 : Work.BoseBox.fsXp t 12 = t ^ ((12 : ℝ) / 323) := rfl
    rw [h3]
    linarith
  have hXinv : (Work.BoseBox.fsXp t 1) ^ (-(12 : ℝ)) = (Work.BoseBox.fsXp t 12)⁻¹ := by
    rw [Work.BoseBox.fsXp_rpow ht.le 1 (-(12 : ℝ)), Work.BoseBox.fsXp_inv ht]
    congr 1
    norm_num
  have hpos : 0 < Work.BoseBox.fsXp t 12 := Work.BoseBox.fsXp_pos ht
  have h2 : (2 : ℝ) ≤ (Work.BoseBox.fsXp t 12)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num : (0 : ℝ) < 2) hpos,
      show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
    exact hpow
  rw [hXinv]
  linarith

end Work.BoseBogFS

namespace Work.BoseBogFS

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseBoxFix Work.BoseFixR

set_option linter.unusedVariables false

theorem honest_linHi {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut}
    {HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ} {R : ℝ}
    (hR : 0 < R) (hv : ∀ x, 0 ≤ v x) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).viewFSAll v h μ → ∀ ρ : ℝ,
      Work.BoseBoxFock.CloseCondFS v μ ρ →
      ∀ f : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.H,
        (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T.NWindow
          (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM f →
        |(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.qw f
          (∑ k ∈ Finset.univ.filter (Work.BoseBoxFock.RHi
              (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F
              (Work.BoseFixR.KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ)),
            ((1 / 2 : ℝ) * Work.BoseBogFS.bogC (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ k) •
              ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.a k
                + (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.aDag k
                + (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.a (-k)
                + (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.aDag (-k)))|
          ≤ C * Work.BoseBogFS.errBracket v R μ
              * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.normSq f := by
  obtain ⟨Cchi, hCchi0, hChi26⟩ := Work.BoseK15.ChiReg_corpus 26
  obtain ⟨ε₁, hε₁0, hε₁⟩ := Work.BoseBogFS.exists_adm_ell_ge (v := v) hav
    (M := R / Submission.BoseGases.chiR0) (div_pos hR Submission.BoseGases.chiR0_pos)
  refine ⟨min ε₁ (min 1 ((2 : ℝ) ^ (-(323 / 12 : ℝ)))),
    (2 : ℝ) ^ 48 * Cchi + 1, ?_, ?_, ?_⟩
  · exact lt_min hε₁0 (lt_min one_pos (Real.rpow_pos_of_pos (by norm_num) _))
  · have h1 : 0 ≤ (2 : ℝ) ^ 48 * Cchi := mul_nonneg (by norm_num) hCchi0
    linarith
  · intro μ hAdm hview ρ hρ
    have hμ : 0 < μ := hAdm.1
    have hdil0 : 0 < dil v μ := mul_pos hμ (pow_pos hav 3)
    have hdil_le : dil v μ ≤ min ε₁ (min 1 ((2 : ℝ) ^ (-(323 / 12 : ℝ)))) := hAdm.2.1
    have hdil1 : dil v μ ≤ 1 :=
      le_trans hdil_le (le_trans (min_le_right _ _) (min_le_left _ _))
    have hdil12 : dil v μ ≤ (2 : ℝ) ^ (-(323 / 12 : ℝ)) :=
      le_trans hdil_le (le_trans (min_le_right _ _) (min_le_right _ _))
    have hRℓ : R ≤ ell v μ * Submission.BoseGases.chiR0 := by
      have hh := hε₁ μ (Work.BoseBogFS.adm_mono (min_le_left _ _) hAdm)
      rwa [div_le_iff₀ Submission.BoseGases.chiR0_pos] at hh
    have hℓpos : 0 < ell v μ := by
      rw [Work.BoseFixR.ell_eq]
      exact Work.BoseBox.sideAt_pos hμ hav
    have hR1 : 1 ≤ (Work.BoseFixR.fsX v μ) ^ (-(12 : ℝ)) / 2 := by
      rw [Work.BoseFixR.fsX]
      exact one_le_fsX_neg12 hdil0 hdil12
    -- the datum and the view
    set D := Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ with hD
    have hviewE : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).viewFSAll v h μ := by
      rw [← hD]; exact hview
    unfold Work.BoseFixR.KzDatum.viewFSAll Work.BoseBoxFock.RViewFSAll at hview
    obtain ⟨hFS, hmu_eq, ha_eq, hell_eq, hbM_eq, hb_eq, hd_eq, hs_eq, heT_eq, hintM_eq, hg0_eq,
      htau_eq, hA_eq, hB_eq, hW1pin, hWo_eq, hWo0_eq, hhat_eq, hhatSq_eq, hfLp, hNHp,
      hBessel, hgate⟩ := hview
    obtain ⟨hpv⟩ := hFS
    obtain ⟨Cn, hCn0, hCn16, hBesselRow⟩ := hBessel
    obtain ⟨K₀, b₀, hK₀0, hb₀0, hb₀b, hgateAt⟩ := hgate
    have hgateρ := hgateAt ρ hρ
    intro f hf
    have ht_eq : hpv.t = dil v μ := by
      rw [← hpv.mu_eq, hmu_eq, ha_eq]
      rfl
    have hbigM : D.E.bigM = Work.BoseBox.fsXp (dil v μ) (-(327 / 4)) := by
      rw [Work.BoseB7.bigM_val D.E hpv, ht_eq]
    have hbigM0 : 0 ≤ D.E.bigM := by
      rw [hbigM]; exact (Work.BoseBox.fsXp_pos hdil0).le
    have hmue : D.E.mu * D.E.ell ^ 3 = Work.BoseBox.fsXp (dil v μ) (-166) := by
      rw [Work.BoseB7.mue_val D.E hpv, ht_eq]
    have hEℓ : D.E.ell = ell v μ := hell_eq
    have hℓEpos : 0 < D.E.ell := by rw [hEℓ]; exact hℓpos
    have hNf : 0 ≤ D.F.normSq f := D.F.bp_nonneg f
    -- the Bessel / window row
    have hspec : (∑ k : D.Mode, D.F.normSq (D.F.a k f)) ≤ 16 * D.E.bigM * D.F.normSq f :=
      Work.BoseBogFS.sum_normSq_a_le D.F D.T D.E Cn hbigM0 hBesselRow hCn16 f hf
    have hnorm : (∑ k ∈ Finset.univ.filter
          (Work.BoseBoxFock.RHi D.F (Work.BoseFixR.KzEnvAt D.E ρ)),
        D.F.bp (D.F.a k f) (D.F.a k f)) ≤ 16 * D.E.bigM * D.F.normSq f := by
      have hspec' : (∑ k : D.Mode, D.F.bp (D.F.a k f) (D.F.a k f))
          ≤ 16 * D.E.bigM * D.F.normSq f := by
        simpa only [Work.BoseB7.FockData.normSq] using hspec
      have h1 := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset
          (fun k => Work.BoseBoxFock.RHi D.F (Work.BoseFixR.KzEnvAt D.E ρ) k)
          Finset.univ)
        (fun x _ _ => D.F.bp_nonneg (D.F.a x f))
      exact le_trans h1 hspec'
    -- symmetry of the region and evenness of `𝒞`
    have hhat_even : ∀ k : D.Mode, D.E.hatChi (-k) = D.E.hatChi k :=
      fun k => hgateρ.hatChi_even k
    have hSsym : ∀ k : D.Mode, k ∈ Finset.univ.filter
          (Work.BoseBoxFock.RHi D.F (Work.BoseFixR.KzEnvAt D.E ρ))
        ↔ -k ∈ Finset.univ.filter
          (Work.BoseBoxFock.RHi D.F (Work.BoseFixR.KzEnvAt D.E ρ)) := by
      intro k
      have h : ‖D.F.kmom (-k)‖ = ‖D.F.kmom k‖ := by rw [D.F.kmom_neg, norm_neg]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      unfold Work.BoseBoxFock.RHi Work.BoseFixR.KzEnvAt
      rw [h]
    have hcev : ∀ k : D.Mode, Work.BoseBogFS.bogC D.E ρ (-k) = Work.BoseBogFS.bogC D.E ρ k := by
      intro k
      simp only [Work.BoseBogFS.bogC]
      rw [hhat_even k]
    -- the Fock-form bound
    have hK0 : 0 ≤ 16 * D.E.bigM * D.F.normSq f :=
      mul_nonneg (mul_nonneg (by norm_num) hbigM0) hNf
    have hform := Work.BoseBogFS.linHi_form_le D.F
      (Finset.univ.filter (Work.BoseBoxFock.RHi D.F (Work.BoseFixR.KzEnvAt D.E ρ)))
      (fun k => Work.BoseBogFS.bogC D.E ρ k) f (16 * D.E.bigM * D.F.normSq f)
      hSsym hcev hK0 hnorm
    -- the χ̂-decay sum
    have hχsum : (∑ k ∈ Finset.univ.filter
          (Work.BoseBoxFock.RHi D.F (Work.BoseFixR.KzEnvAt D.E ρ)),
        (D.E.hatChi k) ^ 2) ≤ 128 * Cchi ^ 2 * 2 ^ 101 * (Work.BoseFixR.fsX v μ) ^ 1212 := by
      rw [hD]
      exact Work.BoseBoxFock.honest_RHi_hatChi_sq_le hμ hav hChi26 hCchi0 hR1 hviewE
    -- the four factor bounds for the `𝒞`-sum
    have hF3 : Work.BoseBox.fsXp (dil v μ) 3 ≤ 1 :=
      Work.BoseBox.fsXp_le_one hdil0 hdil1 (by norm_num)
    have hden0 : (0 : ℝ) ≤ (2 : ℝ) ^ 14 * Real.pi := by positivity
    have hdenpos : (0 : ℝ) < (2 : ℝ) ^ 14 * Real.pi := by positivity
    have hden1 : (1 : ℝ) ≤ (2 : ℝ) ^ 14 * Real.pi := by
      have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ 14 := by norm_num
      have h3 : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
      exact one_le_mul_of_one_le_of_one_le h2 h3
    have hA0 : 0 ≤ μ * Work.BoseBox.fsXp (dil v μ) 3 / ((2 : ℝ) ^ 14 * Real.pi) :=
      div_nonneg (mul_nonneg hμ.le (Work.BoseBox.fsXp_pos hdil0).le) hden0
    have hAμ : μ * Work.BoseBox.fsXp (dil v μ) 3 / ((2 : ℝ) ^ 14 * Real.pi) ≤ μ := by
      rw [div_le_iff₀ hdenpos]
      have h1 : μ * Work.BoseBox.fsXp (dil v μ) 3 ≤ μ := by
        calc μ * Work.BoseBox.fsXp (dil v μ) 3 ≤ μ * 1 := mul_le_mul_of_nonneg_left hF3 hμ.le
          _ = μ := mul_one μ
      have h2 : μ ≤ μ * ((2 : ℝ) ^ 14 * Real.pi) := le_mul_of_one_le_right hμ.le hden1
      exact le_trans h1 h2
    have hρμ : |ρ - μ| ≤ μ * Work.BoseBox.fsXp (dil v μ) 3 / ((2 : ℝ) ^ 14 * Real.pi) := by
      have h := hρ
      change |ρ - μ| ≤ Work.BoseBoxFock.closeThresholdFS v μ at h
      rwa [Work.BoseBogFS.closeThresholdFS_eq hμ hav] at h
    have hρ2 : ρ ≤ 2 * μ := by
      have h1 : ρ - μ ≤ |ρ - μ| := le_abs_self _
      linarith [hAμ, hρμ]
    have hρ0 : 0 ≤ ρ := by
      have h1 : -(ρ - μ) ≤ |ρ - μ| := neg_le_abs _
      linarith [hρμ, hAμ]
    have hA2 : (ρ - D.E.mu) ^ 2
        ≤ (μ * Work.BoseBox.fsXp (dil v μ) 3 / ((2 : ℝ) ^ 14 * Real.pi)) ^ 2 := by
      rw [hmu_eq, sq_le_sq, abs_of_nonneg hA0]
      exact hρμ
    have hW1zero : |D.E.W1 0| ≤ 16 * Real.pi * a v := by
      obtain ⟨fu', Λ, hΛ, hW1eq⟩ := hW1pin
      have h0 : D.E.W1 0 = uvCut fu' Λ (D.F.kmom 0)
          * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (ell v μ)) (D.F.kmom 0) := by
        rw [hW1eq]
        rfl
      rw [h0]
      calc |uvCut fu' Λ (D.F.kmom 0)
            * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (ell v μ)) (D.F.kmom 0)|
          = |uvCut fu' Λ (D.F.kmom 0)|
            * |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (ell v μ)) (D.F.kmom 0)| :=
            abs_mul _ _
        _ ≤ 1 * |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (ell v μ)) (D.F.kmom 0)| :=
            mul_le_mul_of_nonneg_right (Work.BoseBogFS.abs_uvCut_le_one fu' Λ _) (abs_nonneg _)
        _ = |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (ell v μ)) (D.F.kmom 0)| := one_mul _
        _ ≤ 16 * Real.pi * a v :=
            Work.BoseB7AK.W1rows.W1hat_abs_le hR hℓpos hv hvrad hv_supp h hRℓ (D.F.kmom 0)
    have hW12 : (D.E.W1 0) ^ 2 ≤ (16 * Real.pi * a v) ^ 2 := by
      rw [sq_le_sq, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 16 * Real.pi * a v)]
      exact hW1zero
    have hz2 : (Work.BoseBogFS.bogZ D.E ρ) ^ 2 ≤ 2 * Work.BoseBox.fsXp (dil v μ) (-166) := by
      rw [Work.BoseBogFS.bogZ, Real.sq_sqrt (mul_nonneg hρ0 (pow_nonneg hℓEpos.le 3))]
      have h3 : 0 < D.E.ell ^ 3 := pow_pos hℓEpos 3
      calc ρ * D.E.ell ^ 3 ≤ 2 * μ * D.E.ell ^ 3 := mul_le_mul_of_nonneg_right hρ2 h3.le
        _ = 2 * (D.E.mu * D.E.ell ^ 3) := by rw [hmu_eq]; ring
        _ = 2 * Work.BoseBox.fsXp (dil v μ) (-166) := by rw [hmue]
    have hχ2 : (∑ k ∈ Finset.univ.filter
          (Work.BoseBoxFock.RHi D.F (Work.BoseFixR.KzEnvAt D.E ρ)),
        (D.E.hatChi k) ^ 2) ≤ 128 * Cchi ^ 2 * 2 ^ 101
          * Work.BoseBox.fsXp (dil v μ) 1212 := by
      refine le_trans hχsum ?_
      rw [show (Work.BoseFixR.fsX v μ) ^ 1212 = Work.BoseBox.fsXp (dil v μ) 1212 by
        rw [Work.BoseFixR.fsX, Work.BoseBox.fsXp_pow hdil0.le 1 1212]
        norm_num]
    -- the `𝒞`-sum bound
    have hterm : ∀ k ∈ Finset.univ.filter
          (Work.BoseBoxFock.RHi D.F (Work.BoseFixR.KzEnvAt D.E ρ)),
        (Work.BoseBogFS.bogC D.E ρ k) ^ 2
          ≤ (μ * Work.BoseBox.fsXp (dil v μ) 3 / ((2 : ℝ) ^ 14 * Real.pi)) ^ 2
            * (16 * Real.pi * a v) ^ 2 * (2 * Work.BoseBox.fsXp (dil v μ) (-166))
            * (D.E.hatChi k) ^ 2 := by
      intro k hk
      have h4 : (Work.BoseBogFS.bogC D.E ρ k) ^ 2
          = (ρ - D.E.mu) ^ 2 * (D.E.W1 0) ^ 2 * (Work.BoseBogFS.bogZ D.E ρ) ^ 2
            * (D.E.hatChi k) ^ 2 := by
        rw [Work.BoseBogFS.bogC]; ring
      rw [h4]
      exact Work.BoseBogFS.mul_le_mul4 hA2 hW12 hz2 le_rfl (sq_nonneg _) (sq_nonneg _)
        (sq_nonneg _) (sq_nonneg _) (sq_nonneg _)
        (mul_nonneg (by norm_num) (Work.BoseBox.fsXp_pos hdil0).le)
    have hsumc : (∑ k ∈ Finset.univ.filter
          (Work.BoseBoxFock.RHi D.F (Work.BoseFixR.KzEnvAt D.E ρ)),
        (Work.BoseBogFS.bogC D.E ρ k) ^ 2)
        ≤ (2 : ℝ) ^ 89 * Cchi ^ 2 * μ ^ 2 * (a v) ^ 2
          * Work.BoseBox.fsXp (dil v μ) 1052 := by
      have hpos3 : 0 ≤ (μ * Work.BoseBox.fsXp (dil v μ) 3 / ((2 : ℝ) ^ 14 * Real.pi)) ^ 2
          * (16 * Real.pi * a v) ^ 2 * (2 * Work.BoseBox.fsXp (dil v μ) (-166)) :=
        mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
          (mul_nonneg (by norm_num) (Work.BoseBox.fsXp_pos hdil0).le)
      calc (∑ k ∈ Finset.univ.filter
            (Work.BoseBoxFock.RHi D.F (Work.BoseFixR.KzEnvAt D.E ρ)),
            (Work.BoseBogFS.bogC D.E ρ k) ^ 2)
          ≤ ∑ k ∈ Finset.univ.filter
              (Work.BoseBoxFock.RHi D.F (Work.BoseFixR.KzEnvAt D.E ρ)),
              (μ * Work.BoseBox.fsXp (dil v μ) 3 / ((2 : ℝ) ^ 14 * Real.pi)) ^ 2
                * (16 * Real.pi * a v) ^ 2 * (2 * Work.BoseBox.fsXp (dil v μ) (-166))
                * (D.E.hatChi k) ^ 2 := Finset.sum_le_sum hterm
        _ = (μ * Work.BoseBox.fsXp (dil v μ) 3 / ((2 : ℝ) ^ 14 * Real.pi)) ^ 2
              * (16 * Real.pi * a v) ^ 2 * (2 * Work.BoseBox.fsXp (dil v μ) (-166))
              * (∑ k ∈ Finset.univ.filter
                  (Work.BoseBoxFock.RHi D.F (Work.BoseFixR.KzEnvAt D.E ρ)),
                  (D.E.hatChi k) ^ 2) := by
            rw [Finset.mul_sum]
        _ ≤ (μ * Work.BoseBox.fsXp (dil v μ) 3 / ((2 : ℝ) ^ 14 * Real.pi)) ^ 2
              * (16 * Real.pi * a v) ^ 2 * (2 * Work.BoseBox.fsXp (dil v μ) (-166))
              * (128 * Cchi ^ 2 * 2 ^ 101 * Work.BoseBox.fsXp (dil v μ) 1212) :=
            mul_le_mul_of_nonneg_left hχ2 hpos3
        _ = (2 : ℝ) ^ 89 * Cchi ^ 2 * μ ^ 2 * (a v) ^ 2
              * Work.BoseBox.fsXp (dil v μ) 1052 := by
          have hfs1 : (Work.BoseBox.fsXp (dil v μ) 3) ^ 2
              = Work.BoseBox.fsXp (dil v μ) 6 := by
            rw [Work.BoseBox.fsXp_pow hdil0.le 3 2]; norm_num
          have hfs2 : Work.BoseBox.fsXp (dil v μ) 6
              * Work.BoseBox.fsXp (dil v μ) (-166) * Work.BoseBox.fsXp (dil v μ) 1212
              = Work.BoseBox.fsXp (dil v μ) 1052 := by
            rw [Work.BoseBox.fsXp_mul hdil0, Work.BoseBox.fsXp_mul hdil0]
            congr 1
            norm_num
          calc (μ * Work.BoseBox.fsXp (dil v μ) 3 / ((2 : ℝ) ^ 14 * Real.pi)) ^ 2
                * (16 * Real.pi * a v) ^ 2 * (2 * Work.BoseBox.fsXp (dil v μ) (-166))
                * (128 * Cchi ^ 2 * 2 ^ 101 * Work.BoseBox.fsXp (dil v μ) 1212)
              = (μ ^ 2 / ((2 : ℝ) ^ 14 * Real.pi) ^ 2) * (256 * Real.pi ^ 2 * (a v) ^ 2)
                * (2 * ((Work.BoseBox.fsXp (dil v μ) 3) ^ 2
                    * Work.BoseBox.fsXp (dil v μ) (-166) * Work.BoseBox.fsXp (dil v μ) 1212))
                * (128 * Cchi ^ 2 * 2 ^ 101) := by ring
            _ = (μ ^ 2 / ((2 : ℝ) ^ 14 * Real.pi) ^ 2) * (256 * Real.pi ^ 2 * (a v) ^ 2)
                * (2 * Work.BoseBox.fsXp (dil v μ) 1052)
                * (128 * Cchi ^ 2 * 2 ^ 101) := by rw [hfs1, hfs2]
            _ = (2 : ℝ) ^ 89 * Cchi ^ 2 * μ ^ 2 * (a v) ^ 2
                * Work.BoseBox.fsXp (dil v μ) 1052 := by
              field_simp
              ring
    -- the arithmetic and the assembly
    have hS2nn : 0 ≤ ∑ k ∈ Finset.univ.filter
          (Work.BoseBoxFock.RHi D.F (Work.BoseFixR.KzEnvAt D.E ρ)),
        (Work.BoseBogFS.bogC D.E ρ k) ^ 2 :=
      Finset.sum_nonneg (fun k _ => sq_nonneg _)
    have harith := Work.BoseBogFS.linHi_arith (t := dil v μ) (μ := μ) (a := a v)
      (Cchi := Cchi) (S2 := _) hdil0 hdil1 hμ hav hCchi0 hS2nn hsumc
    have herr : μ * a v ≤ errBracket v R μ := by
      have hX1 : fsX v μ ≤ 1 := by
        rw [Work.BoseFixR.fsX, Work.BoseBox.fsXp]
        exact Real.rpow_le_one hdil0.le hdil1 (by norm_num)
      exact mul_a_le_errBracket hμ hav hR hX1
    have hsq16 : Real.sqrt (16 * D.E.bigM * D.F.normSq f)
        = 4 * (Real.sqrt D.E.bigM * Real.sqrt (D.F.normSq f)) := by
      rw [show (16 : ℝ) * D.E.bigM * D.F.normSq f = 16 * (D.E.bigM * D.F.normSq f) by ring,
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16), Real.sqrt_mul hbigM0]
      norm_num
    have hsqNf : Real.sqrt (D.F.normSq f) * Real.sqrt (D.F.normSq f) = D.F.normSq f :=
      Real.mul_self_sqrt hNf
    have hsqrtM : Real.sqrt D.E.bigM
        = Real.sqrt (Work.BoseBox.fsXp (dil v μ) (-(327 / 4))) := by rw [hbigM]
    have hkey : (2 * Real.sqrt (∑ k ∈ Finset.univ.filter
            (Work.BoseBoxFock.RHi D.F (Work.BoseFixR.KzEnvAt D.E ρ)),
            (Work.BoseBogFS.bogC D.E ρ k) ^ 2))
          * (4 * (Real.sqrt D.E.bigM * Real.sqrt (D.F.normSq f)))
          * Real.sqrt (D.F.normSq f)
        = 8 * Real.sqrt (∑ k ∈ Finset.univ.filter
            (Work.BoseBoxFock.RHi D.F (Work.BoseFixR.KzEnvAt D.E ρ)),
            (Work.BoseBogFS.bogC D.E ρ k) ^ 2)
          * Real.sqrt D.E.bigM * D.F.normSq f := by
      rw [show (2 * Real.sqrt (∑ k ∈ Finset.univ.filter
              (Work.BoseBoxFock.RHi D.F (Work.BoseFixR.KzEnvAt D.E ρ)),
              (Work.BoseBogFS.bogC D.E ρ k) ^ 2))
            * (4 * (Real.sqrt D.E.bigM * Real.sqrt (D.F.normSq f)))
            * Real.sqrt (D.F.normSq f)
          = 8 * Real.sqrt (∑ k ∈ Finset.univ.filter
              (Work.BoseBoxFock.RHi D.F (Work.BoseFixR.KzEnvAt D.E ρ)),
              (Work.BoseBogFS.bogC D.E ρ k) ^ 2) * Real.sqrt D.E.bigM
            * (Real.sqrt (D.F.normSq f) * Real.sqrt (D.F.normSq f)) by ring, hsqNf]
    have h8 : 8 * Real.sqrt (∑ k ∈ Finset.univ.filter
          (Work.BoseBoxFock.RHi D.F (Work.BoseFixR.KzEnvAt D.E ρ)),
          (Work.BoseBogFS.bogC D.E ρ k) ^ 2) * Real.sqrt D.E.bigM
        ≤ ((2 : ℝ) ^ 48 * Cchi + 1) * (μ * a v) := by
      rw [hsqrtM]
      exact harith
    have hC0 : 0 ≤ (2 : ℝ) ^ 48 * Cchi + 1 := by linarith [hCchi0]
    show |D.F.qw f (∑ k ∈ Finset.univ.filter
          (Work.BoseBoxFock.RHi D.F (Work.BoseFixR.KzEnvAt D.E ρ)),
          ((1 / 2 : ℝ) * Work.BoseBogFS.bogC D.E ρ k) •
            (D.F.a k + D.F.aDag k + D.F.a (-k) + D.F.aDag (-k)))|
        ≤ ((2 : ℝ) ^ 48 * Cchi + 1) * errBracket v R μ * D.F.normSq f
    rw [Work.BoseB7.FockData.qw]
    calc |D.F.bp ((∑ k ∈ Finset.univ.filter
            (Work.BoseBoxFock.RHi D.F (Work.BoseFixR.KzEnvAt D.E ρ)),
            ((1 / 2 : ℝ) * Work.BoseBogFS.bogC D.E ρ k) •
              (D.F.a k + D.F.aDag k + D.F.a (-k) + D.F.aDag (-k))) f) f|
        ≤ 2 * Real.sqrt (∑ k ∈ Finset.univ.filter
              (Work.BoseBoxFock.RHi D.F (Work.BoseFixR.KzEnvAt D.E ρ)),
              (Work.BoseBogFS.bogC D.E ρ k) ^ 2)
            * Real.sqrt (16 * D.E.bigM * D.F.normSq f)
            * Real.sqrt (D.F.normSq f) := hform
      _ = 8 * Real.sqrt (∑ k ∈ Finset.univ.filter
              (Work.BoseBoxFock.RHi D.F (Work.BoseFixR.KzEnvAt D.E ρ)),
              (Work.BoseBogFS.bogC D.E ρ k) ^ 2)
            * Real.sqrt D.E.bigM * D.F.normSq f := by rw [hsq16, hkey]
      _ ≤ ((2 : ℝ) ^ 48 * Cchi + 1) * (μ * a v) * D.F.normSq f :=
          mul_le_mul_of_nonneg_right h8 hNf
      _ ≤ ((2 : ℝ) ^ 48 * Cchi + 1) * errBracket v R μ * D.F.normSq f :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left herr hC0) hNf

end Work.BoseBogFS
