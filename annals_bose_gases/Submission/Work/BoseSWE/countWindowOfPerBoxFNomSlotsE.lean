import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseSWE.LedgerNomEUnif
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseSWE

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal
open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB Work.BoseFixB1
open Work.SmallBoxSliding

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-! ## The diluteness arithmetic behind the absorption of the error slot

`Work.BoseSWE.LedgerNomEUnif` hands back the error coefficient `E'` of its error slot as part of an
existential, so it is an ordinary real number produced by the hypothesis, not a constant we may
choose.  The twin `Work.BoseB1Cube.countWindowOfNominal` chooses that coefficient (`EF`) *before*
running the ledger, and discharges the absorption hypothesis
`C₀·EF·κ·(1 + 2μ(a v)ℓ²/b) ≤ 1/2` of `Work.BoseB1Cube.nomCountArith` by the identity
`(C₀·EF)(1 + 2/b) = C₀/(2M₀)`.  Here the same absorption is discharged by *shrinking the output
threshold* `ε₀` of `CountWindow`: with `t := μ(a v)³ ≤ ε₀`,

    C₀·E'·κ·(1 + 2μ(a v)ℓ²/b)
      = C₀·E'·(t^{287/646} + (2/b)·t^{281/646})
      ≤ C₀·E'·(1 + 2/b)·ε₀^{281/646} ≤ 1/2

for `ε₀` small enough, since `κ = t^{287/646}` and `μ(a v)ℓ²κ = t^{281/646}` both vanish with the
diluteness (the two identities below, from FS's parameter block). -/

/-- `κ = K_B³ (μ(a v)³)^{1/2} = (μ(a v)³)^{287/646}`. -/
lemma kappa_eq_rpow {v : E3 → ℝ} {μ : ℝ} (hav : 0 < a v) (hμ : 0 < μ) :
    Work.BoseB1Cube.kappa v μ = (μ * (a v) ^ 3) ^ (287 / 646 : ℝ) := by
  rw [Work.BoseB1Cube.kappa, Work.BoseFixB1.KB3_half_eq hav hμ, Work.BoseBox.fsXp]
  congr 1
  norm_num

/-- `μ(a v)ℓ²κ = Kl²·κ = (μ(a v)³)^{281/646}`. -/
lemma mu_a_ell_sq_kappa_eq {v : E3 → ℝ} {μ : ℝ} (hav : 0 < a v) (hμ : 0 < μ) :
    μ * (a v) * (sideAt μ (a v)) ^ 2 * Work.BoseB1Cube.kappa v μ
      = (μ * (a v) ^ 3) ^ (281 / 646 : ℝ) := by
  have ht0 : 0 < μ * (a v) ^ 3 := by positivity
  rw [Work.BoseFixB1.mu_mul_a_mul_ell_sq μ (a v) hμ hav, Work.BoseB1Cube.kappa,
    Work.BoseFixB1.KB3_half_eq hav hμ, Work.BoseFixB1.Kl_eq_fsXp μ (a v),
    Work.BoseBox.fsXp_pow ht0.le, Work.BoseBox.fsXp_mul ht0, Work.BoseBox.fsXp]
  norm_num

/-- **The absorption of the error slot.**  For every fixed `C₀, EF ≥ 0` and `b > 0` there is a
threshold `δ ∈ (0,1]` such that the absorption hypothesis of `Work.BoseB1Cube.nomCountArith`
holds at every diluteness `μ(a v)³ ≤ δ`. -/
lemma exists_delta_absorb {v : E3 → ℝ} {b C₀ EF : ℝ} (hav : 0 < a v) (hb : 0 < b)
    (hC₀ : 0 ≤ C₀) (hEF : 0 ≤ EF) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ μ : ℝ, 0 < μ → μ * (a v) ^ 3 ≤ δ →
      C₀ * EF * Work.BoseB1Cube.kappa v μ
        * (1 + 2 * (μ * (a v) * (sideAt μ (a v)) ^ 2) / b) ≤ 1 / 2 := by
  set A : ℝ := (1 + 2 / b) * C₀ * EF with hAdef
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  have h2A1 : 0 < 2 * A + 1 := by linarith
  set δ : ℝ := (2 * A + 1) ^ (-(646 / 281) : ℝ) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; exact Real.rpow_pos_of_pos h2A1 _
  have hδle1 : δ ≤ 1 := by
    rw [hδdef]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  have hδpow : δ ^ (281 / 646 : ℝ) = (2 * A + 1)⁻¹ := by
    rw [hδdef, ← Real.rpow_mul h2A1.le,
      show (-(646 / 281)) * (281 / 646) = -(1 : ℝ) by norm_num,
      Real.rpow_neg h2A1.le, Real.rpow_one]
  refine ⟨δ, hδpos, hδle1, ?_⟩
  intro μ hμ ht
  have ht0 : 0 < μ * (a v) ^ 3 := by positivity
  have htle1 : μ * (a v) ^ 3 ≤ 1 := le_trans ht hδle1
  have h2b : (0 : ℝ) ≤ 2 / b := by positivity
  have htk : (μ * (a v) ^ 3) ^ (287 / 646 : ℝ) ≤ (μ * (a v) ^ 3) ^ (281 / 646 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge ht0 htle1 (by norm_num)
  have hinner : (μ * (a v) ^ 3) ^ (287 / 646 : ℝ)
        + (2 / b) * (μ * (a v) ^ 3) ^ (281 / 646 : ℝ)
      ≤ (1 + 2 / b) * (μ * (a v) ^ 3) ^ (281 / 646 : ℝ) := by
    calc (μ * (a v) ^ 3) ^ (287 / 646 : ℝ)
          + (2 / b) * (μ * (a v) ^ 3) ^ (281 / 646 : ℝ)
        ≤ (μ * (a v) ^ 3) ^ (281 / 646 : ℝ)
            + (2 / b) * (μ * (a v) ^ 3) ^ (281 / 646 : ℝ) := add_le_add htk le_rfl
      _ = (1 + 2 / b) * (μ * (a v) ^ 3) ^ (281 / 646 : ℝ) := by ring
  calc C₀ * EF * Work.BoseB1Cube.kappa v μ
        * (1 + 2 * (μ * (a v) * (sideAt μ (a v)) ^ 2) / b)
      = C₀ * EF * ((μ * (a v) ^ 3) ^ (287 / 646 : ℝ)
          + (2 / b) * (μ * (a v) * (sideAt μ (a v)) ^ 2
              * Work.BoseB1Cube.kappa v μ)) := by
        rw [kappa_eq_rpow hav hμ]; ring
      _ = C₀ * EF * ((μ * (a v) ^ 3) ^ (287 / 646 : ℝ)
          + (2 / b) * (μ * (a v) ^ 3) ^ (281 / 646 : ℝ)) := by
        rw [mu_a_ell_sq_kappa_eq hav hμ]
      _ ≤ C₀ * EF * ((1 + 2 / b) * (μ * (a v) ^ 3) ^ (281 / 646 : ℝ)) :=
        mul_le_mul_of_nonneg_left hinner (mul_nonneg hC₀ hEF)
      _ = A * (μ * (a v) ^ 3) ^ (281 / 646 : ℝ) := by rw [hAdef]; ring
      _ ≤ A * δ ^ (281 / 646 : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ht0.le ht (by norm_num)) hA0
      _ = A * (2 * A + 1)⁻¹ := by rw [hδpow]
      _ ≤ 1 / 2 := by
        rw [show A * (2 * A + 1)⁻¹ = A / (2 * A + 1) by ring, div_le_iff₀ h2A1]
        linarith

/-- **F4b of the `BoseSWE` route**: FS `eq:apriorinn+`'s count window from the two-slot row with
the slack.  Recipe (`Submission/Work/BoseSWE/BRIEF.md` §9): copy
`Work.BoseB1Cube.countWindowOfNominal` (`Submission/Work/BoseB1Cube/countWindowOfNominal.lean`),
which consumes the PROVED `Work.BoseB1Cube.ledgerNom`; here the ledger is taken as the *hypothesis*
`hLed : Work.BoseSWE.LedgerNomEUnif v h R` (the a-priori ledger with the slack, stated as a `Prop`
in its row parameters), so that this proof does not depend on the ledger file — the instance
`fun c₁ C E CE h1 h2 h3 h4 row hSgood => Work.BoseSWE.ledgerNomE …` is supplied by the area owner.

NOTE ON THE ERROR SLOT (answering a reviewer concern): `hLed` returns the coefficient `E'` as part
of an existential, so inside the proof `E'` is an ordinary real *term* (obtained from the
hypothesis applied at the constants extracted from `hN`); the output threshold `ε₀` of
`CountWindow` **may depend on it** (the `∃ ε₀ C` of `CountWindow` is the proof's to choose), and the
absorption hypothesis of the twinned `nomCountArith` (`C₀·E'·κ·(1 + 2μaℓ²/b) ≤ 1/2`) is then
discharged by shrinking `ε₀`: `κ = (μ(a v)³)^{287/646}` and `μaℓ²κ ≤ 1` on the regime, so the whole
bracket is `≤ C₀E'·(const)·ε₀^{287/646} ≤ 1/2`.  The extra `−ErrE·‖Φ‖²` term is `n`-proportional,
so the rest of the absorption is the twin's. -/
theorem countWindowOfPerBoxFNomSlotsE {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v)
    (hS : Work.BoseB1Cube.SlidingGoodCube v h)
    (hLed : Work.BoseSWE.LedgerNomEUnif v h R)
    (hN : Work.BoseSWE.PerBoxFNomSlotsE v h R) :
    Work.BoseB1Cube.CountWindow v h := by
  classical
  obtain ⟨εN, c₁, C, CE, hεN, hc₁, hC, hCE, hper⟩ := hN
  obtain ⟨εA, C₀, hεA, hC₀, habs⟩ :=
    Work.BoseB1Cube.nomCountAbsorb (v := v) h hv hvrad hR hv_supp hav
  have hbpos : 0 < Work.BoseBox.bValue := by norm_num [Work.BoseBox.bValue]
  have h1bpos : 0 < 1 + 2 / Work.BoseBox.bValue := by positivity
  -- the a-priori ledger with the slack, at the row parameters extracted from `hN` and at the
  -- prescribed error slot `E = 1`; its output error coefficient is the existential `E'`
  obtain ⟨εL, C_A, E', hεL, hC_A, hE'nn, hled⟩ :=
    hLed c₁ C 1 CE hc₁ hC one_pos hCE ⟨εN, hεN, hper⟩ hS
  -- the common error coefficient of the two rows fed to the count arithmetic
  set EF : ℝ := max (E' / c₁) E' with hEFdef
  have hEFnn : 0 ≤ EF := le_trans (div_nonneg hE'nn hc₁.le) (le_max_left _ _)
  -- the threshold at which the error slot is absorbed into the mean-field scale
  obtain ⟨δ, hδpos, hδle1, habsorb⟩ :=
    exists_delta_absorb (v := v) (b := Work.BoseBox.bValue) hav hbpos hC₀ hEFnn
  refine ⟨min (min εN εA) (min εL δ),
    2 * C₀ * (1 + (max (C_A / c₁) C_A) * (1 + 2 / Work.BoseBox.bValue)), ?_, ?_, ?_⟩
  · exact lt_min (lt_min hεN hεA) (lt_min hεL hδpos)
  · have hCA1 : 0 ≤ C_A / c₁ := div_nonneg hC_A hc₁.le
    have hCA2 : 0 ≤ max (C_A / c₁) C_A := le_trans hCA1 (le_max_left _ _)
    have h1b : 0 ≤ 1 + 2 / Work.BoseBox.bValue := le_of_lt h1bpos
    have h2 : 0 ≤ (max (C_A / c₁) C_A) * (1 + 2 / Work.BoseBox.bValue) := mul_nonneg hCA2 h1b
    exact mul_nonneg (mul_nonneg (by norm_num) hC₀) (by linarith)
  · intro J μ hAdm hJK n Φ hNpos hlow
    have hμ : 0 < μ := Work.BoseFixB1.adm_mu_pos hAdm
    have hℓ : 0 < sideAt μ (a v) := Work.BoseFixB1.adm_ell_pos hAdm
    have hAdmA : Adm v εA μ :=
      Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_left _ _) (min_le_right _ _))
    have hAdmL : Adm v εL μ :=
      Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_right _ _) (min_le_left _ _))
    have hAdmδ : Adm v δ μ :=
      Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_right _ _) (min_le_right _ _))
    have hAdm1 : Adm v 1 μ := Work.BoseFixB1.Adm.mono hAdmδ hδle1
    have ht1 : μ * (a v) ^ 3 ≤ 1 := Work.BoseFixB1.adm_dilute_le_one hAdm1 le_rfl
    have htδ : μ * (a v) ^ 3 ≤ δ := hAdmδ.2.1
    obtain ⟨hrow1, hrow2⟩ := hled J μ hAdmL hJK n Φ hNpos hlow
    have hNnn : 0 ≤ normB v μ n (Φ : X n → ℝ) := Work.BoseFixB1.normB_nonneg _
    have hκnn : 0 ≤ Work.BoseB1Cube.kappa v μ := Work.BoseB1Cube.kappa_nonneg hμ hav
    have hκ1 : Work.BoseB1Cube.kappa v μ ≤ 1 := Work.BoseB1Cube.kappa_le_one hμ hav ht1
    have hKl : μ * (a v) * (sideAt μ (a v)) ^ 2 * Work.BoseB1Cube.kappa v μ ≤ 1 :=
      Work.BoseB1Cube.mu_a_ell_sq_kappa_le_one hμ hav ht1
    have hDnn : 0 ≤ μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3 * Work.BoseB1Cube.kappa v μ :=
      mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg μ) hav.le) (pow_nonneg hℓ.le 3)) hκnn
    have hFnn : 0 ≤ μ * (a v) * Work.BoseB1Cube.kappa v μ :=
      mul_nonneg (mul_nonneg hμ.le hav.le) hκnn
    have hcPnn : 0 ≤ cnPlus (sideAt μ (a v)) (Φ : X n → ℝ) := by
      rw [Submission.BoseGases.cnPlus]
      exact Finset.sum_nonneg fun i _ => MeasureTheory.integral_nonneg fun x => sq_nonneg _
    -- the two coefficient comparisons coming from the choice of `EF`
    have hE1 : E' / c₁ ≤ EF := le_max_left _ _
    have hE2 : E' ≤ EF := le_max_right _ _
    have hrow1' : Work.BoseB1Cube.nomRPsi h μ (Φ : X n → ℝ)
        ≤ max (C_A / c₁) C_A
            * (μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3 * Work.BoseB1Cube.kappa v μ)
            * normB v μ n (Φ : X n → ℝ)
          + EF * (μ * (a v) * Work.BoseB1Cube.kappa v μ) * (n : ℝ)
              * normB v μ n (Φ : X n → ℝ) := by
      have hmul := mul_le_mul_of_nonneg_left hrow1 (by positivity : (0 : ℝ) ≤ 1 / c₁)
      have e1 : (1 / c₁) * (c₁ * Work.BoseB1Cube.nomRPsi h μ (Φ : X n → ℝ))
          = Work.BoseB1Cube.nomRPsi h μ (Φ : X n → ℝ) := by
        field_simp
      have e2 : (1 / c₁) * (C_A * (μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3
                * Work.BoseB1Cube.kappa v μ)
              * normB v μ n (Φ : X n → ℝ)
            + E' * (μ * (a v) * Work.BoseB1Cube.kappa v μ) * (n : ℝ)
                * normB v μ n (Φ : X n → ℝ))
          = (C_A / c₁) * (μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3
                * Work.BoseB1Cube.kappa v μ)
              * normB v μ n (Φ : X n → ℝ)
            + (E' / c₁) * (μ * (a v) * Work.BoseB1Cube.kappa v μ) * (n : ℝ)
                * normB v μ n (Φ : X n → ℝ) := by
        ring
      rw [e1, e2] at hmul
      have h1 : (C_A / c₁) * (μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3
              * Work.BoseB1Cube.kappa v μ)
            * normB v μ n (Φ : X n → ℝ)
          ≤ max (C_A / c₁) C_A * (μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3
              * Work.BoseB1Cube.kappa v μ)
            * normB v μ n (Φ : X n → ℝ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_left _ _) hDnn) hNnn
      have h3 : (E' / c₁) * (μ * (a v) * Work.BoseB1Cube.kappa v μ) * (n : ℝ)
            * normB v μ n (Φ : X n → ℝ)
          ≤ EF * (μ * (a v) * Work.BoseB1Cube.kappa v μ) * (n : ℝ)
              * normB v μ n (Φ : X n → ℝ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hE1 hFnn)
            (Nat.cast_nonneg n)) hNnn
      set_option maxRecDepth 4000 in
      linarith [hmul, h1, h3]
    have hrow2' : ((paramsAt μ (a v)).b / (2 * (sideAt μ (a v)) ^ 2))
          * cnPlus (sideAt μ (a v)) (Φ : X n → ℝ)
        ≤ max (C_A / c₁) C_A
            * (μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3 * Work.BoseB1Cube.kappa v μ)
            * normB v μ n (Φ : X n → ℝ)
          + EF * (μ * (a v) * Work.BoseB1Cube.kappa v μ) * (n : ℝ)
              * normB v μ n (Φ : X n → ℝ) := by
      have h1 : C_A * (μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3 * Work.BoseB1Cube.kappa v μ)
            * normB v μ n (Φ : X n → ℝ)
          ≤ max (C_A / c₁) C_A * (μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3
              * Work.BoseB1Cube.kappa v μ)
            * normB v μ n (Φ : X n → ℝ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right _ _) hDnn) hNnn
      have h3 : E' * (μ * (a v) * Work.BoseB1Cube.kappa v μ) * (n : ℝ)
            * normB v μ n (Φ : X n → ℝ)
          ≤ EF * (μ * (a v) * Work.BoseB1Cube.kappa v μ) * (n : ℝ)
              * normB v μ n (Φ : X n → ℝ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hE2 hFnn)
            (Nat.cast_nonneg n)) hNnn
      have h4 : ((paramsAt μ (a v)).b / (2 * (sideAt μ (a v)) ^ 2))
            * cnPlus (sideAt μ (a v)) (Φ : X n → ℝ)
          ≤ max (C_A / c₁) C_A
              * (μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3 * Work.BoseB1Cube.kappa v μ)
              * normB v μ n (Φ : X n → ℝ)
            + EF * (μ * (a v) * Work.BoseB1Cube.kappa v μ) * (n : ℝ)
                * normB v μ n (Φ : X n → ℝ) := by
        set_option maxRecDepth 4000 in
        linarith [hrow2, h1, h3]
      rw [Work.BoseFixB1.paramsAt_b_eq μ (a v)] at h4
      exact h4
    -- the error slot is absorbed because the diluteness is below `δ`
    have hsmall : C₀ * EF * Work.BoseB1Cube.kappa v μ
        * (1 + 2 * (μ * (a v) * (sideAt μ (a v)) ^ 2) / Work.BoseBox.bValue) ≤ 1 / 2 :=
      habsorb μ hμ htδ
    exact Work.BoseB1Cube.nomCountArith (μ := μ) (a := a v) (ℓ := sideAt μ (a v))
      (κ := Work.BoseB1Cube.kappa v μ) (b := Work.BoseBox.bValue) (C₀ := C₀)
      (C_A := max (C_A / c₁) C_A) (E := EF) (n := n)
      (N := normB v μ n (Φ : X n → ℝ))
      (R := Work.BoseB1Cube.nomRPsi h μ (Φ : X n → ℝ))
      (cP := cnPlus (sideAt μ (a v)) (Φ : X n → ℝ))
      hμ hav hℓ hbpos hC₀ (le_trans (div_nonneg hC_A hc₁.le) (le_max_left _ _)) hEFnn
      hNpos hcPnn hκnn hκ1 hKl hsmall (habs μ hAdmA n Φ) hrow1' hrow2'

end Work.BoseSWE
