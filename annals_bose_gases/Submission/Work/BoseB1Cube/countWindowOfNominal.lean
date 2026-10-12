import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB1Cube.nomCountAbsorb
import Submission.Work.BoseB1Cube.nomCountArith
import Submission.Work.BoseB1Cube.nomLedger
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB1Cube

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB Work.BoseFixB1
open Work.SmallBoxSliding

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-- `κ = K_B³(μ(a v)³)^{1/2}` is nonnegative, at FS's parameters. -/
lemma kappa_nonneg {v : E3 → ℝ} {μ : ℝ} (hμ : 0 < μ) (hav : 0 < a v) :
    0 ≤ kappa v μ := by
  have ht : 0 < μ * (a v) ^ 3 := mul_pos hμ (pow_pos hav 3)
  have hKB : 0 ≤ (Work.BoseBox.paramsAt μ (a v)).KB := by
    rw [Work.BoseFixB1.KB_eq_fsXp μ (a v)]
    exact Work.BoseBox.fsXp_nonneg (t := μ * (a v) ^ 3) (c := -6) ht.le
  unfold Work.BoseB1Cube.kappa
  exact mul_nonneg (pow_nonneg hKB 3) (Real.rpow_nonneg ht.le _)

/-- `κ ≤ 1` for diluteness `μ(a v)³ ≤ 1`, since `κ = (μa³)^{287/646}`. -/
lemma kappa_le_one {v : E3 → ℝ} {μ : ℝ} (hμ : 0 < μ) (hav : 0 < a v)
    (ht1 : μ * (a v) ^ 3 ≤ 1) : kappa v μ ≤ 1 :=
  Work.BoseFixB1.kb3_half_le_one hav hμ ht1

/-- `μ·(a v)·ℓ²·κ ≤ 1` for diluteness `μ(a v)³ ≤ 1`, since
`μaℓ²κ = (μa³)^{281/646}`. -/
lemma mu_a_ell_sq_kappa_le_one {v : E3 → ℝ} {μ : ℝ} (hμ : 0 < μ) (hav : 0 < a v)
    (ht1 : μ * (a v) ^ 3 ≤ 1) :
    μ * (a v) * (sideAt μ (a v)) ^ 2 * kappa v μ ≤ 1 := by
  have ht : 0 < μ * (a v) ^ 3 := mul_pos hμ (pow_pos hav 3)
  have hKl : μ * (a v) * (sideAt μ (a v)) ^ 2 = (Work.BoseBox.paramsAt μ (a v)).Kl ^ 2 :=
    Work.BoseFixB1.mu_mul_a_mul_ell_sq μ (a v) hμ hav
  unfold Work.BoseB1Cube.kappa
  calc μ * (a v) * (sideAt μ (a v)) ^ 2
        * ((Work.BoseBox.paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
      = (Work.BoseBox.fsXp (μ * (a v) ^ 3) (-(3 / 2))) ^ 2
          * Work.BoseBox.fsXp (μ * (a v) ^ 3) (287 / 2) := by
        rw [hKl, Work.BoseFixB1.KB3_half_eq hav hμ, Work.BoseFixB1.Kl_eq_fsXp μ (a v)]
    _ = Work.BoseBox.fsXp (μ * (a v) ^ 3) (-3)
          * Work.BoseBox.fsXp (μ * (a v) ^ 3) (287 / 2) := by
        rw [Work.BoseBox.fsXp_pow ht.le (-(3 / 2)) 2]
        congr 1
        norm_num
    _ = Work.BoseBox.fsXp (μ * (a v) ^ 3) (-3 + 287 / 2) :=
        Work.BoseBox.fsXp_mul ht (-3) (287 / 2)
    _ = Work.BoseBox.fsXp (μ * (a v) ^ 3) (281 / 2) := by
        congr 1
        norm_num
    _ ≤ 1 := Work.BoseBox.fsXp_le_one ht ht1 (by norm_num)

/-- `(paramsAt μ a).b = bValue`. -/
lemma paramsAt_b_eq' (μ a : ℝ) : (Work.BoseBox.paramsAt μ a).b = Work.BoseBox.bValue :=
  Work.BoseFixB1.paramsAt_b_eq μ a

/-- FS `thm:aprioriHLambda` at the nominal spelling: the low-state count window from FS's own
localisation over `goodSet` (`SlidingGoodCube`, with the chemical-potential slot `m(u)μ`) plus
`PerBoxFNom` (FS `thm:smallbox` in the nominal/indicator-count spelling) at the two slots
`μp = μ` (the `F`-row on `I₋`) and `μp = 4μ` (the rough layer bound on `goodSet ∖ interiorSet`).
This is FS l.4050-4200 minus the two on-disk PROVED steps (the convexity `U`-argument, mirroring
`countAbsorb_holds`, and the arithmetic, mirroring `windowBridge_holds`).  It needs neither the
outer band nor `hcount`/`(R1)`/`(R2)`.  Recipe and provenance:
`FINDING_cubeCrudeBand_session5.md` §9/§9bis/§11. -/
theorem countWindowOfNominal {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v)
    (hS : Work.BoseB1Cube.SlidingGoodCube v h)
    (hN : ∃ ε₀ c₁ C : ℝ, 0 < ε₀ ∧ 0 < c₁ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
          (u : EuclideanSpace ℝ (Fin 3)),
          u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
          ∀ μp : ℝ, (μp = μ ∨ μp = 4 * μ) →
            Work.BoseB1Cube.PerBoxFNom v h R c₁ C μp μ n Φ u) :
    Work.BoseB1Cube.CountWindow v h := by
  classical
  obtain ⟨εN, c₁, C, hεN, hc₁, hC, hper⟩ := hN
  obtain ⟨εA, C₀, hεA, hC₀, habs⟩ := nomCountAbsorb (v := v) h hv hvrad hR hv_supp hav
  have hbpos : 0 < Work.BoseBox.bValue := by norm_num [Work.BoseBox.bValue]
  have hbne : Work.BoseBox.bValue ≠ 0 := ne_of_gt hbpos
  have h1bpos : 0 < 1 + 2 / Work.BoseBox.bValue := by positivity
  have h1bne : (1 + 2 / Work.BoseBox.bValue) ≠ 0 := ne_of_gt h1bpos
  set M₀ : ℝ := max C₀ 1 with hM₀def
  have hM₀pos : 0 < M₀ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hM₀ne : M₀ ≠ 0 := ne_of_gt hM₀pos
  have hC₀M₀ : C₀ ≤ M₀ := le_max_left _ _
  -- the final coefficient of the excited count `n₊`
  set EF : ℝ := 1 / (2 * M₀ * (1 + 2 / Work.BoseBox.bValue)) with hEFdef
  have hEFnn : 0 ≤ EF := by rw [hEFdef]; positivity
  -- the chemical-potential slot fed to the ledger: `E ≤ EF` and `E / c₁ ≤ EF`
  set E : ℝ := EF * min c₁ 1 with hEdef
  have hEpos : 0 < E := by rw [hEdef]; positivity
  have hc₁ne : c₁ ≠ 0 := ne_of_gt hc₁
  obtain ⟨εL, C_A, hεL, hC_A, hled⟩ :=
    ledgerNom (v := v) h hv hv1 hvrad hR hv_supp hav hc₁ hC hEpos ⟨εN, hεN, hper⟩ hS
  refine ⟨min (min εN εA) (min εL 1),
    2 * C₀ * (1 + (max (C_A / c₁) C_A) * (1 + 2 / Work.BoseBox.bValue)), ?_, ?_, ?_⟩
  · exact lt_min (lt_min hεN hεA) (lt_min hεL one_pos)
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
    have hAdm1 : Adm v 1 μ :=
      Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_right _ _) (min_le_right _ _))
    have ht1 : μ * (a v) ^ 3 ≤ 1 := Work.BoseFixB1.adm_dilute_le_one hAdm1 le_rfl
    obtain ⟨hrow1, hrow2⟩ := hled J μ hAdmL hJK n Φ hNpos hlow
    have hNnn : 0 ≤ normB v μ n (Φ : X n → ℝ) := Work.BoseFixB1.normB_nonneg _
    have hκnn : 0 ≤ kappa v μ := kappa_nonneg hμ hav
    have hκ1 : kappa v μ ≤ 1 := kappa_le_one hμ hav ht1
    have hKl : μ * (a v) * (sideAt μ (a v)) ^ 2 * kappa v μ ≤ 1 :=
      mu_a_ell_sq_kappa_le_one hμ hav ht1
    have hDnn : 0 ≤ μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3 * kappa v μ :=
      mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg μ) hav.le) (pow_nonneg hℓ.le 3)) hκnn
    have hFnn : 0 ≤ μ * (a v) * kappa v μ :=
      mul_nonneg (mul_nonneg hμ.le hav.le) hκnn
    have hcPnn : 0 ≤ cnPlus (sideAt μ (a v)) (Φ : X n → ℝ) := by
      rw [Submission.BoseGases.cnPlus]
      exact Finset.sum_nonneg fun i _ => MeasureTheory.integral_nonneg fun x => sq_nonneg _
    -- the two coefficient comparisons coming from the choice of `E`
    have hE2 : E ≤ EF := by
      rw [hEdef]
      calc EF * min c₁ 1 ≤ EF * 1 := mul_le_mul_of_nonneg_left (min_le_right _ _) hEFnn
        _ = EF := by ring
    have hE1 : E / c₁ ≤ EF := by
      rw [hEdef, div_le_iff₀ hc₁]
      calc EF * min c₁ 1 ≤ EF * c₁ := mul_le_mul_of_nonneg_left (min_le_left _ _) hEFnn
        _ = EF * c₁ := rfl
    have hrow1' : nomRPsi h μ (Φ : X n → ℝ)
        ≤ max (C_A / c₁) C_A
            * (μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3 * kappa v μ)
            * normB v μ n (Φ : X n → ℝ)
          + EF * (μ * (a v) * kappa v μ) * (n : ℝ) * normB v μ n (Φ : X n → ℝ) := by
      have hmul := mul_le_mul_of_nonneg_left hrow1 (by positivity : (0 : ℝ) ≤ 1 / c₁)
      have e1 : (1 / c₁) * (c₁ * nomRPsi h μ (Φ : X n → ℝ)) = nomRPsi h μ (Φ : X n → ℝ) := by
        field_simp
      have e2 : (1 / c₁) * (C_A * (μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3 * kappa v μ)
              * normB v μ n (Φ : X n → ℝ)
            + E * (μ * (a v) * kappa v μ) * (n : ℝ) * normB v μ n (Φ : X n → ℝ))
          = (C_A / c₁) * (μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3 * kappa v μ)
              * normB v μ n (Φ : X n → ℝ)
            + (E / c₁) * (μ * (a v) * kappa v μ) * (n : ℝ) * normB v μ n (Φ : X n → ℝ) := by
        ring
      rw [e1, e2] at hmul
      have h1 : (C_A / c₁) * (μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3 * kappa v μ)
            * normB v μ n (Φ : X n → ℝ)
          ≤ max (C_A / c₁) C_A * (μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3 * kappa v μ)
            * normB v μ n (Φ : X n → ℝ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_left _ _) hDnn) hNnn
      have h3 : (E / c₁) * (μ * (a v) * kappa v μ) * (n : ℝ) * normB v μ n (Φ : X n → ℝ)
          ≤ EF * (μ * (a v) * kappa v μ) * (n : ℝ) * normB v μ n (Φ : X n → ℝ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hE1 hFnn)
            (Nat.cast_nonneg n)) hNnn
      set_option maxRecDepth 4000 in
      linarith [hmul, h1, h3]
    have hrow2' : (Work.BoseBox.bValue / (2 * (sideAt μ (a v)) ^ 2))
          * cnPlus (sideAt μ (a v)) (Φ : X n → ℝ)
        ≤ max (C_A / c₁) C_A
            * (μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3 * kappa v μ)
            * normB v μ n (Φ : X n → ℝ)
          + EF * (μ * (a v) * kappa v μ) * (n : ℝ) * normB v μ n (Φ : X n → ℝ) := by
      have h1 : C_A * (μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3 * kappa v μ)
            * normB v μ n (Φ : X n → ℝ)
          ≤ max (C_A / c₁) C_A * (μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3 * kappa v μ)
            * normB v μ n (Φ : X n → ℝ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right _ _) hDnn) hNnn
      have h3 : E * (μ * (a v) * kappa v μ) * (n : ℝ) * normB v μ n (Φ : X n → ℝ)
          ≤ EF * (μ * (a v) * kappa v μ) * (n : ℝ) * normB v μ n (Φ : X n → ℝ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hE2 hFnn)
            (Nat.cast_nonneg n)) hNnn
      have h4 : ((paramsAt μ (a v)).b / (2 * (sideAt μ (a v)) ^ 2))
            * cnPlus (sideAt μ (a v)) (Φ : X n → ℝ)
          ≤ max (C_A / c₁) C_A
              * (μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3 * kappa v μ)
              * normB v μ n (Φ : X n → ℝ)
            + EF * (μ * (a v) * kappa v μ) * (n : ℝ) * normB v μ n (Φ : X n → ℝ) := by
        set_option maxRecDepth 4000 in
        linarith [hrow2, h1, h3]
      rw [Work.BoseFixB1.paramsAt_b_eq μ (a v)] at h4
      exact h4
    -- `κ(1 + 2 μaℓ²/b) ≤ 1 + 2/b`
    have hunit : (2 * (μ * (a v) * (sideAt μ (a v)) ^ 2) / Work.BoseBox.bValue) * kappa v μ
        ≤ 2 / Work.BoseBox.bValue := by
      have h2 := mul_le_mul_of_nonneg_right hKl (by positivity : (0 : ℝ) ≤ 2 / Work.BoseBox.bValue)
      calc (2 * (μ * (a v) * (sideAt μ (a v)) ^ 2) / Work.BoseBox.bValue) * kappa v μ
          = (μ * (a v) * (sideAt μ (a v)) ^ 2 * kappa v μ) * (2 / Work.BoseBox.bValue) := by ring
        _ ≤ 1 * (2 / Work.BoseBox.bValue) := h2
        _ = 2 / Work.BoseBox.bValue := by ring
    have hkey : kappa v μ * (1 + 2 * (μ * (a v) * (sideAt μ (a v)) ^ 2) / Work.BoseBox.bValue)
        ≤ 1 + 2 / Work.BoseBox.bValue := by
      calc kappa v μ * (1 + 2 * (μ * (a v) * (sideAt μ (a v)) ^ 2) / Work.BoseBox.bValue)
          = kappa v μ
            + (2 * (μ * (a v) * (sideAt μ (a v)) ^ 2) / Work.BoseBox.bValue) * kappa v μ := by ring
        _ ≤ 1 + 2 / Work.BoseBox.bValue := add_le_add hκ1 hunit
    have hsmall : C₀ * EF * kappa v μ
        * (1 + 2 * (μ * (a v) * (sideAt μ (a v)) ^ 2) / Work.BoseBox.bValue) ≤ 1 / 2 := by
      have hCE₀nn : 0 ≤ C₀ * EF := mul_nonneg hC₀ hEFnn
      calc C₀ * EF * kappa v μ
            * (1 + 2 * (μ * (a v) * (sideAt μ (a v)) ^ 2) / Work.BoseBox.bValue)
          = (C₀ * EF) * (kappa v μ
              * (1 + 2 * (μ * (a v) * (sideAt μ (a v)) ^ 2) / Work.BoseBox.bValue)) := by ring
        _ ≤ (C₀ * EF) * (1 + 2 / Work.BoseBox.bValue) :=
            mul_le_mul_of_nonneg_left hkey hCE₀nn
        _ ≤ 1 / 2 := by
            have h5 : (C₀ * EF) * (1 + 2 / Work.BoseBox.bValue) = C₀ / (2 * M₀) := by
              rw [hEFdef]
              field_simp
            rw [h5, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * M₀)]
            linarith [hC₀M₀]
    exact nomCountArith (μ := μ) (a := a v) (ℓ := sideAt μ (a v))
      (κ := kappa v μ) (b := Work.BoseBox.bValue) (C₀ := C₀) (C_A := max (C_A / c₁) C_A)
      (E := EF) (n := n) (N := normB v μ n (Φ : X n → ℝ))
      (R := nomRPsi h μ (Φ : X n → ℝ))
      (cP := cnPlus (sideAt μ (a v)) (Φ : X n → ℝ))
      hμ hav hℓ hbpos hC₀ (le_trans (div_nonneg hC_A hc₁.le) (le_max_left _ _)) hEFnn
      hNpos hcPnn hκnn hκ1 hKl hsmall (habs μ hAdmA n Φ) hrow1' hrow2'

end Work.BoseB1Cube
