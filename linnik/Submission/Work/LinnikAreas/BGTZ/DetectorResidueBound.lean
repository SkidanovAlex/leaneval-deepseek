/-
# The residue term of the BGTZ zero detector fits the first summand of the target bound

This module proves `Work.LinnikAreas.BGTZ.DetectorResidueBound`, the estimate of the residue
term `detResBound χ₁ χ R θw N ρ` of the BGTZ zero detector (BGTZ, arXiv:2410.06082,
Proposition 5.1, first summand).

The residue term is

  `‖L(1,χ₁)‖ · (φ(q)/q) · ‖G(1,χ₀)‖ · N^{1-Re ρ} / ‖(1-ρ)(2-ρ)‖`

(`DetectorDefs.detResBound`) and the target is its comparison with
`(2-β₁)(1-β₁)N^{1-Re ρ}/(1-Re ρ)`.  The three inputs are

* Graham's bound for the Selberg sieve (`sieveGre ≤ (q/φ(q))(Σ_{n≤R}a(n)/n)⁻¹`, a hypothesis);
* `G(1,χ₀)` is a *non-negative real* (`SieveGAtOneSq`), so its norm is the real part;
* the smoothed lower bound `SmoothedCoeffLower` for `Σ_{n≤R}a(n)n^{-β₁}(1-n/R)`, combined with
  the elementary "bracket" estimate `smoothed_le_sum` (`DetectorAux`), which yields

  `‖L(1,χ₁)‖ · (Σ_{n≤R}a(n)/n)⁻¹ ≤ (1-β₁)(2-β₁)`.

The last step is the only place where the constants have to be matched: the smoothing of
`SmoothedCoeffLower` is compensated by the bracket factor
`(1-β₁)^{1-β₁}/(2-β₁)^{2-β₁}`, and the error `CS·A·exp((log q)^{3/4})·q^θ/R^{1/2}` is absorbed
by the hypothesis `R ≥ C·A²q^{2θ}exp(2(log q)^{3/4})(1-β₁)^{-2}` with `C ≥ 4CS²`
(`EpsLeOfRpowGe`), which gives the needed `ε ≤ (1-β₁)/(2-β₁)`.
-/
import Mathlib
import Submission.Work.LinnikAreas.BGTZSetup
import Submission.Work.LinnikAreas.BGTZ.DetectorDefs
import Submission.Work.LinnikAreas.BGTZ.DetectorAux
import Submission.Work.LinnikAreas.BGTZ.SmoothedCoeffLower
import Submission.Work.LinnikAreas.BGTZ.SieveGAtOneSq
import Submission.Work.LinnikAreas.BGTZ.DetectorContourCore
import Submission.Work.LinnikAreas.BGTZ.EpsLeOfRpowGe

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas.BGTZ

/-- Elementary bookkeeping: if the smoothed lower bound
`L·R^δ/(δ(1+δ))·(1-ε) ≤ S·(δ^δ R^δ/(1+δ)^{1+δ})` holds with `ε ≤ δ/(1+δ)`, then
`L/S ≤ δ(1+δ)`.  The gain is the factor `(δ/(1+δ))^δ ≤ 1` supplied by the smoothing. -/
private theorem ratio_le_of_smoothed {L S R δ ε : ℝ} (hL : 0 ≤ L) (hS : 0 < S) (hR : 0 < R)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hε : ε ≤ δ / (1 + δ))
    (hSmo : L * R ^ δ / (δ * (1 + δ)) * (1 - ε)
      ≤ S * (δ ^ δ * R ^ δ / (1 + δ) ^ (1 + δ))) :
    L / S ≤ δ * (1 + δ) := by
  have h1δ : 0 < 1 + δ := by linarith
  have hRδ : 0 < R ^ δ := Real.rpow_pos_of_pos hR δ
  simp only [div_eq_mul_inv] at hSmo hε ⊢
  have hfrac : δ * (1 + δ)⁻¹ = 1 - (1 + δ)⁻¹ := by
    field_simp
    ring
  have h1ε : ((1 : ℝ) + δ)⁻¹ ≤ 1 - ε := by
    rw [hfrac] at hε
    linarith
  have hp : 0 < δ * (1 + δ) * (R ^ δ)⁻¹ := by positivity
  have hmul := mul_le_mul_of_nonneg_right hSmo hp.le
  have hA : L * R ^ δ * (δ * (1 + δ))⁻¹ * (1 - ε) * (δ * (1 + δ) * (R ^ δ)⁻¹)
      = L * (1 - ε) := by
    field_simp
  have hB : S * (δ ^ δ * R ^ δ * ((1 + δ) ^ (1 + δ))⁻¹) * (δ * (1 + δ) * (R ^ δ)⁻¹)
      = S * (δ * (1 + δ) * δ ^ δ * ((1 + δ) ^ (1 + δ))⁻¹) := by
    field_simp
  rw [hA, hB] at hmul
  have hL2 : L * ((1 : ℝ) + δ)⁻¹ ≤ L * (1 - ε) := mul_le_mul_of_nonneg_left h1ε hL
  have hstep : L * ((1 : ℝ) + δ)⁻¹
      ≤ S * (δ * (1 + δ) * δ ^ δ * ((1 + δ) ^ (1 + δ))⁻¹) := hL2.trans hmul
  have hmul2 := mul_le_mul_of_nonneg_right hstep h1δ.le
  have hL3 : L * ((1 : ℝ) + δ)⁻¹ * (1 + δ) = L := by
    field_simp
  have hpow1 : (1 + δ) ^ (1 + δ) = (1 + δ) ^ δ * (1 + δ) := by
    have h := Real.rpow_add h1δ δ 1
    rw [Real.rpow_one] at h
    rw [← h]
    congr 1
    ring
  have hR3 : S * (δ * (1 + δ) * δ ^ δ * ((1 + δ) ^ (1 + δ))⁻¹) * (1 + δ)
      = S * (δ * (1 + δ) * (δ ^ δ * ((1 + δ) ^ δ)⁻¹)) := by
    rw [hpow1]
    field_simp
  rw [hL3, hR3] at hmul2
  have hfac : δ ^ δ * ((1 + δ) ^ δ)⁻¹ = (δ * (1 + δ)⁻¹) ^ δ := by
    rw [Real.mul_rpow hδ.le (inv_nonneg.mpr h1δ.le), Real.inv_rpow h1δ.le]
  have hle1 : (δ * (1 + δ)⁻¹) ^ δ ≤ 1 := by
    have h0 : (0 : ℝ) ≤ δ * (1 + δ)⁻¹ := by positivity
    have h1 : δ * (1 + δ)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one h1δ]
      linarith
    exact Real.rpow_le_one h0 h1 hδ.le
  have hfin : L ≤ S * (δ * (1 + δ)) := by
    calc L ≤ S * (δ * (1 + δ) * (δ ^ δ * ((1 + δ) ^ δ)⁻¹)) := hmul2
      _ = S * (δ * (1 + δ) * (δ * (1 + δ)⁻¹) ^ δ) := by rw [hfac]
      _ ≤ S * (δ * (1 + δ) * 1) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left hle1 (by positivity)
      _ = S * (δ * (1 + δ)) := by ring
  rw [← div_eq_mul_inv, div_le_iff₀ hS]
  calc L ≤ S * (δ * (1 + δ)) := hfin
    _ = δ * (1 + δ) * S := by ring

theorem DetectorResidueBound :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q], 400000 < q → ∀ (χ₁ χ : DirichletCharacter ℂ q),
      χ₁ ^ 2 = 1 → χ₁ ≠ 1 → ∀ {β₁ : ℝ}, β₁ < 1 → Work.LinnikContract.zeroMult χ₁ (β₁ : ℂ) ≠ 0 →
      1 - 1 / (10 * Real.log q) < β₁ →
      ∀ {A θ Cz : ℝ}, HypA A θ → HypZeta Cz → ∀ {R : ℕ}, 200 ≤ R →
      C * A ^ 2 * (q : ℝ) ^ (2 * θ) * Real.exp (2 * (Real.log q) ^ (3 / 4 : ℝ))
          * (1 - β₁) ^ (-2 : ℝ) ≤ (R : ℝ) →
      ∀ {θw : ℕ → ℝ}, IsSieveWeight R θw →
      sieveGre χ₁ R θw 1 (1 : DirichletCharacter ℂ q)
        ≤ ((q : ℝ) / (q.totient : ℝ)) * (∑ n ∈ Finset.Icc 1 R, aCoeff χ₁ n / (n : ℝ))⁻¹ →
      ∀ {ρ : ℂ},
        (DirichletCharacter.LFunction χ ρ = 0 ∨ DirichletCharacter.LFunction (χ * χ₁) ρ = 0) →
        1 / 2 < ρ.re →
      ∀ (N : ℕ),
        detResBound χ₁ χ R θw N ρ
          ≤ (2 - β₁) * (1 - β₁) * ((N : ℝ) ^ (1 - ρ.re)) / (1 - ρ.re) := by
  obtain ⟨CS, hCSpos, hCS⟩ := SmoothedCoeffLower
  refine ⟨max 1 (4 * CS ^ 2), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro q inst hq χ₁ χ hχ₁ hχ₁ne β₁ hβ₁ hzm hβ₁' A θ Cz hA hZ R hR hRlo θw hθw hGraham
    ρ hzero hre N
  have hC4 : 4 * CS ^ 2 ≤ max 1 (4 * CS ^ 2) := le_max_right _ _
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast NeZero.pos q
  have hlogq : (1 : ℝ) < Real.log q := by
    have h3 : (3 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 3 < q)
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ < Real.log q := Real.log_lt_log (Real.exp_pos 1) (lt_trans Real.exp_one_lt_three h3)
  have h2β : 2 - β₁ = 1 + (1 - β₁) := by ring
  have hδpos : 0 < 1 - β₁ := by
    have h1 : 1 / (10 * Real.log q) < 1 := by
      rw [div_lt_one (by positivity)]
      linarith
    linarith
  have hδlt1 : 1 - β₁ < 1 := by
    have h1 : 1 / (10 * Real.log q) < 1 := by
      rw [div_lt_one (by positivity)]
      linarith
    linarith
  have hNnonneg : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hRpos : (0 : ℝ) < (R : ℝ) := by
    have : 0 < R := by omega
    exact_mod_cast this
  have hρlt : ρ.re < 1 := det_rho_re_lt_one hq χ₁ χ hχ₁ne hzero hre
  have hηpos : 0 < 1 - ρ.re := by linarith
  have hden : (1 - ρ.re) ≤ ‖(1 - ρ) * (2 - ρ)‖ := by
    have h := denom_bound hre hρlt
    have h2 : (1 : ℝ) ≤ 2 - ρ.re := by linarith
    calc (1 - ρ.re) = (1 - ρ.re) * 1 := by ring
      _ ≤ (1 - ρ.re) * (2 - ρ.re) := mul_le_mul_of_nonneg_left h2 hηpos.le
      _ ≤ ‖(1 - ρ) * (2 - ρ)‖ := h
  obtain ⟨hGre0, hGcast⟩ :=
    SieveGAtOneSq (R := R) (θw := θw) χ₁ hχ₁ hθw
  have hGnorm : ‖sieveG χ₁ R θw 1 (1 : DirichletCharacter ℂ q)‖ = sieveGre χ₁ R θw 1 1 := by
    rw [hGcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hGre0]
  have hS1 : 1 ≤ ∑ n ∈ Finset.Icc 1 R, aCoeff χ₁ n / (n : ℝ) := by
    have hmem : 1 ∈ Finset.Icc 1 R := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
    have hnonneg : ∀ i ∈ Finset.Icc 1 R, (0 : ℝ) ≤ aCoeff χ₁ i / (i : ℝ) := by
      intro i _
      have hi : (0 : ℝ) ≤ (i : ℝ) := by positivity
      exact div_nonneg (aCoeff_nonneg χ₁ hχ₁ i) hi
    have hle := Finset.single_le_sum (f := fun n : ℕ => aCoeff χ₁ n / (n : ℝ)) hnonneg hmem
    rw [aCoeff_one] at hle
    simpa using hle
  have hSpos : 0 < ∑ n ∈ Finset.Icc 1 R, aCoeff χ₁ n / (n : ℝ) := lt_of_lt_of_le one_pos hS1
  have hcancel : ((q.totient : ℝ) / (q : ℝ)) * sieveGre χ₁ R θw 1 1
      ≤ (∑ n ∈ Finset.Icc 1 R, aCoeff χ₁ n / (n : ℝ))⁻¹ := by
    have hstep := mul_le_mul_of_nonneg_left hGraham (by positivity :
      (0 : ℝ) ≤ (q.totient : ℝ) / (q : ℝ))
    calc ((q.totient : ℝ) / (q : ℝ)) * sieveGre χ₁ R θw 1 1
        ≤ ((q.totient : ℝ) / (q : ℝ))
          * (((q : ℝ) / (q.totient : ℝ)) * (∑ n ∈ Finset.Icc 1 R, aCoeff χ₁ n / (n : ℝ))⁻¹) :=
          hstep
      _ = (∑ n ∈ Finset.Icc 1 R, aCoeff χ₁ n / (n : ℝ))⁻¹ := by
          rw [← mul_assoc, totient_ratio, one_mul]
  have hSmoRaw := hCS q hq χ₁ hχ₁ hχ₁ne hβ₁ hzm hβ₁' hA hZ hR
  have hBracket := smoothed_le_sum χ₁ hχ₁ hβ₁ (by omega : 1 ≤ R)
  rw [h2β] at hSmoRaw hBracket
  have hchain := hSmoRaw.trans hBracket
  have hq2θ : (q : ℝ) ^ (2 * θ) = ((q : ℝ) ^ θ) ^ 2 := by
    rw [show (2 : ℝ) * θ = θ + θ by ring, Real.rpow_add hqpos, pow_two]
  have hExp2 : Real.exp (2 * (Real.log q) ^ (3 / 4 : ℝ))
      = (Real.exp ((Real.log q) ^ (3 / 4 : ℝ))) ^ 2 := by
    rw [show (2 : ℝ) * (Real.log q) ^ (3 / 4 : ℝ)
        = ((2 : ℕ) : ℝ) * (Real.log q) ^ (3 / 4 : ℝ) by norm_num, Real.exp_nat_mul]
  have hRlo' : max 1 (4 * CS ^ 2) * A ^ 2 * ((q : ℝ) ^ θ) ^ 2
      * (Real.exp ((Real.log q) ^ (3 / 4 : ℝ))) ^ 2 * (1 - β₁) ^ (-2 : ℝ) ≤ (R : ℝ) := by
    rw [← hq2θ, ← hExp2]
    exact hRlo
  have hEpsLe : CS * A * Real.exp ((Real.log q) ^ (3 / 4 : ℝ)) * (q : ℝ) ^ θ
      / (R : ℝ) ^ (1 / 2 : ℝ) ≤ (1 - β₁) / (1 + (1 - β₁)) :=
    EpsLeOfRpowGe (CS := CS) (A := A) (E := Real.exp ((Real.log q) ^ (3 / 4 : ℝ)))
      (Q := (q : ℝ) ^ θ) (δ := 1 - β₁) (R := (R : ℝ)) (C := max 1 (4 * CS ^ 2))
      hCSpos hA.1 (Real.exp_pos _) (Real.rpow_pos_of_pos hqpos θ) hδpos hδlt1 hRpos hC4 hRlo'
  have hratio : ‖DirichletCharacter.LFunction χ₁ (1 : ℂ)‖
      / (∑ n ∈ Finset.Icc 1 R, aCoeff χ₁ n / (n : ℝ)) ≤ (1 - β₁) * (1 + (1 - β₁)) :=
    ratio_le_of_smoothed (L := ‖DirichletCharacter.LFunction χ₁ (1 : ℂ)‖)
      (S := ∑ n ∈ Finset.Icc 1 R, aCoeff χ₁ n / (n : ℝ)) (R := (R : ℝ))
      (δ := 1 - β₁)
      (ε := CS * A * Real.exp ((Real.log q) ^ (3 / 4 : ℝ)) * (q : ℝ) ^ θ
        / (R : ℝ) ^ (1 / 2 : ℝ))
      (norm_nonneg _) hSpos hRpos hδpos hδlt1 hEpsLe hchain
  calc detResBound χ₁ χ R θw N ρ
      = ‖DirichletCharacter.LFunction χ₁ (1 : ℂ)‖ * ((q.totient : ℝ) / (q : ℝ))
          * sieveGre χ₁ R θw 1 1 * (N : ℝ) ^ (1 - ρ.re) / ‖(1 - ρ) * (2 - ρ)‖ := by
        rw [detResBound, hGnorm]
    _ ≤ ‖DirichletCharacter.LFunction χ₁ (1 : ℂ)‖
          * (∑ n ∈ Finset.Icc 1 R, aCoeff χ₁ n / (n : ℝ))⁻¹
          * (N : ℝ) ^ (1 - ρ.re) / ‖(1 - ρ) * (2 - ρ)‖ := by
        apply div_le_div_of_nonneg_right _ (norm_nonneg _)
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hNnonneg _)
        calc ‖DirichletCharacter.LFunction χ₁ (1 : ℂ)‖ * ((q.totient : ℝ) / (q : ℝ))
              * sieveGre χ₁ R θw 1 1
            = ‖DirichletCharacter.LFunction χ₁ (1 : ℂ)‖
              * (((q.totient : ℝ) / (q : ℝ)) * sieveGre χ₁ R θw 1 1) := by ring
          _ ≤ ‖DirichletCharacter.LFunction χ₁ (1 : ℂ)‖
              * (∑ n ∈ Finset.Icc 1 R, aCoeff χ₁ n / (n : ℝ))⁻¹ :=
              mul_le_mul_of_nonneg_left hcancel (norm_nonneg _)
    _ = ‖DirichletCharacter.LFunction χ₁ (1 : ℂ)‖
          / (∑ n ∈ Finset.Icc 1 R, aCoeff χ₁ n / (n : ℝ))
          * (N : ℝ) ^ (1 - ρ.re) / ‖(1 - ρ) * (2 - ρ)‖ := by
        ring
    _ ≤ (1 - β₁) * (1 + (1 - β₁)) * (N : ℝ) ^ (1 - ρ.re) / ‖(1 - ρ) * (2 - ρ)‖ := by
        apply div_le_div_of_nonneg_right _ (norm_nonneg _)
        exact mul_le_mul_of_nonneg_right hratio (Real.rpow_nonneg hNnonneg _)
    _ ≤ (1 - β₁) * (1 + (1 - β₁)) * (N : ℝ) ^ (1 - ρ.re) / (1 - ρ.re) := by
        apply div_le_div_of_nonneg_left _ hηpos hden
        exact mul_nonneg (mul_nonneg hδpos.le (by linarith)) (Real.rpow_nonneg hNnonneg _)
    _ = (2 - β₁) * (1 - β₁) * ((N : ℝ) ^ (1 - ρ.re)) / (1 - ρ.re) := by
        rw [← h2β]
        ring

end Work.LinnikAreas.BGTZ
