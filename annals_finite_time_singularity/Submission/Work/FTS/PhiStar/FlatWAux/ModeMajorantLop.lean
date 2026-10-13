import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.PSeries
import Submission.Work.FTS.PhiStar.FlatWAux.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.PhiStar.FlatWAux.ModeMajorant
import Submission.Work.FTS.PhiStar.FlatWAux.QmLopBound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.FlatWAux

noncomputable section

set_option autoImplicit false

/-!
# `Work.FTS.PhiStar.FlatWAux.ModeMajorantLop`

The `Lop`-weighted companion of `ModeMajorant`: the same `m`-series, but with the angular mode
bound carrying the factor `(2m+1)^(2i+4)` for an `i ≤ 6` (`Lop^i` costs two powers of
`(2m+1)` per application, and the mode bound itself carries `(2m+1)^4`).

With `λ_m = lam m = 2m(2m+5)` and `q_m = √(2m+1)` the `m`-th term of the series is

`Cd / (λ_m q_m) · λ_m^{-J} · (CRG / λ_m) · (CL i · (2m+1)^(2i+4))`
  `= Cd · CRG · CL i · λ_m^{-(J+2)} q_m^{-1} (2m+1)^(2i+4)`,

and since `λ_m ≥ 4m²`, `q_m ≥ 1` and `(2m+1)^(2i+4) ≤ (2m+1)^16 ≤ (3m)^16` for `i ≤ 6`,

`λ_m^{-(J+2)} q_m^{-1} (2m+1)^(2i+4) ≤ (3^16/4^10) · m^{-4} ≤ ((4·3^16/4^10)) · ((m+1)^2)^{-1}`,

so the series is dominated by the summable comparison series `Σ_m ((m+1)^2)^{-1}` with the
constant `Cmaj = 4·3^16/4^10`; the constant of the statement is `K i = Σ_m G i m`
(the supremum of the shape function), so no numerical sharpness is needed.
The term `m = 0` is handled by shifting the index by one (`λ_0 = 0`).
-/

/-- The shape function of the `Lop`-weighted majorant: the `m`-th term of the statement's
series with the three constants `Cd, CRG, CL i` stripped off. -/
private def Gmaj (i m : ℕ) : ℝ :=
  (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))⁻¹
    * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
    * (Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹ * (2 * (m : ℝ) + 1) ^ (2 * i + 4)

/-- The (generous) comparison constant `4·3^16/4^10`. -/
private def Cmaj : ℝ := 4 * (3 : ℝ) ^ 16 / (4 : ℝ) ^ 10

private lemma lam_nonneg (m : ℕ) : 0 ≤ Work.FTS.PhiStar.Gegenbauer.lam m := by
  simp only [Work.FTS.PhiStar.Gegenbauer.lam]
  positivity

private lemma lam_ge_four_sq (m : ℕ) :
    4 * (m : ℝ) ^ 2 ≤ Work.FTS.PhiStar.Gegenbauer.lam m := by
  have h : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  simp only [Work.FTS.PhiStar.Gegenbauer.lam]
  nlinarith

private lemma Cmaj_nonneg : 0 ≤ Cmaj := by
  norm_num [Cmaj]

private lemma Gmaj_nonneg (i m : ℕ) : 0 ≤ Gmaj i m := by
  have h0 : (0 : ℝ) ≤ Work.FTS.PhiStar.Gegenbauer.lam m := lam_nonneg m
  have h1 : (0 : ℝ) ≤
      (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))⁻¹ :=
    inv_nonneg.mpr (mul_nonneg h0 (Real.sqrt_nonneg _))
  have h2 : (0 : ℝ) ≤ ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J :=
    pow_nonneg (inv_nonneg.mpr h0) J
  have h3 : (0 : ℝ) ≤ (Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹ := inv_nonneg.mpr h0
  have h4 : (0 : ℝ) ≤ (2 * (m : ℝ) + 1) ^ (2 * i + 4) :=
    pow_nonneg (by positivity) _
  simp only [Gmaj]
  exact mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) h4

/-- `Gmaj` is the reciprocal-power form of the term: the product of the inverse `λ`-powers
collapses to `λ_m^{-10} = λ_m^{-(J+2)}`. -/
private lemma Gmaj_eq (i m : ℕ) :
    Gmaj i m = (2 * (m : ℝ) + 1) ^ (2 * i + 4)
      / ((Work.FTS.PhiStar.Gegenbauer.lam m) ^ 10 * Real.sqrt (2 * (m : ℝ) + 1)) := by
  simp only [Gmaj, J]
  rw [mul_inv, inv_pow]
  ring_nf

/-- The comparison series `Σ_m ((m+1)^2)^{-1}` is summable. -/
private lemma summable_inv_sq_shift : Summable (fun m : ℕ => (((m : ℝ) + 1) ^ 2)⁻¹) := by
  have h : Summable (fun m : ℕ => ((m : ℝ) + 1) ^ (-(2 : ℝ))) := by
    have h0 : Summable (fun n : ℕ => ((n : ℝ)) ^ (-(2 : ℝ))) :=
      (Real.summable_nat_rpow).mpr (by norm_num)
    have h1 := (summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ)) ^ (-(2 : ℝ))) 1).mpr h0
    simpa only [Nat.cast_add, Nat.cast_one] using h1
  refine h.congr (fun m => ?_)
  rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ (m : ℝ) + 1)]
  norm_num

/-- The pointwise comparison, for `m ≥ 1` and `i ≤ 6`. -/
private lemma Gmaj_le {i m : ℕ} (hm : 1 ≤ m) (hi : i ≤ 6) :
    Gmaj i m ≤ Cmaj * (((m : ℝ) + 1) ^ 2)⁻¹ := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hbase : (1 : ℝ) ≤ 2 * (m : ℝ) + 1 := by linarith
  have hs1 : (1 : ℝ) ≤ Real.sqrt (2 * (m : ℝ) + 1) := Real.one_le_sqrt.mpr (by linarith)
  have hlam4 : 4 * (m : ℝ) ^ 2 ≤ Work.FTS.PhiStar.Gegenbauer.lam m := lam_ge_four_sq m
  have hlam0 : (0 : ℝ) ≤ Work.FTS.PhiStar.Gegenbauer.lam m := lam_nonneg m
  -- the numerator: `(2m+1)^(2i+4) ≤ (2m+1)^16 ≤ (3m)^16`
  have hnum : (2 * (m : ℝ) + 1) ^ (2 * i + 4) ≤ (3 : ℝ) ^ 16 * (m : ℝ) ^ 16 := by
    have h1 : (2 * (m : ℝ) + 1) ^ (2 * i + 4) ≤ (2 * (m : ℝ) + 1) ^ 16 :=
      pow_le_pow_right₀ hbase (by omega)
    have h2 : (2 * (m : ℝ) + 1) ^ 16 ≤ (3 * (m : ℝ)) ^ 16 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 16
    rw [mul_pow] at h2
    linarith
  -- the denominator: `λ_m^10 √(2m+1) ≥ (4m²)^10`
  have hden : (4 * (m : ℝ) ^ 2) ^ 10 * 1
      ≤ (Work.FTS.PhiStar.Gegenbauer.lam m) ^ 10 * Real.sqrt (2 * (m : ℝ) + 1) := by
    have h4 : (4 * (m : ℝ) ^ 2) ^ 10 ≤ (Work.FTS.PhiStar.Gegenbauer.lam m) ^ 10 :=
      pow_le_pow_left₀ (by positivity) hlam4 10
    have h5 : (0 : ℝ) ≤ (Work.FTS.PhiStar.Gegenbauer.lam m) ^ 10 := by positivity
    calc (4 * (m : ℝ) ^ 2) ^ 10 * 1 = (4 * (m : ℝ) ^ 2) ^ 10 := by ring
      _ ≤ (Work.FTS.PhiStar.Gegenbauer.lam m) ^ 10 := h4
      _ = (Work.FTS.PhiStar.Gegenbauer.lam m) ^ 10 * 1 := by ring
      _ ≤ (Work.FTS.PhiStar.Gegenbauer.lam m) ^ 10 * Real.sqrt (2 * (m : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left hs1 h5
  have hdpos1 : (0 : ℝ) < (4 * (m : ℝ) ^ 2) ^ 10 * 1 := by positivity
  have hdpos2 : (0 : ℝ) < (4 : ℝ) ^ 10 * ((m : ℝ) + 1) ^ 2 := by positivity
  have hstep1 : Gmaj i m
      ≤ (3 : ℝ) ^ 16 * (m : ℝ) ^ 16 / ((4 * (m : ℝ) ^ 2) ^ 10 * 1) := by
    rw [Gmaj_eq]
    exact div_le_div₀ (by positivity) hnum (by positivity) hden
  -- `(m+1)² ≤ 4m⁴` for `m ≥ 1`
  have hq : ((m : ℝ) + 1) ^ 2 ≤ 4 * (m : ℝ) ^ 4 := by
    have h3 : (0 : ℝ) ≤ (3 * (m : ℝ) + 1) * ((m : ℝ) - 1) :=
      mul_nonneg (by linarith) (by linarith)
    have hm4 : (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 4 := by nlinarith
    nlinarith [h3, hm4]
  have hstep2 : (3 : ℝ) ^ 16 * (m : ℝ) ^ 16 / ((4 * (m : ℝ) ^ 2) ^ 10 * 1)
      ≤ 4 * (3 : ℝ) ^ 16 / ((4 : ℝ) ^ 10 * ((m : ℝ) + 1) ^ 2) := by
    rw [div_le_div_iff₀ hdpos1 hdpos2,
      show ((4 : ℝ) * (m : ℝ) ^ 2) ^ 10 * 1 = (4 : ℝ) ^ 10 * (m : ℝ) ^ 20 from by ring]
    have hq16 : (m : ℝ) ^ 16 * ((m : ℝ) + 1) ^ 2
        ≤ (m : ℝ) ^ 16 * (4 * (m : ℝ) ^ 4) :=
      mul_le_mul_of_nonneg_left hq (by positivity)
    have hfinal : (3 : ℝ) ^ 16 * (4 : ℝ) ^ 10 * ((m : ℝ) ^ 16 * ((m : ℝ) + 1) ^ 2)
        ≤ (3 : ℝ) ^ 16 * (4 : ℝ) ^ 10 * ((m : ℝ) ^ 16 * (4 * (m : ℝ) ^ 4)) :=
      mul_le_mul_of_nonneg_left hq16 (by positivity)
    calc (3 : ℝ) ^ 16 * (m : ℝ) ^ 16 * ((4 : ℝ) ^ 10 * ((m : ℝ) + 1) ^ 2)
        = (3 : ℝ) ^ 16 * (4 : ℝ) ^ 10 * ((m : ℝ) ^ 16 * ((m : ℝ) + 1) ^ 2) := by ring
      _ ≤ (3 : ℝ) ^ 16 * (4 : ℝ) ^ 10 * ((m : ℝ) ^ 16 * (4 * (m : ℝ) ^ 4)) := hfinal
      _ = 4 * (3 : ℝ) ^ 16 * ((4 : ℝ) ^ 10 * (m : ℝ) ^ 20) := by ring
  have hconv : Cmaj * (((m : ℝ) + 1) ^ 2)⁻¹
      = 4 * (3 : ℝ) ^ 16 / ((4 : ℝ) ^ 10 * ((m : ℝ) + 1) ^ 2) := by
    simp only [Cmaj, div_eq_mul_inv]
    rw [mul_inv]
    ring
  rw [hconv]
  exact le_trans hstep1 hstep2

private lemma summable_Gmaj {i : ℕ} (hi : i ≤ 6) : Summable (fun m : ℕ => Gmaj i m) := by
  have hmaj : Summable (fun m : ℕ => Cmaj * ((((m + 1 : ℕ) : ℝ) + 1) ^ 2)⁻¹) := by
    have hsh : Summable (fun m : ℕ => ((((m + 1 : ℕ) : ℝ) + 1) ^ 2)⁻¹) :=
      (summable_nat_add_iff (f := fun m : ℕ => (((m : ℝ) + 1) ^ 2)⁻¹) 1).mpr
        summable_inv_sq_shift
    exact hsh.mul_left Cmaj
  have hshift : Summable (fun m : ℕ => Gmaj i (m + 1)) := by
    refine Summable.of_nonneg_of_le
      (f := fun m : ℕ => Cmaj * ((((m + 1 : ℕ) : ℝ) + 1) ^ 2)⁻¹)
      (g := fun m : ℕ => Gmaj i (m + 1))
      (fun m => Gmaj_nonneg i (m + 1)) (fun m => ?_) hmaj
    exact Gmaj_le (m := m + 1) (by omega) hi
  exact (summable_nat_add_iff (f := fun m : ℕ => Gmaj i m) 1).mp hshift

theorem ModeMajorantLop : ∃ K : ℕ → ℝ, (∀ i : ℕ, 0 ≤ K i) ∧
    ∀ (Cd CRG : ℝ), 0 ≤ Cd → 0 ≤ CRG → ∀ (CL : ℕ → ℝ), (∀ i : ℕ, 0 ≤ CL i) →
    ∀ (i : ℕ), i ≤ 6 →
      Summable (fun m : ℕ =>
          Cd / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
            * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ Work.FTS.PhiStar.FlatWAux.J
            * (CRG / Work.FTS.PhiStar.Gegenbauer.lam m)
            * (CL i * (2 * (m : ℝ) + 1) ^ (2 * i + 4))) ∧
      (∑' m : ℕ, Cd / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
            * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ Work.FTS.PhiStar.FlatWAux.J
            * (CRG / Work.FTS.PhiStar.Gegenbauer.lam m)
            * (CL i * (2 * (m : ℝ) + 1) ^ (2 * i + 4)))
        ≤ K i * Cd * CRG * (CL i) := by
  refine ⟨fun i => ∑' m : ℕ, Gmaj i m, fun i => tsum_nonneg (fun m => Gmaj_nonneg i m), ?_⟩
  intro Cd CRG _ _ CL _ i hi
  have hGsum : Summable (fun m : ℕ => Gmaj i m) := summable_Gmaj hi
  have hEq : ∀ m : ℕ,
      Cd / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
          * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
          * (CRG / Work.FTS.PhiStar.Gegenbauer.lam m)
          * (CL i * (2 * (m : ℝ) + 1) ^ (2 * i + 4))
        = Cd * CRG * CL i * Gmaj i m := by
    intro m
    simp only [Gmaj, div_eq_mul_inv]
    ring
  refine ⟨?_, ?_⟩
  · exact (hGsum.mul_left (Cd * CRG * CL i)).congr (fun m => (hEq m).symm)
  · rw [tsum_congr (fun m => hEq m), tsum_mul_left]
    show Cd * CRG * CL i * (∑' m : ℕ, Gmaj i m)
        ≤ (∑' m : ℕ, Gmaj i m) * Cd * CRG * CL i
    exact le_of_eq (by ring)

end

end Work.FTS.PhiStar.FlatWAux
