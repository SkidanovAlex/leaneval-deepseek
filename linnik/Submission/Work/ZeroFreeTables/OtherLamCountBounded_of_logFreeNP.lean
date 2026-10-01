/-
# ZeroFreeTables — `OtherLamCountBounded_of_logFreeNP`

The near-line count `Work.ZeroFreeTables.OtherLamCountBounded` (Heath-Brown's Lemma 6.1, the only
analytic input of Table 7) from a **log-free non-principal family zero-density estimate with an
arbitrary exponent coefficient**:

for every `ε > 0` there is `C = C(ε) > 0` with

`Σ_{χ ≠ 1 mod q} N(σ,T,χ) ≤ C (qT)^{(c+ε)(1-σ)}`  for `σ₀ ≤ σ ≤ 1`, `T ≥ 1`,

where `σ₀ < 1` and `c > 0` are fixed.  The conclusion is that the multiplicity-weighted count of
the zeros of the `χ ∉ {1, χ₁, χ₁⁻¹}` with `λ(ρ) = (1-Re ρ) log q ≤ Λ ≤ 3` and `|Im ρ| ≤ H ≤ 10 log q`
is bounded by a constant depending only on `σ₀`, `c` and the constants of the hypothesis —
uniformly in `q`, in the excluded character `χ₁` and in `Λ, H`.

This is the reduction used when the density input available is not literally Jutila's
`c = 2` form `FamilyZeroDensityJutilaNP` but an amplified version of it (e.g. the `(12/5+ε)`
exponent of Heath-Brown's (1.4), or any `(c+ε)` form): the near-line region
`1 - σ = λ/log q`, `λ ≤ 3` converts *any* fixed exponent coefficient into a constant, because

`(qT)^{(c+ε)λ/log q} = exp((c+ε)·λ·log(qT)/log q) ≤ exp(2·3·(c+ε))`

for `log q ≥ max 15 (3/(1-σ₀))` (here `T ≤ max(10 log q, 1) ≤ 10 log q`, so
`log(q·10 log q) ≤ 2 log q`).

The counting step is the *non-principal* refinement `otherLamCount_le_zeroCountSumNP`
(`Submission/Work/ZeroFreeTables/OtherLamCountBounded_of_jutilaNP.lean`), so no input at all is
required for the principal character.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.OtherLamCountBounded_of_jutilaNP
import Submission.Work.LinnikAreas.FarBoundOfJutilaMontgomery

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

/-- `log 10 ≤ L/2` as soon as `L ≥ 8`.  (`log 10 ≤ log 16 = 4 log 2 ≤ 4 ≤ L/2`.) -/
private lemma log_ten_le_half {L : ℝ} (hL : 8 ≤ L) : Real.log 10 ≤ L / 2 := by
  have h1 : Real.log 10 ≤ Real.log 16 := Real.log_le_log (by norm_num) (by norm_num)
  have h2 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have h3 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  linarith

/-- `log L ≤ L/2` as soon as `L ≥ 2`.  (`log L = log 2 + log (L/2) ≤ log 2 + (L/2 - 1) ≤ L/2`.) -/
private lemma log_self_le_half {L : ℝ} (hL : 2 ≤ L) : Real.log L ≤ L / 2 := by
  have h2 : (0 : ℝ) < L / 2 := by linarith
  have hsplit : Real.log L = Real.log 2 + Real.log (L / 2) := by
    calc Real.log L = Real.log (2 * (L / 2)) := by rw [show 2 * (L / 2) = L by ring]
      _ = Real.log 2 + Real.log (L / 2) := Real.log_mul (by norm_num) (ne_of_gt h2)
  have h3 : Real.log (L / 2) ≤ L / 2 - 1 := Real.log_le_sub_one_of_pos h2
  have h4 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  linarith

/-- `log (q · 10 log q) ≤ 2 log q` for `q > 0` with `log q ≥ 8`.  Indeed
`log(10 log q) = log 10 + log log q ≤ (log q)/2 + (log q)/2 = log q`. -/
private lemma log_mul_ten_log_le {q : ℝ} (hqpos : 0 < q) (hq : 8 ≤ Real.log q) :
    Real.log (q * (10 * Real.log q)) ≤ 2 * Real.log q := by
  set L := Real.log q with hL
  have hLpos : 0 < L := by linarith
  have h1 : Real.log (q * (10 * L)) = Real.log q + Real.log (10 * L) :=
    Real.log_mul (ne_of_gt hqpos) (by positivity)
  have h2 : Real.log (10 * L) = Real.log 10 + Real.log L :=
    Real.log_mul (by norm_num) (ne_of_gt hLpos)
  have h3 : Real.log 10 ≤ L / 2 := log_ten_le_half (by linarith)
  have h4 : Real.log L ≤ L / 2 := log_self_le_half (by linarith)
  rw [h1, h2, ← hL]
  linarith

/-- **The near-line count from a log-free non-principal family zero-density estimate with an
arbitrary exponent coefficient.**  See the file header. -/
theorem OtherLamCountBounded_of_logFreeNP (σ₀ c : ℝ) (hσ₀ : σ₀ < 1) (hc : 0 < c)
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q] (σ T : ℝ), σ₀ ≤ σ → σ ≤ 1 → 1 ≤ T →
        (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
            Work.LinnikAreas.zeroCountIn χ σ T)
          ≤ C * ((q : ℝ) * T) ^ ((c + ε) * (1 - σ))) :
    Work.ZeroFreeTables.OtherLamCountBounded := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := h 1 (by norm_num)
  have hσ01 : 0 < 1 - σ₀ := by linarith
  refine ⟨C₁ * Real.exp (6 * (c + 1)), mul_pos hC₁pos (Real.exp_pos _),
    max 10000 (Nat.ceil (Real.exp (max 15 (3 / (1 - σ₀)))) + 1), ?_⟩
  intro q hQ inst χ₁ Λ H hΛ hH
  -- basic facts about `q`
  have hq2 : 2 ≤ q :=
    le_trans (by norm_num : (2 : ℕ) ≤ 10000) (le_trans (le_max_left _ _) hQ)
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
  have hceil : (Nat.ceil (Real.exp (max 15 (3 / (1 - σ₀)))) + 1 : ℕ) ≤ q :=
    le_trans (le_max_right _ _) hQ
  have hceil' : (Nat.ceil (Real.exp (max 15 (3 / (1 - σ₀))) : ℝ) : ℕ) ≤ q := by omega
  have hexpA : Real.exp (max 15 (3 / (1 - σ₀))) ≤ (q : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hceil')
  have hA : max 15 (3 / (1 - σ₀)) ≤ Real.log (q : ℝ) :=
    (Real.le_log_iff_exp_le hqpos).mpr hexpA
  have hL15 : 15 ≤ Real.log (q : ℝ) := le_trans (le_max_left _ _) hA
  have hLbig : 3 / (1 - σ₀) ≤ Real.log (q : ℝ) := le_trans (le_max_right _ _) hA
  have hLpos : 0 < Real.log (q : ℝ) := by linarith
  -- the rectangle `(σ, T)` on which the hypothesis is applied
  set σ : ℝ := 1 - max Λ 0 / Real.log (q : ℝ) with hσdef
  set T : ℝ := max H 1 with hTdef
  have h1σ : 1 - σ = max Λ 0 / Real.log (q : ℝ) := by rw [hσdef]; ring
  have hmaxΛ : max Λ 0 ≤ 3 := max_le hΛ (by norm_num)
  have hσlo : σ₀ ≤ σ := by
    have h3 : max Λ 0 ≤ (1 - σ₀) * Real.log (q : ℝ) := by
      have h4 := (div_le_iff₀ hσ01).mp hLbig
      nlinarith
    have h5 : max Λ 0 / Real.log (q : ℝ) ≤ 1 - σ₀ := (div_le_iff₀ hLpos).mpr h3
    rw [hσdef]; linarith
  have hσhi : σ ≤ 1 := by
    have h : 0 ≤ max Λ 0 / Real.log (q : ℝ) := div_nonneg (le_max_right _ _) hLpos.le
    rw [hσdef]; linarith
  have hT1 : 1 ≤ T := by rw [hTdef]; exact le_max_right _ _
  have hTq : T ≤ 10 * Real.log (q : ℝ) := by
    rw [hTdef]
    exact max_le hH (by linarith)
  -- the hypothesis at `(σ, T)` and the counting lemma
  have hbound := hC₁ q hq2 σ T hσlo hσhi hT1
  have hcount := otherLamCount_le_zeroCountSumNP hq2 χ₁ Λ H
  -- the exponent never exceeds a constant
  have hE : 0 ≤ (c + 1) * (1 - σ) := by
    rw [h1σ]
    exact mul_nonneg (by linarith) (div_nonneg (le_max_right _ _) hLpos.le)
  have hbase : (q : ℝ) * T ≤ (q : ℝ) * (10 * Real.log (q : ℝ)) :=
    mul_le_mul_of_nonneg_left hTq hqpos.le
  have hbasepos : 0 < (q : ℝ) * (10 * Real.log (q : ℝ)) :=
    mul_pos hqpos (by linarith)
  have hkey : ((q : ℝ) * T) ^ ((c + 1) * (1 - σ)) ≤ Real.exp (6 * (c + 1)) := by
    have hbase0 : 0 ≤ (q : ℝ) * T := by
      have : 0 < T := by rw [hTdef]; linarith
      exact mul_nonneg hqpos.le this.le
    have hlogb : Real.log ((q : ℝ) * (10 * Real.log (q : ℝ))) ≤ 2 * Real.log (q : ℝ) :=
      log_mul_ten_log_le hqpos (by linarith)
    have hlogbnn : 0 ≤ 2 * Real.log (q : ℝ) := by linarith
    have hlognn : 0 ≤ Real.log ((q : ℝ) * (10 * Real.log (q : ℝ))) := by
      apply Real.log_nonneg
      calc (1 : ℝ) ≤ 10 * Real.log (q : ℝ) := by linarith
        _ ≤ (q : ℝ) * (10 * Real.log (q : ℝ)) :=
            le_mul_of_one_le_left (by linarith) hq1
    have hE' : (c + 1) * (1 - σ) ≤ 3 * (c + 1) / Real.log (q : ℝ) := by
      rw [h1σ]
      have h1 : max Λ 0 / Real.log (q : ℝ) ≤ 3 / Real.log (q : ℝ) :=
        div_le_div_of_nonneg_right hmaxΛ hLpos.le
      have h2 : (c + 1) * (max Λ 0 / Real.log (q : ℝ))
          ≤ (c + 1) * (3 / Real.log (q : ℝ)) :=
        mul_le_mul_of_nonneg_left h1 (by linarith)
      have h3 : (c + 1) * (3 / Real.log (q : ℝ)) = 3 * (c + 1) / Real.log (q : ℝ) := by ring
      linarith [h2, h3]
    have hprod : Real.log ((q : ℝ) * (10 * Real.log (q : ℝ))) * ((c + 1) * (1 - σ))
        ≤ 6 * (c + 1) := by
      have h4 := mul_le_mul hlogb hE' hE hlogbnn
      have h5 : 2 * Real.log (q : ℝ) * (3 * (c + 1) / Real.log (q : ℝ)) = 6 * (c + 1) := by
        field_simp
        ring
      linarith [h4, h5]
    calc ((q : ℝ) * T) ^ ((c + 1) * (1 - σ))
        ≤ ((q : ℝ) * (10 * Real.log (q : ℝ))) ^ ((c + 1) * (1 - σ)) :=
          Real.rpow_le_rpow hbase0 hbase hE
      _ = Real.exp (Real.log ((q : ℝ) * (10 * Real.log (q : ℝ))) * ((c + 1) * (1 - σ))) :=
          Real.rpow_def_of_pos hbasepos _
      _ ≤ Real.exp (6 * (c + 1)) := Real.exp_le_exp.mpr hprod
  rw [hσdef, hTdef] at hbound hkey
  calc Work.ZeroFreeTables.otherLamCount χ₁ Λ H
      ≤ ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          Work.LinnikAreas.zeroCountIn χ (1 - max Λ 0 / Real.log (q : ℝ)) (max H 1) := hcount
    _ ≤ C₁ * ((q : ℝ) * max H 1)
          ^ ((c + 1) * (1 - (1 - max Λ 0 / Real.log (q : ℝ)))) := hbound
    _ ≤ C₁ * Real.exp (6 * (c + 1)) := mul_le_mul_of_nonneg_left hkey hC₁pos.le

end Work.ZeroFreeTables
