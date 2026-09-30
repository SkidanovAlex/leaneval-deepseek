import Mathlib
import Submission.Work.BW.Defs
import Submission.Work.BW.auxpolydefs
import Submission.Work.BW.card_multIdx
import Submission.Work.BW.factorial_pow_ge
import Submission.Work.BW.Mu_lower_bound
import Submission.Work.BW.Me_upper_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- The number of unknowns of the BW §13 system dominates the number of equations by a factor
`> 3.3`, which is what makes the Siegel factor `rho = M_e/(M_u - M_e)` at most `0.45`.

PROOF SKETCH.  With `d = [K:ℚ]`, `D = pD r d σ`, `S = 16 r d h`, `T = ⌊11.75 r D⌋`,
`D₀ = ⌊rD/(2 log(2rd))⌋`, `D_j = ⌊D/(r d σ_j)⌋`:
* `M_e = (2S+1)·binom(T+r,r) ≤ 32.1·r·d·h·D^r(11.75r+1)^r/r!`
  (companion lemma `Me_upper_bound`: `card_multIdx`, `Nat.choose_le_pow_div`, `T + r ≤ (11.75r+1)D`);
* `M_u = h(D₀+1)∏(D_j+1) ≥ h·r·d·32^{r+1}·D^r`
  (companion lemma `Mu_lower_bound`: `⌊x⌋₊ + 1 > x` for every floor argument, and the exact
  cancellation `D/(2 log(2rd) ∏σ) = r^r (32d)^{r+1}`);
* the ratio `M_u/M_e` is therefore at least `(32/32.1)·r!·32^r/(11.75r+1)^r ≥ (32/32.1)·3.4 > 3.3`
  (companion lemma `factorial_pow_ge`: `105.93·(11.75r+1)^r ≤ 32^{r+1}·r!` for `r ≥ 2`).
The strict inequality follows from `M_e ≥ 1`. -/
theorem Mu_ge_Me {K : Type*} [Field K] [NumberField K] (r h : ℕ) (hr : 2 ≤ r) (hh : 19 ≤ h)
    (σ : Fin r → ℝ) (hσ : ∀ j, 1 / (Module.finrank ℚ K : ℝ) ≤ σ j) :
    (3.3 : ℝ) * (Fintype.card (AuxEqnIdx r (pS r (Module.finrank ℚ K) h)
        (pT r (Module.finrank ℚ K) σ)) : ℝ)
      ≤ ((h * (pD0 r (Module.finrank ℚ K) σ + 1) *
          ∏ j, (pDj r (Module.finrank ℚ K) σ j + 1) : ℕ) : ℝ)
    ∧ Fintype.card (AuxEqnIdx r (pS r (Module.finrank ℚ K) h) (pT r (Module.finrank ℚ K) σ))
        < h * (pD0 r (Module.finrank ℚ K) σ + 1) * ∏ j, (pDj r (Module.finrank ℚ K) σ j + 1) := by
  have hMe := Me_upper_bound (K := K) r h hr hh σ hσ
  have hMu := Mu_lower_bound (K := K) r h hr σ hσ
  have hnum := factorial_pow_ge r hr
  have hd : 1 ≤ Module.finrank ℚ K := Module.finrank_pos
  have hdR1 : (1 : ℝ) ≤ (Module.finrank ℚ K : ℝ) := by exact_mod_cast hd
  have hdR : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by linarith
  have hprodpos : 0 < ∏ j, σ j := Finset.prod_pos fun j _ => by
    have := hσ j
    have h1 : (0 : ℝ) < 1 / (Module.finrank ℚ K : ℝ) := by positivity
    linarith
  have hlogpos : 0 < Real.log (2 * (r : ℝ) * (Module.finrank ℚ K : ℝ)) := by
    apply Real.log_pos
    have h4 : (2 : ℝ) * 1 ≤ (r : ℝ) * (Module.finrank ℚ K : ℝ) :=
      mul_le_mul (by exact_mod_cast hr) hdR1 (by norm_num) (by positivity)
    have : (4 : ℝ) ≤ 2 * (r : ℝ) * (Module.finrank ℚ K : ℝ) := by nlinarith
    linarith
  have hpD : 0 < pD r (Module.finrank ℚ K) σ := by
    rw [pD]
    have h1 : (0 : ℝ) < (r : ℝ) ^ r := by positivity
    have h2 : (0 : ℝ) < (32 * (Module.finrank ℚ K : ℝ)) ^ (r + 1) := by positivity
    have h3 : (0 : ℝ) < (↑(32 * Module.finrank ℚ K) : ℝ) := by positivity
    positivity
  have hDnn : (0 : ℝ) ≤ pD r (Module.finrank ℚ K) σ := le_of_lt hpD
  have hF : (0 : ℝ) < (r.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos r
  have hY : (0 : ℝ) ≤ (r : ℝ) * (Module.finrank ℚ K : ℝ) * (h : ℝ) *
      (pD r (Module.finrank ℚ K) σ) ^ r :=
    mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg r) (Nat.cast_nonneg _))
      (Nat.cast_nonneg h)) (pow_nonneg hDnn r)
  have s1 : (3.3 : ℝ) *
        ((Fintype.card (AuxEqnIdx r (pS r (Module.finrank ℚ K) h)
          (pT r (Module.finrank ℚ K) σ)) : ℝ) * (r.factorial : ℝ))
      ≤ 3.3 * (32.1 * (r : ℝ) * (Module.finrank ℚ K : ℝ) * (h : ℝ) *
          (11.75 * (r : ℝ) + 1) ^ r * (pD r (Module.finrank ℚ K) σ) ^ r) :=
    mul_le_mul_of_nonneg_left hMe (by norm_num)
  have s2 : 3.3 * (32.1 * (r : ℝ) * (Module.finrank ℚ K : ℝ) * (h : ℝ) *
        (11.75 * (r : ℝ) + 1) ^ r * (pD r (Module.finrank ℚ K) σ) ^ r)
      = (r : ℝ) * (Module.finrank ℚ K : ℝ) * (h : ℝ) * (pD r (Module.finrank ℚ K) σ) ^ r *
        ((105.93 : ℝ) * (11.75 * (r : ℝ) + 1) ^ r) := by ring
  have s3 : (r : ℝ) * (Module.finrank ℚ K : ℝ) * (h : ℝ) *
        (pD r (Module.finrank ℚ K) σ) ^ r * ((105.93 : ℝ) * (11.75 * (r : ℝ) + 1) ^ r)
      ≤ (r : ℝ) * (Module.finrank ℚ K : ℝ) * (h : ℝ) *
        (pD r (Module.finrank ℚ K) σ) ^ r * ((32 : ℝ) ^ (r + 1) * (r.factorial : ℝ)) :=
    mul_le_mul_of_nonneg_left hnum hY
  have s4 : (r : ℝ) * (Module.finrank ℚ K : ℝ) * (h : ℝ) *
        (pD r (Module.finrank ℚ K) σ) ^ r * ((32 : ℝ) ^ (r + 1) * (r.factorial : ℝ))
      = (r.factorial : ℝ) * ((h : ℝ) * (r : ℝ) * (Module.finrank ℚ K : ℝ) *
        (32 : ℝ) ^ (r + 1) * (pD r (Module.finrank ℚ K) σ) ^ r) := by ring
  have s5 := mul_le_mul_of_nonneg_left hMu (le_of_lt hF)
  have main : (3.3 : ℝ) * (Fintype.card (AuxEqnIdx r (pS r (Module.finrank ℚ K) h)
        (pT r (Module.finrank ℚ K) σ)) : ℝ) * (r.factorial : ℝ)
      ≤ (r.factorial : ℝ) * ((h * (pD0 r (Module.finrank ℚ K) σ + 1) *
          ∏ j, (pDj r (Module.finrank ℚ K) σ j + 1) : ℕ) : ℝ) := by
    calc (3.3 : ℝ) * (Fintype.card (AuxEqnIdx r (pS r (Module.finrank ℚ K) h)
            (pT r (Module.finrank ℚ K) σ)) : ℝ) * (r.factorial : ℝ)
        = 3.3 * ((Fintype.card (AuxEqnIdx r (pS r (Module.finrank ℚ K) h)
            (pT r (Module.finrank ℚ K) σ)) : ℝ) * (r.factorial : ℝ)) := by ring
      _ ≤ _ := s1
      _ = _ := s2
      _ ≤ _ := s3
      _ = _ := s4
      _ ≤ _ := s5
  have h1 : (3.3 : ℝ) * (Fintype.card (AuxEqnIdx r (pS r (Module.finrank ℚ K) h)
        (pT r (Module.finrank ℚ K) σ)) : ℝ)
      ≤ ((h * (pD0 r (Module.finrank ℚ K) σ + 1) *
          ∏ j, (pDj r (Module.finrank ℚ K) σ j + 1) : ℕ) : ℝ) := by
    have hh2 : (3.3 : ℝ) * (Fintype.card (AuxEqnIdx r (pS r (Module.finrank ℚ K) h)
          (pT r (Module.finrank ℚ K) σ)) : ℝ) * (r.factorial : ℝ)
        ≤ ((h * (pD0 r (Module.finrank ℚ K) σ + 1) *
            ∏ j, (pDj r (Module.finrank ℚ K) σ j + 1) : ℕ) : ℝ) * (r.factorial : ℝ) := by
      simpa [mul_comm] using main
    exact le_of_mul_le_mul_right hh2 hF
  refine ⟨h1, ?_⟩
  have hcard : 0 < Fintype.card (AuxEqnIdx r (pS r (Module.finrank ℚ K) h)
      (pT r (Module.finrank ℚ K) σ)) :=
    Fintype.card_pos_iff.mpr
      ⟨⟨⟨0, by simp [Finset.mem_Icc]⟩, ⟨(0, fun _ => 0), by simp⟩⟩⟩
  have hc1 : (1 : ℝ) ≤ (Fintype.card (AuxEqnIdx r (pS r (Module.finrank ℚ K) h)
      (pT r (Module.finrank ℚ K) σ)) : ℝ) := by exact_mod_cast hcard
  have : (Fintype.card (AuxEqnIdx r (pS r (Module.finrank ℚ K) h)
      (pT r (Module.finrank ℚ K) σ)) : ℝ)
      < ((h * (pD0 r (Module.finrank ℚ K) σ + 1) *
          ∏ j, (pDj r (Module.finrank ℚ K) σ j + 1) : ℕ) : ℝ) := by nlinarith
  exact_mod_cast this

end Work.BW
