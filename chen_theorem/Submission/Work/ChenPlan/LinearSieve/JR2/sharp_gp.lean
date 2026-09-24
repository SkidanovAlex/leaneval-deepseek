import Mathlib
import Submission.Work.ChenPlan.LinearSieve.JR2.Defs
import Submission.Work.ChenPlan.LinearSieve.JR2.sharp_sieve_upper
import Submission.Work.ChenPlan.LinearSieve.JR2.sharp_sieve_lower
import Submission.Work.ChenPlan.LinearSieve.RI.identity_plus
import Submission.Work.ChenPlan.LinearSieve.RI.identity_minus

/-!
# The `Gp`/`Gm` main-term bounds under the sharp normalisation

`RI.Gp A Z D` (resp. `RI.Gm A Z D`) is the `λ⁺` (resp. `λ⁻`) main-term sum over the divisors of
`Pz A Z`.  `RI.identity_plus` / `RI.identity_minus` express them as `VfR A Z ± Σ_{n odd/even} T_n`,
so the per-layer bound `LayerSharpBound` gives the main-term bounds directly (no upper-Moebius
property needed).  These are the statements the `Q`-trick consumes.
-/

open Finset
open scoped BigOperators

set_option autoImplicit false

namespace Work.ChenPlan.LinearSieve.JR2

noncomputable section

open Classical
open Work.NumberTheory.Chen.APSwitchUpper

set_option maxHeartbeats 1000000

/-- The finite **odd** layer sum is bounded by `VfR A Z·(riPhi s + ε C₂ errH s)`. -/
theorem sum_odd_T_le_riPhi {C ρ : ℝ} (hC : 0 ≤ C) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 99/100)
    (hLayer : LayerSharpBound C ρ) (A : BoundingSieve)
    {ε Z D : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1/100) (hZ : 2 ≤ Z) (hD : 1 ≤ D)
    (hSharp : SharpNorm A Z ε) (hs : 1 ≤ Real.log D / Real.log Z) :
    ∑ n ∈ (Finset.range (Nat.log 2 ⌈D⌉₊ + 3)).filter (fun n : ℕ => Odd n), T A n D Z
      ≤ VfR A Z * (riPhi (Real.log D / Real.log Z)
          + ε * (C * 10100) * errH (Real.log D / Real.log Z)) := by
  set s : ℝ := Real.log D / Real.log Z with hsdef
  set F : Finset ℕ := (Finset.range (Nat.log 2 ⌈D⌉₊ + 3)).filter (fun n : ℕ => Odd n) with hF
  have hterm : ∀ n ∈ F, T A n D Z ≤ VfR A Z *
      (profC (n - 1) s + ε * C * ((n : ℝ) + 1) * ρ ^ (n - 1) * errH s) := by
    intro n hn
    rw [hF, Finset.mem_filter] at hn
    obtain ⟨-, hodd⟩ := hn
    have hn1 : 1 ≤ n := by obtain ⟨k, hk⟩ := hodd; omega
    have hb := hLayer (A := A) (ε := ε) (D := D) (z := Z) hε0 hε1 hZ hD hSharp n hn1
      (fun _ => by rw [← hsdef]; exact hs) (fun he => absurd he (Nat.not_even_iff_odd.mpr hodd))
    rw [hsdef]
    exact hb
  have hinner : ∑ n ∈ F, (profC (n - 1) s + ε * C * ((n : ℝ) + 1) * ρ ^ (n - 1) * errH s)
      ≤ riPhi s + ε * (C * 10100) * errH s := by
    rw [Finset.sum_add_distrib]
    refine add_le_add ?_ ?_
    · have h := sum_odd_profC_le_riPhi_aux (Nat.log 2 ⌈D⌉₊ + 3) (s := s) (by rw [hsdef]; exact hs)
      rw [hF]
      exact h
    · have hfac : ∑ n ∈ F, ε * C * ((n : ℝ) + 1) * ρ ^ (n - 1) * errH s
          = (ε * C * errH s) * ∑ n ∈ F, (((n : ℝ) + 1) * ρ ^ (n - 1)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun n _ => by ring)
      rw [hfac]
      have hg := sum_odd_geom_le_10100 (Nat.log 2 ⌈D⌉₊ + 3) hρ hρ1
      rw [hF]
      have herr : 0 ≤ ε * C * errH s :=
        mul_nonneg (mul_nonneg hε0 hC) (errH_nonneg s)
      calc (ε * C * errH s) * ∑ n ∈ F, (((n : ℝ) + 1) * ρ ^ (n - 1))
          ≤ (ε * C * errH s) * 10100 := mul_le_mul_of_nonneg_left hg herr
        _ = ε * (C * 10100) * errH s := by ring
  calc ∑ n ∈ F, T A n D Z
      ≤ ∑ n ∈ F, VfR A Z * (profC (n - 1) s + ε * C * ((n : ℝ) + 1) * ρ ^ (n - 1) * errH s) :=
        Finset.sum_le_sum hterm
    _ = VfR A Z * ∑ n ∈ F,
          (profC (n - 1) s + ε * C * ((n : ℝ) + 1) * ρ ^ (n - 1) * errH s) := by
        rw [Finset.mul_sum]
    _ ≤ VfR A Z * (riPhi s + ε * (C * 10100) * errH s) :=
        mul_le_mul_of_nonneg_left hinner (VfR_nonneg A Z)
    _ = VfR A Z * (riPhi (Real.log D / Real.log Z)
          + ε * (C * 10100) * errH (Real.log D / Real.log Z)) := by rw [hsdef]

/-- `λ⁻(·, D, d)` depends on the modulus only through the divisibility `d ∣ P`. -/
lemma lamMinus_eq_of_dvd {P P' : ℕ} {D : ℝ} {d : ℕ} (hd : d ∣ P) (hd' : d ∣ P') :
    lamMinus P D d = lamMinus P' D d := by
  unfold lamMinus
  by_cases h : rdMinus D d
  · rw [if_pos ⟨hd, h⟩, if_pos ⟨hd', h⟩]
  · rw [if_neg (fun hc => h hc.2), if_neg (fun hc => h hc.2)]

/-- `RI.Gp` is the `λ⁺` main-term sum over the divisors of `Pz A Z`. -/
theorem Gp_eq_sum_lamPlus (A : BoundingSieve) (Z D : ℝ) :
    ∑ d ∈ (Pz A Z).divisors, lamPlus (Pz A Z) D d * A.nu d = RI.Gp A Z D := by
  unfold RI.Gp
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have hdd : d ∣ Pz A Z := (Nat.mem_divisors.mp hd).1
  have hrd : lamPlus (Pz A Z) D d
      = (if rdPlus D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0) := by
    unfold lamPlus
    by_cases h : rdPlus D d
    · rw [if_pos ⟨hdd, h⟩, if_pos h]
    · rw [if_neg (fun hc => h hc.2), if_neg h]
  rw [hrd]

/-- `RI.Gm` is the `λ⁻` main-term sum over the divisors of `Pz A Z`. -/
theorem Gm_eq_sum_lamMinus (A : BoundingSieve) (Z D : ℝ) :
    ∑ d ∈ (Pz A Z).divisors, lamMinus (Pz A Z) D d * A.nu d = RI.Gm A Z D := by
  unfold RI.Gm
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have hdd : d ∣ Pz A Z := (Nat.mem_divisors.mp hd).1
  have hrd : lamMinus (Pz A Z) D d
      = (if rdMinus D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0) := by
    unfold lamMinus
    by_cases h : rdMinus D d
    · rw [if_pos ⟨hdd, h⟩, if_pos h]
    · rw [if_neg (fun hc => h hc.2), if_neg h]
  rw [hrd]

/-- **The `λ⁺` main-term bound under the sharp normalisation.** -/
theorem sharp_gp (C ρ : ℝ) (hC : 0 ≤ C) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 99/100) :
    SharpGp C ρ (C * 10100) := by
  intro hLayer A ε Z D hε0 hε1 hZ hD hSharp hs
  have hZ1 : (1 : ℝ) < Z := by linarith
  have hlogZpos : 0 < Real.log Z := Real.log_pos hZ1
  have hlogDpos : 0 < Real.log D := by
    have h := (le_div_iff₀ hlogZpos).mp hs
    linarith
  have hDne1 : D ≠ 1 := by
    intro h
    rw [h, Real.log_one] at hlogDpos
    exact lt_irrefl 0 hlogDpos
  have hDgt1 : 1 < D := lt_of_le_of_ne hD (Ne.symm hDne1)
  have hGp : RI.Gp A Z D = VfR A Z
      + ∑ n ∈ (Finset.range (Nat.log 2 ⌈D⌉₊ + 3)).filter (fun n : ℕ => Odd n), T A n D Z := by
    rw [← Gp_eq_sum_lamPlus A Z D, ← RI.identity_plus A (D := D) (z := Z) (le_of_lt hDgt1)]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    have hdd : d ∣ Pz A Z := (Nat.mem_divisors.mp hd).1
    rw [lamPlus_eq_of_dvd hdd (dvd_trans hdd (RI.Pz_dvd_prodPrimes A Z))]
  have hsum := sum_odd_T_le_riPhi hC hρ hρ1 hLayer A hε0 hε1 hZ hD hSharp hs
  rw [hGp]
  linarith [mul_le_mul_of_nonneg_left hsum (VfR_nonneg A Z)]

/-- **The `λ⁻` main-term bound under the sharp normalisation.** -/
theorem sharp_gm (C ρ : ℝ) (hC : 0 ≤ C) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 99/100) :
    SharpGm C ρ (C * 10100) := by
  intro hLayer A ε Z D hε0 hε1 hZ hD hSharp hs
  have hZ1 : (1 : ℝ) < Z := by linarith
  have hlogZpos : 0 < Real.log Z := Real.log_pos hZ1
  have hlogDpos : 0 < Real.log D := by
    have h := (le_div_iff₀ hlogZpos).mp (le_trans (by norm_num : (1:ℝ) ≤ 2) hs)
    linarith
  have hDne1 : D ≠ 1 := by
    intro h
    rw [h, Real.log_one] at hlogDpos
    exact lt_irrefl 0 hlogDpos
  have hDgt1 : 1 < D := lt_of_le_of_ne hD (Ne.symm hDne1)
  have hGm : RI.Gm A Z D = VfR A Z
      - ∑ n ∈ (Finset.range (Nat.log 2 ⌈D⌉₊ + 3)).filter (fun n : ℕ => Even n ∧ n ≠ 0),
          T A n D Z := by
    rw [← Gm_eq_sum_lamMinus A Z D, ← RI.identity_minus A (D := D) (z := Z) (le_of_lt hDgt1)]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    have hdd : d ∣ Pz A Z := (Nat.mem_divisors.mp hd).1
    rw [lamMinus_eq_of_dvd hdd (dvd_trans hdd (RI.Pz_dvd_prodPrimes A Z))]
  have hsum := sum_T_le_riPsi hC hρ hρ1 hLayer A hε0 hε1 hZ hD hSharp hs
  rw [hGm]
  have hV := VfR_nonneg A Z
  have := mul_le_mul_of_nonneg_left hsum hV
  linarith

end

end Work.ChenPlan.LinearSieve.JR2
