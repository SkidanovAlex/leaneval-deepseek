import Mathlib
import Submission.Work.ChenPlan.LinearSieve.JR2.Defs
import Submission.Work.ChenPlan.LinearSieve.RI.identity_plus
import Submission.Work.ChenPlan.LinearSieve.RI.upper_moebius
import Submission.Work.ChenPlan.LinearSieve.Assembly.rem_bound_plus
import Submission.Work.ChenPlan.LinearSieve.RIMain.LayerAux

namespace Work.ChenPlan.LinearSieve.JR2

open Finset
open scoped BigOperators
open Work.NumberTheory.Chen.APSwitchUpper

noncomputable section

open Classical

set_option maxHeartbeats 1000000

/-! ## Auxiliary lemmas for the sharp upper sieve

The four ingredients of the assembly:

* `lamPlus_eq_of_dvd`: the upper Rosser–Iwaniec weight only sees `d` through the modulus `P` via
  the divisibility `d ∣ P`, so `λ⁺(P,D,d) = λ⁺(P',D,d)` for two moduli both divisible by `d`.
  This lets us pass between the modulus `A.prodPrimes` (used by `RI.identity_plus`) and the
  sift-limit modulus `Pz A Z` (used by `remSum`/the layer bound).
* `siftedSumR_le_sum_lamPlus`: Mathlib's `siftedSum_le_sum_of_upperMoebius` for the *sub-sieve*
  with `prodPrimes = Pz A Z`, which is exactly the problem that `siftedSumR A Z` sifts.
* `sum_odd_geom_le_10100`: `Σ_{n odd < N}(n+1)ρ^{n-1} ≤ 10100` for `ρ ≤ 99/100` — this is the
  constant that `C₂ = C·10100` absorbs.
* `sum_odd_profC_le_riPhi_aux`: the finite odd layer sum of the profiles is dominated by the full
  even series `riPhi s`. -/

/-- `λ⁺(·, D, d)` depends on the modulus only through the divisibility `d ∣ P`. -/
lemma lamPlus_eq_of_dvd {P P' : ℕ} {D : ℝ} {d : ℕ} (hd : d ∣ P) (hd' : d ∣ P') :
    lamPlus P D d = lamPlus P' D d := by
  unfold lamPlus
  by_cases h : rdPlus D d
  · rw [if_pos ⟨hd, h⟩, if_pos ⟨hd', h⟩]
  · rw [if_neg (fun hc => h hc.2), if_neg (fun hc => h hc.2)]

/-- **The upper Möbius bound for the sift-limit problem `P(Z)`.**  Mathlib's
`BoundingSieve.siftedSum_le_sum_of_upperMoebius` applied to the sub-sieve whose `prodPrimes` is
`Pz A Z` (same support, weights, `totalMass` and `ν`).  The sifted sum of that sub-sieve is exactly
`siftedSumR A Z`, by `RI.coprime_Pz_iff`. -/
theorem siftedSumR_le_sum_lamPlus (A : BoundingSieve) (D Z : ℝ) :
    siftedSumR A Z ≤ ∑ d ∈ (Pz A Z).divisors, lamPlus (Pz A Z) D d * A.multSum d := by
  let A' : BoundingSieve :=
    { support := A.support
      prodPrimes := Pz A Z
      prodPrimes_squarefree := RI.Pz_squarefree A Z
      weights := A.weights
      weights_nonneg := A.weights_nonneg
      totalMass := A.totalMass
      nu := A.nu
      nu_mult := A.nu_mult
      nu_pos_of_prime := fun p hp hd =>
        A.nu_pos_of_prime p hp (dvd_trans hd (RI.Pz_dvd_prodPrimes A Z))
      nu_lt_one_of_prime := fun p hp hd =>
        A.nu_lt_one_of_prime p hp (dvd_trans hd (RI.Pz_dvd_prodPrimes A Z)) }
  have hsift : A'.siftedSum = siftedSumR A Z := by
    unfold BoundingSieve.siftedSum siftedSumR
    refine Finset.sum_congr rfl (fun n _ => ?_)
    have hiff : (Nat.Coprime (Pz A Z) n) ↔
        (∀ p ∈ A.prodPrimes.primeFactors, (p : ℝ) < Z → ¬ p ∣ n) := by
      rw [Nat.coprime_comm, Nat.coprime_iff_gcd_eq_one, RI.coprime_Pz_iff A n Z]
    by_cases h : Nat.Coprime (Pz A Z) n
    · rw [if_pos h, if_pos (hiff.mp h)]
    · rw [if_neg h, if_neg (fun hc => h (hiff.mpr hc))]
  have hmoeb := BoundingSieve.siftedSum_le_sum_of_upperMoebius (s := A')
      (lamPlus (Pz A Z) D) (RI.upper_moebius (Pz A Z) D)
  rw [hsift] at hmoeb
  simpa using hmoeb

/-- `Σ_{n odd, n < N} (n+1) ρ^{n-1} ≤ 10100` for `0 ≤ ρ ≤ 99/100`.  Reindexing `n = 2j+1` turns
the sum into `Σ_j (2j+2)(ρ²)^j = 2/(1-ρ²)² ≤ 2(10000/199)² ≤ 10100` (the sharper full-series value
`(2-ρ)/(1-ρ)² = 10100` at `ρ = 99/100` is not needed). -/
theorem sum_odd_geom_le_10100 (N : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 99/100) :
    ∑ n ∈ (Finset.range N).filter (fun n : ℕ => Odd n), ((n : ℝ) + 1) * ρ ^ (n - 1) ≤ 10100 := by
  rw [RI.filter_odd_range_eq]
  rw [Finset.sum_image]
  swap
  · intro a _ b _ h
    have h' : 2 * a + 1 = 2 * b + 1 := h
    omega
  have hρ2 : ‖ρ ^ 2‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [hρ, hρ1]
  have hS : Summable (fun j : ℕ => ((j : ℝ) + 1) * (ρ ^ 2) ^ j) := by
    have h := (hasSum_coe_mul_geometric_of_norm_lt_one hρ2).summable.add
      (summable_geometric_of_norm_lt_one hρ2)
    refine h.congr (fun j => ?_)
    ring
  calc ∑ j ∈ Finset.range (N / 2), ((↑(2 * j + 1) : ℝ) + 1) * ρ ^ (2 * j + 1 - 1)
      = ∑ j ∈ Finset.range (N / 2), 2 * (((j : ℝ) + 1) * (ρ ^ 2) ^ j) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [show ρ ^ (2 * j + 1 - 1) = (ρ ^ 2) ^ j from by
          rw [Nat.add_sub_cancel, pow_mul]]
        push_cast
        ring
    _ = 2 * ∑ j ∈ Finset.range (N / 2), ((j : ℝ) + 1) * (ρ ^ 2) ^ j := by
        rw [Finset.mul_sum]
    _ ≤ 2 * (1 - ρ ^ 2)⁻¹ ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        rw [← RI.tsum_succ_mul_pow (ρ ^ 2) hρ2]
        exact hS.sum_le_tsum _ (fun j _ => by positivity)
    _ ≤ 10100 := by
        have hx : 0 < 1 - ρ ^ 2 := by nlinarith
        have hge : (199 / 10000 : ℝ) ≤ 1 - ρ ^ 2 := by nlinarith
        have hinv : (1 - ρ ^ 2)⁻¹ ≤ (199 / 10000 : ℝ)⁻¹ := by
          rw [inv_le_inv₀ hx (by norm_num : (0 : ℝ) < 199 / 10000)]
          exact hge
        have h2 := pow_le_pow_left₀ (inv_nonneg.mpr hx.le) hinv 2
        nlinarith [h2]

/-- The finite odd layer sum of the profiles is dominated by the full even series `riPhi s`
(reindex `n = 2j+1`, then `profC_nonneg` and `RI.summable_profC_two_mul`). -/
theorem sum_odd_profC_le_riPhi_aux (N : ℕ) {s : ℝ} (hs : 1 ≤ s) :
    ∑ n ∈ (Finset.range N).filter (fun n : ℕ => Odd n), profC (n - 1) s ≤ riPhi s := by
  rw [RI.filter_odd_range_eq]
  rw [Finset.sum_image]
  swap
  · intro a _ b _ h
    have h' : 2 * a + 1 = 2 * b + 1 := h
    omega
  rw [riPhi]
  exact (RI.summable_profC_two_mul s hs).sum_le_tsum _ (fun j _ => profC_nonneg _ _)

/-- **The sharp-normalised `λ⁺` (upper) sieve**, from the per-layer bound `LayerSharpBound C ρ`
(defined in `JR2/Defs.lean`; see `JR2/NOTES.md` for the whole route).

NOTE: `Submission/Work/ChenPlan/LinearSieve/Assembly/sieve_of_main.lean` does NOT compile under
the v5/v6 interface change — do NOT import it; read it for the blueprint of the assembly and
reprove what you need here.  Working ingredients: `RI/upper_moebius.lean` (`λ⁺` is upper Moebius),
`Assembly/rem_bound_plus.lean` (the `λ⁺` remainder `≤ remSum A D`, needs `1 < D`),
`RI/identity_plus.lean` (`RI.Gp A z D = VfR A z + Σ_{n odd < N} T_n`, `N = Nat.log 2 ⌈D⌉₊ + 3`),
`RI/basic.lean` (`T`), `APSwitchUpper/prof.lean` (`profC`, `riPhi`), `RIMain/LayerAux.lean`
(`RI.summable_profC_two_mul`).

Assembly: `siftedSumR A Z ≤ Σ_{d ∣ Pz} λ⁺(d) multSum d ≤ X·Gp + remSum A D`
(`BoundingSieve.siftedSum_le_sum_of_upperMoebius`), then `Gp = VfR Z + Σ_{odd n < N} T_n` and the
per-layer bound gives `T_n ≤ VfR Z·(profC (n-1) s + ε C (n+1) ρ^{n-1} errH s)`; the sum over odd
`n < N` of `profC (n-1) s` is `≤ riPhi s` (nonnegative summands + summability), and
`Σ_{n ≥ 1} (n+1)ρ^{n-1} = (2-ρ)/(1-ρ)² ≤ 10100` for `ρ ≤ 99/100` absorbs the allowance. -/
theorem sharp_sieve_upper (C ρ : ℝ) (hC : 0 ≤ C) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 99/100) :
    Work.ChenPlan.LinearSieve.JR2.SharpSieveUpper C ρ (C * 10100) := by
  intro hL A ε Z D hε0 hε1 hZ2 hD1 hSN hX hs
  -- the level is `> 1`: `s ≥ 1` forces `log D ≥ log Z > 0`, so `D ≠ 1`
  have hZ1 : (1 : ℝ) < Z := by linarith
  have hlogZpos : 0 < Real.log Z := Real.log_pos hZ1
  have hlogZle : Real.log Z ≤ Real.log D := by
    have h := (le_div_iff₀ hlogZpos).mp hs
    simpa using h
  have hlogDpos : 0 < Real.log D := lt_of_lt_of_le hlogZpos hlogZle
  have hDne1 : D ≠ 1 := by
    intro h
    rw [h, Real.log_one] at hlogDpos
    exact lt_irrefl 0 hlogDpos
  have hDgt1 : 1 < D := lt_of_le_of_ne hD1 (Ne.symm hDne1)
  -- the `λ⁺` main-term sum over the divisors of `P(Z)` is `Gp`
  have hGpsum : ∑ d ∈ (Pz A Z).divisors, lamPlus (Pz A Z) D d * A.nu d = RI.Gp A Z D := by
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
  -- `Gp` is the product plus the odd layers (`RI.identity_plus`)
  have hGp : RI.Gp A Z D = VfR A Z
      + ∑ n ∈ (Finset.range (Nat.log 2 ⌈D⌉₊ + 3)).filter (fun n : ℕ => Odd n), T A n D Z := by
    rw [← hGpsum, ← RI.identity_plus A (D := D) (z := Z) (le_of_lt hDgt1)]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    have hdd : d ∣ Pz A Z := (Nat.mem_divisors.mp hd).1
    rw [lamPlus_eq_of_dvd hdd (dvd_trans hdd (RI.Pz_dvd_prodPrimes A Z))]
  -- split `multSum = ν · X + rem`
  have hsplit : ∑ d ∈ (Pz A Z).divisors, lamPlus (Pz A Z) D d * A.multSum d
      = A.totalMass * RI.Gp A Z D
        + ∑ d ∈ (Pz A Z).divisors, lamPlus (Pz A Z) D d * A.rem d := by
    calc ∑ d ∈ (Pz A Z).divisors, lamPlus (Pz A Z) D d * A.multSum d
        = ∑ d ∈ (Pz A Z).divisors, (lamPlus (Pz A Z) D d * (A.nu d * A.totalMass)
            + lamPlus (Pz A Z) D d * A.rem d) := by
          refine Finset.sum_congr rfl (fun d _ => ?_)
          rw [BoundingSieve.multSum_eq_main_err]
          ring
      _ = (∑ d ∈ (Pz A Z).divisors, lamPlus (Pz A Z) D d * A.nu d) * A.totalMass
            + ∑ d ∈ (Pz A Z).divisors, lamPlus (Pz A Z) D d * A.rem d := by
          rw [Finset.sum_add_distrib, Finset.sum_mul]
          congr 1
          exact Finset.sum_congr rfl (fun d _ => by ring)
      _ = A.totalMass * RI.Gp A Z D
            + ∑ d ∈ (Pz A Z).divisors, lamPlus (Pz A Z) D d * A.rem d := by
          rw [hGpsum]
          ring
  -- the remainder sum is absorbed by `remSum A D`
  have hrem : ∑ d ∈ (Pz A Z).divisors, lamPlus (Pz A Z) D d * A.rem d
      ≤ Submission.ChenPlan.remSum A D := by
    calc ∑ d ∈ (Pz A Z).divisors, lamPlus (Pz A Z) D d * A.rem d
        ≤ ∑ d ∈ (Pz A Z).divisors, |lamPlus (Pz A Z) D d| * |A.rem d| := by
          refine Finset.sum_le_sum (fun d _ => ?_)
          rw [← abs_mul]
          exact le_abs_self _
      _ = ∑ d ∈ (Pz A Z).divisors, |lamPlus A.prodPrimes D d| * |A.rem d| := by
          refine Finset.sum_congr rfl (fun d hd => ?_)
          have hdd : d ∣ Pz A Z := (Nat.mem_divisors.mp hd).1
          rw [lamPlus_eq_of_dvd hdd (dvd_trans hdd (RI.Pz_dvd_prodPrimes A Z))]
      _ ≤ ∑ d ∈ A.prodPrimes.divisors, |lamPlus A.prodPrimes D d| * |A.rem d| := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro d hd
            exact Nat.mem_divisors.mpr
              ⟨dvd_trans (Nat.mem_divisors.mp hd).1 (RI.Pz_dvd_prodPrimes A Z),
                A.prodPrimes_ne_zero⟩
          · intro d _ _
            positivity
      _ ≤ Submission.ChenPlan.remSum A D := Assembly.rem_bound_plus A hDgt1
  -- the per-layer bound summed over the odd layers
  have hlayer : ∑ n ∈ (Finset.range (Nat.log 2 ⌈D⌉₊ + 3)).filter (fun n : ℕ => Odd n), T A n D Z
      ≤ VfR A Z * (riPhi (Real.log D / Real.log Z)
          + ε * (C * 10100) * errH (Real.log D / Real.log Z)) := by
    have hpt : ∀ n ∈ (Finset.range (Nat.log 2 ⌈D⌉₊ + 3)).filter (fun n : ℕ => Odd n),
        T A n D Z ≤ VfR A Z * (profC (n - 1) (Real.log D / Real.log Z)
          + ε * C * ((n : ℝ) + 1) * ρ ^ (n - 1) * errH (Real.log D / Real.log Z)) := by
      intro n hn
      obtain ⟨hnM, hnodd⟩ := Finset.mem_filter.mp hn
      have hn1 : 1 ≤ n := by obtain ⟨k, hk⟩ := hnodd; omega
      exact hL (A := A) (ε := ε) (D := D) (z := Z) hε0 hε1 hZ2 hD1 hSN n hn1
        (fun _ => hs) (fun he => absurd he (Nat.not_even_iff_odd.mpr hnodd))
    calc ∑ n ∈ (Finset.range (Nat.log 2 ⌈D⌉₊ + 3)).filter (fun n : ℕ => Odd n), T A n D Z
        ≤ ∑ n ∈ (Finset.range (Nat.log 2 ⌈D⌉₊ + 3)).filter (fun n : ℕ => Odd n),
            VfR A Z * (profC (n - 1) (Real.log D / Real.log Z)
              + ε * C * ((n : ℝ) + 1) * ρ ^ (n - 1) * errH (Real.log D / Real.log Z)) :=
          Finset.sum_le_sum hpt
      _ = VfR A Z * ∑ n ∈ (Finset.range (Nat.log 2 ⌈D⌉₊ + 3)).filter (fun n : ℕ => Odd n),
            (profC (n - 1) (Real.log D / Real.log Z)
              + ε * C * ((n : ℝ) + 1) * ρ ^ (n - 1) * errH (Real.log D / Real.log Z)) := by
          rw [Finset.mul_sum]
      _ ≤ VfR A Z * (riPhi (Real.log D / Real.log Z)
            + ε * (C * 10100) * errH (Real.log D / Real.log Z)) := by
          refine mul_le_mul_of_nonneg_left ?_ (VfR_nonneg A Z)
          rw [Finset.sum_add_distrib]
          have h1 := sum_odd_profC_le_riPhi_aux (Nat.log 2 ⌈D⌉₊ + 3) hs
          have h2 : ∑ n ∈ (Finset.range (Nat.log 2 ⌈D⌉₊ + 3)).filter (fun n : ℕ => Odd n),
                ε * C * ((n : ℝ) + 1) * ρ ^ (n - 1) * errH (Real.log D / Real.log Z)
              ≤ ε * (C * 10100) * errH (Real.log D / Real.log Z) := by
            have hfac : ∑ n ∈ (Finset.range (Nat.log 2 ⌈D⌉₊ + 3)).filter (fun n : ℕ => Odd n),
                  ε * C * ((n : ℝ) + 1) * ρ ^ (n - 1) * errH (Real.log D / Real.log Z)
                = (ε * C * errH (Real.log D / Real.log Z))
                  * ∑ n ∈ (Finset.range (Nat.log 2 ⌈D⌉₊ + 3)).filter (fun n : ℕ => Odd n),
                      ((n : ℝ) + 1) * ρ ^ (n - 1) := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl (fun n _ => by ring)
            rw [hfac]
            calc (ε * C * errH (Real.log D / Real.log Z))
                  * ∑ n ∈ (Finset.range (Nat.log 2 ⌈D⌉₊ + 3)).filter (fun n : ℕ => Odd n),
                      ((n : ℝ) + 1) * ρ ^ (n - 1)
                ≤ (ε * C * errH (Real.log D / Real.log Z)) * 10100 :=
                  mul_le_mul_of_nonneg_left (sum_odd_geom_le_10100 _ hρ hρ1)
                    (mul_nonneg (mul_nonneg hε0 hC) (errH_nonneg _))
              _ = ε * (C * 10100) * errH (Real.log D / Real.log Z) := by ring
          linarith
  calc siftedSumR A Z
      ≤ ∑ d ∈ (Pz A Z).divisors, lamPlus (Pz A Z) D d * A.multSum d :=
        siftedSumR_le_sum_lamPlus A D Z
    _ = A.totalMass * RI.Gp A Z D
          + ∑ d ∈ (Pz A Z).divisors, lamPlus (Pz A Z) D d * A.rem d := hsplit
    _ ≤ A.totalMass * RI.Gp A Z D + Submission.ChenPlan.remSum A D := by linarith
    _ = A.totalMass * (VfR A Z
          + ∑ n ∈ (Finset.range (Nat.log 2 ⌈D⌉₊ + 3)).filter (fun n : ℕ => Odd n), T A n D Z)
          + Submission.ChenPlan.remSum A D := by rw [hGp]
    _ ≤ A.totalMass * (VfR A Z + VfR A Z * (riPhi (Real.log D / Real.log Z)
          + ε * (C * 10100) * errH (Real.log D / Real.log Z)))
          + Submission.ChenPlan.remSum A D :=
        add_le_add (mul_le_mul_of_nonneg_left (add_le_add le_rfl hlayer) hX) le_rfl
    _ = A.totalMass * VfR A Z * (1 + riPhi (Real.log D / Real.log Z)
          + ε * (C * 10100) * errH (Real.log D / Real.log Z))
          + Submission.ChenPlan.remSum A D := by ring

end

end Work.ChenPlan.LinearSieve.JR2
