import Mathlib
import Submission.Work.ZeroDensity.Jutila.Bz3Defs
import Submission.Work.ZeroDensity.Jutila.KappaMertensDefs
import Submission.Work.ZeroDensity.Jutila.KMSsumRecursion
import Submission.Work.ZeroDensity.Jutila.LzDiffAux.KMSsumOneDecayHere
import Submission.Work.ZeroDensity.Jutila.KMDcDivLe
import Submission.Work.ZeroDensity.Jutila.KMKappaGSum
import Submission.Work.ZeroDensity.Jutila.KMTsumAbel
import Submission.Work.ZeroDensity.Jutila.KMDcTailBound
import Submission.Work.ZeroDensity.Jutila.LzDiffAux.DcInvSumDyadicHere
import Submission.Work.ZeroDensity.Jutila.LzDiffAux.ExpSumNegSqrtSqBoundHere
import Submission.Work.ZeroDensity.Jutila.KMTsumTendsto


/-! Re-homing of `KappaMertens` into `Work.ZeroDensity.Jutila.LzDiffAux`, with the import of the
currently broken module `KMDcTailBound` replaced by an explicit invocation of the proved
`KMDcTailBound_aux` on the two inputs `DcInvSumDyadic` and `ExpSumNegSqrtSqBound`.  The main
theorem is named `KappaMertensHere`. -/

namespace Work.ZeroDensity.Jutila.LzDiffAux

open Finset

noncomputable section

/-- The `Dc`-tail bound, assembled from the two proved inputs `DcInvSumDyadic` and
`ExpSumNegSqrtSqBound` through `KMDcTailBound_aux`. -/
theorem KMDcTailBound :
    ∃ K : ℝ, 0 < K ∧ ∀ c : ℝ, 0 < c → ∀ N M : ℕ, N ≤ M →
      (∑ m ∈ Finset.Icc N M, Dc c m * Real.log (1 + 1 / (m : ℝ)))
        ≤ K * (1 + 1 / c) ^ 2 * Dc (c / 2) N :=
  KMDcTailBound_aux (fun d hd M => DcInvSumDyadic (d := d) hd M)
    (fun a ha J => ExpSumNegSqrtSqBound (a := a) ha J)

/-! ## Elementary evaluations of the two sums -/

lemma Ssum_zero (t : ℕ) : Ssum 0 t = 0 := by
  simp [Ssum]

lemma Ssum_one (t : ℕ) : Ssum 1 t = 1 := by
  have h : (Finset.Icc 1 1).filter (fun r => Nat.Coprime r t) = {1} := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨h1, h2⟩, _⟩
      omega
    · rintro rfl
      exact ⟨⟨le_rfl, le_rfl⟩, Nat.coprime_one_left t⟩
  rw [Ssum, h, Finset.sum_singleton]
  simp [kappa, ArithmeticFunction.moebius_apply_one]

lemma one_le_sigHalf {t : ℕ} (ht : 1 ≤ t) : 1 ≤ sigHalf t := by
  have hmem : 1 ∈ t.divisors := Nat.one_mem_divisors.mpr (by omega)
  have h := Finset.single_le_sum (f := fun d : ℕ => 1 / Real.sqrt (d : ℝ))
    (fun d _ => by positivity) hmem
  simpa [sigHalf] using h

lemma Tsum_zero (t : ℕ) : Tsum 0 t = 0 := by
  simp [Tsum]

/-- The target's `kap`-weighted version of `Ssum`. -/
lemma Ssum_eq_sum_if_kap (x t : ℕ) :
    Ssum x t = ∑ r ∈ Finset.Icc 1 x,
      (if Nat.Coprime r t then (ArithmeticFunction.moebius r : ℝ) / kap r else 0) := by
  rw [Ssum_eq_sum_if]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases h : Nat.Coprime r t
  · rw [if_pos h, if_pos h, mu_div_kappa_eq_mu_div_kap]
  · rw [if_neg h, if_neg h]

/-- The target's `kap`-weighted version of `Tsum`. -/
lemma Tsum_eq_sum_if_kap (x t : ℕ) :
    Tsum x t = ∑ r ∈ Finset.Icc 1 x,
      (if Nat.Coprime r t then (ArithmeticFunction.moebius r : ℝ) / kap r else 0)
        * Real.log ((x : ℝ) / (r : ℝ)) := by
  rw [Tsum_eq_sum_if]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases h : Nat.Coprime r t
  · rw [if_pos h, if_pos h, mu_div_kappa_eq_mu_div_kap]
  · rw [if_neg h, if_neg h]

/-! ## The unweighted decay, by induction on the modulus -/

/-- **Mertens-type decay of `Σ_{r ≤ x, (r,t)=1} μ(r)/κ(r)`**, uniformly in the squarefree modulus
`t`, with the divisor factor `sigHalf t = Σ_{d | t} d^{-1/2}`.

The recursion `KMSsumRecursion` reduces the modulus `t` to its divisors.  For `e = 1` one uses the
base case `KMSsumOneDecay`; for `1 < e < t` the induction on `t`; for `e = t` the induction on `x`.
The loss incurred by replacing `Dc c (x/e)` by `Dc c x` is paid by the factor `g e`, the content of
`KMDcDivLe`; the resulting divisor sum is evaluated exactly by `KMKappaGSum`. -/
theorem Ssum_decay : ∃ K c : ℝ, 0 < K ∧ 0 < c ∧
    ∀ (t x : ℕ), Squarefree t → |Ssum x t| ≤ K * sigHalf t * Dc c x := by
  obtain ⟨K₁, c₁, hK₁, hc₁, hdec⟩ := KMSsumOneDecay
  refine ⟨max K₁ 1, min c₁ (1 / 16), lt_max_of_lt_left hK₁, lt_min hc₁ (by norm_num), ?_⟩
  set c : ℝ := min c₁ (1 / 16) with hcdef
  have hcpos : 0 < c := lt_min hc₁ (by norm_num)
  have hcle : c ≤ c₁ := min_le_left _ _
  have hc16 : c ≤ 1 / 16 := min_le_right _ _
  have hK1 : (1 : ℝ) ≤ max K₁ 1 := le_max_right _ _
  have hKpos : (0 : ℝ) < max K₁ 1 := lt_of_lt_of_le zero_lt_one hK1
  have hdec' : ∀ x : ℕ, |Ssum x 1| ≤ max K₁ 1 * Dc c x := by
    intro x
    calc |Ssum x 1| ≤ K₁ * Dc c₁ x := hdec x
      _ ≤ max K₁ 1 * Dc c x :=
          mul_le_mul (le_max_left K₁ 1) (Dc_le_of_le_rate hcle x) (Dc_pos c₁ x).le
            (le_of_lt hKpos)
  have key : ∀ t : ℕ, Squarefree t → ∀ x : ℕ,
      |Ssum x t| ≤ max K₁ 1 * sigHalf t * Dc c x := by
    intro t
    refine Nat.strong_induction_on t ?_
    intro t ih ht x
    by_cases ht1 : t = 1
    · subst ht1
      rw [sigHalf_one]
      simpa using hdec' x
    · have ht0 : t ≠ 0 := fun h => by rw [h] at ht; exact not_squarefree_zero ht
      refine Nat.strong_induction_on x ?_
      intro x ihx
      by_cases hx : x ≤ 1
      · interval_cases x
        · rw [Ssum_zero, abs_zero]
          exact mul_nonneg (mul_nonneg hKpos.le (sigHalf_nonneg t)) (Dc_pos c 0).le
        · rw [Ssum_one, abs_one]
          have h1 : 1 ≤ sigHalf t := one_le_sigHalf (by omega)
          rw [show Dc c 1 = 1 by simp [Dc]]
          calc (1 : ℝ) = 1 * 1 * 1 := by ring
            _ ≤ max K₁ 1 * sigHalf t * 1 :=
                mul_le_mul (mul_le_mul hK1 h1 (by norm_num) (le_of_lt hKpos))
                  le_rfl (by norm_num) (mul_nonneg hKpos.le (sigHalf_nonneg t))
      · push_neg at hx
        rw [KMSsumRecursion x t ht]
        calc |∑ e ∈ t.divisors, (kappa e)⁻¹ * Ssum (x / e) e|
            ≤ ∑ e ∈ t.divisors, |(kappa e)⁻¹ * Ssum (x / e) e| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ e ∈ t.divisors, max K₁ 1 * Dc c x *
                ((kappa e)⁻¹ * sigHalf e
                  * ∏ p ∈ e.primeFactors, ((p : ℝ) + 1) / (Real.sqrt (p : ℝ) + 1)) := by
              refine Finset.sum_le_sum fun e he => ?_
              obtain ⟨hedvd, htne⟩ := Nat.mem_divisors.mp he
              have hepos : 0 < e := Nat.pos_of_dvd_of_pos hedvd (by omega)
              have hkpos : 0 < kappa e := kappa_pos hepos.ne'
              have hsfe : Squarefree e := Squarefree.squarefree_of_dvd hedvd ht
              have hgnn : 0 ≤ ∏ p ∈ e.primeFactors,
                  ((p : ℝ) + 1) / (Real.sqrt (p : ℝ) + 1) := by
                apply Finset.prod_nonneg
                intro p hp
                have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
                have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
                positivity
              have hmain : |Ssum (x / e) e| ≤ max K₁ 1 * sigHalf e * Dc c (x / e) := by
                rcases eq_or_lt_of_le (Nat.succ_le_of_lt hepos) with h1 | h2
                · subst h1
                  rw [Nat.div_one, sigHalf_one]
                  simpa using hdec' x
                · rcases eq_or_lt_of_le (Nat.le_of_dvd (by omega) hedvd) with h | h
                  · rw [h] at h2 ⊢
                    exact ihx (x / t) (Nat.div_lt_self (by omega) h2)
                  · exact ih e h hsfe (x / e)
              have hdiv := KMDcDivLe c hcpos hc16 x e hsfe
              calc |(kappa e)⁻¹ * Ssum (x / e) e|
                  = (kappa e)⁻¹ * |Ssum (x / e) e| := by
                    rw [abs_mul, abs_of_pos (inv_pos.mpr hkpos)]
                _ ≤ (kappa e)⁻¹ * (max K₁ 1 * sigHalf e * Dc c (x / e)) :=
                    mul_le_mul_of_nonneg_left hmain (inv_nonneg.mpr hkpos.le)
                _ ≤ (kappa e)⁻¹ * (max K₁ 1 * sigHalf e *
                      ((∏ p ∈ e.primeFactors, ((p : ℝ) + 1) / (Real.sqrt (p : ℝ) + 1))
                        * Dc c x)) := by
                    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hkpos.le)
                    exact mul_le_mul_of_nonneg_left hdiv
                      (mul_nonneg hKpos.le (sigHalf_nonneg e))
                _ = max K₁ 1 * Dc c x * ((kappa e)⁻¹ * sigHalf e
                      * ∏ p ∈ e.primeFactors, ((p : ℝ) + 1) / (Real.sqrt (p : ℝ) + 1)) := by
                    ring
          _ = max K₁ 1 * Dc c x * ∑ e ∈ t.divisors, ((kappa e)⁻¹ * sigHalf e
                * ∏ p ∈ e.primeFactors, ((p : ℝ) + 1) / (Real.sqrt (p : ℝ) + 1)) := by
              rw [Finset.mul_sum]
          _ = max K₁ 1 * Dc c x * sigHalf t := by rw [KMKappaGSum t ht]
          _ = max K₁ 1 * sigHalf t * Dc c x := by ring
  exact fun t x ht => key t ht x

/-! ## The log-weighted decay -/

/-- The Abel identity `KMTsumAbel` combined with `KMDcTailBound`: the log-weighted sum
`Tsum x t` converges to `ζ(2)·κ(t)/t` (limit from `KMTsumTendsto`) with the same exponential
rate, the tail being controlled by `Ssum_decay`. -/
theorem Tsum_decay : ∃ K c : ℝ, 0 < K ∧ 0 < c ∧
    ∀ (t x : ℕ), Squarefree t → 1 ≤ x →
      |Tsum x t - (Real.pi ^ 2 / 6) * (kappa t / (t : ℝ))| ≤ K * sigHalf t * Dc c x := by
  obtain ⟨K₁, c₁, hK₁, hc₁, hS⟩ := Ssum_decay
  obtain ⟨K₂, hK₂, hTb⟩ := KMDcTailBound
  set Cst : ℝ := K₁ * (K₂ * (1 + 1 / c₁) ^ 2) with hCst
  have hCstpos : 0 < Cst := by rw [hCst]; positivity
  refine ⟨Cst, c₁ / 2, hCstpos, by linarith, ?_⟩
  intro t x ht hx
  set L : ℝ := (Real.pi ^ 2 / 6) * (kappa t / (t : ℝ)) with hL
  have htend : Filter.Tendsto (fun M : ℕ => Tsum M t) Filter.atTop (nhds L) := KMTsumTendsto t ht
  have hdiff : ∀ M : ℕ, x ≤ M →
      Tsum x t - Tsum M t
        = -∑ m ∈ Finset.Icc x (M - 1), Ssum m t * Real.log (((m : ℝ) + 1) / (m : ℝ)) := by
    intro M hM
    rw [KMTsumAbel x t, KMTsumAbel M t]
    have hsplit : Finset.Icc 1 (M - 1)
        = Finset.Icc 1 (x - 1) ∪ Finset.Icc x (M - 1) := by
      ext m
      simp only [Finset.mem_Icc, Finset.mem_union]
      constructor
      · rintro ⟨h1, h2⟩
        by_cases h : m ≤ x - 1
        · exact Or.inl ⟨h1, h⟩
        · exact Or.inr ⟨by omega, h2⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> omega
    have hdisj : Disjoint (Finset.Icc 1 (x - 1)) (Finset.Icc x (M - 1)) := by
      rw [Finset.disjoint_left]
      intro m hm1 hm2
      simp only [Finset.mem_Icc] at hm1 hm2
      omega
    rw [hsplit, Finset.sum_union hdisj]
    ring
  have htail : ∀ M : ℕ, x ≤ M →
      |Tsum x t - Tsum M t| ≤ Cst * sigHalf t * Dc (c₁ / 2) x := by
    intro M hM
    rw [hdiff M hM, abs_neg]
    have hstep : ∀ m ∈ Finset.Icc x (M - 1),
        |Ssum m t * Real.log (((m : ℝ) + 1) / (m : ℝ))|
          ≤ K₁ * sigHalf t * (Dc c₁ m * Real.log (1 + 1 / (m : ℝ))) := by
      intro m hm
      obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
      have hmpos : 0 < m := by omega
      have hlogeq : Real.log (((m : ℝ) + 1) / (m : ℝ)) = Real.log (1 + 1 / (m : ℝ)) := by
        congr 1
        field_simp
      have hlognn : 0 ≤ Real.log (1 + 1 / (m : ℝ)) := by
        apply Real.log_nonneg
        have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
        have : (0 : ℝ) ≤ 1 / (m : ℝ) := by positivity
        linarith
      rw [abs_mul, hlogeq, abs_of_nonneg hlognn]
      have h1 := hS t m ht
      calc |Ssum m t| * Real.log (1 + 1 / (m : ℝ))
          ≤ (K₁ * sigHalf t * Dc c₁ m) * Real.log (1 + 1 / (m : ℝ)) :=
            mul_le_mul_of_nonneg_right h1 hlognn
        _ = K₁ * sigHalf t * (Dc c₁ m * Real.log (1 + 1 / (m : ℝ))) := by ring
    calc |∑ m ∈ Finset.Icc x (M - 1), Ssum m t * Real.log (((m : ℝ) + 1) / (m : ℝ))|
        ≤ ∑ m ∈ Finset.Icc x (M - 1),
            |Ssum m t * Real.log (((m : ℝ) + 1) / (m : ℝ))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ m ∈ Finset.Icc x (M - 1),
            K₁ * sigHalf t * (Dc c₁ m * Real.log (1 + 1 / (m : ℝ))) :=
          Finset.sum_le_sum hstep
      _ = K₁ * sigHalf t * ∑ m ∈ Finset.Icc x (M - 1),
            Dc c₁ m * Real.log (1 + 1 / (m : ℝ)) := by rw [Finset.mul_sum]
      _ ≤ K₁ * sigHalf t * (K₂ * (1 + 1 / c₁) ^ 2 * Dc (c₁ / 2) x) := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hK₁.le (sigHalf_nonneg t))
          by_cases hcase : x ≤ M - 1
          · exact hTb c₁ hc₁ x (M - 1) hcase
          · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
            exact mul_nonneg (mul_nonneg hK₂.le (by positivity)) (Dc_pos (c₁ / 2) x).le
      _ = Cst * sigHalf t * Dc (c₁ / 2) x := by rw [hCst]; ring
  have hlim : Filter.Tendsto (fun M : ℕ => |Tsum x t - Tsum M t|) Filter.atTop
      (nhds |Tsum x t - L|) := (tendsto_const_nhds.sub htend).abs
  have hev : ∀ᶠ M in Filter.atTop, |Tsum x t - Tsum M t| ≤ Cst * sigHalf t * Dc (c₁ / 2) x :=
    Filter.eventually_atTop.mpr ⟨x, htail⟩
  exact le_of_tendsto hlim hev

/-! ## Splitting the logarithm in the target's first sum -/

lemma Tsum_split (R t : ℕ) (Y : ℝ) (hR : 1 ≤ R) (hY : (R : ℝ) ≤ Y) :
    (∑ r ∈ Finset.Icc 1 R,
        (if Nat.Coprime r t then (ArithmeticFunction.moebius r : ℝ) / kap r else 0)
          * (Real.log (Y / (r : ℝ)) - 1))
      = (Real.log (Y / (R : ℝ)) - 1) * Ssum R t + Tsum R t := by
  have hR0 : (0 : ℝ) < (R : ℝ) := by exact_mod_cast (by omega : 0 < R)
  have hY0 : (0 : ℝ) < Y := lt_of_lt_of_le hR0 hY
  have hstep : ∀ r ∈ Finset.Icc 1 R,
      (if Nat.Coprime r t then (ArithmeticFunction.moebius r : ℝ) / kap r else 0)
          * (Real.log (Y / (r : ℝ)) - 1)
        = (if Nat.Coprime r t then (ArithmeticFunction.moebius r : ℝ) / kap r else 0)
            * (Real.log (Y / (R : ℝ)) - 1)
          + (if Nat.Coprime r t then (ArithmeticFunction.moebius r : ℝ) / kap r else 0)
            * Real.log ((R : ℝ) / (r : ℝ)) := by
    intro r hr
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
    have hkey : Y / (r : ℝ) = (Y / (R : ℝ)) * ((R : ℝ) / (r : ℝ)) := by
      field_simp
    have hlog : Real.log (Y / (r : ℝ))
        = Real.log (Y / (R : ℝ)) + Real.log ((R : ℝ) / (r : ℝ)) := by
      rw [hkey, Real.log_mul (by positivity) (by positivity)]
    rw [hlog]
    ring
  rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib]
  congr 1
  · rw [Ssum_eq_sum_if_kap, Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ => by ring
  · exact (Tsum_eq_sum_if_kap R t).symm

/-! ## The target -/

/-- **Mertens-type inputs for the `S₃` main term** (rational case; Graham 1978 (11),(12);
An, arXiv:2206.10104, Lemmas 11ing/12ing with no Siegel zero).  This is exactly the body of
`Work.ZeroDensity.Jutila.KappaMertensInput` (`Bz3Defs.lean`), written out.  With
`kap c = ∏_{p | c}(p+1)`, for squarefree `t` and `2 ≤ R ≤ Y`:
`Σ_{r ≤ R,(r,t)=1} (μ(r)/κ(r))(log(Y/r) − 1) = ζ(2)·κ(t)/t + log(Y/R)·Σ_{r ≤ R,(r,t)=1} μ(r)/κ(r)
 + O((Σ_{d|t} 1/√d)·e^{−c√log R})`, and the un-weighted sum is `O((Σ_{d|t} 1/√d)·e^{−c√log R})`;
both errors are absolute up to `C, c > 0`. -/
theorem KappaMertensHere :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      (∀ (t R : ℕ) (Y : ℝ), Squarefree t → 2 ≤ R → (R : ℝ) ≤ Y →
          |(∑ r ∈ Finset.Icc 1 R,
              (if Nat.Coprime r t then (ArithmeticFunction.moebius r : ℝ) / Work.ZeroDensity.Jutila.kap r else 0) *
                (Real.log (Y / (r : ℝ)) - 1))
            - (Real.pi ^ 2 / 6) * (Work.ZeroDensity.Jutila.kap t / (t : ℝ))
            - Real.log (Y / (R : ℝ)) *
                (∑ r ∈ Finset.Icc 1 R,
                  if Nat.Coprime r t then (ArithmeticFunction.moebius r : ℝ) / Work.ZeroDensity.Jutila.kap r else 0)|
          ≤ C * (∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ))
              * Real.exp (-(c * Real.sqrt (Real.log (R : ℝ)))))
      ∧ (∀ (t R : ℕ), Squarefree t → 2 ≤ R →
          |(∑ r ∈ Finset.Icc 1 R,
              if Nat.Coprime r t then (ArithmeticFunction.moebius r : ℝ) / Work.ZeroDensity.Jutila.kap r else 0)|
          ≤ C * (∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ))
              * Real.exp (-(c * Real.sqrt (Real.log (R : ℝ))))) := by
  obtain ⟨K₁, c₁, hK₁, hc₁, hS⟩ := Ssum_decay
  obtain ⟨K₂, c₂, hK₂, hc₂, hT⟩ := Tsum_decay
  refine ⟨K₁ + K₂, min c₁ c₂, by positivity, lt_min hc₁ hc₂, ?_, ?_⟩
  · intro t R Y ht hR hY
    have hR1 : 1 ≤ R := by omega
    have hB := Tsum_split R t Y hR1 hY
    have hA : (∑ r ∈ Finset.Icc 1 R,
        (if Nat.Coprime r t then (ArithmeticFunction.moebius r : ℝ) / kap r else 0))
        = Ssum R t := (Ssum_eq_sum_if_kap R t).symm
    rw [hB, hA, ← kappa_eq_kap_of_squarefree ht]
    have hkey : (Real.log (Y / (R : ℝ)) - 1) * Ssum R t + Tsum R t
          - Real.pi ^ 2 / 6 * (kappa t / (t : ℝ))
          - Real.log (Y / (R : ℝ)) * Ssum R t
        = (Tsum R t - Real.pi ^ 2 / 6 * (kappa t / (t : ℝ))) - Ssum R t := by ring
    rw [hkey]
    have hs : 0 ≤ sigHalf t := sigHalf_nonneg t
    have hmn : min c₁ c₂ ≤ c₁ := min_le_left _ _
    have hmx : min c₁ c₂ ≤ c₂ := min_le_right _ _
    calc |(Tsum R t - Real.pi ^ 2 / 6 * (kappa t / (t : ℝ))) - Ssum R t|
        ≤ |Tsum R t - Real.pi ^ 2 / 6 * (kappa t / (t : ℝ))| + |Ssum R t| := abs_sub _ _
      _ ≤ K₂ * sigHalf t * Dc c₂ R + K₁ * sigHalf t * Dc c₁ R :=
          add_le_add (hT t R ht hR1) (hS t R ht)
      _ ≤ (K₁ + K₂) * sigHalf t * Dc (min c₁ c₂) R := by
          have h2 : K₂ * sigHalf t * Dc c₂ R ≤ K₂ * sigHalf t * Dc (min c₁ c₂) R :=
            mul_le_mul_of_nonneg_left (Dc_le_of_le_rate hmx R) (mul_nonneg hK₂.le hs)
          have h3 : K₁ * sigHalf t * Dc c₁ R ≤ K₁ * sigHalf t * Dc (min c₁ c₂) R :=
            mul_le_mul_of_nonneg_left (Dc_le_of_le_rate hmn R) (mul_nonneg hK₁.le hs)
          have h4 : K₁ * sigHalf t * Dc (min c₁ c₂) R
              ≤ (K₁ + K₂) * sigHalf t * Dc (min c₁ c₂) R := by
            apply mul_le_mul_of_nonneg_right _ (Dc_pos (min c₁ c₂) R).le
            apply mul_le_mul_of_nonneg_right _ hs
            linarith
          linarith [h2, h3, h4]
  · intro t R ht hR
    have hR1 : 1 ≤ R := by omega
    have hA : (∑ r ∈ Finset.Icc 1 R,
        (if Nat.Coprime r t then (ArithmeticFunction.moebius r : ℝ) / kap r else 0))
        = Ssum R t := (Ssum_eq_sum_if_kap R t).symm
    rw [hA]
    have hs : 0 ≤ sigHalf t := sigHalf_nonneg t
    have hmn : min c₁ c₂ ≤ c₁ := min_le_left _ _
    calc |Ssum R t| ≤ K₁ * sigHalf t * Dc c₁ R := hS t R ht
      _ ≤ K₁ * sigHalf t * Dc (min c₁ c₂) R :=
          mul_le_mul_of_nonneg_left (Dc_le_of_le_rate hmn R) (mul_nonneg hK₁.le hs)
      _ ≤ (K₁ + K₂) * sigHalf t * Dc (min c₁ c₂) R := by
          apply mul_le_mul_of_nonneg_right _ (Dc_pos (min c₁ c₂) R).le
          apply mul_le_mul_of_nonneg_right _ hs
          linarith

end

end Work.ZeroDensity.Jutila.LzDiffAux
