/-
# ZeroFreeTables/XY/ImprimitiveSigmaReduce

`Work.ZeroFreeTables.XY.ImprimitiveSigmaReduce`: the reduction of HB's `Σ(s,χ)` (with the
free scale `L`) for an *imprimitive* Dirichlet character `χ` of modulus `q` to the same
quantity for its primitive character `χ.primitiveCharacter` of modulus `χ.conductor`, up to
an error `(a+λ₁)·e`.

The point is the "change of level" identity: for `N ∣ q` and `ψ` mod `N`,
`Σ^q(changeLevel ψ) − Σ^N(ψ)` is supported on the `n` that are *not* coprime to `q`; there
each summand is bounded by `Λ(n) n^{-Re s} u(log n / L)`.  The support consists of the prime
powers `p^k` with `p ∣ q`, so the whole difference is bounded by
`(K/L)·(α S₁ + (α²/L) S₂ + (α³/L²) S₃)` where `S_j = ∑_{p|q} (log p)^j / p` and `α = a+λ₁`.
Since `∑_{p|q} log p ≤ log q ≤ L`, the sums `S_j` are `O((log L)^{j+1})` uniformly in `q`,
and the error can be made smaller than `α·e` by taking `L` large.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P3.DefsL
import Submission.Work.ZeroFreeTables.P3.SummableVonMangoldtLogPow
import Submission.Work.ZeroFreeTables.P9.SigmaP3LChangeLevelAux
import Submission.Work.ZeroFreeTables.P9.summable_sigmaTerm
import Submission.Work.ZeroFreeTables.P9.norm_sigmaTerm_changeLevel_sub_le
import Submission.Work.ZeroFreeTables.P9.primeFactors_logPow_div_le
import Submission.Work.ZeroFreeTables.P9.vonMangoldt_compl_coprime_eq_sum_F
import Submission.Work.ZeroFreeTables.P9.summable_vonMangoldt_primePow

open scoped BigOperators
open ArithmeticFunction
noncomputable section

set_option maxHeartbeats 1600000

namespace Work.ZeroFreeTables.XY

/-! ## Elementary bound `(k+1)^2 ≤ 5·(3/2)^k` -/

lemma pow_two_le (k : ℕ) : ((k:ℝ) + 1)^2 ≤ 5 * (3/2)^k := by
  rcases Nat.lt_or_ge k 5 with hk | hk
  · interval_cases k <;> norm_num
  · induction k, hk using Nat.le_induction with
    | base => norm_num
    | succ m hm ih =>
      have hmR : (5:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
      have h1 : ((m:ℝ)+2)^2 ≤ (3/2) * ((m:ℝ)+1)^2 := by nlinarith [hmR]
      have h2 : (3/2) * ((m:ℝ)+1)^2 ≤ (3/2) * (5*(3/2)^m) :=
        mul_le_mul_of_nonneg_left ih (by norm_num)
      have hcast : (((m+1:ℕ):ℝ)+1) = (m:ℝ)+2 := by push_cast; ring
      rw [hcast]
      calc ((m:ℝ)+2)^2 ≤ (3/2) * ((m:ℝ)+1)^2 := h1
        _ ≤ (3/2) * (5*(3/2)^m) := h2
        _ = 5 * (3/2)^((m+1:ℕ)) := by rw [pow_succ]; ring

/-! ## The non-coprime von Mangoldt tail

We bound `∑_n [¬coprime n q] Λ(n) n^{-σ} (log n)^j` by `24 ∑_{p|q}(log p)^{j+1}/p`.
The support of the summand is the set of prime powers `p^k` with `p ∣ q`; for each such
prime the `k`-sum `∑ k^j p^{-σk}` is at most `24/p`. -/

/-- Value of the restricted summand at the prime power `p^{m+1}`. -/
private lemma F_pow (p : ℕ) (hp : p.Prime) {σ : ℝ} (j m : ℕ) :
    (if IsPrimePow (p^(m+1)) ∧ (p^(m+1)).minFac = p
      then (ArithmeticFunction.vonMangoldt (p^(m+1)) : ℝ) * ((p^(m+1) : ℕ) : ℝ) ^ (-σ)
        * (Real.log ((p^(m+1) : ℕ) : ℝ)) ^ j else 0)
      = (Real.log (p:ℝ))^(j+1) * (((m:ℝ)+1)^j * (p:ℝ)^(-σ*((m:ℝ)+1))) := by
  have hppos : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp.pos
  have hm1 : m + 1 ≠ 0 := by omega
  have h1 : IsPrimePow (p^(m+1)) := (hp.isPrimePow).pow (k := m+1) hm1
  have h2 : (p^(m+1)).minFac = p := by
    rw [Nat.pow_minFac hm1, Nat.Prime.minFac_eq hp]
  have h3 : (ArithmeticFunction.vonMangoldt (p^(m+1)) : ℝ) = Real.log (p:ℝ) := by
    rw [ArithmeticFunction.vonMangoldt_apply_pow hm1, ArithmeticFunction.vonMangoldt_apply_prime hp]
  have h4 : ((p^(m+1) : ℕ) : ℝ) = (p:ℝ)^(m+1) := by push_cast; ring
  have hlog : Real.log ((p:ℝ)^(m+1)) = ((m:ℝ)+1) * Real.log (p:ℝ) := by
    rw [Real.log_pow]; push_cast; ring
  have hrpow : ((p:ℝ)^(m+1)) ^ (-σ) = (p:ℝ)^(-σ*((m:ℝ)+1)) := by
    rw [← Real.rpow_natCast (p:ℝ) (m+1), ← Real.rpow_mul (le_of_lt hppos)]
    congr 1
    push_cast; ring
  rw [if_pos ⟨h1, h2⟩, h3, h4, hlog, hrpow, mul_pow, pow_succ]
  ring

/-- The `k`-sum at a prime: `∑_m ((m+1)^j · p^{-σ(m+1)}) ≤ 24/p` for `j ≤ 2`, `σ > 1`. -/
private lemma geom_bound (p : ℕ) (hp : p.Prime) {σ : ℝ} (hσ : 1 < σ) (j : ℕ) (hj : j ≤ 2) :
    (∑' m : ℕ, (((m:ℝ)+1)^j * (p:ℝ)^(-σ*((m:ℝ)+1)))) ≤ 24 / (p:ℝ) := by
  have hp2 : 2 ≤ p := hp.two_le
  have hppos : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp.pos
  have hp1 : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp.one_le
  set f : ℕ → ℝ := fun m => ((m:ℝ)+1)^j * (p:ℝ)^(-σ*((m:ℝ)+1)) with hf
  set gg : ℕ → ℝ := fun m => (5/(p:ℝ)) * ((3:ℝ)/4)^m with hgg
  have hpt : ∀ m, f m ≤ gg m := by
    intro m
    have hm1 : (1:ℝ) ≤ (m:ℝ)+1 := by
      have : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m; linarith
    have hmnn : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
    have hpow2 : ((m:ℝ)+1)^j ≤ 5*(3/2)^m :=
      le_trans (pow_le_pow_right₀ hm1 hj) (pow_two_le m)
    have h2m : (2:ℝ)^(-(m:ℝ)) = ((2:ℝ)⁻¹)^m := by
      rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast]
      exact (inv_pow (2:ℝ) m).symm
    have hrpow : (p:ℝ)^(-σ*((m:ℝ)+1)) ≤ (p:ℝ)⁻¹ * (2:ℝ)^(-(m:ℝ)) := by
      have e1 : -σ*((m:ℝ)+1) = (-(m:ℝ)) + (-1) + (-(σ-1)*((m:ℝ)+1)) := by ring
      rw [e1]
      rw [show (-(m:ℝ)) + (-1) + (-(σ-1)*((m:ℝ)+1))
          = ((-(m:ℝ)) + (-1)) + (-(σ-1)*((m:ℝ)+1)) by ring]
      rw [Real.rpow_add hppos, Real.rpow_add hppos]
      have hle1 : (p:ℝ)^(-(σ-1)*((m:ℝ)+1)) ≤ 1 := by
        apply Real.rpow_le_one_of_one_le_of_nonpos hp1
        nlinarith [hσ, hmnn]
      have hle2 : (p:ℝ)^(-(m:ℝ)) ≤ (2:ℝ)^(-(m:ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast hp2)
          (by linarith : -(m:ℝ) ≤ 0)
      have hB : 0 ≤ (p:ℝ)^(-1:ℝ) := Real.rpow_nonneg (le_of_lt hppos) _
      have hp_inv : (p:ℝ)^(-1:ℝ) = (p:ℝ)⁻¹ := by
        rw [Real.rpow_neg (le_of_lt hppos) (1:ℝ), Real.rpow_one]
      calc (p:ℝ)^(-(m:ℝ)) * (p:ℝ)^(-1:ℝ) * (p:ℝ)^(-(σ-1)*((m:ℝ)+1))
          ≤ (p:ℝ)^(-(m:ℝ)) * (p:ℝ)^(-1:ℝ) * 1 := by
            apply mul_le_mul_of_nonneg_left hle1
            positivity
        _ = (p:ℝ)^(-(m:ℝ)) * (p:ℝ)^(-1:ℝ) := by ring
        _ ≤ (2:ℝ)^(-(m:ℝ)) * (p:ℝ)^(-1:ℝ) := mul_le_mul_of_nonneg_right hle2 hB
        _ = (p:ℝ)⁻¹ * (2:ℝ)^(-(m:ℝ)) := by rw [hp_inv]; ring
    have hgeom : (3/2:ℝ)^m * (2:ℝ)^(-(m:ℝ)) = ((3:ℝ)/4)^m := by
      rw [h2m, ← mul_pow]; norm_num
    have hprod : ((m:ℝ)+1)^j * (p:ℝ)^(-σ*((m:ℝ)+1))
        ≤ 5*(3/2)^m * ((p:ℝ)⁻¹ * (2:ℝ)^(-(m:ℝ))) :=
      mul_le_mul hpow2 hrpow (Real.rpow_nonneg (le_of_lt hppos) _) (by positivity)
    rw [hf, hgg]
    calc ((m:ℝ)+1)^j * (p:ℝ)^(-σ*((m:ℝ)+1))
        ≤ 5*(3/2)^m * ((p:ℝ)⁻¹ * (2:ℝ)^(-(m:ℝ))) := hprod
      _ = (5/(p:ℝ)) * ((3/2:ℝ)^m * (2:ℝ)^(-(m:ℝ))) := by ring
      _ = (5/(p:ℝ)) * ((3:ℝ)/4)^m := by rw [hgeom]
  have hggsumm : Summable gg := by
    rw [hgg]
    exact (summable_geometric_of_abs_lt_one (by norm_num : |((3:ℝ)/4)| < 1)).mul_left (5/(p:ℝ))
  have hfsumm : Summable f := Summable.of_nonneg_of_le (fun m => by positivity) hpt hggsumm
  have hgeom_sum : (∑' m : ℕ, ((3:ℝ)/4)^m) = 4 := by
    rw [tsum_geometric_of_abs_lt_one (by norm_num : |((3:ℝ)/4)| < 1)]
    norm_num
  calc ∑' m, f m ≤ ∑' m, gg m := Summable.tsum_le_tsum hpt hfsumm hggsumm
    _ = (5/(p:ℝ)) * (∑' m : ℕ, ((3:ℝ)/4)^m) := by rw [hgg, tsum_mul_left]
    _ = (5/(p:ℝ)) * 4 := by rw [hgeom_sum]
    _ = 20/(p:ℝ) := by ring
    _ ≤ 24/(p:ℝ) := div_le_div_of_nonneg_right (by norm_num) (le_of_lt hppos)

/-- The restricted von Mangoldt series at a fixed prime: `≤ 24 (log p)^{j+1}/p`. -/
private lemma primePow_tail_le (p : ℕ) (hp : p.Prime) {σ : ℝ} (hσ : 1 < σ) (j : ℕ) (hj : j ≤ 2) :
    (∑' n : ℕ, (if IsPrimePow n ∧ n.minFac = p then (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) * (Real.log (n : ℝ)) ^ j else (0:ℝ)))
      ≤ 24 * (Real.log (p : ℝ)) ^ (j + 1) / (p : ℝ) := by
  have hp2 : 2 ≤ p := hp.two_le
  have hlogp : 0 < Real.log (p:ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hinj : Function.Injective (fun m : ℕ => p ^ (m+1)) := by
    intro a b hab
    have h2 := Nat.pow_right_injective hp2 hab
    omega
  have hsupp : Function.support (fun n : ℕ => (if IsPrimePow n ∧ n.minFac = p then (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) * (Real.log (n : ℝ)) ^ j else (0:ℝ)))
      ⊆ Set.range (fun m : ℕ => p ^ (m+1)) := by
    intro n hn
    rw [Function.mem_support, ne_eq] at hn
    by_cases hc : IsPrimePow n ∧ n.minFac = p
    · rw [if_pos hc] at hn
      obtain ⟨hpp, hmf⟩ := hc
      have hfac : p ^ (n.factorization p) = n := by
        have h := IsPrimePow.minFac_pow_factorization_eq hpp
        rwa [hmf] at h
      have hpos : 0 < n.factorization p := by
        by_contra hz
        have hz0 : n.factorization p = 0 := by omega
        rw [hz0, pow_zero] at hfac
        have := IsPrimePow.one_lt hpp
        omega
      refine ⟨n.factorization p - 1, ?_⟩
      show p ^ (n.factorization p - 1 + 1) = n
      have : n.factorization p - 1 + 1 = n.factorization p := by omega
      rw [this, hfac]
    · rw [if_neg hc] at hn; exact absurd rfl hn
  have hkey : (∑' n : ℕ, (if IsPrimePow n ∧ n.minFac = p then (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) * (Real.log (n : ℝ)) ^ j else (0:ℝ)))
      = ∑' m : ℕ, (Real.log (p:ℝ))^(j+1) * (((m:ℝ)+1)^j * (p:ℝ)^(-σ*((m:ℝ)+1))) := by
    rw [← Function.Injective.tsum_eq hinj hsupp]
    exact tsum_congr (fun m => F_pow p hp j m)
  rw [hkey]
  rw [show (∑' m : ℕ, (Real.log (p:ℝ))^(j+1) * (((m:ℝ)+1)^j * (p:ℝ)^(-σ*((m:ℝ)+1))))
      = (Real.log (p:ℝ))^(j+1) * (∑' m : ℕ, (((m:ℝ)+1)^j * (p:ℝ)^(-σ*((m:ℝ)+1)))) from tsum_mul_left]
  have hb := geom_bound p hp hσ j hj
  have hlog_nonneg : 0 ≤ (Real.log (p:ℝ))^(j+1) := pow_nonneg (le_of_lt hlogp) _
  calc (Real.log (p:ℝ))^(j+1) * (∑' m : ℕ, ((m:ℝ)+1)^j * (p:ℝ)^(-σ*((m:ℝ)+1)))
      ≤ (Real.log (p:ℝ))^(j+1) * (24/(p:ℝ)) := mul_le_mul_of_nonneg_left hb hlog_nonneg
    _ = 24 * (Real.log (p:ℝ))^(j+1) / (p:ℝ) := by ring

/-- The non-coprime tail with `(log n)^j` weight: `≤ 24 ∑_{p|q}(log p)^{j+1}/p`. -/
private lemma nonCoprime_tail_le {q : ℕ} (hq : q ≠ 0) {σ : ℝ} (hσ : 1 < σ) (j : ℕ) (hj : j ≤ 2) :
    (∑' n : ℕ, (if Nat.Coprime n q then (0:ℝ) else 1) * (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) * (Real.log (n : ℝ)) ^ j)
      ≤ 24 * ∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ (j + 1) / (p : ℝ) := by
  have hcongr : ∀ n : ℕ, (if Nat.Coprime n q then (0:ℝ) else 1) * (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) * (Real.log (n : ℝ)) ^ j
      = ∑ p ∈ q.primeFactors, (if IsPrimePow n ∧ n.minFac = p then (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) * (Real.log (n : ℝ)) ^ j else (0:ℝ)) :=
    fun n => Work.ZeroFreeTables.P9.vonMangoldt_compl_coprime_eq_sum_F hq j n
  rw [tsum_congr hcongr]
  rw [Summable.tsum_finsetSum (f := fun p n => (if IsPrimePow n ∧ n.minFac = p then (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) * (Real.log (n : ℝ)) ^ j else (0:ℝ)))
      (fun p hp => Work.ZeroFreeTables.P9.summable_vonMangoldt_primePow p (Nat.prime_of_mem_primeFactors hp) hσ j)]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have h := primePow_tail_le p (Nat.prime_of_mem_primeFactors hp) hσ j hj
  simpa [mul_div_assoc] using h

/-! ## Summability of the `hbWL`-weighted von Mangoldt series -/

private lemma summable_vonMangoldt_natCast_neg {σ : ℝ} (hσ : 1 < σ) (A : ℕ) :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (Real.log (n:ℝ))^A * (n:ℝ)^(-σ)) := by
  refine (Work.ZeroFreeTables.P3.SummableVonMangoldtLogPow (σ := σ) hσ A).congr (fun n => ?_)
  rw [div_eq_mul_inv, ← Real.rpow_neg (Nat.cast_nonneg n)]

private lemma summable_hbWL_tail {L a lam₁ σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n:ℝ)^(-σ)
      * Work.ZeroFreeTables.hbWL L a lam₁ n) := by
  have h0 := summable_vonMangoldt_natCast_neg (σ := σ) hσ 0
  have h1 := summable_vonMangoldt_natCast_neg (σ := σ) hσ 1
  have h2 := summable_vonMangoldt_natCast_neg (σ := σ) hσ 2
  refine (((h0.mul_left (a + lam₁)).add (h1.mul_left ((a + lam₁)^2 / L))).add
      (h2.mul_left ((1/3) * (a + lam₁)^3 / L^2))).congr (fun n => ?_)
  unfold Work.ZeroFreeTables.hbWL
  ring

private lemma hbWL_nonneg' {L a lam₁ : ℝ} (hL : 0 < L) (hα : 0 ≤ a + lam₁) (n : ℕ) :
    0 ≤ Work.ZeroFreeTables.hbWL L a lam₁ n := by
  have hy : 0 ≤ Real.log (n:ℝ) / L := div_nonneg (Real.log_natCast_nonneg n) hL.le
  have h2 : 0 ≤ (a + lam₁)^2 * (Real.log (n:ℝ)/L) := mul_nonneg (pow_nonneg hα 2) hy
  have h3 : 0 ≤ (1/3) * (a+lam₁)^3 * (Real.log (n:ℝ)/L)^2 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 3)) (pow_nonneg hy 2)
  unfold Work.ZeroFreeTables.hbWL
  linarith

/-! ## The change-of-level difference bound -/

private lemma SigmaChangeLevelAbsDiff {N q : ℕ} [NeZero N] [NeZero q] (hNq : N ∣ q)
    (ψ : DirichletCharacter ℂ N) {L : ℝ} (hL : 0 < L) {s : ℂ} (hs : 1 < s.re)
    {a lam₁ : ℝ} (ha : 0 < a) (hlam₁ : 0 ≤ lam₁) :
    |Work.ZeroFreeTables.SigmaP3L q L (DirichletCharacter.changeLevel hNq ψ) s a lam₁
        - Work.ZeroFreeTables.SigmaP3L N L ψ s a lam₁|
      ≤ L⁻¹ * ∑' n : ℕ, (if Nat.Coprime n q then (0:ℝ) else 1)
          * (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-s.re)
          * Work.ZeroFreeTables.hbWL L a lam₁ n := by
  have hα : 0 ≤ a + lam₁ := by linarith
  set χ' : DirichletCharacter ℂ q := DirichletCharacter.changeLevel hNq ψ with hχ'def
  have hFs : Summable (Work.ZeroFreeTables.P9.sigmaTerm q L χ' s a lam₁) :=
    Work.ZeroFreeTables.P9.summable_sigmaTerm L χ' a lam₁ hs ha hlam₁ hL
  have hGs : Summable (Work.ZeroFreeTables.P9.sigmaTerm N L ψ s a lam₁) :=
    Work.ZeroFreeTables.P9.summable_sigmaTerm L ψ a lam₁ hs ha hlam₁ hL
  have hdiff : (∑' n, Work.ZeroFreeTables.P9.sigmaTerm q L χ' s a lam₁ n)
      - (∑' n, Work.ZeroFreeTables.P9.sigmaTerm N L ψ s a lam₁ n)
      = ∑' n, (Work.ZeroFreeTables.P9.sigmaTerm q L χ' s a lam₁ n
          - Work.ZeroFreeTables.P9.sigmaTerm N L ψ s a lam₁ n) :=
    (Summable.tsum_sub hFs hGs).symm
  have hpt : ∀ n : ℕ,
      ‖Work.ZeroFreeTables.P9.sigmaTerm q L χ' s a lam₁ n
          - Work.ZeroFreeTables.P9.sigmaTerm N L ψ s a lam₁ n‖
      ≤ (if Nat.Coprime n q then (0:ℝ) else 1) * (ArithmeticFunction.vonMangoldt n : ℝ)
          * (n : ℝ) ^ (-s.re) * Work.ZeroFreeTables.hbWL L a lam₁ n := by
    intro n
    have h := Work.ZeroFreeTables.P9.norm_sigmaTerm_changeLevel_sub_le hNq ψ L s a lam₁ ha hlam₁ hL n
    rw [← hχ'def] at h
    have hind : (if Nat.Coprime n N ∧ ¬ Nat.Coprime n q then (1:ℝ) else 0)
        ≤ (if Nat.Coprime n q then (0:ℝ) else 1) := by
      by_cases hc : Nat.Coprime n q
      · rw [if_neg (fun h : Nat.Coprime n N ∧ ¬ Nat.Coprime n q => h.2 hc), if_pos hc]
      · rw [if_neg hc]
        by_cases hN : Nat.Coprime n N
        · rw [if_pos (show Nat.Coprime n N ∧ ¬ Nat.Coprime n q from ⟨hN, hc⟩)]
        · rw [if_neg (show ¬(Nat.Coprime n N ∧ ¬ Nat.Coprime n q) from fun h => hN h.1)]
          norm_num
    have hw : 0 ≤ Work.ZeroFreeTables.hbWL L a lam₁ n := hbWL_nonneg' hL hα n
    calc ‖Work.ZeroFreeTables.P9.sigmaTerm q L χ' s a lam₁ n
            - Work.ZeroFreeTables.P9.sigmaTerm N L ψ s a lam₁ n‖
        ≤ (if Nat.Coprime n N ∧ ¬ Nat.Coprime n q then (1:ℝ) else 0)
            * (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-s.re)
            * Work.ZeroFreeTables.hbWL L a lam₁ n := h
      _ ≤ (if Nat.Coprime n q then (0:ℝ) else 1) * (ArithmeticFunction.vonMangoldt n : ℝ)
            * (n : ℝ) ^ (-s.re) * Work.ZeroFreeTables.hbWL L a lam₁ n := by
          apply mul_le_mul_of_nonneg_right _ hw
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg n) _)
          exact mul_le_mul_of_nonneg_right hind ArithmeticFunction.vonMangoldt_nonneg
  have hHsumm : Summable (fun n : ℕ => (if Nat.Coprime n q then (0:ℝ) else 1)
      * (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-s.re)
      * Work.ZeroFreeTables.hbWL L a lam₁ n) := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
      (summable_hbWL_tail (L := L) (a := a) (lam₁ := lam₁) (σ := s.re) hs)
    · have h1 : (0:ℝ) ≤ (if Nat.Coprime n q then (0:ℝ) else 1) := by split <;> norm_num
      exact mul_nonneg (mul_nonneg (mul_nonneg h1 ArithmeticFunction.vonMangoldt_nonneg)
        (Real.rpow_nonneg (Nat.cast_nonneg n) _)) (hbWL_nonneg' hL hα n)
    · have h1 : (if Nat.Coprime n q then (0:ℝ) else 1) ≤ 1 := by split <;> norm_num
      have h2 : (if Nat.Coprime n q then (0:ℝ) else 1) * (ArithmeticFunction.vonMangoldt n : ℝ)
          ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := by
        simpa using mul_le_mul_of_nonneg_right h1 ArithmeticFunction.vonMangoldt_nonneg
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg (Nat.cast_nonneg n) _))
        (hbWL_nonneg' hL hα n)
  rw [Work.ZeroFreeTables.P9.SigmaP3L_eq_tsum_sigmaTerm,
    Work.ZeroFreeTables.P9.SigmaP3L_eq_tsum_sigmaTerm]
  rw [← mul_sub, abs_mul, abs_of_nonneg (inv_nonneg.mpr hL.le), ← Real.norm_eq_abs]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hL.le)
  rw [hdiff]
  calc ‖∑' n, (Work.ZeroFreeTables.P9.sigmaTerm q L χ' s a lam₁ n
          - Work.ZeroFreeTables.P9.sigmaTerm N L ψ s a lam₁ n)‖
      ≤ ∑' n, ‖Work.ZeroFreeTables.P9.sigmaTerm q L χ' s a lam₁ n
          - Work.ZeroFreeTables.P9.sigmaTerm N L ψ s a lam₁ n‖ :=
        norm_tsum_le_tsum_norm ((hFs.sub hGs).norm)
    _ ≤ ∑' n, ((if Nat.Coprime n q then (0:ℝ) else 1) * (ArithmeticFunction.vonMangoldt n : ℝ)
          * (n : ℝ) ^ (-s.re) * Work.ZeroFreeTables.hbWL L a lam₁ n) :=
        Summable.tsum_le_tsum hpt ((hFs.sub hGs).norm) hHsumm

/-! ## The `hbWL`-weighted non-coprime tail: the split plus the prime bound -/

private lemma NonCoprimeHbWLTailLe (q : ℕ) [NeZero q] {σ : ℝ} (hσ : 1 < σ) {L : ℝ} (hL : 0 < L)
    {a lam₁ : ℝ} (ha : 0 < a) (hlam₁ : 0 ≤ lam₁) :
    (∑' n : ℕ, (if Nat.Coprime n q then (0:ℝ) else 1) * (ArithmeticFunction.vonMangoldt n : ℝ)
        * (n : ℝ) ^ (-σ) * Work.ZeroFreeTables.hbWL L a lam₁ n)
      ≤ 24 * (a + lam₁) * (∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (p : ℝ))
        + 24 * ((a + lam₁) ^ 2 / L) * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 2 / (p : ℝ))
        + 8 * ((a + lam₁) ^ 3 / L ^ 2) * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 3 / (p : ℝ)) := by
  have hq : q ≠ 0 := NeZero.ne q
  have hαnn : 0 ≤ a + lam₁ := by linarith
  set α : ℝ := a + lam₁ with hα
  set f : ℕ → ℕ → ℝ := fun j n =>
    (if Nat.Coprime n q then (0:ℝ) else 1) * (ArithmeticFunction.vonMangoldt n : ℝ)
      * (n : ℝ) ^ (-σ) * (Real.log (n : ℝ)) ^ j with hf
  have hsumm : ∀ j : ℕ, Summable (f j) := by
    intro j
    have hmaj : Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ)
        * (Real.log (n:ℝ))^j * (n:ℝ)^(-σ)) :=
      summable_vonMangoldt_natCast_neg hσ j
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hmaj
    · have h1 : (0:ℝ) ≤ (if Nat.Coprime n q then (0:ℝ) else 1) := by split <;> norm_num
      rw [hf]
      exact mul_nonneg (mul_nonneg (mul_nonneg h1 ArithmeticFunction.vonMangoldt_nonneg)
        (Real.rpow_nonneg (Nat.cast_nonneg n) _)) (pow_nonneg (Real.log_natCast_nonneg n) j)
    · have h1 : (if Nat.Coprime n q then (0:ℝ) else 1) ≤ 1 := by split <;> norm_num
      have h2 : (if Nat.Coprime n q then (0:ℝ) else 1) * (ArithmeticFunction.vonMangoldt n : ℝ)
          ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := by
        simpa using mul_le_mul_of_nonneg_right h1 ArithmeticFunction.vonMangoldt_nonneg
      rw [hf]
      calc (if Nat.Coprime n q then (0:ℝ) else 1) * (ArithmeticFunction.vonMangoldt n : ℝ)
              * (n : ℝ) ^ (-σ) * (Real.log (n : ℝ)) ^ j
          ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) * (Real.log (n : ℝ)) ^ j := by
            apply mul_le_mul_of_nonneg_right _ (pow_nonneg (Real.log_natCast_nonneg n) j)
            exact mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg (Nat.cast_nonneg n) _)
        _ = (ArithmeticFunction.vonMangoldt n : ℝ) * (Real.log (n : ℝ)) ^ j * (n : ℝ) ^ (-σ) := by
            ring
  have hsplit : (∑' n : ℕ, (if Nat.Coprime n q then (0:ℝ) else 1) * (ArithmeticFunction.vonMangoldt n : ℝ)
        * (n : ℝ) ^ (-σ) * Work.ZeroFreeTables.hbWL L a lam₁ n)
      = α * (∑' n, f 0 n) + ((α^2/L) * (∑' n, f 1 n) + ((1/3)*(α^3/L^2)) * (∑' n, f 2 n)) := by
    have hpt : ∀ n : ℕ, (if Nat.Coprime n q then (0:ℝ) else 1) * (ArithmeticFunction.vonMangoldt n : ℝ)
        * (n : ℝ) ^ (-σ) * Work.ZeroFreeTables.hbWL L a lam₁ n
        = α * f 0 n + ((α^2/L) * f 1 n + ((1/3)*(α^3/L^2)) * f 2 n) := by
      intro n
      rw [hf, hα]
      unfold Work.ZeroFreeTables.hbWL
      ring
    rw [tsum_congr hpt]
    rw [Summable.tsum_add ((hsumm 0).mul_left α) (((hsumm 1).mul_left (α^2/L)).add ((hsumm 2).mul_left ((1/3)*(α^3/L^2)))),
        Summable.tsum_add ((hsumm 1).mul_left (α^2/L)) ((hsumm 2).mul_left ((1/3)*(α^3/L^2))),
        tsum_mul_left, tsum_mul_left, tsum_mul_left]
  rw [hsplit]
  have hS0nn : 0 ≤ (∑' n, f 0 n) := tsum_nonneg (fun n => by
    have h1 : (0:ℝ) ≤ (if Nat.Coprime n q then (0:ℝ) else 1) := by split <;> norm_num
    simp only [hf]; exact mul_nonneg (mul_nonneg (mul_nonneg h1 ArithmeticFunction.vonMangoldt_nonneg)
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)) (pow_nonneg (Real.log_natCast_nonneg n) 0))
  have hS1nn : 0 ≤ (∑' n, f 1 n) := tsum_nonneg (fun n => by
    have h1 : (0:ℝ) ≤ (if Nat.Coprime n q then (0:ℝ) else 1) := by split <;> norm_num
    simp only [hf]; exact mul_nonneg (mul_nonneg (mul_nonneg h1 ArithmeticFunction.vonMangoldt_nonneg)
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)) (pow_nonneg (Real.log_natCast_nonneg n) 1))
  have hS2nn : 0 ≤ (∑' n, f 2 n) := tsum_nonneg (fun n => by
    have h1 : (0:ℝ) ≤ (if Nat.Coprime n q then (0:ℝ) else 1) := by split <;> norm_num
    simp only [hf]; exact mul_nonneg (mul_nonneg (mul_nonneg h1 ArithmeticFunction.vonMangoldt_nonneg)
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)) (pow_nonneg (Real.log_natCast_nonneg n) 2))
  have hb0 : (∑' n, f 0 n) ≤ 24 * ∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (p : ℝ) := by
    have h := nonCoprime_tail_le (q := q) hq hσ 0 (by norm_num)
    simpa only [zero_add, pow_one] using h
  have hb1 : (∑' n, f 1 n) ≤ 24 * ∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 2 / (p : ℝ) :=
    nonCoprime_tail_le (q := q) hq hσ 1 (by norm_num)
  have hb2 : (∑' n, f 2 n) ≤ 24 * ∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 3 / (p : ℝ) :=
    nonCoprime_tail_le (q := q) hq hσ 2 (by norm_num)
  have hc0 : 0 ≤ α := by rw [hα]; linarith
  have hc1 : 0 ≤ α^2/L := div_nonneg (sq_nonneg α) hL.le
  have hc2 : 0 ≤ (1/3)*(α^3/L^2) := by positivity
  have e0 := mul_le_mul_of_nonneg_left hb0 hc0
  have e1 := mul_le_mul_of_nonneg_left hb1 hc1
  have e2 := mul_le_mul_of_nonneg_left hb2 hc2
  rw [hα] at e0 e1 e2 ⊢
  simp only [div_eq_mul_inv] at e0 e1 e2 ⊢
  linarith [e0, e1, e2]

/-! ## The numerical absorption of the prime-factor sums -/

theorem PrimeFactorTailNumeric {a e : ℝ} (ha : 0 < a) (he : 0 < e) :
    ∃ L₀ : ℝ, ∀ {q : ℕ}, 1 ≤ q → ∀ {L lam₁ : ℝ}, L₀ ≤ L → Real.log (q : ℝ) ≤ L →
      0 ≤ lam₁ → lam₁ ≤ 1 →
      (24 / L) * ((a + lam₁) * (∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (p : ℝ))
        + ((a + lam₁) ^ 2 / L) * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 2 / (p : ℝ))
        + ((a + lam₁) ^ 3 / L ^ 2) * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 3 / (p : ℝ)))
      ≤ (a + lam₁) * e := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.ZeroFreeTables.P9.primeFactors_logPow_div_le 1 (by norm_num)
  have hC₁' : ∀ q' : ℕ, 3 ≤ q' → (∑ p ∈ q'.primeFactors, Real.log (p:ℝ)/(p:ℝ))
      ≤ C₁ * (Real.log (Real.log (q':ℝ)))^2 := by
    intro q' hq'
    have h := hC₁ q' hq'
    simp only [pow_one] at h
    exact h
  obtain ⟨C₂, hC₂pos, hC₂⟩ := Work.ZeroFreeTables.P9.primeFactors_logPow_div_le 2 (by norm_num)
  obtain ⟨C₃, hC₃pos, hC₃⟩ := Work.ZeroFreeTables.P9.primeFactors_logPow_div_le 3 (by norm_num)
  set Cc : ℝ := max 1 (max C₁ (max C₂ C₃)) with hCc
  set Kk : ℝ := 1 + (a + 1) + (a + 1) ^ 2 with hKk
  refine ⟨max (Real.exp 1) ((6144 * Cc * Kk / e) ^ 2), ?_⟩
  intro q hq L lam₁ hL hlogq hlam₁ hlam₁1
  have hCc1 : 1 ≤ Cc := by rw [hCc]; exact le_max_left _ _
  have hCcpos : 0 < Cc := lt_of_lt_of_le zero_lt_one hCc1
  have hmax2 : max C₂ C₃ ≤ max 1 (max C₁ (max C₂ C₃)) :=
    le_trans (le_max_right C₁ (max C₂ C₃)) (le_max_right 1 (max C₁ (max C₂ C₃)))
  have hC1le : C₁ ≤ Cc := by
    rw [hCc]; exact le_trans (le_max_left C₁ (max C₂ C₃)) (le_max_right 1 (max C₁ (max C₂ C₃)))
  have hC2le : C₂ ≤ Cc := by
    rw [hCc]; exact le_trans (le_max_left C₂ C₃) hmax2
  have hC3le : C₃ ≤ Cc := by
    rw [hCc]; exact le_trans (le_max_right C₂ C₃) hmax2
  have hKkpos : 0 < Kk := by rw [hKk]; positivity
  have hLexp : Real.exp 1 ≤ L := le_trans (le_max_left _ _) hL
  have hLbig : (6144 * Cc * Kk / e) ^ 2 ≤ L := le_trans (le_max_right _ _) hL
  have hLpos : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) hLexp
  have hL1 : (1:ℝ) ≤ L := le_trans (by linarith [Real.add_one_le_exp 1]) hLexp
  have hlogL1 : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLpos).mpr hLexp
  have hlogLnn : 0 ≤ Real.log L := le_trans zero_le_one hlogL1
  have hαnn : 0 ≤ a + lam₁ := by linarith
  have hαle : a + lam₁ ≤ a + 1 := by linarith
  have hlog4 : Real.log L ≤ 4 * L^((1:ℝ)/4) := by
    have h := Real.log_le_rpow_div (le_of_lt hLpos) (show (0:ℝ) < 1/4 by norm_num)
    rw [div_eq_mul_inv] at h
    have h4 : ((1:ℝ)/4)⁻¹ = 4 := by norm_num
    calc Real.log L ≤ L^((1:ℝ)/4) * ((1:ℝ)/4)⁻¹ := h
      _ = 4 * L^((1:ℝ)/4) := by rw [h4]; ring
  have hmul : ∀ k : ℕ, ((4:ℝ) * L^((1:ℝ)/4))^k = (4:ℝ)^k * L^((k:ℝ)/4) := by
    intro k
    rw [mul_pow, ← Real.rpow_natCast (L^((1:ℝ)/4)) k, ← Real.rpow_mul (le_of_lt hLpos)]
    congr 1
    ring
  have hbound : ∀ k : ℕ, 2 ≤ k → k ≤ 4 →
      (Real.log L)^k / L^((k:ℝ)-1) ≤ (4:ℝ)^k * L^(1 - (3:ℝ)*k/4) := by
    intro k hk2 hk4
    have hlogpow : (Real.log L)^k ≤ ((4:ℝ) * L^((1:ℝ)/4))^k :=
      pow_le_pow_left₀ hlogLnn hlog4 k
    rw [hmul k] at hlogpow
    have hLposk : (0:ℝ) < L^((k:ℝ)-1) := Real.rpow_pos_of_pos hLpos _
    rw [div_le_iff₀ hLposk]
    calc (Real.log L)^k ≤ (4:ℝ)^k * L^((k:ℝ)/4) := hlogpow
      _ = (4:ℝ)^k * L^(1 - (3:ℝ)*k/4) * L^((k:ℝ)-1) := by
          rw [mul_assoc, ← Real.rpow_add hLpos]
          congr 1
          ring
  have hsqpos : 0 < Real.sqrt L := Real.sqrt_pos.mpr hLpos
  have hLhalf : L^(-(1/2:ℝ)) = (Real.sqrt L)⁻¹ := by
    rw [Real.rpow_neg (le_of_lt hLpos) (1/2), Real.sqrt_eq_rpow]
  have hL54 : L^(-(5/4:ℝ)) ≤ (Real.sqrt L)⁻¹ := by
    rw [← hLhalf]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hL2 : L^(-2:ℝ) ≤ (Real.sqrt L)⁻¹ := by
    rw [← hLhalf]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hb2 : (Real.log L)^2 / L ≤ 16 * (Real.sqrt L)⁻¹ := by
    have h := hbound 2 (by norm_num) (by norm_num)
    rw [show ((2:ℕ):ℝ) - 1 = ((1:ℕ):ℝ) by norm_num, Real.rpow_natCast, pow_one,
        show (1:ℝ) - 3*((2:ℕ):ℝ)/4 = -(1/2) by norm_num, hLhalf] at h
    norm_num at h
    exact h
  have hb3 : (Real.log L)^3 / L^2 ≤ 64 * (Real.sqrt L)⁻¹ := by
    have h := hbound 3 (by norm_num) (by norm_num)
    rw [show ((3:ℕ):ℝ) - 1 = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast,
        show (1:ℝ) - 3*((3:ℕ):ℝ)/4 = -(5/4) by norm_num] at h
    norm_num at h
    calc (Real.log L)^3 / L^2 ≤ 64 * L^(-(5/4:ℝ)) := h
      _ ≤ 64 * (Real.sqrt L)⁻¹ := by linarith [hL54]
  have hb4 : (Real.log L)^4 / L^3 ≤ 256 * (Real.sqrt L)⁻¹ := by
    have h := hbound 4 (by norm_num) (by norm_num)
    rw [show ((4:ℕ):ℝ) - 1 = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast,
        show (1:ℝ) - 3*((4:ℕ):ℝ)/4 = -(2:ℝ) by norm_num,
        show ((4:ℝ))^4 = 256 by norm_num] at h
    calc (Real.log L)^4 / L^3 ≤ 256 * L^(-(2:ℝ)) := h
      _ ≤ 256 * (Real.sqrt L)⁻¹ := by linarith [hL2]
  -- the three prime-factor sums
  have hS1 : (∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (p : ℝ)) ≤ Cc * (Real.log L)^2 := by
    rcases Nat.lt_or_ge q 3 with hq3 | hq3
    · have hsub : q.primeFactors ⊆ ({2} : Finset ℕ) := by
        intro p hp
        have hp' := Nat.mem_primeFactors.mp hp
        have hpq : p ≤ q := Nat.le_of_dvd (by omega) hp'.2.1
        have : p = 2 := by have := hp'.1.two_le; omega
        simp [this]
      have hsmall : (∑ p ∈ q.primeFactors, Real.log (p:ℝ)/(p:ℝ)) ≤ 1 := by
        calc (∑ p ∈ q.primeFactors, Real.log (p:ℝ)/(p:ℝ))
            ≤ ∑ p ∈ ({2}:Finset ℕ), Real.log (p:ℝ)/(p:ℝ) :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => by positivity)
          _ = Real.log 2 / 2 := by simp
          _ ≤ 1 := by
              have h2' : Real.log 2 ≤ 1 := by
                have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
              exact (div_le_one (by norm_num : (0:ℝ) < 2)).mpr (le_trans h2' (by norm_num))
      have hR : 1 ≤ Cc * (Real.log L)^2 := by
        have : (1:ℝ) ≤ (Real.log L)^2 := one_le_pow₀ hlogL1
        nlinarith [hCc1, this]
      linarith
    · have hq3' : (3:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq3
      have hlog3 : 1 < Real.log 3 := by
        rw [← Real.exp_lt_exp, Real.exp_log (by norm_num : (0:ℝ) < 3)]
        exact Real.exp_one_lt_three
      have hlogq_gt1 : 1 < Real.log (q:ℝ) :=
        lt_of_lt_of_le hlog3 (Real.log_le_log (by norm_num) hq3')
      have hllpos : 0 < Real.log (Real.log (q:ℝ)) := Real.log_pos hlogq_gt1
      have hllle : Real.log (Real.log (q:ℝ)) ≤ Real.log L :=
        Real.log_le_log (lt_trans zero_lt_one hlogq_gt1) hlogq
      have hpow : (Real.log (Real.log (q:ℝ)))^2 ≤ (Real.log L)^2 :=
        pow_le_pow_left₀ (le_of_lt hllpos) hllle 2
      calc (∑ p ∈ q.primeFactors, Real.log (p:ℝ)/(p:ℝ))
          ≤ C₁ * (Real.log (Real.log (q:ℝ)))^2 := hC₁' q hq3
        _ ≤ Cc * (Real.log (Real.log (q:ℝ)))^2 :=
            mul_le_mul_of_nonneg_right hC1le (pow_nonneg (le_of_lt hllpos) 2)
        _ ≤ Cc * (Real.log L)^2 := mul_le_mul_of_nonneg_left hpow hCcpos.le
  have hS2 : (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 2 / (p : ℝ)) ≤ Cc * (Real.log L)^3 := by
    rcases Nat.lt_or_ge q 3 with hq3 | hq3
    · have hsub : q.primeFactors ⊆ ({2} : Finset ℕ) := by
        intro p hp
        have hp' := Nat.mem_primeFactors.mp hp
        have hpq : p ≤ q := Nat.le_of_dvd (by omega) hp'.2.1
        have : p = 2 := by have := hp'.1.two_le; omega
        simp [this]
      have hsmall : (∑ p ∈ q.primeFactors, (Real.log (p:ℝ))^2/(p:ℝ)) ≤ 1 := by
        calc (∑ p ∈ q.primeFactors, (Real.log (p:ℝ))^2/(p:ℝ))
            ≤ ∑ p ∈ ({2}:Finset ℕ), (Real.log (p:ℝ))^2/(p:ℝ) :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => by positivity)
          _ = (Real.log 2)^2 / 2 := by simp
          _ ≤ 1 := by
              have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
              have h2' : Real.log 2 ≤ 1 := by
                have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
              have hle : (Real.log 2)^2 ≤ 1 := pow_le_one₀ h2 h2'
              exact (div_le_one (by norm_num : (0:ℝ) < 2)).mpr (le_trans hle (by norm_num))
      have hR : 1 ≤ Cc * (Real.log L)^3 := by
        have : (1:ℝ) ≤ (Real.log L)^3 := one_le_pow₀ hlogL1
        nlinarith [hCc1, this]
      linarith
    · have hq3' : (3:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq3
      have hlog3 : 1 < Real.log 3 := by
        rw [← Real.exp_lt_exp, Real.exp_log (by norm_num : (0:ℝ) < 3)]
        exact Real.exp_one_lt_three
      have hlogq_gt1 : 1 < Real.log (q:ℝ) :=
        lt_of_lt_of_le hlog3 (Real.log_le_log (by norm_num) hq3')
      have hllpos : 0 < Real.log (Real.log (q:ℝ)) := Real.log_pos hlogq_gt1
      have hllle : Real.log (Real.log (q:ℝ)) ≤ Real.log L :=
        Real.log_le_log (lt_trans zero_lt_one hlogq_gt1) hlogq
      have hpow : (Real.log (Real.log (q:ℝ)))^3 ≤ (Real.log L)^3 :=
        pow_le_pow_left₀ (le_of_lt hllpos) hllle 3
      calc (∑ p ∈ q.primeFactors, (Real.log (p:ℝ))^2/(p:ℝ))
          ≤ C₂ * (Real.log (Real.log (q:ℝ)))^3 := hC₂ q hq3
        _ ≤ Cc * (Real.log (Real.log (q:ℝ)))^3 :=
            mul_le_mul_of_nonneg_right hC2le (pow_nonneg (le_of_lt hllpos) 3)
        _ ≤ Cc * (Real.log L)^3 := mul_le_mul_of_nonneg_left hpow hCcpos.le
  have hS3 : (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 3 / (p : ℝ)) ≤ Cc * (Real.log L)^4 := by
    rcases Nat.lt_or_ge q 3 with hq3 | hq3
    · have hsub : q.primeFactors ⊆ ({2} : Finset ℕ) := by
        intro p hp
        have hp' := Nat.mem_primeFactors.mp hp
        have hpq : p ≤ q := Nat.le_of_dvd (by omega) hp'.2.1
        have : p = 2 := by have := hp'.1.two_le; omega
        simp [this]
      have hsmall : (∑ p ∈ q.primeFactors, (Real.log (p:ℝ))^3/(p:ℝ)) ≤ 1 := by
        calc (∑ p ∈ q.primeFactors, (Real.log (p:ℝ))^3/(p:ℝ))
            ≤ ∑ p ∈ ({2}:Finset ℕ), (Real.log (p:ℝ))^3/(p:ℝ) :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => by positivity)
          _ = (Real.log 2)^3 / 2 := by simp
          _ ≤ 1 := by
              have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
              have h2' : Real.log 2 ≤ 1 := by
                have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
              have hle : (Real.log 2)^3 ≤ 1 := pow_le_one₀ h2 h2'
              exact (div_le_one (by norm_num : (0:ℝ) < 2)).mpr (le_trans hle (by norm_num))
      have hR : 1 ≤ Cc * (Real.log L)^4 := by
        have : (1:ℝ) ≤ (Real.log L)^4 := one_le_pow₀ hlogL1
        nlinarith [hCc1, this]
      linarith
    · have hq3' : (3:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq3
      have hlog3 : 1 < Real.log 3 := by
        rw [← Real.exp_lt_exp, Real.exp_log (by norm_num : (0:ℝ) < 3)]
        exact Real.exp_one_lt_three
      have hlogq_gt1 : 1 < Real.log (q:ℝ) :=
        lt_of_lt_of_le hlog3 (Real.log_le_log (by norm_num) hq3')
      have hllpos : 0 < Real.log (Real.log (q:ℝ)) := Real.log_pos hlogq_gt1
      have hllle : Real.log (Real.log (q:ℝ)) ≤ Real.log L :=
        Real.log_le_log (lt_trans zero_lt_one hlogq_gt1) hlogq
      have hpow : (Real.log (Real.log (q:ℝ)))^4 ≤ (Real.log L)^4 :=
        pow_le_pow_left₀ (le_of_lt hllpos) hllle 4
      calc (∑ p ∈ q.primeFactors, (Real.log (p:ℝ))^3/(p:ℝ))
          ≤ C₃ * (Real.log (Real.log (q:ℝ)))^4 := hC₃ q hq3
        _ ≤ Cc * (Real.log (Real.log (q:ℝ)))^4 :=
            mul_le_mul_of_nonneg_right hC3le (pow_nonneg (le_of_lt hllpos) 4)
        _ ≤ Cc * (Real.log L)^4 := mul_le_mul_of_nonneg_left hpow hCcpos.le
  -- sqrt factor
  set c : ℝ := (Real.sqrt L)⁻¹ with hcdef
  have hcpos : 0 < c := by rw [hcdef]; positivity
  -- termwise bounds
  have hA : (24 / L) * (a + lam₁) * (∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (p : ℝ))
      ≤ 384 * (a + lam₁) * Cc * c := by
    have h1 : (24/L) * (a+lam₁) * (∑ p ∈ q.primeFactors, Real.log (p:ℝ)/(p:ℝ))
        ≤ (24/L) * (a+lam₁) * (Cc * (Real.log L)^2) :=
      mul_le_mul_of_nonneg_left hS1 (by positivity)
    have h2 : (24/L) * (a+lam₁) * (Cc * (Real.log L)^2)
        = 24 * (a+lam₁) * Cc * ((Real.log L)^2 / L) := by rw [div_eq_mul_inv]; ring
    rw [h2] at h1
    have h3 : 24 * (a+lam₁) * Cc * ((Real.log L)^2 / L)
        ≤ 24 * (a+lam₁) * Cc * (16 * c) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [hcdef]; exact hb2
    calc (24/L) * (a+lam₁) * (∑ p ∈ q.primeFactors, Real.log (p:ℝ)/(p:ℝ))
        ≤ 24 * (a+lam₁) * Cc * ((Real.log L)^2 / L) := h1
      _ ≤ 24 * (a+lam₁) * Cc * (16 * c) := h3
      _ = 384 * (a+lam₁) * Cc * c := by ring
  have hB : (24 / L) * ((a + lam₁)^2 / L) * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ))^2 / (p : ℝ))
      ≤ 1536 * (a + lam₁)^2 * Cc * c := by
    have h1 : (24/L) * ((a+lam₁)^2/L) * (∑ p ∈ q.primeFactors, (Real.log (p:ℝ))^2/(p:ℝ))
        ≤ (24/L) * ((a+lam₁)^2/L) * (Cc * (Real.log L)^3) :=
      mul_le_mul_of_nonneg_left hS2 (by positivity)
    have h2 : (24/L) * ((a+lam₁)^2/L) * (Cc * (Real.log L)^3)
        = 24 * (a+lam₁)^2 * Cc * ((Real.log L)^3 / L^2) := by rw [div_eq_mul_inv]; ring
    rw [h2] at h1
    have h3 : 24 * (a+lam₁)^2 * Cc * ((Real.log L)^3 / L^2)
        ≤ 24 * (a+lam₁)^2 * Cc * (64 * c) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [hcdef]; exact hb3
    calc (24/L) * ((a+lam₁)^2/L) * (∑ p ∈ q.primeFactors, (Real.log (p:ℝ))^2/(p:ℝ))
        ≤ 24 * (a+lam₁)^2 * Cc * ((Real.log L)^3 / L^2) := h1
      _ ≤ 24 * (a+lam₁)^2 * Cc * (64 * c) := h3
      _ = 1536 * (a+lam₁)^2 * Cc * c := by ring
  have hC : (24 / L) * ((a + lam₁)^3 / L^2) * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ))^3 / (p : ℝ))
      ≤ 6144 * (a + lam₁)^3 * Cc * c := by
    have h1 : (24/L) * ((a+lam₁)^3/L^2) * (∑ p ∈ q.primeFactors, (Real.log (p:ℝ))^3/(p:ℝ))
        ≤ (24/L) * ((a+lam₁)^3/L^2) * (Cc * (Real.log L)^4) :=
      mul_le_mul_of_nonneg_left hS3 (by positivity)
    have h2 : (24/L) * ((a+lam₁)^3/L^2) * (Cc * (Real.log L)^4)
        = 24 * (a+lam₁)^3 * Cc * ((Real.log L)^4 / L^3) := by rw [div_eq_mul_inv]; ring
    rw [h2] at h1
    have h3 : 24 * (a+lam₁)^3 * Cc * ((Real.log L)^4 / L^3)
        ≤ 24 * (a+lam₁)^3 * Cc * (256 * c) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [hcdef]; exact hb4
    calc (24/L) * ((a+lam₁)^3/L^2) * (∑ p ∈ q.primeFactors, (Real.log (p:ℝ))^3/(p:ℝ))
        ≤ 24 * (a+lam₁)^3 * Cc * ((Real.log L)^4 / L^3) := h1
      _ ≤ 24 * (a+lam₁)^3 * Cc * (256 * c) := h3
      _ = 6144 * (a+lam₁)^3 * Cc * c := by ring
  have hsq : 6144 * Cc * Kk / e ≤ Real.sqrt L := by
    have h1 : Real.sqrt ((6144 * Cc * Kk / e) ^ 2) ≤ Real.sqrt L := Real.sqrt_le_sqrt hLbig
    rwa [Real.sqrt_sq (by positivity)] at h1
  have hkey : 6144 * Cc * Kk * c ≤ e := by
    rw [hcdef, mul_inv_le_iff₀ hsqpos, mul_comm e (Real.sqrt L)]
    have h1 := mul_le_mul_of_nonneg_right hsq (le_of_lt he)
    rwa [div_mul_cancel₀ _ (ne_of_gt he)] at h1
  have hcoef : 384 * (a + lam₁) + 1536 * (a + lam₁)^2 + 6144 * (a + lam₁)^3
      ≤ (a + lam₁) * (6144 * Kk) := by
    have hA0 : 0 ≤ a + 1 := by linarith
    have h1 : (a+lam₁)^2 ≤ (a+lam₁)*(a+1) := by
      rw [pow_two]; exact mul_le_mul_of_nonneg_left hαle hαnn
    have h2 : (a+lam₁)^2 ≤ (a+1)^2 := by
      rw [pow_two, pow_two]; exact mul_le_mul hαle hαle hαnn hA0
    have h3 : (a+lam₁)^3 ≤ (a+lam₁)*(a+1)^2 := by
      calc (a+lam₁)^3 = (a+lam₁)*(a+lam₁)^2 := by ring
        _ ≤ (a+lam₁)*(a+1)^2 := mul_le_mul_of_nonneg_left h2 hαnn
    have hk1 : 1 ≤ Kk := by rw [hKk]; nlinarith [hA0, sq_nonneg (a+1)]
    rw [hKk]
    nlinarith [hαnn, h1, h3, hk1, sq_nonneg (a+lam₁), sq_nonneg (a+1)]
  have hsum : (24 / L) * (a + lam₁) * (∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (p : ℝ))
        + (24 / L) * ((a + lam₁)^2 / L) * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ))^2 / (p : ℝ))
        + (24 / L) * ((a + lam₁)^3 / L^2) * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ))^3 / (p : ℝ))
      ≤ 384 * (a + lam₁) * Cc * c + 1536 * (a + lam₁)^2 * Cc * c + 6144 * (a + lam₁)^3 * Cc * c := by
    linarith [hA, hB, hC]
  have hcoef2 : 384 * (a + lam₁) * Cc * c + 1536 * (a + lam₁)^2 * Cc * c
        + 6144 * (a + lam₁)^3 * Cc * c ≤ (a + lam₁) * e := by
    have h1 : 384 * (a + lam₁) * Cc * c + 1536 * (a + lam₁)^2 * Cc * c
        + 6144 * (a + lam₁)^3 * Cc * c
        = (384 * (a + lam₁) + 1536 * (a + lam₁)^2 + 6144 * (a + lam₁)^3) * (Cc * c) := by ring
    rw [h1]
    have h2 : (384 * (a + lam₁) + 1536 * (a + lam₁)^2 + 6144 * (a + lam₁)^3) * (Cc * c)
        ≤ ((a + lam₁) * (6144 * Kk)) * (Cc * c) :=
      mul_le_mul_of_nonneg_right hcoef (by positivity)
    have h3 : ((a + lam₁) * (6144 * Kk)) * (Cc * c) = (a + lam₁) * (6144 * Cc * Kk * c) := by ring
    rw [h3] at h2
    calc (384 * (a + lam₁) + 1536 * (a + lam₁)^2 + 6144 * (a + lam₁)^3) * (Cc * c)
        ≤ (a + lam₁) * (6144 * Cc * Kk * c) := h2
      _ ≤ (a + lam₁) * e := mul_le_mul_of_nonneg_left hkey hαnn
  have hmain : (24 / L) * ((a + lam₁) * (∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (p : ℝ))
        + ((a + lam₁) ^ 2 / L) * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 2 / (p : ℝ))
        + ((a + lam₁) ^ 3 / L ^ 2) * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 3 / (p : ℝ)))
      = (24 / L) * (a + lam₁) * (∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (p : ℝ))
        + (24 / L) * ((a + lam₁)^2 / L) * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ))^2 / (p : ℝ))
        + (24 / L) * ((a + lam₁)^3 / L^2) * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ))^3 / (p : ℝ)) := by
    ring
  rw [hmain]
  linarith [hsum, hcoef2]

/-! ## The main theorem -/

theorem ImprimitiveSigmaReduce {a e : ℝ} (ha : 0 < a) (he : 0 < e) :
    ∃ L₀ : ℝ, ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hreal : χ ^ 2 = 1)
      {L lam₁ : ℝ}, L₀ ≤ L → Real.log (q : ℝ) ≤ L → 0 ≤ lam₁ → lam₁ ≤ 1 →
      ∀ s : ℂ, s.re = 1 + a / L → |s.im| ≤ 3 →
        Work.ZeroFreeTables.SigmaP3L q L χ s a lam₁
          ≤ @Work.ZeroFreeTables.SigmaP3L χ.conductor ⟨χ.conductor_ne_zero⟩ L χ.primitiveCharacter s a lam₁
            + (a + lam₁) * e := by
  obtain ⟨L₁, hL₁⟩ := PrimeFactorTailNumeric (a := a) (e := e) ha he
  refine ⟨max L₁ (Real.exp 1), ?_⟩
  intro q _ χ hχ hreal L lam₁ hL hlogq hlam₁ hlam₁1 s hsr him
  have hLL1 : L₁ ≤ L := le_trans (le_max_left _ _) hL
  have hLexp : Real.exp 1 ≤ L := le_trans (le_max_right _ _) hL
  have hLpos : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) hLexp
  have hre : 1 < s.re := by
    rw [hsr]
    have : 0 < a / L := div_pos ha hLpos
    linarith
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hNq : χ.conductor ∣ q := χ.conductor_dvd_level
  have hψ : DirichletCharacter.changeLevel hNq χ.primitiveCharacter = χ :=
    DirichletCharacter.changeLevel_primitiveCharacter χ
  have h1 := SigmaChangeLevelAbsDiff (N := χ.conductor) (q := q) hNq χ.primitiveCharacter hLpos hre ha hlam₁
  rw [hψ] at h1
  have h2 := NonCoprimeHbWLTailLe (q := q) (σ := s.re) hre hLpos ha hlam₁
  have h3 := hL₁ (Nat.pos_of_neZero q) hLL1 hlogq hlam₁ hlam₁1
  have hαnn : 0 ≤ a + lam₁ := by linarith
  have hS1nn : 0 ≤ ∑ p ∈ q.primeFactors, Real.log (p:ℝ)/(p:ℝ) :=
    Finset.sum_nonneg (fun p _ => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))
  have hS2nn : 0 ≤ ∑ p ∈ q.primeFactors, (Real.log (p:ℝ))^2/(p:ℝ) :=
    Finset.sum_nonneg (fun p _ => div_nonneg (pow_nonneg (Real.log_natCast_nonneg p) 2) (Nat.cast_nonneg p))
  have hS3nn : 0 ≤ ∑ p ∈ q.primeFactors, (Real.log (p:ℝ))^3/(p:ℝ) :=
    Finset.sum_nonneg (fun p _ => div_nonneg (pow_nonneg (Real.log_natCast_nonneg p) 3) (Nat.cast_nonneg p))
  have h8 : 8 * ((a+lam₁)^3/L^2) * (∑ p ∈ q.primeFactors, (Real.log (p:ℝ))^3/(p:ℝ))
      ≤ 24 * ((a+lam₁)^3/L^2) * (∑ p ∈ q.primeFactors, (Real.log (p:ℝ))^3/(p:ℝ)) := by
    apply mul_le_mul_of_nonneg_right _ hS3nn
    apply mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  have hXT : L⁻¹ * (∑' n : ℕ, (if Nat.Coprime n q then (0:ℝ) else 1)
        * (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-s.re)
        * Work.ZeroFreeTables.hbWL L a lam₁ n)
      ≤ (24/L) * ((a+lam₁) * (∑ p ∈ q.primeFactors, Real.log (p:ℝ)/(p:ℝ))
        + ((a+lam₁)^2/L) * (∑ p ∈ q.primeFactors, (Real.log (p:ℝ))^2/(p:ℝ))
        + ((a+lam₁)^3/L^2) * (∑ p ∈ q.primeFactors, (Real.log (p:ℝ))^3/(p:ℝ))) := by
    have hX : 24 * (a+lam₁) * (∑ p ∈ q.primeFactors, Real.log (p:ℝ)/(p:ℝ))
          + 24 * ((a+lam₁)^2/L) * (∑ p ∈ q.primeFactors, (Real.log (p:ℝ))^2/(p:ℝ))
          + 8 * ((a+lam₁)^3/L^2) * (∑ p ∈ q.primeFactors, (Real.log (p:ℝ))^3/(p:ℝ))
        ≤ 24 * ((a+lam₁) * (∑ p ∈ q.primeFactors, Real.log (p:ℝ)/(p:ℝ))
          + ((a+lam₁)^2/L) * (∑ p ∈ q.primeFactors, (Real.log (p:ℝ))^2/(p:ℝ))
          + ((a+lam₁)^3/L^2) * (∑ p ∈ q.primeFactors, (Real.log (p:ℝ))^3/(p:ℝ))) := by
      nlinarith [h8, hS1nn, hS2nn, hS3nn, hαnn, sq_nonneg (a+lam₁), hLpos]
    calc L⁻¹ * (∑' n : ℕ, (if Nat.Coprime n q then (0:ℝ) else 1)
            * (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-s.re)
            * Work.ZeroFreeTables.hbWL L a lam₁ n)
        ≤ L⁻¹ * (24 * (a+lam₁) * (∑ p ∈ q.primeFactors, Real.log (p:ℝ)/(p:ℝ))
            + 24 * ((a+lam₁)^2/L) * (∑ p ∈ q.primeFactors, (Real.log (p:ℝ))^2/(p:ℝ))
            + 8 * ((a+lam₁)^3/L^2) * (∑ p ∈ q.primeFactors, (Real.log (p:ℝ))^3/(p:ℝ))) :=
          mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr hLpos.le)
      _ ≤ L⁻¹ * (24 * ((a+lam₁) * (∑ p ∈ q.primeFactors, Real.log (p:ℝ)/(p:ℝ))
            + ((a+lam₁)^2/L) * (∑ p ∈ q.primeFactors, (Real.log (p:ℝ))^2/(p:ℝ))
            + ((a+lam₁)^3/L^2) * (∑ p ∈ q.primeFactors, (Real.log (p:ℝ))^3/(p:ℝ)))) :=
          mul_le_mul_of_nonneg_left hX (inv_nonneg.mpr hLpos.le)
      _ = (24/L) * ((a+lam₁) * (∑ p ∈ q.primeFactors, Real.log (p:ℝ)/(p:ℝ))
            + ((a+lam₁)^2/L) * (∑ p ∈ q.primeFactors, (Real.log (p:ℝ))^2/(p:ℝ))
            + ((a+lam₁)^3/L^2) * (∑ p ∈ q.primeFactors, (Real.log (p:ℝ))^3/(p:ℝ))) := by ring
  have hfin : Work.ZeroFreeTables.SigmaP3L q L χ s a lam₁
      - @Work.ZeroFreeTables.SigmaP3L χ.conductor ⟨χ.conductor_ne_zero⟩ L χ.primitiveCharacter s a lam₁
      ≤ (a + lam₁) * e := by
    calc Work.ZeroFreeTables.SigmaP3L q L χ s a lam₁
          - @Work.ZeroFreeTables.SigmaP3L χ.conductor ⟨χ.conductor_ne_zero⟩ L χ.primitiveCharacter s a lam₁
        ≤ |Work.ZeroFreeTables.SigmaP3L q L χ s a lam₁
          - @Work.ZeroFreeTables.SigmaP3L χ.conductor ⟨χ.conductor_ne_zero⟩ L χ.primitiveCharacter s a lam₁| :=
            le_abs_self _
      _ ≤ L⁻¹ * (∑' n : ℕ, (if Nat.Coprime n q then (0:ℝ) else 1)
            * (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-s.re)
            * Work.ZeroFreeTables.hbWL L a lam₁ n) := h1
      _ ≤ (24/L) * ((a+lam₁) * (∑ p ∈ q.primeFactors, Real.log (p:ℝ)/(p:ℝ))
            + ((a+lam₁)^2/L) * (∑ p ∈ q.primeFactors, (Real.log (p:ℝ))^2/(p:ℝ))
            + ((a+lam₁)^3/L^2) * (∑ p ∈ q.primeFactors, (Real.log (p:ℝ))^3/(p:ℝ))) := hXT
      _ ≤ (a + lam₁) * e := h3
  linarith [hfin]

end Work.ZeroFreeTables.XY
