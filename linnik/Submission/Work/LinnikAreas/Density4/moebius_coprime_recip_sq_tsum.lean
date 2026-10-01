import Mathlib
import Submission.Commons.NumberTheory.Moebius.tsum_moebius_div_sq
import Submission.Work.LinnikAreas.Density4.prod_primesBelow_split

/-!
# The Möbius series restricted to integers coprime to `r`, at `s = 2`

We prove
`∑_{gcd(a,r)=1} μ(a)/a² = (6/π²) · ∏_{p | r} (1 - 1/p²)⁻¹`,
which is the `s = 2` case of the Euler product
`∑_{gcd(a,r)=1} μ(a)/a^s = ∏_{p ∤ r} (1 - p^{-s}) = ζ(s)⁻¹ · ∏_{p|r} (1-p^{-s})⁻¹`.
-/

namespace Work.LinnikAreas.Density4

open scoped ArithmeticFunction.Moebius

/-- `μ(a)/a²` if `a` is coprime to `r`, and `0` otherwise. -/
noncomputable def moebiusCoprimeRecipSq (r a : ℕ) : ℝ :=
  if Nat.Coprime a r then (ArithmeticFunction.moebius a : ℝ) / (a : ℝ) ^ 2 else 0

/-- The local factor `1 - 1/p²` of the Euler product of `ζ⁻¹`. -/
noncomputable def oneSubInvSq (p : ℕ) : ℝ := 1 - (1 : ℝ) / (p : ℝ) ^ 2

lemma moebiusCoprimeRecipSq_zero (r : ℕ) : moebiusCoprimeRecipSq r 0 = 0 := by
  unfold moebiusCoprimeRecipSq
  simp

lemma moebiusCoprimeRecipSq_one (r : ℕ) : moebiusCoprimeRecipSq r 1 = 1 := by
  unfold moebiusCoprimeRecipSq
  simp

lemma moebiusCoprimeRecipSq_mul (r : ℕ) {m n : ℕ} (h : Nat.Coprime m n) :
    moebiusCoprimeRecipSq r (m * n) = moebiusCoprimeRecipSq r m * moebiusCoprimeRecipSq r n := by
  unfold moebiusCoprimeRecipSq
  simp only [Nat.coprime_mul_iff_left]
  by_cases hm : Nat.Coprime m r
  · by_cases hn : Nat.Coprime n r
    · rw [if_pos ⟨hm, hn⟩, if_pos hm, if_pos hn,
        ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime h]
      push_cast
      field_simp
    · rw [if_neg (fun hh => hn hh.2), if_pos hm, if_neg hn]
      simp
  · rw [if_neg (fun hh => hm hh.1), if_neg hm]
    simp

lemma summable_norm_moebiusCoprimeRecipSq (r : ℕ) :
    Summable (fun a : ℕ => ‖moebiusCoprimeRecipSq r a‖) := by
  apply Summable.of_nonneg_of_le (fun a => norm_nonneg _) _ hasSum_zeta_two.summable
  intro a
  unfold moebiusCoprimeRecipSq
  split_ifs with h
  · rw [norm_div]
    have hden : ‖((a : ℝ)) ^ 2‖ = (a : ℝ) ^ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    rw [hden]
    have hμ : ‖(ArithmeticFunction.moebius a : ℝ)‖ ≤ 1 := by
      rw [Real.norm_eq_abs]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := a)
    exact div_le_div_of_nonneg_right hμ (sq_nonneg _)
  · simp

/-- The value of the `p`-local Euler factor of `∑_{gcd(a,r)=1} μ(a)/a²`:
it is `1` when `p ∣ r` and `1 - 1/p²` otherwise. -/
lemma moebiusCoprimeRecipSq_local (r p : ℕ) (hr : 1 ≤ r) (hp : p.Prime) :
    (∑' e : ℕ, moebiusCoprimeRecipSq r (p ^ e))
      = if p ∈ r.primeFactors then 1 else oneSubInvSq p := by
  have hzero : ∀ e, 2 ≤ e → moebiusCoprimeRecipSq r (p ^ e) = 0 := by
    intro e he
    have h0 : ArithmeticFunction.moebius (p ^ e) = 0 := by
      rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega)]
      simp [show e ≠ 1 by omega]
    simp [moebiusCoprimeRecipSq, h0]
  rw [tsum_eq_sum (s := Finset.range 2) (fun e he => by
    simp only [Finset.mem_range, not_lt] at he
    exact hzero e he)]
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  have hc : Nat.Coprime p r ↔ p ∉ r.primeFactors := by
    rw [Nat.mem_primeFactors, hp.coprime_iff_not_dvd]
    constructor
    · rintro h ⟨_, hdvd, _⟩; exact h hdvd
    · intro h hcon; exact h ⟨hp, hcon, by omega⟩
  simp only [pow_zero, pow_one, moebiusCoprimeRecipSq, oneSubInvSq]
  rw [if_pos (Nat.coprime_one_left r)]
  simp only [ArithmeticFunction.moebius_apply_one, Nat.cast_one, one_pow, div_one]
  rw [ArithmeticFunction.moebius_apply_prime hp]
  push_cast
  by_cases h : p ∈ r.primeFactors
  · have hcn : ¬ Nat.Coprime p r := fun hh => (hc.mp hh) h
    rw [if_neg hcn, if_pos h]
    norm_num
  · have hcp : Nat.Coprime p r := hc.mpr h
    rw [if_pos hcp, if_neg h]
    ring

lemma oneSubInvSq_ne_zero (p : ℕ) (hp : p.Prime) : oneSubInvSq p ≠ 0 := by
  have h1 : (1 : ℝ) < (p : ℝ) ^ 2 := by
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    nlinarith [hp2, sq_nonneg ((p : ℝ) - 1)]
  have h2 : (1 : ℝ) / (p : ℝ) ^ 2 < 1 := (div_lt_one (by positivity)).mpr h1
  have h3 : (0 : ℝ) < oneSubInvSq p := by rw [oneSubInvSq]; linarith
  exact ne_of_gt h3

/-- The Euler product for `∑_{gcd(a,r)=1} μ(a)/a²`, in the form of convergence of the
finite partial products over the primes below `N`. -/
lemma moebiusCoprimeRecipSq_euler_tendsto (r : ℕ) (hr : 1 ≤ r) :
    Filter.Tendsto (fun N : ℕ => ∏ p ∈ Nat.primesBelow N,
        (if p ∈ r.primeFactors then 1 else oneSubInvSq p)) Filter.atTop
      (nhds (∑' a : ℕ, moebiusCoprimeRecipSq r a)) := by
  have h := EulerProduct.eulerProduct (f := moebiusCoprimeRecipSq r)
      (moebiusCoprimeRecipSq_one r)
      (fun {m n : ℕ} (h : Nat.Coprime m n) => moebiusCoprimeRecipSq_mul r h)
      (summable_norm_moebiusCoprimeRecipSq r)
      (moebiusCoprimeRecipSq_zero r)
  refine h.congr (fun N => ?_)
  apply Finset.prod_congr rfl
  intro p hp
  exact moebiusCoprimeRecipSq_local r p hr (Nat.mem_primesBelow.mp hp).2

theorem moebius_coprime_recip_sq_tsum (r : ℕ) (hr : 1 ≤ r) :
    (∑' a : ℕ, if Nat.Coprime a r then (ArithmeticFunction.moebius a : ℝ) / (a : ℝ) ^ 2 else 0)
      = (6 / Real.pi ^ 2) * ∏ p ∈ r.primeFactors, (1 - (1 : ℝ) / (p : ℝ) ^ 2)⁻¹ := by
  change (∑' a : ℕ, moebiusCoprimeRecipSq r a)
      = (6 / Real.pi ^ 2) * ∏ p ∈ r.primeFactors, (oneSubInvSq p)⁻¹
  set c : ℝ := ∏ p ∈ r.primeFactors, oneSubInvSq p with hc
  have hcnz : c ≠ 0 := by
    rw [hc]
    exact Finset.prod_ne_zero_iff.mpr fun p hp =>
      oneSubInvSq_ne_zero p (Nat.prime_of_mem_primeFactors hp)
  have hG := moebiusCoprimeRecipSq_euler_tendsto r hr
  have hA_lim : Filter.Tendsto (fun N : ℕ => ∏ p ∈ Nat.primesBelow N, oneSubInvSq p)
      Filter.atTop (nhds (6 / Real.pi ^ 2)) := by
    have h1 : Filter.Tendsto (fun N : ℕ => ∏ p ∈ Nat.primesBelow N, oneSubInvSq p)
        Filter.atTop (nhds (∑' a : ℕ, moebiusCoprimeRecipSq 1 a)) := by
      have h0 := moebiusCoprimeRecipSq_euler_tendsto 1 le_rfl
      refine h0.congr (fun N => ?_)
      apply Finset.prod_congr rfl
      intro p hp
      simp
    have hG1 : (∑' a : ℕ, moebiusCoprimeRecipSq 1 a) = 6 / Real.pi ^ 2 := by
      rw [← Commons.NumberTheory.Moebius.tsum_moebius_div_sq]
      apply tsum_congr
      intro a
      rw [moebiusCoprimeRecipSq]
      simp
    rwa [hG1] at h1
  have hsub : ∀ N : ℕ, r + 1 ≤ N → r.primeFactors ⊆ Nat.primesBelow N := by
    intro N hN p hp
    rw [Nat.mem_primesBelow]
    refine ⟨?_, Nat.prime_of_mem_primeFactors hp⟩
    have hpr : p ∣ r := (Nat.mem_primeFactors.mp hp).2.1
    have hle : p ≤ r := Nat.le_of_dvd (by omega) hpr
    omega
  have hev : (fun N : ℕ => ∏ p ∈ Nat.primesBelow N, oneSubInvSq p) =ᶠ[Filter.atTop]
      (fun N : ℕ => (∏ p ∈ Nat.primesBelow N,
        (if p ∈ r.primeFactors then 1 else oneSubInvSq p)) * c) := by
    show ∀ᶠ N in Filter.atTop, (∏ p ∈ Nat.primesBelow N, oneSubInvSq p)
        = (∏ p ∈ Nat.primesBelow N, (if p ∈ r.primeFactors then 1 else oneSubInvSq p)) * c
    rw [Filter.eventually_atTop]
    exact ⟨r + 1, fun N hN => by
      rw [prod_primesBelow_split r N (hsub N hN) oneSubInvSq, hc]⟩
  have h2 : (∑' a : ℕ, moebiusCoprimeRecipSq r a) * c = 6 / Real.pi ^ 2 := by
    have hh : Filter.Tendsto (fun N : ℕ => (∏ p ∈ Nat.primesBelow N,
        (if p ∈ r.primeFactors then 1 else oneSubInvSq p)) * c) Filter.atTop
        (nhds ((∑' a : ℕ, moebiusCoprimeRecipSq r a) * c)) :=
      hG.mul tendsto_const_nhds
    have hh2 : Filter.Tendsto (fun N : ℕ => ∏ p ∈ Nat.primesBelow N, oneSubInvSq p)
        Filter.atTop (nhds ((∑' a : ℕ, moebiusCoprimeRecipSq r a) * c)) :=
      hh.congr' hev.symm
    exact tendsto_nhds_unique hh2 hA_lim
  rw [show (∑' a : ℕ, moebiusCoprimeRecipSq r a) = (6 / Real.pi ^ 2) * c⁻¹ from by
        rw [← h2, mul_inv_cancel_right₀ hcnz]]
  congr 1
  rw [hc]
  exact (Finset.prod_inv_distrib oneSubInvSq).symm

end Work.LinnikAreas.Density4
