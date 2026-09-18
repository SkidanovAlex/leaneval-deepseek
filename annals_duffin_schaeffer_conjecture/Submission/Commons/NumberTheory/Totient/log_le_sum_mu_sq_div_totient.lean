import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# `∑_{r ≤ R} μ(r)²/φ(r) ≥ log R`

A lower bound for the squarefree-restricted sum of `1/φ`, in the form needed in
Helfgott's large sieve for primes (arXiv:1312.7748, (eq. `eq:coro`)).

**Math.**  Writing `rad n = ∏_{p | n} p` for the radical, the identity
`1/φ(r) = (1/r) ∏_{p | r} (1 - 1/p)⁻¹` for squarefree `r` expands as
`1/φ(r) = (1/r) ∑_{rad(m) | r} 1/m`.  Hence

`∑_{r ≤ R} μ(r)²/φ(r) = ∑_{rad(n) ≤ R} 1/n ≥ ∑_{n ≤ R} 1/n ≥ log R`,

the middle inequality because `rad n ≤ n`.  The proof below makes this explicit
via the bijection `n ↦ (rad n, n / rad n)` between `{1,…,R}` and the set of pairs
`(r,m)` with `r ≤ R` squarefree, `m ≤ R/r` and `primeFactors m ⊆ primeFactors r`,
combined with the Euler-product bound `∑_{m | N} 1/m ≤ ∏_{p | N} (1 - 1/p)⁻¹`.
-/

open scoped BigOperators
open Finset

namespace Commons.NumberTheory.Totient

noncomputable section

/-! ## The radical and its basic properties -/

/-- The radical `rad n = ∏_{p | n} p` of a natural number. -/
private def rad (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

private lemma rad_pos (n : ℕ) : 0 < rad n := by
  unfold rad; exact Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)

private lemma rad_ne_zero (n : ℕ) : rad n ≠ 0 := (rad_pos n).ne'

private lemma rad_dvd (n : ℕ) : rad n ∣ n := by
  unfold rad; exact Nat.prod_primeFactors_dvd n

private lemma rad_squarefree (n : ℕ) : Squarefree (rad n) := by
  unfold rad
  have hprod_ne : (∏ p ∈ n.primeFactors, p) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun p hp => (Nat.prime_of_mem_primeFactors hp).ne_zero)
  rw [Nat.squarefree_iff_factorization_le_one hprod_ne]
  intro q
  rw [Nat.factorization_prod_apply (fun p hp => (Nat.prime_of_mem_primeFactors hp).ne_zero)]
  have h1 : ∀ p ∈ n.primeFactors, p.factorization q = if p = q then (1:ℕ) else 0 := by
    intro p hp; rw [(Nat.prime_of_mem_primeFactors hp).factorization]; simp [Finsupp.single_apply]
  rw [Finset.sum_congr rfl h1]
  rw [Finset.sum_ite_eq' n.primeFactors q (fun _ => 1)]
  split <;> norm_num

private lemma primeFactors_rad (n : ℕ) : (rad n).primeFactors = n.primeFactors := by
  unfold rad; exact Nat.primeFactors_prod_primeFactors n

private lemma rad_mul_eq_self {r m : ℕ} (hr : Squarefree r) (hm : m ≠ 0)
    (h : m.primeFactors ⊆ r.primeFactors) : rad (r * m) = r := by
  have hr0 : r ≠ 0 := fun h0 => not_squarefree_zero (h0 ▸ hr)
  have hunion : (r * m).primeFactors = r.primeFactors := by
    rw [Nat.primeFactors_mul hr0 hm, Finset.union_eq_left.mpr h]
  calc rad (r * m) = ∏ p ∈ r.primeFactors, p := by unfold rad; rw [hunion]
    _ = r := Nat.prod_primeFactors_of_squarefree hr

private lemma rad_le {n : ℕ} (hn : 1 ≤ n) : rad n ≤ n :=
  Nat.le_of_dvd (by omega) (rad_dvd n)

/-! ## The reindexing identity -/

/-- `∑_{n ≤ R} 1/n` reindexed along `n ↦ (rad n, n / rad n)`. -/
private lemma sum_inv_eq_reindex (R : ℕ) :
    (∑ n ∈ Finset.Icc 1 R, (1:ℝ)/n)
      = ∑ r ∈ (Finset.Icc 1 R).filter Squarefree,
          (1/(r:ℝ)) * ∑ m ∈ (Finset.Icc 1 (R/r)).filter (fun m => m.primeFactors ⊆ r.primeFactors),
            (1:ℝ)/m := by
  classical
  set F : Finset ℕ := (Finset.Icc 1 R).filter Squarefree with hF
  set G : ℕ → Finset ℕ := fun r => (Finset.Icc 1 (R/r)).filter
      (fun m => m.primeFactors ⊆ r.primeFactors) with hG
  have hbij : (∑ x ∈ F.sigma G, (1:ℝ)/(x.1 * x.2)) = ∑ n ∈ Finset.Icc 1 R, (1:ℝ)/n := by
    apply Finset.sum_bij (fun x _ => x.1 * x.2)
    · intro x hx
      rw [Finset.mem_sigma] at hx
      obtain ⟨hrF, hmG⟩ := hx
      rw [hF, Finset.mem_filter, Finset.mem_Icc] at hrF
      rw [hG, Finset.mem_filter, Finset.mem_Icc] at hmG
      obtain ⟨⟨hr1, hrR⟩, hsq⟩ := hrF
      obtain ⟨⟨hm1, hmRd⟩, hsub⟩ := hmG
      rw [Finset.mem_Icc]
      refine ⟨?_, ?_⟩
      · exact le_trans (by omega : 1 ≤ 1 * 1) (Nat.mul_le_mul hr1 hm1)
      · calc x.1 * x.2 ≤ x.1 * (R / x.1) := Nat.mul_le_mul_left _ hmRd
          _ ≤ R := Nat.mul_div_le R x.1
    · intro a ha b hb hab
      rw [Finset.mem_sigma] at ha hb
      obtain ⟨haF, haG⟩ := ha
      obtain ⟨hbF, hbG⟩ := hb
      rw [hF, Finset.mem_filter, Finset.mem_Icc] at haF hbF
      rw [hG, Finset.mem_filter, Finset.mem_Icc] at haG hbG
      obtain ⟨⟨ha1, haR⟩, hasq⟩ := haF
      obtain ⟨haG1, hasub⟩ := haG
      obtain ⟨⟨hb1, hbR⟩, hbsq⟩ := hbF
      obtain ⟨hbG1, hbsub⟩ := hbG
      have ha2 : a.2 ≠ 0 := by have := haG1.1; omega
      have hb2 : b.2 ≠ 0 := by have := hbG1.1; omega
      have hra : rad (a.1 * a.2) = a.1 := rad_mul_eq_self hasq ha2 hasub
      have hrb : rad (b.1 * b.2) = b.1 := rad_mul_eq_self hbsq hb2 hbsub
      have hfst : a.1 = b.1 := by rw [← hra, hab, hrb]
      have hsnd : a.2 = b.2 := by
        have h : a.1 * a.2 = a.1 * b.2 := by rw [hab, hfst]
        exact Nat.mul_left_cancel (by omega : 0 < a.1) h
      exact Sigma.ext hfst (heq_of_eq hsnd)
    · intro n hn
      rw [Finset.mem_Icc] at hn
      obtain ⟨hn1, hnR⟩ := hn
      refine ⟨⟨rad n, n / rad n⟩, ?_, ?_⟩
      · rw [Finset.mem_sigma]
        constructor
        · rw [hF, Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨Nat.one_le_iff_ne_zero.mpr (rad_ne_zero n),
            le_trans (rad_le hn1) hnR⟩, rad_squarefree n⟩
        · rw [hG, Finset.mem_filter, Finset.mem_Icc]
          refine ⟨⟨?_, ?_⟩, ?_⟩
          · rw [Nat.one_le_div_iff (rad_pos n)]
            exact rad_le hn1
          · exact Nat.div_le_div_right hnR
          · rw [primeFactors_rad]
            exact Nat.primeFactors_mono (Nat.div_dvd_of_dvd (rad_dvd n)) (by omega)
      · exact Nat.mul_div_cancel' (rad_dvd n)
    · intro x _; push_cast; ring
  calc (∑ n ∈ Finset.Icc 1 R, (1:ℝ)/n)
      = ∑ x ∈ F.sigma G, (1:ℝ)/(x.1 * x.2) := hbij.symm
    _ = ∑ r ∈ F, ∑ m ∈ G r, (1:ℝ)/(r*m) := by
          rw [Finset.sum_sigma']
    _ = ∑ r ∈ F, (1/(r:ℝ)) * ∑ m ∈ G r, (1:ℝ)/m := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro m hm
          rw [one_div, one_div, one_div, mul_inv]

/-! ## The Euler-product bound for divisor sums -/

/-- Geometric partial-sum bound: `∑_{i<N} (1/p)^i ≤ (1 - 1/p)⁻¹` for a prime `p`. -/
private lemma geom_sum_inv_le (p : ℕ) (hp : Nat.Prime p) (N : ℕ) :
    ∑ i ∈ Finset.range N, ((p:ℝ)⁻¹)^i ≤ (1 - (p:ℝ)⁻¹)⁻¹ := by
  have hp2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp.two_le
  have hx0 : 0 ≤ (p:ℝ)⁻¹ := by positivity
  have hx1 : (p:ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have h1x : 0 < 1 - (p:ℝ)⁻¹ := by linarith
  rw [inv_eq_one_div (1 - (p:ℝ)⁻¹), le_div_iff₀ h1x, geom_sum_mul_neg]
  have : 0 ≤ ((p:ℝ)⁻¹)^N := pow_nonneg hx0 N
  linarith

/-- `∑_{m | n} 1/m ≤ ∏_{p | n} (1 - 1/p)⁻¹`. -/
private theorem sum_divisors_inv_le_euler_product (n : ℕ) :
    (∑ m ∈ n.divisors, (1:ℝ)/m) ≤ ∏ p ∈ n.primeFactors, (1 - (p:ℝ)⁻¹)⁻¹ := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  set g : ArithmeticFunction ℝ := ⟨fun m => (m:ℝ)⁻¹, by simp⟩ with hg
  have hgd : ∀ d, g d = (d:ℝ)⁻¹ := fun d => rfl
  have hgmult : g.IsMultiplicative := by
    refine ⟨?_, ?_⟩
    · simp [hg]
    · intro m n _
      rw [hgd, hgd, hgd, Nat.cast_mul, mul_inv]
  have hz : (ArithmeticFunction.zeta : ArithmeticFunction ℝ).IsMultiplicative :=
    ArithmeticFunction.IsMultiplicative.natCast ArithmeticFunction.isMultiplicative_zeta
  have hFmult : (g * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)).IsMultiplicative :=
    hgmult.mul hz
  have hFapply : ∀ m, (g * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m
      = ∑ d ∈ m.divisors, (1:ℝ)/d := by
    intro m
    rw [ArithmeticFunction.coe_mul_zeta_apply]
    apply Finset.sum_congr rfl
    intro d _
    rw [hgd, one_div]
  calc (∑ d ∈ n.divisors, (1:ℝ)/d)
      = (g * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n := (hFapply n).symm
    _ = n.factorization.prod
          (fun p k => (g * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) (p^k)) :=
          ArithmeticFunction.IsMultiplicative.multiplicative_factorization _ hFmult hn
    _ = ∏ p ∈ n.primeFactors,
          (g * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) (p^(n.factorization p)) :=
          Nat.prod_factorization_eq_prod_primeFactors _
    _ ≤ ∏ p ∈ n.primeFactors, (1 - (p:ℝ)⁻¹)⁻¹ := by
          apply Finset.prod_le_prod₀
          · intro p hp
            rw [hFapply, Nat.sum_divisors_prime_pow (Nat.prime_of_mem_primeFactors hp)]
            apply Finset.sum_nonneg
            intro i _
            positivity
          · intro p hp
            have hpp := Nat.prime_of_mem_primeFactors hp
            rw [hFapply, Nat.sum_divisors_prime_pow hpp]
            have hcast : ∀ x, (1:ℝ)/(((p^x : ℕ)):ℝ) = ((p:ℝ)⁻¹)^x := by
              intro x; rw [Nat.cast_pow, inv_pow, one_div]
            rw [Finset.sum_congr rfl (fun x _ => hcast x)]
            exact geom_sum_inv_le p hpp _

/-- `r / φ(r) = ∏_{p | r} (1 - 1/p)⁻¹` for `r ≥ 1`. -/
private lemma totient_ratio_eq_prod_inv (r : ℕ) (hr : 1 ≤ r) :
    (r:ℝ)/(Nat.totient r : ℝ) = ∏ p ∈ r.primeFactors, (1 - (p:ℝ)⁻¹)⁻¹ := by
  have hmain := congrArg (fun x:ℕ => (x:ℝ)) (Nat.totient_mul_prod_primeFactors r)
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_prod, Nat.cast_prod] at hmain
  have hr0 : (r:ℝ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
  have hP0 : (∏ p ∈ r.primeFactors, (p:ℝ)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]; intro p hp
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
  have hstep : (∏ p ∈ r.primeFactors, ((p-1:ℕ):ℝ)) / (∏ p ∈ r.primeFactors, (p:ℝ))
      = ∏ p ∈ r.primeFactors, (1 - (p:ℝ)⁻¹) := by
    rw [← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hp0 : (p:ℝ) ≠ 0 := by exact_mod_cast hpp.ne_zero
    have hcast1 : ((p-1:ℕ):ℝ) = (p:ℝ) - 1 := by rw [Nat.cast_sub hpp.one_le]; ring
    rw [hcast1]
    field_simp
  have hφeq : (Nat.totient r : ℝ) = (r:ℝ) * ∏ p ∈ r.primeFactors, (1 - (p:ℝ)⁻¹) := by
    have hthis : (∏ p ∈ r.primeFactors, ((p-1:ℕ):ℝ))
        = (∏ p ∈ r.primeFactors, (1 - (p:ℝ)⁻¹)) * (∏ p ∈ r.primeFactors, (p:ℝ)) :=
      (div_eq_iff hP0).mp hstep
    exact mul_right_cancel₀ hP0 (by rw [hmain, hthis]; ring)
  rw [hφeq, div_mul_eq_div_div, div_self hr0, one_div, ← Finset.prod_inv_distrib]

/-! ## The smooth-sum bound -/

/-- Every `P`-smooth `m ≤ Y` divides `(∏_{p ∈ P} p)^Y`; here `P = r.primeFactors`. -/
private lemma smooth_dvd_pow (r Y m : ℕ) (hr : 1 ≤ r) (hm1 : 1 ≤ m) (hmY : m ≤ Y)
    (hsub : m.primeFactors ⊆ r.primeFactors) : m ∣ r^Y := by
  have hm0 : m ≠ 0 := by omega
  have hN0 : r^Y ≠ 0 := pow_ne_zero _ (by omega)
  apply (Nat.factorization_le_iff_dvd hm0 hN0).mp
  rw [Finsupp.le_def]
  intro q
  rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  by_cases hq0 : m.factorization q = 0
  · simp [hq0]
  · have hqpos : 0 < m.factorization q := Nat.pos_of_ne_zero hq0
    have hqp : q.Prime := by
      by_contra h
      exact hq0 (Nat.factorization_eq_zero_of_not_prime m h)
    have hqdm : q ∣ m := hqp.dvd_iff_one_le_factorization hm0 |>.mpr (by omega)
    have hqmem : q ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨hqp, hqdm, hm0⟩
    have hqr : q ∈ r.primeFactors := hsub hqmem
    have hrdvd : q ∣ r := (Nat.mem_primeFactors.mp hqr).2.1
    have hr0 : r ≠ 0 := by omega
    have h1r : 1 ≤ r.factorization q := hqp.dvd_iff_one_le_factorization hr0 |>.mp hrdvd
    have hleY : m.factorization q ≤ Y := by
      have hdvd : q ^ m.factorization q ∣ m := hqp.pow_dvd_iff_le_factorization hm0 |>.mpr le_rfl
      have hle : q ^ m.factorization q ≤ m := Nat.le_of_dvd (by omega) hdvd
      have h2 : 2 ^ m.factorization q ≤ q ^ m.factorization q := Nat.pow_le_pow_left hqp.two_le _
      have h3 : 2 ^ m.factorization q ≤ Y := le_trans h2 (le_trans hle hmY)
      have h4 : m.factorization q < 2 ^ m.factorization q := Nat.lt_two_pow_self
      omega
    nlinarith [hleY, h1r]

/-- `∑_{m ≤ Y, primeFactors m ⊆ primeFactors r} 1/m ≤ r/φ(r)`. -/
private lemma smooth_inv_sum_le_totient_ratio (r Y : ℕ) (hr : 1 ≤ r) :
    (∑ m ∈ (Finset.Icc 1 Y).filter (fun m => m.primeFactors ⊆ r.primeFactors), (1:ℝ)/m)
      ≤ (r:ℝ)/(Nat.totient r : ℝ) := by
  rw [totient_ratio_eq_prod_inv r hr]
  rcases eq_or_ne Y 0 with rfl | hY
  · simp only [Finset.Icc_eq_empty_of_lt (show 0 < 1 by omega), Finset.filter_empty,
      Finset.sum_empty]
    apply Finset.prod_nonneg
    intro p hp
    have hp2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have hpos : (0:ℝ) < 1 - (p:ℝ)⁻¹ := by
      rw [sub_pos]; exact inv_lt_one_of_one_lt₀ (by linarith)
    positivity
  · have hN : r^Y ≠ 0 := pow_ne_zero _ (by omega)
    have hsubset : (Finset.Icc 1 Y).filter (fun m => m.primeFactors ⊆ r.primeFactors)
        ⊆ (r^Y).divisors := by
      intro m hm
      rw [Finset.mem_filter, Finset.mem_Icc] at hm
      obtain ⟨⟨hm1, hmY⟩, hsub⟩ := hm
      rw [Nat.mem_divisors]
      exact ⟨smooth_dvd_pow r Y m hr hm1 hmY hsub, hN⟩
    have hnn : ∀ m ∈ (r^Y).divisors,
        m ∉ (Finset.Icc 1 Y).filter (fun m => m.primeFactors ⊆ r.primeFactors) → 0 ≤ (1:ℝ)/m := by
      intro m _ _; positivity
    calc (∑ m ∈ (Finset.Icc 1 Y).filter (fun m => m.primeFactors ⊆ r.primeFactors), (1:ℝ)/m)
        ≤ ∑ m ∈ (r^Y).divisors, (1:ℝ)/m :=
          Finset.sum_le_sum_of_subset_of_nonneg hsubset hnn
      _ ≤ ∏ p ∈ (r^Y).primeFactors, (1 - (p:ℝ)⁻¹)⁻¹ := sum_divisors_inv_le_euler_product (r^Y)
      _ = ∏ p ∈ r.primeFactors, (1 - (p:ℝ)⁻¹)⁻¹ := by rw [Nat.primeFactors_pow r hY]

/-! ## The main theorem -/

/-- **Lower bound.** For every `R ≥ 1`, `log R ≤ ∑_{r ≤ R} μ(r)²/φ(r)`. -/
theorem log_le_sum_mu_sq_div_totient (R : ℕ) (hR : 1 ≤ R) :
    Real.log (R : ℝ) ≤ ∑ r ∈ Finset.Icc 1 R,
        ((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 / (Nat.totient r : ℝ) := by
  have hlog : Real.log (R : ℝ) ≤ ∑ n ∈ Finset.Icc 1 R, (1:ℝ)/n := by
    have h1 : Real.log (R : ℝ) ≤ Real.log ((R : ℝ) + 1) :=
      Real.log_le_log (by positivity) (by linarith)
    have h2 := log_add_one_le_harmonic R
    rw [harmonic_eq_sum_Icc] at h2
    push_cast at h2
    simp only [one_div] at h2 ⊢
    linarith
  have hsum : (∑ n ∈ Finset.Icc 1 R, (1:ℝ)/n)
      ≤ ∑ r ∈ Finset.Icc 1 R,
          ((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 / (Nat.totient r : ℝ) := by
    rw [sum_inv_eq_reindex R]
    have hzero : ∀ x ∈ Finset.Icc 1 R, x ∉ (Finset.Icc 1 R).filter Squarefree →
        ((ArithmeticFunction.moebius x : ℤ) : ℝ) ^ 2 / (Nat.totient x : ℝ) = 0 := by
      intro x hx hxnot
      rw [Finset.mem_filter] at hxnot
      push Not at hxnot
      have hm : ((ArithmeticFunction.moebius x : ℤ) : ℝ) ^ 2 = 0 := by
        rw [← Int.cast_pow, ArithmeticFunction.moebius_eq_zero_of_not_squarefree (hxnot hx)]
        norm_num
      rw [hm, zero_div]
    have hsum_eq : (∑ r ∈ (Finset.Icc 1 R).filter Squarefree,
          ((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 / (Nat.totient r : ℝ))
        = ∑ r ∈ Finset.Icc 1 R,
          ((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 / (Nat.totient r : ℝ) :=
      Finset.sum_subset (Finset.filter_subset Squarefree (Finset.Icc 1 R)) hzero
    rw [← hsum_eq]
    apply Finset.sum_le_sum
    intro r hr
    rw [Finset.mem_filter, Finset.mem_Icc] at hr
    obtain ⟨⟨hr1, hrR⟩, hsq⟩ := hr
    have hS := smooth_inv_sum_le_totient_ratio r (R/r) hr1
    calc (1/(r:ℝ)) * ∑ m ∈ (Finset.Icc 1 (R/r)).filter
            (fun m => m.primeFactors ⊆ r.primeFactors), (1:ℝ)/m
        ≤ (1/(r:ℝ)) * ((r:ℝ)/(Nat.totient r : ℝ)) :=
          mul_le_mul_of_nonneg_left hS (by positivity)
      _ = 1/(Nat.totient r : ℝ) := by field_simp
      _ = ((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 / (Nat.totient r : ℝ) := by
          have hm : ((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 = 1 := by
            rw [← Int.cast_pow, ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq]
            norm_num
          rw [hm, one_div]
  exact le_trans hlog hsum

end

end Commons.NumberTheory.Totient