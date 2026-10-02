import Mathlib
import Submission.Commons.NumberTheory.Zeta.chebyshev_psi_sub_id_exp
import Submission.Commons.Algebra.BigOperators.abel_full
import Submission.Commons.Analysis.Real.rpow_neg_sub_le

set_option maxHeartbeats 4000000

open scoped BigOperators
open MeasureTheory Set Finset

namespace Work.LinnikAreas

noncomputable section

/-- A continuous function on `[0,∞)` supported in `[0,x₀]` is bounded on `[0,∞)`. -/
private lemma exists_abs_bound_of_contOn_support {x₀ : ℝ} {f : ℝ → ℝ}
    (hcont : ContinuousOn f (Set.Ici 0)) (hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 0 ≤ t → |f t| ≤ K := by
  obtain ⟨K, hK⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc
    (hcont.mono Set.Icc_subset_Ici_self)
  refine ⟨max K 0, le_max_right _ _, fun t ht => ?_⟩
  by_cases h : t ≤ x₀
  · have h1 := hK t ⟨ht, h⟩
    rw [Real.norm_eq_abs] at h1
    exact le_trans h1 (le_max_left _ _)
  · rw [hsupp t (le_of_lt (not_le.mp h)), abs_zero]
    exact le_max_right _ _

/-- For a `C²` function on `(0,x₀)` with second derivative bounded by `B`, the first
derivative is bounded on `(0,x₀)`. -/
private lemma exists_deriv_bound {x₀ B : ℝ} (hx₀ : 0 < x₀) {f : ℝ → ℝ}
    (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Set.Ioo (0:ℝ) x₀, |deriv f t| ≤ K := by
  have ht₀ : x₀/2 ∈ Set.Ioo (0:ℝ) x₀ := ⟨by linarith, by linarith⟩
  have hB : 0 ≤ B := le_trans (norm_nonneg _) (hBnd (x₀/2) ht₀)
  have hderiv2 : ∀ s ∈ Set.Ioo (0:ℝ) x₀, HasDerivAt (deriv f) (iteratedDeriv 2 f s) s := by
    intro s hs
    have hca : ContDiffAt ℝ 2 f s := hf2.contDiffAt (Ioo_mem_nhds hs.1 hs.2)
    have hc1 : ContDiffAt ℝ 1 (deriv f) s := hca.derivWithin (m := 1) (by norm_num)
    have hd : DifferentiableAt ℝ (deriv f) s := hc1.differentiableAt (by norm_num)
    rw [show iteratedDeriv 2 f s = deriv (deriv f) s by
      rw [show (2:ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]]
    exact hd.hasDerivAt
  have hlip : ∀ s ∈ Set.Ioo (0:ℝ) x₀, ∀ t ∈ Set.Ioo (0:ℝ) x₀,
      ‖deriv f t - deriv f s‖ ≤ B * ‖t - s‖ := by
    intro s hs t ht
    exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := deriv f) (f' := iteratedDeriv 2 f) (s := Set.Ioo (0:ℝ) x₀) (C := B)
      (fun x hx => (hderiv2 x hx).hasDerivWithinAt) (fun x hx => hBnd x hx)
      (convex_Ioo 0 x₀) hs ht
  refine ⟨|deriv f (x₀/2)| + B*x₀ + 1, by positivity, fun t ht => ?_⟩
  have h1 := hlip (x₀/2) ht₀ t ht
  have h2 : ‖t - x₀/2‖ ≤ x₀ := by
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [ht.1, ht.2, hx₀]
  have h3 : ‖deriv f t - deriv f (x₀/2)‖ ≤ B * x₀ :=
    le_trans h1 (by nlinarith [hB, h2])
  have h5 : |deriv f t| ≤ |deriv f (x₀/2)| + B*x₀ := by
    have h6 : |deriv f t| = ‖deriv f t‖ := rfl
    rw [h6]
    have h7 : deriv f t = (deriv f t - deriv f (x₀/2)) + deriv f (x₀/2) := by ring
    rw [h7]
    calc ‖(deriv f t - deriv f (x₀/2)) + deriv f (x₀/2)‖
        ≤ ‖deriv f t - deriv f (x₀/2)‖ + ‖deriv f (x₀/2)‖ := norm_add_le _ _
      _ ≤ B*x₀ + |deriv f (x₀/2)| := by
          rw [Real.norm_eq_abs]; exact add_le_add h3 le_rfl
      _ = |deriv f (x₀/2)| + B*x₀ := by ring
  linarith

/-- If `n` and `q` are not coprime, some prime divides both. -/
private lemma exists_prime_dvd_of_not_coprime {n q : ℕ} (h : ¬ Nat.Coprime n q) :
    ∃ p, p.Prime ∧ p ∣ n ∧ p ∣ q := by
  have hg : Nat.gcd n q ≠ 1 := h
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hg
  exact ⟨p, hp, (Nat.dvd_gcd_iff.mp hpdvd).1, (Nat.dvd_gcd_iff.mp hpdvd).2⟩

/-- Weighted version of the non-coprime von Mangoldt sum: the non-coprime integers
carrying von Mangoldt mass are exactly the prime powers `p^k` with `p ∣ q`. -/
private lemma sum_vonMangoldt_not_coprime_weighted (q M : ℕ) (w : ℕ → ℝ) :
    ∑ n ∈ (Finset.Icc 1 M).filter (fun n => ¬ Nat.Coprime n q),
        (ArithmeticFunction.vonMangoldt n) * w n
      = ∑ p ∈ (Finset.Icc 1 M).filter (fun p => p.Prime ∧ p ∣ q),
          ∑ k ∈ Finset.Icc 1 (Nat.log p M), Real.log p * w (p ^ k) := by
  classical
  let P : Finset ℕ := (Finset.Icc 1 M).filter (fun p => p.Prime ∧ p ∣ q)
  let S : Finset ℕ := (Finset.Icc 1 M).filter (fun n => ¬ Nat.Coprime n q)
  let K : ℕ → Finset ℕ := fun p => Finset.Icc 1 (Nat.log p M)
  let Im : ℕ → Finset ℕ := fun p => (K p).image (fun k => p ^ k)
  let U : Finset ℕ := P.biUnion Im
  have hUsub : U ⊆ S := by
    intro n hn
    dsimp only [U, Im, K, P, S] at hn ⊢
    rw [Finset.mem_biUnion] at hn
    obtain ⟨p, hp, hn⟩ := hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hp
    obtain ⟨⟨hp1, hpM⟩, hpprime, hpdvd⟩ := hp
    rw [Finset.mem_image] at hn
    obtain ⟨k, hk, rfl⟩ := hn
    rw [Finset.mem_Icc] at hk
    obtain ⟨hk1, hklog⟩ := hk
    rw [Finset.mem_filter, Finset.mem_Icc]
    have hMpos : M ≠ 0 := by omega
    have hpowle : p ^ k ≤ M := (Nat.le_log_iff_pow_le hpprime.one_lt hMpos).mp hklog
    refine ⟨⟨Nat.one_le_pow k p hpprime.pos, hpowle⟩, ?_⟩
    intro hc
    have hpgcd : p ∣ Nat.gcd (p ^ k) q := Nat.dvd_gcd (dvd_pow_self p (by omega)) hpdvd
    have hpos : 0 < Nat.gcd (p ^ k) q := Nat.gcd_pos_of_pos_left q (pow_pos hpprime.pos k)
    have hle : p ≤ Nat.gcd (p ^ k) q := Nat.le_of_dvd hpos hpgcd
    have : Nat.gcd (p ^ k) q = 1 := hc
    have hp2 : 2 ≤ p := hpprime.two_le
    omega
  have hvan : ∀ n ∈ S, n ∉ U → (ArithmeticFunction.vonMangoldt n) * w n = 0 := by
    intro n hn hnU
    suffices hz : ArithmeticFunction.vonMangoldt n = 0 by rw [hz, zero_mul]
    rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]
    intro hpw
    dsimp only [S] at hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hnM⟩, hncop⟩ := hn
    obtain ⟨p, k, hpprime, hkpos, hpk⟩ := (isPrimePow_nat_iff n).mp hpw
    obtain ⟨r, hrprime, hrn, hrq⟩ := exists_prime_dvd_of_not_coprime hncop
    have hrpk : r ∣ p ^ k := by rw [hpk]; exact hrn
    have hrp : r = p :=
      (Nat.prime_dvd_prime_iff_eq hrprime hpprime).mp (hrprime.dvd_of_dvd_pow hrpk)
    have hpdvdq : p ∣ q := hrp ▸ hrq
    have hpM : p ≤ M := by
      have hle : p ≤ p ^ k := Nat.le_self_pow hkpos.ne' p
      rw [hpk] at hle
      exact hle.trans hnM
    have hpP : p ∈ P := by
      dsimp only [P]
      rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hpprime.one_le, hpM⟩, hpprime, hpdvdq⟩
    have hklog : k ≤ Nat.log p M :=
      Nat.le_log_of_pow_le hpprime.one_lt (by rw [hpk]; exact hnM)
    have : n ∈ U := by
      dsimp only [U, Im, K]
      rw [Finset.mem_biUnion]
      refine ⟨p, hpP, ?_⟩
      rw [Finset.mem_image]
      exact ⟨k, by rw [Finset.mem_Icc]; exact ⟨hkpos, hklog⟩, hpk⟩
    exact hnU this
  have hdisj : (↑P : Set ℕ).PairwiseDisjoint Im := by
    intro p hp q hq hpq
    refine Finset.disjoint_left.mpr ?_
    intro n hnp hnq
    change p ∈ P at hp
    change q ∈ P at hq
    rw [Finset.mem_filter] at hp hq
    have hpprime : p.Prime := hp.2.1
    have hqprime : q.Prime := hq.2.1
    dsimp only [Im, K] at hnp hnq
    rw [Finset.mem_image] at hnp
    rw [Finset.mem_image] at hnq
    obtain ⟨k, hk, hk'⟩ := hnp
    obtain ⟨l, hl, hl'⟩ := hnq
    have hkpos : k ≠ 0 := by have := (Finset.mem_Icc.mp hk).1; omega
    have hlpos : l ≠ 0 := by have := (Finset.mem_Icc.mp hl).1; omega
    have heq : p ^ k = q ^ l := by rw [hk', hl']
    exact hpq (Nat.Prime.pow_inj' hpprime hqprime hkpos hlpos heq).1
  show ∑ n ∈ S, (ArithmeticFunction.vonMangoldt n) * w n
      = ∑ p ∈ P, ∑ k ∈ K p, Real.log p * w (p ^ k)
  calc
    ∑ n ∈ S, (ArithmeticFunction.vonMangoldt n) * w n
        = ∑ n ∈ U, (ArithmeticFunction.vonMangoldt n) * w n :=
          (Finset.sum_subset hUsub hvan).symm
    _ = ∑ p ∈ P, ∑ n ∈ Im p, (ArithmeticFunction.vonMangoldt n) * w n := by
          dsimp only [U]
          exact Finset.sum_biUnion hdisj
    _ = ∑ p ∈ P, ∑ k ∈ K p, (ArithmeticFunction.vonMangoldt (p ^ k)) * w (p ^ k) := by
          refine Finset.sum_congr rfl fun p hp => ?_
          dsimp only [P] at hp
          rw [Finset.mem_filter] at hp
          have hpprime : p.Prime := hp.2.1
          dsimp only [Im]
          rw [Finset.sum_image (g := fun k => p ^ k)
                (fun a _ b _ hab => Nat.pow_right_injective hpprime.two_le hab)]
    _ = ∑ p ∈ P, ∑ k ∈ K p, Real.log p * w (p ^ k) := by
          refine Finset.sum_congr rfl fun p hp => ?_
          dsimp only [P] at hp
          rw [Finset.mem_filter] at hp
          have hpprime : p.Prime := hp.2.1
          refine Finset.sum_congr rfl fun k hk => ?_
          dsimp only [K] at hk
          have hk0 : k ≠ 0 := by have := (Finset.mem_Icc.mp hk).1; omega
          rw [ArithmeticFunction.vonMangoldt_apply_pow hk0,
              ArithmeticFunction.vonMangoldt_apply_prime hpprime]

private lemma cast_pow_rpow_neg (n k : ℕ) (σ : ℝ) :
    (((n^k : ℕ)) : ℝ)^(-σ) = (((n:ℝ))^(-σ))^k := by
  rw [Nat.cast_pow, ← Real.rpow_natCast ((n:ℝ)) k,
      ← Real.rpow_natCast (((n:ℝ))^(-σ)) k]
  rw [← Real.rpow_mul (by positivity : (0:ℝ) ≤ (n:ℝ)) (k:ℝ) (-σ),
      ← Real.rpow_mul (by positivity : (0:ℝ) ≤ (n:ℝ)) (-σ) (k:ℝ)]
  ring_nf

private lemma geom_rpow_bound {p : ℕ} (hp : 2 ≤ p) {σ : ℝ} (hσ : 0 < σ) (K : ℕ) :
    Real.log p * ∑ k ∈ Finset.Icc 1 K, (((p:ℝ))^(-σ))^k ≤ 1/σ := by
  have hp1 : (1:ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  have hp0 : (0:ℝ) < p := by linarith
  have hlogp : 0 < Real.log p := Real.log_pos hp1
  set r : ℝ := (p:ℝ)^(-σ) with hrdef
  have hr0 : 0 < r := Real.rpow_pos_of_pos hp0 _
  have hpow1 : (1:ℝ) < (p:ℝ)^σ := Real.one_lt_rpow hp1 hσ
  have hrn : r = ((p:ℝ)^σ)⁻¹ := by
    rw [hrdef, Real.rpow_neg hp0.le]
  have hr1 : r < 1 := by
    rw [hrn]
    exact inv_lt_one_of_one_lt₀ hpow1
  have h1r : 0 < 1 - r := by linarith
  -- geometric bound
  have hsplit : ∑ k ∈ Finset.Icc 1 K, r^k = r * ∑ i ∈ Finset.range K, r^i := by
    rw [show Finset.Icc 1 K = Finset.Ico 1 (K+1) from by
      ext k; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega]
    rw [Finset.sum_Ico_eq_sum_range]
    rw [show (K+1) - 1 = K from by omega, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [pow_add, pow_one]
  have hgeom : (∑ i ∈ Finset.range K, r^i) * (1 - r) ≤ 1 := by
    rw [geom_sum_mul_neg (x := r) K]
    have hK : (0:ℝ) ≤ r^K := by positivity
    linarith
  have hstep1 : ∑ k ∈ Finset.Icc 1 K, r^k ≤ r/(1-r) := by
    rw [hsplit, le_div_iff₀ h1r]
    have h2 : r * ((∑ i ∈ Finset.range K, r^i) * (1 - r)) ≤ r * 1 :=
      mul_le_mul_of_nonneg_left hgeom hr0.le
    linarith
  have hid : r/(1-r) = 1/((p:ℝ)^σ - 1) := by
    rw [hrn]
    have h : (p:ℝ)^σ ≠ 0 := (Real.rpow_pos_of_pos hp0 σ).ne'
    field_simp
  have hkey : σ * Real.log p ≤ (p:ℝ)^σ - 1 := by
    have h := Real.add_one_le_exp (σ * Real.log p)
    rw [Real.rpow_def_of_pos hp0]
    rw [mul_comm (Real.log ((p:ℝ))) σ]
    linarith
  have hfin : Real.log p / ((p:ℝ)^σ - 1) ≤ 1/σ := by
    rw [div_le_div_iff₀ (by linarith : (0:ℝ) < (p:ℝ)^σ - 1) hσ]
    linarith
  calc Real.log p * ∑ k ∈ Finset.Icc 1 K, (((p:ℝ))^(-σ))^k
      ≤ Real.log p * (r/(1-r)) := by
        refine mul_le_mul_of_nonneg_left ?_ hlogp.le
        simpa only [hrdef] using hstep1
    _ = Real.log p / ((p:ℝ)^σ - 1) := by rw [hid]; ring
    _ ≤ 1/σ := hfin

/-- The von Mangoldt sum over the integers that are not coprime to `q`, weighted by
`n^{-σ}`, is bounded by `ω(q)/σ`. -/
private lemma bad_sum_bound {q M : ℕ} (hq : 0 < q) {σ : ℝ} (hσ : 0 < σ) :
    ∑ n ∈ (Finset.Icc 1 M).filter (fun n => ¬ Nat.Coprime n q),
        (ArithmeticFunction.vonMangoldt n) * (n:ℝ)^(-σ)
      ≤ (q.primeFactors.card : ℝ) / σ := by
  rw [sum_vonMangoldt_not_coprime_weighted]
  set P : Finset ℕ := (Finset.Icc 1 M).filter (fun p => p.Prime ∧ p ∣ q) with hPdef
  have hinner : ∀ p ∈ P, ∑ k ∈ Finset.Icc 1 (Nat.log p M),
      Real.log p * (((p^k : ℕ)) : ℝ)^(-σ) ≤ 1/σ := by
    intro p hp
    rw [hPdef, Finset.mem_filter, Finset.mem_Icc] at hp
    obtain ⟨⟨hp1, hpM⟩, hpprime, hpdvd⟩ := hp
    have hp2 : 2 ≤ p := hpprime.two_le
    have hcongr : ∑ k ∈ Finset.Icc 1 (Nat.log p M),
        Real.log p * (((p^k : ℕ)) : ℝ)^(-σ)
      = Real.log p * ∑ k ∈ Finset.Icc 1 (Nat.log p M), (((p:ℝ))^(-σ))^k := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      rw [cast_pow_rpow_neg]
    rw [hcongr]
    exact geom_rpow_bound hp2 hσ _
  calc ∑ p ∈ P, ∑ k ∈ Finset.Icc 1 (Nat.log p M), Real.log p * (((p^k : ℕ)) : ℝ)^(-σ)
      ≤ ∑ p ∈ P, (1/σ : ℝ) := Finset.sum_le_sum hinner
    _ = (P.card : ℝ) * (1/σ) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (q.primeFactors.card : ℝ) / σ := by
        have hsub : P ⊆ q.primeFactors := by
          intro p hp
          rw [hPdef, Finset.mem_filter] at hp
          obtain ⟨-, hpprime, hpdvd⟩ := hp
          rw [Nat.mem_primeFactors]
          exact ⟨hpprime, hpdvd, hq.ne'⟩
        have hcard : (P.card : ℝ) ≤ (q.primeFactors.card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
        have : (P.card : ℝ) * (1/σ) = (P.card : ℝ) / σ := by ring
        rw [this]
        exact div_le_div_of_nonneg_right hcard hσ.le

/-- Auxiliary function whose derivatives control the smoothed von Mangoldt sum. -/
private abbrev gfun (L : ℝ) (s : ℂ) (f : ℝ → ℝ) (t : ℝ) : ℂ :=
  Complex.exp (-s * ((Real.log t : ℝ) : ℂ)) * ((f (Real.log t / L) : ℝ) : ℂ)

private abbrev gd (L : ℝ) (s : ℂ) (f : ℝ → ℝ) (x : ℝ) : ℂ :=
  Complex.exp (-s * ((Real.log x : ℝ) : ℂ)) * (-s * ((x:ℂ)⁻¹)) * ((f (Real.log x / L) : ℝ) : ℂ)
    + Complex.exp (-s * ((Real.log x : ℝ) : ℂ)) *
        (((deriv f (Real.log x / L) : ℝ) : ℂ) * (((L:ℂ) * (x:ℂ))⁻¹))

private lemma hasDerivAt_exp_log (s : ℂ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun t : ℝ => Complex.exp (-s * ((Real.log t : ℝ) : ℂ)))
      (Complex.exp (-s * ((Real.log x : ℝ) : ℂ)) * (-s * ((x:ℂ)⁻¹))) x := by
  have h1 : HasDerivAt (fun t : ℝ => ((Real.log t : ℝ) : ℂ)) (((x:ℝ)⁻¹ : ℝ) : ℂ) x :=
    (Real.hasDerivAt_log hx).ofReal_comp
  have h2 : HasDerivAt (fun t : ℝ => -s * ((Real.log t : ℝ) : ℂ)) (-s * (((x:ℝ)⁻¹ : ℝ) : ℂ)) x :=
    h1.const_mul (-s)
  have h3 := h2.cexp
  rw [Complex.ofReal_inv] at h3
  exact h3

private lemma hasDerivAt_f_log_div {x₀ L : ℝ} {f : ℝ → ℝ} (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    {x : ℝ} (hx : x ≠ 0) (hxu : Real.log x / L ∈ Set.Ioo (0:ℝ) x₀) :
    HasDerivAt (fun t : ℝ => ((f (Real.log t / L) : ℝ) : ℂ))
      (((deriv f (Real.log x / L) : ℝ) : ℂ) * (((L:ℂ) * (x:ℂ))⁻¹)) x := by
  have h1 : HasDerivAt (fun t : ℝ => Real.log t / L) ((x:ℝ)⁻¹ / L) x :=
    (Real.hasDerivAt_log hx).div_const L
  have h2 : HasDerivAt f (deriv f (Real.log x / L)) (Real.log x / L) :=
    (hf2.differentiableOn (by norm_num)).differentiableAt (Ioo_mem_nhds hxu.1 hxu.2) |>.hasDerivAt
  have h3 := h2.comp x h1
  have h4 := h3.ofReal_comp
  convert h4 using 1
  · ext t; rfl
  · have hkey : (((x:ℝ)⁻¹ / L : ℝ) : ℂ) = ((L:ℂ) * (x:ℂ))⁻¹ := by
      rw [Complex.ofReal_div, Complex.ofReal_inv, div_eq_mul_inv, mul_inv_rev]
    rw [Complex.ofReal_mul, hkey]

private lemma continuousOn_exp_log (s : ℂ) {a b : ℝ} (hab : 0 < a) :
    ContinuousOn (fun t : ℝ => Complex.exp (-s * ((Real.log t : ℝ) : ℂ))) (Set.Icc a b) := by
  have h1 : ContinuousOn (fun t : ℝ => ((Real.log t : ℝ) : ℂ)) (Set.Icc a b) :=
    Complex.continuous_ofReal.comp_continuousOn
      ((Real.continuousOn_log.mono) (fun x hx => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact ne_of_gt (lt_of_lt_of_le hab hx.1)))
  exact ((h1.const_mul (-s)).cexp)

private lemma continuousOn_gfun {x₀ L b : ℝ} (hx₀ : 0 < x₀) (hL : 0 < L) {f : ℝ → ℝ}
    (hcont : ContinuousOn f (Set.Ici 0)) (s : ℂ) (hb1 : 1 ≤ b) (hbe : b ≤ Real.exp (L*x₀)) :
    ContinuousOn (gfun L s f) (Set.Icc 1 b) := by
  have h1 : ContinuousOn (fun t : ℝ => Real.log t / L) (Set.Icc 1 b) :=
    ((Real.continuousOn_log.mono) (fun x hx => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ne_of_gt (lt_of_lt_of_le zero_lt_one hx.1))).div_const L
  have hmap : MapsTo (fun t : ℝ => Real.log t / L) (Set.Icc 1 b) (Set.Icc 0 x₀) := by
    intro t ht
    have ht1 : (1:ℝ) ≤ t := ht.1
    have htb : t ≤ b := ht.2
    have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht1
    constructor
    · exact div_nonneg (Real.log_nonneg ht1) hL.le
    · rw [div_le_iff₀ hL]
      have h2 : Real.log t ≤ L*x₀ := by
        rw [← Real.log_exp (L*x₀)]
        exact Real.log_le_log htpos (le_trans htb hbe)
      linarith
  have h2 : ContinuousOn (fun t : ℝ => f (Real.log t / L)) (Set.Icc 1 b) :=
    (hcont.mono Set.Icc_subset_Ici_self).comp h1 hmap
  have h3 : ContinuousOn (fun t : ℝ => ((f (Real.log t / L) : ℝ) : ℂ)) (Set.Icc 1 b) :=
    Complex.continuous_ofReal.comp_continuousOn h2
  have h4 := (continuousOn_exp_log s (a := 1) (b := b) zero_lt_one).mul h3
  convert h4 using 1
  all_goals (ext t; simp [gfun, Pi.mul_apply])

private lemma hasDerivAt_gfun {x₀ L : ℝ} {f : ℝ → ℝ} (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    {s : ℂ} {x : ℝ} (hx : x ≠ 0) (hxu : Real.log x / L ∈ Set.Ioo (0:ℝ) x₀) :
    HasDerivAt (gfun L s f) (gd L s f x) x := by
  have h3 := (hasDerivAt_exp_log s hx).mul (hasDerivAt_f_log_div hf2 hx hxu)
  convert h3 using 1
  all_goals first | rfl | (funext t; rfl)

/-- Pointwise bound for the derivative of `gfun`. -/
private lemma norm_gd_le {L Kf Kd : ℝ} {f : ℝ → ℝ} {s : ℂ} {x : ℝ}
    (hL : 0 < L) (hx1 : 1 ≤ x) (hσ : 0 ≤ s.re)
    (hKf : |f (Real.log x / L)| ≤ Kf) (hKd : |deriv f (Real.log x / L)| ≤ Kd) :
    ‖gd L s f x‖ ≤ (‖s‖ * Kf + Kd / L) / x := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hKf0 : 0 ≤ Kf := le_trans (abs_nonneg _) hKf
  have hKd0 : 0 ≤ Kd := le_trans (abs_nonneg _) hKd
  have hxnn : (0:ℝ) ≤ x := le_trans zero_le_one hx1
  have hxinvpos : 0 < x⁻¹ := inv_pos.mpr hxpos
  have hexp : ‖Complex.exp (-s * ((Real.log x : ℝ) : ℂ))‖ = x ^ (-s.re) := by
    rw [Complex.norm_exp]
    have h1 : (-s * ((Real.log x : ℝ) : ℂ)).re = -s.re * Real.log x := by
      simp [Complex.mul_re]
    rw [h1, Real.rpow_def_of_pos hxpos]
    ring_nf
  have hxs : x ^ (-s.re) ≤ 1 := by
    have h := Real.rpow_le_rpow_of_exponent_le hx1 (show -s.re ≤ (0:ℝ) by linarith)
    simpa using h
  have hF : ‖((f (Real.log x / L) : ℝ) : ℂ)‖ = |f (Real.log x / L)| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  have hD : ‖((deriv f (Real.log x / L) : ℝ) : ℂ)‖ = |deriv f (Real.log x / L)| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  have hxinv : ‖((x:ℂ))⁻¹‖ = x⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hxnn]
  have hLxinv : ‖(((L:ℂ) * (x:ℂ))⁻¹)‖ = (L*x)⁻¹ := by
    rw [norm_inv, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hL.le, abs_of_nonneg hxnn]
  have hsn : ‖-s * ((x:ℂ)⁻¹)‖ = ‖s‖ * x⁻¹ := by
    rw [norm_mul, norm_neg, hxinv]
  have h1 : ‖Complex.exp (-s * ((Real.log x : ℝ) : ℂ)) * (-s * ((x:ℂ)⁻¹)) *
      ((f (Real.log x / L) : ℝ) : ℂ)‖ ≤ ‖s‖ * Kf * x⁻¹ := by
    rw [norm_mul, norm_mul, hexp, hsn, hF]
    calc x ^ (-s.re) * (‖s‖ * x⁻¹) * |f (Real.log x / L)|
        ≤ 1 * (‖s‖ * x⁻¹) * Kf := by gcongr
      _ = ‖s‖ * Kf * x⁻¹ := by ring
  have h2 : ‖Complex.exp (-s * ((Real.log x : ℝ) : ℂ)) *
      (((deriv f (Real.log x / L) : ℝ) : ℂ) * (((L:ℂ) * (x:ℂ))⁻¹))‖ ≤ Kd * (L*x)⁻¹ := by
    rw [norm_mul, hexp, norm_mul, hD, hLxinv]
    calc x ^ (-s.re) * (|deriv f (Real.log x / L)| * (L*x)⁻¹)
        ≤ 1 * (Kd * (L*x)⁻¹) := by gcongr
      _ = Kd * (L*x)⁻¹ := by ring
  rw [gd]
  refine le_trans (norm_add_le _ _) ?_
  have h5 : ‖s‖ * Kf * x⁻¹ + Kd * (L*x)⁻¹ = (‖s‖ * Kf + Kd / L) / x := by
    rw [div_eq_mul_inv]; ring
  linarith [h1, h2, h5]

/-- The derivative of `gfun` is integrable on `[1,M]`. -/
private lemma integrableOn_deriv_gfun {x₀ L Kf Kd : ℝ} {M : ℕ} (hx₀ : 0 < x₀)
    (hL : 1 < L) (hM1 : 1 ≤ M) (hMe : (M:ℝ) ≤ Real.exp (L*x₀))
    {f : ℝ → ℝ} (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀)) {s : ℂ} (hσ : 0 ≤ s.re)
    (hKf : ∀ t, 0 ≤ t → |f t| ≤ Kf) (hKd : ∀ t ∈ Set.Ioo 0 x₀, |deriv f t| ≤ Kd) :
    MeasureTheory.IntegrableOn (deriv (gfun L s f)) (Set.uIcc 1 (M:ℝ)) volume := by
  have hLpos : (0:ℝ) < L := by linarith
  have hM1' : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM1
  have hpt : ∀ x ∈ Set.Ioo (1:ℝ) (M:ℝ), deriv (gfun L s f) x = gd L s f x := by
    intro x hx
    have hxpos : 0 < x := by linarith [hx.1]
    have hlogpos : 0 < Real.log x / L := div_pos (Real.log_pos hx.1) hLpos
    have hloglt : Real.log x / L < x₀ := by
      rw [div_lt_iff₀ hLpos]
      have h2 : Real.log x < L * x₀ := by
        rw [← Real.log_exp (L*x₀)]
        exact Real.log_lt_log hxpos (lt_of_lt_of_le hx.2 hMe)
      linarith
    exact (hasDerivAt_gfun hf2 (ne_of_gt hxpos) ⟨hlogpos, hloglt⟩).deriv
  have hbound : ∀ x ∈ Set.Ioo (1:ℝ) (M:ℝ), ‖deriv (gfun L s f) x‖ ≤ (‖s‖*Kf + Kd/L) := by
    intro x hx
    rw [hpt x hx]
    have hx1 : (1:ℝ) ≤ x := le_of_lt hx.1
    have hKfx : |f (Real.log x / L)| ≤ Kf :=
      hKf _ (div_nonneg (Real.log_nonneg hx1) hLpos.le)
    have hlogmem : Real.log x / L ∈ Set.Ioo (0:ℝ) x₀ := by
      refine ⟨div_pos (Real.log_pos hx.1) hLpos, ?_⟩
      rw [div_lt_iff₀ hLpos]
      have h2 : Real.log x < L * x₀ := by
        rw [← Real.log_exp (L*x₀)]
        exact Real.log_lt_log (by linarith) (lt_of_lt_of_le hx.2 hMe)
      linarith
    have hKdx : |deriv f (Real.log x / L)| ≤ Kd := hKd _ hlogmem
    have h1 := norm_gd_le (L := L) (Kf := Kf) (Kd := Kd) (f := f) (s := s) (x := x)
      hLpos hx1 hσ hKfx hKdx
    have h3 : 0 ≤ ‖s‖*Kf + Kd/L := by
      have h4 : 0 ≤ Kf := le_trans (abs_nonneg _) (hKf 0 le_rfl)
      have h5 : 0 ≤ Kd := le_trans (abs_nonneg _) (hKd (x₀/2) ⟨by linarith, by linarith⟩)
      positivity
    have h2 : (‖s‖*Kf + Kd/L)/x ≤ ‖s‖*Kf + Kd/L := by
      rw [div_le_iff₀ (by linarith : (0:ℝ) < x)]
      nlinarith [hx.1, h3]
    linarith
  have hfin : volume (Set.uIcc (1:ℝ) (M:ℝ)) < ⊤ := by
    rw [Set.uIcc_of_le hM1', Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have h0 : MeasureTheory.IntegrableOn (deriv (gfun L s f)) (Set.uIcc 1 (M:ℝ)) volume := by
    refine MeasureTheory.IntegrableOn.of_bound (f := deriv (gfun L s f)) hfin ?_
      (‖s‖*Kf + Kd/L) ?_
    · exact (measurable_deriv (gfun L s f)).aestronglyMeasurable
    · rw [MeasureTheory.ae_restrict_iff' measurableSet_uIcc, MeasureTheory.ae_iff]
      apply MeasureTheory.measure_mono_null (t := {x : ℝ | x = 1 ∨ x = (M:ℝ)}) _ ?_
      · intro x hx
        simp only [Set.mem_setOf_eq, Set.uIcc_of_le hM1', Classical.not_imp] at hx
        by_contra hcon
        simp only [Set.mem_setOf_eq, not_or] at hcon
        exact hx.2 (hbound x ⟨lt_of_le_of_ne hx.1.1 (Ne.symm hcon.1),
          lt_of_le_of_ne hx.1.2 hcon.2⟩)
      · rw [Set.setOf_or]
        exact measure_union_null (measure_singleton 1) (measure_singleton _)
  exact h0

private lemma psi_eq_of_mem_Ico {n : ℕ} {t : ℝ} (ht : t ∈ Set.Ico (n:ℝ) ((n:ℝ)+1)) :
    Chebyshev.psi t = Chebyshev.psi (n:ℝ) := by
  rw [Chebyshev.psi_eq_sum_Icc, Chebyshev.psi_eq_sum_Icc]
  have hfloor : ⌊t⌋₊ = n := by
    rw [Nat.floor_eq_iff (by linarith [ht.1] : (0:ℝ) ≤ t)]
    exact ⟨by exact_mod_cast ht.1, ht.2⟩
  rw [hfloor, Nat.floor_natCast]

private lemma psi_nat_eq_sum_Icc1 (n : ℕ) :
    Chebyshev.psi (n:ℝ) = ∑ m ∈ Finset.Icc 1 n, (ArithmeticFunction.vonMangoldt m) := by
  rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · rw [show Finset.Icc 0 n = insert 0 (Finset.Icc 1 n) from by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega,
      Finset.sum_insert (by simp)]
    simp

/-- Change of variables: `∫₁^{e^{Lx₀}} gfun = L∫₀^{x₀} e^{-(s-1)Lt} f(t) dt`. -/
private lemma integral_gfun_eq_main {x₀ L : ℝ} (hx₀ : 0 < x₀) (hL : 0 < L)
    {f : ℝ → ℝ} (hcont : ContinuousOn f (Set.Ici 0)) (s : ℂ) :
    (∫ t in (1:ℝ)..Real.exp (L*x₀), gfun L s f t)
      = (L:ℂ) * (∫ t in (0:ℝ)..x₀, Complex.exp (-(((s-1) * L : ℂ) * (t:ℂ))) * ((f t : ℝ):ℂ)) := by
  have hLne : L ≠ 0 := ne_of_gt hL
  have hderiv : ∀ u ∈ Set.uIcc (0:ℝ) x₀,
      HasDerivAt (fun u : ℝ => Real.exp (L*u)) (L * Real.exp (L*u)) u := by
    intro u _
    exact ((Real.hasDerivAt_exp (L*u)).comp u ((hasDerivAt_id u).const_mul L)).congr_deriv (by ring)
  have hcont' : ContinuousOn (fun u : ℝ => L * Real.exp (L*u)) (Set.uIcc 0 x₀) :=
    (continuous_const.mul (Real.continuous_exp.comp (continuous_id.const_mul L))).continuousOn
  have himg : Set.image (fun u : ℝ => Real.exp (L*u)) (Set.uIcc 0 x₀)
      ⊆ Set.Icc 1 (Real.exp (L*x₀)) := by
    rintro y ⟨u, hu, rfl⟩
    rw [Set.uIcc_of_le hx₀.le] at hu
    refine ⟨?_, ?_⟩
    · rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by nlinarith [hu.1, hL])
    · exact Real.exp_le_exp.mpr (by nlinarith [hu.2, hL])
  have hg : ContinuousOn (gfun L s f) (Set.image (fun u : ℝ => Real.exp (L*u)) (Set.uIcc 0 x₀)) :=
    (continuousOn_gfun hx₀ hL hcont s (by rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by positivity))
      le_rfl).mono himg
  have hsub := intervalIntegral.integral_deriv_smul_comp'
    (f := fun u : ℝ => Real.exp (L*u)) (f' := fun u : ℝ => L * Real.exp (L*u))
    (g := gfun L s f) (a := (0:ℝ)) (b := x₀) hderiv hcont' hg
  simp only [mul_zero, Real.exp_zero] at hsub
  rw [← hsub]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro u _
  have hpt : (L * Real.exp (L*u)) • gfun L s f (Real.exp (L*u))
      = (L:ℂ) * (Complex.exp (-(((s-1) * L : ℂ) * (u:ℂ))) * ((f u : ℝ):ℂ)) := by
    have hlog : Real.log (Real.exp (L*u)) = L*u := Real.log_exp _
    have hdiv : L*u/L = u := by field_simp
    simp only [gfun, hlog, hdiv]
    rw [RCLike.real_smul_eq_coe_mul]
    calc (↑(L * Real.exp (L * u)) : ℂ) * (Complex.exp (-s * ((L*u:ℝ):ℂ)) * ((f u : ℝ):ℂ))
        = (↑L * Complex.exp ((L*u:ℝ):ℂ)) * (Complex.exp (-s * ((L*u:ℝ):ℂ)) * ((f u : ℝ):ℂ)) := by
          rw [Complex.ofReal_mul, Complex.ofReal_exp]
      _ = ↑L * (Complex.exp (((L*u:ℝ):ℂ) + (-s * ((L*u:ℝ):ℂ)))) * ((f u : ℝ):ℂ) := by
          rw [Complex.exp_add]; ring
      _ = ↑L * (Complex.exp (-(((s-1) * L : ℂ) * (u:ℂ))) * ((f u : ℝ):ℂ)) := by
          rw [show ((L*u:ℝ):ℂ) + (-s * ((L*u:ℝ):ℂ)) = -(((s-1) * L : ℂ) * (u:ℂ)) by
            push_cast; ring]
          ring
  exact hpt

private lemma intervalIntegrable_deriv_gfun {x₀ L Kf Kd : ℝ} {M : ℕ} (hx₀ : 0 < x₀)
    (hL : 1 < L) (hM1 : 1 ≤ M) (hMe : (M:ℝ) ≤ Real.exp (L*x₀))
    {f : ℝ → ℝ} (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀)) {s : ℂ} (hσ : 0 ≤ s.re)
    (hKf : ∀ t, 0 ≤ t → |f t| ≤ Kf) (hKd : ∀ t ∈ Set.Ioo 0 x₀, |deriv f t| ≤ Kd) :
    IntervalIntegrable (deriv (gfun L s f)) volume 1 (M:ℝ) := by
  have hM1' : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM1
  rw [intervalIntegrable_iff]
  refine (integrableOn_deriv_gfun hx₀ hL hM1 hMe hf2 hσ hKf hKd).mono_set ?_
  rw [Set.uIoc_of_le hM1', Set.uIcc_of_le hM1']
  exact Set.Ioc_subset_Icc_self

/-- The `ψ`-weighted derivative of `gfun` is interval integrable. -/
private lemma intervalIntegrable_psi_deriv {x₀ L Kf Kd : ℝ} {M : ℕ} (hx₀ : 0 < x₀)
    (hL : 1 < L) (hM1 : 1 ≤ M) (hMe : (M:ℝ) ≤ Real.exp (L*x₀))
    {f : ℝ → ℝ} (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀)) {s : ℂ} (hσ : 0 ≤ s.re)
    (hKf : ∀ t, 0 ≤ t → |f t| ≤ Kf) (hKd : ∀ t ∈ Set.Ioo 0 x₀, |deriv f t| ≤ Kd) :
    IntervalIntegrable (fun t => (Chebyshev.psi t : ℂ) * deriv (gfun L s f) t) volume 1 (M:ℝ) := by
  have hM1' : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM1
  have h0 := integrableOn_deriv_gfun hx₀ hL hM1 hMe hf2 hσ hKf hKd
  have hmeas : AEStronglyMeasurable (fun t : ℝ => ((Chebyshev.psi t : ℝ) : ℂ))
      (volume.restrict (Set.uIcc (1:ℝ) (M:ℝ))) :=
    (Complex.continuous_ofReal.measurable.comp Chebyshev.psi_mono.measurable).aestronglyMeasurable
  have hbdd : ∀ᵐ t ∂(volume.restrict (Set.uIcc (1:ℝ) (M:ℝ))),
      ‖((Chebyshev.psi t : ℝ) : ℂ)‖ ≤ (Real.log 4 + 4) * (M:ℝ) := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_uIcc]
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    rw [Set.uIcc_of_le hM1'] at ht
    have ht0 : 0 ≤ t := le_trans zero_le_one ht.1
    have h1 : Chebyshev.psi t ≤ (Real.log 4 + 4) * t := Chebyshev.psi_le_const_mul_self ht0
    have h2 : 0 ≤ Chebyshev.psi t := Chebyshev.psi_nonneg t
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h2]
    calc Chebyshev.psi t ≤ (Real.log 4 + 4) * t := h1
      _ ≤ (Real.log 4 + 4) * (M:ℝ) := mul_le_mul_of_nonneg_left ht.2 (by positivity)
  have h := MeasureTheory.Integrable.mul_bdd (μ := volume.restrict (Set.uIcc (1:ℝ) (M:ℝ)))
    (f := deriv (gfun L s f)) (g := fun t : ℝ => ((Chebyshev.psi t : ℝ) : ℂ))
    (c := (Real.log 4 + 4) * (M:ℝ)) h0 hmeas hbdd
  have hsub : Set.uIoc (1:ℝ) (M:ℝ) ⊆ Set.uIcc (1:ℝ) (M:ℝ) := by
    rw [Set.uIoc_of_le hM1', Set.uIcc_of_le hM1']
    exact Set.Ioc_subset_Icc_self
  have hres : MeasureTheory.IntegrableOn
      (fun t : ℝ => deriv (gfun L s f) t * ((Chebyshev.psi t : ℝ):ℂ)) (Set.uIoc (1:ℝ) (M:ℝ)) volume :=
    MeasureTheory.IntegrableOn.mono_set h hsub
  rw [intervalIntegrable_iff]
  rw [show (fun t : ℝ => (Chebyshev.psi t : ℂ) * deriv (gfun L s f) t)
      = fun t : ℝ => deriv (gfun L s f) t * (Chebyshev.psi t : ℂ) from by
        funext t; ring]
  exact hres

/-- On `[n,n+1]`, `ψ` is the constant `ψ(n)`, so `∫ ψ·g' = ψ(n)·(g(n+1)-g(n))`. -/
private lemma integral_psi_deriv_interval {x₀ L Kf Kd : ℝ} {M n : ℕ} (hx₀ : 0 < x₀)
    (hL : 1 < L) (hn1 : 1 ≤ n) (hnM : n + 1 ≤ M) (hMe : (M:ℝ) ≤ Real.exp (L*x₀))
    {f : ℝ → ℝ} (hcont : ContinuousOn f (Set.Ici 0)) (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    {s : ℂ} (hσ : 0 ≤ s.re) (hKf : ∀ t, 0 ≤ t → |f t| ≤ Kf)
    (hKd : ∀ t ∈ Set.Ioo 0 x₀, |deriv f t| ≤ Kd) :
    (∫ t in (n:ℝ)..((n:ℝ)+1), (Chebyshev.psi t : ℂ) * deriv (gfun L s f) t)
      = (Chebyshev.psi (n:ℝ) : ℂ) * (gfun L s f ((n:ℝ)+1) - gfun L s f (n:ℝ)) := by
  have hLpos : (0:ℝ) < L := by linarith
  have hM1 : 1 ≤ M := by omega
  have hn1' : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
  have hnM' : (n:ℝ)+1 ≤ (M:ℝ) := by exact_mod_cast hnM
  have hMe' : (M:ℝ) ≤ Real.exp (L*x₀) := hMe
  have hIcc_sub : Set.uIcc (n:ℝ) ((n:ℝ)+1) ⊆ Set.uIcc (1:ℝ) (M:ℝ) := by
    rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith : (1:ℝ) ≤ (M:ℝ))]
    exact Set.Icc_subset_Icc hn1' hnM'
  have hcontg : ContinuousOn (gfun L s f) (Set.uIcc (n:ℝ) ((n:ℝ)+1)) := by
    refine (continuousOn_gfun hx₀ hLpos hcont s (by
      rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by positivity)) le_rfl).mono ?_
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    exact ⟨le_trans hn1' hx.1, le_trans hx.2 (le_trans hnM' hMe')⟩
  have hdiff : ∀ x ∈ Set.uIoo (n:ℝ) ((n:ℝ)+1), DifferentiableAt ℝ (gfun L s f) x := by
    intro x hx
    rw [Set.uIoo_of_le (by linarith)] at hx
    have hxgt1 : (1:ℝ) < x := lt_of_le_of_lt hn1' hx.1
    have hxpos : 0 < x := by linarith
    have hlogpos : 0 < Real.log x / L := div_pos (Real.log_pos hxgt1) hLpos
    have hloglt : Real.log x / L < x₀ := by
      rw [div_lt_iff₀ hLpos]
      have h2 : Real.log x < L*x₀ := by
        rw [← Real.log_exp (L*x₀)]
        exact Real.log_lt_log hxpos (lt_of_lt_of_le (lt_of_lt_of_le hx.2 hnM') hMe')
      linarith
    exact (hasDerivAt_gfun hf2 (ne_of_gt hxpos) ⟨hlogpos, hloglt⟩).differentiableAt
  have hint : IntervalIntegrable (deriv (gfun L s f)) volume (n:ℝ) ((n:ℝ)+1) := by
    rw [intervalIntegrable_iff]
    refine (integrableOn_deriv_gfun hx₀ hL hM1 hMe hf2 hσ hKf hKd).mono_set ?_
    rw [Set.uIoc_of_le (by linarith), Set.uIcc_of_le (by exact_mod_cast hM1)]
    intro x hx
    rw [Set.mem_Ioc] at hx
    exact ⟨le_trans hn1' (le_of_lt hx.1), le_trans hx.2 hnM'⟩

  have hFTC := intervalIntegral.integral_deriv_eq_sub_uIoo hcontg hdiff hint
  have hae : ∀ᵐ x ∂volume, x ∈ Set.uIoc (n:ℝ) ((n:ℝ)+1) →
      (Chebyshev.psi x : ℂ) * deriv (gfun L s f) x
        = (Chebyshev.psi (n:ℝ) : ℂ) * deriv (gfun L s f) x := by
    have hne : ∀ᵐ x ∂volume, x ≠ (n:ℝ)+1 := by
      rw [MeasureTheory.ae_iff]
      have h0 : volume {x : ℝ | ¬x ≠ (n:ℝ)+1} = 0 := by
        rw [show {x : ℝ | ¬x ≠ (n:ℝ)+1} = {((n:ℝ)+1)} from by ext x; simp]
        exact measure_singleton _
      exact h0
    refine hne.mono (fun x hne hx => ?_)
    rw [Set.uIoc_of_le (by linarith), Set.mem_Ioc] at hx
    have hlt : x < (n:ℝ)+1 := lt_of_le_of_ne hx.2 hne
    rw [psi_eq_of_mem_Ico ⟨le_of_lt hx.1, hlt⟩]
  rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_const_mul, hFTC]

/-- `∫₁^M ψ·g'` as the discrete Abel sum. -/
private lemma integral_psi_deriv_eq_sum {x₀ L Kf Kd : ℝ} {M : ℕ} (hx₀ : 0 < x₀) (hL : 1 < L)
    (hM1 : 1 ≤ M) (hMe : (M:ℝ) ≤ Real.exp (L*x₀))
    {f : ℝ → ℝ} (hcont : ContinuousOn f (Set.Ici 0)) (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    {s : ℂ} (hσ : 0 ≤ s.re) (hKf : ∀ t, 0 ≤ t → |f t| ≤ Kf)
    (hKd : ∀ t ∈ Set.Ioo 0 x₀, |deriv f t| ≤ Kd) :
    (∫ t in (1:ℝ)..(M:ℝ), (Chebyshev.psi t : ℂ) * deriv (gfun L s f) t)
      = ∑ n ∈ Finset.Icc 1 (M-1),
          (Chebyshev.psi (n:ℝ) : ℂ) * (gfun L s f ((n:ℝ)+1) - gfun L s f (n:ℝ)) := by
  have hM1' : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM1
  have hpsi := intervalIntegrable_psi_deriv hx₀ hL hM1 hMe hf2 hσ hKf hKd
  have hsub : ∀ k : ℕ, k < M - 1 →
      Set.uIcc ((k:ℝ)+1) ((((k+1:ℕ)):ℝ)+1) ⊆ Set.uIcc (1:ℝ) (M:ℝ) := by
    intro k hk
    have hk' : k + 2 ≤ M := by omega
    have hk2 : ((k:ℝ) + 2 : ℝ) ≤ (M:ℝ) := by exact_mod_cast hk'
    have hcast : ((((k+1:ℕ)):ℝ)+1) = (k:ℝ) + 2 := by
      rw [Nat.cast_add, Nat.cast_one]; ring
    have hle : ((k:ℝ)+1) ≤ ((((k+1:ℕ)):ℝ)+1) := by rw [hcast]; linarith
    intro x hx
    rw [Set.uIcc_of_le hM1']
    rw [Set.uIcc_of_le hle] at hx
    refine ⟨le_trans (by linarith : (1:ℝ) ≤ (k:ℝ)+1) hx.1, ?_⟩
    calc x ≤ (((k+1:ℕ)):ℝ) + 1 := hx.2
      _ = (k:ℝ)+2 := hcast
      _ ≤ (M:ℝ) := hk2
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun k : ℕ => (k:ℝ)+1)
    (f := fun t : ℝ => (Chebyshev.psi t : ℂ) * deriv (gfun L s f) t) (n := M-1)
    (fun k hk => hpsi.mono_set (hsub k hk))
  have hsum' : ∑ k ∈ Finset.range (M-1),
        ∫ t in (((k:ℝ)+1))..((((k+1:ℕ)):ℝ)+1), (Chebyshev.psi t : ℂ) * deriv (gfun L s f) t
      = ∫ t in (1:ℝ)..(M:ℝ), (Chebyshev.psi t : ℂ) * deriv (gfun L s f) t := by
    have h := hsum
    simp only [Nat.cast_zero, zero_add] at h
    rw [show ((M-1:ℕ):ℝ)+1 = (M:ℝ) from by rw [Nat.cast_sub hM1]; ring] at h
    exact h
  rw [show Finset.Icc 1 (M-1) = Finset.Ico 1 M from by
    ext k; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega]
  rw [Finset.sum_Ico_eq_sum_range]
  rw [← hsum']
  apply Finset.sum_congr rfl
  intro k hk
  have hk1 : k < M - 1 := Finset.mem_range.mp hk
  have hk' : k + 2 ≤ M := by omega
  clear hk1
  have hkey := integral_psi_deriv_interval (n := k+1) hx₀ hL (by omega) (by omega) hMe
    hcont hf2 hσ hKf hKd
  convert hkey using 2 <;> (push_cast; ring)

/-- Abel summation: the full von Mangoldt sum in terms of `ψ` and the weighted integral. -/
private lemma sum_full_eq {x₀ L Kf Kd : ℝ} {M : ℕ} (hx₀ : 0 < x₀) (hL : 1 < L)
    (hM1 : 1 ≤ M) (hMe : (M:ℝ) ≤ Real.exp (L*x₀))
    {f : ℝ → ℝ} (hcont : ContinuousOn f (Set.Ici 0)) (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    {s : ℂ} (hσ : 0 ≤ s.re) (hKf : ∀ t, 0 ≤ t → |f t| ≤ Kf)
    (hKd : ∀ t ∈ Set.Ioo 0 x₀, |deriv f t| ≤ Kd) :
    (∑ n ∈ Finset.Icc 1 M, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * gfun L s f (n:ℝ))
      = (Chebyshev.psi (M:ℝ) : ℂ) * gfun L s f (M:ℝ)
        - ∫ t in (1:ℝ)..(M:ℝ), (Chebyshev.psi t : ℂ) * deriv (gfun L s f) t := by
  have hpsi_sum : ∀ n : ℕ, (∑ m ∈ Finset.Icc 1 n, ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ))
      = (Chebyshev.psi (n:ℝ) : ℂ) := by
    intro n
    rw [psi_nat_eq_sum_Icc1 n]
    push_cast
    rfl
  have habel := Commons.Algebra.BigOperators.abel_full
    (a := fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
    (w := fun n : ℕ => gfun L s f (n:ℝ)) M
  rw [habel, hpsi_sum]
  simp only [show (∑ m ∈ Finset.Icc 1 0, ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ)) = 0 from by simp,
    zero_mul, sub_zero]
  simp only [hpsi_sum]
  rw [integral_psi_deriv_eq_sum hx₀ hL hM1 hMe hcont hf2 hσ hKf hKd]
  have hFG : (∑ x ∈ Finset.Icc 1 (M-1),
        (Chebyshev.psi (x:ℝ) : ℂ) * (gfun L s f (x:ℝ) - gfun L s f (((x+1:ℕ)):ℝ)))
      = - ∑ n ∈ Finset.Icc 1 (M-1),
        (Chebyshev.psi (n:ℝ) : ℂ) * (gfun L s f ((n:ℝ)+1) - gfun L s f (n:ℝ)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    push_cast
    ring
  rw [hFG]
  ring

private lemma psi_range_sum (k : ℕ) :
    (∑ i ∈ Finset.range k, (ArithmeticFunction.vonMangoldt i : ℝ)) = Chebyshev.psi ((k:ℝ) - 1) := by
  rcases Nat.eq_zero_or_pos k with h | h
  · subst h
    rw [Finset.range_zero, Finset.sum_empty]
    have h1 : ((0:ℕ):ℝ) - 1 = (-1:ℝ) := by norm_num
    rw [h1, Chebyshev.psi_eq_zero_of_lt_two (by norm_num : (-1:ℝ) < 2)]
  · have hcast : ((k:ℝ) - 1) = ((k - 1 : ℕ) : ℝ) := by rw [Nat.cast_sub h]; ring
    rw [hcast, Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
    congr 1
    ext n; simp only [Finset.mem_range, Finset.mem_Icc]; omega

/-- Abel summation identity for `∑ Λ(n) n^{-σ}`. -/
private lemma sum_vonMangoldt_mul_rpow_neg_eq {N : ℕ} (hN : 1 ≤ N) {σ : ℝ} :
    (∑ i ∈ Finset.Icc 1 N, (i:ℝ)^(-σ) * (ArithmeticFunction.vonMangoldt i : ℝ))
      = Chebyshev.psi (N:ℝ) * (N:ℝ)^(-σ)
        + ∑ i ∈ Finset.Ico 1 N,
            (((i:ℝ)^(-σ) - (((i:ℝ)+1))^(-σ)) * Chebyshev.psi (i:ℝ)) := by
  have h := Finset.sum_Ico_by_parts (R := ℝ) (M := ℝ)
    (f := fun i : ℕ => (i:ℝ)^(-σ)) (g := fun i : ℕ => (ArithmeticFunction.vonMangoldt i : ℝ))
    (m := 1) (n := N+1) (by omega)
  simp only [smul_eq_mul] at h
  rw [show Finset.Ico 1 (N+1) = Finset.Icc 1 N from by
        ext n; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega,
      show (N+1) - 1 = N from by omega] at h
  simp only [psi_range_sum, Nat.cast_add, Nat.cast_one] at h
  simp only [add_sub_cancel_right, sub_self] at h
  rw [Chebyshev.psi_eq_zero_of_lt_two (by norm_num : (0:ℝ) < 2), mul_zero, sub_zero] at h
  have hcongr' : (∑ i ∈ Finset.Ico 1 N,
        (((((i:ℝ)+1))^(-σ) - (i:ℝ)^(-σ)) * Chebyshev.psi (i:ℝ)))
      = - ∑ i ∈ Finset.Ico 1 N,
          (((i:ℝ)^(-σ) - (((i:ℝ)+1))^(-σ)) * Chebyshev.psi (i:ℝ)) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun i hi => by ring)
  rw [h, hcongr']
  ring

/-- `∑_{n ≤ N} n^{-σ} ≤ 1 + ∫₁^N t^{-σ} dt`. -/
private lemma sum_Icc_rpow_neg_le {σ : ℝ} (hσ : 0 < σ) {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, (n:ℝ)^(-σ) ≤ 1 + ∫ t in (1:ℝ)..(N:ℝ), t^(-σ) := by
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hcast : (1:ℝ) + ((N-1:ℕ):ℝ) = (N:ℝ) := by rw [Nat.cast_sub hN]; ring
  have hanti : AntitoneOn (fun t : ℝ => t^(-σ)) (Set.Icc 1 (1 + ((N-1:ℕ):ℝ))) := by
    intro x hx y hy hxy
    have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx.1
    exact Real.rpow_le_rpow_of_nonpos hx0 hxy (by linarith)
  have hsum := hanti.sum_le_integral
  rw [hcast] at hsum
  rw [show Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) from by
        ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; omega,
      Finset.sum_insert (by simp), Nat.cast_one, Real.one_rpow]
  have hkey : (∑ i ∈ Finset.range (N-1), ((1:ℝ) + (((i+1:ℕ)):ℝ))^(-σ))
      = ∑ n ∈ Finset.Icc 2 N, (n:ℝ)^(-σ) := by
    rw [show Finset.Icc 2 N = (Finset.range (N-1)).image (fun i : ℕ => i+2) from by
      ext n; simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
      constructor
      · intro h; exact ⟨n-2, by omega, by omega⟩
      · rintro ⟨i, hi, rfl⟩; omega,
      Finset.sum_image (fun a _ b _ hab => by omega)]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    push_cast
    ring_nf
  rw [hkey] at hsum
  linarith

/-- Continuity of `t ↦ t^{-σ}` on a positive interval. -/
private lemma continuousOn_rpow_neg {σ a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ContinuousOn (fun t : ℝ => t^(-σ)) (Set.uIcc a b) := by
  refine ContinuousOn.rpow continuousOn_id continuousOn_const (fun x hx => Or.inl ?_)
  rw [Set.uIcc_of_le hab] at hx
  exact ne_of_gt (lt_of_lt_of_le ha hx.1)

/-- `exp x ≤ 1 + 3x` on `[0,1]`. -/
private lemma exp_le_one_add_three {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp x ≤ 1 + 3 * x := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := Real.exp) (f' := fun t => Real.exp t) (s := Set.Icc (0:ℝ) 1) (C := 3)
    (fun t ht => (Real.hasDerivAt_exp t).hasDerivWithinAt)
    (fun t ht => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos t)]
      calc Real.exp t ≤ Real.exp 1 := Real.exp_le_exp.mpr ht.2
        _ ≤ 3 := Real.exp_one_lt_three.le)
    (convex_Icc 0 1) ⟨hx0, hx1⟩ ⟨le_rfl, zero_le_one⟩
  have h' : |Real.exp x - 1| ≤ 3 * |x| := by
    have h2 := h
    rw [Real.exp_zero, Real.norm_eq_abs, Real.norm_eq_abs, zero_sub] at h2
    rw [abs_sub_comm] at h2
    rwa [abs_neg] at h2
  have hge : 0 ≤ Real.exp x - 1 := by
    have := Real.one_le_exp hx0
    linarith
  rw [abs_of_nonneg hge, abs_of_nonneg hx0] at h'
  linarith

/-- `∫₁^N t^{-σ} dt ≤ 1 + 2 log N` when `(1-σ) log N ≤ 1`. -/
private lemma integral_rpow_neg_le {σ N : ℝ} (hσ : 0 < σ) (h1 : 1 ≤ N)
    (hcond : (1 - σ) * Real.log N ≤ 1) :
    ∫ t in (1:ℝ)..N, t^(-σ) ≤ 4 * (1 + Real.log N) := by
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg h1
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one h1
  have hmain : ∫ t in (1:ℝ)..N, t^(-σ) ≤ ∫ t in (1:ℝ)..N, Real.exp 1 * t^(-1:ℝ) := by
    refine intervalIntegral.integral_mono_on h1 ?_ ?_ ?_
    · exact (continuousOn_rpow_neg (σ := σ) zero_lt_one h1).intervalIntegrable
    · exact (ContinuousOn.const_mul (continuousOn_rpow_neg (σ := 1) zero_lt_one h1) (Real.exp 1)).intervalIntegrable
    · intro x hx
      rw [Set.mem_Icc] at hx
      have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx.1
      have h2 : x^(1-σ) ≤ Real.exp 1 := by
        by_cases h : 1 ≤ σ
        · calc x^(1-σ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx.1 (by linarith)
            _ ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
        · push_neg at h
          calc x^(1-σ) ≤ N^(1-σ) := Real.rpow_le_rpow hx0.le hx.2 (by linarith)
            _ = Real.exp ((1-σ)*Real.log N) := by rw [Real.rpow_def_of_pos hNpos, mul_comm]
            _ ≤ Real.exp 1 := Real.exp_le_exp.mpr hcond
      calc x^(-σ) = x^(-1:ℝ) * x^(1-σ) := by
            rw [← Real.rpow_add hx0]; ring_nf
        _ ≤ x^(-1:ℝ) * Real.exp 1 := mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hx0.le _)
        _ = Real.exp 1 * x^(-1:ℝ) := by ring
  have h2 : ∫ t in (1:ℝ)..N, Real.exp 1 * t^(-1:ℝ) = Real.exp 1 * Real.log N := by
    rw [intervalIntegral.integral_const_mul]
    congr 1
    rw [show (fun t : ℝ => t^(-1:ℝ)) = fun t : ℝ => 1/t from by
      funext t; rw [Real.rpow_neg_one, one_div]]
    rw [integral_one_div (by
      rw [Set.uIcc_of_le h1]
      intro hmem
      exact absurd hmem.1 (by norm_num : ¬ ((1:ℝ) ≤ 0)))]
    rw [div_one]
  rw [h2] at hmain
  have hexp3 : Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
  nlinarith [hmain, hexp3, hlogN]

/-- `∑_{n ≤ N} Λ(n) n^{-σ} ≤ 100 (log 4 + 5) (1 + log N)` under `(1-σ) log N ≤ 1`. -/
private lemma sum_vonMangoldt_mul_rpow_neg_le {σ : ℝ} (hσ : 0 < σ) (hσ2 : σ ≤ 2)
    {N : ℕ} (hN : 1 ≤ N) (hcond : (1 - σ) * Real.log (N:ℝ) ≤ 1) :
    (∑ i ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt i : ℝ) * (i:ℝ)^(-σ))
      ≤ 200 * (Real.log 4 + 5) * (1 + Real.log (N:ℝ)) := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hlogN : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg hN1
  have hNpow : (N:ℝ)^(1-σ) ≤ 3 := by
    by_cases h : 1 ≤ σ
    · calc (N:ℝ)^(1-σ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
        _ ≤ 3 := by norm_num
    · push_neg at h
      calc (N:ℝ)^(1-σ) = Real.exp ((1-σ)*Real.log (N:ℝ)) := by
            rw [Real.rpow_def_of_pos hNpos, mul_comm]
        _ ≤ Real.exp 1 := Real.exp_le_exp.mpr hcond
        _ ≤ 3 := Real.exp_one_lt_three.le
  have hfirst : Chebyshev.psi (N:ℝ) * (N:ℝ)^(-σ) ≤ (Real.log 4 + 5) * 3 := by
    have hψ := Chebyshev.psi_le_const_mul_self hNpos.le
    have hmul : (N:ℝ) * (N:ℝ)^(-σ) = (N:ℝ)^(1-σ) := by
      have h1 : (N:ℝ)^(1:ℝ) * (N:ℝ)^(-σ) = (N:ℝ)^((1:ℝ) + (-σ)) :=
        (Real.rpow_add hNpos 1 (-σ)).symm
      rw [Real.rpow_one] at h1
      rw [h1]; ring_nf
    have hnonneg : 0 ≤ (N:ℝ)^(-σ) := Real.rpow_nonneg hNpos.le _
    have h1 : Chebyshev.psi (N:ℝ) * (N:ℝ)^(-σ) ≤ ((Real.log 4 + 4) * (N:ℝ)) * (N:ℝ)^(-σ) :=
      mul_le_mul_of_nonneg_right hψ hnonneg
    have h2 : ((Real.log 4 + 4) * (N:ℝ)) * (N:ℝ)^(-σ) = (Real.log 4 + 4) * (N:ℝ)^(1-σ) := by
      rw [mul_assoc, hmul]
    rw [h2] at h1
    nlinarith [h1, hNpow, Real.log_pos (by norm_num : (1:ℝ) < 4)]
  have hterm : ∀ i ∈ Finset.Ico 1 N,
      (((i:ℝ)^(-σ) - (((i:ℝ)+1))^(-σ)) * Chebyshev.psi (i:ℝ))
        ≤ (Real.log 4 + 5) * σ * (i:ℝ)^(-σ) := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    have hi1 : (1:ℝ) ≤ i := by exact_mod_cast hi.1
    have hipos : (0:ℝ) < i := lt_of_lt_of_le zero_lt_one hi1
    have hb := Commons.Analysis.Real.rpow_neg_sub_le hσ hi.1
    have hpsi := Chebyshev.psi_le_const_mul_self hipos.le
    have hpsi0 : 0 ≤ Chebyshev.psi (i:ℝ) := Chebyshev.psi_nonneg _
    have hrw : (i:ℝ)^(-σ-1) * (i:ℝ) = (i:ℝ)^(-σ) := by
      have h1 : (i:ℝ)^(-σ-1) * (i:ℝ)^(1:ℝ) = (i:ℝ)^((-σ-1) + 1) :=
        (Real.rpow_add hipos (-σ-1) 1).symm
      rw [Real.rpow_one] at h1
      rw [h1]; ring_nf
    calc ((i:ℝ)^(-σ) - (((i:ℝ)+1))^(-σ)) * Chebyshev.psi (i:ℝ)
        ≤ (σ * (i:ℝ)^(-σ-1)) * ((Real.log 4 + 4) * (i:ℝ)) :=
          mul_le_mul hb hpsi hpsi0 (by positivity)
      _ = (Real.log 4 + 4) * σ * ((i:ℝ)^(-σ-1) * (i:ℝ)) := by ring
      _ = (Real.log 4 + 4) * σ * (i:ℝ)^(-σ) := by rw [hrw]
      _ ≤ (Real.log 4 + 5) * σ * (i:ℝ)^(-σ) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hipos.le _)
          nlinarith [hσ]
  have hsumbound : (∑ i ∈ Finset.Ico 1 N,
        (((i:ℝ)^(-σ) - (((i:ℝ)+1))^(-σ)) * Chebyshev.psi (i:ℝ)))
      ≤ (Real.log 4 + 5) * σ * (∑ i ∈ Finset.Ico 1 N, (i:ℝ)^(-σ)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  have hIco : (∑ i ∈ Finset.Ico 1 N, (i:ℝ)^(-σ)) ≤ 8 * (1 + Real.log (N:ℝ)) := by
    have h1 : (∑ i ∈ Finset.Ico 1 N, (i:ℝ)^(-σ)) ≤ ∑ n ∈ Finset.Icc 1 N, (n:ℝ)^(-σ) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro x hx; rw [Finset.mem_Ico] at hx; rw [Finset.mem_Icc]; omega
      · intro x hx1 hx2; exact Real.rpow_nonneg (by positivity) _
    have h2 := sum_Icc_rpow_neg_le hσ hN
    have h3 := integral_rpow_neg_le hσ hN1 hcond
    linarith
  have hsum := sum_vonMangoldt_mul_rpow_neg_eq (σ := σ) hN
  have hcomm : (∑ i ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt i : ℝ) * (i:ℝ)^(-σ))
      = ∑ i ∈ Finset.Icc 1 N, (i:ℝ)^(-σ) * (ArithmeticFunction.vonMangoldt i : ℝ) :=
    Finset.sum_congr rfl (fun i hi => mul_comm _ _)
  rw [hcomm, hsum]
  have hC2 : 0 < Real.log 4 + 5 := by
    have : 0 < Real.log 4 := Real.log_pos (by norm_num)
    linarith
  have hfin1 : Chebyshev.psi (N:ℝ) * (N:ℝ)^(-σ) ≤ (Real.log 4 + 5) * 3 * (1 + Real.log (N:ℝ)) := by
    nlinarith [hfirst, hlogN, hC2]
  have hfin2 : (Real.log 4 + 5) * σ * (∑ i ∈ Finset.Ico 1 N, (i:ℝ)^(-σ))
      ≤ (Real.log 4 + 5) * 2 * (8 * (1 + Real.log (N:ℝ))) := by
    have hSnn : 0 ≤ ∑ i ∈ Finset.Ico 1 N, (i:ℝ)^(-σ) :=
      Finset.sum_nonneg (fun i hi => Real.rpow_nonneg (by positivity) _)
    calc (Real.log 4 + 5) * σ * (∑ i ∈ Finset.Ico 1 N, (i:ℝ)^(-σ))
        ≤ (Real.log 4 + 5) * σ * (8 * (1 + Real.log (N:ℝ))) :=
          mul_le_mul_of_nonneg_left hIco (by positivity)
      _ ≤ (Real.log 4 + 5) * 2 * (8 * (1 + Real.log (N:ℝ))) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hσ2 hC2.le
  have h1 : (∑ i ∈ Finset.Ico 1 N,
        (((i:ℝ)^(-σ) - (((i:ℝ)+1))^(-σ)) * Chebyshev.psi (i:ℝ)))
      ≤ (Real.log 4 + 5) * 2 * (8 * (1 + Real.log (N:ℝ))) := le_trans hsumbound hfin2
  have h2 : (Real.log 4 + 5) * 3 + (Real.log 4 + 5) * 2 * (8 * (1 + Real.log (N:ℝ)))
      ≤ 200 * (Real.log 4 + 5) * (1 + Real.log (N:ℝ)) := by
    nlinarith [hC2, hlogN]
  linarith [hfin1, h1, h2]

/-- Integration by parts: `∫ₘⁿ t·g' = n·g(n) - m·g(m) - ∫ₘⁿ g`. -/
private lemma integral_id_deriv_interval {x₀ L Kf Kd : ℝ} {f : ℝ → ℝ} {s : ℂ} {m n : ℕ}
    (hx₀ : 0 < x₀) (hL : 1 < L) (hm1 : 1 ≤ m) (hmn : m ≤ n)
    (hne : (n:ℝ) ≤ Real.exp (L*x₀))
    (hcont : ContinuousOn f (Set.Ici 0)) (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    (hσ : 0 ≤ s.re) (hKf : ∀ t, 0 ≤ t → |f t| ≤ Kf)
    (hKd : ∀ t ∈ Set.Ioo 0 x₀, |deriv f t| ≤ Kd) :
    (∫ t in (m:ℝ)..(n:ℝ), (t:ℂ) * deriv (gfun L s f) t)
      = (((n:ℝ):ℂ)) * gfun L s f n - (((m:ℝ):ℂ)) * gfun L s f m
        - ∫ t in (m:ℝ)..(n:ℝ), gfun L s f t := by
  have hLpos : (0:ℝ) < L := by linarith
  have hm1' : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm1
  have hmn' : (m:ℝ) ≤ (n:ℝ) := by exact_mod_cast hmn
  have hn1' : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hder := integrableOn_deriv_gfun (M := n) hx₀ hL (by omega : 1 ≤ n) hne hf2 hσ hKf hKd
  have hderInt : IntervalIntegrable (deriv (gfun L s f)) volume (m:ℝ) (n:ℝ) := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hmn']
    refine hder.mono_set (fun x hx => ?_)
    rw [Set.uIcc_of_le hn1']
    simp only [Set.uIoc_of_le hmn', Set.mem_Ioc] at hx
    exact ⟨le_trans hm1' (le_of_lt hx.1), hx.2⟩
  have hbase : ContinuousOn (gfun L s f) (Set.Icc (1:ℝ) (Real.exp (L*x₀))) :=
    continuousOn_gfun hx₀ hLpos hcont s (by
      rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by positivity)) le_rfl
  have hcontg : ContinuousOn (gfun L s f) (Set.uIcc (m:ℝ) (n:ℝ)) := by
    refine hbase.mono ?_
    intro x hx
    rw [Set.uIcc_of_le hmn'] at hx
    exact ⟨le_trans hm1' hx.1, le_trans hx.2 hne⟩
  have hcontu : ContinuousOn (fun t : ℝ => (t:ℂ)) (Set.uIcc (m:ℝ) (n:ℝ)) := by fun_prop
  have hderiv_u : ∀ x ∈ Set.Ioo (min (m:ℝ) (n:ℝ)) (max (m:ℝ) (n:ℝ)),
      HasDerivWithinAt (fun t : ℝ => (t:ℂ)) 1 (Set.Ioi x) x :=
    fun x _ => ((hasDerivAt_id x).ofReal_comp).hasDerivWithinAt
  have hderiv_g : ∀ x ∈ Set.Ioo (min (m:ℝ) (n:ℝ)) (max (m:ℝ) (n:ℝ)),
      HasDerivWithinAt (gfun L s f) (deriv (gfun L s f) x) (Set.Ioi x) x := by
    intro x hx
    rw [min_eq_left hmn', max_eq_right hmn'] at hx
    have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one (le_trans hm1' (le_of_lt hx.1))
    have hxgt1 : (1:ℝ) < x := lt_of_le_of_lt hm1' hx.1
    have hlogpos : 0 < Real.log x / L := div_pos (Real.log_pos hxgt1) hLpos
    have hloglt : Real.log x / L < x₀ := by
      rw [div_lt_iff₀ hLpos]
      have h2 : Real.log x < L * x₀ := by
        rw [← Real.log_exp (L*x₀)]
        exact Real.log_lt_log hxpos (lt_of_lt_of_le hx.2 hne)
      linarith
    have hh := hasDerivAt_gfun (s := s) hf2 (ne_of_gt hxpos) ⟨hlogpos, hloglt⟩
    rw [hh.deriv]
    exact hh.hasDerivWithinAt
  have h1int : IntervalIntegrable (fun _ : ℝ => (1:ℂ)) volume (m:ℝ) (n:ℝ) := intervalIntegrable_const
  have hIBP := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDeriv_right
    (u := fun t : ℝ => (t:ℂ)) (v := gfun L s f) (u' := fun _ => (1:ℂ))
    (v' := fun t => deriv (gfun L s f) t) (a := (m:ℝ)) (b := (n:ℝ))
    hcontu hcontg hderiv_u hderiv_g h1int hderInt
  have hgInt : IntervalIntegrable (gfun L s f) volume (m:ℝ) (n:ℝ) := hcontg.intervalIntegrable
  have htderivInt : IntervalIntegrable (fun t : ℝ => (t:ℂ) * deriv (gfun L s f) t) volume (m:ℝ) (n:ℝ) :=
    hderInt.continuousOn_mul hcontu
  have hsplit : (∫ t in (m:ℝ)..(n:ℝ), (1:ℂ) * gfun L s f t + (t:ℂ) * deriv (gfun L s f) t)
      = (∫ t in (m:ℝ)..(n:ℝ), gfun L s f t)
        + ∫ t in (m:ℝ)..(n:ℝ), (t:ℂ) * deriv (gfun L s f) t := by
    rw [intervalIntegral.integral_add (hgInt.continuousOn_mul (continuous_const.continuousOn)) htderivInt]
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    simp
  rw [hsplit] at hIBP
  rw [← hIBP]
  ring

/-- Sharp pointwise bound for the derivative of `gfun`. -/
private lemma norm_gd_le_shift {L Kf Kd : ℝ} {f : ℝ → ℝ} {s : ℂ} {x : ℝ}
    (hL : 0 < L) (hx1 : 1 ≤ x)
    (hKf : |f (Real.log x / L)| ≤ Kf) (hKd : |deriv f (Real.log x / L)| ≤ Kd) :
    ‖gd L s f x‖ ≤ (‖s‖ * Kf + Kd / L) * x^(-s.re-1) := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hxnn : (0:ℝ) ≤ x := le_trans zero_le_one hx1
  have hKf0 : 0 ≤ Kf := le_trans (abs_nonneg _) hKf
  have hKd0 : 0 ≤ Kd := le_trans (abs_nonneg _) hKd
  have hexp : ‖Complex.exp (-s * ((Real.log x : ℝ) : ℂ))‖ = x ^ (-s.re) := by
    rw [Complex.norm_exp]
    have h1 : (-s * ((Real.log x : ℝ) : ℂ)).re = -s.re * Real.log x := by
      simp [Complex.mul_re]
    rw [h1, Real.rpow_def_of_pos hxpos]
    ring_nf
  have hF : ‖((f (Real.log x / L) : ℝ) : ℂ)‖ = |f (Real.log x / L)| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  have hD : ‖((deriv f (Real.log x / L) : ℝ) : ℂ)‖ = |deriv f (Real.log x / L)| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  have hxinv : ‖((x:ℂ))⁻¹‖ = x⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hxnn]
  have hLxinv : ‖(((L:ℂ) * (x:ℂ))⁻¹)‖ = (L*x)⁻¹ := by
    rw [norm_inv, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hL.le, abs_of_nonneg hxnn]
  have hsn : ‖-s * ((x:ℂ)⁻¹)‖ = ‖s‖ * x⁻¹ := by
    rw [norm_mul, norm_neg, hxinv]
  have h1 : ‖Complex.exp (-s * ((Real.log x : ℝ) : ℂ)) * (-s * ((x:ℂ)⁻¹)) *
      ((f (Real.log x / L) : ℝ) : ℂ)‖ ≤ x ^ (-s.re) * (‖s‖ * x⁻¹) * Kf := by
    rw [norm_mul, norm_mul, hexp, hsn, hF]
    exact mul_le_mul_of_nonneg_left hKf (by positivity)
  have h2 : ‖Complex.exp (-s * ((Real.log x : ℝ) : ℂ)) *
      (((deriv f (Real.log x / L) : ℝ) : ℂ) * (((L:ℂ) * (x:ℂ))⁻¹))‖
      ≤ x ^ (-s.re) * Kd * (L*x)⁻¹ := by
    rw [norm_mul, hexp, norm_mul, hD, hLxinv]
    have h1 : |deriv f (Real.log x / L)| * (L*x)⁻¹ ≤ Kd * (L*x)⁻¹ :=
      mul_le_mul_of_nonneg_right hKd (by positivity)
    calc x ^ (-s.re) * (|deriv f (Real.log x / L)| * (L*x)⁻¹)
        ≤ x ^ (-s.re) * (Kd * (L*x)⁻¹) := mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hxnn _)
      _ = x ^ (-s.re) * Kd * (L*x)⁻¹ := by ring
  rw [gd]
  refine le_trans (norm_add_le _ _) ?_
  have h5 : x ^ (-s.re) * (‖s‖ * x⁻¹) * Kf + x ^ (-s.re) * Kd * (L*x)⁻¹
      = (‖s‖ * Kf + Kd / L) * x^(-s.re-1) := by
    have hrw : x^(-s.re-1) = x^(-s.re) * x^(-1:ℝ) := by
      rw [← Real.rpow_add hxpos]
      ring_nf
    rw [hrw, Real.rpow_neg_one]
    field_simp
  linarith [h1, h2, h5]

/-- Bound for `∫ₘⁿ (ψ(t)-t)·g'(t)`: if `|ψ(t)-t|·t^{-σ} ≤ Cc·L^{-2}` on `[m,n]`,
then the integral is `≤ Cc L^{-2} (‖s‖Kf + Kd) L x₀`. -/
private lemma norm_integral_R_le {x₀ L Kf Kd Cc : ℝ} {f : ℝ → ℝ} {s : ℂ} {m n : ℕ}
    (hx₀ : 0 < x₀) (hL : 1 < L) (hm1 : 1 ≤ m) (hmn : m ≤ n)
    (hne : (n:ℝ) ≤ Real.exp (L*x₀))
    (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀)) (hKf : ∀ t, 0 ≤ t → |f t| ≤ Kf)
    (hKd : ∀ t ∈ Set.Ioo 0 x₀, |deriv f t| ≤ Kd)
    (hCc : 0 ≤ Cc) (hLpos : 0 < L)
    (hR : ∀ t ∈ Set.Icc (m:ℝ) (n:ℝ), |Chebyshev.psi t - t| * t^(-s.re) ≤ Cc * L^(-2:ℝ)) :
    ‖∫ t in (m:ℝ)..(n:ℝ), (((Chebyshev.psi t - t : ℝ)) : ℂ) * deriv (gfun L s f) t‖
      ≤ Cc * L^(-2:ℝ) * (‖s‖ * Kf + Kd) * (L * x₀) := by
  have hm1' : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm1
  have hmn' : (m:ℝ) ≤ (n:ℝ) := by exact_mod_cast hmn
  have hKf0 : 0 ≤ Kf := le_trans (abs_nonneg _) (hKf 0 le_rfl)
  have hKd0 : 0 ≤ Kd := le_trans (abs_nonneg _) (hKd (x₀/2) ⟨by linarith, by linarith⟩)
  have hKg : 0 ≤ ‖s‖ * Kf + Kd / L := by
    have h3 : 0 ≤ Kd / L := div_nonneg hKd0 hLpos.le
    have h4 : 0 ≤ ‖s‖ * Kf := mul_nonneg (norm_nonneg _) hKf0
    linarith
  have hKg2 : 0 ≤ ‖s‖ * Kf + Kd := by
    have h4 : 0 ≤ ‖s‖ * Kf := mul_nonneg (norm_nonneg _) hKf0
    linarith
  have hne_ae : ∀ᵐ t ∂volume, t ≠ Real.exp (L*x₀) := by
    rw [MeasureTheory.ae_iff]
    have h0 : volume {t : ℝ | ¬t ≠ Real.exp (L*x₀)} = 0 := by
      rw [show {t : ℝ | ¬t ≠ Real.exp (L*x₀)} = {Real.exp (L*x₀)} from by ext t; simp]
      exact measure_singleton _
    exact h0
  have hpt : ∀ᵐ t ∂volume, t ∈ Set.Ioc (m:ℝ) (n:ℝ) →
      ‖(((Chebyshev.psi t - t : ℝ)) : ℂ) * deriv (gfun L s f) t‖
        ≤ Cc * L^(-2:ℝ) * (‖s‖ * Kf + Kd / L) * t^(-1:ℝ) := by
    refine hne_ae.mono (fun t hte ht => ?_)
    rw [Set.mem_Ioc] at ht
    have ht1 : (1:ℝ) ≤ t := le_trans hm1' (le_of_lt ht.1)
    have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht1
    have hmem : t ∈ Set.Icc (m:ℝ) (n:ℝ) := ⟨le_of_lt ht.1, ht.2⟩
    have htlt : t < Real.exp (L*x₀) := lt_of_le_of_ne (le_trans ht.2 hne) hte
    have hlogmem : Real.log t / L ∈ Set.Ioo (0:ℝ) x₀ := by
      refine ⟨div_pos (Real.log_pos (lt_of_le_of_lt hm1' ht.1)) hLpos, ?_⟩
      rw [div_lt_iff₀ hLpos]
      have h2 : Real.log t < L * x₀ := by
        rw [← Real.log_exp (L*x₀)]
        exact Real.log_lt_log htpos htlt
      linarith
    have hder : deriv (gfun L s f) t = gd L s f t :=
      (hasDerivAt_gfun (s := s) hf2 (ne_of_gt htpos) hlogmem).deriv
    have hd := norm_gd_le_shift (L := L) (Kf := Kf) (Kd := Kd) (f := f) (s := s) (x := t)
      hLpos ht1 (hKf _ (div_nonneg (Real.log_nonneg ht1) hLpos.le)) (hKd _ hlogmem)
    rw [hder, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 : |Chebyshev.psi t - t| * ‖gd L s f t‖
        ≤ |Chebyshev.psi t - t| * ((‖s‖ * Kf + Kd / L) * t^(-s.re-1)) :=
      mul_le_mul_of_nonneg_left hd (abs_nonneg _)
    have h2 : |Chebyshev.psi t - t| * ((‖s‖ * Kf + Kd / L) * t^(-s.re-1))
        = (‖s‖ * Kf + Kd / L) * t^(-1:ℝ) * (|Chebyshev.psi t - t| * t^(-s.re)) := by
      rw [show t^(-s.re-1) = t^(-s.re) * t^(-1:ℝ) from by
        rw [← Real.rpow_add htpos]; ring_nf]
      ring
    rw [h2] at h1
    have h3 : |Chebyshev.psi t - t| * t^(-s.re) ≤ Cc * L^(-2:ℝ) := hR t hmem
    calc |Chebyshev.psi t - t| * ‖gd L s f t‖
        ≤ (‖s‖ * Kf + Kd / L) * t^(-1:ℝ) * (|Chebyshev.psi t - t| * t^(-s.re)) := h1
      _ ≤ (‖s‖ * Kf + Kd / L) * t^(-1:ℝ) * (Cc * L^(-2:ℝ)) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = Cc * L^(-2:ℝ) * (‖s‖ * Kf + Kd / L) * t^(-1:ℝ) := by ring
  have hCont : ContinuousOn (fun t : ℝ => Cc * L^(-2:ℝ) * (‖s‖ * Kf + Kd / L) * t^(-1:ℝ))
      (Set.uIcc (m:ℝ) (n:ℝ)) :=
    ContinuousOn.const_mul
      (continuousOn_rpow_neg (σ := 1) (by exact_mod_cast (by omega : 0 < m)) hmn')
      (Cc * L^(-2:ℝ) * (‖s‖ * Kf + Kd / L))
  have hbound := intervalIntegral.norm_integral_le_of_norm_le hmn' hpt hCont.intervalIntegrable
  have hInt : ∫ t in (m:ℝ)..(n:ℝ), Cc * L^(-2:ℝ) * (‖s‖ * Kf + Kd / L) * t^(-1:ℝ)
      = Cc * L^(-2:ℝ) * (‖s‖ * Kf + Kd / L) * Real.log ((n:ℝ)/(m:ℝ)) := by
    rw [intervalIntegral.integral_const_mul]
    congr 1
    rw [show (fun t : ℝ => t^(-1:ℝ)) = fun t : ℝ => 1/t from by
      funext t; rw [Real.rpow_neg_one, one_div]]
    rw [integral_one_div (by
      rw [Set.uIcc_of_le hmn']
      intro hmem
      exact absurd hmem.1 (not_le.mpr (lt_of_lt_of_le zero_lt_one hm1')))]
  rw [hInt] at hbound
  have hlog : Real.log ((n:ℝ)/(m:ℝ)) ≤ L * x₀ := by
    have h1 : (n:ℝ)/(m:ℝ) ≤ Real.exp (L*x₀) := by
      rw [div_le_iff₀ (lt_of_lt_of_le zero_lt_one hm1')]
      nlinarith [hne, hm1']
    have h2 : 0 < (n:ℝ)/(m:ℝ) := by
      apply div_pos
      · exact lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hm1') hmn'
      · linarith
    calc Real.log ((n:ℝ)/(m:ℝ)) ≤ Real.log (Real.exp (L*x₀)) := Real.log_le_log h2 h1
      _ = L * x₀ := Real.log_exp _
  have hlog0 : 0 ≤ Real.log ((n:ℝ)/(m:ℝ)) := Real.log_nonneg (by
    rw [le_div_iff₀ (lt_of_lt_of_le zero_lt_one hm1')]
    simpa using hmn')
  have hKg3 : ‖s‖ * Kf + Kd / L ≤ ‖s‖ * Kf + Kd := by
    have h1 : Kd / L ≤ Kd := by
      rw [div_le_iff₀ hLpos]
      nlinarith [hKd0]
    linarith
  calc ‖∫ t in (m:ℝ)..(n:ℝ), (((Chebyshev.psi t - t : ℝ)) : ℂ) * deriv (gfun L s f) t‖
      ≤ Cc * L^(-2:ℝ) * (‖s‖ * Kf + Kd / L) * Real.log ((n:ℝ)/(m:ℝ)) := hbound
    _ ≤ Cc * L^(-2:ℝ) * (‖s‖ * Kf + Kd) * (L * x₀) := by
        have hnp : 0 ≤ Cc * L^(-2:ℝ) := by positivity
        have h1 : Cc * L^(-2:ℝ) * (‖s‖ * Kf + Kd / L) ≤ Cc * L^(-2:ℝ) * (‖s‖ * Kf + Kd) :=
          mul_le_mul_of_nonneg_left hKg3 hnp
        have h3 : 0 ≤ Cc * L^(-2:ℝ) * (‖s‖ * Kf + Kd) := by positivity
        calc Cc * L^(-2:ℝ) * (‖s‖ * Kf + Kd / L) * Real.log ((n:ℝ)/(m:ℝ))
            ≤ Cc * L^(-2:ℝ) * (‖s‖ * Kf + Kd) * Real.log ((n:ℝ)/(m:ℝ)) :=
              mul_le_mul_of_nonneg_right h1 hlog0
          _ ≤ Cc * L^(-2:ℝ) * (‖s‖ * Kf + Kd) * (L * x₀) :=
              mul_le_mul_of_nonneg_left hlog h3

/-- The `tsum` of the smoothed von Mangoldt sum is a finite sum (support in `[1, e^{Lx₀}]`). -/
private lemma tsum_eq_finset_sum {x₀ L : ℝ} (hx₀ : 0 < x₀) (hL : 0 < L) {f : ℝ → ℝ}
    (hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0) (s : ℂ) :
    (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * ((n:ℂ)^s)⁻¹ *
        ((f (Real.log n / L) : ℝ) : ℂ))
      = ∑ n ∈ Finset.Icc 1 ⌊Real.exp (L*x₀)⌋₊,
          ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * ((n:ℂ)^s)⁻¹ *
            ((f (Real.log n / L) : ℝ) : ℂ) := by
  refine tsum_eq_sum (s := Finset.Icc 1 ⌊Real.exp (L*x₀)⌋₊) (fun b hb => ?_)
  by_cases hb0 : b = 0
  · subst hb0; simp
  · have hb1 : 1 ≤ b := Nat.one_le_iff_ne_zero.mpr hb0
    have hbM : ⌊Real.exp (L*x₀)⌋₊ < b := by
      by_contra h; push_neg at h
      exact hb (Finset.mem_Icc.mpr ⟨hb1, h⟩)
    have hbexp : Real.exp (L*x₀) < (b:ℝ) := by
      have h1 : Real.exp (L*x₀) < ((⌊Real.exp (L*x₀)⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
      have h2 : ((⌊Real.exp (L*x₀)⌋₊ : ℕ) : ℝ) + 1 ≤ (b:ℝ) := by
        exact_mod_cast (by omega : ⌊Real.exp (L*x₀)⌋₊ + 1 ≤ b)
      linarith
    have hlog : x₀ ≤ Real.log b / L := by
      rw [le_div_iff₀ hL]
      have h3 : Real.log (Real.exp (L*x₀)) < Real.log b := Real.log_lt_log (Real.exp_pos _) hbexp
      rw [Real.log_exp] at h3
      linarith
    rw [hsupp (Real.log b / L) hlog]
    simp


/-- `exp (-s * log n) = (n^s)^{-1}`. -/
private lemma exp_neg_log_eq_cpow_inv {s : ℂ} {n : ℕ} (hn : n ≠ 0) :
    Complex.exp (-s * Complex.log (n:ℂ)) = ((n:ℂ)^s)⁻¹ := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn), ← Complex.exp_neg]
  congr 1
  ring

private lemma rpow_two_eq_sq (x : ℝ) : x ^ (2:ℝ) = x^2 := by
  rw [show (2:ℝ) = ((2:ℕ):ℝ) from by norm_num, Real.rpow_natCast]

/-- If `a √u ≤ c/2` then `a u ≤ (c/2)√u` for `u ≥ 0`. -/
private lemma mul_self_le_of_mul_sqrt_le {a c u : ℝ} (hu : 0 ≤ u)
    (h : a * Real.sqrt u ≤ c/2) : a * u ≤ (c/2) * Real.sqrt u := by
  have hsu : 0 ≤ Real.sqrt u := Real.sqrt_nonneg _
  have hsq : Real.sqrt u * Real.sqrt u = u := by rw [← sq]; exact Real.sq_sqrt hu
  calc a * u = a * (Real.sqrt u * Real.sqrt u) := by rw [hsq]
    _ = (a * Real.sqrt u) * Real.sqrt u := by ring
    _ ≤ (c/2) * Real.sqrt u := mul_le_mul_of_nonneg_right h hsu

private lemma tendsto_log_rpow_div_self (k : ℝ) :
    Filter.Tendsto (fun L : ℝ => (Real.log L) ^ k / L) Filter.atTop (nhds 0) := by
  have h : (fun x : ℝ => Real.log x ^ k) =o[Filter.atTop] (fun x : ℝ => x ^ (1:ℝ)) :=
    isLittleO_log_rpow_rpow_atTop (s := 1) k (by norm_num)
  have h2 : Filter.Tendsto (fun x : ℝ => Real.log x ^ k / x ^ (1:ℝ)) Filter.atTop (nhds 0) :=
    h.tendsto_div_nhds_zero
  refine h2.congr' ?_
  filter_upwards with x
  rw [Real.rpow_one]

private lemma tendsto_log_sq_div_self :
    Filter.Tendsto (fun L : ℝ => (Real.log L)^2 / L) Filter.atTop (nhds 0) := by
  have h := tendsto_log_rpow_div_self 2
  refine h.congr' ?_
  filter_upwards with x
  rw [rpow_two_eq_sq]

/-- `tsum` of a supported summand is a finite sum. -/
private lemma tsum_mul_supp {x₀ L : ℝ} (hL : 0 < L) {f : ℝ → ℝ}
    (hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0) (a : ℕ → ℂ) (ha0 : a 0 = 0) :
    (∑' n : ℕ, a n * ((f (Real.log n / L) : ℝ) : ℂ))
      = ∑ n ∈ Finset.Icc 1 ⌊Real.exp (L*x₀)⌋₊, a n * ((f (Real.log n / L) : ℝ) : ℂ) := by
  refine tsum_eq_sum (s := Finset.Icc 1 ⌊Real.exp (L*x₀)⌋₊) (fun b hb => ?_)
  by_cases hb0 : b = 0
  · subst hb0; rw [ha0, zero_mul]
  · have hb1 : 1 ≤ b := Nat.one_le_iff_ne_zero.mpr hb0
    have hbM : ⌊Real.exp (L*x₀)⌋₊ < b := by
      by_contra h; push_neg at h
      exact hb (Finset.mem_Icc.mpr ⟨hb1, h⟩)
    have hbexp : Real.exp (L*x₀) < (b:ℝ) := by
      have h1 : Real.exp (L*x₀) < ((⌊Real.exp (L*x₀)⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
      have h2 : ((⌊Real.exp (L*x₀)⌋₊ : ℕ) : ℝ) + 1 ≤ (b:ℝ) := by
        exact_mod_cast (by omega : ⌊Real.exp (L*x₀)⌋₊ + 1 ≤ b)
      linarith
    have hlog : x₀ ≤ Real.log b / L := by
      rw [le_div_iff₀ hL]
      have h3 : Real.log (Real.exp (L*x₀)) < Real.log b := Real.log_lt_log (Real.exp_pos _) hbexp
      rw [Real.log_exp] at h3
      linarith
    rw [hsupp (Real.log b / L) hlog]
    simp

/-- Pointwise bound `‖gfun L s f x‖ ≤ Kf · x^{-Re s}` for `x ≥ 1`. -/
private lemma norm_gfun_le {L Kf : ℝ} {f : ℝ → ℝ} {s : ℂ} {x : ℝ}
    (hx1 : 1 ≤ x) (hKf : |f (Real.log x / L)| ≤ Kf) :
    ‖gfun L s f x‖ ≤ Kf * x^(-s.re) := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hxnn : 0 ≤ x := le_trans zero_le_one hx1
  have hKf0 : 0 ≤ Kf := le_trans (abs_nonneg _) hKf
  have hexp : ‖Complex.exp (-s * ((Real.log x : ℝ) : ℂ))‖ = x ^ (-s.re) := by
    rw [Complex.norm_exp]
    have h1 : (-s * ((Real.log x : ℝ) : ℂ)).re = -s.re * Real.log x := by
      simp [Complex.mul_re]
    rw [h1, Real.rpow_def_of_pos hxpos]
    ring_nf
  calc ‖gfun L s f x‖ = x ^ (-s.re) * |f (Real.log x / L)| := by
        rw [gfun, norm_mul, hexp, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ x ^ (-s.re) * Kf := mul_le_mul_of_nonneg_left hKf (Real.rpow_nonneg hxnn _)
    _ = Kf * x ^ (-s.re) := by ring

/-- Bound for the truncation of the smoothed von Mangoldt sum. -/
private lemma norm_sum_vonMangoldt_gfun_le {L Kf : ℝ} {f : ℝ → ℝ} {s : ℂ} {N : ℕ}
    (hL : 0 < L) (hN : 1 ≤ N) (hσ : 0 < s.re) (hσ2 : s.re ≤ 2)
    (hcond : (1 - s.re) * Real.log (N:ℝ) ≤ 1)
    (hKf : ∀ t, 0 ≤ t → |f t| ≤ Kf) :
    ‖∑ n ∈ Finset.Icc 1 N, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * gfun L s f (n:ℝ)‖
      ≤ Kf * (200 * (Real.log 4 + 5)) * (1 + Real.log (N:ℝ)) := by
  have hKf0 : 0 ≤ Kf := le_trans (abs_nonneg _) (hKf 0 le_rfl)
  have hterm : ∀ n ∈ Finset.Icc 1 N,
      ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * gfun L s f (n:ℝ)‖
        ≤ (ArithmeticFunction.vonMangoldt n) * (Kf * (n:ℝ)^(-s.re)) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn.1
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact mul_le_mul_of_nonneg_left
      (norm_gfun_le hn1 (hKf _ (div_nonneg (Real.log_nonneg hn1) hL.le)))
      ArithmeticFunction.vonMangoldt_nonneg
  calc ‖∑ n ∈ Finset.Icc 1 N, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * gfun L s f (n:ℝ)‖
      ≤ ∑ n ∈ Finset.Icc 1 N, ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * gfun L s f (n:ℝ)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n) * (Kf * (n:ℝ)^(-s.re)) :=
        Finset.sum_le_sum hterm
    _ = Kf * ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n) * (n:ℝ)^(-s.re) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun n _ => by ring)
    _ ≤ Kf * (200 * (Real.log 4 + 5) * (1 + Real.log (N:ℝ))) :=
        mul_le_mul_of_nonneg_left (sum_vonMangoldt_mul_rpow_neg_le hσ hσ2 hN hcond) hKf0
    _ = Kf * (200 * (Real.log 4 + 5)) * (1 + Real.log (N:ℝ)) := by ring

/-- Bound for `∫₁^N gfun`. -/
private lemma norm_integral_gfun_le {L Kf : ℝ} {f : ℝ → ℝ} {s : ℂ} {N : ℕ}
    (hL : 0 < L) (hN : 1 ≤ N) (hσ : 0 < s.re)
    (hcond : (1 - s.re) * Real.log (N:ℝ) ≤ 1)
    (hKf : ∀ t, 0 ≤ t → |f t| ≤ Kf) :
    ‖∫ t in (1:ℝ)..(N:ℝ), gfun L s f t‖ ≤ Kf * 4 * (1 + Real.log (N:ℝ)) := by
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hKf0 : 0 ≤ Kf := le_trans (abs_nonneg _) (hKf 0 le_rfl)
  have hpt : ∀ᵐ t ∂volume, t ∈ Set.Ioc (1:ℝ) (N:ℝ) → ‖gfun L s f t‖ ≤ Kf * t^(-s.re) := by
    filter_upwards with t ht
    rw [Set.mem_Ioc] at ht
    have ht1 : (1:ℝ) ≤ t := le_of_lt ht.1
    exact norm_gfun_le ht1 (hKf _ (div_nonneg (Real.log_nonneg ht1) hL.le))
  have hcont : ContinuousOn (fun t : ℝ => Kf * t^(-s.re)) (Set.uIcc (1:ℝ) (N:ℝ)) :=
    (continuousOn_rpow_neg (σ := s.re) zero_lt_one hN1).const_mul Kf
  have h := intervalIntegral.norm_integral_le_of_norm_le hN1 hpt hcont.intervalIntegrable
  rw [intervalIntegral.integral_const_mul] at h
  have h2 := integral_rpow_neg_le hσ hN1 hcond
  calc ‖∫ t in (1:ℝ)..(N:ℝ), gfun L s f t‖ ≤ Kf * ∫ t in (1:ℝ)..(N:ℝ), t^(-s.re) := h
    _ ≤ Kf * (4 * (1 + Real.log (N:ℝ))) := mul_le_mul_of_nonneg_left h2 hKf0
    _ = Kf * 4 * (1 + Real.log (N:ℝ)) := by ring

/-- The term `(ψ(t)-t)·g(t)` is bounded by `Cc·Kf`. -/
private lemma norm_R_gfun_le {c Cc L Kf : ℝ} {f : ℝ → ℝ} {s : ℂ} {t : ℝ}
    (hc : 0 < c) (hCc : 0 ≤ Cc) (ht1 : 1 ≤ t)
    (hψ : |Chebyshev.psi t - t| ≤ Cc * t * Real.exp (-c * Real.sqrt (Real.log t)))
    (h1σ : (1 - s.re) * Real.sqrt (Real.log t) ≤ c / 2)
    (hKf : |f (Real.log t / L)| ≤ Kf) :
    ‖(((Chebyshev.psi t - t : ℝ)) : ℂ) * gfun L s f t‖ ≤ Cc * Kf := by
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have htnn : 0 ≤ t := le_trans zero_le_one ht1
  have hKf0 : 0 ≤ Kf := le_trans (abs_nonneg _) hKf
  have hlogt : 0 ≤ Real.sqrt (Real.log t) := Real.sqrt_nonneg _
  have hexp : ‖Complex.exp (-s * ((Real.log t : ℝ) : ℂ))‖ = t ^ (-s.re) := by
    rw [Complex.norm_exp]
    have h1 : (-s * ((Real.log t : ℝ) : ℂ)).re = -s.re * Real.log t := by
      simp [Complex.mul_re]
    rw [h1, Real.rpow_def_of_pos htpos]
    ring_nf
  have hnorm : (((Chebyshev.psi t - t : ℝ)) : ℂ) * gfun L s f t
      = (((Chebyshev.psi t - t : ℝ)) : ℂ) *
        (Complex.exp (-s * ((Real.log t : ℝ) : ℂ)) * ((f (Real.log t / L) : ℝ) : ℂ)) := by
    rw [gfun]
  rw [hnorm, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, hexp, Complex.norm_real,
    Real.norm_eq_abs]
  have hstep1 : |Chebyshev.psi t - t| * (t ^ (-s.re) * |f (Real.log t / L)|)
      ≤ (Cc * t * Real.exp (-c * Real.sqrt (Real.log t))) * (t ^ (-s.re) * Kf) := by
    refine mul_le_mul hψ (mul_le_mul_of_nonneg_left hKf (Real.rpow_nonneg htnn _))
      (mul_nonneg (Real.rpow_nonneg htnn _) (abs_nonneg _)) ?_
    exact mul_nonneg (mul_nonneg hCc htnn) (Real.exp_pos _).le
  have hstep2 : (Cc * t * Real.exp (-c * Real.sqrt (Real.log t))) * (t ^ (-s.re) * Kf)
      = Cc * Kf * (Real.exp ((1 - s.re) * Real.log t) *
          Real.exp (-c * Real.sqrt (Real.log t))) := by
    have h1 : t * t ^ (-s.re) = Real.exp ((1 - s.re) * Real.log t) := by
      calc t * t ^ (-s.re) = t^(1:ℝ) * t ^ (-s.re) := by rw [Real.rpow_one]
        _ = t^((1:ℝ) + -s.re) := by rw [Real.rpow_add htpos]
        _ = Real.exp (Real.log t * ((1:ℝ) + -s.re)) := by rw [Real.rpow_def_of_pos htpos]
        _ = Real.exp ((1 - s.re) * Real.log t) := by congr 1; ring
    calc (Cc * t * Real.exp (-c * Real.sqrt (Real.log t))) * (t ^ (-s.re) * Kf)
        = Cc * Kf * ((t * t ^ (-s.re)) * Real.exp (-c * Real.sqrt (Real.log t))) := by ring
      _ = Cc * Kf * (Real.exp ((1 - s.re) * Real.log t) *
            Real.exp (-c * Real.sqrt (Real.log t))) := by rw [h1]
  have hstep3 : Real.exp ((1 - s.re) * Real.log t) * Real.exp (-c * Real.sqrt (Real.log t))
      ≤ 1 := by
    have hA : Real.exp ((1 - s.re) * Real.log t) * Real.exp (-c * Real.sqrt (Real.log t))
        = Real.exp ((1 - s.re) * Real.log t + -c * Real.sqrt (Real.log t)) := by
      rw [Real.exp_add]
    rw [hA]
    have hB : (1 - s.re) * Real.log t + -c * Real.sqrt (Real.log t) ≤ 0 := by
      have hlogt0 : 0 ≤ Real.log t := Real.log_nonneg ht1
      have hle := mul_self_le_of_mul_sqrt_le hlogt0 h1σ
      nlinarith [hle, hlogt, hc]
    calc Real.exp ((1 - s.re) * Real.log t + -c * Real.sqrt (Real.log t))
        ≤ Real.exp 0 := Real.exp_le_exp.mpr hB
      _ = 1 := Real.exp_zero
  calc |Chebyshev.psi t - t| * (t ^ (-s.re) * |f (Real.log t / L)|)
      ≤ (Cc * t * Real.exp (-c * Real.sqrt (Real.log t))) * (t ^ (-s.re) * Kf) := hstep1
    _ = Cc * Kf * (Real.exp ((1 - s.re) * Real.log t) *
          Real.exp (-c * Real.sqrt (Real.log t))) := hstep2
    _ ≤ Cc * Kf * 1 := mul_le_mul_of_nonneg_left hstep3 (by positivity)
    _ = Cc * Kf := by ring

/-- Pointwise bound for the de la Vallée Poussin error term against `t^{-σ}`. -/
private lemma psi_sub_id_mul_rpow_le {c Cc L σ : ℝ} (hc : 0 < c) (hCc : 0 ≤ Cc)
    (hL : 1 < L) {t : ℝ} (ht2 : 2 ≤ t)
    (hσ : (1 - σ) * Real.sqrt (Real.log t) ≤ c / 2)
    (hbig : (4/c) * Real.log L ≤ Real.sqrt (Real.log t))
    (hψ : |Chebyshev.psi t - t| ≤ Cc * t * Real.exp (-c * Real.sqrt (Real.log t))) :
    |Chebyshev.psi t - t| * t^(-σ) ≤ Cc * L^(-2:ℝ) := by
  have htpos : 0 < t := by linarith
  have htnn : 0 ≤ t := le_of_lt htpos
  have hLpos : 0 < L := by linarith
  have hlogt0 : 0 ≤ Real.log t := Real.log_nonneg (by linarith : (1:ℝ) ≤ t)
  have h1 : |Chebyshev.psi t - t| * t^(-σ)
      ≤ (Cc * t * Real.exp (-c * Real.sqrt (Real.log t))) * t^(-σ) :=
    mul_le_mul_of_nonneg_right hψ (Real.rpow_nonneg htnn _)
  have h2 : (Cc * t * Real.exp (-c * Real.sqrt (Real.log t))) * t^(-σ)
      = Cc * (Real.exp ((1-σ) * Real.log t) * Real.exp (-c * Real.sqrt (Real.log t))) := by
    have h1' : t * t^(-σ) = Real.exp ((1-σ) * Real.log t) := by
      calc t * t ^ (-σ) = t^(1:ℝ) * t ^ (-σ) := by rw [Real.rpow_one]
        _ = t^((1:ℝ) + -σ) := by rw [Real.rpow_add htpos]
        _ = Real.exp (Real.log t * ((1:ℝ) + -σ)) := by rw [Real.rpow_def_of_pos htpos]
        _ = Real.exp ((1 - σ) * Real.log t) := by congr 1; ring
    calc (Cc * t * Real.exp (-c * Real.sqrt (Real.log t))) * t^(-σ)
        = Cc * ((t * t^(-σ)) * Real.exp (-c * Real.sqrt (Real.log t))) := by ring
      _ = Cc * (Real.exp ((1-σ) * Real.log t) * Real.exp (-c * Real.sqrt (Real.log t))) := by
            rw [h1']
  have h3 : Real.exp ((1-σ) * Real.log t) * Real.exp (-c * Real.sqrt (Real.log t))
      ≤ Real.exp (-2 * Real.log L) := by
    have hA : Real.exp ((1-σ) * Real.log t) * Real.exp (-c * Real.sqrt (Real.log t))
        = Real.exp ((1-σ) * Real.log t + -c * Real.sqrt (Real.log t)) := by
      rw [Real.exp_add]
    rw [hA]
    refine Real.exp_le_exp.mpr ?_
    have hmul' := mul_self_le_of_mul_sqrt_le hlogt0 hσ
    have hbig' : (c/2) * ((4/c) * Real.log L) ≤ (c/2) * Real.sqrt (Real.log t) :=
      mul_le_mul_of_nonneg_left hbig (by positivity)
    have hc2 : (c/2)*(4/c) = 2 := by field_simp; ring
    have h2logL : 2 * Real.log L ≤ (c/2) * Real.sqrt (Real.log t) := by
      have := hbig'
      rw [show (c/2)*((4/c) * Real.log L) = ((c/2)*(4/c)) * Real.log L by ring, hc2] at this
      simpa using this
    linarith [hmul', h2logL]
  have h5 : Real.exp (-2 * Real.log L) = L^(-2:ℝ) := by
    rw [Real.rpow_def_of_pos hLpos]
    congr 1
    ring
  calc |Chebyshev.psi t - t| * t^(-σ)
      ≤ (Cc * t * Real.exp (-c * Real.sqrt (Real.log t))) * t^(-σ) := h1
    _ = Cc * (Real.exp ((1-σ) * Real.log t) * Real.exp (-c * Real.sqrt (Real.log t))) := h2
    _ ≤ Cc * Real.exp (-2 * Real.log L) := mul_le_mul_of_nonneg_left h3 hCc
    _ = Cc * L^(-2:ℝ) := by rw [h5]


/-- Abel-summation decomposition of the smoothed von Mangoldt sum. -/
private lemma sum_decomp {x₀ L Kf Kd : ℝ} {f : ℝ → ℝ} {s : ℂ} {M NA : ℕ}
    (hx₀ : 0 < x₀) (hL : 1 < L) (hM1 : 1 ≤ M) (hNA1 : 1 ≤ NA) (hNAM : NA ≤ M)
    (hMe : (M:ℝ) ≤ Real.exp (L*x₀)) (hNAe : (NA:ℝ) ≤ Real.exp (L*x₀))
    (hcont : ContinuousOn f (Set.Ici 0)) (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    (hσ : 0 ≤ s.re) (hKf : ∀ t, 0 ≤ t → |f t| ≤ Kf)
    (hKd : ∀ t ∈ Set.Ioo 0 x₀, |deriv f t| ≤ Kd) :
    (∑ n ∈ Finset.Icc 1 M, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * gfun L s f (n:ℝ))
      - (L:ℂ) * (∫ t in (0:ℝ)..x₀,
          Complex.exp (-(((s-1) * L : ℂ) * (t:ℂ))) * ((f t : ℝ):ℂ))
      = ((∑ n ∈ Finset.Icc 1 NA, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * gfun L s f (n:ℝ))
          - (∫ t in (1:ℝ)..(NA:ℝ), gfun L s f t))
        + (((Chebyshev.psi (M:ℝ) - (M:ℝ) : ℝ)) : ℂ) * gfun L s f (M:ℝ)
        - (((Chebyshev.psi (NA:ℝ) - (NA:ℝ) : ℝ)) : ℂ) * gfun L s f (NA:ℝ)
        - (∫ t in (NA:ℝ)..(M:ℝ), (((Chebyshev.psi t - t : ℝ)) : ℂ) * deriv (gfun L s f) t)
        - (∫ t in (M:ℝ)..Real.exp (L*x₀), gfun L s f t) := by
  have hLpos : (0:ℝ) < L := by linarith
  have hM1' : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM1
  have hNA1' : (1:ℝ) ≤ (NA:ℝ) := by exact_mod_cast hNA1
  have hNAM' : (NA:ℝ) ≤ (M:ℝ) := by exact_mod_cast hNAM
  have hexp1 : (1:ℝ) ≤ Real.exp (L*x₀) := le_trans hM1' hMe
  have hSM := sum_full_eq (M := M) hx₀ hL hM1 hMe hcont hf2 hσ hKf hKd
  have hSNA := sum_full_eq (M := NA) hx₀ hL hNA1 hNAe hcont hf2 hσ hKf hKd
  have hIBP := integral_id_deriv_interval (m := NA) (n := M) hx₀ hL hNA1 hNAM hMe hcont hf2 hσ hKf hKd
  have hImain := integral_gfun_eq_main hx₀ hLpos hcont s
  have hpsiM : IntervalIntegrable (fun t : ℝ => (Chebyshev.psi t : ℂ) * deriv (gfun L s f) t)
      volume (1:ℝ) (M:ℝ) := intervalIntegrable_psi_deriv hx₀ hL hM1 hMe hf2 hσ hKf hKd
  have hsubNA : Set.uIcc (1:ℝ) (NA:ℝ) ⊆ Set.uIcc (1:ℝ) (M:ℝ) := by
    rw [Set.uIcc_of_le hNA1', Set.uIcc_of_le hM1']
    exact fun x hx => ⟨hx.1, le_trans hx.2 hNAM'⟩
  have hsubNAM : Set.uIcc (NA:ℝ) (M:ℝ) ⊆ Set.uIcc (1:ℝ) (M:ℝ) := by
    rw [Set.uIcc_of_le hNAM', Set.uIcc_of_le hM1']
    exact fun x hx => ⟨le_trans hNA1' hx.1, hx.2⟩
  have hpsiNA := hpsiM.mono_set hsubNA
  have hpsiNAM := hpsiM.mono_set hsubNAM
  have hderM : IntervalIntegrable (deriv (gfun L s f)) volume (1:ℝ) (M:ℝ) :=
    intervalIntegrable_deriv_gfun hx₀ hL hM1 hMe hf2 hσ hKf hKd
  have hderNAM := hderM.mono_set hsubNAM
  have hcontu : ContinuousOn (fun t : ℝ => (t:ℂ)) (Set.uIcc (NA:ℝ) (M:ℝ)) := by fun_prop
  have htderivNAM : IntervalIntegrable (fun t : ℝ => (t:ℂ) * deriv (gfun L s f) t)
      volume (NA:ℝ) (M:ℝ) := hderNAM.continuousOn_mul hcontu
  have hRderNAM : IntervalIntegrable
      (fun t : ℝ => (((Chebyshev.psi t - t : ℝ)) : ℂ) * deriv (gfun L s f) t)
      volume (NA:ℝ) (M:ℝ) := by
    have h := hpsiNAM.sub htderivNAM
    refine h.congr (fun t _ => ?_)
    push_cast
    ring
  have hgIcc : ContinuousOn (gfun L s f) (Set.uIcc (1:ℝ) (Real.exp (L*x₀))) := by
    rw [Set.uIcc_of_le hexp1]
    exact continuousOn_gfun hx₀ hLpos hcont s hexp1 le_rfl
  have hgMain : IntervalIntegrable (gfun L s f) volume (1:ℝ) (Real.exp (L*x₀)) :=
    hgIcc.intervalIntegrable
  have hgNA : IntervalIntegrable (gfun L s f) volume (1:ℝ) (NA:ℝ) :=
    hgMain.mono_set (by
      rw [Set.uIcc_of_le hNA1', Set.uIcc_of_le hexp1]
      exact fun x hx => ⟨hx.1, le_trans hx.2 hNAe⟩)
  have hgNAM : IntervalIntegrable (gfun L s f) volume (NA:ℝ) (M:ℝ) :=
    hgMain.mono_set (by
      rw [Set.uIcc_of_le hNAM', Set.uIcc_of_le hexp1]
      exact fun x hx => ⟨le_trans hNA1' hx.1, le_trans hx.2 hMe⟩)
  have hgTail : IntervalIntegrable (gfun L s f) volume (M:ℝ) (Real.exp (L*x₀)) :=
    hgMain.mono_set (by
      rw [Set.uIcc_of_le hMe, Set.uIcc_of_le hexp1]
      exact fun x hx => ⟨le_trans hM1' hx.1, hx.2⟩)
  have hsplit1 : (∫ t in (1:ℝ)..(M:ℝ), (Chebyshev.psi t : ℂ) * deriv (gfun L s f) t)
      = (∫ t in (1:ℝ)..(NA:ℝ), (Chebyshev.psi t : ℂ) * deriv (gfun L s f) t)
        + ∫ t in (NA:ℝ)..(M:ℝ), (Chebyshev.psi t : ℂ) * deriv (gfun L s f) t :=
    (intervalIntegral.integral_add_adjacent_intervals hpsiNA hpsiNAM).symm
  have hsplit2 : (∫ t in (NA:ℝ)..(M:ℝ), (Chebyshev.psi t : ℂ) * deriv (gfun L s f) t)
      = (∫ t in (NA:ℝ)..(M:ℝ), (t:ℂ) * deriv (gfun L s f) t)
        + ∫ t in (NA:ℝ)..(M:ℝ), (((Chebyshev.psi t - t : ℝ)) : ℂ) * deriv (gfun L s f) t := by
    rw [intervalIntegral.integral_congr (fun t _ => ?_),
      intervalIntegral.integral_add htderivNAM hRderNAM]
    push_cast
    ring
  have hsplit3 : (∫ t in (1:ℝ)..Real.exp (L*x₀), gfun L s f t)
      = (∫ t in (1:ℝ)..(NA:ℝ), gfun L s f t) + (∫ t in (NA:ℝ)..(M:ℝ), gfun L s f t)
        + ∫ t in (M:ℝ)..Real.exp (L*x₀), gfun L s f t := by
    have h1 := (intervalIntegral.integral_add_adjacent_intervals hgNA (hgNAM.trans hgTail)).symm
    have h2 := (intervalIntegral.integral_add_adjacent_intervals hgNAM hgTail).symm
    rw [h2] at h1
    rw [h1]
    ring
  have hsplit4 : (∫ t in (1:ℝ)..(M:ℝ), gfun L s f t)
      = (∫ t in (1:ℝ)..(NA:ℝ), gfun L s f t) + ∫ t in (NA:ℝ)..(M:ℝ), gfun L s f t :=
    (intervalIntegral.integral_add_adjacent_intervals hgNA hgNAM).symm
  have hR1 : (((Chebyshev.psi (M:ℝ) - (M:ℝ) : ℝ)) : ℂ) * gfun L s f (M:ℝ)
      = (Chebyshev.psi (M:ℝ) : ℂ) * gfun L s f (M:ℝ)
        - ((M:ℝ):ℂ) * gfun L s f (M:ℝ) := by push_cast; ring
  have hR2 : (((Chebyshev.psi (NA:ℝ) - (NA:ℝ) : ℝ)) : ℂ) * gfun L s f (NA:ℝ)
      = (Chebyshev.psi (NA:ℝ) : ℂ) * gfun L s f (NA:ℝ)
        - ((NA:ℝ):ℂ) * gfun L s f (NA:ℝ) := by push_cast; ring
  have hI2 : (∫ t in (1:ℝ)..(NA:ℝ), (Chebyshev.psi t : ℂ) * deriv (gfun L s f) t)
      = (Chebyshev.psi (NA:ℝ) : ℂ) * gfun L s f (NA:ℝ)
        - ∑ n ∈ Finset.Icc 1 NA,
            ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * gfun L s f (n:ℝ) := by
    rw [hSNA]; ring
  rw [hR1, hR2]
  rw [hSM]
  rw [← hImain]
  rw [hsplit1]
  rw [hsplit2]
  rw [hIBP]
  rw [hI2]
  rw [hsplit3]
  ring


/-- `√(log L)/L ≤ 1/2` for `L ≥ 2`. -/
private lemma sqrt_log_div_self_le_half {L : ℝ} (hL : 2 ≤ L) :
    Real.sqrt (Real.log L) / L ≤ 1/2 := by
  have hLpos : 0 < L := by linarith
  have h1 : Real.log L ≤ L - 1 := Real.log_le_sub_one_of_pos hLpos
  have h2 : L - 1 ≤ L^2/4 := by nlinarith
  have h3 : Real.log L ≤ L^2/4 := le_trans h1 h2
  have h4 : Real.sqrt (Real.log L) ≤ Real.sqrt (L^2/4) := Real.sqrt_le_sqrt h3
  have h5 : Real.sqrt (L^2/4) = L/2 := by
    rw [show L^2/4 = (L/2)^2 by ring]
    exact Real.sqrt_sq (by linarith)
  rw [h5] at h4
  rw [div_le_iff₀ hLpos]
  linarith

private lemma tendsto_log_pow_div_self (k : ℕ) :
    Filter.Tendsto (fun L : ℝ => (Real.log L)^k / L) Filter.atTop (nhds 0) := by
  have h := tendsto_log_rpow_div_self (k:ℝ)
  refine h.congr' ?_
  filter_upwards with x
  rw [← Real.rpow_natCast]

/-- Crude bound for the truncated smoothed von Mangoldt sum. -/
private lemma norm_sum_vonMangoldt_gfun_crude {x₀ L L0 Kf : ℝ} {f : ℝ → ℝ} {s : ℂ} {M : ℕ}
    (hx₀ : 0 < x₀) (hL : 0 < L) (hLL0 : L ≤ L0) (hM : (M:ℝ) ≤ Real.exp (L*x₀))
    (hσ : 0 < s.re) (hKf : ∀ t, 0 ≤ t → |f t| ≤ Kf) :
    ‖∑ n ∈ Finset.Icc 1 M, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * gfun L s f (n:ℝ)‖
      ≤ Kf * (Real.log 4 + 5) * Real.exp (L0 * x₀) := by
  have hKf0 : 0 ≤ Kf := le_trans (abs_nonneg _) (hKf 0 le_rfl)
  have hterm : ∀ n ∈ Finset.Icc 1 M,
      ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * gfun L s f (n:ℝ)‖
        ≤ (ArithmeticFunction.vonMangoldt n) * Kf := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn.1
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    have h1 := norm_gfun_le (s := s) hn1 (hKf _ (div_nonneg (Real.log_nonneg hn1) hL.le))
    have h2 : (n:ℝ)^(-s.re) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
    calc (ArithmeticFunction.vonMangoldt n) * ‖gfun L s f (n:ℝ)‖
        ≤ (ArithmeticFunction.vonMangoldt n) * (Kf * (n:ℝ)^(-s.re)) :=
          mul_le_mul_of_nonneg_left h1 ArithmeticFunction.vonMangoldt_nonneg
      _ ≤ (ArithmeticFunction.vonMangoldt n) * Kf := by
          apply mul_le_mul_of_nonneg_left _ ArithmeticFunction.vonMangoldt_nonneg
          calc Kf * (n:ℝ)^(-s.re) ≤ Kf * 1 := mul_le_mul_of_nonneg_left h2 hKf0
            _ = Kf := by ring
  have hpsi := Chebyshev.psi_le_const_mul_self (show (0:ℝ) ≤ (M:ℝ) by positivity)
  calc ‖∑ n ∈ Finset.Icc 1 M, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * gfun L s f (n:ℝ)‖
      ≤ ∑ n ∈ Finset.Icc 1 M,
          ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * gfun L s f (n:ℝ)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 M, (ArithmeticFunction.vonMangoldt n) * Kf := Finset.sum_le_sum hterm
    _ = Kf * ∑ n ∈ Finset.Icc 1 M, (ArithmeticFunction.vonMangoldt n) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun n _ => by ring)
    _ = Kf * Chebyshev.psi (M:ℝ) := by rw [psi_nat_eq_sum_Icc1]
    _ ≤ Kf * ((Real.log 4 + 4) * Real.exp (L0*x₀)) := by
        apply mul_le_mul_of_nonneg_left _ hKf0
        calc Chebyshev.psi (M:ℝ) ≤ (Real.log 4 + 4) * (M:ℝ) := hpsi
          _ ≤ (Real.log 4 + 4) * Real.exp (L0*x₀) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact le_trans hM (Real.exp_le_exp.mpr (by nlinarith [hLL0, hx₀]))
    _ ≤ Kf * (Real.log 4 + 5) * Real.exp (L0*x₀) := by
        have hC : Real.log 4 + 4 ≤ Real.log 4 + 5 := by linarith
        nlinarith [hKf0, Real.exp_pos (L0*x₀), hC]

/-- Crude bound for the main integral `L∫₀^{x₀} e^{-(s-1)Lt} f`. -/
private lemma norm_main_integral_le {x₀ L L0 Kf : ℝ} {f : ℝ → ℝ} {s : ℂ}
    (hx₀ : 0 < x₀) (hLpos : 0 < L) (hle : L ≤ L0)
    (hσ1 : |s.re - 1| ≤ Real.sqrt (Real.log L)/L) (hKf : ∀ t, 0 ≤ t → |f t| ≤ Kf) :
    ‖(L:ℂ) * (∫ t in (0:ℝ)..x₀,
        Complex.exp (-(((s-1) * L : ℂ) * (t:ℂ))) * ((f t:ℝ):ℂ))‖
      ≤ L0 * Kf * x₀ * Real.exp (x₀ * Real.sqrt (Real.log L0)) := by
  have hKf0 : 0 ≤ Kf := le_trans (abs_nonneg _) (hKf 0 le_rfl)
  have hE0 : 0 < Real.exp (x₀ * Real.sqrt (Real.log L0)) := Real.exp_pos _
  have hlogmono : Real.log L ≤ Real.log L0 := Real.log_le_log hLpos hle
  have hsqrtmono : Real.sqrt (Real.log L) ≤ Real.sqrt (Real.log L0) := Real.sqrt_le_sqrt hlogmono
  have hpt : ∀ᵐ t ∂volume, t ∈ Set.Ioc (0:ℝ) x₀ →
      ‖Complex.exp (-(((s-1) * L : ℂ) * (t:ℂ))) * ((f t : ℝ):ℂ)‖
        ≤ Kf * Real.exp (x₀ * Real.sqrt (Real.log L0)) := by
    filter_upwards with t ht
    rw [Set.mem_Ioc] at ht
    have ht0 : 0 ≤ t := le_of_lt ht.1
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hnorm : ‖Complex.exp (-(((s-1) * L : ℂ) * (t:ℂ)))‖ = Real.exp ((1 - s.re)*(L*t)) := by
      rw [Complex.norm_exp]
      congr 1
      simp only [Complex.neg_re, Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero]
      ring
    rw [hnorm]
    have h1 : (1 - s.re)*(L*t) ≤ x₀ * Real.sqrt (Real.log L0) := by
      have h2 : (1 - s.re) * (L*t) ≤ |s.re - 1| * (L*t) := by
        have h3 : (1 - s.re) ≤ |s.re - 1| := by
          have := neg_le_abs (s.re - 1); linarith
        exact mul_le_mul_of_nonneg_right h3 (by positivity)
      have h4 : |s.re - 1| * (L*t) ≤ (Real.sqrt (Real.log L)/L) * (L*x₀) := by
        apply mul_le_mul hσ1 (by nlinarith [ht.2, hLpos]) (by positivity) (by positivity)
      have h5 : (Real.sqrt (Real.log L)/L) * (L*x₀) = Real.sqrt (Real.log L)*x₀ := by
        field_simp
      rw [h5] at h4
      calc (1 - s.re) * (L*t) ≤ |s.re - 1| * (L*t) := h2
        _ ≤ Real.sqrt (Real.log L) * x₀ := h4
        _ ≤ Real.sqrt (Real.log L0) * x₀ := by
            apply mul_le_mul_of_nonneg_right hsqrtmono hx₀.le
        _ = x₀ * Real.sqrt (Real.log L0) := by ring
    calc Real.exp ((1 - s.re)*(L*t)) * |f t|
        ≤ Real.exp (x₀ * Real.sqrt (Real.log L0)) * Kf := by
          apply mul_le_mul (Real.exp_le_exp.mpr h1) (hKf t ht0) (abs_nonneg _)
          positivity
      _ = Kf * Real.exp (x₀ * Real.sqrt (Real.log L0)) := by ring
  have hcont : ContinuousOn (fun _ : ℝ => Kf * Real.exp (x₀ * Real.sqrt (Real.log L0)))
      (Set.uIcc (0:ℝ) x₀) := continuousOn_const
  have h := intervalIntegral.norm_integral_le_of_norm_le hx₀.le hpt hcont.intervalIntegrable
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h
  have h2 : ‖(L:ℂ) * (∫ t in (0:ℝ)..x₀,
        Complex.exp (-(((s-1) * L : ℂ) * (t:ℂ))) * ((f t:ℝ):ℂ))‖
      = L * ‖∫ t in (0:ℝ)..x₀,
        Complex.exp (-(((s-1) * L : ℂ) * (t:ℂ))) * ((f t:ℝ):ℂ)‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hLpos.le]
  rw [h2]
  calc L * ‖∫ t in (0:ℝ)..x₀,
        Complex.exp (-(((s-1) * L : ℂ) * (t:ℂ))) * ((f t:ℝ):ℂ)‖
      ≤ L * (x₀ * (Kf * Real.exp (x₀ * Real.sqrt (Real.log L0)))) :=
        mul_le_mul_of_nonneg_left h hLpos.le
    _ ≤ L0 * Kf * x₀ * Real.exp (x₀ * Real.sqrt (Real.log L0)) := by
        have h1 : 0 ≤ x₀ * (Kf * Real.exp (x₀ * Real.sqrt (Real.log L0))) := by positivity
        calc L * (x₀ * (Kf * Real.exp (x₀ * Real.sqrt (Real.log L0))))
            ≤ L0 * (x₀ * (Kf * Real.exp (x₀ * Real.sqrt (Real.log L0)))) :=
              mul_le_mul_of_nonneg_right hle h1
          _ = L0 * Kf * x₀ * Real.exp (x₀ * Real.sqrt (Real.log L0)) := by ring


/-- The character-free smoothed von Mangoldt sum differs from the main term by `O(log²L)`. -/
private theorem full_sum_bound (x₀ B : ℝ) (hx₀ : 0 < x₀) {f : ℝ → ℝ}
    (hcont : ContinuousOn f (Set.Ici 0)) (hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0)
    (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ {L : ℝ} (hL : 2 ≤ L) (s : ℂ),
      |s.re - 1| ≤ Real.sqrt (Real.log L) / L → |s.im| ≤ 10 * L →
      ‖(∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * ((n:ℂ)^s)⁻¹ *
            ((f (Real.log n / L) : ℝ) : ℂ))
        - ((L : ℝ) : ℂ) * (∫ t in (0:ℝ)..x₀,
            (Complex.exp (-(((s - 1) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)))‖
          ≤ C * (Real.log L)^2 := by
  obtain ⟨Kf, hKf0, hKf⟩ := exists_abs_bound_of_contOn_support hcont hsupp
  obtain ⟨Kd, hKd0, hKd⟩ := exists_deriv_bound hx₀ hf2 hBnd
  obtain ⟨c, Cc, hc, hCc, hpsi⟩ := Commons.NumberTheory.Zeta.chebyshev_psi_sub_id_exp_uniform
  have hC2pos : 0 < Real.log 4 + 5 := by
    have := Real.log_pos (by norm_num : (1:ℝ) < 4); linarith
  set B0 : ℝ := 1024 / c^2 with hB0def
  have hB0pos : 0 < B0 := by rw [hB0def]; positivity
  have hsqrtB0 : Real.sqrt B0 = 32 / c := by
    rw [hB0def]
    rw [show (1024:ℝ)/c^2 = (32/c)^2 by field_simp; ring]
    exact Real.sqrt_sq (by positivity)
  -- ============ eventual conditions ============
  have hEvA : ∀ᶠ L : ℝ in Filter.atTop, Real.exp 1 ≤ L := Filter.eventually_ge_atTop _
  have hEvB : ∀ᶠ L : ℝ in Filter.atTop, Real.log 2 ≤ B0 * (Real.log L)^2 := by
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (Real.sqrt (Real.log 2 / B0))]
      with L hL
    have h1 : Real.log 2 / B0 ≤ (Real.log L)^2 := by
      have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hL 2
      rwa [Real.sq_sqrt (div_nonneg hlog2 hB0pos.le)] at h2
    rw [div_le_iff₀ hB0pos] at h1
    nlinarith [h1]
  have hEvC : ∀ᶠ L : ℝ in Filter.atTop, 2 * B0 * (Real.log L)^2 ≤ L * x₀ := by
    have h := tendsto_log_pow_div_self 2
    have h1 : ∀ᶠ L : ℝ in Filter.atTop, (Real.log L)^2 / L < x₀ / (2*B0) :=
      Filter.Tendsto.eventually_lt_const (by positivity) h
    filter_upwards [h1, Filter.eventually_ge_atTop (1:ℝ)] with L h1 hL1
    have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL1
    rw [div_lt_iff₀ hLp] at h1
    have h2 : (x₀/(2*B0)) * (2*B0) = x₀ := by field_simp
    nlinarith [h1, h2, hB0pos]
  have hEvD : ∀ᶠ L : ℝ in Filter.atTop,
      (Real.sqrt (Real.log L) / L) * (B0 * (Real.log L)^2) ≤ 1 := by
    have h := tendsto_log_pow_div_self 3
    have h1 : ∀ᶠ L : ℝ in Filter.atTop, (Real.log L)^3 / L < 1/B0 :=
      Filter.Tendsto.eventually_lt_const (by positivity) h
    filter_upwards [h1, Real.tendsto_log_atTop.eventually_ge_atTop (1:ℝ),
      Filter.eventually_ge_atTop (1:ℝ)] with L h1 hlog1 hL1
    have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL1
    have hlog0 : 0 ≤ Real.log L := le_trans zero_le_one hlog1
    have hsqrt_le : Real.sqrt (Real.log L) ≤ Real.log L := by
      have h2 : Real.log L ≤ (Real.log L)^2 := by nlinarith
      calc Real.sqrt (Real.log L) ≤ Real.sqrt ((Real.log L)^2) := Real.sqrt_le_sqrt h2
        _ = Real.log L := Real.sqrt_sq hlog0
    have h3 : Real.sqrt (Real.log L) * (Real.log L)^2 ≤ (Real.log L)^3 := by
      calc Real.sqrt (Real.log L) * (Real.log L)^2 ≤ (Real.log L) * (Real.log L)^2 :=
            mul_le_mul_of_nonneg_right hsqrt_le (by positivity)
        _ = (Real.log L)^3 := by ring
    have h4 : B0 * (Real.log L)^3 / L ≤ 1 := by
      rw [div_le_iff₀ hLp]
      have h5 := h1
      rw [div_lt_iff₀ hLp] at h5
      have h6 : B0 * (1/B0) = 1 := by field_simp
      nlinarith [h5, h6, hB0pos]
    calc (Real.sqrt (Real.log L) / L) * (B0 * (Real.log L)^2)
        = B0 * (Real.sqrt (Real.log L) * (Real.log L)^2) / L := by ring
      _ ≤ B0 * (Real.log L)^3 / L := by
          apply div_le_div_of_nonneg_right _ hLp.le
          exact mul_le_mul_of_nonneg_left h3 hB0pos.le
      _ ≤ 1 := h4
  have hEvE : ∀ᶠ L : ℝ in Filter.atTop,
      (Real.sqrt (Real.log L) / L) * Real.sqrt (L * x₀) ≤ c / 2 := by
    have h1 : ∀ᶠ L : ℝ in Filter.atTop, Real.log L / L < c^2/(4*x₀) := by
      have h := tendsto_log_pow_div_self 1
      have h2 : (fun L : ℝ => (Real.log L)^1 / L) = fun L : ℝ => Real.log L / L := by
        funext L; rw [pow_one]
      rw [h2] at h
      exact Filter.Tendsto.eventually_lt_const (by positivity) h
    filter_upwards [h1, Filter.eventually_ge_atTop (1:ℝ),
      Real.tendsto_log_atTop.eventually_ge_atTop 1] with L h1 hL1 hlog1
    have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL1
    have hlog0 : 0 ≤ Real.log L := le_trans zero_le_one hlog1
    have hLx0 : 0 ≤ L * x₀ := by positivity
    have hnn : 0 ≤ Real.sqrt (Real.log L) / L * Real.sqrt (L * x₀) := by positivity
    have hsq : (Real.sqrt (Real.log L) / L * Real.sqrt (L * x₀))^2 = x₀ * Real.log L / L := by
      rw [mul_pow, div_pow, Real.sq_sqrt hlog0, Real.sq_sqrt hLx0]
      field_simp
    have hc2 : 0 ≤ c/2 := by linarith
    have hsq2 : (Real.sqrt (Real.log L) / L * Real.sqrt (L * x₀))^2 ≤ (c/2)^2 := by
      rw [hsq, show (c/2)^2 = c^2/4 by ring]
      have h2 : x₀ * (Real.log L / L) ≤ x₀ * (c^2/(4*x₀)) :=
        mul_le_mul_of_nonneg_left h1.le hx₀.le
      have h3 : x₀ * (Real.log L / L) = x₀ * Real.log L / L := by ring
      have h4 : x₀ * (c^2/(4*x₀)) = c^2/4 := by field_simp
      rw [h3] at h2
      linarith [h2, h4]
    have h5 := sq_le_sq.mp hsq2
    rwa [abs_of_nonneg hnn, abs_of_nonneg hc2] at h5
  have hEvF : ∀ᶠ L : ℝ in Filter.atTop, (4/3 : ℝ) ≤ B0 * (Real.log L)^2 := by
    filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (Real.sqrt (4/(3*B0)))]
      with L hL
    have h1 : 4/(3*B0) ≤ (Real.log L)^2 := by
      have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hL 2
      rwa [Real.sq_sqrt (by positivity)] at h2
    have h1' : 4/3 / B0 ≤ (Real.log L)^2 := by
      have heq : 4/3 / B0 = 4/(3*B0) := by field_simp
      rwa [heq]
    rw [div_le_iff₀ hB0pos] at h1'
    nlinarith [h1']
  have hEvG : ∀ᶠ L : ℝ in Filter.atTop, Real.sqrt (Real.log L) / L ≤ 1/2 := by
    have h := tendsto_log_rpow_div_self (1/2)
    have h1 : ∀ᶠ L : ℝ in Filter.atTop, (Real.log L)^(1/2:ℝ) / L < 1/2 :=
      Filter.Tendsto.eventually_lt_const (by norm_num) h
    filter_upwards [h1] with L h1
    rw [Real.sqrt_eq_rpow]
    exact le_of_lt h1
  have hEv : ∀ᶠ L : ℝ in Filter.atTop,
      Real.exp 1 ≤ L ∧ Real.log 2 ≤ B0 * (Real.log L)^2 ∧
      2 * B0 * (Real.log L)^2 ≤ L * x₀ ∧
      (Real.sqrt (Real.log L) / L) * (B0 * (Real.log L)^2) ≤ 1 ∧
      (Real.sqrt (Real.log L) / L) * Real.sqrt (L * x₀) ≤ c / 2 ∧
      (4/3 : ℝ) ≤ B0 * (Real.log L)^2 ∧
      Real.sqrt (Real.log L) / L ≤ 1/2 :=
    hEvA.and (hEvB.and (hEvC.and (hEvD.and (hEvE.and (hEvF.and hEvG)))))
  obtain ⟨L0₀, hL0₀⟩ := Filter.eventually_atTop.mp hEv
  set L0 : ℝ := max L0₀ 2 with hL0def
  have hL0ge2 : 2 ≤ L0 := le_max_right _ _
  have hL0pos : 0 < L0 := by linarith
  have hL0 : ∀ L : ℝ, L0 ≤ L →
      Real.exp 1 ≤ L ∧ Real.log 2 ≤ B0 * (Real.log L)^2 ∧
      2 * B0 * (Real.log L)^2 ≤ L * x₀ ∧
      (Real.sqrt (Real.log L) / L) * (B0 * (Real.log L)^2) ≤ 1 ∧
      (Real.sqrt (Real.log L) / L) * Real.sqrt (L * x₀) ≤ c / 2 ∧
      (4/3 : ℝ) ≤ B0 * (Real.log L)^2 ∧
      Real.sqrt (Real.log L) / L ≤ 1/2 :=
    fun L hL => hL0₀ L (le_trans (le_max_left _ _) hL)
  clear hEvA hEvB hEvC hEvD hEvE hEvF hEvG hEv hL0₀
  -- ============ the constant ============
  set A1 : ℝ := (200*(Real.log 4+5) + 4) * Kf * (4 + B0) with hA1def
  set A2 : ℝ := 4 * (Cc * Kf) with hA2def
  set A3 : ℝ := 4 * (Cc * (11*Kf + Kd) * x₀) with hA3def
  set A4 : ℝ := 4 * Kf with hA4def
  set A5 : ℝ := 4 * (Kf * (Real.log 4+5) * Real.exp (L0*x₀)) with hA5def
  set A6 : ℝ := 4 * (L0 * Kf * x₀ * Real.exp (x₀ * Real.sqrt (Real.log L0))) with hA6def
  set C : ℝ := A1 + 2*A2 + A3 + A4 + A5 + A6 + 1 with hCdef
  have hA1nn : 0 ≤ A1 := by
    rw [hA1def]
    exact mul_nonneg (mul_nonneg (by linarith [hC2pos]) hKf0) (by linarith [hB0pos])
  have hA2nn : 0 ≤ A2 := by
    rw [hA2def]; exact mul_nonneg (by norm_num) (mul_nonneg hCc.le hKf0)
  have hA3nn : 0 ≤ A3 := by
    rw [hA3def]
    exact mul_nonneg (by norm_num)
      (mul_nonneg (mul_nonneg hCc.le (by linarith [hKf0, hKd0])) hx₀.le)
  have hA4nn : 0 ≤ A4 := by rw [hA4def]; positivity
  have hA5nn : 0 ≤ A5 := by
    rw [hA5def]
    exact mul_nonneg (by norm_num)
      (mul_nonneg (mul_nonneg hKf0 (le_of_lt hC2pos)) (le_of_lt (Real.exp_pos _)))
  have hA6nn : 0 ≤ A6 := by
    rw [hA6def]
    exact mul_nonneg (by norm_num)
      (mul_nonneg (mul_nonneg (mul_nonneg hL0pos.le hKf0) hx₀.le)
        (le_of_lt (Real.exp_pos _)))
  have hCpos : 0 < C := by rw [hCdef]; linarith
  refine ⟨C, hCpos, ?_⟩
  intro L hL s hσ1 hτ
  have hLpos : 0 < L := by linarith
  have hD4 : (1:ℝ)/4 ≤ (Real.log L)^2 := by
    have h1 : (1:ℝ)/2 ≤ Real.log L := by
      have h2 : Real.log 2 ≤ Real.log L := Real.log_le_log (by norm_num) hL
      have h3 := Real.log_two_gt_d9
      linarith
    nlinarith
  have hDnn : (0:ℝ) ≤ (Real.log L)^2 := by positivity
  -- write the tsum as a finite sum of `gfun`s
  have ha0 : (fun n : ℕ =>
      ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * ((n:ℂ)^s)⁻¹) 0 = 0 := by simp
  have hsum_eq :
      (∑ n ∈ Finset.Icc 1 ⌊Real.exp (L*x₀)⌋₊,
          ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * ((n:ℂ)^s)⁻¹ *
            ((f (Real.log n / L) : ℝ) : ℂ))
      = ∑ n ∈ Finset.Icc 1 ⌊Real.exp (L*x₀)⌋₊,
          ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * gfun L s f (n:ℝ) := by
    refine Finset.sum_congr rfl (fun n hn => ?_)
    rw [Finset.mem_Icc] at hn
    have hn0 : n ≠ 0 := by omega
    rw [gfun]
    have h1 : ((n:ℂ)^s)⁻¹ = Complex.exp (-s * ((Real.log (n:ℝ) : ℝ) : ℂ)) := by
      rw [Complex.ofReal_log (Nat.cast_nonneg n)]
      exact (exp_neg_log_eq_cpow_inv hn0).symm
    rw [h1]
    ring
  rw [tsum_mul_supp hLpos hsupp
      (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * ((n:ℂ)^s)⁻¹) ha0, hsum_eq]
  by_cases hLc : L < L0
  · -- ============ crude case `L < L0` ============
    have hσlo : (1:ℝ)/2 ≤ s.re := by
      have h2 : Real.sqrt (Real.log L)/L ≤ 1/2 := sqrt_log_div_self_le_half hL
      have h3 : |s.re - 1| ≤ 1/2 := le_trans hσ1 h2
      have h4 := (abs_le.mp h3).1
      linarith
    have hσpos : 0 < s.re := by linarith
    have hMle : ((⌊Real.exp (L*x₀)⌋₊ : ℕ):ℝ) ≤ Real.exp (L*x₀) :=
      Nat.floor_le (Real.exp_pos _).le
    have hsum := norm_sum_vonMangoldt_gfun_crude hx₀ hLpos (le_of_lt hLc) hMle hσpos hKf
    have hint := norm_main_integral_le hx₀ hLpos (le_of_lt hLc) hσ1 hKf
    have hbdcrude : ‖(∑ n ∈ Finset.Icc 1 ⌊Real.exp (L*x₀)⌋₊,
          ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * gfun L s f (n:ℝ))
        - ((L : ℝ) : ℂ) * (∫ t in (0:ℝ)..x₀,
            Complex.exp (-(((s - 1) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ))‖
        ≤ Kf * (Real.log 4 + 5) * Real.exp (L0 * x₀)
          + L0 * Kf * x₀ * Real.exp (x₀ * Real.sqrt (Real.log L0)) := by
      calc ‖(∑ n ∈ Finset.Icc 1 ⌊Real.exp (L*x₀)⌋₊,
            ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * gfun L s f (n:ℝ))
          - ((L : ℝ) : ℂ) * (∫ t in (0:ℝ)..x₀,
              (Complex.exp (-(((s - 1) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)))‖
          ≤ ‖(∑ n ∈ Finset.Icc 1 ⌊Real.exp (L*x₀)⌋₊,
              ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * gfun L s f (n:ℝ))‖
            + ‖((L : ℝ) : ℂ) * (∫ t in (0:ℝ)..x₀,
              (Complex.exp (-(((s - 1) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)))‖ := norm_sub_le _ _
        _ ≤ _ := add_le_add hsum hint
    have hD1 : 1 ≤ 4 * (Real.log L)^2 := by linarith [hD4]
    have hb1 : Kf * (Real.log 4 + 5) * Real.exp (L0 * x₀) ≤ A5 * (Real.log L)^2 := by
      have hBv : 0 ≤ Kf * (Real.log 4 + 5) * Real.exp (L0 * x₀) :=
        mul_nonneg (mul_nonneg hKf0 (le_of_lt hC2pos)) (le_of_lt (Real.exp_pos _))
      rw [hA5def]
      nlinarith only [hD1, hBv]
    have hb2 : L0 * Kf * x₀ * Real.exp (x₀ * Real.sqrt (Real.log L0))
        ≤ A6 * (Real.log L)^2 := by
      have hBv : 0 ≤ L0 * Kf * x₀ * Real.exp (x₀ * Real.sqrt (Real.log L0)) :=
        mul_nonneg (mul_nonneg (mul_nonneg hL0pos.le hKf0) hx₀.le) (le_of_lt (Real.exp_pos _))
      rw [hA6def]
      nlinarith only [hD1, hBv]
    refine le_trans hbdcrude ?_
    calc Kf * (Real.log 4 + 5) * Real.exp (L0 * x₀)
          + L0 * Kf * x₀ * Real.exp (x₀ * Real.sqrt (Real.log L0))
        ≤ A5 * (Real.log L)^2 + A6 * (Real.log L)^2 := add_le_add hb1 hb2
      _ ≤ C * (Real.log L)^2 := by
          rw [hCdef]
          nlinarith only [hA1nn, hA2nn, hA3nn, hA4nn, hA5nn, hA6nn, hD4, sq_nonneg (Real.log L)]
  · -- ============ main case `L0 ≤ L` ============
    have hL0L : L0 ≤ L := not_lt.mp hLc
    rcases hL0 L hL0L with ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7⟩
    set A : ℝ := Real.exp (B0 * (Real.log L)^2) with hAdef
    set M : ℕ := ⌊Real.exp (L*x₀)⌋₊ with hMdef
    set NA : ℕ := ⌊A⌋₊ with hNAdef
    have hlogL0 : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
    have hA2 : 2 ≤ A := by
      rw [hAdef]
      calc (2:ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
        _ ≤ Real.exp (B0 * (Real.log L)^2) := Real.exp_le_exp.mpr hc2
    have hNA2 : 2 ≤ NA := by rw [hNAdef]; exact Nat.le_floor hA2
    have hNA1 : 1 ≤ NA := by omega
    have hApos : 0 < A := by rw [hAdef]; positivity
    have hNAleA : (NA:ℝ) ≤ A := by
      rw [hNAdef]; exact Nat.floor_le hApos.le
    have hMgeA : A ≤ (M:ℝ) := by
      rw [hMdef]
      have h1 : A^2 ≤ Real.exp (L*x₀) := by
        rw [hAdef, sq, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        linarith only [hc3]
      have h3 : A + 1 ≤ Real.exp (L*x₀) := by
        nlinarith only [hA2, h1]
      have h5 : A ≤ ((⌊Real.exp (L*x₀)⌋₊ : ℕ):ℝ) := by
        have h6 : Real.exp (L*x₀) - 1 < ((⌊Real.exp (L*x₀)⌋₊ : ℕ):ℝ) := by
          have := Nat.lt_floor_add_one (Real.exp (L*x₀)); linarith
        linarith
      exact h5
    have hNAM : NA ≤ M := by
      have h5 : (NA:ℝ) ≤ (M:ℝ) := le_trans hNAleA hMgeA
      exact_mod_cast h5
    have hM1 : 1 ≤ M := le_trans hNA1 hNAM
    have hMM : (M:ℝ) ≤ Real.exp (L*x₀) := by
      rw [hMdef]; exact Nat.floor_le (Real.exp_pos _).le
    have hMM2 : 2 ≤ (M:ℝ) := by
      have h5 : (2:ℝ) ≤ (NA:ℝ) := by exact_mod_cast hNA2
      have h6 : (NA:ℝ) ≤ (M:ℝ) := by exact_mod_cast hNAM
      linarith
    have hNAe : (NA:ℝ) ≤ Real.exp (L*x₀) := le_trans hNAleA (le_trans hMgeA hMM)
    have hlogNAle : Real.log (NA:ℝ) ≤ B0 * (Real.log L)^2 := by
      have h1 : Real.log A = B0 * (Real.log L)^2 := by rw [hAdef, Real.log_exp]
      calc Real.log (NA:ℝ) ≤ Real.log A := Real.log_le_log (by positivity) hNAleA
        _ = B0 * (Real.log L)^2 := h1
    have hNAgeAhalf : A/2 ≤ (NA:ℝ) := by
      have h5 : A - 1 < (NA:ℝ) := by
        rw [hNAdef]; have := Nat.lt_floor_add_one A; linarith
      linarith [hA2]
    have hlogNAge : B0 * (Real.log L)^2 - 1 ≤ Real.log (NA:ℝ) := by
      have h1 : Real.log (A/2) ≤ Real.log (NA:ℝ) :=
        Real.log_le_log (by positivity) hNAgeAhalf
      have h2 : Real.log (A/2) = B0*(Real.log L)^2 - Real.log 2 := by
        rw [Real.log_div (by positivity) (by norm_num), hAdef, Real.log_exp]
      have h3 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
      linarith
    -- ============ `σ` facts ============
    have hσlo : (1:ℝ)/2 ≤ s.re := by
      have h2 : |s.re - 1| ≤ 1/2 := le_trans hσ1 hc7
      have h3 := (abs_le.mp h2).1
      linarith
    have hσhi : s.re ≤ 3/2 := by
      have h2 : |s.re - 1| ≤ 1/2 := le_trans hσ1 hc7
      have h3 := (abs_le.mp h2).2
      linarith
    have hσpos : 0 < s.re := by linarith
    have hσ2 : s.re ≤ 2 := by linarith
    have hη0 : 0 ≤ Real.sqrt (Real.log L) / L := by positivity
    -- widened: `|Im s| ≤ 10L` and `1/2 ≤ Re s ≤ 3/2`, so `‖s‖ ≤ 1 + 10L ≤ 11L`
    have hnorm_s : ‖s‖ ≤ 11 * L := by
      have h1 : ‖s‖^2 ≤ (11*L)^2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        have h2 := (abs_le.mp hτ).1
        have h3 := (abs_le.mp hτ).2
        nlinarith only [hσlo, hσhi, h2, h3, hL]
      have h2 := sq_le_sq.mp h1
      rwa [abs_of_nonneg (norm_nonneg s), abs_of_nonneg (by linarith : (0:ℝ) ≤ 11*L)] at h2
    have hcondNA : (1 - s.re) * Real.log (NA:ℝ) ≤ 1 := by
      by_cases h : 1 - s.re ≤ 0
      · have h3 : 0 ≤ Real.log (NA:ℝ) := Real.log_nonneg (by exact_mod_cast hNA1)
        nlinarith only [h3, h, hc]
      · push_neg at h
        have h2 : 1 - s.re ≤ Real.sqrt (Real.log L)/L := by
          have := (abs_le.mp hσ1).1; linarith
        have h3 : 0 ≤ Real.log (NA:ℝ) := Real.log_nonneg (by exact_mod_cast hNA1)
        calc (1 - s.re) * Real.log (NA:ℝ)
            ≤ (Real.sqrt (Real.log L)/L) * (B0*(Real.log L)^2) :=
              mul_le_mul h2 hlogNAle h3 hη0
          _ ≤ 1 := hc4
    -- ============ piecewise bounds ============
    have hp1 : ‖(∑ n ∈ Finset.Icc 1 NA,
          ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * gfun L s f (n:ℝ))
        - (∫ t in (1:ℝ)..(NA:ℝ), gfun L s f t)‖
        ≤ (200 * (Real.log 4 + 5) + 4) * Kf * (1 + Real.log (NA:ℝ)) := by
      have h1 := norm_sum_vonMangoldt_gfun_le (N := NA) hLpos hNA1 hσpos hσ2 hcondNA hKf
      have h2 := norm_integral_gfun_le (N := NA) hLpos hNA1 hσpos hcondNA hKf
      calc ‖(∑ n ∈ Finset.Icc 1 NA,
            ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * gfun L s f (n:ℝ))
          - (∫ t in (1:ℝ)..(NA:ℝ), gfun L s f t)‖
          ≤ ‖(∑ n ∈ Finset.Icc 1 NA,
              ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * gfun L s f (n:ℝ))‖
            + ‖(∫ t in (1:ℝ)..(NA:ℝ), gfun L s f t)‖ := norm_sub_le _ _
        _ ≤ (200 * (Real.log 4 + 5) + 4) * Kf * (1 + Real.log (NA:ℝ)) := by
            linarith [h1, h2]
    have hlogNAbd : 1 + Real.log (NA:ℝ) ≤ (4 + B0) * (Real.log L)^2 := by
      linarith only [hlogNAle, hD4]
    have hp1' : ‖(∑ n ∈ Finset.Icc 1 NA,
          ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * gfun L s f (n:ℝ))
        - (∫ t in (1:ℝ)..(NA:ℝ), gfun L s f t)‖ ≤ A1 * (Real.log L)^2 := by
      have hc5' : 0 ≤ (200 * (Real.log 4 + 5) + 4) * Kf :=
        mul_nonneg (by linarith [hC2pos]) hKf0
      have hstep : (200 * (Real.log 4 + 5) + 4) * Kf * (1 + Real.log (NA:ℝ))
          ≤ (200 * (Real.log 4 + 5) + 4) * Kf * ((4 + B0) * (Real.log L)^2) :=
        mul_le_mul_of_nonneg_left hlogNAbd hc5'
      have hA1eq : (200 * (Real.log 4 + 5) + 4) * Kf * ((4 + B0) * (Real.log L)^2)
          = A1 * (Real.log L)^2 := by rw [hA1def]; ring
      linarith [hp1, hstep, hA1eq]
    have h1σM : (1 - s.re) * Real.sqrt (Real.log (M:ℝ)) ≤ c/2 := by
      by_cases h : 1 - s.re ≤ 0
      · have h4 : 0 ≤ Real.sqrt (Real.log (M:ℝ)) := Real.sqrt_nonneg _
        nlinarith only [h4, h, hc]
      · push_neg at h
        have h2 : 1 - s.re ≤ Real.sqrt (Real.log L)/L := by
          have := (abs_le.mp hσ1).1; linarith
        have h3 : Real.sqrt (Real.log (M:ℝ)) ≤ Real.sqrt (L*x₀) := by
          apply Real.sqrt_le_sqrt
          calc Real.log (M:ℝ) ≤ Real.log (Real.exp (L*x₀)) :=
                Real.log_le_log (by positivity) hMM
            _ = L*x₀ := Real.log_exp _
        have h4 : 0 ≤ Real.sqrt (Real.log (M:ℝ)) := Real.sqrt_nonneg _
        calc (1 - s.re) * Real.sqrt (Real.log (M:ℝ))
            ≤ (Real.sqrt (Real.log L)/L) * Real.sqrt (L*x₀) :=
              mul_le_mul h2 h3 h4 hη0
          _ ≤ c/2 := hc5
    have hp2 : ‖(((Chebyshev.psi (M:ℝ) - (M:ℝ) : ℝ)) : ℂ) * gfun L s f (M:ℝ)‖
        ≤ Cc*Kf :=
      norm_R_gfun_le hc hCc.le (by linarith : (1:ℝ) ≤ (M:ℝ))
        (hpsi (M:ℝ) hMM2) h1σM
        (hKf _ (div_nonneg (Real.log_nonneg (by linarith [hMM2] : (1:ℝ) ≤ (M:ℝ))) hLpos.le))
    have h1σNA : (1 - s.re) * Real.sqrt (Real.log (NA:ℝ)) ≤ c/2 := by
      by_cases h : 1 - s.re ≤ 0
      · have h4 : 0 ≤ Real.sqrt (Real.log (NA:ℝ)) := Real.sqrt_nonneg _
        nlinarith only [h4, h, hc]
      · push_neg at h
        have h2 : 1 - s.re ≤ Real.sqrt (Real.log L)/L := by
          have := (abs_le.mp hσ1).1; linarith
        have h3 : Real.sqrt (Real.log (NA:ℝ)) ≤ Real.sqrt (L*x₀) := by
          apply Real.sqrt_le_sqrt
          calc Real.log (NA:ℝ) ≤ Real.log (Real.exp (L*x₀)) :=
                Real.log_le_log (by positivity) hNAe
            _ = L*x₀ := Real.log_exp _
        have h4 : 0 ≤ Real.sqrt (Real.log (NA:ℝ)) := Real.sqrt_nonneg _
        calc (1 - s.re) * Real.sqrt (Real.log (NA:ℝ))
            ≤ (Real.sqrt (Real.log L)/L) * Real.sqrt (L*x₀) :=
              mul_le_mul h2 h3 h4 hη0
          _ ≤ c/2 := hc5
    have hp3 : ‖(((Chebyshev.psi (NA:ℝ) - (NA:ℝ) : ℝ)) : ℂ) * gfun L s f (NA:ℝ)‖
        ≤ Cc*Kf :=
      norm_R_gfun_le hc hCc.le (by linarith : (1:ℝ) ≤ (NA:ℝ))
        (hpsi (NA:ℝ) (by exact_mod_cast hNA2 : (2:ℝ) ≤ (NA:ℝ))) h1σNA
        (hKf _ (div_nonneg (Real.log_nonneg (by exact_mod_cast hNA1 : (1:ℝ) ≤ (NA:ℝ))) hLpos.le))
    have hp2' : ‖(((Chebyshev.psi (M:ℝ) - (M:ℝ) : ℝ)) : ℂ) * gfun L s f (M:ℝ)‖
        ≤ A2 * (Real.log L)^2 := by
      rw [hA2def]
      have : (4:ℝ) * (Cc*Kf) * (Real.log L)^2 = 4*(Cc*Kf)*(Real.log L)^2 := by ring
      linarith only [hp2, mul_le_mul_of_nonneg_left hD4 (mul_nonneg hCc.le hKf0)]
    have hp3' : ‖(((Chebyshev.psi (NA:ℝ) - (NA:ℝ) : ℝ)) : ℂ) * gfun L s f (NA:ℝ)‖
        ≤ A2 * (Real.log L)^2 := by
      rw [hA2def]
      linarith only [hp3, mul_le_mul_of_nonneg_left hD4 (mul_nonneg hCc.le hKf0)]
    have hbig_t : ∀ t ∈ Set.Icc (NA:ℝ) (M:ℝ), (4/c) * Real.log L ≤ Real.sqrt (Real.log t) := by
      intro t ht
      have htNA : (NA:ℝ) ≤ t := ht.1
      have h1 : B0*(Real.log L)^2 - 1 ≤ Real.log t :=
        le_trans hlogNAge (Real.log_le_log (by positivity) htNA)
      have h6 : Real.sqrt (B0*(Real.log L)^2) = (32/c)*Real.log L := by
        rw [Real.sqrt_mul hB0pos.le, Real.sqrt_sq hlogL0, hsqrtB0]
      have h7 : (1/2)*Real.sqrt (B0*(Real.log L)^2) ≤ Real.sqrt (B0*(Real.log L)^2 - 1) := by
        have h8 : ((1/2)*Real.sqrt (B0*(Real.log L)^2))^2 ≤ B0*(Real.log L)^2 - 1 := by
          rw [mul_pow, Real.sq_sqrt (by positivity)]
          linarith only [hc6]
        calc (1/2)*Real.sqrt (B0*(Real.log L)^2)
            = Real.sqrt (((1/2)*Real.sqrt (B0*(Real.log L)^2))^2) := by
              rw [Real.sqrt_sq (by positivity)]
          _ ≤ Real.sqrt (B0*(Real.log L)^2 - 1) := Real.sqrt_le_sqrt h8
      calc (4/c) * Real.log L ≤ (16/c) * Real.log L := by
            apply mul_le_mul_of_nonneg_right _ hlogL0
            exact div_le_div_of_nonneg_right (by norm_num) hc.le
        _ = (1/2)*((32/c)*Real.log L) := by ring
        _ = (1/2)*Real.sqrt (B0*(Real.log L)^2) := by rw [h6]
        _ ≤ Real.sqrt (B0*(Real.log L)^2 - 1) := h7
        _ ≤ Real.sqrt (Real.log t) := Real.sqrt_le_sqrt h1
    have hσ_t : ∀ t ∈ Set.Icc (NA:ℝ) (M:ℝ),
        (1 - s.re) * Real.sqrt (Real.log t) ≤ c/2 := by
      intro t ht
      by_cases h : 1 - s.re ≤ 0
      · have h4 : 0 ≤ Real.sqrt (Real.log t) := Real.sqrt_nonneg _
        nlinarith only [h4, h, hc]
      · push_neg at h
        have h2 : 1 - s.re ≤ Real.sqrt (Real.log L)/L := by
          have := (abs_le.mp hσ1).1; linarith
        have h3 : Real.sqrt (Real.log t) ≤ Real.sqrt (L*x₀) := by
          apply Real.sqrt_le_sqrt
          calc Real.log t ≤ Real.log (Real.exp (L*x₀)) :=
                Real.log_le_log (by linarith [ht.1]) (le_trans ht.2 hMM)
            _ = L*x₀ := Real.log_exp _
        have h4 : 0 ≤ Real.sqrt (Real.log t) := Real.sqrt_nonneg _
        calc (1 - s.re) * Real.sqrt (Real.log t)
            ≤ (Real.sqrt (Real.log L)/L) * Real.sqrt (L*x₀) :=
              mul_le_mul h2 h3 h4 hη0
          _ ≤ c/2 := hc5
    have hR : ∀ t ∈ Set.Icc (NA:ℝ) (M:ℝ),
        |Chebyshev.psi t - t| * t^(-s.re) ≤ Cc * L^(-2:ℝ) := by
      intro t ht
      have ht2 : 2 ≤ t := le_trans (by exact_mod_cast hNA2 : (2:ℝ) ≤ (NA:ℝ)) ht.1
      exact psi_sub_id_mul_rpow_le hc hCc.le (by linarith : 1 < L) ht2
        (hσ_t t ht) (hbig_t t ht) (hpsi t ht2)
    have hp4 := norm_integral_R_le (m := NA) (n := M) hx₀ (by linarith : 1 < L) hNA1 hNAM hMM
      hf2 hKf hKd hCc.le hLpos hR
    have hp4' : ‖∫ t in (NA:ℝ)..(M:ℝ),
        (((Chebyshev.psi t - t : ℝ)) : ℂ) * deriv (gfun L s f) t‖
        ≤ Cc*(11*Kf+Kd)*x₀ := by
      refine le_trans hp4 ?_
      have hAineq : ‖s‖*Kf + Kd ≤ 11*L*Kf + Kd := by
        have hh := mul_le_mul_of_nonneg_right hnorm_s hKf0
        linarith
      have hLpow : L^(-2:ℝ) * L = L^(-1:ℝ) := by
        calc L^(-2:ℝ) * L = L^(-2:ℝ) * L^(1:ℝ) := by rw [Real.rpow_one]
          _ = L^((-2:ℝ) + 1) := by rw [Real.rpow_add hLpos]
          _ = L^(-1:ℝ) := by congr 1; norm_num
      have hkey : Cc * L^(-2:ℝ) * (‖s‖*Kf+Kd) * (L*x₀)
          = Cc * (‖s‖*Kf+Kd) * (L^(-2:ℝ) * L) * x₀ := by ring
      rw [hkey, hLpow, Real.rpow_neg_one]
      have h3 : (‖s‖*Kf+Kd) * L⁻¹ ≤ 11*Kf + Kd := by
        have h4 : (‖s‖*Kf+Kd) * L⁻¹ = (‖s‖*Kf+Kd) / L := by rw [div_eq_mul_inv]
        rw [h4, div_le_iff₀ hLpos]
        nlinarith only [hAineq, hKd0, hL]
      calc Cc * (‖s‖*Kf+Kd) * L⁻¹ * x₀ = Cc * ((‖s‖*Kf+Kd) * L⁻¹) * x₀ := by ring
        _ ≤ Cc * (11*Kf+Kd) * x₀ := by
            apply mul_le_mul_of_nonneg_right _ hx₀.le
            exact mul_le_mul_of_nonneg_left h3 hCc.le
    have hp4'' : ‖∫ t in (NA:ℝ)..(M:ℝ),
        (((Chebyshev.psi t - t : ℝ)) : ℂ) * deriv (gfun L s f) t‖
        ≤ A3 * (Real.log L)^2 := by
      rw [hA3def]
      linarith only [hp4', mul_le_mul_of_nonneg_left hD4 (mul_nonneg (mul_nonneg hCc.le
        (add_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 11) hKf0) hKd0)) hx₀.le)]
    have hp5 : ‖∫ t in (M:ℝ)..Real.exp (L*x₀), gfun L s f t‖ ≤ Kf := by
      have hpt : ∀ᵐ t ∂volume, t ∈ Set.Ioc (M:ℝ) (Real.exp (L*x₀)) →
          ‖gfun L s f t‖ ≤ Kf := by
        filter_upwards with t ht
        rw [Set.mem_Ioc] at ht
        have ht1 : (1:ℝ) ≤ t := le_trans (by linarith [hMM2] : (1:ℝ) ≤ (M:ℝ)) (le_of_lt ht.1)
        have h2 := norm_gfun_le (s := s) ht1
          (hKf _ (div_nonneg (Real.log_nonneg ht1) hLpos.le))
        have h3 : t^(-s.re) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht1 (by linarith)
        calc ‖gfun L s f t‖ ≤ Kf * t^(-s.re) := h2
          _ ≤ Kf * 1 := mul_le_mul_of_nonneg_left h3 hKf0
          _ = Kf := by ring
      have hcont' : ContinuousOn (fun _ : ℝ => Kf) (Set.uIcc (M:ℝ) (Real.exp (L*x₀))) :=
        continuousOn_const
      have h := intervalIntegral.norm_integral_le_of_norm_le hMM hpt hcont'.intervalIntegrable
      rw [intervalIntegral.integral_const, smul_eq_mul] at h
      have h2 : Real.exp (L*x₀) - (M:ℝ) ≤ 1 := by
        have h3 := Nat.lt_floor_add_one (Real.exp (L*x₀))
        rw [hMdef]
        linarith
      calc ‖∫ t in (M:ℝ)..Real.exp (L*x₀), gfun L s f t‖ ≤ (Real.exp (L*x₀) - (M:ℝ)) * Kf := h
        _ ≤ 1 * Kf := mul_le_mul_of_nonneg_right h2 hKf0
        _ = Kf := by ring
    have hp5' : ‖∫ t in (M:ℝ)..Real.exp (L*x₀), gfun L s f t‖ ≤ A4 * (Real.log L)^2 := by
      rw [hA4def]
      linarith only [hp5, mul_le_mul_of_nonneg_left hD4 hKf0]
    have hdecomp := sum_decomp (M := M) (NA := NA) hx₀ (by linarith : 1 < L) hM1 hNA1 hNAM
      hMM hNAe hcont hf2 (le_of_lt hσpos) hKf hKd
    rw [hdecomp]
    have hb1 : ‖(∑ n ∈ Finset.Icc 1 NA,
            ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * gfun L s f (n:ℝ)
          - (∫ t in (1:ℝ)..(NA:ℝ), gfun L s f t))
        + (((Chebyshev.psi (M:ℝ) - (M:ℝ) : ℝ)) : ℂ) * gfun L s f (M:ℝ)
        - (((Chebyshev.psi (NA:ℝ) - (NA:ℝ) : ℝ)) : ℂ) * gfun L s f (NA:ℝ)
        - (∫ t in (NA:ℝ)..(M:ℝ), (((Chebyshev.psi t - t : ℝ)) : ℂ) * deriv (gfun L s f) t)
        - (∫ t in (M:ℝ)..Real.exp (L*x₀), gfun L s f t)‖
        ≤ A1 * (Real.log L)^2 + A2 * (Real.log L)^2 + A2 * (Real.log L)^2
          + A3 * (Real.log L)^2 + A4 * (Real.log L)^2 := by
      have h1 : ‖(∑ n ∈ Finset.Icc 1 NA,
            ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * gfun L s f (n:ℝ)
          - (∫ t in (1:ℝ)..(NA:ℝ), gfun L s f t))
        + (((Chebyshev.psi (M:ℝ) - (M:ℝ) : ℝ)) : ℂ) * gfun L s f (M:ℝ)
        - (((Chebyshev.psi (NA:ℝ) - (NA:ℝ) : ℝ)) : ℂ) * gfun L s f (NA:ℝ)
        - (∫ t in (NA:ℝ)..(M:ℝ), (((Chebyshev.psi t - t : ℝ)) : ℂ) * deriv (gfun L s f) t)
        - (∫ t in (M:ℝ)..Real.exp (L*x₀), gfun L s f t)‖
        ≤ ‖(∑ n ∈ Finset.Icc 1 NA,
            ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * gfun L s f (n:ℝ)
          - (∫ t in (1:ℝ)..(NA:ℝ), gfun L s f t))
        + (((Chebyshev.psi (M:ℝ) - (M:ℝ) : ℝ)) : ℂ) * gfun L s f (M:ℝ)
        - (((Chebyshev.psi (NA:ℝ) - (NA:ℝ) : ℝ)) : ℂ) * gfun L s f (NA:ℝ)
        - (∫ t in (NA:ℝ)..(M:ℝ), (((Chebyshev.psi t - t : ℝ)) : ℂ) * deriv (gfun L s f) t)‖
        + ‖(∫ t in (M:ℝ)..Real.exp (L*x₀), gfun L s f t)‖ := norm_sub_le _ _
      have h2 : ‖(∑ n ∈ Finset.Icc 1 NA,
            ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * gfun L s f (n:ℝ)
          - (∫ t in (1:ℝ)..(NA:ℝ), gfun L s f t))
        + (((Chebyshev.psi (M:ℝ) - (M:ℝ) : ℝ)) : ℂ) * gfun L s f (M:ℝ)
        - (((Chebyshev.psi (NA:ℝ) - (NA:ℝ) : ℝ)) : ℂ) * gfun L s f (NA:ℝ)
        - (∫ t in (NA:ℝ)..(M:ℝ), (((Chebyshev.psi t - t : ℝ)) : ℂ) * deriv (gfun L s f) t)‖
        ≤ ‖(∑ n ∈ Finset.Icc 1 NA,
            ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * gfun L s f (n:ℝ)
          - (∫ t in (1:ℝ)..(NA:ℝ), gfun L s f t))
        + (((Chebyshev.psi (M:ℝ) - (M:ℝ) : ℝ)) : ℂ) * gfun L s f (M:ℝ)
        - (((Chebyshev.psi (NA:ℝ) - (NA:ℝ) : ℝ)) : ℂ) * gfun L s f (NA:ℝ)‖
        + ‖(∫ t in (NA:ℝ)..(M:ℝ), (((Chebyshev.psi t - t : ℝ)) : ℂ) * deriv (gfun L s f) t)‖ :=
        norm_sub_le _ _
      have h3 : ‖(∑ n ∈ Finset.Icc 1 NA,
            ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * gfun L s f (n:ℝ)
          - (∫ t in (1:ℝ)..(NA:ℝ), gfun L s f t))
        + (((Chebyshev.psi (M:ℝ) - (M:ℝ) : ℝ)) : ℂ) * gfun L s f (M:ℝ)
        - (((Chebyshev.psi (NA:ℝ) - (NA:ℝ) : ℝ)) : ℂ) * gfun L s f (NA:ℝ)‖
        ≤ ‖(∑ n ∈ Finset.Icc 1 NA,
            ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * gfun L s f (n:ℝ)
          - (∫ t in (1:ℝ)..(NA:ℝ), gfun L s f t))
        + (((Chebyshev.psi (M:ℝ) - (M:ℝ) : ℝ)) : ℂ) * gfun L s f (M:ℝ)‖
        + ‖(((Chebyshev.psi (NA:ℝ) - (NA:ℝ) : ℝ)) : ℂ) * gfun L s f (NA:ℝ)‖ :=
        norm_sub_le _ _
      have h4 : ‖(∑ n ∈ Finset.Icc 1 NA,
            ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * gfun L s f (n:ℝ)
          - (∫ t in (1:ℝ)..(NA:ℝ), gfun L s f t))
        + (((Chebyshev.psi (M:ℝ) - (M:ℝ) : ℝ)) : ℂ) * gfun L s f (M:ℝ)‖
        ≤ ‖(∑ n ∈ Finset.Icc 1 NA,
            ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * gfun L s f (n:ℝ)
          - (∫ t in (1:ℝ)..(NA:ℝ), gfun L s f t))‖
        + ‖(((Chebyshev.psi (M:ℝ) - (M:ℝ) : ℝ)) : ℂ) * gfun L s f (M:ℝ)‖ :=
        norm_add_le _ _
      linarith [h1, h2, h3, h4, hp1', hp2', hp3', hp4'', hp5']
    refine le_trans hb1 ?_
    rw [hCdef]
    linarith only [mul_nonneg (add_nonneg (add_nonneg hA5nn hA6nn) zero_le_one) hDnn]


/-- `‖(n^s)^{-1}‖ = n^{-Re s}` for `1 ≤ n`. -/
private lemma norm_cpow_inv {s : ℂ} {n : ℕ} (hn : 1 ≤ n) :
    ‖((n:ℂ)^s)⁻¹‖ = (n:ℝ)^(-s.re) := by
  have hn0 : (n:ℕ) ≠ 0 := by omega
  have hnpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  rw [← exp_neg_log_eq_cpow_inv hn0, Complex.norm_exp]
  have hgoal : (-s * Complex.log (n:ℂ)).re = -s.re * Real.log n := by
    rw [Complex.mul_re]
    have harg : ((n:ℂ)).arg = 0 := by
      rw [← Complex.ofReal_natCast n]
      exact Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg n)
    rw [Complex.neg_re, Complex.neg_im, Complex.log_re, Complex.log_im, harg,
      Complex.norm_natCast]
    ring
  rw [hgoal, Real.rpow_def_of_pos hnpos]
  congr 1
  ring

/-- **Heath-Brown (1992), Lemma 5.3**, *wide range* (principal character, complex `s`).

Identical to `Commons.NumberTheory.Linnik.lemma5_3` except that the imaginary range is
`|Im s| ≤ 10 L` instead of `|Im s| ≤ L`.  In the proof the imaginary part of `s` is used
in exactly one place: to bound `‖s‖ ≤ 2L`.  With the wider range one gets `‖s‖ ≤ 11L`
(and `|Re s| ≤ 3/2 ≤ L`), which only multiplies the constant by an absolute factor; all
the analytic estimates below are absolute-value estimates in `Re s` alone, so they are
unaffected. -/
theorem lemma5_3_wide (x₀ B : ℝ) (hx₀ : 0 < x₀) (hB : 0 ≤ B) :
    ∀ {f : ℝ → ℝ}
      (hcont : ContinuousOn f (Set.Ici 0)) (hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0)
      (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
      (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B),
      ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] {L : ℝ} (hL : 2 ≤ L),
      ∀ s : ℂ, |s.re - 1| ≤ Real.sqrt (Real.log L) / L → |s.im| ≤ 10 * L →
        ‖(∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) *
              (((1 : DirichletCharacter ℂ q) (n : ZMod q) : ℂ)) / (n : ℂ) ^ s *
              ((f (Real.log n / L) : ℝ) : ℂ))
         - ((L : ℝ) : ℂ) * ((∫ t in (0:ℝ)..x₀,
              Complex.exp (-(((s - 1) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)))‖
        ≤ C * ((q.primeFactors.card : ℝ) + (Real.log L) ^ 2) := by
  intro f hcont hsupp hf2 hBnd
  obtain ⟨Kf, hKf0, hKf⟩ := exists_abs_bound_of_contOn_support hcont hsupp
  obtain ⟨C0, hC0pos, hC0⟩ := full_sum_bound x₀ B hx₀ hcont hsupp hf2 hBnd
  refine ⟨max 1 (max C0 (2*Kf)), lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro q hq L hL s hσ1 hτ
  have hqpos : 0 < q := Nat.pos_of_ne_zero hq.out
  have hLpos : 0 < L := by linarith
  have hω : 0 ≤ (q.primeFactors.card : ℝ) := by positivity
  have hDnn : 0 ≤ (Real.log L)^2 := by positivity
  have hηhalf : Real.sqrt (Real.log L)/L ≤ 1/2 := sqrt_log_div_self_le_half hL
  have hσlo : (1:ℝ)/2 ≤ s.re := by
    have h2 : |s.re - 1| ≤ 1/2 := le_trans hσ1 hηhalf
    have h3 := (abs_le.mp h2).1
    linarith
  have hσpos : 0 < s.re := by linarith
  -- rewrite both `tsum`s as finite sums
  have ha10 : (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * ((n:ℂ)^s)⁻¹) 0 = 0 := by
    simp
  have ha20 : (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
      (((1 : DirichletCharacter ℂ q) (n : ZMod q) : ℂ)) / (n : ℂ) ^ s) 0 = 0 := by simp
  have htsum_full := tsum_mul_supp (x₀ := x₀) hLpos hsupp
    (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * ((n:ℂ)^s)⁻¹) ha10
  have htsum_chi := tsum_mul_supp (x₀ := x₀) hLpos hsupp
    (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
      (((1 : DirichletCharacter ℂ q) (n : ZMod q) : ℂ)) / (n : ℂ) ^ s) ha20
  rw [htsum_chi]
  -- the full sum bound
  have hFULL : ‖(∑ n ∈ Finset.Icc 1 ⌊Real.exp (L*x₀)⌋₊,
          ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * ((n:ℂ)^s)⁻¹ *
            ((f (Real.log n / L) : ℝ) : ℂ))
        - ((L : ℝ) : ℂ) * (∫ t in (0:ℝ)..x₀,
          (Complex.exp (-(((s - 1) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)))‖
        ≤ C0 * (Real.log L)^2 := by
    have h := hC0 hL s hσ1 hτ
    rw [htsum_full] at h
    exact h
  -- the non-coprime correction
  have hcorr : ‖(∑ n ∈ Finset.Icc 1 ⌊Real.exp (L*x₀)⌋₊,
            (ArithmeticFunction.vonMangoldt n : ℂ) *
              (((1 : DirichletCharacter ℂ q) (n : ZMod q) : ℂ)) / (n : ℂ)^s *
              ((f (Real.log n / L) : ℝ) : ℂ))
        - (∑ n ∈ Finset.Icc 1 ⌊Real.exp (L*x₀)⌋₊,
            ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * ((n:ℂ)^s)⁻¹ *
              ((f (Real.log n / L) : ℝ) : ℂ))‖ ≤ 2 * Kf * (q.primeFactors.card : ℝ) := by
    rw [← Finset.sum_sub_distrib]
    have hterm : ∀ n ∈ Finset.Icc 1 ⌊Real.exp (L*x₀)⌋₊,
        ‖(ArithmeticFunction.vonMangoldt n : ℂ) *
              (((1 : DirichletCharacter ℂ q) (n : ZMod q) : ℂ)) / (n : ℂ)^s *
              ((f (Real.log n / L) : ℝ) : ℂ)
            - ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * ((n:ℂ)^s)⁻¹ *
              ((f (Real.log n / L) : ℝ) : ℂ)‖
        ≤ (ArithmeticFunction.vonMangoldt n) * Kf * (n:ℝ)^(-s.re) := by
      intro n hn
      rw [Finset.mem_Icc] at hn
      have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn.1
      have hftermle : |f (Real.log n / L)| ≤ Kf :=
        hKf _ (div_nonneg (Real.log_nonneg hn1) hLpos.le)
      have hchi_norm : ‖(ArithmeticFunction.vonMangoldt n : ℂ) *
              (((1 : DirichletCharacter ℂ q) (n : ZMod q) : ℂ)) / (n : ℂ)^s
            - ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * ((n:ℂ)^s)⁻¹‖
          ≤ (ArithmeticFunction.vonMangoldt n) * (n:ℝ)^(-s.re) := by
        by_cases hcop : Nat.Coprime n q
        · have hχ : (((1 : DirichletCharacter ℂ q) (n : ZMod q) : ℂ)) = 1 :=
            MulChar.one_apply ((ZMod.isUnit_iff_coprime n q).mpr hcop)
          rw [hχ]
          have hzero : (ArithmeticFunction.vonMangoldt n : ℂ) * 1 / (n : ℂ)^s
              - ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * ((n:ℂ)^s)⁻¹ = 0 := by
            rw [div_eq_mul_inv]; ring
          rw [hzero, norm_zero]
          exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
            (Real.rpow_nonneg (by positivity) _)
        · have hχ : (((1 : DirichletCharacter ℂ q) (n : ZMod q) : ℂ)) = 0 := by
            have h1 : ¬ IsUnit ((n : ZMod q)) := by
              rw [ZMod.isUnit_iff_coprime]; exact hcop
            simpa using MulChar.map_nonunit (1 : DirichletCharacter ℂ q) h1
          rw [hχ]
          have hval : (ArithmeticFunction.vonMangoldt n : ℂ) * 0 / (n : ℂ)^s
              - ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * ((n:ℂ)^s)⁻¹
              = -(((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * ((n:ℂ)^s)⁻¹) := by ring
          rw [hval, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, norm_cpow_inv hn.1]
      have hfac : (ArithmeticFunction.vonMangoldt n : ℂ) *
              (((1 : DirichletCharacter ℂ q) (n : ZMod q) : ℂ)) / (n : ℂ)^s *
              ((f (Real.log n / L) : ℝ) : ℂ)
            - ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * ((n:ℂ)^s)⁻¹ *
              ((f (Real.log n / L) : ℝ) : ℂ)
          = ((ArithmeticFunction.vonMangoldt n : ℂ) *
              (((1 : DirichletCharacter ℂ q) (n : ZMod q) : ℂ)) / (n : ℂ)^s
            - ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * ((n:ℂ)^s)⁻¹) *
              ((f (Real.log n / L) : ℝ) : ℂ) := by ring
      rw [hfac, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc ‖(ArithmeticFunction.vonMangoldt n : ℂ) *
              (((1 : DirichletCharacter ℂ q) (n : ZMod q) : ℂ)) / (n : ℂ)^s
            - ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * ((n:ℂ)^s)⁻¹‖
            * |f (Real.log n / L)|
          ≤ ((ArithmeticFunction.vonMangoldt n) * (n:ℝ)^(-s.re)) * Kf :=
            mul_le_mul hchi_norm hftermle (abs_nonneg _)
              (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
                (Real.rpow_nonneg (by positivity) _))
        _ = (ArithmeticFunction.vonMangoldt n) * Kf * (n:ℝ)^(-s.re) := by ring
    have hsub : (Finset.Icc 1 ⌊Real.exp (L*x₀)⌋₊).filter (fun n => ¬ Nat.Coprime n q)
        ⊆ Finset.Icc 1 ⌊Real.exp (L*x₀)⌋₊ := Finset.filter_subset _ _
    have heq : (∑ n ∈ Finset.Icc 1 ⌊Real.exp (L*x₀)⌋₊,
          ‖(ArithmeticFunction.vonMangoldt n : ℂ) *
              (((1 : DirichletCharacter ℂ q) (n : ZMod q) : ℂ)) / (n : ℂ)^s *
              ((f (Real.log n / L) : ℝ) : ℂ)
            - ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * ((n:ℂ)^s)⁻¹ *
              ((f (Real.log n / L) : ℝ) : ℂ)‖)
        = ∑ n ∈ (Finset.Icc 1 ⌊Real.exp (L*x₀)⌋₊).filter (fun n => ¬ Nat.Coprime n q),
          ‖(ArithmeticFunction.vonMangoldt n : ℂ) *
              (((1 : DirichletCharacter ℂ q) (n : ZMod q) : ℂ)) / (n : ℂ)^s *
              ((f (Real.log n / L) : ℝ) : ℂ)
            - ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * ((n:ℂ)^s)⁻¹ *
              ((f (Real.log n / L) : ℝ) : ℂ)‖ := by
      refine (Finset.sum_subset hsub ?_).symm
      intro n hnIcc hnNot
      rw [Finset.mem_filter] at hnNot
      push_neg at hnNot
      have hcop : Nat.Coprime n q := hnNot hnIcc
      have hχ : (((1 : DirichletCharacter ℂ q) (n : ZMod q) : ℂ)) = 1 :=
        MulChar.one_apply ((ZMod.isUnit_iff_coprime n q).mpr hcop)
      have hzero : (ArithmeticFunction.vonMangoldt n : ℂ) * 1 / (n : ℂ)^s *
            ((f (Real.log n / L) : ℝ) : ℂ)
          - ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * ((n:ℂ)^s)⁻¹ *
            ((f (Real.log n / L) : ℝ) : ℂ) = 0 := by
        rw [div_eq_mul_inv]; ring
      rw [hχ, hzero, norm_zero]
    refine le_trans (norm_sum_le _ _) ?_
    rw [heq]
    refine le_trans (Finset.sum_le_sum (fun n hn => hterm n (Finset.mem_of_mem_filter n hn))) ?_
    rw [show (∑ n ∈ (Finset.Icc 1 ⌊Real.exp (L*x₀)⌋₊).filter (fun n => ¬ Nat.Coprime n q),
          (ArithmeticFunction.vonMangoldt n) * Kf * (n:ℝ)^(-s.re))
        = Kf * ∑ n ∈ (Finset.Icc 1 ⌊Real.exp (L*x₀)⌋₊).filter (fun n => ¬ Nat.Coprime n q),
          (ArithmeticFunction.vonMangoldt n) * (n:ℝ)^(-s.re) from by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun n _ => by ring)]
    refine le_trans (mul_le_mul_of_nonneg_left (bad_sum_bound hqpos hσpos) hKf0) ?_
    have h4 : (q.primeFactors.card : ℝ) / s.re ≤ 2 * (q.primeFactors.card : ℝ) := by
      rw [div_le_iff₀ hσpos]
      nlinarith [hω, hσlo]
    nlinarith [mul_le_mul_of_nonneg_left h4 hKf0]
  -- assembly
  have hsplit : (∑ n ∈ Finset.Icc 1 ⌊Real.exp (L*x₀)⌋₊,
            (ArithmeticFunction.vonMangoldt n : ℂ) *
              (((1 : DirichletCharacter ℂ q) (n : ZMod q) : ℂ)) / (n : ℂ)^s *
              ((f (Real.log n / L) : ℝ) : ℂ))
        - ((L : ℝ) : ℂ) * ((∫ t in (0:ℝ)..x₀,
              Complex.exp (-(((s - 1) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)))
      = ((∑ n ∈ Finset.Icc 1 ⌊Real.exp (L*x₀)⌋₊,
            (ArithmeticFunction.vonMangoldt n : ℂ) *
              (((1 : DirichletCharacter ℂ q) (n : ZMod q) : ℂ)) / (n : ℂ)^s *
              ((f (Real.log n / L) : ℝ) : ℂ))
          - (∑ n ∈ Finset.Icc 1 ⌊Real.exp (L*x₀)⌋₊,
            ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * ((n:ℂ)^s)⁻¹ *
              ((f (Real.log n / L) : ℝ) : ℂ)))
        + ((∑ n ∈ Finset.Icc 1 ⌊Real.exp (L*x₀)⌋₊,
            ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * ((n:ℂ)^s)⁻¹ *
              ((f (Real.log n / L) : ℝ) : ℂ))
          - ((L : ℝ) : ℂ) * (∫ t in (0:ℝ)..x₀,
              (Complex.exp (-(((s - 1) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)))) := by ring
  rw [hsplit]
  have hAeq : ((L : ℝ) : ℂ) * ((∫ t in (0:ℝ)..x₀,
        Complex.exp (-(((s - 1) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)))
      = ((L : ℝ) : ℂ) * (∫ t in (0:ℝ)..x₀,
          (Complex.exp (-(((s - 1) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ))) := rfl
  rw [hAeq]
  have hCm : 2*Kf ≤ max 1 (max C0 (2*Kf)) :=
    le_trans (le_max_right C0 (2*Kf)) (le_max_right 1 (max C0 (2*Kf)))
  have hC0m : C0 ≤ max 1 (max C0 (2*Kf)) :=
    le_trans (le_max_left C0 (2*Kf)) (le_max_right 1 (max C0 (2*Kf)))
  refine le_trans (norm_add_le _ _) ?_
  refine le_trans (add_le_add hcorr hFULL) ?_
  nlinarith [hω, hDnn, hCm, hC0m]

end
end Work.LinnikAreas
