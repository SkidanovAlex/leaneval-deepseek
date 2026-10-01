/-
# HB Lemma 5.3 at a complex point of height `≥ 1`

The target statement (`PrincipalHeight`) and the pieces it is assembled from:
* `exists_abs_bound_of_contOn_support`, `exists_deriv_bound`: the two bounds on `f` and `f'`;
* `KsumRe`: the real `Ksum` is the real part of the complex sum of HB Lemma 5.3 (finite support);
* `AbsorbOmega`: `ω(q) + (log log q)² = o(log q)`;
* `ThresholdExpSqrtLog`: `(1+√(log L))·exp(√(log L)·x₀)` is dominated by `ε L`;
* `IntegralBound`: one integration by parts bounds `∫₀^{x₀} exp(-(z t)) f`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.CertData
import Submission.Work.LinnikAreas.lemma5_3_wide

set_option maxHeartbeats 4000000

open scoped BigOperators
open MeasureTheory

noncomputable section

namespace Work.ZeroFreeTables.OffAxis.RectC

/-! ### Bounds for `f` and `f'` -/

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

/-- `ContDiffOn ℝ 2` on an open interval gives a two-sided derivative at every
interior point. -/
private lemma hasDerivAt_of_contDiffOn {x₀ : ℝ} {f : ℝ → ℝ}
    (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀)) :
    ∀ t ∈ Set.Ioo (0:ℝ) x₀, HasDerivAt f (deriv f t) t := by
  intro t ht
  have hca : ContDiffAt ℝ 2 f t := hf2.contDiffAt (Ioo_mem_nhds ht.1 ht.2)
  exact (hca.differentiableAt (by norm_num)).hasDerivAt

/-! ### The real `Ksum` is the real part of the complex sum -/

/-- For real `a g` and complex `w v`: `ℜ(a·(w/v)·g) = a·ℜ(w/v)·g`. -/
private lemma re_mul_div_mul (a g : ℝ) (w v : ℂ) :
    (((a:ℂ) * w / v) * (g:ℂ)).re = a * (w/v).re * g := by
  have h1 : ((a:ℂ) * w / v) = (a:ℂ) * (w/v) := by
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc]
  rw [h1]
  have h2 : ((a:ℂ) * (w/v) * (g:ℂ)).re = a * ((w/v) * (g:ℂ)).re := by
    rw [mul_assoc, Complex.re_ofReal_mul]
  have h3 : ((w/v) * (g:ℂ)).re = (w/v).re * g := by
    rw [mul_comm (w/v) ((g:ℂ)), Complex.re_ofReal_mul]; ring
  rw [h2, h3]; ring

/-- The real `Ksum` of HB §5 equals the real part of the complex sum of HB Lemma 5.3:
both sums are finite by the support hypothesis. -/
private lemma KsumRe {q : ℕ} [NeZero q] {f : ℝ → ℝ} {L x₀ : ℝ} (hL : 0 < L)
    (hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0) (s : ℂ) :
    Ksum q f L s (1 : DirichletCharacter ℂ q)
      = (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) *
          (((1 : DirichletCharacter ℂ q) (n : ZMod q) : ℂ)) / (n : ℂ) ^ s *
          ((f (Real.log n / L) : ℝ) : ℂ)).re := by
  set N : ℕ := ⌊Real.exp (L * x₀)⌋₊ + 1 with hNdef
  have hsupp_f : ∀ n : ℕ, N ≤ n → f (Real.log n / L) = 0 := by
    intro n hn
    have h2 : ⌊Real.exp (L*x₀)⌋₊ + 1 ≤ n := by omega
    have h1 : ((⌊Real.exp (L*x₀)⌋₊ : ℕ) : ℝ) + 1 ≤ (n:ℝ) := by exact_mod_cast h2
    have h3 := Nat.lt_floor_add_one (Real.exp (L*x₀))
    have hexp : Real.exp (L*x₀) < (n:ℝ) := by linarith
    have hnpos : (0:ℝ) < n := by linarith
    have h4 : L * x₀ < Real.log (n:ℝ) := by
      rw [← Real.log_exp (L*x₀)]
      exact Real.log_lt_log (Real.exp_pos _) hexp
    apply hsupp
    rw [le_div_iff₀ hL]
    linarith
  have hzero_r : ∀ n : ℕ, n ∉ Finset.Icc 1 N →
      (ArithmeticFunction.vonMangoldt n : ℝ) *
        (((1 : DirichletCharacter ℂ q) (n : ZMod q) / (n : ℂ) ^ s).re) *
        f (Real.log n / L) = 0 := by
    intro n hn
    by_cases hn1 : n < 1
    · have hn0 : n = 0 := by omega
      subst hn0
      simp
    · have hnN : N ≤ n := by
        by_contra h
        exact hn (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      rw [hsupp_f n hnN, mul_zero]
  have hzero_c : ∀ n : ℕ, n ∉ Finset.Icc 1 N →
      (ArithmeticFunction.vonMangoldt n : ℂ) *
        (((1 : DirichletCharacter ℂ q) (n : ZMod q) : ℂ)) / (n : ℂ) ^ s *
        ((f (Real.log n / L) : ℝ) : ℂ) = 0 := by
    intro n hn
    by_cases hn1 : n < 1
    · have hn0 : n = 0 := by omega
      subst hn0
      simp
    · have hnN : N ≤ n := by
        by_contra h
        exact hn (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      rw [hsupp_f n hnN]
      simp
  rw [Ksum, tsum_eq_sum (s := Finset.Icc 1 N) hzero_r,
    tsum_eq_sum (s := Finset.Icc 1 N) hzero_c, Complex.re_sum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  have h := re_mul_div_mul (ArithmeticFunction.vonMangoldt n) (f (Real.log n / L))
    ((1 : DirichletCharacter ℂ q) (n : ZMod q)) ((n:ℂ)^s)
  exact h.symm

/-! ### The numerical error budget -/

/-- For `b ≥ 2` and `q ≥ 1`: `ω(q) ≤ b + log_b q`. -/
private lemma card_primeFactors_le_add_log {b q : ℕ} (hb : 1 < b) (hq : q ≠ 0) :
    q.primeFactors.card ≤ b + Nat.log b q := by
  set s : Finset ℕ := q.primeFactors.filter (fun p => b ≤ p) with hs
  set s' : Finset ℕ := q.primeFactors.filter (fun p => p < b) with hs'
  have hsplit : s'.card + s.card = q.primeFactors.card := by
    rw [← Finset.card_filter_add_card_filter_not (p := fun p => p < b) (s := q.primeFactors)]
    have : q.primeFactors.filter (fun p => ¬ p < b) = s := by
      rw [hs]
      refine Finset.filter_congr ?_
      intro p _
      exact not_lt
    rw [this, hs']
  have h1 : s'.card ≤ b := by
    have hsub : s' ⊆ Finset.range b := by
      intro p hp
      rw [hs', Finset.mem_filter] at hp
      exact Finset.mem_range.mpr hp.2
    calc s'.card ≤ (Finset.range b).card := Finset.card_le_card hsub
      _ = b := Finset.card_range b
  have h2 : s.card ≤ Nat.log b q := by
    apply Nat.le_log_of_pow_le hb
    have hbpow : (b : ℕ) ^ s.card = ∏ x ∈ s, b := (Finset.prod_const b).symm
    rw [hbpow]
    have hle1 : ∏ x ∈ s, b ≤ ∏ x ∈ s, x := by
      refine Finset.prod_le_prod₀ (fun x _ => Nat.zero_le _) ?_
      intro x hx
      rw [hs, Finset.mem_filter] at hx
      exact hx.2
    have hle2 : ∏ x ∈ s, x ≤ q := by
      have hsub : s ⊆ q.primeFactors := by
        rw [hs]; exact Finset.filter_subset _ _
      have hsplit2 : ∏ x ∈ q.primeFactors, x
          = (∏ x ∈ s, x) * (∏ x ∈ q.primeFactors \ s, x) := by
        rw [← Finset.prod_sdiff hsub]; ring
      have hqeq : ∏ x ∈ q.primeFactors, x ≤ q :=
        Nat.le_of_dvd (Nat.pos_of_ne_zero hq) (Nat.prod_primeFactors_dvd q)
      have hone : 1 ≤ ∏ x ∈ q.primeFactors \ s, x := by
        refine Finset.one_le_prod₀ ?_
        intro x hx
        rw [Finset.mem_sdiff] at hx
        exact Nat.Prime.one_le (Nat.prime_of_mem_primeFactors hx.1)
      nlinarith
    exact le_trans hle1 hle2
  omega

/-- `ω(q) = o(log q)`: for every `δ > 0` all sufficiently large `q` satisfy
`ω(q) ≤ δ log q`. -/
private theorem primeFactors_card_le_eps_log (δ : ℝ) (hδ : 0 < δ) :
    ∃ q₁ : ℕ, ∀ q : ℕ, q₁ ≤ q → (q.primeFactors.card : ℝ) ≤ δ * Real.log (q : ℝ) := by
  have h8 : (0:ℝ) < 8 / δ := by positivity
  set b : ℕ := ⌈Real.exp (8 / δ)⌉₊ + 2 with hbdef
  have hb1 : 1 < b := by omega
  have hlogb : 8 / δ ≤ Real.log b := by
    have hle : Real.exp (8/δ) ≤ (b : ℝ) := by
      have h1 : Real.exp (8/δ) ≤ ((⌈Real.exp (8/δ)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
      have h2 : ((⌈Real.exp (8/δ)⌉₊ : ℕ) : ℝ) ≤ (b : ℝ) := by
        rw [hbdef]; push_cast; linarith
      linarith
    calc 8 / δ = Real.log (Real.exp (8/δ)) := (Real.log_exp _).symm
      _ ≤ Real.log b := Real.log_le_log (Real.exp_pos _) hle
  refine ⟨⌈Real.exp (4 * (b : ℝ) / δ)⌉₊ + 1, ?_⟩
  intro q hq
  have hceilq : ((⌈Real.exp (4 * (b:ℝ) / δ)⌉₊ : ℕ) : ℝ) < (q : ℝ) := by
    have : (⌈Real.exp (4 * (b:ℝ) / δ)⌉₊ : ℕ) < q := by omega
    exact_mod_cast this
  have hqpos : 0 < q := by
    have : (0:ℕ) < ⌈Real.exp (4 * (b:ℝ) / δ)⌉₊ + 1 := by omega
    omega
  have hlogq : 4 * (b:ℝ) / δ ≤ Real.log q := by
    have hle : Real.exp (4 * (b:ℝ) / δ) ≤ (q : ℝ) := by
      have h1 : Real.exp (4 * (b:ℝ) / δ) ≤ ((⌈Real.exp (4 * (b:ℝ) / δ)⌉₊ : ℕ) : ℝ) :=
        Nat.le_ceil _
      linarith
    calc 4 * (b:ℝ) / δ = Real.log (Real.exp (4 * (b:ℝ) / δ)) := (Real.log_exp _).symm
      _ ≤ Real.log q := Real.log_le_log (Real.exp_pos _) hle
  have hlogqnonneg : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ q))
  have hcard := card_primeFactors_le_add_log hb1 hqpos.ne'
  have hcastcard : (q.primeFactors.card : ℝ) ≤ (b : ℝ) + (Nat.log b q : ℝ) := by
    exact_mod_cast hcard
  have hlogbq : (Nat.log b q : ℝ) ≤ Real.log (q:ℝ) / Real.log b := by
    have hpow : b ^ Nat.log b q ≤ q := Nat.pow_log_le_self b hqpos.ne'
    have hcast : ((b:ℝ)) ^ Nat.log b q ≤ (q:ℝ) := by exact_mod_cast hpow
    have h1 : Real.log ((b:ℝ) ^ Nat.log b q) ≤ Real.log q :=
      Real.log_le_log (by positivity) hcast
    rw [Real.log_pow] at h1
    rw [le_div_iff₀ (by linarith : (0:ℝ) < Real.log b)]
    linarith
  have hstep1 : Real.log (q:ℝ) / Real.log b ≤ (δ/8) * Real.log (q:ℝ) := by
    rw [div_le_iff₀ (by linarith : (0:ℝ) < Real.log b)]
    have hprod : (δ/8) * (8/δ) = (1:ℝ) := by field_simp
    have h1 : (δ/8) * (8/δ) ≤ (δ/8) * Real.log b :=
      mul_le_mul_of_nonneg_left hlogb (by positivity)
    rw [hprod] at h1
    nlinarith
  have hstep2 : (b:ℝ) ≤ (δ/4) * Real.log (q:ℝ) := by
    have h1 : (δ/4) * (4 * (b:ℝ)/δ) ≤ (δ/4) * Real.log q :=
      mul_le_mul_of_nonneg_left hlogq (by positivity)
    have h2 : (δ/4) * (4 * (b:ℝ)/δ) = (b:ℝ) := by field_simp
    linarith
  nlinarith [hcastcard, hlogbq, hstep1, hstep2, hlogqnonneg]

/-- `ω(q) + (log log q)² = o(log q)`: the error term of HB Lemma 5.3 is absorbed in
`ε log q` for large `q`. -/
private theorem AbsorbOmega (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
      C * ((q.primeFactors.card : ℝ) + (Real.log (Real.log (q : ℝ))) ^ 2)
        ≤ ε * Real.log (q : ℝ) := by
  set δ : ℝ := ε / (4 * C) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  obtain ⟨q₁, hq₁⟩ := primeFactors_card_le_eps_log δ hδpos
  set T : ℝ := 16 / δ with hTdef
  have hTpos : 0 < T := by rw [hTdef]; positivity
  refine ⟨max q₁ (⌈Real.exp (T^2 + 1)⌉₊ + 1), ?_⟩
  intro q hq
  have hq1 : q₁ ≤ q := le_trans (le_max_left _ _) hq
  have hq2 : ⌈Real.exp (T^2 + 1)⌉₊ + 1 ≤ q := le_trans (le_max_right _ _) hq
  have hω : (q.primeFactors.card : ℝ) ≤ δ * Real.log (q : ℝ) := hq₁ q hq1
  have hceil : Real.exp (T^2 + 1) ≤ (q : ℝ) := by
    have h1 : Real.exp (T^2+1) ≤ ((⌈Real.exp (T^2+1)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have h2 : ((⌈Real.exp (T^2+1)⌉₊ : ℕ) : ℝ) < (q:ℝ) := by
      have h3 : ⌈Real.exp (T^2+1)⌉₊ < q := by omega
      exact_mod_cast h3
    linarith
  have hlogq : T^2 + 1 ≤ Real.log (q:ℝ) := by
    calc T^2 + 1 = Real.log (Real.exp (T^2+1)) := (Real.log_exp _).symm
      _ ≤ Real.log q := Real.log_le_log (Real.exp_pos _) hceil
  have hlogq1 : 1 ≤ Real.log (q:ℝ) := by nlinarith [hlogq, sq_nonneg T]
  have hlogqpos : 0 < Real.log (q:ℝ) := by linarith
  have hTle : T ≤ Real.sqrt (Real.log (q:ℝ)) := by
    have h1 : Real.sqrt (T^2) ≤ Real.sqrt (Real.log q) :=
      Real.sqrt_le_sqrt (by nlinarith [hlogq])
    rwa [Real.sqrt_sq (le_of_lt hTpos)] at h1
  have h16 : 16 * Real.sqrt (Real.log (q:ℝ)) ≤ δ * Real.log (q:ℝ) := by
    have hδT : δ * T = 16 := by rw [hTdef]; field_simp
    have h2 : T * Real.sqrt (Real.log (q:ℝ))
        ≤ Real.sqrt (Real.log (q:ℝ)) * Real.sqrt (Real.log (q:ℝ)) :=
      mul_le_mul_of_nonneg_right hTle (Real.sqrt_nonneg _)
    calc 16 * Real.sqrt (Real.log (q:ℝ))
        = δ * (T * Real.sqrt (Real.log (q:ℝ))) := by rw [← hδT]; ring
      _ ≤ δ * (Real.sqrt (Real.log (q:ℝ)) * Real.sqrt (Real.log (q:ℝ))) :=
          mul_le_mul_of_nonneg_left h2 (le_of_lt hδpos)
      _ = δ * Real.log (q:ℝ) := by rw [Real.mul_self_sqrt (le_of_lt hlogqpos)]
  have hsq : (Real.log (Real.log (q:ℝ)))^2 ≤ δ * Real.log (q:ℝ) := by
    have hll : 0 ≤ Real.log (Real.log (q:ℝ)) := Real.log_nonneg hlogq1
    have hloglog : Real.log (Real.log (q:ℝ)) ≤ 4 * (Real.log (q:ℝ))^(1/4:ℝ) := by
      have h1 : Real.log (Real.log (q:ℝ)) ≤ (Real.log (q:ℝ))^(1/4:ℝ) / (1/4) :=
        Real.log_le_rpow_div (le_of_lt hlogqpos) (by norm_num)
      have h3 : (Real.log (q:ℝ))^(1/4:ℝ) / (1/4) = 4 * (Real.log (q:ℝ))^(1/4:ℝ) := by ring
      linarith [h1, h3]
    have hrpow : (Real.log (q:ℝ))^(1/4:ℝ) = Real.sqrt (Real.sqrt (Real.log (q:ℝ))) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (le_of_lt hlogqpos)]
      norm_num
    have h4 : (4 * (Real.log (q:ℝ))^(1/4:ℝ))^2 = 16 * Real.sqrt (Real.log (q:ℝ)) := by
      rw [hrpow, mul_pow, Real.sq_sqrt (Real.sqrt_nonneg _)]
      ring
    have h5 : (Real.log (Real.log (q:ℝ)))^2 ≤ (4 * (Real.log (q:ℝ))^(1/4:ℝ))^2 := by
      nlinarith [hloglog, hll, Real.rpow_nonneg (le_of_lt hlogqpos) (1/4:ℝ)]
    rw [h4] at h5
    linarith [h5, h16]
  have hsum : (q.primeFactors.card : ℝ) + (Real.log (Real.log (q:ℝ)))^2
      ≤ 2 * δ * Real.log (q:ℝ) := by linarith [hω, hsq]
  have hfinal : C * (2 * δ * Real.log (q:ℝ)) = (ε/2) * Real.log (q:ℝ) := by
    rw [hδdef]; field_simp; ring
  have hLnn : 0 ≤ Real.log (q:ℝ) := le_of_lt hlogqpos
  calc C * ((q.primeFactors.card : ℝ) + (Real.log (Real.log (q:ℝ)))^2)
      ≤ C * (2 * δ * Real.log (q:ℝ)) := mul_le_mul_of_nonneg_left hsum (le_of_lt hC)
    _ = (ε/2) * Real.log (q:ℝ) := hfinal
    _ ≤ ε * Real.log (q:ℝ) := by nlinarith [hLnn, hε]

/-! ### The subpolynomial threshold -/

/-- A fixed multiple of `(1 + √(log L))·exp (√(log L)·x₀)` is eventually dominated by
`ε·L`. -/
private theorem ThresholdExpSqrtLog (A x₀ ε : ℝ) (hA : 0 ≤ A) (hx₀ : 0 ≤ x₀) (hε : 0 < ε) :
    ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      A * (1 + Real.sqrt (Real.log L)) * Real.exp (Real.sqrt (Real.log L) * x₀) ≤ ε * L := by
  rcases eq_or_lt_of_le hA with hA0 | hApos
  · refine ⟨1, fun L hL => ?_⟩
    have hL0 : 0 ≤ L := by linarith
    simp only [← hA0, zero_mul]
    exact mul_nonneg hε.le hL0
  · set u₀ : ℝ := max 4 (max (x₀ + 2) (|Real.log A| + |Real.log ε| + 1)) with hu₀def
    refine ⟨Real.exp (u₀^2), fun L hL => ?_⟩
    have hLpos : 0 < L := lt_of_lt_of_le (Real.exp_pos _) hL
    have h4 : 4 ≤ u₀ := le_max_left _ _
    have hx0u : x₀ + 2 ≤ u₀ := le_trans (le_max_left _ _) (le_max_right _ _)
    have hlogu : |Real.log A| + |Real.log ε| + 1 ≤ u₀ :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    have hlogL : u₀^2 ≤ Real.log L := by
      rw [← Real.log_exp (u₀^2)]
      exact Real.log_le_log (Real.exp_pos _) hL
    have hlogLnn : 0 ≤ Real.log L := by nlinarith [sq_nonneg u₀, hlogL]
    set u : ℝ := Real.sqrt (Real.log L) with hu
    have hu_nonneg : 0 ≤ u := Real.sqrt_nonneg _
    have hu2 : u^2 = Real.log L := Real.sq_sqrt hlogLnn
    have huu₀ : u₀ ≤ u := by
      have h1 : u₀^2 ≤ u^2 := by rw [hu2]; exact hlogL
      nlinarith [h1, hu_nonneg, (by linarith : (0:ℝ) ≤ u₀)]
    have hu4 : 4 ≤ u := le_trans h4 huu₀
    have hux₀ : x₀ + 2 ≤ u := le_trans hx0u huu₀
    have hulog : |Real.log A| + |Real.log ε| + 1 ≤ u := le_trans hlogu huu₀
    have hkey1 : Real.log (1 + u) ≤ u := by
      have h1 : (0:ℝ) < 1 + u := by linarith
      have h2 := Real.log_le_sub_one_of_pos h1
      linarith
    have hkey2 : Real.log A - Real.log ε ≤ u := by
      have h1 : Real.log A ≤ |Real.log A| := le_abs_self _
      have h2 : -|Real.log ε| ≤ Real.log ε := neg_abs_le _
      linarith
    have hkey3 : Real.log A - Real.log ε ≤ u * (u - x₀ - 1) := by
      have h3 : 1 ≤ u - x₀ - 1 := by linarith
      nlinarith [hkey2, hu_nonneg, h3]
    have hkey : Real.log A + Real.log (1 + u) + u * x₀ ≤ Real.log ε + u^2 := by
      nlinarith [hkey1, hkey3]
    have h1u : (0:ℝ) < 1 + u := by linarith
    have hexp1 : Real.exp (Real.log A + Real.log (1 + u) + u * x₀)
        = A * (1 + u) * Real.exp (u * x₀) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_log hApos, Real.exp_log h1u] <;> ring
    have hexp2 : Real.exp (Real.log ε + u^2) = ε * L := by
      rw [Real.exp_add, Real.exp_log hε, hu2, Real.exp_log hLpos] <;> ring
    rw [← hexp1, ← hexp2]
    exact Real.exp_le_exp.mpr hkey

/-! ### One integration by parts -/

/-- `t ↦ -(z⁻¹)·exp (-(z t))` has derivative `exp (-(z t))`. -/
private lemma hasDerivAt_const_mul_exp_neg_mul (z : ℂ) (hz : z ≠ 0) (x : ℝ) :
    HasDerivAt (fun t : ℝ => -(z⁻¹) * Complex.exp (-(z * (t:ℂ))))
      (Complex.exp (-(z * (x:ℂ)))) x := by
  have a : HasDerivAt (fun y : ℂ => y * (-z)) (-z) (x:ℂ) := hasDerivAt_mul_const (-z)
  have b2 : HasDerivAt (Complex.exp ∘ fun y : ℂ => y * (-z))
      (Complex.exp ((x:ℂ) * (-z)) * (-z)) (x:ℂ) :=
    HasDerivAt.comp (x:ℂ) (Complex.hasDerivAt_exp ((x:ℂ) * (-z))) a
  have c : HasDerivAt (fun y : ℂ => (-(z⁻¹)) * Complex.exp (y * (-z)))
      ((-(z⁻¹)) * (Complex.exp ((x:ℂ) * (-z)) * (-z))) (x:ℂ) := b2.const_mul (-(z⁻¹))
  have d := c.comp_ofReal
  have hfun : (fun y : ℝ => (-(z⁻¹)) * Complex.exp (↑y * (-z)))
      = fun t : ℝ => -(z⁻¹) * Complex.exp (-(z * (t:ℂ))) := by
    funext t; congr 1; ring_nf
  rw [hfun] at d
  refine d.congr_deriv ?_
  have hz' : z⁻¹ * z = 1 := inv_mul_cancel₀ hz
  have harg : (x:ℂ) * (-z) = -(z * (x:ℂ)) := by ring
  rw [harg]
  calc (-(z⁻¹)) * (Complex.exp (-(z * (x:ℂ))) * (-z))
      = z⁻¹ * (Complex.exp (-(z * (x:ℂ))) * z) := by ring
    _ = (z⁻¹ * z) * Complex.exp (-(z * (x:ℂ))) := by ring
    _ = Complex.exp (-(z * (x:ℂ))) := by rw [hz']; ring

/-- One integration by parts bounds the Laplace transform of a `C¹` function vanishing at
`x₀`, for `|Im z| ≥ 1`. -/
private lemma IntegralBound {x₀ : ℝ} (hx₀ : 0 < x₀) {f : ℝ → ℝ} {z : ℂ}
    (hfcont : ContinuousOn f (Set.Icc (0:ℝ) x₀))
    (hfderiv : ∀ t ∈ Set.Ioo (0:ℝ) x₀, HasDerivAt f (deriv f t) t)
    (hfx₀ : f x₀ = 0)
    {Kf Kd : ℝ} (hKf : 0 ≤ Kf) (hKd : 0 ≤ Kd)
    (hbnd0 : |f 0| ≤ Kf)
    (hbndIcc : ∀ t ∈ Set.Icc (0:ℝ) x₀, |deriv f t| ≤ Kd)
    (hz : 1 ≤ |z.im|) :
    ‖∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t:ℂ))) * ((f t : ℝ) : ℂ)‖
      ≤ (Kf + Real.exp (|z.re| * x₀) * (x₀ * Kd)) / |z.im| := by
  have hzpos : 0 < |z.im| := lt_of_lt_of_le one_pos hz
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hz
    simp at hz
    linarith
  -- interval-integrability of the complexified derivative
  have hderiv_int : IntervalIntegrable (fun t : ℝ => ((deriv f t : ℝ) : ℂ)) volume (0:ℝ) x₀ := by
    rw [intervalIntegrable_iff]
    refine MeasureTheory.IntegrableOn.of_bound ?_ ?_ Kd ?_
    · rw [Set.uIoc_of_le hx₀.le, Real.volume_Ioc]
      exact ENNReal.ofReal_lt_top
    · exact (Complex.measurable_ofReal.comp (measurable_deriv f)).aestronglyMeasurable
    · rw [Set.uIoc_of_le hx₀.le, MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
      refine Filter.Eventually.of_forall (fun x hx => ?_)
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact hbndIcc x ⟨le_of_lt hx.1, hx.2⟩
  have hv'_int : IntervalIntegrable (fun t : ℝ => Complex.exp (-(z * (t:ℂ)))) volume (0:ℝ) x₀ := by
    apply ContinuousOn.intervalIntegrable
    fun_prop
  -- integration by parts
  have hIBP := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt
    (u := fun t : ℝ => ((f t : ℝ) : ℂ))
    (v := fun t : ℝ => -(z⁻¹) * Complex.exp (-(z * (t:ℂ))))
    (u' := fun t : ℝ => ((deriv f t : ℝ) : ℂ))
    (v' := fun t : ℝ => Complex.exp (-(z * (t:ℂ))))
    (by rw [Set.uIcc_of_le hx₀.le]
        exact Complex.continuous_ofReal.comp_continuousOn hfcont)
    (by have hc : Continuous (fun t : ℝ => -(z⁻¹) * Complex.exp (-(z * (t:ℂ)))) := by fun_prop
        exact hc.continuousOn)
    (by intro x hx
        rw [min_eq_left hx₀.le, max_eq_right hx₀.le] at hx
        exact (hfderiv x hx).ofReal_comp)
    (by intro x hx
        exact hasDerivAt_const_mul_exp_neg_mul z hz0 x)
    hderiv_int hv'_int
  -- abbreviations for the two integrals
  set J : ℂ := ∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t:ℂ))) * ((f t : ℝ) : ℂ) with hJdef
  set J' : ℂ := ∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t:ℂ))) * ((deriv f t : ℝ) : ℂ) with hJ'def
  have hLHS : (∫ x in (0:ℝ)..x₀,
        ((deriv f x : ℝ) : ℂ) * (-(z⁻¹) * Complex.exp (-(z * (x:ℂ))))
        + ((f x : ℝ) : ℂ) * Complex.exp (-(z * (x:ℂ))))
      = (-(z⁻¹)) * J' + J := by
    have hc1 : ContinuousOn (fun x : ℝ => -(z⁻¹) * Complex.exp (-(z * (x:ℂ)))) (Set.uIcc (0:ℝ) x₀) :=
      (by fun_prop : Continuous (fun x : ℝ => -(z⁻¹) * Complex.exp (-(z * (x:ℂ))))).continuousOn
    have hc2 : ContinuousOn (fun x : ℝ => Complex.exp (-(z * (x:ℂ)))) (Set.uIcc (0:ℝ) x₀) := by
      fun_prop
    have hfc : ContinuousOn (fun x : ℝ => ((f x : ℝ) : ℂ)) (Set.uIcc (0:ℝ) x₀) := by
      rw [Set.uIcc_of_le hx₀.le]
      exact Complex.continuous_ofReal.comp_continuousOn hfcont
    have hswap : (∫ x in (0:ℝ)..x₀,
          ((deriv f x : ℝ) : ℂ) * (-(z⁻¹) * Complex.exp (-(z * (x:ℂ))))
          + ((f x : ℝ) : ℂ) * Complex.exp (-(z * (x:ℂ))))
        = ∫ x in (0:ℝ)..x₀,
          (-(z⁻¹) * Complex.exp (-(z * (x:ℂ)))) * ((deriv f x : ℝ) : ℂ)
          + Complex.exp (-(z * (x:ℂ))) * ((f x : ℝ) : ℂ) := by
      refine intervalIntegral.integral_congr (fun x _ => ?_)
      ring
    have hi1 : IntervalIntegrable
        (fun x : ℝ => (-(z⁻¹) * Complex.exp (-(z * (x:ℂ)))) * ((deriv f x : ℝ) : ℂ))
        volume (0:ℝ) x₀ := hderiv_int.continuousOn_mul hc1
    have hi2 : IntervalIntegrable
        (fun x : ℝ => Complex.exp (-(z * (x:ℂ))) * ((f x : ℝ) : ℂ)) volume (0:ℝ) x₀ :=
      hfc.intervalIntegrable.continuousOn_mul hc2
    have e1 : (∫ x in (0:ℝ)..x₀,
          (-(z⁻¹) * Complex.exp (-(z * (x:ℂ)))) * ((deriv f x : ℝ) : ℂ))
        = (-(z⁻¹)) * J' := by
      rw [hJ'def, ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr (fun x _ => ?_)
      ring
    have e2 : (∫ x in (0:ℝ)..x₀, Complex.exp (-(z * (x:ℂ))) * ((f x : ℝ) : ℂ)) = J := by
      rw [hJdef]
    rw [hswap, intervalIntegral.integral_add hi1 hi2, e1, e2]
  have hRHS : ((f x₀ : ℝ) : ℂ) * (-(z⁻¹) * Complex.exp (-(z * (x₀:ℂ))))
      - ((f 0 : ℝ) : ℂ) * (-(z⁻¹) * Complex.exp (-(z * ((0:ℝ):ℂ)))) = (f 0 : ℂ) / z := by
    have h1 : Complex.exp (-(z * ((0:ℝ):ℂ))) = 1 := by simp
    rw [h1, mul_one, hfx₀, Complex.ofReal_zero, zero_mul, zero_sub, div_eq_mul_inv]
    ring
  have hJ : J = (f 0 : ℂ) / z + z⁻¹ * J' := by
    have hmain := hIBP
    rw [hLHS, hRHS] at hmain
    rw [eq_comm, ← hmain]
    ring
  -- norm estimates
  have hb1 : ‖(f 0 : ℂ) / z‖ ≤ Kf / |z.im| := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
    calc |f 0| / ‖z‖ ≤ Kf / ‖z‖ := div_le_div_of_nonneg_right hbnd0 (norm_nonneg z)
      _ ≤ Kf / |z.im| := div_le_div_of_nonneg_left hKf hzpos (Complex.abs_im_le_norm z)
  have hJ'bound : ‖J'‖ ≤ Real.exp (|z.re| * x₀) * (x₀ * Kd) := by
    have hpt : ∀ t ∈ Set.Icc (0:ℝ) x₀,
        ‖Complex.exp (-(z * (t:ℂ))) * ((deriv f t : ℝ) : ℂ)‖
          ≤ Real.exp (|z.re| * x₀) * Kd := by
      intro t ht
      rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
      have hexp : Real.exp ((-(z * (t:ℂ))).re) ≤ Real.exp (|z.re| * x₀) := by
        refine Real.exp_le_exp.mpr ?_
        have h1 : (-(z * (t:ℂ))).re = -(z.re * t) := by
          rw [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
          ring
        rw [h1]
        have h2 : -(z.re * t) ≤ |z.re * t| := neg_le_abs _
        have h3 : |z.re * t| = |z.re| * t := by rw [abs_mul, abs_of_nonneg ht.1]
        rw [h3] at h2
        exact le_trans h2 (mul_le_mul_of_nonneg_left ht.2 (abs_nonneg _))
      exact mul_le_mul hexp (hbndIcc t ht) (abs_nonneg _) (Real.exp_pos _).le
    have hpt' : ∀ t ∈ Set.uIoc (0:ℝ) x₀,
        ‖Complex.exp (-(z * (t:ℂ))) * ((deriv f t : ℝ) : ℂ)‖
          ≤ Real.exp (|z.re| * x₀) * Kd := by
      intro t ht
      rw [Set.uIoc_of_le hx₀.le] at ht
      exact hpt t ⟨le_of_lt ht.1, ht.2⟩
    have hint := intervalIntegral.norm_integral_le_of_norm_le_const hpt'
    rw [hJ'def]
    calc ‖∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t:ℂ))) * ((deriv f t : ℝ) : ℂ)‖
        ≤ (Real.exp (|z.re| * x₀) * Kd) * |x₀ - 0| := hint
      _ = Real.exp (|z.re| * x₀) * (x₀ * Kd) := by
          rw [sub_zero, abs_of_pos hx₀]; ring
  have hb2 : ‖z⁻¹ * J'‖ ≤ (1 / |z.im|) * (Real.exp (|z.re| * x₀) * (x₀ * Kd)) := by
    rw [norm_mul, norm_inv]
    have h1 : ‖z‖⁻¹ ≤ 1 / |z.im| := by
      rw [inv_eq_one_div]
      exact one_div_le_one_div_of_le hzpos (Complex.abs_im_le_norm z)
    exact mul_le_mul h1 hJ'bound (norm_nonneg _) (by positivity)
  calc ‖J‖ ≤ ‖(f 0 : ℂ) / z‖ + ‖z⁻¹ * J'‖ := by rw [hJ]; exact norm_add_le _ _
    _ ≤ Kf / |z.im| + (1 / |z.im|) * (Real.exp (|z.re| * x₀) * (x₀ * Kd)) :=
        add_le_add hb1 hb2
    _ = (Kf + Real.exp (|z.re| * x₀) * (x₀ * Kd)) / |z.im| := by
        rw [one_div]
        ring

/-! ### Rewriting the shift `(s-1)L` -/

/-- The real part of `((β + iτ) - 1)·L`. -/
private lemma re_shift (β τ L : ℝ) :
    ((((β:ℂ) + (τ:ℂ) * Complex.I) - 1) * (L:ℂ)).re = (β - 1) * L := by
  have h1 : (((β:ℂ) + (τ:ℂ) * Complex.I) - 1) * (L:ℂ)
      = (((β - 1) * L : ℝ) : ℂ) + (((τ * L : ℝ)) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h1]
  simp [Complex.add_re, Complex.mul_re]

/-- The imaginary part of `((β + iτ) - 1)·L`. -/
private lemma im_shift (β τ L : ℝ) :
    ((((β:ℂ) + (τ:ℂ) * Complex.I) - 1) * (L:ℂ)).im = τ * L := by
  have h1 : (((β:ℂ) + (τ:ℂ) * Complex.I) - 1) * (L:ℂ)
      = (((β - 1) * L : ℝ) : ℂ) + (((τ * L : ℝ)) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h1]
  simp [Complex.add_im, Complex.mul_im]

/-- **HB Lemma 5.3 at a complex point of height `≥ 1`.**  For a `C²`-function `f` supported in
`[0, x₀]` with `f 0 > 0`, and every `ε > 0`, there is `q₀` such that for `q ≥ q₀`, every
`s = β + iτ` with `|β - 1| ≤ √(log log q)/log q` and `1 ≤ |τ| ≤ 10 log q` satisfies
`K(s, χ₀) = Σ_n Λ(n) Re(χ₀(n)/n^s) f(log n / log q) ≤ ε log q`.
(`Ksum` is `Work.ZeroFreeTables.Ksum` in `Submission/Work/ZeroFreeTables/CertData.lean`; the `1`
is the principal character mod `q`.) -/
theorem PrincipalHeight (x₀ B : ℝ) (hx₀ : 0 < x₀) (hB : 0 ≤ B) :
    ∀ {f : ℝ → ℝ} (hcont : ContinuousOn f (Set.Ici 0))
      (hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0)
      (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
      (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B)
      {ε : ℝ} (hε : 0 < ε) (hf0 : 0 < f 0),
      ∃ q₀ : ℕ, ∀ {q : ℕ} [NeZero q], q₀ ≤ q → ∀ {β τ : ℝ},
        |β - 1| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) →
        1 ≤ |τ| → |τ| ≤ 10 * Real.log (q : ℝ) →
        Work.ZeroFreeTables.Ksum q f (Real.log (q : ℝ)) ((β : ℂ) + (τ : ℂ) * Complex.I)
            (1 : DirichletCharacter ℂ q)
          ≤ ε * Real.log (q : ℝ) := by
  intro f hcont hsupp hf2 hBnd ε hε hf0
  obtain ⟨Kf, hKf0, hKf⟩ := exists_abs_bound_of_contOn_support hcont hsupp
  obtain ⟨Kd₀, hKd₀0, hKd₀⟩ := exists_deriv_bound hx₀ hf2 hBnd
  set Kd : ℝ := max Kd₀ (max |deriv f 0| |deriv f x₀|) with hKddef
  have hKd0 : 0 ≤ Kd := le_trans hKd₀0 (le_max_left _ _)
  have hKdIoo : ∀ t ∈ Set.Ioo (0:ℝ) x₀, |deriv f t| ≤ Kd :=
    fun t ht => le_trans (hKd₀ t ht) (le_max_left _ _)
  have hKdIcc : ∀ t ∈ Set.Icc (0:ℝ) x₀, |deriv f t| ≤ Kd := by
    intro t ht
    rcases lt_or_eq_of_le ht.1 with h1 | h1
    · rcases lt_or_eq_of_le ht.2 with h2 | h2
      · exact hKdIoo t ⟨h1, h2⟩
      · rw [h2]
        exact le_trans (le_max_right (|deriv f 0|) (|deriv f x₀|)) (le_max_right Kd₀ _)
    · rw [← h1]
      exact le_trans (le_max_left (|deriv f 0|) (|deriv f x₀|)) (le_max_right Kd₀ _)
  obtain ⟨C, hCpos, hCbd⟩ := Work.LinnikAreas.lemma5_3_wide x₀ B hx₀ hB hcont hsupp hf2 hBnd
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨q₁, hq₁⟩ := AbsorbOmega C (ε/2) hCpos hε2
  obtain ⟨L₀, hL₀⟩ := ThresholdExpSqrtLog (Kf + x₀ * Kd) x₀ (ε/2) (by positivity) hx₀.le hε2
  refine ⟨max q₁ (max (⌈Real.exp L₀⌉₊ + 1) 8), ?_⟩
  intro q hqNe hq β τ hβ hτ1 hτ10
  have hq₁le : q₁ ≤ q := le_trans (le_max_left _ _) hq
  have hqAle : ⌈Real.exp L₀⌉₊ + 1 ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hq
  have hq8 : 8 ≤ q := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hq
  have hτpos : 0 < |τ| := lt_of_lt_of_le one_pos hτ1
  set L : ℝ := Real.log (q : ℝ) with hLdef
  have hL2 : 2 ≤ L := by
    rw [hLdef]
    have h1 : Real.log 8 ≤ Real.log (q:ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hq8)
    have h3 : Real.log (8:ℝ) = 3 * Real.log 2 := by
      rw [show (8:ℝ) = 2^3 by norm_num, Real.log_pow]; norm_num
    rw [h3] at h1
    have h4 : (2:ℝ) < 3 * Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    linarith
  have hLpos : 0 < L := by linarith
  have hL₀le : L₀ ≤ L := by
    have h1 : Real.exp L₀ < (q : ℝ) := by
      have h2 : Real.exp L₀ ≤ ((⌈Real.exp L₀⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
      have h3 : ((⌈Real.exp L₀⌉₊ : ℕ) : ℝ) + 1 ≤ (q : ℝ) := by exact_mod_cast hqAle
      linarith
    rw [hLdef, ← Real.log_exp L₀]
    exact Real.log_le_log (Real.exp_pos L₀) h1.le
  set s : ℂ := (β : ℂ) + (τ : ℂ) * Complex.I with hsdef
  have hsre : s.re = β := by simp [hsdef]
  have hsim : s.im = τ := by simp [hsdef]
  have hβ' : |s.re - 1| ≤ Real.sqrt (Real.log L) / L := by
    rw [hsre, hLdef]
    exact hβ
  have hβ'' : |β - 1| ≤ Real.sqrt (Real.log L) / L := by
    rw [← hsre]; exact hβ'
  have hτ10' : |s.im| ≤ 10 * L := by
    rw [hsim, hLdef]
    exact hτ10
  -- HB Lemma 5.3, wide range
  have h5 := hCbd (q := q) (L := L) hL2 s hβ' hτ10'
  -- the two integrals
  set M : ℂ := ∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - 1) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)
    with hMdef
  have h5' : ‖(∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) *
        (((1 : DirichletCharacter ℂ q) (n : ZMod q) : ℂ)) / (n : ℂ) ^ s *
        ((f (Real.log n / L) : ℝ) : ℂ)) - ((L : ℝ) : ℂ) * M‖
      ≤ C * ((q.primeFactors.card : ℝ) + (Real.log L)^2) := by
    rw [hMdef]
    exact h5
  -- the finite-support identity
  have hKsum := KsumRe (q := q) (f := f) (L := L) (x₀ := x₀) hLpos hsupp s
  -- The integral bound
  have hzre : ((s - 1) * L).re = (β - 1) * L := by
    rw [hsdef]
    exact re_shift β τ L
  have hzim : ((s - 1) * L).im = τ * L := by
    rw [hsdef]
    exact im_shift β τ L
  have hzre_le : |((s - 1) * L).re| ≤ Real.sqrt (Real.log L) := by
    rw [hzre, abs_mul, abs_of_pos hLpos]
    have h1 : |β - 1| * L ≤ (Real.sqrt (Real.log L) / L) * L :=
      mul_le_mul_of_nonneg_right hβ'' hLpos.le
    rw [div_mul_cancel₀ _ hLpos.ne'] at h1
    exact h1
  have hzim_ge : 1 ≤ |((s - 1) * L).im| := by
    rw [hzim, abs_mul, abs_of_pos hLpos]
    nlinarith [hτ1, hL2]
  have hIntB := IntegralBound (x₀ := x₀) hx₀ (f := f) (z := (s - 1) * L)
    (hcont.mono Set.Icc_subset_Ici_self) (hasDerivAt_of_contDiffOn hf2)
    (hsupp x₀ le_rfl) hKf0 hKd0 (hKf 0 le_rfl) hKdIcc hzim_ge
  have hMbound : ‖M‖ ≤
      (Kf + Real.exp (Real.sqrt (Real.log L) * x₀) * (x₀ * Kd)) / (|τ| * L) := by
    have h1 : ‖M‖ ≤ (Kf + Real.exp (|((s - 1) * L).re| * x₀) * (x₀ * Kd))
        / |((s - 1) * L).im| := by
      rw [hMdef]
      exact hIntB
    have hexp_le : Real.exp (|((s - 1) * L).re| * x₀)
        ≤ Real.exp (Real.sqrt (Real.log L) * x₀) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hzre_le hx₀.le)
    have hnum : Kf + Real.exp (|((s - 1) * L).re| * x₀) * (x₀ * Kd)
        ≤ Kf + Real.exp (Real.sqrt (Real.log L) * x₀) * (x₀ * Kd) := by
      have h2 : Real.exp (|((s - 1) * L).re| * x₀) * (x₀ * Kd)
          ≤ Real.exp (Real.sqrt (Real.log L) * x₀) * (x₀ * Kd) :=
        mul_le_mul_of_nonneg_right hexp_le (by positivity)
      linarith
    rw [hzim] at h1
    have h1' : ‖M‖ ≤ (Kf + Real.exp (|((s - 1) * L).re| * x₀) * (x₀ * Kd)) / |τ * L| := h1
    have h2 : |τ * L| = |τ| * L := by rw [abs_mul, abs_of_pos hLpos]
    rw [h2] at h1'
    calc ‖M‖ ≤ (Kf + Real.exp (|((s - 1) * L).re| * x₀) * (x₀ * Kd)) / (|τ| * L) := h1'
      _ ≤ (Kf + Real.exp (Real.sqrt (Real.log L) * x₀) * (x₀ * Kd)) / (|τ| * L) :=
          div_le_div_of_nonneg_right hnum (mul_pos hτpos hLpos).le
  -- the main term is O(1)
  have hLM : L * M.re ≤ (ε/2) * L := by
    have h1 : M.re ≤ ‖M‖ := Complex.re_le_norm _
    have h2 : L * M.re ≤ L * ‖M‖ := mul_le_mul_of_nonneg_left h1 hLpos.le
    have h3 : L * ‖M‖ ≤ L * ((Kf + Real.exp (Real.sqrt (Real.log L) * x₀) * (x₀ * Kd))
        / (|τ| * L)) := mul_le_mul_of_nonneg_left hMbound hLpos.le
    have h4 : L * ((Kf + Real.exp (Real.sqrt (Real.log L) * x₀) * (x₀ * Kd)) / (|τ| * L))
        = (Kf + Real.exp (Real.sqrt (Real.log L) * x₀) * (x₀ * Kd)) / |τ| := by
      have hLne : L ≠ 0 := hLpos.ne'
      have hτne : (|τ| : ℝ) ≠ 0 := hτpos.ne'
      field_simp <;> ring
    have h5 : (Kf + Real.exp (Real.sqrt (Real.log L) * x₀) * (x₀ * Kd)) / |τ|
        ≤ Kf + Real.exp (Real.sqrt (Real.log L) * x₀) * (x₀ * Kd) := by
      rw [div_le_iff₀ hτpos]
      have h6 : 0 ≤ Kf + Real.exp (Real.sqrt (Real.log L) * x₀) * (x₀ * Kd) := by
        have h7 : 0 ≤ Real.exp (Real.sqrt (Real.log L) * x₀) * (x₀ * Kd) := by positivity
        linarith
      nlinarith [h6, hτ1]
    have h6 : Kf + Real.exp (Real.sqrt (Real.log L) * x₀) * (x₀ * Kd)
        ≤ (Kf + x₀ * Kd) * (1 + Real.sqrt (Real.log L))
            * Real.exp (Real.sqrt (Real.log L) * x₀) := by
      set S : ℝ := Real.sqrt (Real.log L) with hSdef
      set E : ℝ := Real.exp (S * x₀) with hEdef
      have hS0 : 0 ≤ S := Real.sqrt_nonneg _
      have hE1 : 1 ≤ E := by
        rw [hEdef, ← Real.exp_zero]
        exact Real.exp_le_exp.mpr (by nlinarith [hS0, hx₀])
      have hE0 : 0 ≤ E := le_trans zero_le_one hE1
      have hxKd : 0 ≤ x₀ * Kd := by positivity
      have hbig : 1 ≤ (1 + S) * E := by nlinarith [hS0, hE1]
      have h21 : Kf ≤ Kf * ((1 + S) * E) := by nlinarith [hKf0, hbig]
      have hterm : (x₀ * Kd) * E ≤ (x₀ * Kd) * ((1 + S) * E) := by
        have h5' : E ≤ (1 + S) * E := by nlinarith [hE0, hS0, hE1]
        exact mul_le_mul_of_nonneg_left h5' hxKd
      calc Kf + Real.exp (S * x₀) * (x₀ * Kd) = Kf + (x₀ * Kd) * E := by
            rw [hEdef]; ring
        _ ≤ Kf * ((1 + S) * E) + (x₀ * Kd) * ((1 + S) * E) := by linarith
        _ = (Kf + x₀ * Kd) * (1 + S) * E := by ring
    have h7 := hL₀ L hL₀le
    linarith
  -- the error term is o(log q)
  have hErr : ((∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) *
        (((1 : DirichletCharacter ℂ q) (n : ZMod q) : ℂ)) / (n : ℂ) ^ s *
        ((f (Real.log n / L) : ℝ) : ℂ)) - ((L : ℝ) : ℂ) * M).re ≤ (ε/2) * L := by
    have h1 : ((∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) *
        (((1 : DirichletCharacter ℂ q) (n : ZMod q) : ℂ)) / (n : ℂ) ^ s *
        ((f (Real.log n / L) : ℝ) : ℂ)) - ((L : ℝ) : ℂ) * M).re
        ≤ ‖(∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) *
        (((1 : DirichletCharacter ℂ q) (n : ZMod q) : ℂ)) / (n : ℂ) ^ s *
        ((f (Real.log n / L) : ℝ) : ℂ)) - ((L : ℝ) : ℂ) * M‖ := Complex.re_le_norm _
    have h2 : C * ((q.primeFactors.card : ℝ) + (Real.log L)^2) ≤ (ε/2) * L := by
      have h3 : Real.log L = Real.log (Real.log (q:ℝ)) := by rw [hLdef]
      rw [h3, hLdef]
      exact hq₁ q hq₁le
    linarith
  -- assembly
  rw [hKsum]
  have hsplit : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) *
        (((1 : DirichletCharacter ℂ q) (n : ZMod q) : ℂ)) / (n : ℂ) ^ s *
        ((f (Real.log n / L) : ℝ) : ℂ)).re
      = L * M.re + ((∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) *
        (((1 : DirichletCharacter ℂ q) (n : ZMod q) : ℂ)) / (n : ℂ) ^ s *
        ((f (Real.log n / L) : ℝ) : ℂ)) - ((L : ℝ) : ℂ) * M).re := by
    rw [Complex.sub_re, Complex.re_ofReal_mul]
    ring
  rw [hsplit]
  linarith [hLM, hErr]

end Work.ZeroFreeTables.OffAxis.RectC
