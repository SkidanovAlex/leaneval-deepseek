import Mathlib
import Submission.Commons.NumberTheory.Sieve.moebius_density_sum_le
import Submission.Commons.NumberTheory.Sieve.density_eulerProd_div_sigma_tendsto
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sum_mul_log_abel
import Submission.Commons.NumberTheory.FriedlanderIwaniec.tendsto_tsum_mul_abelskernel
import Submission.Commons.NumberTheory.FriedlanderIwaniec.summable_cA_log

open scoped BigOperators
open Filter

namespace Commons.NumberTheory.Sieve

noncomputable section

/-! ### Abel summation machinery (general, duplicated here to be self-contained) -/

private lemma hasSum_ite_telescope {f : ℕ → ℝ} (hf : Filter.Tendsto f Filter.atTop (nhds 0))
    (hanti : ∀ d : ℕ, 1 ≤ d → f (d + 1) ≤ f d)
    {e : ℕ} (he : 1 ≤ e) :
    HasSum (fun d : ℕ => if e ≤ d then f d - f (d + 1) else 0) (f e) := by
  refine (hasSum_iff_tendsto_nat_of_nonneg (f := fun d : ℕ => if e ≤ d then f d - f (d + 1) else 0)
    ?_ (f e)).mpr ?_
  · intro d
    by_cases h : e ≤ d
    · rw [if_pos h]
      have hd : 1 ≤ d := le_trans he h
      linarith [hanti d hd]
    · rw [if_neg h]
  · have hev : ∀ᶠ N in Filter.atTop,
        (∑ i ∈ Finset.range N, (if e ≤ i then f i - f (i + 1) else 0)) = f e - f N := by
      filter_upwards [Filter.eventually_ge_atTop e] with N hN
      rw [← Finset.sum_filter]
      have hfil : (Finset.range N).filter (fun i => e ≤ i) = Finset.Ico e N := by
        ext i; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
      rw [hfil]
      have hneg : (∑ i ∈ Finset.Ico e N, (f i - f (i + 1)))
          = -(∑ i ∈ Finset.Ico e N, (f (i + 1) - f i)) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      rw [hneg, Finset.sum_Ico_sub f hN]
      ring
    have hbase : Filter.Tendsto (fun N : ℕ => f e - f N) Filter.atTop (nhds (f e)) := by
      simpa using (tendsto_const_nhds (x := f e) (f := Filter.atTop)).sub hf
    exact hbase.congr' (hev.mono fun N hN => hN.symm)

private lemma tsum_ite_telescope {f : ℕ → ℝ} (hf : Filter.Tendsto f Filter.atTop (nhds 0))
    (hanti : ∀ d : ℕ, 1 ≤ d → f (d + 1) ≤ f d)
    {e : ℕ} (he : 1 ≤ e) :
    (∑' d : ℕ, (if e ≤ d then f d - f (d + 1) else 0)) = f e :=
  (hasSum_ite_telescope hf hanti he).tsum_eq

/-- The auxiliary kernel of the Abel summation identity. -/
private def abelH (b f : ℕ → ℝ) : ℕ → ℕ → ℝ :=
  fun d e => if e ∈ Finset.Icc 1 d then b e * (f d - f (d + 1)) else 0

/-- **Abel summation (partial summation) for unconditional `tsum`s.** -/
private lemma abel_tsum {b f : ℕ → ℝ} (hf0 : f 0 = 0)
    (hf : Filter.Tendsto f Filter.atTop (nhds 0))
    (hanti : ∀ d : ℕ, 1 ≤ d → f (d + 1) ≤ f d)
    (hb : Summable (fun e : ℕ => ‖b e * f e‖)) :
    (∑' e : ℕ, b e * f e) =
      ∑' d : ℕ, (∑ e ∈ Finset.Icc 1 d, b e) * (f d - f (d + 1)) := by
  have hfnn : ∀ e : ℕ, 0 ≤ f e := by
    intro e
    rcases Nat.eq_zero_or_pos e with h | h
    · rw [h, hf0]
    · have hdec : ∀ N, e ≤ N → f N ≤ f e := by
        intro N hN
        obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
        clear hN
        induction k with
        | zero => simp
        | succ k ih =>
            have h1 : f (e + (k + 1)) ≤ f (e + k) := by
              have := hanti (e + k) (by omega)
              rwa [show e + k + 1 = e + (k + 1) from by ring] at this
            exact le_trans h1 ih
      have hev : ∀ᶠ N in Filter.atTop, f N ≤ f e :=
        Filter.eventually_atTop.mpr ⟨e, hdec⟩
      exact le_of_tendsto hf hev
  have hsumm_bf : Summable (fun e : ℕ => ‖b e‖ * f e) :=
    hb.congr (fun e => by rw [norm_mul, Real.norm_of_nonneg (hfnn e)])
  have key : ∀ u : Finset (ℕ × ℕ),
      ∑ p ∈ u, ‖Function.uncurry (abelH b f) p‖ ≤ ∑' e, ‖b e‖ * f e := by
    intro u
    set N : ℕ := u.sup (fun p => max p.1 p.2) with hN
    have hNle : ∀ p ∈ u, p.1 ≤ N ∧ p.2 ≤ N := by
      intro p hp
      have h1 : max p.1 p.2 ≤ N := by
        rw [hN]; exact Finset.le_sup (f := fun p : ℕ × ℕ => max p.1 p.2) hp
      exact ⟨le_trans (le_max_left _ _) h1, le_trans (le_max_right _ _) h1⟩
    have hbox : u ⊆ (Finset.range (N + 1)) ×ˢ (Finset.range (N + 1)) := by
      intro p hp
      obtain ⟨h1, h2⟩ := hNle p hp
      simp only [Finset.mem_product, Finset.mem_range]
      exact ⟨by omega, by omega⟩
    calc ∑ p ∈ u, ‖Function.uncurry (abelH b f) p‖
        ≤ ∑ p ∈ (Finset.range (N + 1)) ×ˢ (Finset.range (N + 1)),
            ‖Function.uncurry (abelH b f) p‖ :=
          Finset.sum_le_sum_of_subset_of_nonneg hbox (fun p _ _ => norm_nonneg _)
      _ = ∑ e ∈ Finset.range (N + 1), ∑ d ∈ Finset.range (N + 1), ‖abelH b f d e‖ := by
          rw [Finset.sum_product, Finset.sum_comm]
          rfl
      _ ≤ ∑ e ∈ Finset.range (N + 1), ‖b e‖ * f e := by
          apply Finset.sum_le_sum
          intro e he
          by_cases he0 : e = 0
          · subst he0
            have hz : ∀ d : ℕ, abelH b f d 0 = 0 := by
              intro d; simp only [abelH, Finset.mem_Icc]; simp
            simp only [hz, norm_zero, Finset.sum_const_zero]
            simp [hf0]
          · have he1 : 1 ≤ e := Nat.one_le_iff_ne_zero.mpr he0
            have hcond : ∀ d : ℕ, abelH b f d e
                = b e * (if e ≤ d then f d - f (d + 1) else 0) := by
              intro d
              by_cases h : e ≤ d
              · have hm : e ∈ Finset.Icc 1 d := by simp only [Finset.mem_Icc]; omega
                simp [abelH, hm, h]
              · have hm : e ∉ Finset.Icc 1 d := by simp only [Finset.mem_Icc]; omega
                simp [abelH, hm, h]
            have hnorm2 : ∀ d : ℕ,
                ‖(if e ≤ d then f d - f (d + 1) else 0 : ℝ)‖
                  = (if e ≤ d then f d - f (d + 1) else 0) := by
              intro d
              by_cases h : e ≤ d
              · rw [if_pos h, Real.norm_of_nonneg (by linarith [hanti d (le_trans he1 h)])]
              · rw [if_neg h, norm_zero]
            simp only [hcond, norm_mul, hnorm2]
            rw [← Finset.mul_sum]
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
            rw [← Finset.sum_filter]
            have hfil : (Finset.range (N + 1)).filter (fun d => e ≤ d) = Finset.Ico e (N + 1) := by
              ext d; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
            rw [hfil]
            by_cases heN : e ≤ N + 1
            · have hneg : (∑ d ∈ Finset.Ico e (N + 1), (f d - f (d + 1)))
                  = -(∑ d ∈ Finset.Ico e (N + 1), (f (d + 1) - f d)) := by
                rw [← Finset.sum_neg_distrib]
                exact Finset.sum_congr rfl (fun d _ => by ring)
              rw [hneg, Finset.sum_Ico_sub f heN]
              linarith [hfnn (N + 1)]
            · have hemp : Finset.Ico e (N + 1) = ∅ := by
                apply Finset.eq_empty_iff_forall_notMem.mpr
                intro d hd; simp only [Finset.mem_Ico] at hd; omega
              rw [hemp, Finset.sum_empty]
              exact hfnn e
      _ ≤ ∑' e, ‖b e‖ * f e :=
          Summable.sum_le_tsum (Finset.range (N + 1))
            (fun e _ => mul_nonneg (norm_nonneg _) (hfnn e)) hsumm_bf
  have hsumm0 : Summable (fun p : ℕ × ℕ => ‖Function.uncurry (abelH b f) p‖) :=
    summable_of_sum_le (fun p => norm_nonneg _) key
  have hsumm : Summable (Function.uncurry (abelH b f)) := hsumm0.of_norm
  have h1 : ∀ d : ℕ, (∑' e : ℕ, abelH b f d e)
      = (∑ e ∈ Finset.Icc 1 d, b e) * (f d - f (d + 1)) := by
    intro d
    rw [tsum_eq_sum (s := Finset.Icc 1 d) (fun e he => by simp [abelH, he])]
    rw [show (∑ e ∈ Finset.Icc 1 d, abelH b f d e)
          = ∑ e ∈ Finset.Icc 1 d, b e * (f d - f (d + 1)) from
        Finset.sum_congr rfl (fun e he => by simp [abelH, he])]
    rw [Finset.sum_mul]
  have h2 : ∀ e : ℕ, (∑' d : ℕ, abelH b f d e) = b e * f e := by
    intro e
    rcases Nat.eq_zero_or_pos e with he | he
    · subst he
      rw [tsum_eq_sum (s := ∅) (fun d _ => by simp [abelH, Finset.mem_Icc])]
      simp only [Finset.sum_empty]
      rw [hf0, mul_zero]
    · have hcond : ∀ d : ℕ, abelH b f d e
          = b e * (if e ≤ d then f d - f (d + 1) else 0) := by
        intro d
        by_cases h : e ≤ d
        · have hm : e ∈ Finset.Icc 1 d := by simp only [Finset.mem_Icc]; omega
          simp [abelH, hm, h]
        · have hm : e ∉ Finset.Icc 1 d := by simp only [Finset.mem_Icc]; omega
          simp [abelH, hm, h]
      simp_rw [hcond]
      rw [tsum_mul_left, tsum_ite_telescope hf hanti he]
  calc (∑' e : ℕ, b e * f e)
      = ∑' e : ℕ, ∑' d : ℕ, abelH b f d e := (tsum_congr h2).symm
    _ = ∑' d : ℕ, ∑' e : ℕ, abelH b f d e := Summable.tsum_comm hsumm
    _ = ∑' d : ℕ, (∑ e ∈ Finset.Icc 1 d, b e) * (f d - f (d + 1)) := tsum_congr h1

/-! ### The telescoping identity for the general density -/

/-- Telescoping (Abel) identity for the shifted Dirichlet series of a density `g`:
for `σ > 0`, `(∑_e μ(e) g(e) e^{-σ})/σ = ∑_d (∑_{e ≤ d} μ(e) g(e))·(d^{-σ} − (d+1)^{-σ})/σ`. -/
private lemma density_telescoping {g : ℕ → ℝ}
    (hmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n)
    (hg1 : g 1 = 1)
    (hp : ∀ p : ℕ, p.Prime → 0 ≤ g p)
    (hbound : ∃ C : ℝ, ∀ p : ℕ, p.Prime → g p ≤ C / (p : ℝ))
    (σ : ℝ) (hσ : 0 < σ) :
    (∑' e : ℕ, (ArithmeticFunction.moebius e : ℝ) * g e * (e : ℝ) ^ (-σ)) / σ
      = ∑' d : ℕ, (∑ e ∈ Finset.Icc 1 d, (ArithmeticFunction.moebius e : ℝ) * g e)
          * (((d : ℝ) ^ (-σ) - ((d : ℝ) + 1) ^ (-σ)) / σ) := by
  have hb := summable_norm_moebius_mul_g_rpow hmul hg1 hp hbound hσ
  have hf0 : (fun d : ℕ => (d : ℝ) ^ (-σ)) 0 = 0 := by
    simp only [Nat.cast_zero]
    exact Real.zero_rpow (ne_of_lt (neg_lt_zero.mpr hσ))
  have hftend : Filter.Tendsto (fun d : ℕ => (d : ℝ) ^ (-σ)) Filter.atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hσ).comp tendsto_natCast_atTop_atTop
  have hanti : ∀ d : ℕ, 1 ≤ d →
      (fun d : ℕ => (d : ℝ) ^ (-σ)) (d + 1) ≤ (fun d : ℕ => (d : ℝ) ^ (-σ)) d := by
    intro d hd
    show ((d + 1 : ℕ) : ℝ) ^ (-σ) ≤ (d : ℝ) ^ (-σ)
    have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    rw [Nat.cast_add, Nat.cast_one, Real.rpow_neg hd0.le σ,
        Real.rpow_neg (by linarith : (0:ℝ) ≤ (d:ℝ) + 1) σ]
    exact (inv_le_inv₀ (Real.rpow_pos_of_pos (by linarith : (0:ℝ) < (d:ℝ)+1) σ)
      (Real.rpow_pos_of_pos hd0 σ)).mpr (Real.rpow_le_rpow hd0.le (by linarith) hσ.le)
  have hC := abel_tsum (b := fun e : ℕ => (ArithmeticFunction.moebius e : ℝ) * g e)
      (f := fun d : ℕ => (d : ℝ) ^ (-σ)) hf0 hftend hanti hb
  simp only [Nat.cast_add, Nat.cast_one] at hC
  rw [hC, ← tsum_div_const]
  apply tsum_congr
  intro d
  ring

/-! ### The main term -/

/-- The evaluation of the main-term constant **(1.12)–(1.14) of the companion paper
"Asymptotic sieve for primes"**: for a multiplicative density `g` with `0 ≤ g(p) < 1`,
`g(p) ≪ 1/p` and `∑_{p ≤ y} g(p) = log log y + c + O((log y)^{-10})`, the series
`−∑_d μ(d) g(d) log d` converges to a positive constant `H`, which is also the limit of the
partial Euler products `∏_{p < N} (1−g(p))/(1−1/p)`. -/
theorem sum_mu_mul_density_mul_log_tendsto {g : ℕ → ℝ}
    (hmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n)
    (hg1 : g 1 = 1)
    (hp : ∀ p : ℕ, p.Prime → 0 ≤ g p ∧ g p < 1)
    (hbound : ∃ C : ℝ, ∀ p : ℕ, p.Prime → g p ≤ C / (p : ℝ))
    (h9 : ∃ c C : ℝ, ∀ y : ℝ, 2 ≤ y →
      |(∑ p ∈ (Finset.Icc 2 ⌊y⌋₊).filter Nat.Prime, g p) - Real.log (Real.log y) - c|
        ≤ C * (Real.log y) ^ (-(10 : ℤ))) :
    ∃ H : ℝ, 0 < H ∧
      Filter.Tendsto (fun N : ℕ => ∑ d ∈ Finset.Icc 1 N,
          (ArithmeticFunction.moebius d : ℝ) * g d * Real.log d) Filter.atTop (nhds (-H)) ∧
      Filter.Tendsto (fun N : ℕ => ∏ p ∈ Nat.primesBelow N,
          (1 - g p) / (1 - 1 / (p : ℝ))) Filter.atTop (nhds H) := by
  -- (2.4) with ϱ = 1: bound on the partial sums of μ·g
  obtain ⟨Cb, hCbpos, hCb⟩ := moebius_density_sum_le hmul hg1 hp hbound h9
  have hboundA : ∃ C : ℝ, 0 < C ∧
      ∀ y : ℕ, 2 ≤ y → |∑ d ∈ Finset.Icc 1 y, (ArithmeticFunction.moebius d : ℝ) * g d|
        ≤ C * (Real.log (y : ℝ)) ^ (-6 : ℝ) := by
    refine ⟨Cb, hCbpos, fun y hy => ?_⟩
    have h := hCb 1 y le_rfl hy
    have hfil : (Finset.Icc 1 y).filter (fun d => Nat.Coprime d 1) = Finset.Icc 1 y := by
      apply Finset.filter_true_of_mem
      intro d _; exact Nat.coprime_one_right d
    have hprod : (∏ p ∈ (1 : ℕ).primeFactors, (1 + 1 / Real.sqrt (p : ℝ))) = 1 := by simp
    have hzr : Real.log (y : ℝ) ^ (-(6:ℤ)) = (Real.log (y : ℝ)) ^ (-(6:ℝ)) := by
      rw [← Real.rpow_intCast]; norm_num
    rw [hfil, hprod, mul_one, hzr] at h
    exact h
  -- the crux: identification of the constant
  obtain ⟨H, hHpos, hGlim, hprodlim⟩ :=
    density_eulerProd_div_sigma_tendsto hmul hg1 hp hbound h9
  refine ⟨H, hHpos, ?_, hprodlim⟩
  -- partial sums of μ·g
  set aF : ℕ → ℝ := fun d => (ArithmeticFunction.moebius d : ℝ) * g d with haF
  set A : ℕ → ℝ := fun N => ∑ d ∈ Finset.Icc 1 N, aF d with hA
  have hA0 : A 0 = 0 := by simp [hA]
  have hboundA' : ∃ C : ℝ, 0 < C ∧ ∀ y : ℕ, 2 ≤ y → |A y| ≤ C * (Real.log (y : ℝ)) ^ (-6 : ℝ) := by
    obtain ⟨C, hC, hb⟩ := hboundA
    exact ⟨C, hC, fun y hy => by simpa only [hA, haF] using hb y hy⟩
  -- the limiting value of the Abel kernel series
  have hsumm : Summable (fun d : ℕ => A d * Real.log (((d : ℝ) + 1) / (d : ℝ))) :=
    Commons.NumberTheory.FriedlanderIwaniec.summable_cA_log A hboundA'
  -- A N * log N → 0
  have hANlog : Filter.Tendsto (fun N : ℕ => A N * Real.log N) Filter.atTop (nhds 0) := by
    obtain ⟨C, hC, hb⟩ := hboundA'
    have htend : Filter.Tendsto (fun N : ℕ => (Real.log (N : ℝ)) ^ (-5 : ℝ)) Filter.atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop (show (0 : ℝ) < 5 by norm_num)).comp
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    have hb5 : Filter.Tendsto (fun N : ℕ => C * (Real.log (N : ℝ)) ^ (-5 : ℝ)) Filter.atTop (nhds 0) := by
      simpa using htend.const_mul C
    have hev : ∀ᶠ N : ℕ in Filter.atTop,
        ‖A N * Real.log N‖ ≤ C * (Real.log (N : ℝ)) ^ (-5 : ℝ) := by
      filter_upwards [Filter.eventually_ge_atTop 2] with N hN
      have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
      have hb' := hb N hN
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hlogN]
      calc |A N| * Real.log N ≤ (C * (Real.log (N : ℝ)) ^ (-6 : ℝ)) * Real.log N :=
            mul_le_mul_of_nonneg_right hb' hlogN
        _ = C * (Real.log (N : ℝ)) ^ (-5 : ℝ) := by
            have hlogpos : 0 < Real.log (N : ℝ) := Real.log_pos (by
              exact_mod_cast (by omega : 1 < N))
            have hkey : (Real.log (N : ℝ)) ^ (-6 : ℝ) * Real.log (N : ℝ)
                = (Real.log (N : ℝ)) ^ (-5 : ℝ) := by
              rw [show (-6 : ℝ) = -5 + (-1) by norm_num, Real.rpow_add hlogpos, Real.rpow_neg_one,
                mul_assoc, inv_mul_cancel₀ (ne_of_gt hlogpos), mul_one]
            rw [mul_assoc, hkey]
    exact tendsto_zero_iff_norm_tendsto_zero.mpr
      (squeeze_zero' (Filter.Eventually.of_forall (fun N => norm_nonneg _)) hev hb5)
  -- Abel identity
  have habel : ∀ N : ℕ,
      (∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ) * g d * Real.log d)
        = A N * Real.log N
          - ∑ d ∈ Finset.Icc 1 (N - 1), A d * Real.log (((d : ℝ) + 1) / (d : ℝ)) := by
    intro N
    have h := Commons.NumberTheory.FriedlanderIwaniec.sum_mul_log_abel aF N
    have hL : (∑ d ∈ Finset.Icc 1 N, aF d * Real.log (d : ℝ))
        = ∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ) * g d * Real.log d :=
      Finset.sum_congr rfl (fun d _ => by rw [haF])
    have hR1 : (∑ d ∈ Finset.Icc 1 N, aF d) = A N := by simp only [hA]
    have hR2 : (∑ d ∈ Finset.Icc 1 (N - 1),
          (∑ e ∈ Finset.Icc 1 d, aF e) * Real.log (((d : ℝ) + 1) / (d : ℝ)))
        = ∑ d ∈ Finset.Icc 1 (N - 1), A d * Real.log (((d : ℝ) + 1) / (d : ℝ)) := by
      apply Finset.sum_congr rfl
      intro d _
      rw [show (∑ e ∈ Finset.Icc 1 d, aF e) = A d from by simp only [hA]]
    rw [hL, hR1, hR2] at h
    exact h
  -- conversion Icc 1 (N-1) ↔ range N
  have hconv : ∀ N : ℕ,
      (∑ d ∈ Finset.Icc 1 (N - 1), A d * Real.log (((d : ℝ) + 1) / (d : ℝ)))
        = ∑ d ∈ Finset.range N, A d * Real.log (((d : ℝ) + 1) / (d : ℝ)) := by
    intro N
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN; simp
    · have hins : Finset.range N = insert 0 (Finset.Icc 1 (N - 1)) := by
        ext d; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
      rw [hins, Finset.sum_insert (by simp [Finset.mem_Icc])]
      rw [hA0, zero_mul, zero_add]
  -- the Abel-kernel partial sums converge to the complete series
  have hpartRange : Filter.Tendsto
      (fun N : ℕ => ∑ d ∈ Finset.range N, A d * Real.log (((d : ℝ) + 1) / (d : ℝ)))
      Filter.atTop (nhds (∑' d : ℕ, A d * Real.log (((d : ℝ) + 1) / (d : ℝ)))) :=
    hsumm.hasSum.tendsto_sum_nat
  have hpartial : Filter.Tendsto
      (fun N : ℕ => ∑ d ∈ Finset.Icc 1 (N - 1), A d * Real.log (((d : ℝ) + 1) / (d : ℝ)))
      Filter.atTop (nhds (∑' d : ℕ, A d * Real.log (((d : ℝ) + 1) / (d : ℝ)))) :=
    hpartRange.congr (fun N => (hconv N).symm)
  -- the first limit equals minus the complete Abel series
  have hfirst : Filter.Tendsto
      (fun N : ℕ => ∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ) * g d * Real.log d)
      Filter.atTop (nhds (-(∑' d : ℕ, A d * Real.log (((d : ℝ) + 1) / (d : ℝ))))) := by
    have hmain : Filter.Tendsto
        (fun N : ℕ => A N * Real.log N
          - ∑ d ∈ Finset.Icc 1 (N - 1), A d * Real.log (((d : ℝ) + 1) / (d : ℝ)))
        Filter.atTop (nhds (0 - ∑' d : ℕ, A d * Real.log (((d : ℝ) + 1) / (d : ℝ)))) :=
      hANlog.sub hpartial
    have hmain' : Filter.Tendsto
        (fun N : ℕ => A N * Real.log N
          - ∑ d ∈ Finset.Icc 1 (N - 1), A d * Real.log (((d : ℝ) + 1) / (d : ℝ)))
        Filter.atTop (nhds (-(∑' d : ℕ, A d * Real.log (((d : ℝ) + 1) / (d : ℝ))))) := by
      simpa using hmain
    exact hmain'.congr (fun N => (habel N).symm)
  -- identify the complete Abel series with the constant H
  have hL_eq_H : (∑' d : ℕ, A d * Real.log (((d : ℝ) + 1) / (d : ℝ))) = H := by
    have hker : Filter.Tendsto
        (fun σ : ℝ => ∑' d : ℕ, A d * (((d : ℝ) ^ (-σ) - ((d : ℝ) + 1) ^ (-σ)) / σ))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (∑' d : ℕ, A d * Real.log (((d : ℝ) + 1) / (d : ℝ)))) := by
      have h := Commons.NumberTheory.FriedlanderIwaniec.tendsto_tsum_mul_abelskernel A hA0 hboundA'
      simpa using h
    have hkerH : Filter.Tendsto
        (fun σ : ℝ => ∑' d : ℕ, A d * (((d : ℝ) ^ (-σ) - ((d : ℝ) + 1) ^ (-σ)) / σ))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds H) := by
      refine hGlim.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with σ hσ
      have ht := density_telescoping hmul hg1 (fun p h => (hp p h).1) hbound σ hσ
      have hAexp : ∀ d : ℕ, A d
          = ∑ e ∈ Finset.Icc 1 d, (ArithmeticFunction.moebius e : ℝ) * g e :=
        fun d => by simp only [hA, haF]
      rw [show (∑' d : ℕ, A d * (((d : ℝ) ^ (-σ) - ((d : ℝ) + 1) ^ (-σ)) / σ))
            = ∑' d : ℕ, (∑ e ∈ Finset.Icc 1 d, (ArithmeticFunction.moebius e : ℝ) * g e)
                * (((d : ℝ) ^ (-σ) - ((d : ℝ) + 1) ^ (-σ)) / σ) from
          tsum_congr (fun d => by rw [hAexp d])]
      exact ht
    exact tendsto_nhds_unique hker hkerH
  rw [hL_eq_H] at hfirst
  exact hfirst

end

end Commons.NumberTheory.Sieve
