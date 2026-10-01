import Mathlib
import Submission.Work.LinnikAreas.BGTZSetup
import Submission.Work.LinnikAreas.Sieve.Defs
import Submission.Work.Sieve.aFun_basics
import Submission.Work.Sieve.gFun_theory
import Submission.Work.Sieve.hFun_squarefree
import Submission.Work.Sieve.G_at_one_defs
import Submission.Work.Sieve.theta_bound
import Submission.Work.Sieve.Zfun_nonneg_le_Qfun
import Submission.Work.LinnikAreas.BGTZ.SelbergAux
import Submission.Work.LinnikAreas.BGTZ.SelbergDiag
import Submission.Work.LinnikAreas.BGTZ.SelbergSteps
import Submission.Work.LinnikAreas.BGTZ.SelbergLocal
import Submission.Work.LinnikAreas.BGTZ.SelbergReindex
import Submission.Work.LinnikAreas.BGTZ.SieveGAtOneSq
import Submission.Work.LinnikAreas.BGTZ.moebius_reindex
import Submission.Work.LinnikAreas.BGTZ.sieveKernel_eq_Tsum
import Submission.Work.LinnikAreas.BGTZ.Zsq_sum_le

open scoped BigOperators
open DirichletCharacter

namespace Work.LinnikAreas.BGTZ

variable {q : ℕ} [NeZero q]




/-! ## Auxiliary arithmetic -/

/-- `rad q = ∏_{p ∣ q} p`. -/
private def Rad (q : ℕ) : ℕ := ∏ p ∈ q.primeFactors, p

private lemma squarefree_rad (q : ℕ) : Squarefree (Rad q) :=
  squarefree_prod_primes _ (fun p hp => Nat.prime_of_mem_primeFactors hp)

private lemma coprime_rad_iff {q : ℕ} (hq : q ≠ 0) (d : ℕ) :
    Nat.Coprime d (Rad q) ↔ Nat.Coprime d q := by
  unfold Rad
  conv_rhs => rw [Nat.prod_primeFactors_pow_factorization hq]
  rw [Nat.coprime_prod_right_iff, Nat.coprime_prod_right_iff]
  refine forall₂_congr (fun p hp => ?_)
  have hne : q.factorization p ≠ 0 := by
    rw [← Finsupp.mem_support_iff, Nat.support_factorization]
    exact hp
  rw [Nat.coprime_pow_right_iff (Nat.pos_iff_ne_zero.mpr hne)]

private lemma gFun_one (χ₁ : DirichletCharacter ℂ q) : Work.LinnikAreas.Sieve.gFun χ₁ 1 = 1 := by
  rw [Work.LinnikAreas.Sieve.gFun, Work.LinnikAreas.Sieve.hFun, Nat.primeFactors_one,
    Finset.prod_empty, Finset.prod_empty, mul_one]

private lemma gFun_mul_any (χ₁ : DirichletCharacter ℂ q) (hχ₁ : χ₁ ^ 2 = 1) :
    ∀ a b : ℕ, Nat.Coprime a b → Work.LinnikAreas.Sieve.gFun χ₁ (a * b)
      = Work.LinnikAreas.Sieve.gFun χ₁ a * Work.LinnikAreas.Sieve.gFun χ₁ b := by
  intro a b hab
  rcases Nat.eq_zero_or_pos a with ha | ha
  · have hb1 : b = 1 := by
      have h : Nat.gcd a b = 1 := hab
      rw [ha, Nat.gcd_zero_left] at h
      exact h
    rw [ha, hb1, zero_mul, gFun_one χ₁, mul_one]
  · rcases Nat.eq_zero_or_pos b with hb | hb
    · have ha1 : a = 1 := by
        have h : Nat.gcd a b = 1 := hab
        rw [hb, Nat.gcd_zero_right] at h
        exact h
      rw [hb, ha1, mul_zero, gFun_one χ₁, one_mul]
    · exact gFun_mul χ₁ hχ₁ (Nat.pos_iff_ne_zero.mp ha) (Nat.pos_iff_ne_zero.mp hb) hab

private lemma field_key {A B C D E : ℝ} (hB : B ≠ 0) (hC : C ≠ 0) (hD : D ≠ 0) :
    (A * B / (C * D) * E) / B * C = A * E / D := by
  have h1 : A * B / (C * D) * E = A * B * E / (C * D) := by rw [div_mul_eq_mul_div]
  rw [h1]
  field_simp

private lemma field_key2 {A B C Z : ℝ} (hB : B ≠ 0) (hC : C ≠ 0) (hA : A ^ 2 = 1) :
    B * (A * Z / (B * C)) ^ 2 = (1 / C ^ 2) * (Z ^ 2 / B) := by
  have h1 : (A * Z / (B * C)) ^ 2 = A ^ 2 * Z ^ 2 / (B * C) ^ 2 := by
    rw [div_pow, mul_pow]
  rw [h1, hA, one_mul]
  field_simp

private lemma moebius_sq_one {l : ℕ} (hl : Squarefree l)
    : (((ArithmeticFunction.moebius l : ℤ) : ℝ)) ^ 2 = 1 := by
  rw [← Int.cast_pow, ArithmeticFunction.moebius_sq_eq_one_of_squarefree hl]
  norm_num

/-! ## The Selberg weights -/

theorem isSieveWeight_thetaFun (χ₁ : DirichletCharacter ℂ q) (hχ₁ : χ₁ ^ 2 = 1) {R : ℕ}
    (hR : 1 ≤ R) : IsSieveWeight R (Work.LinnikAreas.Sieve.thetaFun χ₁ R) :=
  ⟨thetaFun_one χ₁ hχ₁ hR,
   fun d hd => by
     rcases hd with h | h
     · exact thetaFun_eq_zero_of_not_squarefree χ₁ R d h
     · exact thetaFun_eq_zero_of_gt χ₁ h,
   fun d => Work.Sieve.theta_bound χ₁ hχ₁ R d⟩

theorem sieveGre_eq_sum (χ₁ : DirichletCharacter ℂ q) (hχ₁ : χ₁ ^ 2 = 1) (R : ℕ) (θw : ℕ → ℝ) :
    sieveGre χ₁ R θw 1 (1 : DirichletCharacter ℂ q) =
      ∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R, θw d * θw e *
        ∏ p ∈ (Nat.lcm d e).primeFactors,
          (sieveLocal χ₁ (1 : DirichletCharacter ℂ q) (1 : ℂ) p).re := by
  rw [sieveGre, sieveG_one_one_cast χ₁ hχ₁ R θw, Complex.ofReal_re]

/-- `Y_l · V(R) = μ(l) Z_l / g(l)`. -/
theorem thetaY_mul_VFun (χ₁ : DirichletCharacter ℂ q) (hχ₁ : χ₁ ^ 2 = 1) (R : ℕ) {l : ℕ}
    (hl : l ∈ (Finset.Icc 1 R).filter (fun d => Squarefree d ∧ Nat.Coprime d q)) :
    (∑ d ∈ ((Finset.Icc 1 R).filter (fun d => Squarefree d ∧ Nat.Coprime d q)).filter
        (fun d => l ∣ d),
        Work.LinnikAreas.Sieve.thetaFun χ₁ R d / Work.LinnikAreas.Sieve.hFun χ₁ d)
      * Work.LinnikAreas.Sieve.VFun χ₁ R
      = ((ArithmeticFunction.moebius l : ℤ) : ℝ) / Work.LinnikAreas.Sieve.gFun χ₁ l
          * Work.Sieve.Zfun χ₁ R l := by
  obtain ⟨hlI, hlsf, hlc⟩ := Finset.mem_filter.mp hl
  have hl1 : 1 ≤ l := (Finset.mem_Icc.mp hlI).1
  have hR1 : 1 ≤ R := le_trans hl1 (Finset.mem_Icc.mp hlI).2
  obtain ⟨-, -, -, -, hgspos, hgmul, hVpos⟩ := Work.Sieve.gFun_theory χ₁ hχ₁
  have hV : Work.LinnikAreas.Sieve.VFun χ₁ R ≠ 0 := ne_of_gt (hVpos R hR1)
  set T : Finset ℕ := (Finset.Icc 1 R).filter (fun d => Squarefree d ∧ Nat.Coprime d q) with hT
  set Q0 : ℕ := ∏ p ∈ q.primeFactors, p with hQ0
  set W : ℕ → ℝ := fun d => ∑ r ∈ (Finset.Icc 1 (R / d)).filter (fun r => Nat.Coprime r d),
      (if Squarefree r then (1 : ℝ) else 0) / Work.LinnikAreas.Sieve.gFun χ₁ r with hW
  set W' : ℕ → ℝ := fun d => ∑ r ∈ (Finset.Icc 1 (R / d)).filter
      (fun r => Nat.Coprime r d ∧ Squarefree r), 1 / Work.LinnikAreas.Sieve.gFun χ₁ r with hW'
  have hWW : ∀ d : ℕ, W d = W' d := by
    intro d
    have hL : W d = ∑ r ∈ (Finset.Icc 1 (R / d)).filter (fun r => Nat.Coprime r d),
        (if Squarefree r then 1 / Work.LinnikAreas.Sieve.gFun χ₁ r else 0) := by
      rw [hW]; simp only []
      refine Finset.sum_congr rfl (fun r _ => ?_)
      by_cases hs : Squarefree r <;> simp [hs]
    have hR : W' d = ∑ r ∈ (Finset.Icc 1 (R / d)).filter (fun r => Nat.Coprime r d),
        (if Squarefree r then 1 / Work.LinnikAreas.Sieve.gFun χ₁ r else 0) := by
      rw [hW']; simp only []
      conv_lhs => rw [← Finset.filter_filter, Finset.sum_filter]
    rw [hL, hR]
  have hA : (∑ d ∈ T.filter (fun d => l ∣ d),
        Work.LinnikAreas.Sieve.thetaFun χ₁ R d / Work.LinnikAreas.Sieve.hFun χ₁ d)
      * Work.LinnikAreas.Sieve.VFun χ₁ R
      = ∑ d ∈ T.filter (fun d => l ∣ d),
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) * W d / Work.LinnikAreas.Sieve.gFun χ₁ d := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    obtain ⟨hdT, -⟩ := Finset.mem_filter.mp hd
    obtain ⟨-, hdsf, -⟩ := Finset.mem_filter.mp (hT ▸ hdT)
    have hhn : Work.LinnikAreas.Sieve.hFun χ₁ d ≠ 0 := ne_of_gt (hFun_pos χ₁ hχ₁ d)
    have hgn : Work.LinnikAreas.Sieve.gFun χ₁ d ≠ 0 := ne_of_gt (hgspos d hdsf)
    rw [Work.LinnikAreas.Sieve.thetaFun, hW]
    simp only []
    exact field_key hhn hV hgn
  have hB : (∑ d ∈ T.filter (fun d => l ∣ d),
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) * W d / Work.LinnikAreas.Sieve.gFun χ₁ d)
      = ∑ d ∈ T.filter (fun d => l ∣ d),
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) * W' d / Work.LinnikAreas.Sieve.gFun χ₁ d :=
    Finset.sum_congr rfl (fun d _ => by rw [hWW d])
  have hsub : T.filter (fun d => l ∣ d) ⊆
      (Finset.Icc 1 R).filter (fun d => l ∣ d ∧ Nat.Coprime d Q0) := by
    intro d hd
    obtain ⟨hdT, hld⟩ := Finset.mem_filter.mp hd
    obtain ⟨hdI, -, hdc⟩ := Finset.mem_filter.mp (hT ▸ hdT)
    exact Finset.mem_filter.mpr ⟨hdI, hld, (coprime_rad_iff (NeZero.ne q) d).mpr hdc⟩
  have hzero : ∀ d ∈ (Finset.Icc 1 R).filter (fun d => l ∣ d ∧ Nat.Coprime d Q0),
      d ∉ T.filter (fun d => l ∣ d) →
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) * W' d / Work.LinnikAreas.Sieve.gFun χ₁ d = 0 := by
    intro d hdD hdnot
    obtain ⟨hdI, hld, hdcop⟩ := Finset.mem_filter.mp hdD
    have hnsf : ¬ Squarefree d := by
      intro hsf
      refine hdnot ?_
      exact Finset.mem_filter.mpr ⟨hT.symm ▸ Finset.mem_filter.mpr ⟨hdI, hsf,
        (coprime_rad_iff (NeZero.ne q) d).mp hdcop⟩, hld⟩
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsf]
    norm_num
  have hC : (∑ d ∈ T.filter (fun d => l ∣ d),
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) * W' d / Work.LinnikAreas.Sieve.gFun χ₁ d)
      = ∑ d ∈ (Finset.Icc 1 R).filter (fun d => l ∣ d ∧ Nat.Coprime d Q0),
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) * W' d / Work.LinnikAreas.Sieve.gFun χ₁ d :=
    Finset.sum_subset hsub hzero
  have hlQ0 : Nat.Coprime l Q0 := (coprime_rad_iff (NeZero.ne q) l).mpr hlc
  have hQ0sf : Squarefree Q0 := by
    rw [hQ0]; exact squarefree_prod_primes _ (fun p hp => Nat.prime_of_mem_primeFactors hp)
  have hmoeb := moebius_reindex (Work.LinnikAreas.Sieve.gFun χ₁) (gFun_one χ₁)
    (gFun_mul_any χ₁ hχ₁) R l Q0 hlsf hl1 hlQ0 hQ0sf
  calc (∑ d ∈ T.filter (fun d => l ∣ d),
        Work.LinnikAreas.Sieve.thetaFun χ₁ R d / Work.LinnikAreas.Sieve.hFun χ₁ d)
      * Work.LinnikAreas.Sieve.VFun χ₁ R
      = ∑ d ∈ T.filter (fun d => l ∣ d),
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) * W d / Work.LinnikAreas.Sieve.gFun χ₁ d := hA
    _ = ∑ d ∈ T.filter (fun d => l ∣ d),
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) * W' d / Work.LinnikAreas.Sieve.gFun χ₁ d := hB
    _ = ∑ d ∈ (Finset.Icc 1 R).filter (fun d => l ∣ d ∧ Nat.Coprime d Q0),
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) * W' d / Work.LinnikAreas.Sieve.gFun χ₁ d := hC
    _ = (((ArithmeticFunction.moebius l : ℤ) : ℝ) / Work.LinnikAreas.Sieve.gFun χ₁ l)
          * ∑ m ∈ (Finset.Icc 1 R).filter (fun m => l * m ≤ R ∧ m ∣ Q0),
             1 / Work.LinnikAreas.Sieve.gFun χ₁ m := by
        rw [← hmoeb]
    _ = (((ArithmeticFunction.moebius l : ℤ) : ℝ) / Work.LinnikAreas.Sieve.gFun χ₁ l)
          * Work.Sieve.Zfun χ₁ R l := by simp only [Work.Sieve.Zfun, hQ0]

/-- The diagonalised Selberg weight sum is bounded by `(q/φ(q)) (Σ_{n ≤ R} a(n)/n)^{-1}`. -/
theorem thetaTsq_le (χ₁ : DirichletCharacter ℂ q) (hχ₁ : χ₁ ^ 2 = 1) {R : ℕ} (hR : 200 ≤ R) :
    (∑ d ∈ (Finset.Icc 1 R).filter (fun d => Squarefree d ∧ Nat.Coprime d q),
      ∑ e ∈ (Finset.Icc 1 R).filter (fun e => Squarefree e ∧ Nat.Coprime e q),
        Work.LinnikAreas.Sieve.thetaFun χ₁ R d * Work.LinnikAreas.Sieve.thetaFun χ₁ R e
          / Work.LinnikAreas.Sieve.hFun χ₁ (Nat.lcm d e))
      ≤ (q : ℝ) / (q.totient : ℝ)
          * (∑ n ∈ Finset.Icc 1 R, Work.LinnikAreas.Sieve.aFun χ₁ n / (n : ℝ))⁻¹ := by
  have hR1 : 1 ≤ R := by omega
  obtain ⟨-, -, -, -, hgspos, hgmul, hVpos⟩ := Work.Sieve.gFun_theory χ₁ hχ₁
  have hVpos' : 0 < Work.LinnikAreas.Sieve.VFun χ₁ R := hVpos R hR1
  have hVne : Work.LinnikAreas.Sieve.VFun χ₁ R ≠ 0 := ne_of_gt hVpos'
  set T : Finset ℕ := (Finset.Icc 1 R).filter (fun d => Squarefree d ∧ Nat.Coprime d q) with hT
  have hTmem : ∀ {d : ℕ}, d ∈ T ↔
      (d ∈ Finset.Icc 1 R ∧ Squarefree d ∧ Nat.Coprime d q) := by
    intro d; rw [hT, Finset.mem_filter]
  have hTpos : ∀ d ∈ T, 0 < d := by
    intro d hd
    obtain ⟨hdI, -, -⟩ := hTmem.mp hd
    exact lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hdI).1
  have hTclosed : ∀ {l d : ℕ}, l ∣ d → d ∈ T → l ∈ T := by
    intro l d hld hd
    obtain ⟨hdI, hdsf, hdc⟩ := hTmem.mp hd
    have hl0 : l ≠ 0 := fun h => by
      rw [h] at hld
      exact absurd (Nat.eq_zero_of_zero_dvd hld) (by have := (Finset.mem_Icc.mp hdI).1; omega)
    have hl1 : 1 ≤ l := Nat.one_le_iff_ne_zero.mpr hl0
    have hlR : l ≤ R := le_trans (Nat.le_of_dvd (by have := (Finset.mem_Icc.mp hdI).1; omega) hld)
      (Finset.mem_Icc.mp hdI).2
    exact hTmem.mpr ⟨Finset.mem_Icc.mpr ⟨hl1, hlR⟩, hdsf.squarefree_of_dvd hld,
      hdc.coprime_dvd_left hld⟩
  have hne : ∀ d ∈ T, ∀ e ∈ T, Work.LinnikAreas.Sieve.hFun χ₁ d ≠ 0 ∧
      Work.LinnikAreas.Sieve.hFun χ₁ e ≠ 0 ∧ Work.LinnikAreas.Sieve.hFun χ₁ (Nat.lcm d e) ≠ 0 :=
    fun d _ e _ => ⟨ne_of_gt (hFun_pos χ₁ hχ₁ d), ne_of_gt (hFun_pos χ₁ hχ₁ e),
      ne_of_gt (hFun_pos χ₁ hχ₁ _)⟩
  have hlcm : ∀ d ∈ T, ∀ e ∈ T,
      Work.LinnikAreas.Sieve.hFun χ₁ d * Work.LinnikAreas.Sieve.hFun χ₁ e
        = Work.LinnikAreas.Sieve.hFun χ₁ (Nat.lcm d e)
            * Work.LinnikAreas.Sieve.hFun χ₁ (Nat.gcd d e) := by
    intro d hd e he
    obtain ⟨hdI, -, -⟩ := hTmem.mp hd
    obtain ⟨heI, -, -⟩ := hTmem.mp he
    have hd0 : d ≠ 0 := by have := (Finset.mem_Icc.mp hdI).1; omega
    have he0 : e ≠ 0 := by have := (Finset.mem_Icc.mp heI).1; omega
    exact (hFun_lcm_mul_gcd χ₁ hd0 he0).symm
  have hg : ∀ n ∈ T, Work.LinnikAreas.Sieve.hFun χ₁ n
      = ∑ δ ∈ n.divisors, Work.LinnikAreas.Sieve.gFun χ₁ δ := by
    intro n hn
    obtain ⟨-, hnsf, -⟩ := hTmem.mp hn
    exact hFun_eq_sum_gFun_of_squarefree χ₁ hχ₁ hnsf
  rw [lcm_diagonalization T hTpos hTclosed (Work.LinnikAreas.Sieve.gFun χ₁)
    (Work.LinnikAreas.Sieve.hFun χ₁) (Work.LinnikAreas.Sieve.thetaFun χ₁ R) hne hlcm hg]
  have hYl : ∀ l ∈ T, Work.LinnikAreas.Sieve.gFun χ₁ l
        * (∑ d ∈ T.filter (fun d => l ∣ d),
            Work.LinnikAreas.Sieve.thetaFun χ₁ R d / Work.LinnikAreas.Sieve.hFun χ₁ d) ^ 2
      = (1 / (Work.LinnikAreas.Sieve.VFun χ₁ R) ^ 2)
          * ((Work.Sieve.Zfun χ₁ R l) ^ 2 / Work.LinnikAreas.Sieve.gFun χ₁ l) := by
    intro l hl
    obtain ⟨hlI, hlsf, hlc⟩ := hTmem.mp hl
    have hl' : l ∈ (Finset.Icc 1 R).filter (fun d => Squarefree d ∧ Nat.Coprime d q) :=
      Finset.mem_filter.mpr ⟨hlI, hlsf, hlc⟩
    have hgl : Work.LinnikAreas.Sieve.gFun χ₁ l ≠ 0 := ne_of_gt (hgspos l hlsf)
    have hYV := thetaY_mul_VFun χ₁ hχ₁ R hl'
    have hY : (∑ d ∈ T.filter (fun d => l ∣ d),
          Work.LinnikAreas.Sieve.thetaFun χ₁ R d / Work.LinnikAreas.Sieve.hFun χ₁ d)
        = ((ArithmeticFunction.moebius l : ℤ) : ℝ) * Work.Sieve.Zfun χ₁ R l
            / (Work.LinnikAreas.Sieve.gFun χ₁ l * Work.LinnikAreas.Sieve.VFun χ₁ R) := by
      rw [eq_div_iff (mul_ne_zero hgl hVne)]
      calc (∑ d ∈ T.filter (fun d => l ∣ d),
              Work.LinnikAreas.Sieve.thetaFun χ₁ R d / Work.LinnikAreas.Sieve.hFun χ₁ d)
            * (Work.LinnikAreas.Sieve.gFun χ₁ l * Work.LinnikAreas.Sieve.VFun χ₁ R)
          = (∑ d ∈ T.filter (fun d => l ∣ d),
              Work.LinnikAreas.Sieve.thetaFun χ₁ R d / Work.LinnikAreas.Sieve.hFun χ₁ d)
              * Work.LinnikAreas.Sieve.VFun χ₁ R * Work.LinnikAreas.Sieve.gFun χ₁ l := by ring
        _ = ((((ArithmeticFunction.moebius l : ℤ) : ℝ) / Work.LinnikAreas.Sieve.gFun χ₁ l)
              * Work.Sieve.Zfun χ₁ R l) * Work.LinnikAreas.Sieve.gFun χ₁ l := by rw [hYV]
        _ = ((ArithmeticFunction.moebius l : ℤ) : ℝ) * Work.Sieve.Zfun χ₁ R l := by
              field_simp
    rw [hY]
    exact field_key2 hgl hVne (moebius_sq_one hlsf)
  rw [Finset.sum_congr rfl hYl, ← Finset.mul_sum]
  have hbound : (∑ l ∈ T, (Work.Sieve.Zfun χ₁ R l) ^ 2 / Work.LinnikAreas.Sieve.gFun χ₁ l)
      ≤ Work.Sieve.Qfun χ₁ * Work.LinnikAreas.Sieve.VFun χ₁ R := by
    rw [hT]
    exact Zsq_sum_le χ₁ hχ₁ R
  have hSpos : 0 < ∑ n ∈ Finset.Icc 1 R, Work.LinnikAreas.Sieve.aFun χ₁ n / (n : ℝ) := by
    refine Finset.sum_pos' (fun n _ => div_nonneg
      (Work.Sieve.aFun_nonneg_le_card χ₁ hχ₁ n).1 (Nat.cast_nonneg n)) ⟨1, ?_, ?_⟩
    · rw [Finset.mem_Icc]; exact ⟨le_refl 1, hR1⟩
    · rw [aFun_one', Nat.cast_one, div_one]; exact one_pos
  have hSV : (∑ n ∈ Finset.Icc 1 R, Work.LinnikAreas.Sieve.aFun χ₁ n / (n : ℝ))
      ≤ Work.LinnikAreas.Sieve.VFun χ₁ R := VFun_ge_sum_aFun_div χ₁ hχ₁ R
  have hQnn : 0 ≤ Work.Sieve.Qfun χ₁ := by
    rw [Qfun_eq_totient_div χ₁ hχ₁]
    exact div_nonneg (Nat.cast_nonneg q)
      (le_of_lt (Nat.cast_pos.mpr (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q)))))
  have hstep2 : (1 / (Work.LinnikAreas.Sieve.VFun χ₁ R) ^ 2)
      * (Work.Sieve.Qfun χ₁ * Work.LinnikAreas.Sieve.VFun χ₁ R)
      = Work.Sieve.Qfun χ₁ / Work.LinnikAreas.Sieve.VFun χ₁ R := by
    field_simp
  have hstep3 : Work.Sieve.Qfun χ₁ / Work.LinnikAreas.Sieve.VFun χ₁ R
      ≤ Work.Sieve.Qfun χ₁ / (∑ n ∈ Finset.Icc 1 R, Work.LinnikAreas.Sieve.aFun χ₁ n / (n : ℝ)) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_left ?_ hQnn
    simpa using one_div_le_one_div_of_le hSpos hSV
  have hstep4 : Work.Sieve.Qfun χ₁
        / (∑ n ∈ Finset.Icc 1 R, Work.LinnikAreas.Sieve.aFun χ₁ n / (n : ℝ))
      = (q : ℝ) / (q.totient : ℝ)
          * (∑ n ∈ Finset.Icc 1 R, Work.LinnikAreas.Sieve.aFun χ₁ n / (n : ℝ))⁻¹ := by
    rw [Qfun_eq_totient_div χ₁ hχ₁, div_eq_mul_inv]
  exact le_trans (mul_le_mul_of_nonneg_left hbound (by positivity))
    (le_trans (le_of_eq hstep2) (le_trans hstep3 (le_of_eq hstep4)))

/-- **BGTZ Lemma 4.2 / Graham's Lemma 9.6: the Selberg sieve weights.** -/
theorem SieveWeights {q : ℕ} [NeZero q] (hq : 400000 < q) (χ₁ : DirichletCharacter ℂ q)
    (hχ₁ : χ₁ ^ 2 = 1) {R : ℕ} (hR : 200 ≤ R) :
    ∃ θ : ℕ → ℝ, Work.LinnikAreas.BGTZ.IsSieveWeight R θ ∧
      Work.LinnikAreas.BGTZ.sieveGre χ₁ R θ 1 (1 : DirichletCharacter ℂ q)
        ≤ (q : ℝ) / (q.totient : ℝ)
          * (∑ n ∈ Finset.Icc 1 R, Work.LinnikAreas.BGTZ.aCoeff χ₁ n / (n : ℝ))⁻¹ := by
  have hR1 : 1 ≤ R := by omega
  refine ⟨Work.LinnikAreas.Sieve.thetaFun χ₁ R, isSieveWeight_thetaFun χ₁ hχ₁ hR1, ?_⟩
  rw [sieveGre_eq_sum χ₁ hχ₁ R (Work.LinnikAreas.Sieve.thetaFun χ₁ R)]
  rw [sieveKernel_eq_Tsum χ₁ hχ₁ R (isSieveWeight_thetaFun χ₁ hχ₁ hR1)]
  have hS : (∑ n ∈ Finset.Icc 1 R, aCoeff χ₁ n / (n : ℝ))
      = ∑ n ∈ Finset.Icc 1 R, Work.LinnikAreas.Sieve.aFun χ₁ n / (n : ℝ) :=
    Finset.sum_congr rfl (fun n _ => rfl)
  rw [hS]
  exact thetaTsq_le χ₁ hχ₁ hR

end Work.LinnikAreas.BGTZ
