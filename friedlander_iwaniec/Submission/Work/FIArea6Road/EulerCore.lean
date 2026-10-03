/-
# `Submission.Work.FIArea6Road.EulerCore` — the truncation regrouping `Z(s) = W(s)·Q(s)`

The heart of the Euler-product regrouping *FI* (16.30)–(16.34): the identity

  `Zsfun = Σ_{c ∈ (c,Π)=1, c squarefree, c ≤ ⌊C⌋₊} λ(c)c^{-s}·Gser(cΠ)`

obtained from the divisor decomposition `γ(N;C) = Σ_{c|N, c≤C} μ(c)` and multiplicativity of the
Hecke eigenvalue sequence `λ`.
-/
import Mathlib
import Submission.Work.FIArea6Road.EulerDefs

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FIArea6Road

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The truncation range `1 ≤ c ≤ ⌊C⌋₊` of (16.34). -/
def sfin (Pa : Work.FITop.Params) : Finset ℕ := Finset.Icc 1 ⌊Pa.C⌋₊

lemma mem_sfin {Pa : Work.FITop.Params} {c : ℕ} : c ∈ sfin Pa ↔ 1 ≤ c ∧ c ≤ ⌊Pa.C⌋₊ := by
  simp [sfin]

/-- **Truncation identity.** `γ(N;C) = Σ_{c ∈ sfin, c ∣ N} μ(c)` (for `N ≠ 0`). -/
lemma gammaTrunc_cast_eq (Pa : Work.FITop.Params) {N : ℕ} (hN : N ≠ 0) :
    (Work.FIPlan.gammaTrunc Pa.C N : ℂ)
      = ∑ c ∈ sfin Pa, (if c ∣ N then (ArithmeticFunction.moebius c : ℂ) else 0) := by
  have hC0 : (0 : ℝ) ≤ Pa.C := by linarith [Pa.hC1]
  have hset : N.divisors.filter (fun d => ((d : ℕ) : ℝ) ≤ Pa.C)
      = (sfin Pa).filter (fun c => c ∣ N) := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, mem_sfin, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hdvd, -⟩, hle⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero hN),
        (Nat.le_floor_iff hC0).mpr hle⟩, hdvd⟩
    · rintro ⟨⟨h1, h2⟩, hdvd⟩
      exact ⟨⟨hdvd, hN⟩, (Nat.le_floor_iff hC0).mp h2⟩
  rw [Work.FIPlan.gammaTrunc, hset, Finset.sum_filter]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : i ∣ N <;> simp [h]

/-- **The coefficient identity.** `tcoef(N)·N^{-s} = F(N)·γ(N;C)`. -/
lemma tcoef_mul_eq_Fcoef_mul_gamma (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ)
    (s : ℂ) (N : ℕ) :
    Work.FIArea6.TauPieces.tcoef Pa chi m N * (N : ℂ) ^ (-s)
      = Fcoef Pa chi m s N * (Work.FIPlan.gammaTrunc Pa.C N : ℂ) := by
  rw [Work.FIArea6.TauPieces.tcoef, Fcoef, NoSmallPrimesNat_iff_coprime Pa N]
  by_cases h : Nat.Coprime N (PiPr Pa) <;> simp [h] <;> ring

/-- **The coefficient identity, expanded.** `tcoef(N)·N^{-s} = F(N)·Σ_{c∈sfin, c∣N} μ(c)`. -/
lemma tcoef_mul_eq_sum (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) (s : ℂ)
    (N : ℕ) :
    Work.FIArea6.TauPieces.tcoef Pa chi m N * (N : ℂ) ^ (-s)
      = (∑ c ∈ sfin Pa,
          (if c ∣ N then (ArithmeticFunction.moebius c : ℂ) else 0))
        * Fcoef Pa chi m s N := by
  rcases eq_or_ne N 0 with rfl | hN
  · have h0 : ¬ Work.FIArea6Hecke.NoSmallPrimesNat Pa 0 :=
      fun h => h 2 Nat.prime_two Pa.hP2 (dvd_zero 2)
    rw [Work.FIArea6.TauPieces.tcoef, if_neg h0, Fcoef, Work.FIArea5.S16Hecke.heckeLam_zero]
    ring
  · rw [tcoef_mul_eq_Fcoef_mul_gamma, gammaTrunc_cast_eq Pa hN]
    ring

/-- The summand of `Gser`. -/
def Gterm (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) (s : ℂ) (Q n : ℕ) : ℂ :=
  (if Nat.Coprime n Q then 1 else 0)
    * (Work.FIArea5.S16Hecke.heckeLam chi m n * (ArithmeticFunction.moebius n : ℂ))
    * (n : ℂ) ^ (-s)

lemma Gser_eq_tsum_Gterm (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) (s : ℂ)
    (Q : ℕ) : Gser Pa chi m s Q = ∑' n, Gterm Pa chi m s Q n := rfl

lemma Fcoef_eq_Gterm (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) (s : ℂ)
    (N : ℕ) : Fcoef Pa chi m s N = Gterm Pa chi m s (PiPr Pa) N := rfl

/-- `Σ_n ‖λ(n)μ(n)‖ n^{-σ}` converges for `σ > 1`. -/
lemma summable_norm_lam_mu (chi : GaussianInt → ℂ) (m : ℤ)
    (hchibd : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ =>
      ‖Work.FIArea5.S16Hecke.heckeLam chi m n * (ArithmeticFunction.moebius n : ℂ)‖
        * (n : ℝ) ^ (-s.re)) := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((Work.FIArea5.S16Hecke.summable_card_divisors_mul_rpow_neg hs).mul_left 4)
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Work.FIArea5.S16Hecke.heckeLam_zero]
  · have hm := Work.FIArea5.S16Hecke.heckeLam_bound chi m hchibd (n := n)
      (Nat.one_le_iff_ne_zero.mpr hn)
    have hmu : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := norm_moebius_le_one n
    calc ‖Work.FIArea5.S16Hecke.heckeLam chi m n * (ArithmeticFunction.moebius n : ℂ)‖
            * (n : ℝ) ^ (-s.re)
        ≤ (4 * (n.divisors.card : ℝ)) * (n : ℝ) ^ (-s.re) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (Nat.cast_nonneg n) _)
          calc ‖Work.FIArea5.S16Hecke.heckeLam chi m n * (ArithmeticFunction.moebius n : ℂ)‖
              = ‖Work.FIArea5.S16Hecke.heckeLam chi m n‖
                  * ‖(ArithmeticFunction.moebius n : ℂ)‖ := norm_mul _ _
            _ ≤ (4 * (n.divisors.card : ℝ)) * 1 :=
                mul_le_mul hm hmu (norm_nonneg _) (by positivity)
            _ = 4 * (n.divisors.card : ℝ) := by ring
      _ = 4 * ((n.divisors.card : ℝ) * (n : ℝ) ^ (-s.re)) := by ring

/-- `Gser` is summable for `re s > 1`. -/
lemma summable_Gterm (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) {s : ℂ}
    (hchibd : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) (hs : 1 < s.re) (Q : ℕ) :
    Summable (fun n => Gterm Pa chi m s Q n) := by
  have hsre : s.re ≠ 0 := by linarith
  refine Summable.of_norm ?_
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    (summable_norm_lam_mu chi m hchibd hs)
  rw [Gterm, norm_mul, norm_mul, norm_natCast_cpow_neg n hsre]
  have h1 : ‖(if Nat.Coprime n Q then (1 : ℂ) else 0)‖ ≤ 1 := by split <;> simp
  calc _ ≤ 1 * ‖Work.FIArea5.S16Hecke.heckeLam chi m n
          * (ArithmeticFunction.moebius n : ℂ)‖ * (n : ℝ) ^ (-s.re) := by
        refine mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
          (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    _ = _ := by ring

/-- **Reindexing a sum over the multiples of `c`.** -/
lemma tsum_dvd_mul {c : ℕ} (hc : 1 ≤ c) (g : ℕ → ℂ) :
    (∑' N, (if c ∣ N then g N else 0)) = ∑' mm, g (c * mm) := by
  have hg : Function.Injective (fun mm : ℕ => c * mm) := by
    intro a b hab
    exact Nat.eq_of_mul_eq_mul_left (by omega) hab
  have hsupp : Function.support (fun N => if c ∣ N then g N else 0)
      ⊆ Set.range (fun mm : ℕ => c * mm) := by
    intro N hN
    simp only [Function.mem_support, ne_eq] at hN
    have hdvd : c ∣ N := by
      by_contra h
      exact hN (by simp [h])
    obtain ⟨k, hk⟩ := hdvd
    exact ⟨k, hk.symm⟩
  rw [← Function.Injective.tsum_eq hg (f := fun N => if c ∣ N then g N else 0) hsupp]
  exact tsum_congr fun mm => by rw [if_pos (Nat.dvd_mul_right c mm)]

/-- **Pointwise form of `Fcoef (c·m)`** for `c` coprime to `Π`. -/
lemma Fcoef_mul_eq (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) (s : ℂ)
    (hchimul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w) {c : ℕ}
    (hc : Nat.Coprime c (PiPr Pa)) (mm : ℕ) :
    Fcoef Pa chi m s (c * mm)
      = Work.FIArea5.S16Hecke.heckeLam chi m c * (ArithmeticFunction.moebius c : ℂ)
        * (c : ℂ) ^ (-s) * Gterm Pa chi m s (c * PiPr Pa) mm := by
  rcases eq_or_ne mm 0 with rfl | hmm
  · rw [mul_zero]
    simp only [Fcoef_eq_Gterm, Gterm, Work.FIArea5.S16Hecke.heckeLam_zero]
    ring
  · have hmmp : 0 < mm := Nat.pos_of_ne_zero hmm
    have hc1 : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · rw [h, Nat.coprime_zero_left] at hc
        have := two_le_PiPr Pa
        omega
      · exact h
    simp only [Fcoef_eq_Gterm, Gterm]
    by_cases h : Nat.Coprime mm (c * PiPr Pa)
    · obtain ⟨hmc, hmP⟩ := (Nat.coprime_mul_iff_right).mp h
      have hcm : Nat.Coprime c mm := hmc.symm
      have hcmP : Nat.Coprime (c * mm) (PiPr Pa) :=
        (Nat.coprime_mul_iff_left).mpr ⟨hc, hmP⟩
      rw [if_pos h, if_pos hcmP, Work.FIArea5.S16Hecke.heckeLam_mul chi m hchimul hc1 hmmp hcm,
        ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
          (Nat.coprime_iff_gcd_eq_one.mp hcm),
        Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
      push_cast
      ring
    · have h1 : ¬ Nat.Coprime mm (PiPr Pa) ∨ ¬ Nat.Coprime mm c := by
        by_contra hcon
        push_neg at hcon
        exact h ((Nat.coprime_mul_iff_right).mpr ⟨hcon.2, hcon.1⟩)
      rcases h1 with h1 | h1
      · have hns : ¬ Nat.Coprime (c * mm) (PiPr Pa) := fun hc' =>
          h1 ((Nat.coprime_mul_iff_left).mp hc').2
        rw [if_neg hns, if_neg h]
        ring
      · have hns : ¬ Squarefree (c * mm) := fun hs' =>
          h1 (Nat.coprime_of_squarefree_mul hs').symm
        rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hns, if_neg h]
        ring

/-- Summability of the summand of the truncation regrouping. -/
lemma summable_dvd_indicator (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) {s : ℂ}
    (hchibd : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) (hs : 1 < s.re) (c : ℕ) :
    Summable (fun N => (if c ∣ N then (ArithmeticFunction.moebius c : ℂ) else 0)
      * Fcoef Pa chi m s N) := by
  refine Summable.of_norm ?_
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    (summable_norm_Fcoef Pa chi m hchibd hs)
  rw [norm_mul]
  have hmu : ‖(if c ∣ n then (ArithmeticFunction.moebius c : ℂ) else 0)‖ ≤ 1 := by
    split
    · exact norm_moebius_le_one c
    · simp
  calc _ ≤ 1 * ‖Fcoef Pa chi m s n‖ := mul_le_mul_of_nonneg_right hmu (norm_nonneg _)
    _ = ‖Fcoef Pa chi m s n‖ := one_mul _

/-- **The truncated Möbius sum.** For `c ≥ 1`,
`Σ'_{c|N} μ(c)·F(N) = [c squarefree, (c,Π)=1] · λ(c)c^{-s}·Gser(cΠ)`. -/
lemma sum_dvd_Fcoef_eq (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) (s : ℂ)
    (hchimul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w) {c : ℕ} (hc1 : 1 ≤ c) :
    (∑' N, (if c ∣ N then (ArithmeticFunction.moebius c : ℂ) else 0) * Fcoef Pa chi m s N)
      = (if Squarefree c ∧ Nat.Coprime c (PiPr Pa)
          then Work.FIArea5.S16Hecke.heckeLam chi m c * (c : ℂ) ^ (-s)
            * Gser Pa chi m s (c * PiPr Pa) else 0) := by
  by_cases hcop : Nat.Coprime c (PiPr Pa)
  · by_cases hs : Squarefree c
    · rw [if_pos ⟨hs, hcop⟩]
      rw [show (fun N => (if c ∣ N then (ArithmeticFunction.moebius c : ℂ) else 0)
          * Fcoef Pa chi m s N)
          = (fun N => (ArithmeticFunction.moebius c : ℂ)
              * (if c ∣ N then Fcoef Pa chi m s N else 0)) from funext fun N => by
            by_cases h : c ∣ N <;> simp [h]]
      rw [tsum_mul_left, tsum_dvd_mul hc1 (Fcoef Pa chi m s),
        tsum_congr (fun mm => Fcoef_mul_eq Pa chi m s hchimul hcop mm), tsum_mul_left,
        ← Gser_eq_tsum_Gterm]
      have hmu2 : (ArithmeticFunction.moebius c : ℂ) * (ArithmeticFunction.moebius c : ℂ)
          = 1 := by
        rw [← pow_two, ← Int.cast_pow,
          ArithmeticFunction.moebius_sq_eq_one_of_squarefree hs, Int.cast_one]
      calc (ArithmeticFunction.moebius c : ℂ)
            * (Work.FIArea5.S16Hecke.heckeLam chi m c * (ArithmeticFunction.moebius c : ℂ)
              * (c : ℂ) ^ (-s) * Gser Pa chi m s (c * PiPr Pa))
          = (Work.FIArea5.S16Hecke.heckeLam chi m c * (c : ℂ) ^ (-s)
              * Gser Pa chi m s (c * PiPr Pa))
            * ((ArithmeticFunction.moebius c : ℂ) * (ArithmeticFunction.moebius c : ℂ)) := by
              ring
        _ = _ := by rw [hmu2, mul_one]
    · rw [if_neg (fun h => hs h.1)]
      have h0 : (ArithmeticFunction.moebius c : ℂ) = 0 := by
        rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]; simp
      rw [show (fun N => (if c ∣ N then (ArithmeticFunction.moebius c : ℂ) else 0)
          * Fcoef Pa chi m s N) = fun N => 0 from funext fun N => by
            by_cases h : c ∣ N <;> simp [h, h0]]
      rw [tsum_zero]
  · rw [if_neg (fun h => hcop h.2)]
    have hex : ∃ q : ℕ, q.Prime ∧ q ≤ Pa.Pz ∧ q ∣ c := by
      by_contra hcon
      push_neg at hcon
      exact hcop ((NoSmallPrimesNat_iff_coprime Pa c).mp hcon)
    obtain ⟨q, hq, hqle, hqc⟩ := hex
    have hzero : ∀ N, (if c ∣ N then (ArithmeticFunction.moebius c : ℂ) else 0)
        * Fcoef Pa chi m s N = 0 := by
      intro N
      by_cases h : c ∣ N
      · rw [if_pos h]
        have hqN : q ∣ N := dvd_trans hqc h
        have hqP : q ∣ PiPr Pa := by
          rw [PiPr]
          exact Finset.dvd_prod_of_mem _ (Nat.mem_primesBelow.mpr ⟨by omega, hq⟩)
        have hnc : ¬ Nat.Coprime N (PiPr Pa) := fun hc' => by
          have hg : q ∣ N.gcd (PiPr Pa) := Nat.dvd_gcd hqN hqP
          rw [Nat.coprime_iff_gcd_eq_one.mp hc'] at hg
          exact hq.ne_one (Nat.dvd_one.mp hg)
        simp only [Fcoef_eq_Gterm, Gterm, if_neg hnc]
        ring
      · simp [h]
    rw [tsum_congr hzero, tsum_zero]

/-- **The truncation regrouping** (*FI* (16.30)–(16.34), sum form). -/
theorem Zsfun_regroup (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) {s : ℂ}
    (hs : 1 < s.re) (hchi1 : chi 1 = 1)
    (hchimul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w)
    (hchibd : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) :
    Work.FIArea6.TauPieces.Zsfun Pa chi m s
      = ∑ c ∈ (sfin Pa).filter (fun c => Squarefree c ∧ Nat.Coprime c (PiPr Pa)),
          Work.FIArea5.S16Hecke.heckeLam chi m c * (c : ℂ) ^ (-s)
            * Gser Pa chi m s (c * PiPr Pa) := by
  rw [Zsfun_eq_tsum]
  rw [tsum_congr (fun N => tcoef_mul_eq_sum Pa chi m s N)]
  rw [tsum_congr (fun N => Finset.sum_mul (sfin Pa)
    (fun c => if c ∣ N then (ArithmeticFunction.moebius c : ℂ) else 0)
    (Fcoef Pa chi m s N))]
  rw [Summable.tsum_finsetSum (fun c _ => summable_dvd_indicator Pa chi m hchibd hs c)]
  rw [Finset.sum_congr rfl
    (fun c hc => sum_dvd_Fcoef_eq Pa chi m s hchimul (mem_sfin.mp hc).1)]
  rw [Finset.sum_filter]

end

end Work.FIArea6Road
