import Mathlib
import Submission.Work.FIArea4.A4varbounds
import Submission.Work.FIArea4.PairSumCommon
import Submission.Work.FIArea4.pair_sum_le_Evar
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea4.JacobiChar

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The large sieve for the `d`-sum of the pair sums (FI §§11–12)

This file proves

`‖∑_{D<d≤2D} pairSum R S d β γ‖ ≤ C(ε) · p14T11 D R S ε · (p14L2 R S β)^{1/2} · (p14L2 R S γ)^{1/2}`

for coefficient arrays `β, γ` supported on odd `r`, assuming Friedlander–Iwaniec's
Proposition 11.1 in the form `p14Prop111All` (`Vvar R S D α ≤ C(ε) p14T11 D R S ε p14L2 R S α`).

The proof is the standard large-sieve step:

* for each single `d`, the terms of `pairSum R S d β γ` with `r` not coprime to `d` carry a
  Jacobi factor `(r | d')` with `d' = oddPart d`, which vanishes because `r` is odd; hence the
  pair sum only sees the support with `(r,d) = 1`.  Restricting `β, γ` to that support and
  applying the class decomposition (`pair_sum_le_Evar`) gives
  `‖pairSum R S d β γ‖ ≤ √(Evar d β) √(Evar d γ)`;
* Cauchy–Schwarz over `d ∈ (D, 2D]` upgrades the sum of the products of square roots to the
  product of the square roots of `Vvar R S D β`, `Vvar R S D γ`;
* `h11` controls both variances by `p14T11 D R S ε` times the respective energy.
-/

namespace Work.FIArea4.Vflip.Vfd

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Elementary number theory of `oddPart` -/

/-- The odd part of a positive integer is positive. -/
lemma oddPart_ne_zero (d : ℕ) (hd : 1 ≤ d) : Work.FIPlan.oddPart d ≠ 0 := by
  intro h
  have hmul : 2 ^ d.factorization 2 * Work.FIPlan.oddPart d = d := by
    unfold Work.FIPlan.oddPart
    exact Nat.mul_div_cancel' (Nat.ordProj_dvd d 2)
  rw [h, mul_zero] at hmul
  omega

/-- If `r` is odd and coprime to the odd part of `d`, then `r` is coprime to `d`. -/
lemma coprime_oddPart_of_coprime {d r : ℕ} (hodd : Odd r)
    (h : Nat.Coprime r (Work.FIPlan.oddPart d)) : Nat.Coprime r d := by
  have hmul : d = 2 ^ d.factorization 2 * Work.FIPlan.oddPart d := by
    unfold Work.FIPlan.oddPart
    exact (Nat.mul_div_cancel' (Nat.ordProj_dvd d 2)).symm
  rw [hmul]
  exact (Nat.coprime_two_right.mpr hodd).pow_right (d.factorization 2) |>.mul_right h

/-- For odd `r` not coprime to `d`, the Jacobi weight `(r | d')` of the local variance vanishes. -/
lemma jacobiSym_oddPart_eq_zero {d r : ℕ} (hd : 1 ≤ d) (hr : Odd r)
    (h : ¬ Nat.Coprime r d) : jacobiSym (r : ℤ) (Work.FIPlan.oddPart d) = 0 := by
  rw [jacobiSym.eq_zero_iff]
  refine ⟨oddPart_ne_zero d hd, ?_⟩
  intro hg
  apply h
  apply coprime_oddPart_of_coprime hr
  rw [Nat.Coprime, ← Int.gcd_natCast_natCast r (Work.FIPlan.oddPart d)]
  exact hg

/-! ## Restricting the coefficients to the pairs with `(r,d) = 1` -/

/-- The coefficient array `α` restricted to the pairs whose first coordinate is coprime to `d`. -/
def truncCoeff (d : ℕ) (α : ℕ → ℕ → ℂ) : ℕ → ℕ → ℂ :=
  fun r s => if Nat.Coprime r d then α r s else 0

lemma truncCoeff_of_coprime {d r s : ℕ} (α : ℕ → ℕ → ℂ) (h : Nat.Coprime r d) :
    truncCoeff d α r s = α r s := by
  simp only [truncCoeff, if_pos h]

lemma truncCoeff_coprime (d : ℕ) (α : ℕ → ℕ → ℂ) :
    ∀ r s, truncCoeff d α r s ≠ 0 → Nat.Coprime r d := by
  intro r s h
  by_contra hc
  exact h (by simp only [truncCoeff, if_neg hc])

/-- The Jacobi factor of a single pair summand. -/
def JC (d r1 r2 : ℕ) : ℂ :=
  ((jacobiSym (r1 : ℤ) (Work.FIPlan.oddPart d) * jacobiSym (r2 : ℤ) (Work.FIPlan.oddPart d)
    : ℤ) : ℂ)

/-- A single summand of `pairSum` is unchanged when both coefficient arrays are restricted to
the coprime support: the only points where they differ carry a vanishing Jacobi factor. -/
lemma pairSum_term_eq (d : ℕ) (u v : ℕ → ℕ → ℂ)
    (hu : ∀ r s, u r s ≠ 0 → Odd r) (hv : ∀ r s, v r s ≠ 0 → Odd r) (hd : 1 ≤ d)
    (r1 s1 r2 s2 : ℕ) :
    u r1 s1 * star (v r2 s2) * JC d r1 r2
      = truncCoeff d u r1 s1 * star (truncCoeff d v r2 s2) * JC d r1 r2 := by
  simp only [truncCoeff]
  by_cases h1 : Nat.Coprime r1 d
  · by_cases h2 : Nat.Coprime r2 d
    · rw [if_pos h1, if_pos h2]
    · rw [if_neg h2, star_zero, mul_zero]
      rcases eq_or_ne (v r2 s2) 0 with hv0 | hv0
      · rw [hv0, star_zero, mul_zero]
      · have ho : Odd r2 := hv r2 s2 hv0
        have hjs : jacobiSym (r2 : ℤ) (Work.FIPlan.oddPart d) = 0 :=
          jacobiSym_oddPart_eq_zero hd ho h2
        simp only [JC]
        rw [hjs]
        simp
  · rw [if_neg h1]
    rcases eq_or_ne (u r1 s1) 0 with hu0 | hu0
    · rw [hu0]; ring
    · have ho : Odd r1 := hu r1 s1 hu0
      have hjs : jacobiSym (r1 : ℤ) (Work.FIPlan.oddPart d) = 0 :=
        jacobiSym_oddPart_eq_zero hd ho h1
      simp only [JC]
      rw [hjs]
      simp

/-- **The pair sum only sees the coprime support.**  For coefficient arrays supported on odd `r`,
replacing them by their restrictions to the pairs with `(r,d) = 1` does not change
`pairSum R S d`. -/
lemma pairSum_eq_trunc (R S d : ℕ) (u v : ℕ → ℕ → ℂ)
    (hu : ∀ r s, u r s ≠ 0 → Odd r) (hv : ∀ r s, v r s ≠ 0 → Odd r) (hd : 1 ≤ d) :
    Work.FIArea4.pairSum R S d u v
      = Work.FIArea4.pairSum R S d (truncCoeff d u) (truncCoeff d v) := by
  simp only [Work.FIArea4.pairSum]
  refine Finset.sum_congr rfl (fun r1 _ => Finset.sum_congr rfl (fun s1 _ =>
    Finset.sum_congr rfl (fun r2 _ => Finset.sum_congr rfl (fun s2 _ => ?_))))
  by_cases h : ((r1 * s2 : ℕ) : ZMod d) = ((r2 * s1 : ℕ) : ZMod d)
  · rw [if_pos h, if_pos h]
    exact pairSum_term_eq d u v hu hv hd r1 s1 r2 s2
  · rw [if_neg h, if_neg h]

/-- `Evar` is insensitive to restricting the coefficients to the pairs with `(r,d) = 1`. -/
lemma clsSum_truncCoeff (R S d a : ℕ) (α : ℕ → ℕ → ℂ) :
    Work.FIArea4.clsSum R S d (truncCoeff d α) a = Work.FIArea4.clsSum R S d α a := by
  rw [Work.FIArea4.clsSum, Work.FIArea4.clsSum]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [truncCoeff_of_coprime α
    ((Work.FIArea4.mem_EvarR.mp (Work.FIArea4.mem_EvarCls.mp hp).1).2)]

lemma Evar_truncCoeff (R S d : ℕ) (α : ℕ → ℕ → ℂ) :
    Work.FIPlan.Evar R S d (truncCoeff d α) = Work.FIPlan.Evar R S d α := by
  rw [Work.FIArea4.Evar_eq_sum_normSq_clsSum, Work.FIArea4.Evar_eq_sum_normSq_clsSum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [clsSum_truncCoeff]

/-- **The large-sieve step for a single modulus, under the odd-support hypothesis.** -/
theorem pairSum_le_Evar_odd (R S d : ℕ) (hd : 1 ≤ d) (u v : ℕ → ℕ → ℂ)
    (hu : ∀ r s, u r s ≠ 0 → Odd r) (hv : ∀ r s, v r s ≠ 0 → Odd r) :
    ‖Work.FIArea4.pairSum R S d u v‖
      ≤ Real.sqrt (Work.FIPlan.Evar R S d u) * Real.sqrt (Work.FIPlan.Evar R S d v) := by
  rw [pairSum_eq_trunc R S d u v hu hv hd]
  have h := Work.FIArea4.pair_sum_le_Evar R S d hd (truncCoeff d u) (truncCoeff d v)
    (truncCoeff_coprime d u) (truncCoeff_coprime d v)
  rwa [Evar_truncCoeff R S d u, Evar_truncCoeff R S d v] at h

/-! ## Cauchy–Schwarz over the moduli -/

/-- Cauchy–Schwarz in the form `Σ √a √b ≤ √(Σa) √(Σb)`. -/
lemma sum_sqrt_mul_sqrt_le {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i) :
    ∑ i ∈ s, Real.sqrt (a i) * Real.sqrt (b i)
      ≤ Real.sqrt (∑ i ∈ s, a i) * Real.sqrt (∑ i ∈ s, b i) := by
  set L : ℝ := ∑ i ∈ s, Real.sqrt (a i) * Real.sqrt (b i) with hL
  set A : ℝ := ∑ i ∈ s, a i with hA
  set B : ℝ := ∑ i ∈ s, b i with hB
  have hAnn : 0 ≤ A := Finset.sum_nonneg (fun i hi => ha i hi)
  have hBnn : 0 ≤ B := Finset.sum_nonneg (fun i hi => hb i hi)
  have hLnn : 0 ≤ L :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hRnn : 0 ≤ Real.sqrt A * Real.sqrt B :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsq : L ^ 2 ≤ (Real.sqrt A * Real.sqrt B) ^ 2 := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq s
      (fun i => Real.sqrt (a i)) (fun i => Real.sqrt (b i))
    have h1 : (∑ i ∈ s, Real.sqrt (a i) ^ 2) = A := by
      rw [hA]; exact Finset.sum_congr rfl (fun i hi => Real.sq_sqrt (ha i hi))
    have h2 : (∑ i ∈ s, Real.sqrt (b i) ^ 2) = B := by
      rw [hB]; exact Finset.sum_congr rfl (fun i hi => Real.sq_sqrt (hb i hi))
    have h3 : (Real.sqrt A * Real.sqrt B) ^ 2 = A * B := by
      rw [mul_pow, Real.sq_sqrt hAnn, Real.sq_sqrt hBnn]
    rw [h1, h2] at hcs
    rw [h3, hL]
    exact hcs
  have h := sq_le_sq.mp hsq
  rw [abs_of_nonneg hLnn, abs_of_nonneg hRnn] at h
  rw [hL] at h
  exact h

/-- The elementary identity `√(c t p) √(c t q) = c t p^{1/2} q^{1/2}` for nonnegative reals. -/
lemma sqrt_mul_sqrt_eq (c t p q : ℝ) (hc : 0 ≤ c) (ht : 0 ≤ t) :
    Real.sqrt (c * t * p) * Real.sqrt (c * t * q) = c * t * p ^ ((1 : ℝ) / 2) * q ^ ((1 : ℝ) / 2) := by
  have h1 : Real.sqrt (c * t * p) = Real.sqrt (c * t) * Real.sqrt p :=
    Real.sqrt_mul (by positivity) p
  have h2 : Real.sqrt (c * t * q) = Real.sqrt (c * t) * Real.sqrt q :=
    Real.sqrt_mul (by positivity) q
  have h3 : Real.sqrt (c * t) * Real.sqrt (c * t) = c * t := by
    rw [← sq, Real.sq_sqrt (by positivity)]
  calc Real.sqrt (c * t * p) * Real.sqrt (c * t * q)
      = (Real.sqrt (c * t) * Real.sqrt p) * (Real.sqrt (c * t) * Real.sqrt q) := by rw [h1, h2]
    _ = (Real.sqrt (c * t) * Real.sqrt (c * t)) * (Real.sqrt p * Real.sqrt q) := by ring
    _ = (c * t) * (Real.sqrt p * Real.sqrt q) := by rw [h3]
    _ = c * t * p ^ ((1 : ℝ) / 2) * q ^ ((1 : ℝ) / 2) := by
        rw [Real.sqrt_eq_rpow p, Real.sqrt_eq_rpow q]; ring

/-! ## Nonnegativity of the brackets -/

lemma p14L2_nonneg (R S : ℕ) (α : ℕ → ℕ → ℂ) :
    0 ≤ Work.FIArea4.p14L2 R S α := by
  rw [Work.FIArea4.p14L2]
  exact Finset.sum_nonneg (fun r _ => Finset.sum_nonneg (fun s _ => Complex.normSq_nonneg _))

lemma Evar_nonneg (R S d : ℕ) (α : ℕ → ℕ → ℂ) : 0 ≤ Work.FIPlan.Evar R S d α := by
  rw [Work.FIArea4.Evar_eq_sum_normSq_clsSum]
  exact Finset.sum_nonneg (fun a _ => Complex.normSq_nonneg _)

lemma p14T11_nonneg (D R S : ℕ) (ε : ℝ) : 0 ≤ Work.FIArea4.p14T11 D R S ε := by
  rw [Work.FIArea4.p14T11]
  positivity

/-! ## The main theorem -/

theorem pairSum_large_sieve (h11 : Work.FIArea4.p14Prop111All) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ (D R S : ℕ) (β γ : ℕ → ℕ → ℂ),
      1 ≤ D → 1 ≤ R → 1 ≤ S →
      (∀ r s, β r s ≠ 0 → Odd r) → (∀ r s, γ r s ≠ 0 → Odd r) →
      ‖∑ d ∈ Finset.Ioc D (2 * D), Work.FIArea4.pairSum R S d β γ‖
        ≤ C * Work.FIArea4.p14T11 D R S ε * (Work.FIArea4.p14L2 R S β) ^ ((1 : ℝ) / 2)
            * (Work.FIArea4.p14L2 R S γ) ^ ((1 : ℝ) / 2) := by
  intro ε hε
  obtain ⟨C11, hC11pos, hC11⟩ := h11 ε hε
  refine ⟨C11, hC11pos, ?_⟩
  intro D R S β γ hD hR hS hβ hγ
  have hTnn : 0 ≤ Work.FIArea4.p14T11 D R S ε := p14T11_nonneg D R S ε
  have hPnn : 0 ≤ Work.FIArea4.p14L2 R S β := p14L2_nonneg R S β
  have hQnn : 0 ≤ Work.FIArea4.p14L2 R S γ := p14L2_nonneg R S γ
  have hVβ : Work.FIPlan.Vvar R S D β
      ≤ C11 * Work.FIArea4.p14T11 D R S ε * Work.FIArea4.p14L2 R S β := hC11 D R S β hD hR hS
  have hVγ : Work.FIPlan.Vvar R S D γ
      ≤ C11 * Work.FIArea4.p14T11 D R S ε * Work.FIArea4.p14L2 R S γ := hC11 D R S γ hD hR hS
  calc ‖∑ d ∈ Finset.Ioc D (2 * D), Work.FIArea4.pairSum R S d β γ‖
      ≤ ∑ d ∈ Finset.Ioc D (2 * D), ‖Work.FIArea4.pairSum R S d β γ‖ :=
        norm_sum_le _ _
    _ ≤ ∑ d ∈ Finset.Ioc D (2 * D),
          Real.sqrt (Work.FIPlan.Evar R S d β) * Real.sqrt (Work.FIPlan.Evar R S d γ) :=
        Finset.sum_le_sum (fun d hd => by
          have hd1 : 1 ≤ d := by
            have := (Finset.mem_Ioc.mp hd).1
            omega
          exact pairSum_le_Evar_odd R S d hd1 β γ hβ hγ)
    _ ≤ Real.sqrt (∑ d ∈ Finset.Ioc D (2 * D), Work.FIPlan.Evar R S d β)
          * Real.sqrt (∑ d ∈ Finset.Ioc D (2 * D), Work.FIPlan.Evar R S d γ) :=
        sum_sqrt_mul_sqrt_le _ (fun d => Work.FIPlan.Evar R S d β)
          (fun d => Work.FIPlan.Evar R S d γ)
          (fun d _ => Evar_nonneg R S d β) (fun d _ => Evar_nonneg R S d γ)
    _ = Real.sqrt (Work.FIPlan.Vvar R S D β) * Real.sqrt (Work.FIPlan.Vvar R S D γ) := by
        simp only [Work.FIPlan.Vvar]
    _ ≤ Real.sqrt (C11 * Work.FIArea4.p14T11 D R S ε * Work.FIArea4.p14L2 R S β)
          * Real.sqrt (C11 * Work.FIArea4.p14T11 D R S ε * Work.FIArea4.p14L2 R S γ) :=
        mul_le_mul (Real.sqrt_le_sqrt hVβ) (Real.sqrt_le_sqrt hVγ)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = C11 * Work.FIArea4.p14T11 D R S ε * (Work.FIArea4.p14L2 R S β) ^ ((1 : ℝ) / 2)
          * (Work.FIArea4.p14L2 R S γ) ^ ((1 : ℝ) / 2) :=
        sqrt_mul_sqrt_eq C11 (Work.FIArea4.p14T11 D R S ε) (Work.FIArea4.p14L2 R S β)
          (Work.FIArea4.p14L2 R S γ) hC11pos.le hTnn

end

end Work.FIArea4.Vflip.Vfd
