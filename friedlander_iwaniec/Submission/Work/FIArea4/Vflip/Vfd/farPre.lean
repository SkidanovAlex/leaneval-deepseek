import Mathlib
import Submission.Work.FIArea4.Vflip.Vfd.VfdDefs
import Submission.Work.FIArea4.Vflip.Vfd.pairSum_large_sieve
import Submission.Work.FIArea4.Vflip.Vfd.separation_ineq_nearCut
import Submission.Work.FIArea4.Vflip.Vfd.pairWeight_flip
import Submission.Work.FIArea4.Vflip.Vfd.pairWeight_aux
import Submission.Work.FIArea4.A4varbounds

/-!
# The flip reindexing of the far sum (FI §12, (12.6)–(12.12))

This module contains the combinatorial core of the far part of the flipped-moduli bound: the
pointwise flip identity `GG_mul_BB`, the four-fold reordering `reindex_far`, the reduction by the
common divisor `far_sum_by_pairC`, and the dyadic pieces `FarIdxI` / `InnerRangeI`.
-/

namespace Work.FIArea4.Vflip.Vfd

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-!
# The far part of the flipped-moduli bound (FI §12, (12.10)–(12.17))

This module is the "crux" of the dyadic Friedlander–Iwaniec Proposition 12.1: the bound for the
*far* part of the smoothly cut bilinear form,
`Σ_{p,q ∈ boxF} α p.1 p.2 · conj (α q.1 q.2) · nearCut a b (xPair p q) · pairWeight D p q`.

The strategy is the paper's §12 (see `fi_all.txt`): reduce the pair by its common divisor `c`,
flip the modulus `d` to the complementary divisor `q` of `pairAbs`, separate the variables by the
Fourier–Mellin transform (`separation_ineq_nearCut`), apply the large sieve
(`pairSum_large_sieve`) in each dyadic range of `q`, and sum over `q`, `m ∣ c` and `c`.
-/

/-! ## Elementary properties of the parameters -/

lemma far_H_pos {D R S : ℕ} {H : ℝ} (hR : 1 ≤ R) (hS : 1 ≤ S) (hD : 1 ≤ D)
    (hH : H = ((R : ℝ) * (S : ℝ) / (D : ℝ)) ^ ((1 : ℝ) / 3)) : 0 < H := by
  rw [hH]; positivity

lemma far_a_pos {R S : ℕ} {H a : ℝ} (hR : 1 ≤ R) (hS : 1 ≤ S) (hH : 0 < H)
    (ha : a = 2 * (S : ℝ) / (H * (R : ℝ))) : 0 < a := by
  rw [ha]; positivity

lemma far_b_pos {R S : ℕ} {b : ℝ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    (hb : b = 2 * (S : ℝ) / (R : ℝ)) : 0 < b := by
  rw [hb]; positivity

/-- `b / a = H`; in particular the separation loss is `(log (2 + H) + 1)²`. -/
lemma far_b_div_a {R S D : ℕ} {H a b : ℝ} (hR : 1 ≤ R) (hS : 1 ≤ S) (hD : 1 ≤ D)
    (hH : H = ((R : ℝ) * (S : ℝ) / (D : ℝ)) ^ ((1 : ℝ) / 3))
    (ha : a = 2 * (S : ℝ) / (H * (R : ℝ))) (hb : b = 2 * (S : ℝ) / (R : ℝ)) :
    b / a = H := by
  subst ha hb
  have hR' : (R : ℝ) ≠ 0 := by positivity
  have hS' : (S : ℝ) ≠ 0 := by positivity
  have hH' : H ≠ 0 := by rw [hH]; positivity
  field_simp

lemma far_a_le_b {R S D : ℕ} {H a b : ℝ} (hR : 1 ≤ R) (hS : 1 ≤ S) (hD : 1 ≤ D)
    (hRS : D ≤ R * S)
    (hH : H = ((R : ℝ) * (S : ℝ) / (D : ℝ)) ^ ((1 : ℝ) / 3))
    (ha : a = 2 * (S : ℝ) / (H * (R : ℝ))) (hb : b = 2 * (S : ℝ) / (R : ℝ)) :
    a ≤ b := by
  subst hH ha hb
  have hRS' : (0 : ℝ) < (R : ℝ) * (S : ℝ) := by positivity
  have hDpos : (0 : ℝ) < D := by positivity
  have hbase : (1 : ℝ) ≤ (R : ℝ) * (S : ℝ) / (D : ℝ) := by
    rw [le_div_iff₀ hDpos]
    have h : (D : ℝ) ≤ (R : ℝ) * (S : ℝ) := by exact_mod_cast hRS
    linarith
  have hH1 : (1 : ℝ) ≤ ((R : ℝ) * (S : ℝ) / (D : ℝ)) ^ ((1 : ℝ) / 3) :=
    Real.one_le_rpow hbase (by norm_num)
  refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
  calc (R : ℝ) = 1 * (R : ℝ) := by ring
    _ ≤ ((R : ℝ) * (S : ℝ) / (D : ℝ)) ^ ((1 : ℝ) / 3) * (R : ℝ) :=
        mul_le_mul_of_nonneg_right hH1 (by positivity)

/-- The modulus `2 * s` forces `r` odd. -/
lemma far_odd_of_coprime_two_mul {r s : ℕ} (h : Nat.Coprime r (2 * s)) : Odd r := by
  by_contra hodd
  rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hodd
  have hdvd : 2 ∣ Nat.gcd r (2 * s) := Nat.dvd_gcd hodd (dvd_mul_right 2 s)
  rw [show Nat.gcd r (2*s) = 1 from h] at hdvd
  exact absurd hdvd (by norm_num)

lemma far_coprime_swap {r s : ℕ} (h : Nat.Coprime r (2 * s)) : Nat.Coprime s r :=
  (h.coprime_dvd_right (Nat.dvd_mul_left s 2)).symm

/-! ## The dyadic box -/

lemma mem_boxF {R S : ℕ} {p : ℕ × ℕ} :
    p ∈ boxF R S ↔ R < p.1 ∧ p.1 ≤ 2 * R ∧ S < p.2 ∧ p.2 ≤ 2 * S := by
  rw [boxF, Finset.mem_product, Finset.mem_Ioc, Finset.mem_Ioc]
  tauto

lemma mem_boxF_pos {R S : ℕ} {p : ℕ × ℕ} (h : p ∈ boxF R S) : 0 < p.1 ∧ 0 < p.2 := by
  rw [mem_boxF] at h
  exact ⟨by omega, by omega⟩

/-! ## `xPair`, `pairAbs` and the reduction of a pair -/

lemma xPair_self (p : ℕ × ℕ) : xPair p p = 0 := by
  simp [xPair]

lemma pairC_pos {r1 r2 : ℕ} (h1 : 0 < r1) : 0 < pairC r1 r2 :=
  Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left r1 r2) h1

lemma pairR_pos {r1 r2 : ℕ} (h1 : 0 < r1) : 0 < pairR r1 r2 := by
  rw [pairR]
  exact Nat.div_pos (Nat.gcd_le_left r2 h1) (pairC_pos h1)

lemma pairC_mul_pairR_left' (r1 r2 : ℕ) : (pairC r1 r2 : ℝ) * (pairR r1 r2 : ℝ) = r1 := by
  rw [← Nat.cast_mul, pairC_mul_pairR_left]

lemma pairC_mul_pairR_right' (r1 r2 : ℕ) : (pairC r1 r2 : ℝ) * (pairR r2 r1 : ℝ) = r2 := by
  rw [← Nat.cast_mul, pairC_mul_pairR_right]

lemma natAbs_cast_real (z : ℤ) : ((z.natAbs : ℕ) : ℝ) = |(z : ℝ)| := by
  have hz : (z:ℝ) = ((z.natAbs:ℕ):ℝ) ∨ (z:ℝ) = -((z.natAbs:ℕ):ℝ) := by
    rcases Int.natAbs_eq z with h|h
    · left; rw [h]; simp
    · right; rw [h]; simp
  rcases hz with h|h
  · rw [h, abs_of_nonneg (Nat.cast_nonneg _)]
  · rw [h, abs_neg, abs_of_nonneg (Nat.cast_nonneg _)]

lemma abs_xPair_mul_nat (r1 s1 r2 s2 : ℕ) (h1 : 0 < r1) (h2 : 0 < r2) :
    |xPair (r1, s1) (r2, s2)| * ((r1:ℝ)*(r2:ℝ))
      = (((r1:ℤ)*(s2:ℤ)-(r2:ℤ)*(s1:ℤ):ℤ).natAbs : ℝ) := by
  have h1' : (0:ℝ) < (r1:ℝ) := by exact_mod_cast h1
  have h2' : (0:ℝ) < (r2:ℝ) := by exact_mod_cast h2
  have hx : xPair (r1,s1) (r2,s2) = ((s1:ℝ)*(r2:ℝ)-(s2:ℝ)*(r1:ℝ))/((r1:ℝ)*(r2:ℝ)) := by
    rw [xPair]; field_simp
  rw [hx, abs_div, abs_of_pos (by positivity : (0:ℝ)<(r1:ℝ)*(r2:ℝ))]
  rw [show |(s1:ℝ)*(r2:ℝ)-(s2:ℝ)*(r1:ℝ)| = |((r1:ℝ)*(s2:ℝ)-(r2:ℝ)*(s1:ℝ))| by
    rw [show ((r1:ℝ)*(s2:ℝ)-(r2:ℝ)*(s1:ℝ)) = -((s1:ℝ)*(r2:ℝ)-(s2:ℝ)*(r1:ℝ)) by ring, abs_neg]]
  rw [div_mul_eq_mul_div, mul_div_cancel_right₀ _ (by positivity : ((r1:ℝ)*(r2:ℝ)) ≠ 0)]
  rw [natAbs_cast_real]
  push_cast
  ring

/-- `|xPair p q| · (c · ρ₁ · ρ₂) = pairAbs p q` with `c = pairC`, `ρᵢ = pairR`: this identity
turns the flipped weight `bump (pairAbs / (q·D))` into `bump (|xPair| · y)`, `y = c·ρ₁·ρ₂/(q·D)`. -/
lemma abs_xPair_mul (r1 s1 r2 s2 : ℕ) (h1 : 0 < r1) (h2 : 0 < r2) :
    |xPair (r1, s1) (r2, s2)| * ((pairC r1 r2 : ℝ) * (pairR r1 r2 : ℝ) * (pairR r2 r1 : ℝ))
      = (pairAbs r1 r2 s1 s2 : ℝ) := by
  have hr1 : (r1:ℝ) = (pairC r1 r2 : ℝ) * (pairR r1 r2 : ℝ) := (pairC_mul_pairR_left' r1 r2).symm
  have hr2 : (r2:ℝ) = (pairC r1 r2 : ℝ) * (pairR r2 r1 : ℝ) := (pairC_mul_pairR_right' r1 r2).symm
  have hpc : (0:ℝ) < (pairC r1 r2 : ℝ) := by
    exact_mod_cast pairC_pos h1
  have hnat_eq : (((r1:ℤ)*(s2:ℤ)-(r2:ℤ)*(s1:ℤ):ℤ).natAbs) = pairC r1 r2 * pairAbs r1 r2 s1 s2 :=
    (pairC_mul_pairAbs_eq r1 r2 s1 s2).symm
  have keyA : |xPair (r1, s1) (r2, s2)| * ((r1:ℝ)*(r2:ℝ))
      = (pairC r1 r2 : ℝ) * (pairAbs r1 r2 s1 s2 : ℝ) := by
    rw [abs_xPair_mul_nat r1 s1 r2 s2 h1 h2, hnat_eq]
    push_cast; ring
  have hrprod : (r1:ℝ)*(r2:ℝ)
      = (pairC r1 r2 : ℝ) * ((pairC r1 r2 : ℝ) * ((pairR r1 r2 : ℝ) * (pairR r2 r1 : ℝ))) := by
    rw [hr1, hr2]; ring
  rw [hrprod] at keyA
  have : (pairC r1 r2 : ℝ)
      * (|xPair (r1, s1) (r2, s2)| * ((pairC r1 r2 : ℝ) * (pairR r1 r2 : ℝ) * (pairR r2 r1 : ℝ))
          - (pairAbs r1 r2 s1 s2 : ℝ)) = 0 := by nlinarith [keyA]
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hpc.ne')

/-! ## The coprime-constrained pair sum (the "`(r₁,r₂) = 1`" large sieve) -/

/-- The flipped factor `bump (pairAbs / (q·D))` times the flipped Jacobi weight
`(ρ₁|q')(ρ₂|q')`; the summand of the flipped modulus sum of FI (12.10). -/
def flipWeight (D q : ℕ) (r1 s1 r2 s2 : ℕ) : ℂ :=
  (bump (((pairAbs r1 r2 s1 s2 / q : ℕ) : ℝ) / D) : ℂ) *
    ((jacobiSym ((pairR r1 r2 : ℕ) : ℤ) (Work.FIPlan.oddPart q) *
      jacobiSym ((pairR r2 r1 : ℕ) : ℤ) (Work.FIPlan.oddPart q) : ℤ) : ℂ)

/-- The constant `(s₁|ρ₁)(s₂|ρ₂)` produced by the reciprocity flip. -/
def flipCoef (r1 s1 r2 s2 : ℕ) : ℂ :=
  ((jacobiSym (s1 : ℤ) (pairR r1 r2) * jacobiSym (s2 : ℤ) (pairR r2 r1) : ℤ) : ℂ)

/-! ## The flip reindexing (FI (12.8)–(12.10)) -/

/-- The pair weight before the Möbius/flip reduction, with the smooth cutoff and the flip constant
attached: `α_p conj(α_q) nearCut(x_{pq}) (s₁|ρ₁)(s₂|ρ₂)`. -/
def GG (a b : ℝ) (α : ℕ → ℕ → ℂ) (p q : ℕ × ℕ) : ℂ :=
  α p.1 p.2 * star (α q.1 q.2) * ((nearCut a b (xPair p q) : ℝ) : ℂ) * flipCoef p.1 p.2 q.1 q.2

/-- The flipped modulus sum of a pair (FI (12.10)), written as a sum over the *fixed* ranges
`0 ≤ m ≤ 2R`, `0 ≤ q ≤ 4RS` with the divisor conditions as indicators, so that the sums over the
pair `(p,q)` and over `(m,q)` can be interchanged. -/
def BB (D R S : ℕ) (p q : ℕ × ℕ) : ℂ :=
  ∑ m ∈ Finset.range (2*R+1), ∑ q' ∈ Finset.range (4*R*S+1),
    (if 0 < pairAbs p.1 q.1 p.2 q.2 ∧ m ∣ pairC p.1 q.1 ∧ m*q' ∣ pairAbs p.1 q.1 p.2 q.2
     then (ArithmeticFunction.moebius m : ℂ) * flipWeight D q' p.1 p.2 q.1 q.2 else 0)

lemma natAbs_sub_le_max' (u v : ℕ) : (((u:ℤ) - (v:ℤ)).natAbs) ≤ max u v := by
  rcases le_total u v with h | h
  · have h2 : ((u:ℤ) - (v:ℤ)) = -(((v:ℤ) - (u:ℤ))) := by ring
    rw [h2, Int.natAbs_neg]
    have h3 : ((v:ℤ) - (u:ℤ)) = ((v - u : ℕ) : ℤ) := by omega
    rw [h3, Int.natAbs_natCast]
    omega
  · have h3 : ((u:ℤ) - (v:ℤ)) = ((u - v : ℕ) : ℤ) := by omega
    rw [h3, Int.natAbs_natCast]
    omega

lemma divisors_sum_conversion (c N : ℕ) (hc : 0 < c) (hN : c ≤ N) (f : ℕ → ℂ) :
    (∑ m ∈ Finset.range (N+1), (if m ∣ c then f m else 0)) = ∑ m ∈ c.divisors, f m := by
  rw [← Finset.sum_filter]
  congr 1
  ext m
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hmN, hdvd⟩
    exact Nat.mem_divisors.mpr ⟨hdvd, hc.ne'⟩
  · intro hm
    rw [Nat.mem_divisors] at hm
    exact ⟨by have := Nat.le_of_dvd hc hm.1; omega, hm.1⟩

lemma divisors_sum_conversion' (c N : ℕ) (hc : 0 < c) (hN : c ≤ N) (P : ℕ → Prop)
    [DecidablePred P] (f : ℕ → ℂ) :
    (∑ m ∈ Finset.range (N+1), (if m ∣ c ∧ P m then f m else 0))
      = ∑ m ∈ c.divisors.filter P, f m := by
  rw [← Finset.sum_filter]
  congr 1
  ext m
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hmN, hdvd, hP⟩
    exact ⟨Nat.mem_divisors.mpr ⟨hdvd, hc.ne'⟩, hP⟩
  · rintro ⟨hm, hP⟩
    rw [Nat.mem_divisors] at hm
    exact ⟨by have := Nat.le_of_dvd hc hm.1; omega, hm.1, hP⟩

/-- The double `range`-sum with the divisor conditions equals the double divisor sum. -/
lemma range_range_to_divisors (c k N M : ℕ) (hc : 0 < c) (hk : 0 < k) (hN : c ≤ N) (hM : k ≤ M)
    (g : ℕ → ℕ → ℂ) :
    (∑ m ∈ Finset.range (N+1), ∑ q' ∈ Finset.range (M+1),
        (if m ∣ c ∧ m*q' ∣ k then g m q' else 0))
      = ∑ m ∈ c.divisors, ∑ q' ∈ k.divisors.filter (fun q' => m*q' ∣ k), g m q' := by
  have hfactor : (∑ m ∈ Finset.range (N+1), ∑ q' ∈ Finset.range (M+1),
        (if m ∣ c ∧ m*q' ∣ k then g m q' else 0))
      = ∑ m ∈ Finset.range (N+1), (if m ∣ c then (∑ q' ∈ Finset.range (M+1),
          (if m*q' ∣ k then g m q' else 0)) else 0) := by
    refine Finset.sum_congr rfl (fun m hm => ?_)
    by_cases hmc : m ∣ c
    · rw [if_pos hmc]
      refine Finset.sum_congr rfl (fun q' hq' => ?_)
      by_cases hq : m*q' ∣ k
      · rw [if_pos ⟨hmc, hq⟩, if_pos hq]
      · rw [if_neg (fun h => hq h.2), if_neg hq]
    · rw [if_neg hmc]
      exact Finset.sum_eq_zero (fun q' hq' => by rw [if_neg (fun h => hmc h.1)])
  rw [hfactor]
  rw [divisors_sum_conversion c N hc hN
        (fun m => ∑ q' ∈ Finset.range (M+1), (if m*q' ∣ k then g m q' else 0))]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  rw [show (∑ q' ∈ Finset.range (M+1), (if m*q' ∣ k then g m q' else 0))
        = ∑ q' ∈ Finset.range (M+1), (if q' ∣ k ∧ m*q' ∣ k then g m q' else 0) from ?_]
  · rw [divisors_sum_conversion' k M hk hM (fun q' => m*q' ∣ k) (fun q' => g m q')]
  · refine Finset.sum_congr rfl (fun q' hq' => ?_)
    by_cases hh : m*q' ∣ k
    · rw [if_pos hh, if_pos ⟨dvd_trans (Nat.dvd_mul_left q' m) hh, hh⟩]
    · rw [if_neg hh, if_neg (fun hc => hh hc.2)]

/-- The dyadic box bounds the reduced moduli and the cross difference. -/
lemma pairC_le_twoR {R S : ℕ} {p q : ℕ × ℕ} (hp : p ∈ boxF R S) :
    pairC p.1 q.1 ≤ 2 * R := by
  rw [mem_boxF] at hp
  exact le_trans (Nat.gcd_le_left _ (by omega)) hp.2.1

lemma pairAbs_le_fourRS {R S : ℕ} {p q : ℕ × ℕ}
    (hp : p ∈ boxF R S) (hq : q ∈ boxF R S) :
    pairAbs p.1 q.1 p.2 q.2 ≤ 4 * R * S := by
  rw [mem_boxF] at hp hq
  have h1 : pairR p.1 q.1 ≤ 2 * R := le_trans (Nat.div_le_self _ _) hp.2.1
  have h2 : pairR q.1 p.1 ≤ 2 * R := le_trans (Nat.div_le_self _ _) hq.2.1
  have key : pairAbs p.1 q.1 p.2 q.2 ≤ max (pairR p.1 q.1 * q.2) (pairR q.1 p.1 * p.2) := by
    rw [pairAbs]
    exact natAbs_sub_le_max' _ _
  refine le_trans key ?_
  apply max_le
  · calc pairR p.1 q.1 * q.2 ≤ (2*R) * (2*S) := Nat.mul_le_mul h1 hq.2.2.2
      _ = 4 * R * S := by ring
  · calc pairR q.1 p.1 * p.2 ≤ (2*R) * (2*S) := Nat.mul_le_mul h2 hp.2.2.2
      _ = 4 * R * S := by ring

/-- **The flipped form of `pairWeight`** (the `range`-sum version of `pairWeight_flip`). -/
lemma BB_eq_pairWeight_flip (D R S : ℕ) {r1 s1 r2 s2 : ℕ}
    (hr1 : 0 < r1)
    (hodd1 : Odd r1) (hodd2 : Odd r2) (h8 : r1 % 8 = r2 % 8)
    (hs1 : Nat.Coprime s1 r1) (hs2 : Nat.Coprime s2 r2)
    (hA : 0 < pairAbs r1 r2 s1 s2)
    (hpc : pairC r1 r2 ≤ 2*R) (hpa : pairAbs r1 r2 s1 s2 ≤ 4*R*S) :
    pairWeight D (r1,s1) (r2,s2)
      = flipCoef r1 s1 r2 s2 *
        (∑ m ∈ Finset.range (2*R+1), ∑ q' ∈ Finset.range (4*R*S+1),
          (if 0 < pairAbs r1 r2 s1 s2 ∧ m ∣ pairC r1 r2 ∧ m*q' ∣ pairAbs r1 r2 s1 s2
           then (ArithmeticFunction.moebius m : ℂ) * flipWeight D q' r1 s1 r2 s2 else 0)) := by
  have hflip := pairWeight_flip D r1 s1 r2 s2 hodd1 hodd2 h8 hs1 hs2 hA
  rw [hflip]
  congr 1
  rw [show (∑ m ∈ Finset.range (2*R+1), ∑ q' ∈ Finset.range (4*R*S+1),
          (if 0 < pairAbs r1 r2 s1 s2 ∧ m ∣ pairC r1 r2 ∧ m*q' ∣ pairAbs r1 r2 s1 s2
           then (ArithmeticFunction.moebius m : ℂ) * flipWeight D q' r1 s1 r2 s2 else 0))
      = ∑ m ∈ Finset.range (2*R+1), ∑ q' ∈ Finset.range (4*R*S+1),
          (if m ∣ pairC r1 r2 ∧ m*q' ∣ pairAbs r1 r2 s1 s2
           then (ArithmeticFunction.moebius m : ℂ) * flipWeight D q' r1 s1 r2 s2 else 0) from ?_]
  · conv_rhs => rw [range_range_to_divisors (pairC r1 r2) (pairAbs r1 r2 s1 s2) (2*R) (4*R*S)
        (pairC_pos hr1) hA hpc hpa
        (fun m q' => (ArithmeticFunction.moebius m : ℂ) * flipWeight D q' r1 s1 r2 s2)]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun q' hq' => ?_)
    simp only [flipWeight]
  · refine Finset.sum_congr rfl (fun m hm => Finset.sum_congr rfl (fun q' hq' => ?_))
    by_cases hh : m ∣ pairC r1 r2 ∧ m*q' ∣ pairAbs r1 r2 s1 s2
    · rw [if_pos ⟨hA, hh.1, hh.2⟩, if_pos hh]
    · rw [if_neg (fun h => hh ⟨h.2.1, h.2.2⟩), if_neg hh]

/-- `xPair = 0` exactly on the diagonal `pairAbs = 0`. -/
lemma xPair_eq_zero_iff (r1 s1 r2 s2 : ℕ) (h1 : 0 < r1) (h2 : 0 < r2) :
    xPair (r1, s1) (r2, s2) = 0 ↔ pairAbs r1 r2 s1 s2 = 0 := by
  have hρ1 : 0 < pairR r1 r2 := pairR_pos h1
  have hρ2 : 0 < pairR r2 r1 :=
    Nat.div_pos (Nat.gcd_le_left _ h2) (pairC_pos h2)
  have hpos : (0:ℝ) < (pairC r1 r2 : ℝ) * (pairR r1 r2 : ℝ) * (pairR r2 r1 : ℝ) :=
    mul_pos (mul_pos (by exact_mod_cast pairC_pos (r2 := r2) h1) (by exact_mod_cast hρ1))
      (by exact_mod_cast hρ2)
  have h := abs_xPair_mul r1 s1 r2 s2 h1 h2
  constructor
  · intro hx
    rw [hx, abs_zero, zero_mul] at h
    exact_mod_cast h.symm
  · intro hp
    have h0 : |xPair (r1, s1) (r2, s2)|
        * ((pairC r1 r2 : ℝ) * (pairR r1 r2 : ℝ) * (pairR r2 r1 : ℝ)) = 0 := by
      rw [h, hp]; norm_num
    have := (mul_eq_zero.mp h0).resolve_right hpos.ne'
    rwa [abs_eq_zero] at this

/-- **The pointwise flip identity for the far sum**: the summand of `Vflip_far_bound` is
`GG · BB`, so that the `(m, q)`-sums can be moved outside. -/
lemma GG_mul_BB (D R S : ℕ) (a b : ℝ) (α : ℕ → ℕ → ℂ) (ha : 0 < a)
    (hcop : ∀ r s, α r s ≠ 0 → Nat.Coprime r (2 * s))
    (hcls : ∀ r s, α r s ≠ 0 → ∀ r' s', α r' s' ≠ 0 → r % 8 = r' % 8)
    {p q : ℕ × ℕ} (hp : p ∈ boxF R S) (hq : q ∈ boxF R S) :
    α p.1 p.2 * star (α q.1 q.2) * ((nearCut a b (xPair p q) : ℝ) : ℂ) * pairWeight D p q
      = GG a b α p q * BB D R S p q := by
  by_cases hαp : α p.1 p.2 = 0
  · simp [hαp, GG]
  by_cases hαq : α q.1 q.2 = 0
  · simp [hαq, GG]
  by_cases hg : nearCut a b (xPair p q) = 0
  · rw [hg, GG, hg]
    simp
  · have hx : xPair (p.1,p.2) (q.1,q.2) ≠ 0 := fun hx0 => hg (by rw [hx0]; exact nearCut_zero a b ha)
    have hppos : 0 < p.1 := (mem_boxF_pos hp).1
    have hqpos : 0 < q.1 := (mem_boxF_pos hq).1
    have hpa : 0 < pairAbs p.1 q.1 p.2 q.2 :=
      Nat.pos_of_ne_zero (fun h => hx ((xPair_eq_zero_iff p.1 p.2 q.1 q.2 hppos hqpos).mpr h))
    have hodd1 : Odd p.1 := far_odd_of_coprime_two_mul (hcop p.1 p.2 hαp)
    have hodd2 : Odd q.1 := far_odd_of_coprime_two_mul (hcop q.1 q.2 hαq)
    have hs1 : Nat.Coprime p.2 p.1 := far_coprime_swap (hcop p.1 p.2 hαp)
    have hs2 : Nat.Coprime q.2 q.1 := far_coprime_swap (hcop q.1 q.2 hαq)
    have h8 : p.1 % 8 = q.1 % 8 := hcls p.1 p.2 hαp q.1 q.2 hαq
    have hflip : pairWeight D (p.1,p.2) (q.1,q.2)
        = flipCoef p.1 p.2 q.1 q.2 * BB D R S (p.1,p.2) (q.1,q.2) := by
      rw [BB_eq_pairWeight_flip D R S hppos hodd1 hodd2 h8 hs1 hs2 hpa
        (pairC_le_twoR hp) (pairAbs_le_fourRS hp hq)]
      simp only [BB]
    have hflip' : pairWeight D p q = flipCoef p.1 p.2 q.1 q.2 * BB D R S p q := by
      simpa using hflip
    rw [hflip', GG]
    ring

/-- The summand of the flipped, reindexed far sum. -/
def FarBody (D : ℕ) (a b : ℝ) (α : ℕ → ℕ → ℂ) (p q : ℕ × ℕ) (m q' : ℕ) : ℂ :=
  if 0 < pairAbs p.1 q.1 p.2 q.2 ∧ m ∣ pairC p.1 q.1 ∧ m*q' ∣ pairAbs p.1 q.1 p.2 q.2
    then (ArithmeticFunction.moebius m : ℂ) * (GG a b α p q * flipWeight D q' p.1 p.2 q.1 q.2)
    else 0

/-- `FarBody` is `GG` times the flipped summand. -/
lemma FarBody_eq (D : ℕ) (a b : ℝ) (α : ℕ → ℕ → ℂ) (p q : ℕ × ℕ) (m q' : ℕ) :
    FarBody D a b α p q m q' =
      (if 0 < pairAbs p.1 q.1 p.2 q.2 ∧ m ∣ pairC p.1 q.1 ∧ m*q' ∣ pairAbs p.1 q.1 p.2 q.2
        then (ArithmeticFunction.moebius m : ℂ) * (GG a b α p q * flipWeight D q' p.1 p.2 q.1 q.2)
        else 0) := rfl

/-- **Pure four-fold reordering** of the far sum. -/
lemma far_reorder (D : ℕ) (a b : ℝ) (α : ℕ → ℕ → ℂ) (R S : ℕ) :
    (∑ p ∈ boxF R S, ∑ q ∈ boxF R S, ∑ m ∈ Finset.range (2*R+1),
        ∑ q' ∈ Finset.range (4*R*S+1), FarBody D a b α p q m q')
      = ∑ m ∈ Finset.range (2*R+1), ∑ q' ∈ Finset.range (4*R*S+1),
          ∑ p ∈ boxF R S, ∑ q ∈ boxF R S, FarBody D a b α p q m q' := by
  calc ∑ p ∈ boxF R S, ∑ q ∈ boxF R S, ∑ m ∈ Finset.range (2*R+1),
        ∑ q' ∈ Finset.range (4*R*S+1), FarBody D a b α p q m q'
      = ∑ p ∈ boxF R S, ∑ q ∈ boxF R S,
          ∑ y ∈ Finset.range (2*R+1) ×ˢ Finset.range (4*R*S+1),
            FarBody D a b α p q y.1 y.2 := by
        refine Finset.sum_congr rfl (fun p hp => Finset.sum_congr rfl (fun q hq => ?_))
        exact (Finset.sum_product (Finset.range (2*R+1)) (Finset.range (4*R*S+1))
          (fun y : ℕ × ℕ => FarBody D a b α p q y.1 y.2)).symm
    _ = ∑ x ∈ boxF R S ×ˢ boxF R S,
          ∑ y ∈ Finset.range (2*R+1) ×ˢ Finset.range (4*R*S+1),
            FarBody D a b α x.1 x.2 y.1 y.2 := by
        exact (Finset.sum_product (boxF R S) (boxF R S)
          (fun x : (ℕ × ℕ) × (ℕ × ℕ) => ∑ y ∈ Finset.range (2*R+1) ×ˢ Finset.range (4*R*S+1),
            FarBody D a b α x.1 x.2 y.1 y.2)).symm
    _ = ∑ y ∈ Finset.range (2*R+1) ×ˢ Finset.range (4*R*S+1),
          ∑ x ∈ boxF R S ×ˢ boxF R S, FarBody D a b α x.1 x.2 y.1 y.2 :=
        Finset.sum_comm
    _ = ∑ m ∈ Finset.range (2*R+1), ∑ q' ∈ Finset.range (4*R*S+1),
          ∑ x ∈ boxF R S ×ˢ boxF R S, FarBody D a b α x.1 x.2 m q' := by
        exact Finset.sum_product (Finset.range (2*R+1)) (Finset.range (4*R*S+1))
          (fun y : ℕ × ℕ => ∑ x ∈ boxF R S ×ˢ boxF R S, FarBody D a b α x.1 x.2 y.1 y.2)
    _ = ∑ m ∈ Finset.range (2*R+1), ∑ q' ∈ Finset.range (4*R*S+1),
          ∑ p ∈ boxF R S, ∑ q ∈ boxF R S, FarBody D a b α p q m q' := by
        refine Finset.sum_congr rfl (fun m hm => Finset.sum_congr rfl (fun q' hq' => ?_))
        exact Finset.sum_product (boxF R S) (boxF R S)
          (fun x : (ℕ × ℕ) × (ℕ × ℕ) => FarBody D a b α x.1 x.2 m q')

/-- **The reindexing of the far sum** (FI (12.8)–(12.10)): the `(m,q)`-sums are moved outside. -/
lemma reindex_far (D R S : ℕ) (a b : ℝ) (α : ℕ → ℕ → ℂ) :
    (∑ p ∈ boxF R S, ∑ q ∈ boxF R S, GG a b α p q * BB D R S p q)
      = ∑ m ∈ Finset.range (2*R+1), ∑ q' ∈ Finset.range (4*R*S+1),
          (ArithmeticFunction.moebius m : ℂ) *
            ∑ p ∈ boxF R S, ∑ q ∈ boxF R S,
              (if 0 < pairAbs p.1 q.1 p.2 q.2 ∧ m ∣ pairC p.1 q.1
                  ∧ m*q' ∣ pairAbs p.1 q.1 p.2 q.2
               then GG a b α p q * flipWeight D q' p.1 p.2 q.1 q.2 else 0) := by
  have hstep1 : (∑ p ∈ boxF R S, ∑ q ∈ boxF R S, GG a b α p q * BB D R S p q)
      = ∑ p ∈ boxF R S, ∑ q ∈ boxF R S, ∑ m ∈ Finset.range (2*R+1),
          ∑ q' ∈ Finset.range (4*R*S+1), FarBody D a b α p q m q' := by
    simp only [BB, FarBody]
    refine Finset.sum_congr rfl (fun p hp => Finset.sum_congr rfl (fun q hq => ?_))
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun q' hq' => ?_)
    by_cases h : 0 < pairAbs p.1 q.1 p.2 q.2 ∧ m ∣ pairC p.1 q.1
        ∧ m*q' ∣ pairAbs p.1 q.1 p.2 q.2
    · rw [if_pos h, if_pos h]; ring
    · rw [if_neg h, if_neg h, mul_zero]
  rw [hstep1, far_reorder]
  refine Finset.sum_congr rfl (fun m hm => Finset.sum_congr rfl (fun q' hq' => ?_))
  rw [show (∑ p ∈ boxF R S, ∑ q ∈ boxF R S, FarBody D a b α p q m q')
        = (ArithmeticFunction.moebius m : ℂ) *
          ∑ p ∈ boxF R S, ∑ q ∈ boxF R S,
            (if 0 < pairAbs p.1 q.1 p.2 q.2 ∧ m ∣ pairC p.1 q.1
                ∧ m*q' ∣ pairAbs p.1 q.1 p.2 q.2
             then GG a b α p q * flipWeight D q' p.1 p.2 q.1 q.2 else 0) from ?_]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun q hq => ?_)
  simp only [FarBody]
  by_cases h : 0 < pairAbs p.1 q.1 p.2 q.2 ∧ m ∣ pairC p.1 q.1
      ∧ m*q' ∣ pairAbs p.1 q.1 p.2 q.2
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, mul_zero]

/-- **The reduction by the common divisor** `c = pairC r₁ r₂`. -/
lemma far_sum_by_pairC (R S : ℕ) (F : (ℕ×ℕ) → (ℕ×ℕ) → ℂ) (c : ℕ) :
    (∑ y ∈ (boxF R S ×ˢ boxF R S).filter (fun y : (ℕ×ℕ)×(ℕ×ℕ) => pairC y.1.1 y.2.1 = c),
        F y.1 y.2)
    = ∑ x ∈ (((Finset.range (2*R+1) ×ˢ Finset.range (2*S+1)) ×ˢ
              (Finset.range (2*R+1) ×ˢ Finset.range (2*S+1))).filter
              (fun x : (ℕ×ℕ)×(ℕ×ℕ) => 0 < c ∧ Nat.Coprime x.1.1 x.2.1
                ∧ R < c*x.1.1 ∧ c*x.1.1 ≤ 2*R ∧ R < c*x.2.1 ∧ c*x.2.1 ≤ 2*R
                ∧ S < x.1.2 ∧ x.1.2 ≤ 2*S ∧ S < x.2.2 ∧ x.2.2 ≤ 2*S)),
        F (c*x.1.1, x.1.2) (c*x.2.1, x.2.2) := by
  refine Finset.sum_nbij'
    (fun y : (ℕ×ℕ)×(ℕ×ℕ) => ((pairR y.1.1 y.2.1, y.1.2), (pairR y.2.1 y.1.1, y.2.2)))
    (fun x : (ℕ×ℕ)×(ℕ×ℕ) => ((c*x.1.1, x.1.2), (c*x.2.1, x.2.2))) ?_ ?_ ?_ ?_ ?_
  · intro y hy
    rw [Finset.mem_filter, Finset.mem_product] at hy
    obtain ⟨⟨hy1, hy2⟩, hc⟩ := hy
    rw [mem_boxF] at hy1 hy2
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    have hy1p : 0 < y.1.1 := by omega
    have hcpos : 0 < pairC y.1.1 y.2.1 := pairC_pos hy1p
    have hcop : Nat.Coprime (pairR y.1.1 y.2.1) (pairR y.2.1 y.1.1) := by
      simp only [pairR, pairC, Nat.gcd_comm y.2.1 y.1.1]
      exact Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_left _ hy1p)
    have e1 : c * pairR y.1.1 y.2.1 = y.1.1 := by
      rw [← hc]; exact pairC_mul_pairR_left y.1.1 y.2.1
    have e2 : c * pairR y.2.1 y.1.1 = y.2.1 := by
      rw [← hc]; exact pairC_mul_pairR_right y.1.1 y.2.1
    refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, hc ▸ hcpos, hcop, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have h : pairR y.1.1 y.2.1 ≤ 2*R := le_trans (Nat.div_le_self _ _) hy1.2.1
      omega
    · omega
    · have h : pairR y.2.1 y.1.1 ≤ 2*R := le_trans (Nat.div_le_self _ _) hy2.2.1
      omega
    · omega
    · rw [e1]; exact hy1.1
    · rw [e1]; exact hy1.2.1
    · rw [e2]; exact hy2.1
    · rw [e2]; exact hy2.2.1
    · exact hy1.2.2.1
    · exact hy1.2.2.2
    · exact hy2.2.2.1
    · exact hy2.2.2.2
  · intro x hx
    simp only [Finset.mem_filter] at hx
    obtain ⟨hxt, hc, hcop, h1a, h1b, h2a, h2b, h3a, h3b, h4a, h4b⟩ := hx
    simp only [Finset.mem_filter, Finset.mem_product, mem_boxF]
    refine ⟨⟨⟨h1a, h1b, h3a, h3b⟩, ⟨h2a, h2b, h4a, h4b⟩⟩, ?_⟩
    rw [pairC, Nat.gcd_mul_left, hcop.gcd_eq_one, mul_one]
  · intro y hy
    rw [Finset.mem_filter] at hy
    obtain ⟨_, hc⟩ := hy
    have e1 : c * pairR y.1.1 y.2.1 = y.1.1 := by
      rw [← hc]; exact pairC_mul_pairR_left y.1.1 y.2.1
    have e2 : c * pairR y.2.1 y.1.1 = y.2.1 := by
      rw [← hc]; exact pairC_mul_pairR_right y.1.1 y.2.1
    simp only [Prod.mk.injEq, and_true, e1, e2]
  · intro x hx
    rw [Finset.mem_filter] at hx
    obtain ⟨hxt, hc, hcop, -⟩ := hx
    have hρ1 : pairR (c*x.1.1) (c*x.2.1) = x.1.1 := by
      simp only [pairR, pairC, Nat.gcd_mul_left, hcop.gcd_eq_one, mul_one]
      exact Nat.mul_div_cancel_left x.1.1 (by omega : 0 < c)
    have hρ2 : pairR (c*x.2.1) (c*x.1.1) = x.2.1 := by
      simp only [pairR, pairC, Nat.gcd_comm, Nat.gcd_mul_left, hcop.gcd_eq_one, mul_one]
      exact Nat.mul_div_cancel_left x.2.1 (by omega : 0 < c)
    simp only [Prod.mk.injEq, and_true, hρ1, hρ2]
  · intro y hy
    rw [Finset.mem_filter] at hy
    obtain ⟨_, hc⟩ := hy
    have e1 : c * pairR y.1.1 y.2.1 = y.1.1 := by
      rw [← hc]; exact pairC_mul_pairR_left y.1.1 y.2.1
    have e2 : c * pairR y.2.1 y.1.1 = y.2.1 := by
      rw [← hc]; exact pairC_mul_pairR_right y.1.1 y.2.1
    simp only [Prod.mk.injEq, and_true, e1, e2]

/-- The index set of the far inner sum for a fixed dyadic range `(Q,2Q]` of the flipped divisor. -/
def FarIdx (R S m Q : ℕ) : Finset (ℕ × ((ℕ×ℕ) × (ℕ×ℕ))) :=
  ((Finset.Ioc Q (2*Q)) ×ˢ (boxF R S ×ˢ boxF R S)).filter
    (fun z : ℕ × ((ℕ×ℕ) × (ℕ×ℕ)) =>
      0 < pairAbs z.2.1.1 z.2.2.1 z.2.1.2 z.2.2.2
        ∧ m ∣ pairC z.2.1.1 z.2.2.1
        ∧ m*z.1 ∣ pairAbs z.2.1.1 z.2.2.1 z.2.1.2 z.2.2.2)

lemma mem_FarIdx {R S m Q : ℕ} {z : ℕ × ((ℕ×ℕ) × (ℕ×ℕ))} :
    z ∈ FarIdx R S m Q ↔ Q < z.1 ∧ z.1 ≤ 2*Q ∧ z.2.1 ∈ boxF R S ∧ z.2.2 ∈ boxF R S
      ∧ 0 < pairAbs z.2.1.1 z.2.2.1 z.2.1.2 z.2.2.2
      ∧ m ∣ pairC z.2.1.1 z.2.2.1
      ∧ m*z.1 ∣ pairAbs z.2.1.1 z.2.2.1 z.2.1.2 z.2.2.2 := by
  simp only [FarIdx, Finset.mem_filter, Finset.mem_product, Finset.mem_Ioc]
  tauto

/-- The far inner sum for a fixed dyadic range `(Q,2Q]`. -/
def InnerRange (D R S : ℕ) (a b : ℝ) (α : ℕ → ℕ → ℂ) (m Q : ℕ) : ℂ :=
  ∑ z ∈ FarIdx R S m Q,
    GG a b α z.2.1 z.2.2 * flipWeight D z.1 z.2.1.1 z.2.1.2 z.2.2.1 z.2.2.2

/-- The coefficient of the far inner sum after the separation: `GG` times the flipped Jacobi
weight `(ρ₁|q')(ρ₂|q')`. -/
def FarC (a b : ℝ) (α : ℕ → ℕ → ℂ) (z : ℕ × ((ℕ×ℕ) × (ℕ×ℕ))) : ℂ :=
  α z.2.1.1 z.2.1.2 * star (α z.2.2.1 z.2.2.2) *
    flipCoef z.2.1.1 z.2.1.2 z.2.2.1 z.2.2.2 *
    ((jacobiSym ((pairR z.2.1.1 z.2.2.1 : ℕ) : ℤ) (Work.FIPlan.oddPart z.1) *
      jacobiSym ((pairR z.2.2.1 z.2.1.1 : ℕ) : ℤ) (Work.FIPlan.oddPart z.1) : ℤ) : ℂ)

/-- The separation variable `x` of the far inner sum. -/
def FarX (z : ℕ × ((ℕ×ℕ) × (ℕ×ℕ))) : ℝ := xPair z.2.1 z.2.2

/-- The separation variable `y = c·ρ₁·ρ₂/(q·D)` of the far inner sum. -/
def FarY (D : ℕ) (z : ℕ × ((ℕ×ℕ) × (ℕ×ℕ))) : ℝ :=
  (pairC z.2.1.1 z.2.2.1 : ℝ) * (pairR z.2.1.1 z.2.2.1 : ℝ) * (pairR z.2.2.1 z.2.1.1 : ℝ)
    / ((z.1 * D : ℕ) : ℝ)

/-- The `|x|·y`-argument of the flipped weight is `pairAbs/(q·D)`. -/
lemma bump_arg_eq {D q' : ℕ} {p q : ℕ×ℕ} (h1 : 0 < p.1) (h2 : 0 < q.1) (hq' : 0 < q')
    (hD : 0 < D) (hdvd : q' ∣ pairAbs p.1 q.1 p.2 q.2) :
    |xPair p q| * ((pairC p.1 q.1 : ℝ) * (pairR p.1 q.1 : ℝ) * (pairR q.1 p.1 : ℝ)
        / ((q' * D : ℕ) : ℝ))
      = ((pairAbs p.1 q.1 p.2 q.2 / q' : ℕ) : ℝ) / (D : ℝ) := by
  rw [Nat.cast_div hdvd (by exact_mod_cast hq'.ne')]
  have h := abs_xPair_mul p.1 p.2 q.1 q.2 h1 h2
  have h' : |xPair p q| * ((pairC p.1 q.1 : ℝ) * (pairR p.1 q.1 : ℝ) * (pairR q.1 p.1 : ℝ))
      = (pairAbs p.1 q.1 p.2 q.2 : ℝ) := by simpa using h
  have hq0 : (q' : ℝ) ≠ 0 := by exact_mod_cast hq'.ne'
  have hD0 : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  rw [mul_div_assoc', h']
  field_simp
  push_cast
  ring

lemma FarY_pos {R S m Q D : ℕ} {z : ℕ × ((ℕ×ℕ) × (ℕ×ℕ))} (hD : 0 < D)
    (hz : z ∈ FarIdx R S m Q) : 0 < FarY D z := by
  obtain ⟨hq1, hq2, hp, hq, hpa, hpc, hpq⟩ := mem_FarIdx.mp hz
  have hp1 : 0 < z.2.1.1 := (mem_boxF_pos hp).1
  have hq1' : 0 < z.2.2.1 := (mem_boxF_pos hq).1
  have hq'pos : 0 < z.1 := by omega
  have h1 : (0:ℝ) < (pairC z.2.1.1 z.2.2.1 : ℝ) := by exact_mod_cast pairC_pos hp1
  have h2 : (0:ℝ) < (pairR z.2.1.1 z.2.2.1 : ℝ) := by exact_mod_cast pairR_pos hp1
  have h3 : (0:ℝ) < (pairR z.2.2.1 z.2.1.1 : ℝ) := by exact_mod_cast pairR_pos hq1'
  have h4 : (0:ℝ) < ((z.1 * D : ℕ) : ℝ) := by positivity
  rw [FarY]
  exact div_pos (mul_pos (mul_pos h1 h2) h3) h4

/-- The summand of the far inner sum equals `FarC · (bump (|x|y) · nearCut x)`. -/
lemma InnerRange_summand {R S m Q D : ℕ} {a b : ℝ} {α : ℕ → ℕ → ℂ}
    {z : ℕ × ((ℕ×ℕ) × (ℕ×ℕ))} (hD : 0 < D) (hz : z ∈ FarIdx R S m Q) :
    GG a b α z.2.1 z.2.2 * flipWeight D z.1 z.2.1.1 z.2.1.2 z.2.2.1 z.2.2.2
      = FarC a b α z *
        ((Work.FIArea4.Vflip.bump (|FarX z| * FarY D z) *
          Work.FIArea4.Vflip.nearCut a b (FarX z) : ℝ) : ℂ) := by
  obtain ⟨hq1, hq2, hp, hq, hpa, hpc, hpq⟩ := mem_FarIdx.mp hz
  have hp1 : 0 < z.2.1.1 := (mem_boxF_pos hp).1
  have hq1' : 0 < z.2.2.1 := (mem_boxF_pos hq).1
  have hq'pos : 0 < z.1 := by omega
  have hdvd : z.1 ∣ pairAbs z.2.1.1 z.2.2.1 z.2.1.2 z.2.2.2 :=
    dvd_trans (Nat.dvd_mul_left z.1 m) hpq
  have hbump := bump_arg_eq (D := D) (q' := z.1) (p := z.2.1) (q := z.2.2) hp1 hq1' hq'pos hD hdvd
  simp only [flipWeight, FarC, FarX, FarY, flipCoef, GG]
  rw [hbump]; push_cast; ring

/-- **Fourier–Mellin separation applied to the far inner sum.** If `B` bounds the exponential sums
`Σ c_i e(u x_i) y_i^{it}`, then it bounds the flip sum too, with the loss `(log (2+b/a)+1)²`. -/
lemma far_sep_apply :
    ∃ C : ℝ, 0 < C ∧ ∀ {D R S m Q : ℕ} {a b B : ℝ} {α : ℕ → ℕ → ℂ},
      (ha : 0 < a) → (hab : a ≤ b) → (hD : 0 < D) → (hQ : 1 ≤ Q) →
      (hB : ∀ u t : ℝ, ‖∑ z : ↥(FarIdx R S m Q),
          FarC a b α z.val * Complex.exp (2 * Real.pi * Complex.I * (u * FarX z.val)) *
            ((FarY D z.val : ℝ) : ℂ) ^ (Complex.I * (t : ℂ))‖ ≤ B) →
      ‖InnerRange D R S a b α m Q‖ ≤ C * (Real.log (2 + b / a) + 1) ^ 2 * B := by
  obtain ⟨Cs, hCspos, hsep⟩ := separation_ineq_nearCut
  refine ⟨Cs, hCspos, ?_⟩
  intro D R S m Q a b B α ha hab hD hQ hB
  have hkey := hsep a b ha hab (↥(FarIdx R S m Q)) (fun z => FarX z.val) (fun z => FarY D z.val)
    (fun z => FarC a b α z.val) B (fun z => FarY_pos hD z.2) hB
  have hsum : InnerRange D R S a b α m Q
      = ∑ z : ↥(FarIdx R S m Q),
          FarC a b α z.val *
            ((Work.FIArea4.Vflip.bump (|FarX z.val| * FarY D z.val) *
              Work.FIArea4.Vflip.nearCut a b (FarX z.val) : ℝ) : ℂ) := by
    rw [InnerRange, ← Finset.sum_attach (FarIdx R S m Q)
      (fun z => GG a b α z.2.1 z.2.2 * flipWeight D z.1 z.2.1.1 z.2.1.2 z.2.2.1 z.2.2.2),
      Finset.univ_eq_attach]
    exact Finset.sum_congr rfl (fun z hz => InnerRange_summand hD z.2)
  rw [hsum]
  exact hkey

/-- The index set of a `(m, Q₁, Q₂)`-piece of the far sum: the flipped modulus `q'` runs over
`Q₁ < q' ≤ Q₂`, the pair `(p,q)` over the dyadic box, with the divisibility conditions of the
flip. -/
def FarIdxI (R S m : ℕ) (Q1 Q2 : ℕ) : Finset (ℕ × ((ℕ×ℕ) × (ℕ×ℕ))) :=
  ((Finset.Ioc Q1 Q2) ×ˢ (boxF R S ×ˢ boxF R S)).filter
    (fun z : ℕ × ((ℕ×ℕ) × (ℕ×ℕ)) =>
      0 < pairAbs z.2.1.1 z.2.2.1 z.2.1.2 z.2.2.2
        ∧ m ∣ pairC z.2.1.1 z.2.2.1
        ∧ m*z.1 ∣ pairAbs z.2.1.1 z.2.2.1 z.2.1.2 z.2.2.2)

lemma mem_FarIdxI {R S m Q1 Q2 : ℕ} {z : ℕ × ((ℕ×ℕ) × (ℕ×ℕ))} :
    z ∈ FarIdxI R S m Q1 Q2 ↔ Q1 < z.1 ∧ z.1 ≤ Q2 ∧ z.2.1 ∈ boxF R S ∧ z.2.2 ∈ boxF R S
      ∧ 0 < pairAbs z.2.1.1 z.2.2.1 z.2.1.2 z.2.2.2
      ∧ m ∣ pairC z.2.1.1 z.2.2.1
      ∧ m*z.1 ∣ pairAbs z.2.1.1 z.2.2.1 z.2.1.2 z.2.2.2 := by
  simp only [FarIdxI, Finset.mem_filter, Finset.mem_product, Finset.mem_Ioc]
  tauto

/-- The `(m,Q₁,Q₂)`-piece of the far sum. -/
def InnerRangeI (D R S : ℕ) (a b : ℝ) (α : ℕ → ℕ → ℂ) (m Q1 Q2 : ℕ) : ℂ :=
  ∑ z ∈ FarIdxI R S m Q1 Q2,
    GG a b α z.2.1 z.2.2 * flipWeight D z.1 z.2.1.1 z.2.1.2 z.2.2.1 z.2.2.2

lemma InnerRange_eq_I (D R S : ℕ) (a b : ℝ) (α : ℕ → ℕ → ℂ) (m Q : ℕ) :
    InnerRange D R S a b α m Q = InnerRangeI D R S a b α m Q (2*Q) := rfl

end

end Work.FIArea4.Vflip.Vfd
