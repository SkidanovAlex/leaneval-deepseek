import Mathlib
import Submission.Work.FIArea4.A4varbounds
import Submission.Work.FIArea4.PairSumCommon
import Submission.Work.FIArea4.Vflip.Vfd.VfdDefs
import Submission.Work.FIArea4.Vflip.Vfd.pairWeight_aux
import Submission.Work.FIArea4.Vflip.Vfd.pairWeight_flip
import Submission.Work.FIArea4.Vflip.Vfd.pairSum_large_sieve

/-!
# Vocabulary for the far part of the flipped-moduli bound (FI §12)

This module fixes the objects used to bound the *far* part

`Σ_{p,q ∈ boxF} α_p conj(α_q) · nearCut a b (x_{pq}) · pairWeight D p q`

of the flipped-moduli estimate by way of

* the reduction of the pair `(p,q)` by `c = pairC p.1 q.1`, giving the reduced pair
  `(ρ₁,s₁), (ρ₂,s₂)` with `(ρ₁,ρ₂) = 1` and `p.1 = c ρ₁`, `q.1 = c ρ₂`;
* the per-pair flip of `pairWeight_flip`, which replaces the modulus `d` by the complementary
  divisor `q'` and produces the Jacobi weight `(ρ₁|q')(ρ₂|q')`;
* the Fourier–Mellin separation of `bump (|x| y) · nearCut a b x` with the separation arguments

  `x = xPair (c ρ₁, s₁) (c ρ₂, s₂)`,   `y = c ρ₁ ρ₂ / (q' D)`,

  whose product satisfies `|x| · y = pairAbs (cρ₁) (cρ₂) s₁ s₂ / (q' D)` (the argument of the
  flipped smooth weight `bump`; this is `abs_xOrig_mul_ySep` below).

The index set of the `(m,c,Q)`-piece is a Finset of tuples `((q',(ρ₁,s₁)),(ρ₂,s₂))` carrying the
box conditions, the coprimality `(ρ₁,ρ₂) = 1` of the reduced pair and the divisor conditions
`m ∣ c`, `m q' ∣ A`.  As in the paper, the *support* conditions `bump (…) ≠ 0`, `nearCut … ≠ 0`
are **not** part of the index set: the separation inequality is applied to the full family, the
support entering only through the *values* of the smooth weights.
-/

namespace Work.FIArea4.Vflip.Vfd

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Elementary facts about `pairC`, `pairR` and `xPair` -/

lemma far_pairC_pos {r1 r2 : ℕ} (h1 : 0 < r1) : 0 < Work.FIArea4.Vflip.pairC r1 r2 :=
  Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left r1 r2) h1

lemma far_pairR_pos {r1 r2 : ℕ} (h1 : 0 < r1) : 0 < Work.FIArea4.Vflip.pairR r1 r2 := by
  rw [Work.FIArea4.Vflip.pairR]
  exact Nat.div_pos (Nat.gcd_le_left r2 h1) (far_pairC_pos h1)

lemma far_natAbs_cast_real (z : ℤ) : ((z.natAbs : ℕ) : ℝ) = |(z : ℝ)| := by
  have hz : (z:ℝ) = ((z.natAbs:ℕ):ℝ) ∨ (z:ℝ) = -((z.natAbs:ℕ):ℝ) := by
    rcases Int.natAbs_eq z with h|h
    · left; rw [h]; simp
    · right; rw [h]; simp
  rcases hz with h|h
  · rw [h, abs_of_nonneg (Nat.cast_nonneg _)]
  · rw [h, abs_neg, abs_of_nonneg (Nat.cast_nonneg _)]

lemma far_abs_xPair_mul_nat (r1 s1 r2 s2 : ℕ) (h1 : 0 < r1) (h2 : 0 < r2) :
    |Work.FIArea4.Vflip.xPair (r1, s1) (r2, s2)| * ((r1:ℝ)*(r2:ℝ))
      = (((r1:ℤ)*(s2:ℤ)-(r2:ℤ)*(s1:ℤ):ℤ).natAbs : ℝ) := by
  have h1' : (0:ℝ) < (r1:ℝ) := by exact_mod_cast h1
  have h2' : (0:ℝ) < (r2:ℝ) := by exact_mod_cast h2
  have hx : Work.FIArea4.Vflip.xPair (r1,s1) (r2,s2)
      = ((s1:ℝ)*(r2:ℝ)-(s2:ℝ)*(r1:ℝ))/((r1:ℝ)*(r2:ℝ)) := by
    rw [Work.FIArea4.Vflip.xPair]; field_simp
  rw [hx, abs_div, abs_of_pos (by positivity : (0:ℝ)<(r1:ℝ)*(r2:ℝ))]
  rw [show |(s1:ℝ)*(r2:ℝ)-(s2:ℝ)*(r1:ℝ)| = |((r1:ℝ)*(s2:ℝ)-(r2:ℝ)*(s1:ℝ))| by
    rw [show ((r1:ℝ)*(s2:ℝ)-(r2:ℝ)*(s1:ℝ)) = -((s1:ℝ)*(r2:ℝ)-(s2:ℝ)*(r1:ℝ)) by ring, abs_neg]]
  rw [div_mul_eq_mul_div, mul_div_cancel_right₀ _ (by positivity : ((r1:ℝ)*(r2:ℝ)) ≠ 0)]
  rw [far_natAbs_cast_real]
  push_cast
  ring

/-- `|xPair p q| · (c · ρ₁ · ρ₂) = pairAbs p q` with `c = pairC`, `ρᵢ = pairR`. -/
lemma far_abs_xPair_mul (r1 s1 r2 s2 : ℕ) (h1 : 0 < r1) (h2 : 0 < r2) :
    |Work.FIArea4.Vflip.xPair (r1, s1) (r2, s2)|
        * ((Work.FIArea4.Vflip.pairC r1 r2 : ℝ) * (Work.FIArea4.Vflip.pairR r1 r2 : ℝ)
            * (Work.FIArea4.Vflip.pairR r2 r1 : ℝ))
      = (Work.FIArea4.Vflip.pairAbs r1 r2 s1 s2 : ℝ) := by
  have hr1 : (r1:ℝ) = (Work.FIArea4.Vflip.pairC r1 r2 : ℝ)
      * (Work.FIArea4.Vflip.pairR r1 r2 : ℝ) := by
    rw [← Nat.cast_mul, pairC_mul_pairR_left]
  have hr2 : (r2:ℝ) = (Work.FIArea4.Vflip.pairC r1 r2 : ℝ)
      * (Work.FIArea4.Vflip.pairR r2 r1 : ℝ) := by
    rw [← Nat.cast_mul, pairC_mul_pairR_right]
  have hpc : (0:ℝ) < (Work.FIArea4.Vflip.pairC r1 r2 : ℝ) := by
    exact_mod_cast far_pairC_pos (r2 := r2) h1
  have hnat_eq : (((r1:ℤ)*(s2:ℤ)-(r2:ℤ)*(s1:ℤ):ℤ).natAbs)
      = Work.FIArea4.Vflip.pairC r1 r2 * Work.FIArea4.Vflip.pairAbs r1 r2 s1 s2 :=
    (pairC_mul_pairAbs_eq r1 r2 s1 s2).symm
  have keyA : |Work.FIArea4.Vflip.xPair (r1, s1) (r2, s2)| * ((r1:ℝ)*(r2:ℝ))
      = (Work.FIArea4.Vflip.pairC r1 r2 : ℝ) * (Work.FIArea4.Vflip.pairAbs r1 r2 s1 s2 : ℝ) := by
    rw [far_abs_xPair_mul_nat r1 s1 r2 s2 h1 h2, hnat_eq]
    push_cast; ring
  have hrprod : (r1:ℝ)*(r2:ℝ) = (Work.FIArea4.Vflip.pairC r1 r2 : ℝ)
      * ((Work.FIArea4.Vflip.pairC r1 r2 : ℝ)
          * ((Work.FIArea4.Vflip.pairR r1 r2 : ℝ) * (Work.FIArea4.Vflip.pairR r2 r1 : ℝ))) := by
    rw [hr1, hr2]; ring
  rw [hrprod] at keyA
  have : (Work.FIArea4.Vflip.pairC r1 r2 : ℝ)
      * (|Work.FIArea4.Vflip.xPair (r1, s1) (r2, s2)|
          * ((Work.FIArea4.Vflip.pairC r1 r2 : ℝ) * (Work.FIArea4.Vflip.pairR r1 r2 : ℝ)
              * (Work.FIArea4.Vflip.pairR r2 r1 : ℝ))
          - (Work.FIArea4.Vflip.pairAbs r1 r2 s1 s2 : ℝ)) = 0 := by nlinarith [keyA]
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hpc.ne')

/-! ## The reduced coordinates of the `c`-group -/

/-- The reduced `r`-range parameter of the `c`-group: every reduced modulus `ρ = r/c` of a point
`r` of the box `(R, 2R]` satisfies `ρ ≤ 2R/c`. -/
def Rred (c R : ℕ) : ℕ := 2 * R / c

/-- The reduced coefficient array of the `c`-group: `redA c α ρ s = α (c*ρ) s`. -/
def redA (c : ℕ) (α : ℕ → ℕ → ℂ) : ℕ → ℕ → ℂ := fun ρ s => α (c * ρ) s

@[simp] lemma redA_apply (c : ℕ) (α : ℕ → ℕ → ℂ) (ρ s : ℕ) : redA c α ρ s = α (c * ρ) s := rfl

/-! ## The index set of a `(m,c,Q)`-piece -/

/-- The index type: `((q',(ρ₁,s₁)),(ρ₂,s₂))`. -/
abbrev FarIx : Type := ((ℕ × (ℕ × ℕ)) × (ℕ × ℕ))

/-- The separation argument `y = c ρ₁ ρ₂ / (q' D)` attached to an index. -/
def ySep (c D : ℕ) (i : FarIx) : ℝ :=
  (c:ℝ) * (i.1.2.1 : ℝ) * (i.2.1 : ℝ) / ((i.1.1 : ℝ) * (D : ℝ))

/-- The reduced difference attached to an index: `x' = s₁/ρ₁ - s₂/ρ₂`. -/
def xRed (i : FarIx) : ℝ := (i.1.2.2 : ℝ) / (i.1.2.1 : ℝ) - (i.2.2 : ℝ) / (i.2.1 : ℝ)

/-- The original (unreduced) difference `xPair ((cρ₁,s₁),(cρ₂,s₂))` attached to an index. -/
def xOrig (c : ℕ) (i : FarIx) : ℝ :=
  Work.FIArea4.Vflip.xPair (c * i.1.2.1, i.1.2.2) (c * i.2.1, i.2.2)

/-- The cross difference `A = pairAbs (cρ₁) (cρ₂) s₁ s₂` attached to an index. -/
def iAbs (c : ℕ) (i : FarIx) : ℕ :=
  Work.FIArea4.Vflip.pairAbs (c * i.1.2.1) (c * i.2.1) i.1.2.2 i.2.2

/-- The conditions of the `(m,c,Q)`-piece: the box conditions on the reduced pair, the
coprimality `(ρ₁,ρ₂) = 1` of the reduced pair, and the divisor conditions `m ∣ c`, `m q' ∣ A` of
the flip. -/
def farCond (D R S : ℕ) (a b : ℝ) (m c : ℕ) (i : FarIx) : Prop :=
  0 < c ∧ Nat.Coprime i.1.2.1 i.2.1
    ∧ R < c * i.1.2.1 ∧ c * i.1.2.1 ≤ 2 * R
    ∧ R < c * i.2.1 ∧ c * i.2.1 ≤ 2 * R
    ∧ S < i.1.2.2 ∧ i.1.2.2 ≤ 2 * S
    ∧ S < i.2.2 ∧ i.2.2 ≤ 2 * S
    ∧ m ∣ c
    ∧ m * i.1.1 ∣ iAbs c i

/-- The Finset of indices of the `(m,c,Q₁,Q₂)`-piece: the interval `Q₁ < q' ≤ Q₂` of the flipped
modulus, the reduced pairs of the `c`-group, and all the conditions of `farCond`. -/
def farSet (D R S : ℕ) (a b : ℝ) (m c Q1 Q2 : ℕ) : Finset FarIx :=
  ((Finset.Ioc Q1 Q2 ×ˢ
      (Finset.range (2 * R + 1) ×ˢ Finset.range (2 * S + 1))) ×ˢ
        (Finset.range (2 * R + 1) ×ˢ Finset.range (2 * S + 1))).filter
    (fun i => i.1.1 ≤ Q2 ∧ farCond D R S a b m c i)

lemma mem_farSet {D R S m c Q1 Q2 : ℕ} {a b : ℝ} {i : FarIx} :
    i ∈ farSet D R S a b m c Q1 Q2 ↔
      Q1 < i.1.1 ∧ i.1.1 ≤ Q2 ∧ i.1.2.1 < 2 * R + 1 ∧ i.1.2.2 < 2 * S + 1
        ∧ i.2.1 < 2 * R + 1 ∧ i.2.2 < 2 * S + 1 ∧ i.1.1 ≤ Q2
        ∧ farCond D R S a b m c i := by
  simp only [farSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Ioc, Finset.mem_range]
  tauto

lemma farCond_of_mem_farSet {D R S m c Q1 Q2 : ℕ} {a b : ℝ} {i : FarIx}
    (h : i ∈ farSet D R S a b m c Q1 Q2) : farCond D R S a b m c i :=
  (mem_farSet.mp h).2.2.2.2.2.2.2

/-! ## The summand -/

/-- The coefficient of an index: everything in the flipped summand except the smooth weights
`bump` and `nearCut`, i.e.
`μ(m) · (s₁|ρ₁)(s₂|ρ₂) · α (cρ₁) s₁ · conj (α (cρ₂) s₂) · (ρ₁|q')(ρ₂|q')`. -/
def farCoef (m c : ℕ) (α : ℕ → ℕ → ℂ) (i : FarIx) : ℂ :=
  (ArithmeticFunction.moebius m : ℂ) *
    ((jacobiSym (i.1.2.2 : ℤ) i.1.2.1 * jacobiSym (i.2.2 : ℤ) i.2.1 : ℤ) : ℂ) *
    (α (c * i.1.2.1) i.1.2.2 * star (α (c * i.2.1) i.2.2)) *
    ((jacobiSym (i.1.2.1 : ℤ) (Work.FIPlan.oddPart i.1.1) *
      jacobiSym (i.2.1 : ℤ) (Work.FIPlan.oddPart i.1.1) : ℤ) : ℂ)

/-- The smooth weight of an index: `bump (|x| y) · nearCut a b x` with the separation arguments
`x = xOrig c i`, `y = ySep c D i`. -/
def farWeight (D : ℕ) (a b : ℝ) (c : ℕ) (i : FarIx) : ℂ :=
  ((((Work.FIArea4.Vflip.bump (|xOrig c i| * ySep c D i))
      * Work.FIArea4.Vflip.nearCut a b (xOrig c i) : ℝ)) : ℂ)

/-- The `(m,c,Q)`-piece of the far sum. -/
def farInner (D R S : ℕ) (a b : ℝ) (α : ℕ → ℕ → ℂ) (m c Q1 Q2 : ℕ) : ℂ :=
  ∑ i ∈ farSet D R S a b m c Q1 Q2, farCoef m c α i * farWeight D a b c i

/-- The exponential sum of the `(m,c,Q)`-piece, in the shape of the hypothesis of the separation
inequality: `Σ_i c_i · e(u x_i) · y_i^{it}`. -/
def farExpSum (D R S : ℕ) (a b : ℝ) (α : ℕ → ℕ → ℂ) (m c Q1 Q2 : ℕ) (u t : ℝ) : ℂ :=
  ∑ i ∈ farSet D R S a b m c Q1 Q2,
    farCoef m c α i * Complex.exp (2 * Real.pi * Complex.I * (u * xOrig c i)) *
      (((ySep c D i : ℝ) : ℂ) ^ (Complex.I * (t : ℂ)))

/-! ## Elementary properties -/

lemma ySep_pos {c D : ℕ} (hc : 0 < c) (hD : 0 < D) (i : FarIx)
    (h1 : 0 < i.1.2.1) (h2 : 0 < i.2.1) (hq : 0 < i.1.1) : 0 < ySep c D i := by
  unfold ySep
  have hc' : (0:ℝ) < (c:ℝ) := by exact_mod_cast hc
  have hD' : (0:ℝ) < (D:ℝ) := by exact_mod_cast hD
  have h1' : (0:ℝ) < (i.1.2.1 : ℝ) := by exact_mod_cast h1
  have h2' : (0:ℝ) < (i.2.1 : ℝ) := by exact_mod_cast h2
  have hq' : (0:ℝ) < (i.1.1 : ℝ) := by exact_mod_cast hq
  positivity

lemma farCond_pos {D R S : ℕ} {a b : ℝ} {m c : ℕ} {i : FarIx}
    (hi : farCond D R S a b m c i) :
    0 < c ∧ 0 < i.1.2.1 ∧ 0 < i.2.1 := by
  obtain ⟨hc, hcop, ha1, ha2, hb1, hb2, -, -, -, -, -, -⟩ := hi
  refine ⟨hc, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos i.1.2.1 with h | h
    · rw [h, mul_zero] at ha1; omega
    · exact h
  · rcases Nat.eq_zero_or_pos i.2.1 with h | h
    · rw [h, mul_zero] at hb1; omega
    · exact h

/-- **The key identity of the separation for the flipped summand**: with the separation arguments
`x = xPair (cρ₁,s₁) (cρ₂,s₂)`, `y = cρ₁ρ₂/(q'D)` one has `|x| y = A/(q'D)`, `A = iAbs c i`. -/
lemma abs_xOrig_mul_ySep {c D : ℕ} (hc : 0 < c) (hD : 0 < D) (i : FarIx)
    (hcop : Nat.Coprime i.1.2.1 i.2.1)
    (h1 : 0 < i.1.2.1) (h2 : 0 < i.2.1) (hq : 0 < i.1.1) :
    |xOrig c i| * ySep c D i = (iAbs c i : ℝ) / ((i.1.1 : ℝ) * (D : ℝ)) := by
  have hcr1 : 0 < c * i.1.2.1 := Nat.mul_pos hc h1
  have hcr2 : 0 < c * i.2.1 := Nat.mul_pos hc h2
  have hC : Work.FIArea4.Vflip.pairC (c * i.1.2.1) (c * i.2.1) = c := by
    simp only [Work.FIArea4.Vflip.pairC, Nat.gcd_mul_left, hcop.gcd_eq_one, mul_one]
  have hR1 : Work.FIArea4.Vflip.pairR (c * i.1.2.1) (c * i.2.1) = i.1.2.1 := by
    rw [Work.FIArea4.Vflip.pairR, hC]
    exact Nat.mul_div_cancel_left _ hc
  have hC' : Work.FIArea4.Vflip.pairC (c * i.2.1) (c * i.1.2.1) = c := by
    rw [Work.FIArea4.Vflip.pairC, Nat.gcd_comm]; exact hC
  have hR2 : Work.FIArea4.Vflip.pairR (c * i.2.1) (c * i.1.2.1) = i.2.1 := by
    rw [Work.FIArea4.Vflip.pairR, hC']
    exact Nat.mul_div_cancel_left _ hc
  have hkey := far_abs_xPair_mul (c * i.1.2.1) i.1.2.2 (c * i.2.1) i.2.2 hcr1 hcr2
  rw [hC, hR1, hR2] at hkey
  have hprod : |xOrig c i| * ((c:ℝ) * (i.1.2.1 : ℝ) * (i.2.1 : ℝ)) = (iAbs c i : ℝ) := by
    simpa only [xOrig, iAbs, Nat.cast_mul] using hkey
  rw [ySep]
  rw [show |xOrig c i|
        * ((c:ℝ) * (i.1.2.1 : ℝ) * (i.2.1 : ℝ) / ((i.1.1 : ℝ) * (D : ℝ)))
      = (|xOrig c i| * ((c:ℝ) * (i.1.2.1 : ℝ) * (i.2.1 : ℝ))) / ((i.1.1 : ℝ) * (D : ℝ))
      by ring]
  rw [hprod]

end

end Work.FIArea4.Vflip.Vfd
