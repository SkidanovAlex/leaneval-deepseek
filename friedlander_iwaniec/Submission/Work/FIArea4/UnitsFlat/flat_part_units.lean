import Mathlib
import Submission.Work.FIArea4.box_defs
import Submission.Work.FIArea4.flat_defs
import Submission.Work.FIArea4.Vflip.count_coset_box
import Submission.Work.FIArea4.Vflip.card_sq_filter_le
import Submission.Work.FIArea4.flat_aux

/-!
# The flat (`♭`) part of the dyadic dual variance, assembled

This module combines the per-pair (per flat pair `d₁,d₂`) AM–GM estimate — taken here as the
hypothesis `BlockBound` — with

* the flat-pair counting bound `card_sq_filter_le` (at most `√(2D)` flat partners),
* the two-way coset count `count_coset_box`,
* the elementary arithmetic `flat_arith` (FI (11.20)'s constants),

to produce the FI (11.20)/(11.21) flat-part estimate

`‖∑_{♭ pairs} ∑_{a<[d₁,d₂]} γ_{a%d₁,d₁} conj(γ_{a%d₂,d₂}) KK(a)‖
   ≤ C (D^{-1/2} R S + D √(RS)) ‖γ‖²`.

The unfinished analytical input (`BlockBound`) is exactly the statement of
`Work.FIArea4.UnitsFlat.flat_block_units`.
-/

namespace Work.FIArea4.UnitsFlat

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The per-flat-pair AM–GM estimate (the `♭`-block bound): the Poisson-expanded block
`∑_{a<[d₁,d₂]} γ_{a%d₁,d₁} conj(γ_{a%d₂,d₂}) KK F R d₁ d₂ a` for a flat pair `(d₁,d₂)` is bounded by
the average of the two one-dimensional quantities
`W d = ∑_{a<d} ‖γ a d‖² · #{r ∈ (R,2R], s ∈ suppBox S : s ≡ r a (mod d)}`. -/
def BlockBound : Prop := ∀ (S : ℕ) (hS : 1 ≤ S) (f : ℝ → ℝ) (F : ℝ → ℂ) (C₀ : ℝ)
    (hM : Work.FIArea4.BumpData S f F C₀) (R : ℕ) (γ : ℕ → ℕ → ℂ) (d1 d2 : ℕ)
    (hd1 : 1 ≤ d1) (hd2 : 1 ≤ d2) (hflat : Work.FIArea4.flatPair d1 d2),
    ‖∑ a ∈ Finset.range (Nat.lcm d1 d2), γ (a % d1) d1 * (starRingEnd ℂ) (γ (a % d2) d2)
        * Work.FIArea4.KK F R d1 d2 a‖
      ≤ (1 / 2) * (∑ a ∈ Finset.range d1, ‖γ a d1‖ ^ 2 *
            ((Work.FIArea4.suppCount S R d1 a : ℕ) : ℝ))
        + (1 / 2) * (∑ a ∈ Finset.range d2, ‖γ a d2‖ ^ 2 *
            ((Work.FIArea4.suppCount S R d2 a : ℕ) : ℝ))

/-- **The flat-pair sum.**  Summing the symmetrised block bound over the flat pairs gives at most
`√(2D)` times the unrestricted sum: the `♭`-condition is symmetric and each modulus has at most
`√(2D)` flat partners. -/
lemma flat_pair_sum_half (D : ℕ) (hD : 1 ≤ D) (E : ℕ → ℝ) (hE : ∀ d, 0 ≤ E d) :
    ∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ (Finset.Ioc D (2*D)).filter (fun d2 =>
        Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2)^2
          = Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
      (1/2)*(E d1 + E d2)
    ≤ Real.sqrt (2*D) * ∑ d ∈ Finset.Ioc D (2*D), E d := by
  set s : Finset ℕ := Finset.Ioc D (2*D) with hs
  set Q : ℕ → ℕ → Prop := fun d1 d2 =>
    Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2)^2
      = Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2 with hQ
  have hcard : ∀ d ∈ s, (((s.filter (Q d)).card : ℕ) : ℝ) ≤ Real.sqrt (2*D) := by
    intro d hd
    have hd1 : 1 ≤ d := by
      have := (Finset.mem_Ioc.mp (hs ▸ hd)).1
      omega
    have h := Work.FIArea4.Vflip.card_sq_filter_le D d hD hd1
    simpa [hs, hQ] using h
  have hsym : ∀ d1 d2, Q d1 d2 ↔ Q d2 d1 := by
    intro d1 d2
    simp only [hQ]
    rw [mul_comm (Work.FIPlan.oddPart d1) (Work.FIPlan.oddPart d2)]
  have hA : (∑ d1 ∈ s, ∑ d2 ∈ s.filter (Q d1), E d1) ≤ Real.sqrt (2*D) * ∑ d1 ∈ s, E d1 := by
    calc (∑ d1 ∈ s, ∑ d2 ∈ s.filter (Q d1), E d1)
        = ∑ d1 ∈ s, (((s.filter (Q d1)).card : ℕ) : ℝ) * E d1 := by
          apply Finset.sum_congr rfl
          intro d1 _
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ d1 ∈ s, Real.sqrt (2*D) * E d1 := by
          apply Finset.sum_le_sum
          intro d1 hd1
          exact mul_le_mul_of_nonneg_right (hcard d1 hd1) (hE d1)
      _ = Real.sqrt (2*D) * ∑ d1 ∈ s, E d1 := by rw [Finset.mul_sum]
  have hB : (∑ d1 ∈ s, ∑ d2 ∈ s.filter (Q d1), E d2) ≤ Real.sqrt (2*D) * ∑ d2 ∈ s, E d2 := by
    have hre : (∑ d1 ∈ s, ∑ d2 ∈ s.filter (Q d1), E d2)
        = ∑ d2 ∈ s, (((s.filter (fun d1 => Q d1 d2)).card : ℕ) : ℝ) * E d2 := by
      rw [show (∑ d1 ∈ s, ∑ d2 ∈ s.filter (Q d1), E d2)
          = ∑ d1 ∈ s, ∑ d2 ∈ s, (if Q d1 d2 then E d2 else 0) from by
            apply Finset.sum_congr rfl
            intro d1 _
            rw [Finset.sum_filter]]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d2 _
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    rw [hre]
    calc (∑ d2 ∈ s, (((s.filter (fun d1 => Q d1 d2)).card : ℕ) : ℝ) * E d2)
        ≤ ∑ d2 ∈ s, Real.sqrt (2*D) * E d2 := by
          apply Finset.sum_le_sum
          intro d2 hd2
          have hcf : s.filter (fun d1 => Q d1 d2) = s.filter (Q d2) := by
            apply Finset.filter_congr
            intro x _
            exact hsym x d2
          rw [hcf]
          exact mul_le_mul_of_nonneg_right (hcard d2 hd2) (hE d2)
      _ = Real.sqrt (2*D) * ∑ d2 ∈ s, E d2 := by rw [Finset.mul_sum]
  have h2 : 2 * (∑ d1 ∈ s, ∑ d2 ∈ s.filter (Q d1), (1/2)*(E d1 + E d2))
      = (∑ d1 ∈ s, ∑ d2 ∈ s.filter (Q d1), E d1)
        + (∑ d1 ∈ s, ∑ d2 ∈ s.filter (Q d1), E d2) := by
    rw [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d1 _
    rw [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d2 _
    ring
  calc (∑ d1 ∈ s, ∑ d2 ∈ s.filter (Q d1), (1/2)*(E d1 + E d2))
      = (1/2) * (2 * (∑ d1 ∈ s, ∑ d2 ∈ s.filter (Q d1), (1/2)*(E d1 + E d2))) := by ring
    _ = (1/2) * ((∑ d1 ∈ s, ∑ d2 ∈ s.filter (Q d1), E d1)
          + (∑ d1 ∈ s, ∑ d2 ∈ s.filter (Q d1), E d2)) := by rw [h2]
    _ ≤ (1/2) * (Real.sqrt (2*D) * ∑ d1 ∈ s, E d1 + Real.sqrt (2*D) * ∑ d2 ∈ s, E d2) := by
        linarith [hA, hB]
    _ = Real.sqrt (2*D) * ∑ d ∈ s, E d := by ring

/-- The `suppBox`-coset count: `suppCount S R d a ≤ 10 (R(2S+2)/d + min R (2S+2) + 1)`, obtained
from the shifted-box count `count_coset_box` (the `suppBox` is contained in
`Ioc (S/2-1) (S/2-1 + (2S+2))`). -/
lemma suppCount_cast_le (S R d a : ℕ) (hS : 1 ≤ S) (hR : 1 ≤ R) (hd : 1 ≤ d) :
    ((Work.FIArea4.suppCount S R d a : ℕ) : ℝ)
      ≤ 10 * (((R : ℝ) * (2 * (S : ℝ) + 2)) / (d : ℝ)
          + ((min R (2 * S + 2) : ℕ) : ℝ) + 1) := by
  have hbox : Work.FIArea4.suppBox S
      ⊆ Finset.Ioc (S / 2 - 1) (S / 2 - 1 + (2 * S + 2)) := by
    intro x hx
    rw [Work.FIArea4.suppBox, Finset.mem_Ioc] at hx
    rw [Finset.mem_Ioc]
    refine ⟨hx.1, ?_⟩
    have h5 : 5 * S / 2 = S / 2 + 2 * S := by
      have h : 5 * S = S + 2 * (2 * S) := by ring
      rw [h, Nat.add_mul_div_left S (2 * S) (by norm_num : 0 < 2)]
    omega
  have hsub : (((Finset.Ioc R (2 * R)).product (Work.FIArea4.suppBox S)).filter
        (fun p : ℕ × ℕ => p.2 % d = (p.1 * a) % d))
      ⊆ (((Finset.Ioc R (2 * R)).product
          (Finset.Ioc (S / 2 - 1) (S / 2 - 1 + (2 * S + 2)))).filter
        (fun p : ℕ × ℕ => p.2 % d = (p.1 * a) % d)) := by
    intro p hp
    have h1 : p ∈ (Finset.Ioc R (2 * R)).product (Work.FIArea4.suppBox S) :=
      (Finset.mem_filter.mp hp).1
    have h2 : p.2 % d = (p.1 * a) % d := (Finset.mem_filter.mp hp).2
    rw [Finset.mem_filter]
    refine ⟨?_, h2⟩
    rw [Finset.product_eq_sprod] at h1 ⊢
    exact Finset.mem_product.mpr
      ⟨(Finset.mem_product.mp h1).1, hbox (Finset.mem_product.mp h1).2⟩
  rw [Work.FIArea4.suppCount]
  have hcnt := Work.FIArea4.Vflip.count_coset_box (S / 2 - 1) (2 * S + 2) R d a hR
    (by omega) hd (by omega)
  have hcast : (((((Finset.Ioc R (2 * R)).product
        (Finset.Ioc (S / 2 - 1) (S / 2 - 1 + (2 * S + 2)))).filter
        (fun p : ℕ × ℕ => p.2 % d = (p.1 * a) % d)).card : ℕ) : ℝ)
      ≤ ((10 * (R * (2 * S + 2) / d + min R (2 * S + 2) + 1) : ℕ) : ℝ) := by
    exact_mod_cast hcnt
  have hdiv : ((R * (2 * S + 2) / d : ℕ) : ℝ)
      ≤ (R : ℝ) * (2 * (S : ℝ) + 2) / (d : ℝ) := by
    have h := Nat.cast_div_le (α := ℝ) (m := R * (2 * S + 2)) (n := d)
    push_cast at h
    exact h
  calc (((((Finset.Ioc R (2 * R)).product (Work.FIArea4.suppBox S)).filter
        (fun p : ℕ × ℕ => p.2 % d = (p.1 * a) % d)).card : ℕ) : ℝ)
      ≤ (((((Finset.Ioc R (2 * R)).product
          (Finset.Ioc (S / 2 - 1) (S / 2 - 1 + (2 * S + 2)))).filter
          (fun p : ℕ × ℕ => p.2 % d = (p.1 * a) % d)).card : ℕ) : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ((10 * (R * (2 * S + 2) / d + min R (2 * S + 2) + 1) : ℕ) : ℝ) := hcast
    _ = 10 * (((R * (2 * S + 2) / d : ℕ) : ℝ) + ((min R (2 * S + 2) : ℕ) : ℝ) + 1) := by
        push_cast; ring
    _ ≤ 10 * (((R : ℝ) * (2 * (S : ℝ) + 2)) / (d : ℝ)
          + ((min R (2 * S + 2) : ℕ) : ℝ) + 1) := by linarith [hdiv]

/-- The comparison of the counted bracket with `60 (RS/D + min R S + 1)`. -/
lemma count_bracket_le (D R S : ℕ) (hD : 1 ≤ D) (hR : 1 ≤ R) (hS : 1 ≤ S) :
    10 * (((R : ℝ) * (2 * (S : ℝ) + 2)) / (D : ℝ)
        + ((min R (2 * S + 2) : ℕ) : ℝ) + 1)
      ≤ 60 * (((R : ℝ) * (S : ℝ)) / (D : ℝ) + ((min R S : ℕ) : ℝ) + 1) := by
  have hD0 : (0 : ℝ) < (D : ℝ) := by
    have : 0 < D := by omega
    exact_mod_cast this
  have hS1 : (1 : ℝ) ≤ (S : ℝ) := by exact_mod_cast hS
  have hR0 : (0 : ℝ) ≤ (R : ℝ) := Nat.cast_nonneg R
  have h1 : ((R : ℝ) * (2 * (S : ℝ) + 2)) / (D : ℝ)
      ≤ 6 * (((R : ℝ) * (S : ℝ)) / (D : ℝ)) := by
    have h2S : (2 * (S : ℝ) + 2) ≤ 6 * (S : ℝ) := by linarith
    calc ((R : ℝ) * (2 * (S : ℝ) + 2)) / (D : ℝ)
        ≤ ((R : ℝ) * (6 * (S : ℝ))) / (D : ℝ) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h2S hR0) hD0.le
      _ = 6 * (((R : ℝ) * (S : ℝ)) / (D : ℝ)) := by ring
  have h2 : ((min R (2 * S + 2) : ℕ) : ℝ) ≤ 4 * ((min R S : ℕ) : ℝ) + 1 := by
    rcases le_total R S with h | h
    · have hmin1 : min R (2 * S + 2) = R := Nat.min_eq_left (by omega)
      have hmin2 : min R S = R := Nat.min_eq_left h
      rw [hmin1, hmin2]
      have : (0 : ℝ) ≤ (R : ℝ) := Nat.cast_nonneg R
      linarith
    · have hmin2 : min R S = S := Nat.min_eq_right h
      rw [hmin2]
      have hle : ((min R (2 * S + 2) : ℕ) : ℝ) ≤ 2 * (S : ℝ) + 2 := by
        have : min R (2 * S + 2) ≤ 2 * S + 2 := Nat.min_le_right _ _
        exact_mod_cast this
      linarith
  linarith

/-- The elementary arithmetic of FI (11.20) in the form used here. -/
lemma flat_arith_units (D R S : ℕ) (hD : 1 ≤ D) (hR : 1 ≤ R) (hS : 1 ≤ S) :
    10 * Real.sqrt (2 * (D : ℝ)) * (((R : ℝ) * (2 * (S : ℝ) + 2)) / (D : ℝ)
        + ((min R (2 * S + 2) : ℕ) : ℝ) + 1)
      ≤ 300 * (((D : ℝ) ^ (-(1 : ℝ) / 2) * (R : ℝ) * (S : ℝ))
          + (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ))) := by
  have hx : (0 : ℝ) ≤ Real.sqrt (2 * (D : ℝ)) := Real.sqrt_nonneg _
  have hmain := count_bracket_le D R S hD hR hS
  have hflat := Work.FIArea4.flat_arith D R S hD hR hS
  have hstep : 10 * Real.sqrt (2 * (D : ℝ)) * (((R : ℝ) * (2 * (S : ℝ) + 2)) / (D : ℝ)
        + ((min R (2 * S + 2) : ℕ) : ℝ) + 1)
      ≤ 60 * Real.sqrt (2 * (D : ℝ)) * (((R : ℝ) * (S : ℝ)) / (D : ℝ)
          + ((min R S : ℕ) : ℝ) + 1) := by
    nlinarith [hmain, hx]
  linarith [hstep, hflat]

/-- **FI (11.20)—(11.21), the flat part**, with the per-pair estimate taken as a hypothesis. -/
theorem flat_part_units_of_block (hfb : BlockBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : ℕ) (hS : 1 ≤ S) (f : ℝ → ℝ) (F : ℝ → ℂ) (C₀ : ℝ)
      (hM : Work.FIArea4.BumpData S f F C₀) (D R : ℕ) (γ : ℕ → ℕ → ℂ), 1 ≤ D → 1 ≤ R →
      ‖∑ d1 ∈ Finset.Ioc D (2 * D),
         ∑ d2 ∈ (Finset.Ioc D (2 * D)).filter (fun d2 =>
             Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2
               = Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
          ∑ a ∈ Finset.range (Nat.lcm d1 d2),
            γ (a % d1) d1 * (starRingEnd ℂ) (γ (a % d2) d2) * Work.FIArea4.KK F R d1 d2 a‖
      ≤ C * (((D : ℝ) ^ (-(1 : ℝ) / 2) * (R : ℝ) * (S : ℝ))
              + (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ)))
          * (∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d, Complex.normSq (γ a d)) := by
  refine ⟨300, by norm_num, ?_⟩
  intro S hS f F C₀ hM D R γ hD hR
  set s : Finset ℕ := Finset.Ioc D (2 * D) with hs
  set Q : ℕ → ℕ → Prop := fun d1 d2 =>
    Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2
      = Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2 with hQ
  set W : ℕ → ℝ := fun d => ∑ a ∈ Finset.range d, ‖γ a d‖ ^ 2 *
    ((Work.FIArea4.suppCount S R d a : ℕ) : ℝ) with hW
  set E : ℝ := ∑ d ∈ s, ∑ a ∈ Finset.range d, Complex.normSq (γ a d) with hE
  have hWnn : ∀ d, 0 ≤ W d := by
    intro d
    rw [hW]
    exact Finset.sum_nonneg (fun a _ => mul_nonneg (by positivity) (Nat.cast_nonneg _))
  have hEnn : 0 ≤ E := by
    rw [hE]
    exact Finset.sum_nonneg (fun d _ => Finset.sum_nonneg (fun a _ => Complex.normSq_nonneg _))
  have hEeq : E = ∑ d ∈ s, ∑ a ∈ Finset.range d, ‖γ a d‖ ^ 2 := by
    rw [hE]
    apply Finset.sum_congr rfl
    intro d _
    apply Finset.sum_congr rfl
    intro a _
    rw [Complex.normSq_eq_norm_sq]
  have hd1_of : ∀ d1 ∈ s, 1 ≤ d1 := by
    intro d1 hd1
    have := (Finset.mem_Ioc.mp (hs ▸ hd1)).1
    omega
  have hstep1 : ‖∑ d1 ∈ s, ∑ d2 ∈ s.filter (Q d1), ∑ a ∈ Finset.range (Nat.lcm d1 d2),
        γ (a % d1) d1 * (starRingEnd ℂ) (γ (a % d2) d2) * Work.FIArea4.KK F R d1 d2 a‖
      ≤ ∑ d1 ∈ s, ∑ d2 ∈ s.filter (Q d1), (1/2) * (W d1 + W d2) := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun d1 hd1 => ?_))
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun d2 hd2 => ?_))
    have hd1' : 1 ≤ d1 := hd1_of d1 hd1
    have hd2' : 1 ≤ d2 := hd1_of d2 (Finset.mem_filter.mp hd2).1
    have hflat : Work.FIArea4.flatPair d1 d2 :=
      (Work.FIArea4.flatPair_iff_sqrt d1 d2).mpr (Finset.mem_filter.mp hd2).2
    have hblk := hfb S hS f F C₀ hM R γ d1 d2 hd1' hd2' hflat
    simpa only [hW, mul_add] using hblk
  have hstep3 : (∑ d ∈ s, W d) ≤ 60 * (((R : ℝ) * (S : ℝ)) / (D : ℝ)
      + ((min R S : ℕ) : ℝ) + 1) * E := by
    have hunit : ∀ d ∈ s, ∀ a ∈ Finset.range d,
        ((Work.FIArea4.suppCount S R d a : ℕ) : ℝ)
          ≤ 10 * (((R : ℝ) * (2 * (S : ℝ) + 2)) / (d : ℝ)
              + ((min R (2 * S + 2) : ℕ) : ℝ) + 1) := by
      intro d hd a _
      exact suppCount_cast_le S R d a hS hR (hd1_of d hd)
    have hdD : ∀ d ∈ s, (D : ℝ) ≤ (d : ℝ) := by
      intro d hd
      have hlt : D < d := (Finset.mem_Ioc.mp (hs ▸ hd)).1
      exact_mod_cast (le_of_lt hlt : D ≤ d)
    have hD0 : (0 : ℝ) < (D : ℝ) := by
      have : 0 < D := by omega
      exact_mod_cast this
    have hkey : ∀ d ∈ s, ∀ a ∈ Finset.range d,
        ‖γ a d‖ ^ 2 * ((Work.FIArea4.suppCount S R d a : ℕ) : ℝ)
          ≤ ‖γ a d‖ ^ 2 * (10 * (((R : ℝ) * (2 * (S : ℝ) + 2)) / (D : ℝ)
              + ((min R (2 * S + 2) : ℕ) : ℝ) + 1)) := by
      intro d hd a ha
      have h1 : ((R : ℝ) * (2 * (S : ℝ) + 2)) / (d : ℝ)
          ≤ ((R : ℝ) * (2 * (S : ℝ) + 2)) / (D : ℝ) :=
        div_le_div_of_nonneg_left (by positivity) hD0 (hdD d hd)
      have h2 := hunit d hd a ha
      have h3 : ((R : ℝ) * (2 * (S : ℝ) + 2)) / (d : ℝ)
            + ((min R (2 * S + 2) : ℕ) : ℝ) + 1
          ≤ ((R : ℝ) * (2 * (S : ℝ) + 2)) / (D : ℝ)
            + ((min R (2 * S + 2) : ℕ) : ℝ) + 1 := by linarith
      have hX : ((Work.FIArea4.suppCount S R d a : ℕ) : ℝ)
          ≤ 10 * (((R : ℝ) * (2 * (S : ℝ) + 2)) / (D : ℝ)
              + ((min R (2 * S + 2) : ℕ) : ℝ) + 1) :=
        le_trans h2 (mul_le_mul_of_nonneg_left h3 (by norm_num : (0 : ℝ) ≤ 10))
      exact mul_le_mul_of_nonneg_left hX (by positivity)
    have hsum1 : (∑ d ∈ s, W d)
        ≤ ∑ d ∈ s, ∑ a ∈ Finset.range d, ‖γ a d‖ ^ 2 * (10 * (((R : ℝ) * (2 * (S : ℝ) + 2))
              / (D : ℝ) + ((min R (2 * S + 2) : ℕ) : ℝ) + 1)) := by
      apply Finset.sum_le_sum
      intro d hd
      rw [hW]
      exact Finset.sum_le_sum (fun a ha => hkey d hd a ha)
    have hsum2 : (∑ d ∈ s, ∑ a ∈ Finset.range d, ‖γ a d‖ ^ 2 * (10 * (((R : ℝ) * (2 * (S : ℝ) + 2))
              / (D : ℝ) + ((min R (2 * S + 2) : ℕ) : ℝ) + 1)))
        = 10 * (((R : ℝ) * (2 * (S : ℝ) + 2)) / (D : ℝ)
              + ((min R (2 * S + 2) : ℕ) : ℝ) + 1) * (∑ d ∈ s, ∑ a ∈ Finset.range d, ‖γ a d‖ ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    have hsum3 : 10 * (((R : ℝ) * (2 * (S : ℝ) + 2)) / (D : ℝ)
          + ((min R (2 * S + 2) : ℕ) : ℝ) + 1) * (∑ d ∈ s, ∑ a ∈ Finset.range d, ‖γ a d‖ ^ 2)
        ≤ 60 * (((R : ℝ) * (S : ℝ)) / (D : ℝ) + ((min R S : ℕ) : ℝ) + 1) * E := by
      rw [hEeq]
      exact mul_le_mul_of_nonneg_right (count_bracket_le D R S hD hR hS)
        (Finset.sum_nonneg (fun d _ => Finset.sum_nonneg (fun a _ => by positivity)))
    calc (∑ d ∈ s, W d)
        ≤ ∑ d ∈ s, ∑ a ∈ Finset.range d, ‖γ a d‖ ^ 2
            * (10 * (((R : ℝ) * (2 * (S : ℝ) + 2)) / (D : ℝ)
              + ((min R (2 * S + 2) : ℕ) : ℝ) + 1)) := hsum1
      _ = 10 * (((R : ℝ) * (2 * (S : ℝ) + 2)) / (D : ℝ)
            + ((min R (2 * S + 2) : ℕ) : ℝ) + 1)
          * (∑ d ∈ s, ∑ a ∈ Finset.range d, ‖γ a d‖ ^ 2) := hsum2
      _ ≤ 60 * (((R : ℝ) * (S : ℝ)) / (D : ℝ) + ((min R S : ℕ) : ℝ) + 1) * E := hsum3
  have hstep2 := flat_pair_sum_half D hD W hWnn
  rw [← hs] at hstep2
  have hfinal : Real.sqrt (2 * (D : ℝ)) * (60 * (((R : ℝ) * (S : ℝ)) / (D : ℝ)
      + ((min R S : ℕ) : ℝ) + 1) * E)
      ≤ 300 * (((D : ℝ) ^ (-(1 : ℝ) / 2) * (R : ℝ) * (S : ℝ))
          + (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ))) * E := by
    have hA : 60 * Real.sqrt (2 * (D : ℝ)) * (((R : ℝ) * (S : ℝ)) / (D : ℝ)
        + ((min R S : ℕ) : ℝ) + 1)
        ≤ 300 * (((D : ℝ) ^ (-(1 : ℝ) / 2) * (R : ℝ) * (S : ℝ))
            + (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ))) := by
      have hflat := Work.FIArea4.flat_arith D R S hD hR hS
      linarith [hflat]
    calc Real.sqrt (2 * (D : ℝ)) * (60 * (((R : ℝ) * (S : ℝ)) / (D : ℝ)
            + ((min R S : ℕ) : ℝ) + 1) * E)
        = 60 * Real.sqrt (2 * (D : ℝ)) * (((R : ℝ) * (S : ℝ)) / (D : ℝ)
            + ((min R S : ℕ) : ℝ) + 1) * E := by ring
      _ ≤ 300 * (((D : ℝ) ^ (-(1 : ℝ) / 2) * (R : ℝ) * (S : ℝ))
            + (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ))) * E :=
          mul_le_mul_of_nonneg_right hA hEnn
  calc ‖∑ d1 ∈ s, ∑ d2 ∈ s.filter (Q d1), ∑ a ∈ Finset.range (Nat.lcm d1 d2),
        γ (a % d1) d1 * (starRingEnd ℂ) (γ (a % d2) d2) * Work.FIArea4.KK F R d1 d2 a‖
      ≤ ∑ d1 ∈ s, ∑ d2 ∈ s.filter (Q d1), (1/2) * (W d1 + W d2) := hstep1
    _ ≤ Real.sqrt (2 * (D : ℝ)) * (∑ d ∈ s, W d) := hstep2
    _ ≤ Real.sqrt (2 * (D : ℝ)) * (60 * (((R : ℝ) * (S : ℝ)) / (D : ℝ)
          + ((min R S : ℕ) : ℝ) + 1) * E) :=
        mul_le_mul_of_nonneg_left hstep3 (Real.sqrt_nonneg _)
    _ ≤ 300 * (((D : ℝ) ^ (-(1 : ℝ) / 2) * (R : ℝ) * (S : ℝ))
          + (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ))) * E := hfinal

end

end Work.FIArea4.UnitsFlat
