import Mathlib
import Submission.Commons.NumberTheory.DivisorBound.card_divisors_le_rpow
import Submission.Work.FIArea2.sum_weight_sqcong
import Submission.Work.FIArea2.Count.summable_int_rpow_majorant
import Submission.Work.FIArea2.Count.summable_Wt_tau4
import Submission.Work.FIArea2.Count.dyadic_weight_pointwise
import Submission.Work.FIArea2.Count.dyadic_log_series_bound
set_option maxHeartbeats 1600000

namespace Work.FIArea2.R6

open Work.FIArea2.Count

open Finset
open scoped BigOperators

noncomputable section

private abbrev tau4 (n : ℤ) : ℝ := (((n.natAbs.divisors.card : ℝ)) ^ 4)

private def Fsum (R : ℕ) (p : ℤ × ℤ) : ℝ :=
  ∑ u1 ∈ Finset.Icc (-(R : ℤ)) (R : ℤ), ∑ u2 ∈ Finset.Icc (-(R : ℤ)) (R : ℤ),
    (Nat.gcd u1.natAbs u2.natAbs : ℝ) * tau4 (u1 * p.1 ^ 2 - u2 * p.2 ^ 2)

private def boxX (H : ℝ) (j : ℕ) : ℕ := ⌈(2 : ℝ) ^ j * H⌉₊

private def boxSum (R X Y : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc (-(X : ℤ)) (X : ℤ)) ×ˢ (Finset.Icc (-(Y : ℤ)) (Y : ℤ)), Fsum R p

private def Ft (H : ℝ) (u p : ℤ × ℤ) : ℝ :=
  (Nat.gcd u.1.natAbs u.2.natAbs : ℝ)
    * ((1 + (p.1 : ℝ) ^ 2 / H ^ 2)⁻¹ * (1 + (p.2 : ℝ) ^ 2 / H ^ 2)⁻¹
        * tau4 (u.1 * p.1 ^ 2 - u.2 * p.2 ^ 2))

private lemma Fsum_nonneg (R : ℕ) (p : ℤ × ℤ) : 0 ≤ Fsum R p := by
  unfold Fsum
  refine Finset.sum_nonneg (fun u1 _ => Finset.sum_nonneg (fun u2 _ => ?_))
  exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) 4)

private lemma boxSum_nonneg (R X Y : ℕ) : 0 ≤ boxSum R X Y := by
  unfold boxSum
  exact Finset.sum_nonneg (fun p _ => Fsum_nonneg R p)

private lemma boxX_ge (H : ℝ) (j : ℕ) : (2:ℝ)^j * H ≤ (boxX H j : ℝ) :=
  Nat.le_ceil _

private lemma boxX_le (H : ℝ) (hH : 0 ≤ H) (j : ℕ) : (boxX H j : ℝ) ≤ (2:ℝ)^j * (H + 1) := by
  have h0 : (0:ℝ) ≤ (2:ℝ)^j * H := mul_nonneg (by positivity) hH
  have h1 : (boxX H j : ℝ) < (2:ℝ)^j * H + 1 := Nat.ceil_lt_add_one h0
  have h2 : (1:ℝ) ≤ (2:ℝ)^j := one_le_pow₀ (by norm_num)
  nlinarith

private lemma boxX_one (H : ℝ) (hH : 1 ≤ H) (j : ℕ) : 1 ≤ boxX H j := by
  have h2 : (1:ℝ) ≤ (boxX H j : ℝ) := by
    have h1 := boxX_ge H j
    have h3 : (1:ℝ) ≤ (2:ℝ)^j * H := by
      have : (1:ℝ) ≤ (2:ℝ)^j := one_le_pow₀ (by norm_num)
      nlinarith
    linarith
  exact_mod_cast h2

private lemma sum_swap_four {M : Type*} [AddCommMonoid M] {α β γ δ : Type*}
    (s : Finset α) (t : Finset β) (u : Finset γ) (v : Finset δ) (g : α → β → γ → δ → M) :
    (∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, ∑ d ∈ v, g a b c d)
      = ∑ c ∈ u, ∑ d ∈ v, ∑ a ∈ s, ∑ b ∈ t, g a b c d := by
  calc (∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, ∑ d ∈ v, g a b c d)
      = ∑ a ∈ s, ∑ c ∈ u, ∑ b ∈ t, ∑ d ∈ v, g a b c d := by
          refine Finset.sum_congr rfl (fun a _ => ?_)
          rw [Finset.sum_comm]
    _ = ∑ c ∈ u, ∑ a ∈ s, ∑ b ∈ t, ∑ d ∈ v, g a b c d := by
          rw [Finset.sum_comm]
    _ = ∑ c ∈ u, ∑ d ∈ v, ∑ a ∈ s, ∑ b ∈ t, g a b c d := by
          refine Finset.sum_congr rfl (fun c _ => ?_)
          calc (∑ a ∈ s, ∑ b ∈ t, ∑ d ∈ v, g a b c d)
              = ∑ a ∈ s, ∑ d ∈ v, ∑ b ∈ t, g a b c d := by
                  refine Finset.sum_congr rfl (fun a _ => ?_)
                  rw [Finset.sum_comm]
            _ = ∑ d ∈ v, ∑ a ∈ s, ∑ b ∈ t, g a b c d := by rw [Finset.sum_comm]

private lemma summable_w_tau4 (H : ℝ) (hH : 1 ≤ H) (u1 u2 : ℤ) :
    Summable (fun p : ℤ × ℤ =>
      (1 + (p.1 : ℝ) ^ 2 / H ^ 2)⁻¹ * (1 + (p.2 : ℝ) ^ 2 / H ^ 2)⁻¹
        * tau4 (u1 * p.1 ^ 2 - u2 * p.2 ^ 2)) := by
  obtain ⟨Cd, hCdpos, hCd⟩ :=
    Commons.NumberTheory.DivisorBound.card_divisors_le_rpow ((1:ℝ)/16) (by norm_num)
  have hH0 : (0:ℝ) < H := lt_of_lt_of_le zero_lt_one hH
  let K : ℝ := (1 + H^2)^2
  have hb : Summable (fun t : ℤ => (1 + (t:ℝ)^2)⁻¹) :=
    (Work.FIArea2.summable_Wt 1 le_rfl).congr (fun t => by simp [Work.FIArea2.Wt])
  have hw : Summable (fun t : ℤ => |(t:ℝ)|^((1:ℝ)/2) * (1 + (t:ℝ)^2)⁻¹) :=
    summable_abs_sqrt_mul_one_add_sq_inv
  have hbnn : ∀ t : ℤ, 0 ≤ (1 + (t:ℝ)^2)⁻¹ := fun t => by positivity
  have hwnn : ∀ t : ℤ, 0 ≤ |(t:ℝ)|^((1:ℝ)/2) * (1 + (t:ℝ)^2)⁻¹ := fun t => by positivity
  have hwb : Summable (fun p : ℤ × ℤ =>
      |(p.1:ℝ)|^((1:ℝ)/2) * (1 + (p.1:ℝ)^2)⁻¹ * (1 + (p.2:ℝ)^2)⁻¹) :=
    Summable.mul_of_nonneg hw hb hwnn hbnn
  have hbw : Summable (fun p : ℤ × ℤ =>
      (1 + (p.1:ℝ)^2)⁻¹ * (|(p.2:ℝ)|^((1:ℝ)/2) * (1 + (p.2:ℝ)^2)⁻¹)) :=
    Summable.mul_of_nonneg hb hw hbnn hwnn
  let G : ℤ × ℤ → ℝ := fun p => K * Cd^4 *
      ( |(u1:ℝ)|^((1:ℝ)/4) * (|(p.1:ℝ)|^((1:ℝ)/2) * (1 + (p.1:ℝ)^2)⁻¹ * (1 + (p.2:ℝ)^2)⁻¹)
      + |(u2:ℝ)|^((1:ℝ)/4) * ((1 + (p.1:ℝ)^2)⁻¹ * (|(p.2:ℝ)|^((1:ℝ)/2) * (1 + (p.2:ℝ)^2)⁻¹)) )
  have hG : Summable G :=
    ((hwb.mul_left (|(u1:ℝ)|^((1:ℝ)/4))).add (hbw.mul_left (|(u2:ℝ)|^((1:ℝ)/4)))).mul_left (K * Cd^4)
  refine Summable.of_nonneg_of_le (f := G) ?_ ?_ hG
  · intro p
    exact mul_nonneg (mul_nonneg (by positivity) (by positivity)) (by positivity)
  · intro p
    have hA : (1 + (p.1:ℝ)^2/H^2)⁻¹ * (1 + (p.2:ℝ)^2/H^2)⁻¹
        ≤ K * ((1+(p.1:ℝ)^2)⁻¹ * (1+(p.2:ℝ)^2)⁻¹) := by
      have e1 := inv_one_add_div_sq_le H (p.1) hH0
      have e2 := inv_one_add_div_sq_le H (p.2) hH0
      have h1 : (0:ℝ) ≤ (1+(p.2:ℝ)^2/H^2)⁻¹ := by positivity
      have h2 : (0:ℝ) ≤ (1+H^2)*(1+(p.1:ℝ)^2)⁻¹ := by positivity
      calc (1+(p.1:ℝ)^2/H^2)⁻¹*(1+(p.2:ℝ)^2/H^2)⁻¹
          ≤ ((1+H^2)*(1+(p.1:ℝ)^2)⁻¹) * ((1+H^2)*(1+(p.2:ℝ)^2)⁻¹) := mul_le_mul e1 e2 h1 h2
        _ = K * ((1+(p.1:ℝ)^2)⁻¹ * (1+(p.2:ℝ)^2)⁻¹) := by simp only [K]; ring
    have hB := tau4_le Cd hCdpos hCd u1 u2 p.1 p.2
    have hAnn : 0 ≤ K * ((1+(p.1:ℝ)^2)⁻¹ * (1+(p.2:ℝ)^2)⁻¹) := by positivity
    have hBnn : 0 ≤ ((((u1*p.1^2 - u2*p.2^2).natAbs.divisors.card : ℝ))^4) := by positivity
    calc (1+(p.1:ℝ)^2/H^2)⁻¹*(1+(p.2:ℝ)^2/H^2)⁻¹ * tau4 (u1*p.1^2-u2*p.2^2)
        ≤ (K*((1+(p.1:ℝ)^2)⁻¹*(1+(p.2:ℝ)^2)⁻¹))
            * (Cd^4*(|(u1:ℝ)|^((1:ℝ)/4)*|(p.1:ℝ)|^((1:ℝ)/2) + |(u2:ℝ)|^((1:ℝ)/4)*|(p.2:ℝ)|^((1:ℝ)/2))) :=
          mul_le_mul hA hB hBnn hAnn
      _ = G p := by simp only [G]; ring

theorem hL_avg_fixedK_of_box
    (C0 : ℝ) (hC0 : 0 < C0) (K0 : ℕ)
    (hbox : ∀ (R : ℕ), 1 ≤ R → ∀ (X : ℕ), 1 ≤ X → ∀ (Y : ℕ), 1 ≤ Y →
      (∑ u1 ∈ Finset.Icc (-(R : ℤ)) (R : ℤ), ∑ u2 ∈ Finset.Icc (-(R : ℤ)) (R : ℤ),
        (Nat.gcd u1.natAbs u2.natAbs : ℝ) *
          (∑ h1 ∈ Finset.Icc (-(X : ℤ)) (X : ℤ), ∑ h2 ∈ Finset.Icc (-(Y : ℤ)) (Y : ℤ),
            (((u1 * h1 ^ 2 - u2 * h2 ^ 2).natAbs.divisors.card : ℝ) ^ 4)))
      ≤ C0 * (R : ℝ) ^ 2 * (X : ℝ) * (Y : ℝ)
          * (Real.log ((R : ℝ) + (X : ℝ) + (Y : ℝ) + 2)) ^ K0) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (H : ℝ), 1 ≤ H → ∀ (R : ℕ), 1 ≤ R →
      (∑ u1 ∈ Finset.Icc (-(R : ℤ)) (R : ℤ), ∑ u2 ∈ Finset.Icc (-(R : ℤ)) (R : ℤ),
        (Nat.gcd u1.natAbs u2.natAbs : ℝ) *
          (∑' h : ℤ × ℤ, (1 + (h.1 : ℝ) ^ 2 / H ^ 2)⁻¹ * (1 + (h.2 : ℝ) ^ 2 / H ^ 2)⁻¹
            * (((u1 * h.1 ^ 2 - u2 * h.2 ^ 2).natAbs.divisors.card : ℝ) ^ 4)))
      ≤ C * (H ^ 2 + 1) * ((((2 * R + 1 : ℕ)) : ℝ) ^ 2) * (Real.log (H + R + 2)) ^ K0 := by
  obtain ⟨C1, hC1, hLC⟩ := dyadic_log_series_bound K0
  refine ⟨16 * C0 * C1, by positivity, ?_⟩
  intro H hH R hR
  have hHpos : (0 : ℝ) < H := lt_of_lt_of_le zero_lt_one hH
  have hXle : ∀ j : ℕ, (2:ℝ)^j * H ≤ (boxX H j : ℝ) := boxX_ge H
  have hXub : ∀ j : ℕ, (boxX H j : ℝ) ≤ (2:ℝ)^j * (H + 1) := boxX_le H hHpos.le
  have hXn1 : ∀ j : ℕ, 1 ≤ boxX H j := boxX_one H hH
  obtain ⟨k, hk1, hk2⟩ := dyadic_weight_pointwise H hH (boxX H) hXle
  -- box bound for the u-summed function
  have hboxf : ∀ X' Y' : ℕ, 1 ≤ X' → 1 ≤ Y' →
      boxSum R X' Y' ≤ C0 * (R:ℝ)^2 * (X':ℝ) * (Y':ℝ)
        * (Real.log ((R:ℝ) + (X':ℝ) + (Y':ℝ) + 2))^K0 := by
    intro X' Y' hX' hY'
    have hb := hbox R hR X' hX' Y' hY'
    have hsw : boxSum R X' Y' =
        ∑ u1 ∈ Finset.Icc (-(R:ℤ)) (R:ℤ), ∑ u2 ∈ Finset.Icc (-(R:ℤ)) (R:ℤ),
          (Nat.gcd u1.natAbs u2.natAbs : ℝ) *
            (∑ h1 ∈ Finset.Icc (-(X':ℤ)) (X':ℤ), ∑ h2 ∈ Finset.Icc (-(Y':ℤ)) (Y':ℤ),
              (((u1 * h1^2 - u2 * h2^2).natAbs.divisors.card : ℝ)^4)) := by
      unfold boxSum Fsum
      rw [Finset.sum_product]
      rw [sum_swap_four]
      refine Finset.sum_congr rfl (fun u1 _ => Finset.sum_congr rfl (fun u2 _ => ?_))
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun h1 _ => ?_)
      rw [Finset.mul_sum]
    rw [hsw]
    exact hb
  -- bound on every finite partial sum
  have hmain : ∀ t : Finset (ℤ × ℤ),
      (∑ p ∈ t, (1 + (p.1:ℝ)^2/H^2)⁻¹ * (1 + (p.2:ℝ)^2/H^2)⁻¹ * Fsum R p)
        ≤ 16 * C0 * (R:ℝ)^2 * C1 * (H^2 + 1) * (Real.log (H + (R:ℝ) + 2))^K0 := by
    intro t
    have hw : ∀ p : ℤ × ℤ, (1 + (p.1:ℝ)^2/H^2)⁻¹ * (1 + (p.2:ℝ)^2/H^2)⁻¹
        ≤ 16 * (1/4:ℝ)^(k p.1 + k p.2) := by
      intro p
      have h1 := hk2 p.1
      have h2 := hk2 p.2
      have hp1 : (0:ℝ) ≤ 4 * (1/4:ℝ)^(k p.1) := by positivity
      have hc : (0:ℝ) ≤ (1 + (p.2:ℝ)^2/H^2)⁻¹ := by positivity
      calc (1 + (p.1:ℝ)^2/H^2)⁻¹ * (1 + (p.2:ℝ)^2/H^2)⁻¹
          ≤ (4 * (1/4:ℝ)^(k p.1)) * (4 * (1/4:ℝ)^(k p.2)) := mul_le_mul h1 h2 hc hp1
        _ = 16 * (1/4:ℝ)^(k p.1 + k p.2) := by
              rw [show (4:ℝ) * (1/4)^(k p.1) * (4 * (1/4)^(k p.2))
                    = 16 * ((1/4:ℝ)^(k p.1) * (1/4)^(k p.2)) by ring, ← pow_add]
    have hstep1 : (∑ p ∈ t, (1 + (p.1:ℝ)^2/H^2)⁻¹ * (1 + (p.2:ℝ)^2/H^2)⁻¹ * Fsum R p)
        ≤ ∑ p ∈ t, 16 * (1/4:ℝ)^(k p.1 + k p.2) * Fsum R p := by
      refine Finset.sum_le_sum (fun p _ => ?_)
      exact mul_le_mul_of_nonneg_right (hw p) (Fsum_nonneg R p)
    let g : ℤ × ℤ → ℕ × ℕ := fun p => (k p.1, k p.2)
    have hfiber : (∑ p ∈ t, 16 * (1/4:ℝ)^(k p.1 + k p.2) * Fsum R p)
        = ∑ b ∈ t.image g, 16 * (1/4:ℝ)^(b.1 + b.2)
            * (∑ p ∈ t.filter (fun p => g p = b), Fsum R p) := by
      rw [← Finset.sum_fiberwise_of_maps_to (s := t) (t := t.image g) (g := g)
            (fun i hi => Finset.mem_image_of_mem g hi)
            (fun i => 16 * (1/4:ℝ)^(k i.1 + k i.2) * Fsum R i)]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun p hp => ?_)
      have hgp : g p = b := (Finset.mem_filter.mp hp).2
      have hk1' : k p.1 = b.1 := by
        have h := congrArg Prod.fst hgp; simpa [g] using h
      have hk2' : k p.2 = b.2 := by
        have h := congrArg Prod.snd hgp; simpa [g] using h
      rw [hk1', hk2']
    have hfb : ∀ b ∈ t.image g,
        (∑ p ∈ t.filter (fun p => g p = b), Fsum R p)
          ≤ boxSum R (boxX H b.1) (boxX H b.2) := by
      intro b hb
      have hsub : t.filter (fun p => g p = b)
          ⊆ (Finset.Icc (-(((boxX H b.1 : ℕ)) : ℤ)) (((boxX H b.1 : ℕ)) : ℤ))
              ×ˢ (Finset.Icc (-(((boxX H b.2 : ℕ)) : ℤ)) (((boxX H b.2 : ℕ)) : ℤ)) := by
        intro p hp
        have hgp : g p = b := (Finset.mem_filter.mp hp).2
        have hk1' : k p.1 = b.1 := by
          have h := congrArg Prod.fst hgp; simpa [g] using h
        have hk2' : k p.2 = b.2 := by
          have h := congrArg Prod.snd hgp; simpa [g] using h
        have ha1 := abs_le.mp (hk1 p.1)
        rw [hk1'] at ha1
        have ha2 := abs_le.mp (hk1 p.2)
        rw [hk2'] at ha2
        refine Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, Finset.mem_Icc.mpr ⟨?_, ?_⟩⟩
        · exact_mod_cast ha1.1
        · exact_mod_cast ha1.2
        · exact_mod_cast ha2.1
        · exact_mod_cast ha2.2
      calc (∑ p ∈ t.filter (fun p => g p = b), Fsum R p)
          ≤ ∑ p ∈ (Finset.Icc (-(((boxX H b.1 : ℕ)) : ℤ)) (((boxX H b.1 : ℕ)) : ℤ))
                    ×ˢ (Finset.Icc (-(((boxX H b.2 : ℕ)) : ℤ)) (((boxX H b.2 : ℕ)) : ℤ)), Fsum R p :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => Fsum_nonneg R i)
        _ = boxSum R (boxX H b.1) (boxX H b.2) := rfl
    have hsum_ub : Summable (fun b : ℕ × ℕ =>
        16 * (1/4:ℝ)^(b.1 + b.2) * (C0 * (R:ℝ)^2 * (boxX H b.1 : ℝ) * (boxX H b.2 : ℝ)
          * (Real.log ((R:ℝ) + (boxX H b.1 : ℝ) + (boxX H b.2 : ℝ) + 2))^K0)) := by
      have h0 := (hLC H hH (boxX H) hXle hXub R hR).1
      exact (h0.mul_left (16 * C0 * (R:ℝ)^2)).congr (fun b => by ring)
    have hsum_maj : Summable (fun b : ℕ × ℕ =>
        16 * (1/4:ℝ)^(b.1 + b.2) * boxSum R (boxX H b.1) (boxX H b.2)) := by
      refine Summable.of_nonneg_of_le (f := fun b : ℕ × ℕ =>
          16 * (1/4:ℝ)^(b.1 + b.2) * (C0 * (R:ℝ)^2 * (boxX H b.1 : ℝ) * (boxX H b.2 : ℝ)
            * (Real.log ((R:ℝ) + (boxX H b.1 : ℝ) + (boxX H b.2 : ℝ) + 2))^K0)) ?_ ?_ hsum_ub
      · intro b
        exact mul_nonneg (by positivity) (boxSum_nonneg R (boxX H b.1) (boxX H b.2))
      · intro b
        exact mul_le_mul_of_nonneg_left (hboxf (boxX H b.1) (boxX H b.2) (hXn1 b.1) (hXn1 b.2)) (by positivity)
    calc (∑ p ∈ t, (1 + (p.1:ℝ)^2/H^2)⁻¹ * (1 + (p.2:ℝ)^2/H^2)⁻¹ * Fsum R p)
        ≤ ∑ p ∈ t, 16 * (1/4:ℝ)^(k p.1 + k p.2) * Fsum R p := hstep1
      _ = ∑ b ∈ t.image g, 16 * (1/4:ℝ)^(b.1 + b.2)
            * (∑ p ∈ t.filter (fun p => g p = b), Fsum R p) := hfiber
      _ ≤ ∑ b ∈ t.image g, 16 * (1/4:ℝ)^(b.1 + b.2) * boxSum R (boxX H b.1) (boxX H b.2) := by
            refine Finset.sum_le_sum (fun b hb => ?_)
            exact mul_le_mul_of_nonneg_left (hfb b hb) (by positivity)
      _ ≤ ∑' b : ℕ × ℕ, 16 * (1/4:ℝ)^(b.1 + b.2) * boxSum R (boxX H b.1) (boxX H b.2) :=
            Summable.sum_le_tsum _ (fun b _ => mul_nonneg (by positivity)
              (boxSum_nonneg R (boxX H b.1) (boxX H b.2))) hsum_maj
      _ ≤ ∑' b : ℕ × ℕ, 16 * (1/4:ℝ)^(b.1 + b.2) * (C0 * (R:ℝ)^2 * (boxX H b.1 : ℝ) * (boxX H b.2 : ℝ)
            * (Real.log ((R:ℝ) + (boxX H b.1 : ℝ) + (boxX H b.2 : ℝ) + 2))^K0) := by
            refine Summable.tsum_le_tsum (fun b => ?_) hsum_maj hsum_ub
            exact mul_le_mul_of_nonneg_left (hboxf (boxX H b.1) (boxX H b.2) (hXn1 b.1) (hXn1 b.2)) (by positivity)
      _ = 16 * C0 * (R:ℝ)^2 * (∑' b : ℕ × ℕ, (1/4:ℝ)^(b.1 + b.2) * ((boxX H b.1 : ℝ) * (boxX H b.2 : ℝ))
            * (Real.log ((R:ℝ) + (boxX H b.1 : ℝ) + (boxX H b.2 : ℝ) + 2))^K0) := by
            rw [← tsum_mul_left]
            exact tsum_congr (fun b => by ring)
      _ ≤ 16 * C0 * (R:ℝ)^2 * (C1 * (H^2 + 1) * (Real.log (H + (R:ℝ) + 2))^K0) :=
            mul_le_mul_of_nonneg_left (hLC H hH (boxX H) hXle hXub R hR).2 (by positivity)
      _ = 16 * C0 * (R:ℝ)^2 * C1 * (H^2 + 1) * (Real.log (H + (R:ℝ) + 2))^K0 := by ring
  have hMnn : (0:ℝ) ≤ 16 * C0 * (R:ℝ)^2 * C1 * (H^2 + 1) * (Real.log (H + (R:ℝ) + 2))^K0 := by
    have hR0 : (0:ℝ) ≤ (R:ℝ) := by positivity
    have hl : (0:ℝ) ≤ (Real.log (H + (R:ℝ) + 2))^K0 :=
      pow_nonneg (Real.log_nonneg (by linarith [hH, hR0])) _
    have h1 : (0:ℝ) ≤ 16 * C0 := mul_nonneg (by norm_num) hC0.le
    have h2 : (0:ℝ) ≤ 16 * C0 * (R:ℝ)^2 := mul_nonneg h1 (sq_nonneg _)
    have h3 : (0:ℝ) ≤ 16 * C0 * (R:ℝ)^2 * C1 := mul_nonneg h2 hC1.le
    have h4 : (0:ℝ) ≤ 16 * C0 * (R:ℝ)^2 * C1 * (H^2 + 1) := by
      apply mul_nonneg h3; positivity
    exact mul_nonneg h4 hl
  have htsum : (∑' p : ℤ × ℤ, (1 + (p.1:ℝ)^2/H^2)⁻¹ * (1 + (p.2:ℝ)^2/H^2)⁻¹ * Fsum R p)
      ≤ 16 * C0 * (R:ℝ)^2 * C1 * (H^2 + 1) * (Real.log (H + (R:ℝ) + 2))^K0 :=
    tsum_le_of_sum_le' hMnn hmain
  have hexch : (∑ u1 ∈ Finset.Icc (-(R:ℤ)) (R:ℤ), ∑ u2 ∈ Finset.Icc (-(R:ℤ)) (R:ℤ),
        (Nat.gcd u1.natAbs u2.natAbs : ℝ) *
          (∑' h : ℤ × ℤ, (1 + (h.1:ℝ)^2/H^2)⁻¹ * (1 + (h.2:ℝ)^2/H^2)⁻¹
            * (((u1 * h.1^2 - u2 * h.2^2).natAbs.divisors.card : ℝ)^4)))
      = ∑' p : ℤ × ℤ, (1 + (p.1:ℝ)^2/H^2)⁻¹ * (1 + (p.2:ℝ)^2/H^2)⁻¹ * Fsum R p := by
    set sI : Finset ℤ := Finset.Icc (-(R:ℤ)) (R:ℤ) with hsI
    have hsumm : ∀ u ∈ sI ×ˢ sI, Summable (Ft H u) := by
      intro u _
      exact (summable_w_tau4 H hH u.1 u.2).mul_left _
    have key := Summable.tsum_finsetSum (L := SummationFilter.unconditional (ℤ × ℤ))
        (f := Ft H) (s := sI ×ˢ sI) hsumm
    have h1 : (∑ u1 ∈ Finset.Icc (-(R:ℤ)) (R:ℤ), ∑ u2 ∈ Finset.Icc (-(R:ℤ)) (R:ℤ),
        (Nat.gcd u1.natAbs u2.natAbs : ℝ) *
          (∑' h : ℤ × ℤ, (1 + (h.1:ℝ)^2/H^2)⁻¹ * (1 + (h.2:ℝ)^2/H^2)⁻¹
            * (((u1 * h.1^2 - u2 * h.2^2).natAbs.divisors.card : ℝ)^4)))
        = ∑ u ∈ sI ×ˢ sI, ∑' p : ℤ × ℤ, Ft H u p := by
      rw [hsI, Finset.sum_product]
      refine Finset.sum_congr rfl (fun u1 _ => Finset.sum_congr rfl (fun u2 _ => ?_))
      rw [← tsum_mul_left]
      refine tsum_congr (fun p => ?_)
      simp only [Ft]
    have h2 : (∑' p : ℤ × ℤ, ∑ u ∈ sI ×ˢ sI, Ft H u p)
        = ∑' p : ℤ × ℤ, (1 + (p.1:ℝ)^2/H^2)⁻¹ * (1 + (p.2:ℝ)^2/H^2)⁻¹ * Fsum R p := by
      refine tsum_congr (fun p => ?_)
      have hpt : (∑ u ∈ sI ×ˢ sI, Ft H u p)
          = (1 + (p.1:ℝ)^2/H^2)⁻¹ * (1 + (p.2:ℝ)^2/H^2)⁻¹ * Fsum R p := by
        rw [Finset.sum_product, Fsum]
        simp only [Ft, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun u1 _ => Finset.sum_congr rfl (fun u2 _ => ?_))
        ring
      exact hpt
    rw [h1, ← key, h2]
  rw [hexch]
  refine le_trans htsum ?_
  have hRsq : (R:ℝ)^2 ≤ ((((2 * R + 1 : ℕ)) : ℝ))^2 := by
    have h1 : (R:ℝ) ≤ ((((2 * R + 1 : ℕ)) : ℝ)) := by
      have h2 : R ≤ 2 * R + 1 := by omega
      exact_mod_cast h2
    exact pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (R:ℝ)) h1 2
  have hlog : (0:ℝ) ≤ (Real.log (H + (R:ℝ) + 2))^K0 := by
    apply pow_nonneg
    apply Real.log_nonneg
    have hR0 : (0:ℝ) ≤ (R:ℝ) := by positivity
    linarith [hH, hR0]
  have hA : (0:ℝ) ≤ 16 * C0 * C1 * (H^2+1) := by positivity
  calc 16 * C0 * (R:ℝ)^2 * C1 * (H^2 + 1) * (Real.log (H + (R:ℝ) + 2))^K0
      = (16 * C0 * C1 * (H^2+1)) * (R:ℝ)^2 * (Real.log (H + (R:ℝ) + 2))^K0 := by ring
    _ ≤ (16 * C0 * C1 * (H^2+1)) * ((((2 * R + 1 : ℕ)) : ℝ)^2) * (Real.log (H + (R:ℝ) + 2))^K0 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRsq hA) hlog
    _ = 16 * C0 * C1 * (H ^ 2 + 1) * ((((2 * R + 1 : ℕ)) : ℝ) ^ 2) * (Real.log (H + (R:ℝ) + 2)) ^ K0 := by ring

end

end Work.FIArea2.R6
