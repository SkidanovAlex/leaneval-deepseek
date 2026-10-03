import Mathlib
import Submission.Work.FIArea4.WdyadDefs2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The local variance as a sum of squared class sums

`Wloc F R d₁ d₂ = ∑_{a < q} |K(a)|²` is the *inverse* discrete Fourier transform of the
sequence `C ↦ classSum F R d₁ d₂ C`, where `q = [d₁,d₂]`:

  `K(a) = (1/q) ∑_{C < q} (classSum C) · e(aC/q)`.

The classical Plancherel identity for the Fourier matrix `(a,C) ↦ e(aC/q)` then gives

  `∑_{a<q} |K(a)|² = (1/q) ∑_{C<q} |classSum C|²`,

which is the statement below.  The only analytic input is the summability of `k ↦ F(k/q)`,
which is a consequence of the decay hypothesis on `F`.
-/

namespace Work.FIArea4

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The additive character `x ↦ exp (2πI x)`, evaluated at the rational point `m/q`. -/
def EE (q : ℕ) (m : ℤ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (m : ℝ) / (q : ℝ))

lemma EE_zero (q : ℕ) : EE q 0 = 1 := by simp [EE]

lemma EE_add (q : ℕ) (m n : ℤ) : EE q (m + n) = EE q m * EE q n := by
  simp only [EE, Int.cast_add]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma EE_eq_zeta_zpow (q : ℕ) (m : ℤ) :
    EE q m = (Complex.exp (2 * Real.pi * Complex.I / (q : ℝ))) ^ m := by
  unfold EE
  rw [← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

lemma EE_eq_one_iff (q : ℕ) (hq : q ≠ 0) (m : ℤ) : EE q m = 1 ↔ (q : ℤ) ∣ m := by
  rw [EE_eq_zeta_zpow]
  exact (Complex.isPrimitiveRoot_exp q hq).zpow_eq_one_iff_dvd m

lemma EE_q_mul (q : ℕ) (j : ℤ) : EE q ((q : ℤ) * j) = 1 := by
  rcases eq_or_ne q 0 with hq | hq
  · subst hq; simp [EE]
  · rw [EE_eq_one_iff q hq]; exact dvd_mul_right _ _

lemma EE_neg (q : ℕ) (m : ℤ) : EE q (-m) = (EE q m)⁻¹ := by
  rw [EE_eq_zeta_zpow, EE_eq_zeta_zpow, zpow_neg]

lemma conj_EE (q : ℕ) (m : ℤ) : (starRingEnd ℂ) (EE q m) = EE q (-m) := by
  have h : (starRingEnd ℂ) (EE q m)
      = Complex.exp ((starRingEnd ℂ) (2 * Real.pi * Complex.I * (m : ℝ) / (q : ℝ))) := by
    simp only [EE]
    rw [Complex.exp_conj]
  rw [h]
  have harg : (starRingEnd ℂ) (2 * Real.pi * Complex.I * (m : ℝ) / (q : ℝ))
      = 2 * Real.pi * Complex.I * ((-m : ℤ) : ℝ) / (q : ℝ) := by
    simp only [map_div₀, map_mul, map_ofNat]
    simp
  rw [harg, ← EE, EE_neg]

lemma norm_EE (q : ℕ) (m : ℤ) : ‖EE q m‖ = 1 := by
  simp only [EE, Complex.norm_exp]
  rw [Complex.div_re, Complex.mul_re, Complex.mul_im]
  simp

lemma normSq_EE (q : ℕ) (m : ℤ) : Complex.normSq (EE q m) = 1 := by
  rw [Complex.normSq_eq_norm_sq, norm_EE, one_pow]

lemma EE_nat_mul (q : ℕ) (n : ℕ) (m : ℤ) : EE q ((n : ℤ) * m) = (EE q m) ^ n := by
  simp only [EE]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma EE_int_mul (q : ℕ) (j m : ℤ) : EE q (j * m) = (EE q m) ^ j := by
  simp only [EE]
  rw [← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

lemma EE_mul_conj_EE (q : ℕ) (x y : ℤ) : EE q x * (starRingEnd ℂ) (EE q y) = EE q (x - y) := by
  rw [conj_EE, ← EE_add, sub_eq_add_neg]

/-- Orthogonality of the additive characters: `∑_{a<q} e(am/q) = q` if `q ∣ m`, else `0`. -/
lemma sum_range_EE_mul (q : ℕ) (hq : q ≠ 0) (m : ℤ) :
    ∑ a ∈ Finset.range q, EE q ((a : ℤ) * m) = if (q : ℤ) ∣ m then (q : ℂ) else 0 := by
  have hnat : ∀ a : ℕ, EE q ((a : ℤ) * m) = (EE q m) ^ a := fun a => EE_nat_mul q a m
  simp only [hnat]
  by_cases hx : EE q m = 1
  · rw [hx, if_pos ((EE_eq_one_iff q hq m).mp hx)]
    simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  · rw [if_neg (fun h => hx ((EE_eq_one_iff q hq m).mpr h)), geom_sum_eq hx q]
    have hqpow : (EE q m) ^ q = 1 := by
      rw [← EE_nat_mul]
      exact EE_q_mul q m
    rw [hqpow, sub_self, zero_div]

/-- The residue-class condition `m % q = C % q` against the character `e(aC/q)`: summing over the
classes `C < q` picks out the single class of `m` and returns `e(am/q)`. -/
lemma sum_ite_EE (q : ℕ) (hq : q ≠ 0) (a : ℕ) (m : ℤ) :
    ∑ C ∈ Finset.range q,
        (if m % (q : ℤ) = ((C : ℤ) % (q : ℤ)) then EE q ((a : ℤ) * C) else 0)
      = EE q ((a : ℤ) * m) := by
  have hqZ : (0 : ℤ) < (q : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hq
  set M : ℤ := m % (q : ℤ) with hMdef
  have hMnn : 0 ≤ M := Int.emod_nonneg m (by exact_mod_cast hq : (q : ℤ) ≠ 0)
  have hMlt : M < (q : ℤ) := Int.emod_lt_of_pos m hqZ
  have hMtoNat_lt : M.toNat < q := by
    rw [Int.toNat_lt hMnn]; exact hMlt
  have hstep : ∀ C ∈ Finset.range q,
      (if m % (q : ℤ) = ((C : ℤ) % (q : ℤ)) then EE q ((a : ℤ) * C) else 0)
        = (if C = M.toNat then EE q ((a : ℤ) * C) else 0) := by
    intro C hC
    have hCq : (C : ℤ) < (q : ℤ) := by exact_mod_cast Finset.mem_range.mp hC
    have hC0 : (0 : ℤ) ≤ (C : ℤ) := Int.natCast_nonneg C
    have hCmod : ((C : ℤ) % (q : ℤ)) = (C : ℤ) := Int.emod_eq_of_lt hC0 hCq
    rw [hCmod, ← hMdef]
    by_cases h : C = M.toNat
    · rw [if_pos (by rw [h, Int.toNat_of_nonneg hMnn]), if_pos h]
    · rw [if_neg, if_neg h]
      intro hcon
      apply h
      have : M.toNat = C := by
        have h1 : (M.toNat : ℤ) = (C : ℤ) := by rw [Int.toNat_of_nonneg hMnn]; exact hcon
        exact Int.ofNat_inj.mp h1
      exact this.symm
  rw [Finset.sum_congr rfl hstep, Finset.sum_ite_eq']
  rw [if_pos (Finset.mem_range.mpr hMtoNat_lt)]
  symm
  have hd : (q : ℤ) ∣ ((a : ℤ) * m - (a : ℤ) * (M.toNat : ℤ)) := by
    have hm : m - M = (q : ℤ) * (m / (q : ℤ)) := by
      have h := Int.emod_add_mul_ediv m (q : ℤ)
      rw [← hMdef] at h
      linarith
    have hrw : (a : ℤ) * m - (a : ℤ) * (M.toNat : ℤ) = (a : ℤ) * (m - M) := by
      rw [Int.toNat_of_nonneg hMnn]; ring
    rw [hrw, hm]
    exact ⟨(a : ℤ) * (m / (q : ℤ)), by ring⟩
  have hEd : EE q ((a : ℤ) * m - (a : ℤ) * (M.toNat : ℤ)) = 1 := by
    rw [EE_eq_one_iff q hq]; exact hd
  have hsplit : (a : ℤ) * m
      = (a : ℤ) * (M.toNat : ℤ) + ((a : ℤ) * m - (a : ℤ) * (M.toNat : ℤ)) := by ring
  rw [hsplit, EE_add, hEd, mul_one]

/-- Summability of `k ↦ (1 + t|k|)^{-2}` over `ℤ`, for `t > 0`. -/
lemma summable_one_add_mul_abs_rpow (t : ℝ) (ht : 0 < t) :
    Summable (fun k : ℤ => (1 + t * |(k:ℝ)|) ^ (-(2:ℝ))) := by
  set c : ℝ := min 1 t with hc
  have hcpos : 0 < c := lt_min one_pos ht
  have hgle : ∀ k : ℤ, c * |(k:ℝ)| ≤ 1 + t * |(k:ℝ)| := by
    intro k
    have h1 : c ≤ t := min_le_right _ _
    have h2 : c ≤ 1 := min_le_left _ _
    nlinarith [abs_nonneg (k:ℝ), mul_le_mul_of_nonneg_right h1 (abs_nonneg (k:ℝ)),
      mul_le_mul_of_nonneg_right h2 (abs_nonneg (k:ℝ))]
  have hg : Summable (fun k : ℤ => c⁻¹ ^ 2 * (|(k:ℝ)| ^ 2)⁻¹) := by
    have h := (Real.summable_one_div_int_add_rpow 0 2).mpr (by norm_num : (1:ℝ) < 2)
    have h2 : Summable (fun k : ℤ => (|(k:ℝ)| ^ 2)⁻¹) := by
      simpa [one_div] using h
    exact h2.mul_left (c⁻¹ ^ 2)
  refine Summable.of_norm_bounded_eventually hg ?_
  rw [Filter.eventually_cofinite]
  refine Set.Finite.subset (Set.finite_singleton (0:ℤ)) ?_
  intro k hk
  rw [Set.mem_ofPred_eq] at hk
  simp only [not_le, Set.mem_singleton_iff] at hk ⊢
  by_contra hk0
  have hpos : 0 < 1 + t * |(k:ℝ)| := by positivity
  have hbase : (1 + t * |(k:ℝ)|) ^ (-(2:ℝ)) = ((1 + t * |(k:ℝ)|) ^ 2)⁻¹ := by
    rw [show (-(2:ℝ)) = -((2:ℕ):ℝ) by norm_num, Real.rpow_neg (by positivity), Real.rpow_natCast]
  have hnorm : ‖(1 + t * |(k:ℝ)|) ^ (-(2:ℝ))‖ = ((1 + t * |(k:ℝ)|) ^ 2)⁻¹ := by
    rw [Real.norm_eq_abs, hbase, abs_of_nonneg (by positivity)]
  rw [hnorm] at hk
  have hc2 : 0 < c ^ 2 * |(k:ℝ)| ^ 2 := by
    have : (0:ℝ) < |(k:ℝ)| := by rw [abs_pos]; exact_mod_cast hk0
    positivity
  have hle : c ^ 2 * |(k:ℝ)| ^ 2 ≤ (1 + t * |(k:ℝ)|) ^ 2 := by
    have h := hgle k
    calc c ^ 2 * |(k:ℝ)| ^ 2 = (c * |(k:ℝ)|) ^ 2 := by ring
      _ ≤ (1 + t * |(k:ℝ)|) ^ 2 := pow_le_pow_left₀ (by positivity) h 2
  have hthis : ((1 + t * |(k:ℝ)|) ^ 2)⁻¹ ≤ (c ^ 2 * |(k:ℝ)| ^ 2)⁻¹ :=
    (inv_le_inv₀ (show 0 < (1 + t * |(k:ℝ)|) ^ 2 by positivity) hc2).mpr hle
  have heq : c⁻¹ ^ 2 * (|(k:ℝ)| ^ 2)⁻¹ = (c ^ 2 * |(k:ℝ)| ^ 2)⁻¹ := by
    rw [mul_inv, inv_pow]
  rw [heq] at hk
  linarith [hthis, hk]

/-- Summability of the norms `k ↦ ‖F (k/q)‖` from the decay hypothesis on `F`. -/
lemma summable_phi_norm (σ : ℝ) (hσ : 1 ≤ σ) (F : ℝ → ℂ) (C₀ : ℝ) (_hC₀ : 0 < C₀)
    (hF : ∀ ξ : ℝ, ‖F ξ‖ ≤ C₀ * σ * (1 + σ * |ξ|) ^ (-(2:ℝ)))
    (q : ℕ) (hq : 0 < q) :
    Summable (fun k : ℤ => ‖F ((k : ℝ) / (q : ℝ))‖) := by
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have ht : 0 < σ / (q:ℝ) := div_pos (by linarith) hqR
  refine Summable.of_norm_bounded
    ((summable_one_add_mul_abs_rpow (σ/(q:ℝ)) ht).mul_left (C₀*σ)) (fun k => ?_)
  have h := hF ((k:ℝ)/(q:ℝ))
  have harg : σ * |(k:ℝ)/(q:ℝ)| = (σ/(q:ℝ)) * |(k:ℝ)| := by
    rw [abs_div, abs_of_pos hqR]; field_simp
  rw [harg] at h
  simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (F ((k:ℝ)/(q:ℝ))))] using h

/-- A summable sequence restricted to a subsequence (with a constant prefactor) is summable. -/
lemma summable_ite_cond (φ : ℤ → ℂ) (hφn : Summable (fun k : ℤ => ‖φ k‖)) (w : ℂ)
    (P : ℤ → Prop) [DecidablePred P] :
    Summable (fun k : ℤ => w * (if P k then φ k else 0)) := by
  refine Summable.of_norm_bounded (hφn.mul_left ‖w‖) (fun k => ?_)
  by_cases h : P k
  · rw [if_pos h, norm_mul]
  · rw [if_neg h, norm_mul, norm_zero, mul_zero]; positivity

/-- Residue classes modulo `q` separate the points of `[0,q)`. -/
lemma dvd_sub_iff_eq (q : ℕ) {C C' : ℕ} (hC : C < q) (hC' : C' < q) :
    ((q : ℤ) ∣ ((C : ℤ) - (C' : ℤ))) ↔ C = C' := by
  rw [← ZMod.intCast_eq_intCast_iff_dvd_sub (C' : ℤ) (C : ℤ) q, Int.cast_natCast,
      Int.cast_natCast, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hC', Nat.mod_eq_of_lt hC,
      eq_comm]

/-- The class sums, written as a single `tsum` over `k`. -/
lemma clsm_tsum (q : ℕ) (s : Finset ℕ) (w : ℕ → ℂ) (φ : ℤ → ℂ)
    (hφn : Summable (fun k : ℤ => ‖φ k‖)) (C : ℕ) :
    (∑ r ∈ s, w r * ∑' k : ℤ, (if ((r : ℤ) * k) % (q : ℤ) = (C : ℤ) % (q : ℤ) then φ k else 0))
      = ∑' k : ℤ, (∑ r ∈ s, w r *
            (if ((r : ℤ) * k) % (q : ℤ) = (C : ℤ) % (q : ℤ) then (1 : ℂ) else 0)) * φ k := by
  rw [show (∑ r ∈ s, w r * ∑' k : ℤ,
          (if ((r : ℤ) * k) % (q : ℤ) = (C : ℤ) % (q : ℤ) then φ k else 0))
        = ∑ r ∈ s, ∑' k : ℤ, w r *
          (if ((r : ℤ) * k) % (q : ℤ) = (C : ℤ) % (q : ℤ) then φ k else 0)
        from Finset.sum_congr rfl (fun r _ => (tsum_mul_left).symm)]
  rw [show (∑ r ∈ s, ∑' k : ℤ, w r *
          (if ((r : ℤ) * k) % (q : ℤ) = (C : ℤ) % (q : ℤ) then φ k else 0))
        = ∑' k : ℤ, ∑ r ∈ s, w r *
          (if ((r : ℤ) * k) % (q : ℤ) = (C : ℤ) % (q : ℤ) then φ k else 0)
        from (Summable.tsum_finsetSum
          (fun r _ => summable_ite_cond φ hφn (w r) _)).symm]
  refine tsum_congr (fun k => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  by_cases h : ((r : ℤ) * k) % (q : ℤ) = (C : ℤ) % (q : ℤ)
  · rw [if_pos h, if_pos h]; ring
  · rw [if_neg h, if_neg h]; ring

/-- The inverse Fourier transform identity: the class sums summed against the characters recover
the kernel `Ker`. -/
lemma inversion (q : ℕ) (hq : q ≠ 0) (s : Finset ℕ) (w : ℕ → ℂ) (φ : ℤ → ℂ)
    (hφn : Summable (fun k : ℤ => ‖φ k‖)) (a : ℕ) :
    (∑ C ∈ Finset.range q,
        (∑' k : ℤ, (∑ r ∈ s, w r *
            (if ((r : ℤ) * k) % (q : ℤ) = (C : ℤ) % (q : ℤ) then (1 : ℂ) else 0)) * φ k)
          * EE q ((a : ℤ) * C))
      = ∑' k : ℤ, φ k * (∑ r ∈ s, w r * EE q ((r : ℤ) * k * (a : ℤ))) := by
  have hw : (0:ℝ) ≤ ∑ r ∈ s, ‖w r‖ := Finset.sum_nonneg (fun r _ => norm_nonneg _)
  have hbound : ∀ k : ℤ, ∀ C : ℕ,
      ‖∑ r ∈ s, w r *
        (if ((r : ℤ) * k) % (q : ℤ) = (C : ℤ) % (q : ℤ) then (1 : ℂ) else 0)‖
        ≤ ∑ r ∈ s, ‖w r‖ := by
    intro k C
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun r _ => ?_))
    by_cases h : ((r : ℤ) * k) % (q : ℤ) = (C : ℤ) % (q : ℤ)
    · rw [if_pos h, norm_mul, norm_one, mul_one]
    · rw [if_neg h, norm_mul, norm_zero, mul_zero]
      exact norm_nonneg _
  rw [show (∑ C ∈ Finset.range q,
        (∑' k : ℤ, (∑ r ∈ s, w r *
            (if ((r : ℤ) * k) % (q : ℤ) = (C : ℤ) % (q : ℤ) then (1 : ℂ) else 0)) * φ k)
          * EE q ((a : ℤ) * C))
        = ∑ C ∈ Finset.range q, ∑' k : ℤ, (∑ r ∈ s, w r *
            (if ((r : ℤ) * k) % (q : ℤ) = (C : ℤ) % (q : ℤ) then (1 : ℂ) else 0)) * φ k
            * EE q ((a : ℤ) * C)
        from Finset.sum_congr rfl (fun C _ => (tsum_mul_right).symm)]
  rw [show (∑ C ∈ Finset.range q, ∑' k : ℤ, (∑ r ∈ s, w r *
          (if ((r : ℤ) * k) % (q : ℤ) = (C : ℤ) % (q : ℤ) then (1 : ℂ) else 0)) * φ k
          * EE q ((a : ℤ) * C))
        = ∑' k : ℤ, ∑ C ∈ Finset.range q, (∑ r ∈ s, w r *
            (if ((r : ℤ) * k) % (q : ℤ) = (C : ℤ) % (q : ℤ) then (1 : ℂ) else 0)) * φ k
            * EE q ((a : ℤ) * C)
        from (Summable.tsum_finsetSum (fun C _ =>
          Summable.of_norm_bounded (hφn.mul_left (∑ r ∈ s, ‖w r‖)) (fun k => by
            rw [norm_mul, norm_mul, norm_EE, mul_one]
            exact mul_le_mul_of_nonneg_right (hbound k C) (norm_nonneg _)))).symm]
  refine tsum_congr (fun k => ?_)
  rw [show (∑ C ∈ Finset.range q, (∑ r ∈ s, w r *
          (if ((r : ℤ) * k) % (q : ℤ) = (C : ℤ) % (q : ℤ) then (1 : ℂ) else 0)) * φ k
          * EE q ((a : ℤ) * C))
        = φ k * (∑ C ∈ Finset.range q, ∑ r ∈ s, w r *
            (if ((r : ℤ) * k) % (q : ℤ) = (C : ℤ) % (q : ℤ) then (1 : ℂ) else 0)
            * EE q ((a : ℤ) * C))
        from by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun C _ => ?_)
          rw [← Finset.sum_mul]; ring]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [show (∑ C ∈ Finset.range q, w r *
          (if ((r : ℤ) * k) % (q : ℤ) = (C : ℤ) % (q : ℤ) then (1 : ℂ) else 0)
          * EE q ((a : ℤ) * C))
        = w r * (∑ C ∈ Finset.range q,
            (if ((r : ℤ) * k) % (q : ℤ) = (C : ℤ) % (q : ℤ) then EE q ((a : ℤ) * C) else 0))
        from by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun C _ => ?_)
          by_cases h : ((r : ℤ) * k) % (q : ℤ) = (C : ℤ) % (q : ℤ)
          · rw [if_pos h, if_pos h]; ring
          · rw [if_neg h, if_neg h]; ring]
  rw [sum_ite_EE q hq a ((r : ℤ) * k)]
  congr 1
  ring_nf

/-- Plancherel for the Fourier matrix `(a,C) ↦ e(aC/q)`. -/
lemma parseval_EE (q : ℕ) (hq : q ≠ 0) (x : ℕ → ℂ) :
    ∑ a ∈ Finset.range q, Complex.normSq (∑ C ∈ Finset.range q, x C * EE q ((a : ℤ) * C))
      = (q : ℝ) * ∑ C ∈ Finset.range q, Complex.normSq (x C) := by
  have hcomplex : (∑ a ∈ Finset.range q,
        (∑ C ∈ Finset.range q, x C * EE q ((a : ℤ) * C))
          * (starRingEnd ℂ) (∑ C ∈ Finset.range q, x C * EE q ((a : ℤ) * C)))
      = (q : ℂ) * ∑ C ∈ Finset.range q, x C * (starRingEnd ℂ) (x C) := by
    have hZ : ∀ a : ℕ,
        (∑ C ∈ Finset.range q, x C * EE q ((a : ℤ) * C))
          * (starRingEnd ℂ) (∑ C ∈ Finset.range q, x C * EE q ((a : ℤ) * C))
        = ∑ C ∈ Finset.range q, ∑ C' ∈ Finset.range q,
            x C * (starRingEnd ℂ) (x C') * EE q ((a : ℤ) * ((C : ℤ) - (C' : ℤ))) := by
      intro a
      rw [map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl (fun C _ => ?_)
      refine Finset.sum_congr rfl (fun C' _ => ?_)
      rw [map_mul]
      calc (x C * EE q ((a : ℤ) * C))
              * ((starRingEnd ℂ) (x C') * (starRingEnd ℂ) (EE q ((a : ℤ) * C')))
          = (EE q ((a : ℤ) * C) * (starRingEnd ℂ) (EE q ((a : ℤ) * C')))
              * (x C * (starRingEnd ℂ) (x C')) := by ring
        _ = x C * (starRingEnd ℂ) (x C') * EE q ((a : ℤ) * ((C : ℤ) - (C' : ℤ))) := by
              rw [EE_mul_conj_EE,
                show (a : ℤ) * C - (a : ℤ) * C'
                    = (a : ℤ) * ((C : ℤ) - (C' : ℤ)) from by ring]
              ring
    rw [Finset.sum_congr rfl (fun a _ => hZ a)]
    have hstep : (∑ a ∈ Finset.range q, ∑ C ∈ Finset.range q, ∑ C' ∈ Finset.range q,
          x C * (starRingEnd ℂ) (x C') * EE q ((a : ℤ) * ((C : ℤ) - (C' : ℤ))))
        = ∑ C ∈ Finset.range q, ∑ C' ∈ Finset.range q,
          x C * (starRingEnd ℂ) (x C')
            * (∑ a ∈ Finset.range q, EE q ((a : ℤ) * ((C : ℤ) - (C' : ℤ)))) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun C _ => ?_)
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun C' _ => ?_)
      rw [Finset.mul_sum]
    rw [hstep]
    have hstep2 : (∑ C ∈ Finset.range q, ∑ C' ∈ Finset.range q,
          x C * (starRingEnd ℂ) (x C')
            * (∑ a ∈ Finset.range q, EE q ((a : ℤ) * ((C : ℤ) - (C' : ℤ)))))
        = ∑ C ∈ Finset.range q, ∑ C' ∈ Finset.range q,
          x C * (starRingEnd ℂ) (x C') * (if C = C' then (q : ℂ) else 0) := by
      refine Finset.sum_congr rfl (fun C hC => Finset.sum_congr rfl (fun C' hC' => ?_))
      rw [sum_range_EE_mul q hq,
        if_congr (dvd_sub_iff_eq q (Finset.mem_range.mp hC) (Finset.mem_range.mp hC')) rfl rfl]
    rw [hstep2]
    have hstep3 : (∑ C ∈ Finset.range q, ∑ C' ∈ Finset.range q,
          x C * (starRingEnd ℂ) (x C') * (if C = C' then (q : ℂ) else 0))
        = (q : ℂ) * ∑ C ∈ Finset.range q, x C * (starRingEnd ℂ) (x C) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun C hC => ?_)
      rw [Finset.sum_eq_single C (fun C' _ hne => by rw [if_neg (fun h => hne h.symm), mul_zero])
        (fun h => absurd hC h), if_pos rfl]
      ring
    rw [hstep3]
  have hre := congrArg Complex.re hcomplex
  rw [Complex.re_sum] at hre
  have hR : ((q : ℂ) * ∑ C ∈ Finset.range q, x C * (starRingEnd ℂ) (x C)).re
      = (q : ℝ) * ∑ C ∈ Finset.range q, Complex.normSq (x C) := by
    rw [Complex.mul_re, Complex.re_sum]
    simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
    congr 1
    refine Finset.sum_congr rfl (fun C _ => ?_)
    rw [mul_comm, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
  have hL : (∑ a ∈ Finset.range q,
        ((∑ C ∈ Finset.range q, x C * EE q ((a : ℤ) * C))
          * (starRingEnd ℂ) (∑ C ∈ Finset.range q, x C * EE q ((a : ℤ) * C))).re)
      = ∑ a ∈ Finset.range q,
          Complex.normSq (∑ C ∈ Finset.range q, x C * EE q ((a : ℤ) * C)) :=
    Finset.sum_congr rfl (fun a _ => by
      rw [mul_comm, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re])
  rw [hL, hR] at hre
  exact hre

/-- The exponential appearing in `KK` is `EE` evaluated at the integer `r·k·a`. -/
lemma exp_eq_EE (q : ℕ) (r a : ℕ) (k : ℤ) :
    Complex.exp (2 * Real.pi * Complex.I * (r : ℝ) * (k : ℝ) * (a : ℝ) / (q : ℝ))
      = EE q ((r : ℤ) * k * (a : ℤ)) := by
  simp only [EE]
  congr 1
  push_cast
  ring

end

end Work.FIArea4
