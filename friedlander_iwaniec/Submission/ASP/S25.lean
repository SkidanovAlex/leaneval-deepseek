/-
  Companion/main-paper step: the `τ^{20/3}`-weighted aggregate `(2.3)` for `X² + Y⁴` in its
  *final* form, valid for the whole modulus range `D ≤ x^{3/4}` and for all `t ≤ x`.

  The route is the one indicated by the exponent bookkeeping of `S24`:

  * `sum_tau_pow_Ad_le_cube` reduces `∑_{d ≤ D} τ(d)^{20/3} A_d(t)` to the pair `(a,c) = (0,0)`
    contribution `a_0 ∑_{d ≤ D} τ(d)^{20/3}` plus the **cube range** `d³ ≤ t`, where the weight is
    `(2τ(d))^{40}`;
  * the cube-range sum is handled by the *weighted* `(3.3)` (at the cut-off `t^{1/3}`, where the
    pointwise `τ(d)^{40} ≪ t^{40ε/3}` costs only `t^{13/1000}`) and by the weighted main-term sum
    `sum_Md_weight_le` (a general-weight version of the paper's `(K2)`-driven aggregate);
  * the pair `(a,c) = (0,0)` contribution is `≪ x^{3/4}(log x)^{127} ≪ A(x)(log x)^{127}` because
    `D ≤ x^{3/4}` and `A(x) ≫ x^{3/4}`.

  Consequently `∑_{d ≤ D, ♭} τ(d)^{20/3} |A_d(t) − g(d)A(t)| ≪ A(x)(log x)^B` uniformly for
  `D ≤ x^{3/4}`, `2 ≤ t ≤ x`, which together with `(R)` (`Submission.X2Y4_R_hypothesis`) yields the
  companion's hypothesis `(R′)` for `X² + Y⁴` by Hölder.
-/
import Mathlib
import Submission.ASP.S24
import Submission.S3g
import Submission.ASP_R
import Submission.Commons.NumberTheory.DivisorSum.sum_tau_pow_le
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sum_tau_pow_rho_div_le_general
import Submission.Commons.Analysis.MeanInequalities.sum_rpow_holder

set_option maxHeartbeats 1600000

namespace Submission.ASP

open Finset

noncomputable section

/-! ## Part A: `∑_{d ≤ D} τ(d)^{20/3} ≪ D (log D)^{127}` -/

/-- `∑_{d ≤ D} τ(d)^{20/3} ≤ C·D·(log(D+1))^{127}` (using `τ(d)^{20/3} ≤ τ(d)^7` and the
`k = 7` divisor-sum estimate). -/
theorem sum_tau_pow_twenty_third_le :
    ∃ C : ℝ, 0 < C ∧ ∀ D : ℕ, 1 ≤ D →
      (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ) ^ ((20:ℝ)/3)))
        ≤ C * (D:ℝ) * (Real.log ((D:ℝ) + 1)) ^ (127:ℕ) := by
  obtain ⟨C, hC, h⟩ := Commons.NumberTheory.DivisorSum.sum_tau_pow_le 7
  refine ⟨C, hC, fun D hD => ?_⟩
  have hle : ∀ d : ℕ,
      ((d.divisors.card : ℝ) ^ ((20:ℝ)/3)) ≤ ((d.divisors.card : ℝ)) ^ (7:ℕ) := by
    intro d
    rcases eq_or_ne d 0 with h0 | hd
    · subst h0; simp
    · have h1 : (1:ℝ) ≤ (d.divisors.card : ℝ) := by
        have : 0 < d.divisors.card := Finset.card_pos.mpr ⟨1, Nat.mem_divisors.mpr ⟨one_dvd d, hd⟩⟩
        exact_mod_cast this
      calc ((d.divisors.card : ℝ) ^ ((20:ℝ)/3)) ≤ ((d.divisors.card : ℝ)) ^ ((7:ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
        _ = ((d.divisors.card : ℝ)) ^ (7:ℕ) := Real.rpow_natCast _ 7
  calc (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ) ^ ((20:ℝ)/3)))
      ≤ ∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ)) ^ (7:ℕ) :=
        Finset.sum_le_sum (fun d _ => hle d)
    _ ≤ C * (D:ℝ) * (Real.log ((D:ℝ) + 1)) ^ (2^7 - 1) := h D hD
    _ = C * (D:ℝ) * (Real.log ((D:ℝ) + 1)) ^ (127:ℕ) := by norm_num

/-! ## Part B: the general-weight main-term aggregate -/

theorem sum_Md_weight_le {K C2 B2 : ℝ} (hK : 0 ≤ K) (hC2 : 0 ≤ C2)
    (hK2 : ∀ c D : ℕ, (∑ d ∈ Finset.Icc 1 D,
        ((d.divisors.card : ℝ) ^ K) * ((Submission.rho (c ^ 2) d : ℝ) / (d : ℝ)))
        ≤ C2 * (Real.log ((D : ℝ) + 2)) ^ B2) :
    ∃ C : ℝ, 0 < C ∧ ∀ t D : ℕ, 1 ≤ t → 1 ≤ D →
      (∑ d ∈ Finset.Icc 1 D,
        ((d.divisors.card : ℝ) ^ K) * ((Submission.Md d t : ℚ) : ℝ))
        ≤ C * (Submission.Aseq t : ℝ) * (Real.log ((D : ℝ) + 2)) ^ B2 := by
  refine ⟨4 * C2 + 1, by positivity, fun t D ht hD => ?_⟩
  have hlog0 : (0:ℝ) ≤ Real.log ((D:ℝ) + 2) := by
    apply Real.log_nonneg
    linarith [show (0:ℝ) ≤ (D:ℝ) by positivity]
  have hpw : (0:ℝ) ≤ (Real.log ((D:ℝ) + 2)) ^ B2 := Real.rpow_nonneg hlog0 _
  have hC2P : (0:ℝ) ≤ C2 * (Real.log ((D:ℝ) + 2)) ^ B2 := mul_nonneg hC2 hpw
  -- split each summand, then swap the root sum with the modulus sum
  have hsplit : (∑ d ∈ Finset.Icc 1 D,
        ((d.divisors.card : ℝ) ^ K) * ((Submission.Md d t : ℚ) : ℝ))
      = 2 * (∑ d ∈ Finset.Icc 1 D,
            ((d.divisors.card : ℝ) ^ K)
              * ((∑ c ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt t)),
                  (Submission.rho (c ^ 2) d : ℝ) * ((2 * Nat.sqrt (t - c ^ 4) + 1 : ℕ) : ℝ))
                    / (d : ℝ)))
        + 2 * (Nat.sqrt t : ℝ) * (∑ d ∈ Finset.Icc 1 D,
            ((d.divisors.card : ℝ) ^ K) * ((Submission.rho 0 d : ℝ) / (d : ℝ))) := by
    have hpt : ∀ d : ℕ,
        ((d.divisors.card : ℝ) ^ K) * ((Submission.Md d t : ℚ) : ℝ)
          = 2 * (((d.divisors.card : ℝ) ^ K)
                * ((∑ c ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt t)),
                    (Submission.rho (c ^ 2) d : ℝ) * ((2 * Nat.sqrt (t - c ^ 4) + 1 : ℕ) : ℝ))
                      / (d : ℝ)))
            + 2 * (Nat.sqrt t : ℝ) * (((d.divisors.card : ℝ) ^ K)
                * ((Submission.rho 0 d : ℝ) / (d : ℝ))) := by
      intro d
      rw [Md_eq_rho_sum d t]
      ring
    rw [Finset.sum_congr rfl (fun d _ => hpt d), Finset.sum_add_distrib,
      Finset.mul_sum, Finset.mul_sum]
  rw [hsplit]
  -- bound the two pieces
  have hQ : (∑ d ∈ Finset.Icc 1 D,
        ((d.divisors.card : ℝ) ^ K)
          * ((∑ c ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt t)),
              (Submission.rho (c ^ 2) d : ℝ) * ((2 * Nat.sqrt (t - c ^ 4) + 1 : ℕ) : ℝ))
                / (d : ℝ)))
      = ∑ c ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt t)),
          ((2 * Nat.sqrt (t - c ^ 4) + 1 : ℕ) : ℝ)
            * (∑ d ∈ Finset.Icc 1 D,
                ((d.divisors.card : ℝ) ^ K) * ((Submission.rho (c ^ 2) d : ℝ) / (d : ℝ))) :=
    sum_swap_density _ _ _ _ _ _
  have hQ0 : (∑ d ∈ Finset.Icc 1 D,
        ((d.divisors.card : ℝ) ^ K) * ((Submission.rho 0 d : ℝ) / (d : ℝ)))
      ≤ C2 * (Real.log ((D : ℝ) + 2)) ^ B2 := by
    simpa only [pow_two, mul_zero] using hK2 0 D
  have hQb : (∑ c ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt t)),
        ((2 * Nat.sqrt (t - c ^ 4) + 1 : ℕ) : ℝ)
          * (∑ d ∈ Finset.Icc 1 D,
              ((d.divisors.card : ℝ) ^ K) * ((Submission.rho (c ^ 2) d : ℝ) / (d : ℝ))))
      ≤ (C2 * (Real.log ((D : ℝ) + 2)) ^ B2)
          * (∑ c ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt t)),
              ((2 * Nat.sqrt (t - c ^ 4) + 1 : ℕ) : ℝ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun c _ => ?_
    have h1 : ((2 * Nat.sqrt (t - c ^ 4) + 1 : ℕ) : ℝ)
          * (∑ d ∈ Finset.Icc 1 D,
              ((d.divisors.card : ℝ) ^ K) * ((Submission.rho (c ^ 2) d : ℝ) / (d : ℝ)))
        ≤ ((2 * Nat.sqrt (t - c ^ 4) + 1 : ℕ) : ℝ)
          * (C2 * (Real.log ((D : ℝ) + 2)) ^ B2) :=
      mul_le_mul_of_nonneg_left (hK2 c D) (by positivity)
    calc ((2 * Nat.sqrt (t - c ^ 4) + 1 : ℕ) : ℝ)
          * (∑ d ∈ Finset.Icc 1 D,
              ((d.divisors.card : ℝ) ^ K) * ((Submission.rho (c ^ 2) d : ℝ) / (d : ℝ)))
        ≤ ((2 * Nat.sqrt (t - c ^ 4) + 1 : ℕ) : ℝ) * (C2 * (Real.log ((D : ℝ) + 2)) ^ B2) := h1
      _ = (C2 * (Real.log ((D : ℝ) + 2)) ^ B2)
          * ((2 * Nat.sqrt (t - c ^ 4) + 1 : ℕ) : ℝ) := by ring
  -- the `A`-comparison
  have hAc : ((Submission.Aseq t : ℕ) : ℝ)
      = 2 * (∑ c ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt t)),
              ((2 * Nat.sqrt (t - c ^ 4) + 1 : ℕ) : ℝ)) + (2 * (Nat.sqrt t : ℝ) + 1) := by
    have h := Commons.NumberTheory.FriedlanderIwaniec.Aseq_eq_sum_int_sqrt t
    simp only [Submission.Aseq, Submission.an] at h ⊢
    rw [h]; push_cast; ring
  have hS0 : (0:ℝ) ≤ ∑ c ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt t)),
      ((2 * Nat.sqrt (t - c ^ 4) + 1 : ℕ) : ℝ) := by positivity
  have hA0 : (0:ℝ) ≤ (Submission.Aseq t : ℝ) := by positivity
  have hSle : (∑ c ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt t)),
      ((2 * Nat.sqrt (t - c ^ 4) + 1 : ℕ) : ℝ)) ≤ (Submission.Aseq t : ℝ) := by
    linarith [hAc, hS0, show (0:ℝ) ≤ (Nat.sqrt t : ℝ) by positivity]
  have hst : 2 * (Nat.sqrt t : ℝ) ≤ (Submission.Aseq t : ℝ) := by
    linarith [hAc, hS0, show (0:ℝ) ≤ (Nat.sqrt t : ℝ) by positivity]
  calc 2 * (∑ d ∈ Finset.Icc 1 D,
          ((d.divisors.card : ℝ) ^ K)
            * ((∑ c ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt t)),
                (Submission.rho (c ^ 2) d : ℝ) * ((2 * Nat.sqrt (t - c ^ 4) + 1 : ℕ) : ℝ))
                  / (d : ℝ)))
        + 2 * (Nat.sqrt t : ℝ) * (∑ d ∈ Finset.Icc 1 D,
          ((d.divisors.card : ℝ) ^ K) * ((Submission.rho 0 d : ℝ) / (d : ℝ)))
      = 2 * (∑ c ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt t)),
            ((2 * Nat.sqrt (t - c ^ 4) + 1 : ℕ) : ℝ)
              * (∑ d ∈ Finset.Icc 1 D,
                  ((d.divisors.card : ℝ) ^ K) * ((Submission.rho (c ^ 2) d : ℝ) / (d : ℝ))))
        + 2 * (Nat.sqrt t : ℝ) * (∑ d ∈ Finset.Icc 1 D,
          ((d.divisors.card : ℝ) ^ K) * ((Submission.rho 0 d : ℝ) / (d : ℝ))) := by
        rw [hQ]
    _ ≤ 2 * ((C2 * (Real.log ((D : ℝ) + 2)) ^ B2)
          * (∑ c ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt t)),
              ((2 * Nat.sqrt (t - c ^ 4) + 1 : ℕ) : ℝ)))
        + 2 * (Nat.sqrt t : ℝ) * (C2 * (Real.log ((D : ℝ) + 2)) ^ B2) :=
        add_le_add (mul_le_mul_of_nonneg_left hQb (by norm_num))
          (mul_le_mul_of_nonneg_left hQ0 (by positivity))
    _ ≤ (4 * C2 + 1) * (Submission.Aseq t : ℝ) * (Real.log ((D : ℝ) + 2)) ^ B2 := by
        have h1 : 2 * ((C2 * (Real.log ((D : ℝ) + 2)) ^ B2)
              * (∑ c ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt t)),
                  ((2 * Nat.sqrt (t - c ^ 4) + 1 : ℕ) : ℝ)))
            ≤ 2 * ((C2 * (Real.log ((D : ℝ) + 2)) ^ B2) * (Submission.Aseq t : ℝ)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hSle hC2P) (by norm_num)
        have h2 : 2 * (Nat.sqrt t : ℝ) * (C2 * (Real.log ((D : ℝ) + 2)) ^ B2)
            ≤ (C2 * (Real.log ((D : ℝ) + 2)) ^ B2) * (Submission.Aseq t : ℝ) := by
          calc 2 * (Nat.sqrt t : ℝ) * (C2 * (Real.log ((D : ℝ) + 2)) ^ B2)
              = (2 * (Nat.sqrt t : ℝ)) * (C2 * (Real.log ((D : ℝ) + 2)) ^ B2) := by ring
            _ ≤ (Submission.Aseq t : ℝ) * (C2 * (Real.log ((D : ℝ) + 2)) ^ B2) :=
                mul_le_mul_of_nonneg_right hst hC2P
            _ = (C2 * (Real.log ((D : ℝ) + 2)) ^ B2) * (Submission.Aseq t : ℝ) := by ring
        have h3 : (0:ℝ) ≤ 3 * C2 + 1 := by linarith
        have h4 : 2 * ((C2 * (Real.log ((D : ℝ) + 2)) ^ B2) * (Submission.Aseq t : ℝ))
              + (C2 * (Real.log ((D : ℝ) + 2)) ^ B2) * (Submission.Aseq t : ℝ)
            = (3 * C2) * (Real.log ((D : ℝ) + 2)) ^ B2 * (Submission.Aseq t : ℝ) := by ring
        have h5 : (3 * C2) * (Real.log ((D : ℝ) + 2)) ^ B2 * (Submission.Aseq t : ℝ)
            ≤ (4 * C2 + 1) * (Submission.Aseq t : ℝ) * (Real.log ((D : ℝ) + 2)) ^ B2 := by
          have h6 : (3 * C2) ≤ (4 * C2 + 1) := by linarith
          calc (3 * C2) * (Real.log ((D : ℝ) + 2)) ^ B2 * (Submission.Aseq t : ℝ)
              = (3 * C2) * ((Real.log ((D : ℝ) + 2)) ^ B2 * (Submission.Aseq t : ℝ)) := by ring
            _ ≤ (4 * C2 + 1) * ((Real.log ((D : ℝ) + 2)) ^ B2 * (Submission.Aseq t : ℝ)) :=
                mul_le_mul_of_nonneg_right h6 (by positivity)
            _ = (4 * C2 + 1) * (Submission.Aseq t : ℝ) * (Real.log ((D : ℝ) + 2)) ^ B2 := by ring
        linarith [h1, h2, h4.le, h4.ge, h5]

/-! ## Part C: the weighted `(3.3)` on the cube range -/

/-- **The `(2τ)^{40}`-weighted `(3.3)` on the cube range.**  For `t ≥ 8` the weighted sum of
`|A_d(t) − M_d(t)|` over the moduli `d ≤ ⌊t^{1/3}⌋` is `≪ t^{11/16}`: the pointwise
`τ(d)^{40} ≪ t^{40·(1/1000)/3} = t^{1/75}` costs only `t^{1/75}`, and the unweighted `(3.3)` at the
cut-off `t^{1/3}` contributes `t^{1/12+9/16+1/100}`. -/
theorem weighted_Ad_sub_Md_cube_le :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℕ, 8 ≤ t →
      (∑ d ∈ Finset.Icc 1 ⌊(t:ℝ)^((1:ℝ)/3)⌋₊,
        ((2 * (d.divisors.card : ℝ)) ^ (40:ℝ))
          * |(Submission.Ad d t : ℝ) - ((Submission.Md d t : ℚ) : ℝ)|)
        ≤ C * (t:ℝ)^((11:ℝ)/16) := by
  obtain ⟨C33, hC33, h33⟩ := Submission.Ad_sub_Md_sum_le
  obtain ⟨Cτ, hCτ, hτ⟩ :=
    Commons.NumberTheory.DivisorBound.card_divisors_le_rpow (1/1000 : ℝ) (by norm_num)
  refine ⟨2^40 * Cτ^40 * C33, by positivity, fun t ht => ?_⟩
  set D' : ℕ := ⌊(t:ℝ)^((1:ℝ)/3)⌋₊ with hD'def
  have ht1 : (1:ℝ) ≤ (t:ℝ) := by exact_mod_cast (by omega : 1 ≤ t)
  have htpos : (0:ℝ) < (t:ℝ) := by linarith
  have hD'1 : 1 ≤ D' := by
    rw [hD'def, Nat.one_le_floor_iff]
    exact Real.one_le_rpow ht1 (by norm_num)
  have hD'le : (D':ℝ) ≤ (t:ℝ)^((1:ℝ)/3) := by
    rw [hD'def]; exact Nat.floor_le (Real.rpow_nonneg (le_of_lt htpos) _)
  have hD'le34 : (D':ℝ) ≤ (t:ℝ)^((3:ℝ)/4) :=
    le_trans hD'le (Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num))
  have h33t : D' ≤ ⌊(t:ℝ)^((3:ℝ)/4)⌋₊ := Nat.le_floor hD'le34
  -- pointwise weight bound
  have hpt : ∀ d ∈ Finset.Icc 1 D',
      ((2 * (d.divisors.card : ℝ)) ^ (40:ℝ))
        ≤ 2^40 * Cτ^40 * (t:ℝ)^((1:ℝ)/75) := by
    intro d hd
    have hdD : d ≤ D' := (Finset.mem_Icc.mp hd).2
    have hdr : ((d:ℝ)) ≤ (t:ℝ)^((1:ℝ)/3) := le_trans (by exact_mod_cast hdD) hD'le
    have hτd : ((d.divisors.card : ℝ)) ≤ Cτ * (d:ℝ)^((1:ℝ)/1000) := hτ d
    have h1 : ((2 * (d.divisors.card : ℝ)) ^ (40:ℝ))
        = (2:ℝ)^(40:ℝ) * ((d.divisors.card : ℝ))^(40:ℝ) :=
      Real.mul_rpow (by norm_num) (by positivity)
    have h2 : ((d.divisors.card : ℝ))^(40:ℝ)
        ≤ (Cτ * (d:ℝ)^((1:ℝ)/1000))^(40:ℝ) :=
      Real.rpow_le_rpow (by positivity) hτd (by norm_num)
    have h3 : (Cτ * (d:ℝ)^((1:ℝ)/1000))^(40:ℝ)
        = Cτ^(40:ℝ) * (d:ℝ)^((1:ℝ)/25) := by
      rw [Real.mul_rpow hCτ.le (Real.rpow_nonneg (by positivity) _),
        ← Real.rpow_mul (by positivity : (0:ℝ) ≤ (d:ℝ))]
      norm_num
    have h4 : (d:ℝ)^((1:ℝ)/25) ≤ (t:ℝ)^((1:ℝ)/75) := by
      have h5 : ((d:ℝ))^((1:ℝ)/25) ≤ ((t:ℝ)^((1:ℝ)/3))^((1:ℝ)/25) :=
        Real.rpow_le_rpow (by positivity) hdr (by norm_num)
      have h6 : ((t:ℝ)^((1:ℝ)/3))^((1:ℝ)/25) = (t:ℝ)^((1:ℝ)/75) := by
        rw [← Real.rpow_mul (le_of_lt htpos)]
        norm_num
      linarith [h5, h6.le, h6.ge]
    have h5 : (2:ℝ)^(40:ℝ) = 2^40 := Real.rpow_natCast _ 40
    have h6 : Cτ^(40:ℝ) = Cτ^40 := Real.rpow_natCast _ 40
    calc ((2 * (d.divisors.card : ℝ)) ^ (40:ℝ))
        = (2:ℝ)^(40:ℝ) * ((d.divisors.card : ℝ))^(40:ℝ) := h1
      _ ≤ (2:ℝ)^(40:ℝ) * (Cτ^(40:ℝ) * (d:ℝ)^((1:ℝ)/25)) := by
          rw [h3] at h2
          exact mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = ((2:ℝ)^(40:ℝ) * Cτ^(40:ℝ)) * (d:ℝ)^((1:ℝ)/25) := by ring
      _ ≤ ((2:ℝ)^(40:ℝ) * Cτ^(40:ℝ)) * (t:ℝ)^((1:ℝ)/75) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = 2^40 * Cτ^40 * (t:ℝ)^((1:ℝ)/75) := by rw [h5, h6]
  -- the sum
  have hsum33 : (∑ d ∈ Finset.Icc 1 D',
        |(Submission.Ad d t : ℝ) - ((Submission.Md d t : ℚ) : ℝ)|)
      ≤ C33 * (D':ℝ)^((1:ℝ)/4) * (t:ℝ)^((9:ℝ)/16 + 1/100) :=
    h33 t D' (by omega) hD'1 h33t
  calc (∑ d ∈ Finset.Icc 1 D',
        ((2 * (d.divisors.card : ℝ)) ^ (40:ℝ))
          * |(Submission.Ad d t : ℝ) - ((Submission.Md d t : ℚ) : ℝ)|)
      ≤ ∑ d ∈ Finset.Icc 1 D',
          (2^40 * Cτ^40 * (t:ℝ)^((1:ℝ)/75))
            * |(Submission.Ad d t : ℝ) - ((Submission.Md d t : ℚ) : ℝ)| :=
        Finset.sum_le_sum (fun d hd =>
          mul_le_mul_of_nonneg_right (hpt d hd) (abs_nonneg _))
    _ = (2^40 * Cτ^40 * (t:ℝ)^((1:ℝ)/75))
          * (∑ d ∈ Finset.Icc 1 D',
              |(Submission.Ad d t : ℝ) - ((Submission.Md d t : ℚ) : ℝ)|) := by
        rw [Finset.mul_sum]
    _ ≤ (2^40 * Cτ^40 * (t:ℝ)^((1:ℝ)/75))
          * (C33 * (D':ℝ)^((1:ℝ)/4) * (t:ℝ)^((9:ℝ)/16 + 1/100)) :=
        mul_le_mul_of_nonneg_left hsum33 (by positivity)
    _ ≤ (2^40 * Cτ^40 * C33) * (t:ℝ)^((11:ℝ)/16) := by
        have hD14 : (D':ℝ)^((1:ℝ)/4) ≤ (t:ℝ)^((1:ℝ)/12) := by
          have h5 : (D':ℝ)^((1:ℝ)/4) ≤ ((t:ℝ)^((1:ℝ)/3))^((1:ℝ)/4) :=
            Real.rpow_le_rpow (by positivity) hD'le (by norm_num)
          have h6 : ((t:ℝ)^((1:ℝ)/3))^((1:ℝ)/4) = (t:ℝ)^((1:ℝ)/12) := by
            rw [← Real.rpow_mul (le_of_lt htpos)]; norm_num
          rw [← h6]; exact h5
        have hexp : (1:ℝ)/75 + ((1:ℝ)/12 + ((9:ℝ)/16 + 1/100)) ≤ (11:ℝ)/16 := by norm_num
        have hmain : (t:ℝ)^((1:ℝ)/75) * ((t:ℝ)^((1:ℝ)/12) * (t:ℝ)^((9:ℝ)/16 + 1/100))
            ≤ (t:ℝ)^((11:ℝ)/16) := by
          rw [← Real.rpow_add htpos, ← Real.rpow_add htpos]
          exact Real.rpow_le_rpow_of_exponent_le ht1 hexp
        have hC : (0:ℝ) < 2^40 * Cτ^40 * C33 := by positivity
        calc (2^40 * Cτ^40 * (t:ℝ)^((1:ℝ)/75))
              * (C33 * (D':ℝ)^((1:ℝ)/4) * (t:ℝ)^((9:ℝ)/16 + 1/100))
            ≤ (2^40 * Cτ^40 * (t:ℝ)^((1:ℝ)/75))
              * (C33 * (t:ℝ)^((1:ℝ)/12) * (t:ℝ)^((9:ℝ)/16 + 1/100)) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hD14 hC33.le) (by positivity)
          _ = (2^40 * Cτ^40 * C33)
              * ((t:ℝ)^((1:ℝ)/75) * ((t:ℝ)^((1:ℝ)/12) * (t:ℝ)^((9:ℝ)/16 + 1/100))) := by
              ring
          _ ≤ (2^40 * Cτ^40 * C33) * (t:ℝ)^((11:ℝ)/16) :=
              mul_le_mul_of_nonneg_left hmain hC.le

/-! ## Part D: the cube-range aggregate `∑_{d³ ≤ t} (2τ(d))^{40} A_d(t) ≪ A(x)(log x)^B` -/

/-- `Submission.Aseq` is monotone. -/
private lemma Aseq_mono_local : Monotone Submission.Aseq := by
  intro m n hmn
  unfold Submission.Aseq
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (fun k hk => by rw [Finset.mem_range] at hk ⊢; omega) (fun i _ _ => Nat.zero_le _)

/-- `(log a)^B ≤ max 1 ((log 2)^B)·(log b)^{max B 0}` for `2 ≤ a ≤ b`. -/
private lemma log_rpow_le_max {a b B : ℝ} (h2a : 2 ≤ a) (hab : a ≤ b) :
    (Real.log a)^B ≤ max 1 ((Real.log 2)^B) * (Real.log b)^(max B 0) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hloga : Real.log 2 ≤ Real.log a := Real.log_le_log (by norm_num) h2a
  have hlogapos : 0 < Real.log a := lt_of_lt_of_le hlog2 hloga
  have halt : Real.log a ≤ Real.log b := Real.log_le_log (by linarith) hab
  have hlogbpos : 0 ≤ Real.log b := le_trans (le_trans (le_of_lt hlog2) hloga) halt
  by_cases hB : B ≤ 0
  · have h1 : (Real.log a)^B ≤ (Real.log 2)^B := Real.rpow_le_rpow_of_nonpos hlog2 hloga hB
    rw [max_eq_right hB, Real.rpow_zero, mul_one]
    exact le_trans h1 (le_max_right _ _)
  · push_neg at hB
    have h1 : (Real.log a)^B ≤ (Real.log b)^B :=
      Real.rpow_le_rpow (le_of_lt hlogapos) halt hB.le
    rw [max_eq_left hB.le]
    calc (Real.log a)^B ≤ (Real.log b)^B := h1
      _ = 1 * (Real.log b)^B := by ring
      _ ≤ max 1 ((Real.log 2)^B) * (Real.log b)^B :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hlogbpos _)

/-- **The cube-range aggregate for `X² + Y⁴`.**  For all `2 ≤ t ≤ x`,

  `∑_{d³ ≤ t} (2τ(d))^{40} A_d(t) ≪ A(x)(log x)^B`,

uniformly in `t`.  Proof: `A_d(t) ≤ |A_d(t) − M_d(t)| + M_d(t)`; the error part is the weighted
`(3.3)` of Part C (at the cut-off `t^{1/3}`), and the main part is the general-weight aggregate
`sum_Md_weight_le` at weight `K = 40`, fed by the commons `sum_tau_pow_rho_div_le_general`. -/
theorem cube_range_Ad_le :
    ∃ C B X₀ : ℝ, 0 < C ∧ ∀ x : ℕ, X₀ ≤ x → ∀ t : ℕ, 2 ≤ t → t ≤ x →
      (∑ d ∈ (Finset.Icc 1 t).filter (fun d => d^3 ≤ t),
        ((2 * (d.divisors.card : ℝ)) ^ (40:ℝ)) * (Submission.Ad d t : ℝ))
        ≤ C * (Submission.Aseq x : ℝ) * (Real.log x)^B := by
  obtain ⟨Cw, hCw, hw⟩ := weighted_Ad_sub_Md_cube_le
  obtain ⟨C2, B2, hC2, hK2⟩ :=
    Commons.NumberTheory.FriedlanderIwaniec.sum_tau_pow_rho_div_le_general 40 (by norm_num)
  obtain ⟨CM, hCM, hM⟩ := sum_Md_weight_le (K := 40) (by norm_num) hC2.le hK2
  obtain ⟨cA, hcA, XA, hAlow⟩ :=
    Commons.NumberTheory.FriedlanderIwaniec.X2Y4_Aseq_ge_const_mul_rpow
  set Bk : ℝ := max B2 0 with hBkdef
  set Q : ℝ := max 1 ((Real.log 2)^B2) with hQdef
  set Kc : ℝ := Cw * (1/cA) + 16 * (2:ℝ)^40 * CM * Q * (2:ℝ)^Bk + 16 * (2:ℝ)^40 with hKcdef
  have hQpos : (0:ℝ) < Q := by rw [hQdef]; positivity
  have hQ1 : (1:ℝ) ≤ Q := by rw [hQdef]; exact le_max_left _ _
  have hBk0 : (0:ℝ) ≤ Bk := by rw [hBkdef]; exact le_max_right _ _
  have hKcCw : Cw * (1/cA) ≤ Kc := by
    rw [hKcdef]
    linarith [show (0:ℝ) ≤ 16 * (2:ℝ)^40 * CM * Q * (2:ℝ)^Bk + 16 * (2:ℝ)^40 by positivity]
  have hKc16 : 16 * (2:ℝ)^40 * CM * Q * (2:ℝ)^Bk ≤ Kc := by
    rw [hKcdef]
    linarith [show (0:ℝ) ≤ Cw * (1/cA) + 16 * (2:ℝ)^40 by positivity]
  have hKc16b : (2:ℝ)^40 ≤ Kc := by
    rw [hKcdef]
    have h1 : (0:ℝ) ≤ Cw * (1/cA) + 16 * (2:ℝ)^40 * CM * Q * (2:ℝ)^Bk := by positivity
    have h2 : (2:ℝ)^40 ≤ 16 * (2:ℝ)^40 := by nlinarith [show (0:ℝ) < (2:ℝ)^40 by positivity]
    linarith
  have hKc1 : (1:ℝ) ≤ Kc := by
    have h3 : (1:ℝ) ≤ (2:ℝ)^40 := one_le_pow₀ (by norm_num)
    linarith [hKc16b]
  refine ⟨Kc, Bk, max (XA : ℝ) 8, lt_of_lt_of_le one_pos hKc1, fun x hx t ht2 htx => ?_⟩
  have hx8 : 8 ≤ x := by
    have : (8:ℝ) ≤ (x:ℝ) := le_trans (le_max_right (XA:ℝ) 8) hx
    exact_mod_cast this
  have hx3 : 3 ≤ x := by omega
  have hx1 : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
  have hxpos : (0:ℝ) < (x:ℝ) := by linarith
  have hlog1 : (1:ℝ) ≤ Real.log (x:ℝ) := by
    rw [← Real.log_exp 1]
    refine Real.log_le_log (Real.exp_pos 1) ?_
    have h3 : (3:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx3
    linarith [Real.exp_one_lt_d9]
  have hlogBk1 : (1:ℝ) ≤ (Real.log (x:ℝ))^Bk := Real.one_le_rpow hlog1 hBk0
  have hlogBk0 : (0:ℝ) ≤ (Real.log (x:ℝ))^Bk := le_trans zero_le_one hlogBk1
  have hA0 : (0:ℝ) ≤ (Submission.Aseq x : ℝ) := by positivity
  have hAseq : (Submission.Aseq t : ℝ) ≤ (Submission.Aseq x : ℝ) :=
    Nat.cast_le.mpr (Aseq_mono_local htx)
  rcases lt_or_ge t 8 with hsmall | hbig
  · -- small `t`: only `d = 1` survives
    have hsub1 : (Finset.Icc 1 t).filter (fun d => d^3 ≤ t) ⊆ ({1} : Finset ℕ) := by
      intro d hd
      rw [Finset.mem_filter, Finset.mem_Icc] at hd
      obtain ⟨⟨hd1, -⟩, hd3⟩ := hd
      simp only [Finset.mem_singleton]
      by_contra hne
      have h2 : 2 ≤ d := by omega
      have h3 : 8 ≤ d^3 := by simpa using Nat.pow_le_pow_left h2 3
      omega
    have hAd1 : Submission.Ad 1 t = Submission.Aseq t := by
      rw [Submission.Ad, Submission.Aseq, Finset.filter_true_of_mem (fun n _ => one_dvd n)]
    have hsum_le : (∑ d ∈ (Finset.Icc 1 t).filter (fun d => d^3 ≤ t),
          ((2 * (d.divisors.card : ℝ)) ^ (40:ℝ)) * (Submission.Ad d t : ℝ))
        ≤ (2:ℝ)^40 * (Submission.Aseq x : ℝ) := by
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub1 (fun i _ _ => by positivity)) ?_
      rw [Finset.sum_singleton]
      have h2 : ((2 * ((1:ℕ).divisors.card : ℝ)) ^ (40:ℝ)) = (2:ℝ)^40 := by
        rw [show ((1:ℕ).divisors.card : ℝ) = 1 by simp]
        rw [show ((2 * (1:ℝ)) : ℝ) = 2 by norm_num]
        exact Real.rpow_natCast _ 40
      rw [h2, hAd1]
      exact mul_le_mul_of_nonneg_left hAseq (by positivity)
    calc (∑ d ∈ (Finset.Icc 1 t).filter (fun d => d^3 ≤ t),
          ((2 * (d.divisors.card : ℝ)) ^ (40:ℝ)) * (Submission.Ad d t : ℝ))
        ≤ (2:ℝ)^40 * (Submission.Aseq x : ℝ) := hsum_le
      _ ≤ Kc * (Submission.Aseq x : ℝ) * (Real.log (x:ℝ))^Bk := by
          have h6 : (0:ℝ) ≤ Kc * (Submission.Aseq x : ℝ) :=
            mul_nonneg (le_trans zero_le_one hKc1) hA0
          have h7 : Kc * (Submission.Aseq x : ℝ) ≤ Kc * (Submission.Aseq x : ℝ) * (Real.log (x:ℝ))^Bk :=
            le_mul_of_one_le_right h6 hlogBk1
          linarith [mul_le_mul_of_nonneg_right hKc16b hA0, h7]
  · -- main case
    set D3 : ℕ := ⌊(t:ℝ)^((1:ℝ)/3)⌋₊ with hD3def
    have ht1 : (1:ℝ) ≤ (t:ℝ) := by exact_mod_cast (by omega : 1 ≤ t)
    have htpos : (0:ℝ) < (t:ℝ) := by linarith
    have hsub : (Finset.Icc 1 t).filter (fun d => d^3 ≤ t) ⊆ Finset.Icc 1 D3 := by
      intro d hd
      rw [Finset.mem_filter, Finset.mem_Icc] at hd
      obtain ⟨⟨hd1, -⟩, hd3⟩ := hd
      rw [Finset.mem_Icc]
      refine ⟨hd1, ?_⟩
      rw [hD3def]
      refine Nat.le_floor ?_
      have hdr : ((d:ℝ))^3 ≤ (t:ℝ) := by exact_mod_cast hd3
      have hdpos : (0:ℝ) ≤ (d:ℝ) := by positivity
      have h1 : ((d:ℝ)) = (((d:ℝ))^3)^((1:ℝ)/3) := by
        rw [show ((d:ℝ))^3 = ((d:ℝ))^(3:ℝ) from (Real.rpow_natCast _ 3).symm,
          ← Real.rpow_mul hdpos]
        rw [show (3:ℝ) * (1/3 : ℝ) = 1 by norm_num, Real.rpow_one]
      rw [h1]
      exact Real.rpow_le_rpow (by positivity) hdr (by norm_num)
    have hMd0 : ∀ d : ℕ, (0:ℝ) ≤ ((Submission.Md d t : ℚ) : ℝ) := by
      intro d
      rw [Submission.Md]; push_cast; positivity
    -- the split `A_d ≤ |A_d − M_d| + M_d`
    have hsplit : (∑ d ∈ Finset.Icc 1 D3,
          ((2 * (d.divisors.card : ℝ)) ^ (40:ℝ)) * (Submission.Ad d t : ℝ))
        ≤ (∑ d ∈ Finset.Icc 1 D3,
              ((2 * (d.divisors.card : ℝ)) ^ (40:ℝ))
                * |(Submission.Ad d t : ℝ) - ((Submission.Md d t : ℚ) : ℝ)|)
          + (∑ d ∈ Finset.Icc 1 D3,
              ((2 * (d.divisors.card : ℝ)) ^ (40:ℝ)) * ((Submission.Md d t : ℚ) : ℝ)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun d _ => ?_
      have hw0 : (0:ℝ) ≤ ((2 * (d.divisors.card : ℝ)) ^ (40:ℝ)) :=
        Real.rpow_nonneg (by positivity) _
      have h1 : (Submission.Ad d t : ℝ)
          ≤ |(Submission.Ad d t : ℝ) - ((Submission.Md d t : ℚ) : ℝ)|
            + ((Submission.Md d t : ℚ) : ℝ) := by
        have h := le_abs_self ((Submission.Ad d t : ℝ) - ((Submission.Md d t : ℚ) : ℝ))
        linarith [h, hMd0 d]
      calc ((2 * (d.divisors.card : ℝ)) ^ (40:ℝ)) * (Submission.Ad d t : ℝ)
          ≤ ((2 * (d.divisors.card : ℝ)) ^ (40:ℝ))
              * (|(Submission.Ad d t : ℝ) - ((Submission.Md d t : ℚ) : ℝ)|
                + ((Submission.Md d t : ℚ) : ℝ)) := mul_le_mul_of_nonneg_left h1 hw0
        _ = ((2 * (d.divisors.card : ℝ)) ^ (40:ℝ))
                * |(Submission.Ad d t : ℝ) - ((Submission.Md d t : ℚ) : ℝ)|
            + ((2 * (d.divisors.card : ℝ)) ^ (40:ℝ)) * ((Submission.Md d t : ℚ) : ℝ) := by ring
    have herr : (∑ d ∈ Finset.Icc 1 D3,
          ((2 * (d.divisors.card : ℝ)) ^ (40:ℝ))
            * |(Submission.Ad d t : ℝ) - ((Submission.Md d t : ℚ) : ℝ)|)
        ≤ Cw * (t:ℝ)^((11:ℝ)/16) := hw t (by omega)
    have hmain : (∑ d ∈ Finset.Icc 1 D3,
          ((2 * (d.divisors.card : ℝ)) ^ (40:ℝ)) * ((Submission.Md d t : ℚ) : ℝ))
        ≤ (2:ℝ)^40 * (CM * (Submission.Aseq t : ℝ) * (Real.log ((D3:ℝ) + 2))^B2) := by
      have h2 : ∀ d : ℕ, ((2 * (d.divisors.card : ℝ)) ^ (40:ℝ))
          = (2:ℝ)^40 * ((d.divisors.card : ℝ))^(40:ℝ) := by
        intro d
        have h2a : (2:ℝ)^(40:ℝ) = (2:ℝ)^40 := Real.rpow_natCast _ 40
        rw [Real.mul_rpow (by norm_num) (by positivity), h2a]
      rw [show (∑ d ∈ Finset.Icc 1 D3,
              ((2 * (d.divisors.card : ℝ)) ^ (40:ℝ)) * ((Submission.Md d t : ℚ) : ℝ))
          = (2:ℝ)^40 * ∑ d ∈ Finset.Icc 1 D3,
              ((d.divisors.card : ℝ))^(40:ℝ) * ((Submission.Md d t : ℚ) : ℝ) from by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun d _ => by rw [h2 d]; ring)]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have hD31 : 1 ≤ D3 := by
        rw [hD3def, Nat.one_le_floor_iff]
        exact Real.one_le_rpow ht1 (by norm_num)
      exact hM t D3 (by omega) hD31
    have hTK0 : (∑ d ∈ Finset.Icc 1 D3,
          ((2 * (d.divisors.card : ℝ)) ^ (40:ℝ)) * (Submission.Ad d t : ℝ))
        ≤ Cw * (t:ℝ)^((11:ℝ)/16)
          + (2:ℝ)^40 * (CM * (Submission.Aseq t : ℝ) * (Real.log ((D3:ℝ) + 2))^B2) :=
      le_trans hsplit (add_le_add herr hmain)
    have hTK : (∑ d ∈ (Finset.Icc 1 t).filter (fun d => d^3 ≤ t),
          ((2 * (d.divisors.card : ℝ)) ^ (40:ℝ)) * (Submission.Ad d t : ℝ))
        ≤ Cw * (t:ℝ)^((11:ℝ)/16)
          + (2:ℝ)^40 * (CM * (Submission.Aseq t : ℝ) * (Real.log ((D3:ℝ) + 2))^B2) :=
      le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)) hTK0
    -- conversions
    have ht11 : (t:ℝ)^((11:ℝ)/16) ≤ (1/cA) * (Submission.Aseq x : ℝ) := by
      have h1 : cA * (x:ℝ)^((3:ℝ)/4) ≤ (Submission.Aseq x : ℝ) := by
        apply hAlow x
        have : (XA:ℝ) ≤ (x:ℝ) := le_trans (le_max_left _ _) hx
        exact_mod_cast this
      have h2 : (t:ℝ)^((11:ℝ)/16) ≤ (x:ℝ)^((11:ℝ)/16) :=
        Real.rpow_le_rpow (by positivity) (by exact_mod_cast htx) (by norm_num)
      have h3 : (x:ℝ)^((11:ℝ)/16) ≤ (x:ℝ)^((3:ℝ)/4) :=
        Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
      have h4 : cA * (x:ℝ)^((11:ℝ)/16) ≤ (Submission.Aseq x : ℝ) :=
        le_trans (mul_le_mul_of_nonneg_left h3 hcA.le) h1
      have h5 : (x:ℝ)^((11:ℝ)/16) ≤ (cA)⁻¹ * (Submission.Aseq x : ℝ) :=
        (le_inv_mul_iff₀ hcA).mpr h4
      have h6 : (x:ℝ)^((11:ℝ)/16) ≤ (1/cA) * (Submission.Aseq x : ℝ) := by
        simpa only [one_div] using h5
      exact le_trans h2 h6
    have hx3r : (3:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx3
    have hD3x : (D3:ℝ) + 2 ≤ (x:ℝ)^2 := by
      have hD3le : (D3:ℝ) ≤ (t:ℝ)^((1:ℝ)/3) := by
        rw [hD3def]; exact Nat.floor_le (Real.rpow_nonneg (le_of_lt htpos) _)
      have h1 : (t:ℝ)^((1:ℝ)/3) ≤ (t:ℝ) := by
        calc (t:ℝ)^((1:ℝ)/3) ≤ (t:ℝ)^(1:ℝ) :=
              Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num)
          _ = (t:ℝ) := Real.rpow_one _
      have h2 : (t:ℝ) ≤ (x:ℝ) := by exact_mod_cast htx
      have hxx : (x:ℝ) + 2 ≤ (x:ℝ)^2 := by nlinarith [hx3r]
      linarith [hD3le, h1, h2, hxx]
    have hlogD : (Real.log ((D3:ℝ) + 2))^B2 ≤ Q * (2 * Real.log (x:ℝ))^Bk := by
      have h2le : (2:ℝ) ≤ (D3:ℝ) + 2 := by
        have : (0:ℝ) ≤ (D3:ℝ) := by positivity
        linarith
      have h := log_rpow_le_max (B := B2) h2le hD3x
      have hlogx2 : Real.log ((x:ℝ)^2) = 2 * Real.log (x:ℝ) := by
        rw [Real.log_pow]; push_cast; ring
      rw [← hQdef, ← hBkdef, hlogx2] at h
      exact h
    have hlogx : (2 * Real.log (x:ℝ))^Bk = (2:ℝ)^Bk * (Real.log (x:ℝ))^Bk :=
      Real.mul_rpow (by norm_num) (le_trans zero_le_one hlog1)
    have hlogDnn : (0:ℝ) ≤ (Real.log ((D3:ℝ) + 2))^B2 := by
      have h2le : (2:ℝ) ≤ (D3:ℝ) + 2 := by
        have : (0:ℝ) ≤ (D3:ℝ) := by positivity
        linarith
      exact Real.rpow_nonneg (le_trans (Real.log_pos (by norm_num)).le
        (Real.log_le_log (by norm_num) h2le)) _
    -- the two pieces
    have e1 : Cw * (t:ℝ)^((11:ℝ)/16)
        ≤ (Cw * (1/cA)) * (Submission.Aseq x : ℝ) * (Real.log (x:ℝ))^Bk := by
      have h1 : Cw * (t:ℝ)^((11:ℝ)/16) ≤ (Cw * (1/cA)) * (Submission.Aseq x : ℝ) := by
        calc Cw * (t:ℝ)^((11:ℝ)/16) ≤ Cw * ((1/cA) * (Submission.Aseq x : ℝ)) :=
              mul_le_mul_of_nonneg_left ht11 hCw.le
          _ = (Cw * (1/cA)) * (Submission.Aseq x : ℝ) := by ring
      have h2 : (0:ℝ) ≤ (Cw * (1/cA)) * (Submission.Aseq x : ℝ) :=
        mul_nonneg (by positivity) hA0
      calc Cw * (t:ℝ)^((11:ℝ)/16) ≤ (Cw * (1/cA)) * (Submission.Aseq x : ℝ) := h1
        _ ≤ (Cw * (1/cA)) * (Submission.Aseq x : ℝ) * (Real.log (x:ℝ))^Bk :=
            le_mul_of_one_le_right h2 hlogBk1
    have e2 : (2:ℝ)^40 * (CM * (Submission.Aseq t : ℝ) * (Real.log ((D3:ℝ) + 2))^B2)
        ≤ (16 * (2:ℝ)^40 * CM * Q * (2:ℝ)^Bk) * (Submission.Aseq x : ℝ)
            * (Real.log (x:ℝ))^Bk := by
      have h1 : CM * (Submission.Aseq t : ℝ) * (Real.log ((D3:ℝ) + 2))^B2
          ≤ CM * (Submission.Aseq x : ℝ) * (Q * (2 * Real.log (x:ℝ))^Bk) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hAseq hCM.le) hlogD hlogDnn
          (mul_nonneg hCM.le hA0)
      have h6 : (0:ℝ) < (2:ℝ)^40 * CM * Q * (2:ℝ)^Bk := by positivity
      have h7 : (2:ℝ)^40 * CM * Q * (2:ℝ)^Bk ≤ 16 * ((2:ℝ)^40 * CM * Q * (2:ℝ)^Bk) :=
        le_mul_of_one_le_left h6.le (by norm_num)
      have h9 : (0:ℝ) ≤ (Submission.Aseq x : ℝ) * (Real.log (x:ℝ))^Bk := mul_nonneg hA0 hlogBk0
      calc (2:ℝ)^40 * (CM * (Submission.Aseq t : ℝ) * (Real.log ((D3:ℝ) + 2))^B2)
          ≤ (2:ℝ)^40 * (CM * (Submission.Aseq x : ℝ) * (Q * (2 * Real.log (x:ℝ))^Bk)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = ((2:ℝ)^40 * CM * Q * (2:ℝ)^Bk)
              * ((Submission.Aseq x : ℝ) * (Real.log (x:ℝ))^Bk) := by
            rw [hlogx]; ring
        _ ≤ (16 * (2:ℝ)^40 * CM * Q * (2:ℝ)^Bk)
              * ((Submission.Aseq x : ℝ) * (Real.log (x:ℝ))^Bk) := by
            refine mul_le_mul_of_nonneg_right ?_ h9
            calc (2:ℝ)^40 * CM * Q * (2:ℝ)^Bk ≤ 16 * ((2:ℝ)^40 * CM * Q * (2:ℝ)^Bk) := h7
              _ = 16 * (2:ℝ)^40 * CM * Q * (2:ℝ)^Bk := by ring
        _ = (16 * (2:ℝ)^40 * CM * Q * (2:ℝ)^Bk) * (Submission.Aseq x : ℝ)
              * (Real.log (x:ℝ))^Bk := by ring
    have hc : Cw * (1/cA) + 16 * (2:ℝ)^40 * CM * Q * (2:ℝ)^Bk ≤ Kc := by
      rw [hKcdef]
      linarith [show (0:ℝ) ≤ 16 * (2:ℝ)^40 by positivity]
    calc (∑ d ∈ (Finset.Icc 1 t).filter (fun d => d^3 ≤ t),
          ((2 * (d.divisors.card : ℝ)) ^ (40:ℝ)) * (Submission.Ad d t : ℝ))
        ≤ Cw * (t:ℝ)^((11:ℝ)/16)
          + (2:ℝ)^40 * (CM * (Submission.Aseq t : ℝ) * (Real.log ((D3:ℝ) + 2))^B2) := hTK
      _ ≤ (Cw * (1/cA)) * (Submission.Aseq x : ℝ) * (Real.log (x:ℝ))^Bk
            + (16 * (2:ℝ)^40 * CM * Q * (2:ℝ)^Bk) * (Submission.Aseq x : ℝ)
                * (Real.log (x:ℝ))^Bk := add_le_add e1 e2
      _ = (Cw * (1/cA) + 16 * (2:ℝ)^40 * CM * Q * (2:ℝ)^Bk)
            * (Submission.Aseq x : ℝ) * (Real.log (x:ℝ))^Bk := by ring
      _ ≤ Kc * (Submission.Aseq x : ℝ) * (Real.log (x:ℝ))^Bk :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hA0) hlogBk0

/-! ## Part E: the final `τ^{20/3}`-weighted aggregate `(2.3)` for all `D ≤ x^{3/4}` -/

/-- **The `τ^{20/3}`-weighted `(2.3)` for `X² + Y⁴`, uniformly in `D ≤ x^{3/4}` and `2 ≤ t ≤ x`:**

  `∑_{d ≤ D, ♭} τ(d)^{20/3} |A_d(t) − g(d)A(t)| ≤ C·A(x)(log x)^B`,

where `A = Submission.Aseq` is normalised at the *global* `x`.  This is the second input of the
Hölder step that produces the companion's hypothesis `(R′)` for the sequence. -/
theorem X2Y4_tau_pow_remainder_all :
    ∃ C B X₀ : ℝ, 0 < C ∧ ∀ x : ℕ, X₀ ≤ x → ∀ t : ℕ, 2 ≤ t → t ≤ x → ∀ D : ℕ,
      (D:ℝ) ≤ (x:ℝ)^((3:ℝ)/4) →
      (∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
        ((d.divisors.card : ℝ) ^ ((20:ℝ)/3))
          * |(Submission.Ad d t : ℝ) - (Submission.gdens d : ℝ) * (Submission.Aseq t : ℝ)|)
        ≤ C * (Submission.Aseq x : ℝ) * (Real.log x)^B := by
  obtain ⟨C2, B2, X2, hC2, hcube⟩ := cube_range_Ad_le
  obtain ⟨CS, hCS, hSig⟩ := sum_tau_pow_twenty_third_le
  obtain ⟨Cg, hCg, Kg, hKg0, hg⟩ := sum_sqfree_tau_pow_gdens_le
  obtain ⟨cA, hcA, XA, hAlow⟩ :=
    Commons.NumberTheory.FriedlanderIwaniec.X2Y4_Aseq_ge_const_mul_rpow
  set B2k : ℝ := max B2 0 with hB2kdef
  set Kgk : ℝ := max Kg 0 with hKgkdef
  set B : ℝ := 127 + B2k + Kgk with hBdef
  set C : ℝ := ((Submission.an 0 : ℝ) + 1) * CS * (1/cA) * (2:ℝ)^(127:ℝ)
      + C2 * max 1 ((Real.log 2)^B2)
      + Cg * max 1 ((Real.log 2)^Kg) * (2:ℝ)^B with hCdef
  have hB2k0 : (0:ℝ) ≤ B2k := by rw [hB2kdef]; exact le_max_right _ _
  have hKgk0 : (0:ℝ) ≤ Kgk := by rw [hKgkdef]; exact le_max_right _ _
  have hB0 : (0:ℝ) ≤ B := by rw [hBdef]; linarith
  have hB127 : (127:ℝ) ≤ B := by rw [hBdef]; linarith
  have hB2k_le : B2k ≤ B := by rw [hBdef]; linarith
  have hKgk_le : Kgk ≤ B := by rw [hBdef]; linarith
  have hCpos : (0:ℝ) < C := by
    rw [hCdef]
    have h1 : (0:ℝ) < ((Submission.an 0 : ℝ) + 1) * CS * (1/cA) * (2:ℝ)^(127:ℝ) := by positivity
    have h2 : (0:ℝ) < C2 * max 1 ((Real.log 2)^B2) := by positivity
    have h3 : (0:ℝ) < Cg * max 1 ((Real.log 2)^Kg) * (2:ℝ)^B := by positivity
    linarith
  refine ⟨C, B, max (max (XA:ℝ) X2) 8, hCpos, fun x hx t ht2 htx D hD34 => ?_⟩
  have hxX2 : X2 ≤ (x:ℝ) := le_trans (le_max_right (XA:ℝ) X2) (le_trans (le_max_left _ _) hx)
  have hxXA : XA ≤ x := by
    have h : (XA:ℝ) ≤ (x:ℝ) := le_trans (le_max_left (XA:ℝ) X2) (le_trans (le_max_left _ _) hx)
    exact_mod_cast h
  have hx8 : 8 ≤ x := by
    have h : (8:ℝ) ≤ (x:ℝ) := le_trans (le_max_right (max (XA:ℝ) X2) 8) hx
    exact_mod_cast h
  have hx1 : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
  have hx2 : (2:ℝ) ≤ (x:ℝ) := by exact_mod_cast (by omega : 2 ≤ x)
  have hxpos : (0:ℝ) < (x:ℝ) := by linarith
  have hlog1 : (1:ℝ) ≤ Real.log (x:ℝ) := by
    rw [← Real.log_exp 1]
    refine Real.log_le_log (Real.exp_pos 1) ?_
    have h3 : (3:ℝ) ≤ (x:ℝ) := by exact_mod_cast (by omega : 3 ≤ x)
    linarith [Real.exp_one_lt_d9]
  have hlogpos : (0:ℝ) < Real.log (x:ℝ) := lt_of_lt_of_le one_pos hlog1
  have hA0 : (0:ℝ) ≤ (Submission.Aseq x : ℝ) := by positivity
  have hAseq : (Submission.Aseq t : ℝ) ≤ (Submission.Aseq x : ℝ) :=
    Nat.cast_le.mpr (Aseq_mono_local htx)
  rcases Nat.eq_zero_or_pos D with hD0 | hDpos
  · subst hD0
    rw [Finset.Icc_eq_empty_of_lt (by norm_num : 0 < 1), Finset.filter_empty, Finset.sum_empty]
    positivity
  · have hD1r : (1:ℝ) ≤ (D:ℝ) := by exact_mod_cast hDpos
    have hD_le_x : (D:ℝ) ≤ (x:ℝ) := by
      refine le_trans hD34 ?_
      calc (x:ℝ)^((3:ℝ)/4) ≤ (x:ℝ)^(1:ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
        _ = (x:ℝ) := Real.rpow_one _
    have hDseq : (D:ℝ) ≤ (1/cA) * (Submission.Aseq x : ℝ) := by
      have h1 : cA * (x:ℝ)^((3:ℝ)/4) ≤ (Submission.Aseq x : ℝ) := hAlow x hxXA
      have h3 : cA * (D:ℝ) ≤ (Submission.Aseq x : ℝ) :=
        le_trans (mul_le_mul_of_nonneg_left hD34 hcA.le) h1
      have h4 : (D:ℝ) ≤ (cA)⁻¹ * (Submission.Aseq x : ℝ) := (le_inv_mul_iff₀ hcA).mpr h3
      simpa only [one_div] using h4
    -- notation
    set L : ℝ := (Real.log (x:ℝ))^B with hLdef
    have hL1 : (1:ℝ) ≤ L := by rw [hLdef]; exact Real.one_le_rpow hlog1 hB0
    have hL0 : (0:ℝ) ≤ L := le_trans zero_le_one hL1
    -- `(log x)^e ≤ L` for every `0 ≤ e ≤ B`
    have hlogmono : ∀ e : ℝ, 0 ≤ e → e ≤ B → (Real.log (x:ℝ))^e ≤ L := by
      intro e _ he
      rw [hLdef]
      exact Real.rpow_le_rpow_of_exponent_le hlog1 he
    have hgdens0 : ∀ d : ℕ, (0:ℝ) ≤ (Submission.gdens d : ℝ) := by
      intro d
      rw [Submission.gdens]
      push_cast
      exact div_nonneg (by positivity) (sq_nonneg _)
    -- step 1: triangle inequality and the extension of the modulus range
    have hstep1 : (∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
          ((d.divisors.card : ℝ) ^ ((20:ℝ)/3))
            * |(Submission.Ad d t : ℝ) - (Submission.gdens d : ℝ) * (Submission.Aseq t : ℝ)|)
        ≤ (∑ d ∈ Finset.Icc 1 D,
              ((d.divisors.card : ℝ) ^ ((20:ℝ)/3)) * (Submission.Ad d t : ℝ))
          + (∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
              ((d.divisors.card : ℝ) ^ ((20:ℝ)/3)) * (Submission.gdens d : ℝ))
              * (Submission.Aseq t : ℝ) := by
      have hpt : ∀ d ∈ (Finset.Icc 1 D).filter Squarefree,
          ((d.divisors.card : ℝ) ^ ((20:ℝ)/3))
            * |(Submission.Ad d t : ℝ) - (Submission.gdens d : ℝ) * (Submission.Aseq t : ℝ)|
          ≤ ((d.divisors.card : ℝ) ^ ((20:ℝ)/3)) * (Submission.Ad d t : ℝ)
            + ((d.divisors.card : ℝ) ^ ((20:ℝ)/3)) * (Submission.gdens d : ℝ)
                * (Submission.Aseq t : ℝ) := by
        intro d _
        have hc0 : (0:ℝ) ≤ ((d.divisors.card : ℝ) ^ ((20:ℝ)/3)) :=
          Real.rpow_nonneg (by positivity) _
        have hb : |(Submission.Ad d t : ℝ) - (Submission.gdens d : ℝ) * (Submission.Aseq t : ℝ)|
            ≤ (Submission.Ad d t : ℝ) + (Submission.gdens d : ℝ) * (Submission.Aseq t : ℝ) := by
          have h := abs_sub ((Submission.Ad d t : ℝ)) ((Submission.gdens d : ℝ) * (Submission.Aseq t : ℝ))
          rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ (Submission.Ad d t : ℝ)),
            abs_of_nonneg (mul_nonneg (hgdens0 d) (by positivity))] at h
          linarith
        calc ((d.divisors.card : ℝ) ^ ((20:ℝ)/3))
              * |(Submission.Ad d t : ℝ) - (Submission.gdens d : ℝ) * (Submission.Aseq t : ℝ)|
            ≤ ((d.divisors.card : ℝ) ^ ((20:ℝ)/3))
              * ((Submission.Ad d t : ℝ) + (Submission.gdens d : ℝ) * (Submission.Aseq t : ℝ)) :=
              mul_le_mul_of_nonneg_left hb hc0
          _ = ((d.divisors.card : ℝ) ^ ((20:ℝ)/3)) * (Submission.Ad d t : ℝ)
              + ((d.divisors.card : ℝ) ^ ((20:ℝ)/3)) * (Submission.gdens d : ℝ)
                  * (Submission.Aseq t : ℝ) := by ring
      calc (∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
            ((d.divisors.card : ℝ) ^ ((20:ℝ)/3))
              * |(Submission.Ad d t : ℝ) - (Submission.gdens d : ℝ) * (Submission.Aseq t : ℝ)|)
          ≤ ∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
              (((d.divisors.card : ℝ) ^ ((20:ℝ)/3)) * (Submission.Ad d t : ℝ)
                + ((d.divisors.card : ℝ) ^ ((20:ℝ)/3)) * (Submission.gdens d : ℝ)
                    * (Submission.Aseq t : ℝ)) := Finset.sum_le_sum hpt
        _ = (∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
                ((d.divisors.card : ℝ) ^ ((20:ℝ)/3)) * (Submission.Ad d t : ℝ))
              + (∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
                ((d.divisors.card : ℝ) ^ ((20:ℝ)/3)) * (Submission.gdens d : ℝ))
                * (Submission.Aseq t : ℝ) := by
            rw [Finset.sum_add_distrib, Finset.sum_mul]
        _ ≤ (∑ d ∈ Finset.Icc 1 D,
                ((d.divisors.card : ℝ) ^ ((20:ℝ)/3)) * (Submission.Ad d t : ℝ))
              + (∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
                ((d.divisors.card : ℝ) ^ ((20:ℝ)/3)) * (Submission.gdens d : ℝ))
                * (Submission.Aseq t : ℝ) := by
            refine add_le_add ?_ le_rfl
            exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun i _ _ => mul_nonneg (Real.rpow_nonneg (by positivity) _) (by positivity))
    -- step 2: the `τ^8`-reduction (from `S24`) and the cube-range aggregate
    have hcubeAd : (∑ d ∈ (Finset.Icc 1 t).filter (fun d => d ^ 3 ≤ t),
          (2 * (d.divisors.card : ℝ)) ^ ((40:ℕ):ℝ) * (Submission.Ad d t : ℝ))
        ≤ C2 * (Submission.Aseq x : ℝ) * (Real.log x)^B2 := hcube x hxX2 t ht2 htx
    have hinner : ∀ d : ℕ, (∑ n ∈ (Finset.Icc 1 t).filter (fun n => d ∣ n),
            (Submission.an n : ℝ))
        ≤ (Submission.Ad d t : ℝ) := by
      intro d
      have hsub : (Finset.Icc 1 t).filter (fun n => d ∣ n)
          ⊆ (Finset.range (t + 1)).filter (fun n => d ∣ n) := by
        intro n hn
        rw [Finset.mem_filter, Finset.mem_Icc] at hn
        rw [Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hn.2⟩
      have h1 : (∑ n ∈ (Finset.Icc 1 t).filter (fun n => d ∣ n), (Submission.an n : ℝ))
          ≤ ∑ n ∈ (Finset.range (t + 1)).filter (fun n => d ∣ n), (Submission.an n : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
      rw [Submission.Ad]
      push_cast
      exact h1
    have hred : (∑ d ∈ Finset.Icc 1 D,
            ((d.divisors.card : ℝ) ^ ((20:ℝ)/3)) * (Submission.Ad d t : ℝ))
        ≤ (Submission.an 0 : ℝ) * (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ) ^ ((20:ℝ)/3)))
          + C2 * (Submission.Aseq x : ℝ) * (Real.log x)^B2 := by
      refine le_trans (sum_tau_pow_Ad_le_cube D t) (add_le_add le_rfl ?_)
      refine le_trans (Finset.sum_le_sum (fun d _ =>
        mul_le_mul_of_nonneg_left (hinner d) (by positivity))) hcubeAd
    -- step 3: the `Σ_D` piece
    have hSig : (Submission.an 0 : ℝ) * (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ) ^ ((20:ℝ)/3)))
        ≤ ((Submission.an 0 : ℝ) * CS * (1/cA) * (2:ℝ)^(127:ℝ))
            * (Submission.Aseq x : ℝ) * L := by
      have hs := hSig D hDpos
      have hDlog : (Real.log ((D:ℝ) + 1))^(127:ℕ) ≤ 2^(127:ℕ) * L := by
        have h1 : (Real.log ((D:ℝ) + 1))^(127:ℕ) ≤ (Real.log ((x:ℝ) + 1))^(127:ℕ) :=
          pow_le_pow_left₀ (Real.log_nonneg (by linarith))
            (Real.log_le_log (by linarith) (by linarith)) 127
        have h2 : Real.log ((x:ℝ) + 1) ≤ 2 * Real.log (x:ℝ) := by
          have h3 : (x:ℝ) + 1 ≤ (x:ℝ)^2 := by nlinarith [hx2]
          have h4 : Real.log ((x:ℝ)+1) ≤ Real.log ((x:ℝ)^2) := Real.log_le_log (by linarith) h3
          have h5 : Real.log ((x:ℝ)^2) = 2 * Real.log (x:ℝ) := by
            rw [Real.log_pow]; push_cast; ring
          linarith [h4, h5.le, h5.ge]
        have h3 : (Real.log ((x:ℝ) + 1))^(127:ℕ) ≤ (2 * Real.log (x:ℝ))^(127:ℕ) :=
          pow_le_pow_left₀ (Real.log_nonneg (by linarith)) h2 127
        have h4 : (2 * Real.log (x:ℝ))^(127:ℕ) = 2^(127:ℕ) * (Real.log (x:ℝ))^(127:ℕ) :=
          mul_pow 2 (Real.log (x:ℝ)) 127
        have h5 : (Real.log (x:ℝ))^(127:ℕ) = (Real.log (x:ℝ))^((127:ℝ)) :=
          (Real.rpow_natCast _ 127).symm
        have h6 : (Real.log (x:ℝ))^((127:ℝ)) ≤ L := hlogmono 127 (by norm_num) hB127
        calc (Real.log ((D:ℝ) + 1))^(127:ℕ) ≤ (Real.log ((x:ℝ) + 1))^(127:ℕ) := h1
          _ ≤ (2 * Real.log (x:ℝ))^(127:ℕ) := h3
          _ = 2^(127:ℕ) * (Real.log (x:ℝ))^(127:ℕ) := h4
          _ = 2^(127:ℕ) * (Real.log (x:ℝ))^((127:ℝ)) := by rw [h5]
          _ ≤ 2^(127:ℕ) * L := mul_le_mul_of_nonneg_left h6 (by positivity)
      have han0 : (0:ℝ) ≤ (Submission.an 0 : ℝ) := by positivity
      have hkey : (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ) ^ ((20:ℝ)/3)))
          ≤ CS * (D:ℝ) * (2^(127:ℕ) * L) := by
        refine le_trans hs ?_
        exact mul_le_mul_of_nonneg_left hDlog (by positivity)
      calc (Submission.an 0 : ℝ) * (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ) ^ ((20:ℝ)/3)))
          ≤ (Submission.an 0 : ℝ) * (CS * (D:ℝ) * (2^(127:ℕ) * L)) :=
            mul_le_mul_of_nonneg_left hkey han0
        _ ≤ (Submission.an 0 : ℝ) * (CS * ((1/cA) * (Submission.Aseq x : ℝ)) * (2^(127:ℕ) * L)) := by
            refine mul_le_mul_of_nonneg_left ?_ han0
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hDseq (by positivity)) (by positivity)
        _ = ((Submission.an 0 : ℝ) * CS * (1/cA) * (2:ℝ)^(127:ℝ))
              * (Submission.Aseq x : ℝ) * L := by
            rw [show (2:ℝ)^(127:ℕ) = (2:ℝ)^(127:ℝ) from (Real.rpow_natCast _ 127).symm]
            ring
    -- step 4: the density piece
    have hgdens : (∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
            ((d.divisors.card : ℝ) ^ ((20:ℝ)/3)) * (Submission.gdens d : ℝ))
          * (Submission.Aseq t : ℝ)
        ≤ (Cg * max 1 ((Real.log 2)^Kg) * (2:ℝ)^B) * (Submission.Aseq x : ℝ) * L := by
      have hsub : (Finset.Icc 1 D).filter Squarefree
          ⊆ (Finset.Icc 1 (max D 2)).filter Squarefree := by
        intro d hd
        rw [Finset.mem_filter, Finset.mem_Icc] at hd
        rw [Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨hd.1.1, le_trans hd.1.2 (le_max_left _ _)⟩, hd.2⟩
      have h1 : (∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
            ((d.divisors.card : ℝ) ^ ((20:ℝ)/3)) * (Submission.gdens d : ℝ))
          ≤ Cg * (Real.log (((max D 2 : ℕ) : ℝ) + 2))^Kg :=
        le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun i _ _ => mul_nonneg (Real.rpow_nonneg (by positivity) _) (hgdens0 i)))
          (hg (max D 2) (le_max_right D 2))
      have hmaxD : (max D 2 : ℕ) ≤ x := by
        have hxx : D ≤ x := by
          have : (D:ℝ) ≤ (x:ℝ) := hD_le_x
          exact_mod_cast this
        exact max_le hxx (by omega)
      have h4 : Real.log (2 * (x:ℝ)) ≤ 2 * Real.log (x:ℝ) := by
        rw [Real.log_mul (by norm_num) hxpos.ne']
        linarith [Real.log_le_log (by norm_num) hx2]
      have h5 : (Real.log (2 * (x:ℝ)))^Kgk ≤ (2 * Real.log (x:ℝ))^Kgk :=
        Real.rpow_le_rpow (Real.log_nonneg (by linarith)) h4 hKgk0
      have h7 : (2 * Real.log (x:ℝ))^Kgk ≤ (2:ℝ)^B * L := by
        have h8 : (2 * Real.log (x:ℝ))^Kgk = (2:ℝ)^Kgk * (Real.log (x:ℝ))^Kgk :=
          Real.mul_rpow (by norm_num) hlogpos.le
        rw [h8]
        have h9 : (Real.log (x:ℝ))^Kgk ≤ L := hlogmono Kgk hKgk0 hKgk_le
        have h10 : (2:ℝ)^Kgk ≤ (2:ℝ)^B := Real.rpow_le_rpow_of_exponent_le (by norm_num) hKgk_le
        exact mul_le_mul h10 h9 (Real.rpow_nonneg hlogpos.le _) (Real.rpow_nonneg (by norm_num) _)
      have h3 : (Real.log (((max D 2 : ℕ) : ℝ) + 2))^Kg
          ≤ max 1 ((Real.log 2)^Kg) * ((2:ℝ)^B * L) := by
        have hbase : ((max D 2 : ℕ) : ℝ) + 2 ≤ 2 * (x:ℝ) := by
          have : ((max D 2 : ℕ) : ℝ) ≤ (x:ℝ) := by exact_mod_cast hmaxD
          linarith
        have ha := log_rpow_le_max (B := Kg) (a := ((max D 2 : ℕ) : ℝ) + 2) (b := 2 * (x:ℝ))
          (by linarith [show (0:ℝ) ≤ ((max D 2 : ℕ) : ℝ) by positivity]) hbase
        have hQ : (0:ℝ) ≤ max 1 ((Real.log 2)^Kg) := le_trans zero_le_one (le_max_left _ _)
        have hac : (Real.log (((max D 2 : ℕ) : ℝ) + 2))^Kg ≤ max 1 ((Real.log 2)^Kg) * (Real.log (2 * (x:ℝ)))^Kgk := ha
        have hbd : max 1 ((Real.log 2)^Kg) * (Real.log (2 * (x:ℝ)))^Kgk ≤ max 1 ((Real.log 2)^Kg) * ((2:ℝ)^B * L) := mul_le_mul_of_nonneg_left (le_trans h5 h7) hQ
        exact le_trans hac hbd
      have hAseq0 : (0:ℝ) ≤ (Submission.Aseq t : ℝ) := by positivity
      have hP1 : (∑ d ∈ (Finset.Icc 1 D).filter Squarefree, ((d.divisors.card : ℝ) ^ ((20:ℝ)/3)) * (Submission.gdens d : ℝ)) * (Submission.Aseq t : ℝ)
          ≤ (Cg * (Real.log (((max D 2 : ℕ) : ℝ) + 2))^Kg) * (Submission.Aseq t : ℝ) := mul_le_mul_of_nonneg_right h1 hAseq0
      have hP2 : (Cg * (Real.log (((max D 2 : ℕ) : ℝ) + 2))^Kg) * (Submission.Aseq t : ℝ)
          ≤ (Cg * (max 1 ((Real.log 2)^Kg) * ((2:ℝ)^B * L))) * (Submission.Aseq t : ℝ) := by
        refine mul_le_mul_of_nonneg_right ?_ hAseq0
        exact mul_le_mul_of_nonneg_left h3 hCg.le
      have hP3 : (Cg * (max 1 ((Real.log 2)^Kg) * ((2:ℝ)^B * L))) * (Submission.Aseq t : ℝ)
          ≤ (Cg * (max 1 ((Real.log 2)^Kg) * ((2:ℝ)^B * L))) * (Submission.Aseq x : ℝ) :=
        mul_le_mul_of_nonneg_left hAseq (by positivity)
      have hP4 : (Cg * (max 1 ((Real.log 2)^Kg) * ((2:ℝ)^B * L))) * (Submission.Aseq x : ℝ)
          = (Cg * max 1 ((Real.log 2)^Kg) * (2:ℝ)^B) * (Submission.Aseq x : ℝ) * L := by ring
      exact le_trans hP1 (le_trans hP2 (le_trans hP3 (le_of_eq hP4)))
    -- step 5: assemble
    have hfinal : (∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
          ((d.divisors.card : ℝ) ^ ((20:ℝ)/3))
            * |(Submission.Ad d t : ℝ) - (Submission.gdens d : ℝ) * (Submission.Aseq t : ℝ)|)
        ≤ ((Submission.an 0 : ℝ) * CS * (1/cA) * (2:ℝ)^(127:ℝ)) * (Submission.Aseq x : ℝ) * L
          + (C2 * max 1 ((Real.log 2)^B2)) * (Submission.Aseq x : ℝ) * L
          + (Cg * max 1 ((Real.log 2)^Kg) * (2:ℝ)^B) * (Submission.Aseq x : ℝ) * L := by
      have h2 : C2 * (Submission.Aseq x : ℝ) * (Real.log x)^B2
          ≤ (C2 * max 1 ((Real.log 2)^B2)) * (Submission.Aseq x : ℝ) * L := by
        have h3 : (Real.log (x:ℝ))^B2 ≤ max 1 ((Real.log 2)^B2) * L := by
          have ha := log_rpow_le_max (B := B2) (a := (x:ℝ)) (b := (x:ℝ)) hx2 le_rfl
          have hb : (Real.log (x:ℝ))^B2k ≤ L := hlogmono B2k hB2k0 hB2k_le
          exact le_trans ha
            (mul_le_mul_of_nonneg_left hb (le_trans zero_le_one (le_max_left _ _)))
        have hQp : (0:ℝ) ≤ max 1 ((Real.log 2)^B2) :=
          le_trans zero_le_one (le_max_left _ _)
        have hc1 : C2 * (Submission.Aseq x : ℝ) * (Real.log x)^B2
            ≤ C2 * (Submission.Aseq x : ℝ) * (max 1 ((Real.log 2)^B2) * L) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
        have hc2 : C2 * (Submission.Aseq x : ℝ) * (max 1 ((Real.log 2)^B2) * L)
            = (C2 * max 1 ((Real.log 2)^B2)) * (Submission.Aseq x : ℝ) * L := by ring
        exact le_trans hc1 (le_of_eq hc2)
      linarith [hstep1, hred, hSig, hgdens, h2]
    -- step 6: the constant bookkeeping
    have hCge1 : ((Submission.an 0 : ℝ) * CS * (1/cA) * (2:ℝ)^(127:ℝ))
        ≤ ((Submission.an 0 : ℝ) + 1) * CS * (1/cA) * (2:ℝ)^(127:ℝ) := by
      have han0 : (0:ℝ) ≤ (Submission.an 0 : ℝ) := by positivity
      have hpos : (0:ℝ) ≤ CS * (1/cA) * (2:ℝ)^(127:ℝ) := by positivity
      nlinarith [han0, hpos]
    have hCge : ((Submission.an 0 : ℝ) * CS * (1/cA) * (2:ℝ)^(127:ℝ))
          + C2 * max 1 ((Real.log 2)^B2) + Cg * max 1 ((Real.log 2)^Kg) * (2:ℝ)^B ≤ C := by
      rw [hCdef]; linarith [hCge1]
    have hAxL : (0:ℝ) ≤ (Submission.Aseq x : ℝ) * L := mul_nonneg hA0 hL0
    calc (∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
          ((d.divisors.card : ℝ) ^ ((20:ℝ)/3))
            * |(Submission.Ad d t : ℝ) - (Submission.gdens d : ℝ) * (Submission.Aseq t : ℝ)|)
        ≤ ((Submission.an 0 : ℝ) * CS * (1/cA) * (2:ℝ)^(127:ℝ)) * (Submission.Aseq x : ℝ) * L
          + (C2 * max 1 ((Real.log 2)^B2)) * (Submission.Aseq x : ℝ) * L
          + (Cg * max 1 ((Real.log 2)^Kg) * (2:ℝ)^B) * (Submission.Aseq x : ℝ) * L := hfinal
      _ = (((Submission.an 0 : ℝ) * CS * (1/cA) * (2:ℝ)^(127:ℝ))
            + C2 * max 1 ((Real.log 2)^B2) + Cg * max 1 ((Real.log 2)^Kg) * (2:ℝ)^B)
            * (Submission.Aseq x : ℝ) * L := by ring
      _ ≤ C * (Submission.Aseq x : ℝ) * L :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCge hA0) hL0
      _ = C * (Submission.Aseq x : ℝ) * (Real.log x)^B := by rw [hLdef]

/-! ## Part F: `(R′)` for `X² + Y⁴` (the companion's second remainder hypothesis) -/

/-- **(R′) for the Friedlander–Iwaniec sequence.**  At the cut-off `D = ⌊x^{11/16}⌋` one has

  `∑_{d ≤ D, ♭} τ(d)^5 |A_d(t) − g(d)A(t)| ≤ A(x)(log x)^{-3}`

for every `2 ≤ t ≤ x`.  Proof: Hölder's inequality `τ^5 = (τ^{20/3})^{3/4}·(τ^0)^{1/4}` applied to
the `τ^{20/3}`-weighted `(2.3)` of Part E and to the hypothesis `(R)` (`Rsum ≤ A(x)(log x)^{-λ}`
with `λ = 3·max B₂ 0 + 100`, which the *power-saving* proof of `(R)` provides for every `λ > 0`). -/
theorem X2Y4_Rprime :
    ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → ∀ t : ℕ, 2 ≤ t → t ≤ x →
      (∑ d ∈ (Finset.Icc 1 (Submission.Rcut x)).filter Squarefree,
        ((d.divisors.card : ℝ))^5
          * |(Submission.Ad d t : ℝ) - (Submission.gdens d : ℝ) * (Submission.Aseq t : ℝ)|)
        ≤ (Submission.Aseq x : ℝ) * (Real.log x)^(-(4:ℝ)) := by
  obtain ⟨C2, B2, X2, hC2, h23all⟩ := X2Y4_tau_pow_remainder_all
  set B2k : ℝ := max B2 0 with hB2kdef
  set lam : ℝ := 3 * B2k + 100 with hlamdef
  have hlam0 : 0 < lam := by rw [hlamdef]; linarith [le_max_right B2 0]
  obtain ⟨Xr, hRall⟩ := Submission.X2Y4_R_generic lam hlam0
  set Nc : ℕ := ⌈Real.exp (max 2 (C2 ^ ((3:ℝ)/4) + 1))⌉₊ + 1 with hNcdef
  set X2n : ℕ := ⌈X2⌉₊ + 1 with hX2ndef
  refine ⟨max (max (max X2n Xr) Nc) 8, fun x hx t ht2 htx => ?_⟩
  have hxX2n : X2n ≤ x :=
    le_trans (le_trans (le_trans (le_max_left X2n Xr) (le_max_left (max X2n Xr) Nc))
      (le_max_left (max (max X2n Xr) Nc) 8)) hx
  have hxX2 : X2 ≤ (x:ℝ) := by
    have h1 : ((X2n:ℕ):ℝ) ≤ (x:ℝ) := by exact_mod_cast hxX2n
    have h2 : X2 ≤ ((X2n:ℕ):ℝ) := by
      rw [hX2ndef]; push_cast; linarith [Nat.le_ceil X2]
    linarith
  have hxXr : Xr ≤ x :=
    le_trans (le_trans (le_max_right X2n Xr) (le_max_left (max X2n Xr) Nc))
      (le_trans (le_max_left (max (max X2n Xr) Nc) 8) hx)
  have hxNc : Nc ≤ x :=
    le_trans (le_trans (le_max_right (max X2n Xr) Nc) (le_max_left (max (max X2n Xr) Nc) 8)) hx
  have hx8 : 8 ≤ x := le_trans (le_max_right (max (max X2n Xr) Nc) 8) hx
  have hx1 : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
  have hxpos : (0:ℝ) < (x:ℝ) := by linarith
  have hxexp : Real.exp (max 2 (C2 ^ ((3:ℝ)/4) + 1)) ≤ (x:ℝ) := by
    have hb : ⌈Real.exp (max 2 (C2 ^ ((3:ℝ)/4) + 1))⌉₊ ≤ x := by
      rw [hNcdef] at hxNc; omega
    have h2 : Real.exp (max 2 (C2 ^ ((3:ℝ)/4) + 1))
        ≤ ((⌈Real.exp (max 2 (C2 ^ ((3:ℝ)/4) + 1))⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    exact le_trans h2 (by exact_mod_cast hb)
  have hlogbig : C2 ^ ((3:ℝ)/4) + 1 ≤ Real.log (x:ℝ) := by
    have h1 : max 2 (C2 ^ ((3:ℝ)/4) + 1) ≤ Real.log (x:ℝ) := by
      rw [← Real.log_exp (max 2 (C2 ^ ((3:ℝ)/4) + 1))]
      exact Real.log_le_log (Real.exp_pos _) hxexp
    linarith [le_max_right (2:ℝ) (C2 ^ ((3:ℝ)/4) + 1)]
  have hlog1 : (1:ℝ) ≤ Real.log (x:ℝ) := by
    have h1 : (0:ℝ) ≤ C2 ^ ((3:ℝ)/4) := Real.rpow_nonneg hC2.le _
    linarith [hlogbig, h1]
  have hlog0 : (0:ℝ) ≤ Real.log (x:ℝ) := le_trans zero_le_one hlog1
  have hlogpos : (0:ℝ) < Real.log (x:ℝ) := lt_of_lt_of_le one_pos hlog1
  set L : ℝ := Real.log (x:ℝ) with hLdef
  have hL0 : (0:ℝ) ≤ L := by rw [hLdef]; exact hlog0
  have hL1 : (1:ℝ) ≤ L := by rw [hLdef]; exact hlog1
  have hLpos : (0:ℝ) < L := lt_of_lt_of_le one_pos hL1
  have hA0 : (0:ℝ) ≤ (Submission.Aseq x : ℝ) := by positivity
  have hC2pow : C2 ^ ((3:ℝ)/4) ≤ L ^ (21:ℝ) := by
    have h3 : C2 ^ ((3:ℝ)/4) ≤ L := by rw [hLdef]; linarith
    have h4 : L^(1:ℝ) ≤ L^(21:ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    rw [Real.rpow_one] at h4
    linarith
  have hRcut34 : (Submission.Rcut x : ℝ) ≤ (x:ℝ)^((3:ℝ)/4) :=
    le_trans (Submission.Rcut_le_rpow x)
      (Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : ((11:ℝ)/16) ≤ 3/4))
  -- the two hypotheses
  have hU : (∑ d ∈ (Finset.Icc 1 (Submission.Rcut x)).filter Squarefree,
        ((d.divisors.card : ℝ)) ^ ((20:ℝ)/3)
          * |(Submission.Ad d t : ℝ) - (Submission.gdens d : ℝ) * (Submission.Aseq t : ℝ)|)
      ≤ C2 * (Submission.Aseq x : ℝ) * L^B2 := by
    rw [hLdef]
    exact h23all x hxX2 t ht2 htx (Submission.Rcut x) hRcut34
  have hV : (∑ d ∈ (Finset.Icc 1 (Submission.Rcut x)).filter Squarefree,
        |(Submission.Ad d t : ℝ) - (Submission.gdens d : ℝ) * (Submission.Aseq t : ℝ)|)
      ≤ (Submission.Aseq x : ℝ) * L^(-lam) := by
    rw [hLdef]
    exact hRall x hxXr t ht2 htx
  -- Hölder
  have hholder := Commons.Analysis.MeanInequalities.sum_rpow_holder
    (F := fun d : ℕ => ((d.divisors.card : ℝ)))
    (R := fun d : ℕ => if Squarefree d
      then |(Submission.Ad d t : ℝ) - (Submission.gdens d : ℝ) * (Submission.Aseq t : ℝ)| else 0)
    (fun d => by positivity) (fun d => by positivity) (Submission.Rcut x)
  have hLs : (∑ d ∈ (Finset.Icc 1 (Submission.Rcut x)).filter Squarefree,
        ((d.divisors.card : ℝ)) ^ 5
          * |(Submission.Ad d t : ℝ) - (Submission.gdens d : ℝ) * (Submission.Aseq t : ℝ)|)
      = ∑ d ∈ Finset.Icc 1 (Submission.Rcut x),
          ((d.divisors.card : ℝ)) ^ 5 * (if Squarefree d
            then |(Submission.Ad d t : ℝ) - (Submission.gdens d : ℝ) * (Submission.Aseq t : ℝ)|
            else 0) := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl (fun d _ => by by_cases h : Squarefree d <;> simp [h])
  have hUs : (∑ d ∈ (Finset.Icc 1 (Submission.Rcut x)).filter Squarefree,
        ((d.divisors.card : ℝ)) ^ ((20:ℝ)/3)
          * |(Submission.Ad d t : ℝ) - (Submission.gdens d : ℝ) * (Submission.Aseq t : ℝ)|)
      = ∑ d ∈ Finset.Icc 1 (Submission.Rcut x),
          ((d.divisors.card : ℝ)) ^ ((20:ℝ)/3) * (if Squarefree d
            then |(Submission.Ad d t : ℝ) - (Submission.gdens d : ℝ) * (Submission.Aseq t : ℝ)|
            else 0) := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl (fun d _ => by by_cases h : Squarefree d <;> simp [h])
  have hVs : (∑ d ∈ (Finset.Icc 1 (Submission.Rcut x)).filter Squarefree,
        |(Submission.Ad d t : ℝ) - (Submission.gdens d : ℝ) * (Submission.Aseq t : ℝ)|)
      = ∑ d ∈ Finset.Icc 1 (Submission.Rcut x), (if Squarefree d
          then |(Submission.Ad d t : ℝ) - (Submission.gdens d : ℝ) * (Submission.Aseq t : ℝ)|
          else 0) := by
    rw [Finset.sum_filter]
  have hkey : (∑ d ∈ (Finset.Icc 1 (Submission.Rcut x)).filter Squarefree,
        ((d.divisors.card : ℝ)) ^ 5
          * |(Submission.Ad d t : ℝ) - (Submission.gdens d : ℝ) * (Submission.Aseq t : ℝ)|)
      ≤ (∑ d ∈ (Finset.Icc 1 (Submission.Rcut x)).filter Squarefree,
            ((d.divisors.card : ℝ)) ^ ((20:ℝ)/3)
              * |(Submission.Ad d t : ℝ) - (Submission.gdens d : ℝ) * (Submission.Aseq t : ℝ)|) ^ ((3:ℝ)/4)
        * (∑ d ∈ (Finset.Icc 1 (Submission.Rcut x)).filter Squarefree,
            |(Submission.Ad d t : ℝ) - (Submission.gdens d : ℝ) * (Submission.Aseq t : ℝ)|) ^ ((1:ℝ)/4) := by
    rw [hLs, hUs, hVs]
    exact hholder
  have hU0 : (0:ℝ) ≤ (∑ d ∈ (Finset.Icc 1 (Submission.Rcut x)).filter Squarefree,
        ((d.divisors.card : ℝ)) ^ ((20:ℝ)/3)
          * |(Submission.Ad d t : ℝ) - (Submission.gdens d : ℝ) * (Submission.Aseq t : ℝ)|) :=
    Finset.sum_nonneg (fun d _ => mul_nonneg (by positivity) (abs_nonneg _))
  have hV0 : (0:ℝ) ≤ (∑ d ∈ (Finset.Icc 1 (Submission.Rcut x)).filter Squarefree,
        |(Submission.Ad d t : ℝ) - (Submission.gdens d : ℝ) * (Submission.Aseq t : ℝ)|) :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hUpow0 : (0:ℝ) ≤ C2 * (Submission.Aseq x : ℝ) * L^B2 := by positivity
  have hVpow0 : (0:ℝ) ≤ (Submission.Aseq x : ℝ) * L^(-lam) := by positivity
  refine le_trans hkey ?_
  refine le_trans (mul_le_mul (Real.rpow_le_rpow hU0 hU (by norm_num))
    (Real.rpow_le_rpow hV0 hV (by norm_num)) (Real.rpow_nonneg hV0 _)
    (Real.rpow_nonneg hUpow0 _)) ?_
  -- simplify the resulting exponent
  have hstep1 : (C2 * (Submission.Aseq x : ℝ) * L^B2) ^ ((3:ℝ)/4)
        * ((Submission.Aseq x : ℝ) * L^(-lam)) ^ ((1:ℝ)/4)
      = C2 ^ ((3:ℝ)/4)
        * ((Submission.Aseq x : ℝ)^((3:ℝ)/4) * (Submission.Aseq x : ℝ)^((1:ℝ)/4))
        * (L^(B2*((3:ℝ)/4)) * L^((-lam)*((1:ℝ)/4))) := by
    rw [Real.mul_rpow (mul_nonneg hC2.le hA0) (Real.rpow_nonneg hL0 _),
      Real.mul_rpow hA0 (Real.rpow_nonneg hL0 _),
      Real.mul_rpow hC2.le hA0,
      ← Real.rpow_mul hL0, ← Real.rpow_mul hL0]
    ring
  have hstep2 : C2 ^ ((3:ℝ)/4)
        * ((Submission.Aseq x : ℝ)^((3:ℝ)/4) * (Submission.Aseq x : ℝ)^((1:ℝ)/4))
        * (L^(B2*((3:ℝ)/4)) * L^((-lam)*((1:ℝ)/4)))
      = C2 ^ ((3:ℝ)/4) * (Submission.Aseq x : ℝ) * L^((3:ℝ)/4*B2 - lam/4) := by
    rcases eq_or_lt_of_le hA0 with hA00 | hApos
    · rw [← hA00]; simp
    · rw [← Real.rpow_add hApos, ← Real.rpow_add hLpos,
        show ((3:ℝ)/4 + 1/4) = 1 by norm_num, Real.rpow_one,
        show B2 * ((3:ℝ)/4) + (-lam) * ((1:ℝ)/4) = (3:ℝ)/4*B2 - lam/4 by ring]
      try ring
  rw [hstep1, hstep2]
  have hexp : (3:ℝ)/4*B2 - lam/4 ≤ -25 := by
    rw [hlamdef, hB2kdef]
    by_cases hB : B2 ≤ 0
    · rw [max_eq_right hB]; linarith
    · rw [max_eq_left (le_of_lt (not_le.mp hB))]
      linarith
  have hLexp : L^((3:ℝ)/4*B2 - lam/4) ≤ L^(-(25:ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hL1 hexp
  have hconst : C2 ^ ((3:ℝ)/4) * L^(-(21:ℝ)) ≤ 1 := by
    have h1 : C2 ^ ((3:ℝ)/4) * L^(-(21:ℝ)) ≤ L^(21:ℝ) * L^(-(21:ℝ)) :=
      mul_le_mul_of_nonneg_right hC2pow (Real.rpow_nonneg hL0 _)
    have h2 : L^(21:ℝ) * L^(-(21:ℝ)) = 1 := by
      rw [← Real.rpow_add hLpos]
      norm_num
    linarith [h1, h2.le, h2.ge]
  have hC2A0 : (0:ℝ) ≤ C2 ^ ((3:ℝ)/4) * (Submission.Aseq x : ℝ) :=
    mul_nonneg (Real.rpow_nonneg hC2.le _) hA0
  have h1 : C2 ^ ((3:ℝ)/4) * (Submission.Aseq x : ℝ) * L^((3:ℝ)/4*B2 - lam/4)
      ≤ C2 ^ ((3:ℝ)/4) * (Submission.Aseq x : ℝ) * L^(-(25:ℝ)) :=
    mul_le_mul_of_nonneg_left hLexp hC2A0
  have h2 : C2 ^ ((3:ℝ)/4) * (Submission.Aseq x : ℝ) * L^(-(25:ℝ))
      = (C2 ^ ((3:ℝ)/4) * L^(-(21:ℝ))) * ((Submission.Aseq x : ℝ) * L^(-(4:ℝ))) := by
    rw [show (-(25:ℝ)) = (-(21:ℝ)) + (-(4:ℝ)) by norm_num, Real.rpow_add hLpos]
    ring
  have h3 : (0:ℝ) ≤ (Submission.Aseq x : ℝ) * L^(-(4:ℝ)) := by positivity
  refine le_trans h1 ?_
  rw [h2]
  refine le_trans (mul_le_mul_of_nonneg_right hconst h3) ?_
  rw [one_mul]

/-- The companion's canonical exponent `−3` form of `X2Y4_Rprime` (immediate from the `−4` form). -/
theorem X2Y4_Rprime_three :
    ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → ∀ t : ℕ, 2 ≤ t → t ≤ x →
      (∑ d ∈ (Finset.Icc 1 (Submission.Rcut x)).filter Squarefree,
        ((d.divisors.card : ℝ))^5
          * |(Submission.Ad d t : ℝ) - (Submission.gdens d : ℝ) * (Submission.Aseq t : ℝ)|)
        ≤ (Submission.Aseq x : ℝ) * (Real.log x)^(-(3:ℝ)) := by
  obtain ⟨X₀, h⟩ := X2Y4_Rprime
  refine ⟨max X₀ 3, fun x hx t ht2 htx => ?_⟩
  have hx1 : (1:ℝ) ≤ (x:ℝ) := by
    have : (3:ℕ) ≤ x := le_trans (le_max_right X₀ 3) hx
    exact_mod_cast (by omega : 1 ≤ x)
  have hlog1 : (1:ℝ) ≤ Real.log (x:ℝ) := by
    rw [← Real.log_exp 1]
    refine Real.log_le_log (Real.exp_pos 1) ?_
    have : (3:ℕ) ≤ x := le_trans (le_max_right X₀ 3) hx
    have h3 : (3:ℝ) ≤ (x:ℝ) := by exact_mod_cast this
    linarith [Real.exp_one_lt_d9]
  refine le_trans (h x (le_trans (le_max_left X₀ 3) hx) t ht2 htx) ?_
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hlog1 (by norm_num : (-(4:ℝ)) ≤ -(3:ℝ)))
    (by positivity)

end

end Submission.ASP
