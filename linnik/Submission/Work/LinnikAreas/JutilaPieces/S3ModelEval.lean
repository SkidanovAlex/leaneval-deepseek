import Mathlib
import Submission.Work.LinnikAreas.JutilaPieces.S3ModelDefs
import Submission.Work.ZeroDensity.Jutila.Bz3Defs
import Submission.Work.ZeroDensity.Jutila.Bz3Reduce
import Submission.Work.LinnikAreas.JutilaPieces.S3HarmonicSum
import Submission.Work.LinnikAreas.Density4.BzHard.mertens_log_weighted_one
import Submission.Work.LinnikAreas.Density4.selberg_U_sum_decay
import Submission.Work.LinnikAreas.JutilaPieces.S3ModelDS
import Submission.Work.LinnikAreas.JutilaPieces.S3ModelDSErr
import Submission.Work.LinnikAreas.JutilaPieces.SumInvPowLogExpDecay
import Submission.Work.LinnikAreas.JutilaPieces.SumInvDivLogSq

namespace Work.LinnikAreas.JutilaPieces

set_option maxHeartbeats 4000000

open Finset

noncomputable section

/-! ## Elementary lemmas about the objects of the computation -/

lemma kap_one : Work.ZeroDensity.Jutila.kap 1 = 1 := by
  simp [Work.ZeroDensity.Jutila.kap]

lemma wm_one : wm 1 = 1 := by
  simp [wm, kap_one]

lemma RS0_one : RS0 1 1 = 1 := by
  simp [RS0, wm_one]

lemma RS1_one (Q : ℝ) : RS1 Q 1 1 = Real.log Q - 1 := by
  simp [RS1, wm_one]

lemma s3DSabs_one (Q : ℝ) : s3DSabs Q 1 = (Real.log Q - 1) ^ 2 + 1 := by
  rw [s3DSabs, show Finset.Icc 1 1 = {1} from rfl, Finset.sum_singleton, RS1_one, RS0_one,
    wm_one]
  ring_nf

/-- `(A:ℝ)/q < ⌊A/q⌋ + 1`. -/
lemma div_lt_div_floor_add_one (A q : ℕ) (hq : 0 < q) :
    (A : ℝ) / (q : ℝ) < (((A / q : ℕ)) : ℝ) + 1 := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hA : (A : ℝ) = (q : ℝ) * (((A / q : ℕ)) : ℝ) + (((A % q : ℕ)) : ℝ) := by
    rw [← Nat.cast_mul, ← Nat.cast_add, Nat.div_add_mod]
  have hmod : (((A % q : ℕ)) : ℝ) < (q : ℝ) := by exact_mod_cast Nat.mod_lt A hq
  rw [div_lt_iff₀ hqR]
  nlinarith [hA, hmod]

/-- `⌊A/q⌋ ≤ (A:ℝ)/q`. -/
lemma div_floor_le (A q : ℕ) : (((A / q : ℕ)) : ℝ) ≤ (A : ℝ) / (q : ℝ) := Nat.cast_div_le

/-- For `2q ≤ A`, the floor `⌊A/q⌋` is at least a quarter of `A/q` on the log scale:
`log (A/q) ≤ 4 log ⌊A/q⌋`. -/
lemma log_div_le_four_mul_log_floor (A q : ℕ) (hq : 1 ≤ q) (h2 : 2 * q ≤ A) :
    Real.log ((A : ℝ) / (q : ℝ)) ≤ 4 * Real.log (((A / q : ℕ)) : ℝ) := by
  have hq0 : 0 < q := by omega
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
  have hAR : (0 : ℝ) < (A : ℝ) := by
    have : 0 < A := by omega
    exact_mod_cast this
  have hu : (2 : ℝ) ≤ (A : ℝ) / (q : ℝ) := by
    rw [le_div_iff₀ hqR]
    exact_mod_cast h2
  have hB2 : 2 ≤ A / q := (Nat.le_div_iff_mul_le hq0).mpr (by linarith [h2])
  have hBR : (2 : ℝ) ≤ (((A / q : ℕ)) : ℝ) := by exact_mod_cast hB2
  have hlogB : Real.log (2 : ℝ) ≤ Real.log (((A / q : ℕ)) : ℝ) :=
    Real.log_le_log (by norm_num) hBR
  have hlt := div_lt_div_floor_add_one A q hq0
  have hge : (A : ℝ) / (2 * (q : ℝ)) ≤ (((A / q : ℕ)) : ℝ) := by
    have heq : (A : ℝ) / (2 * (q : ℝ)) = (A : ℝ) / (q : ℝ) / 2 := by field_simp
    rw [heq]
    linarith
  have hlog2B : Real.log ((A : ℝ) / (2 * (q : ℝ))) ≤ Real.log (((A / q : ℕ)) : ℝ) :=
    Real.log_le_log (by positivity) hge
  have hsplit : Real.log ((A : ℝ) / (2 * (q : ℝ)))
      = Real.log ((A : ℝ) / (q : ℝ)) - Real.log 2 := by
    have h1 : (A : ℝ) / (2 * (q : ℝ)) = ((A : ℝ) / (q : ℝ)) / 2 := by field_simp
    rw [h1, Real.log_div (by positivity) (by norm_num)]
  rw [hsplit] at hlog2B
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  by_cases hc : Real.log ((A : ℝ) / (q : ℝ)) ≤ 3 * Real.log 2
  · linarith
  · have hc' : 3 * Real.log 2 < Real.log ((A : ℝ) / (q : ℝ)) := not_le.mp hc
    linarith

/-- `Qf z N q ≤ 2·(⌊N/z⌋)/q` for `1 ≤ q`, `1 ≤ z ≤ N`. -/
lemma Qf_le (z N q : ℕ) (hq : 1 ≤ q) (hz : 1 ≤ z) (hzN : z ≤ N) :
    Qf z N q ≤ 2 * (((N / z : ℕ)) : ℝ) / (q : ℝ) := by
  have hq0 : 0 < q := by omega
  have hz0 : 0 < z := by omega
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
  have hzR : (0 : ℝ) < (z : ℝ) := by exact_mod_cast hz0
  have hA1 : 1 ≤ N / z := (Nat.le_div_iff_mul_le hz0).mpr (by simpa using hzN)
  have hAR1 : (1 : ℝ) ≤ (((N / z : ℕ)) : ℝ) := by exact_mod_cast hA1
  have hN : (N : ℝ) = (z : ℝ) * (((N / z : ℕ)) : ℝ) + (((N % z : ℕ)) : ℝ) := by
    rw [← Nat.cast_mul, ← Nat.cast_add, Nat.div_add_mod]
  have hmod : (((N % z : ℕ)) : ℝ) < (z : ℝ) := by exact_mod_cast Nat.mod_lt N hz0
  have hlt : (N : ℝ) / (z : ℝ) < (((N / z : ℕ)) : ℝ) + 1 := by
    rw [div_lt_iff₀ hzR]
    nlinarith [hN, hmod]
  have hQ : Qf z N q = ((N : ℝ) / (z : ℝ)) / (q : ℝ) := by
    rw [Qf]; field_simp
  rw [hQ, div_le_div_iff_of_pos_right hqR]
  linarith

/-- The decomposition of the `t`-sum of the model: replacing the cut-off `Q` by `⌊Q⌋ = B` in the
logarithm produces the exact Mertens-type main term. -/
lemma M_decomp (Q : ℝ) (B : ℕ) (hB : 1 ≤ B) (hQ0 : 0 < Q) (hQB : (B : ℝ) ≤ Q) :
    (∑ t ∈ Finset.Icc 1 B,
        (ArithmeticFunction.moebius t : ℝ) / (t : ℝ) * (Real.log (Q / (t : ℝ)) - 1))
      = (∑ t ∈ Finset.Icc 1 B,
          (ArithmeticFunction.moebius t : ℝ) / (t : ℝ) * (Real.log ((B : ℝ) / (t : ℝ)) - 1))
        + Real.log (Q / (B : ℝ)) * Commons.NumberTheory.Moebius.muRecipSum B := by
  have hB0 : (0 : ℝ) < (B : ℝ) := by exact_mod_cast (by omega : 0 < B)
  have hterm : ∀ t ∈ Finset.Icc 1 B,
      Real.log (Q / (t : ℝ)) - 1
        = (Real.log ((B : ℝ) / (t : ℝ)) - 1) + Real.log (Q / (B : ℝ)) := by
    intro t ht
    obtain ⟨ht1, _⟩ := Finset.mem_Icc.mp ht
    have ht0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
    rw [Real.log_div (ne_of_gt hQ0) (ne_of_gt ht0),
      Real.log_div (ne_of_gt hB0) (ne_of_gt ht0),
      Real.log_div (ne_of_gt hQ0) (ne_of_gt hB0)]
    ring
  rw [Commons.NumberTheory.Moebius.muRecipSum]
  calc (∑ t ∈ Finset.Icc 1 B,
        (ArithmeticFunction.moebius t : ℝ) / (t : ℝ) * (Real.log (Q / (t : ℝ)) - 1))
      = ∑ t ∈ Finset.Icc 1 B, (ArithmeticFunction.moebius t : ℝ) / (t : ℝ) *
          ((Real.log ((B : ℝ) / (t : ℝ)) - 1) + Real.log (Q / (B : ℝ))) := by
        refine Finset.sum_congr rfl fun t ht => ?_
        rw [hterm t ht]
    _ = ∑ t ∈ Finset.Icc 1 B,
          ((ArithmeticFunction.moebius t : ℝ) / (t : ℝ) * (Real.log ((B : ℝ) / (t : ℝ)) - 1)
            + (ArithmeticFunction.moebius t : ℝ) / (t : ℝ) * Real.log (Q / (B : ℝ))) := by
        refine Finset.sum_congr rfl fun t ht => ?_
        ring
    _ = (∑ t ∈ Finset.Icc 1 B,
          (ArithmeticFunction.moebius t : ℝ) / (t : ℝ) * (Real.log ((B : ℝ) / (t : ℝ)) - 1))
        + (∑ t ∈ Finset.Icc 1 B, (ArithmeticFunction.moebius t : ℝ) / (t : ℝ))
            * Real.log (Q / (B : ℝ)) := by
        rw [Finset.sum_add_distrib, Finset.sum_mul]
    _ = (∑ t ∈ Finset.Icc 1 B,
          (ArithmeticFunction.moebius t : ℝ) / (t : ℝ) * (Real.log ((B : ℝ) / (t : ℝ)) - 1))
        + Real.log (Q / (B : ℝ)) * (∑ t ∈ Finset.Icc 1 B,
            (ArithmeticFunction.moebius t : ℝ) / (t : ℝ)) := by
        ring

end

end Work.LinnikAreas.JutilaPieces

namespace Work.LinnikAreas.JutilaPieces

open Finset

noncomputable section

/-! ## The per-`q` estimate and the summation bookkeeping -/

/-- `e^{-c√log(A/q)}` comparison: if `4 log B ≥ log(A/q)` (both logs nonnegative) and
`2c' ≤ c`, then `e^{-c√log B} ≤ e^{-c'√log(A/q)}`. -/
private lemma exp_decay_le {A B q : ℕ} {c c' : ℝ}
    (hlog : Real.log ((A : ℝ) / (q : ℝ)) ≤ 4 * Real.log ((B : ℝ)))
    (hu : 0 ≤ Real.log ((A : ℝ) / (q : ℝ))) (hc' : 0 < c') (hle : 2 * c' ≤ c) :
    Real.exp (-(c * Real.sqrt (Real.log ((B : ℝ)))))
      ≤ Real.exp (-(c' * Real.sqrt (Real.log ((A : ℝ) / (q : ℝ))))) := by
  apply Real.exp_le_exp.mpr
  have hv : 0 ≤ Real.log ((B : ℝ)) := by linarith
  have hsqrt : Real.sqrt (Real.log ((A : ℝ) / (q : ℝ)))
      ≤ 2 * Real.sqrt (Real.log ((B : ℝ))) := by
    have h1 := Real.sqrt_le_sqrt hlog
    rwa [show Real.sqrt (4 * Real.log ((B : ℝ))) = 2 * Real.sqrt (Real.log ((B : ℝ))) by
      rw [Real.sqrt_mul (by norm_num), show Real.sqrt (4 : ℝ) = 2 by norm_num]] at h1
  have hb : 0 ≤ Real.sqrt (Real.log ((B : ℝ))) := Real.sqrt_nonneg _
  nlinarith [hsqrt, hb, hc'.le, hle]

/-- Absorption: `(log Q + 2)^4 ≤ 16 (u+2)^4` when `0 ≤ u` and `log Q ≤ u + log 2`. -/
private lemma log_add_two_pow_le {u v : ℝ} (hu : 0 ≤ u) (hv0 : 0 ≤ v) (hv : v ≤ u + Real.log 2) :
    (v + 2) ^ 4 ≤ 16 * (u + 2) ^ 4 := by
  have hlog2 : Real.log 2 ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hv2 : v + 2 ≤ 2 * (u + 2) := by linarith
  calc (v + 2) ^ 4 ≤ (2 * (u + 2)) ^ 4 := by
        apply pow_le_pow_left₀ (by linarith) hv2
    _ = 16 * (u + 2) ^ 4 := by ring

/-- `1/log²⌊A/q⌋ ≤ 16/log²(A/q)` when `2q ≤ A`. -/
private lemma inv_log_sq_le {A q : ℕ} (hq : 1 ≤ q) (h2 : 2 * q ≤ A) :
    1 / (Real.log (((A / q : ℕ)) : ℝ)) ^ 2
      ≤ 16 * (1 / (Real.log ((A : ℝ) / (q : ℝ))) ^ 2) := by
  have hlog := log_div_le_four_mul_log_floor A q hq h2
  have hBpos : 0 < Real.log (((A / q : ℕ)) : ℝ) := by
    apply Real.log_pos
    have : 2 ≤ A / q := (Nat.le_div_iff_mul_le (by omega : 0 < q)).mpr (by linarith [h2])
    exact_mod_cast (by omega : 1 < A / q)
  have hApos : 0 < Real.log ((A : ℝ) / (q : ℝ)) := by
    apply Real.log_pos
    rw [one_lt_div (by exact_mod_cast (by omega : 0 < q))]
    exact_mod_cast (by linarith [h2] : q < A)
  have h1 : (Real.log ((A : ℝ) / (q : ℝ))) ^ 2 ≤ 16 * (Real.log (((A / q : ℕ)) : ℝ)) ^ 2 := by
    nlinarith [hlog, hBpos.le, hApos.le]
  have hu2 : (0 : ℝ) < (Real.log ((A : ℝ) / (q : ℝ))) ^ 2 := by positivity
  have hb2 : (0 : ℝ) < (Real.log (((A / q : ℕ)) : ℝ)) ^ 2 := by positivity
  have key : 16 * (1 / (Real.log ((A : ℝ) / (q : ℝ))) ^ 2)
      = 16 / (Real.log ((A : ℝ) / (q : ℝ))) ^ 2 := by
    ring
  rw [key, div_le_div_iff₀ hb2 hu2]
  linarith

/-- **Per-`q` estimate of the continuous model.**  For `2q ≤ N/z`, the `t`-sum `s3DSabs (Qf z N q) (N/(qz))`
is `ζ(2)` plus `ζ(2)` times the Mertens-type error of the `t`-sum, plus the input error. -/
private lemma per_q_big {KDS cDS KM Kmu cmu : ℝ} {N z q : ℕ}
    (hDSw : ∀ (Q : ℝ) (B : ℕ), 2 ≤ B → (B : ℝ) ≤ Q →
        |s3DSabs Q B - (Real.pi ^ 2 / 6) * (∑ t ∈ Finset.Icc 1 B,
            (ArithmeticFunction.moebius t : ℝ) / (t : ℝ) * (Real.log (Q / (t : ℝ)) - 1))|
          ≤ KDS * (Real.log Q + 2) ^ 4 * Real.exp (-(cDS * Real.sqrt (Real.log (B : ℝ)))))
    (hMw : ∀ T : ℕ, 2 ≤ T →
        |(∑ t ∈ Finset.Icc 1 T,
            (ArithmeticFunction.moebius t : ℝ) * (Real.log (T : ℝ) - Real.log (t : ℝ) - 1) / (t : ℝ)) - 1|
          ≤ KM / (Real.log (T : ℝ)) ^ 2)
    (hmuw : ∀ n : ℕ, 1 ≤ n →
        |Commons.NumberTheory.Moebius.muRecipSum n|
          ≤ Kmu * Real.exp (-(cmu * Real.sqrt (Real.log (n : ℝ)))))
    (hz : 1 ≤ z) (hN : 1 ≤ N) (hq : 1 ≤ q) (h2 : 2 * q ≤ N / z)
    (hkd : 0 ≤ KDS) (hkm : 0 ≤ KM) (hcm : 0 ≤ Kmu) :
    |s3DSabs (Qf z N q) (N / (q * z)) - Real.pi ^ 2 / 6|
      ≤ (Real.pi ^ 2 / 6) * KM / (Real.log (((N / (q * z) : ℕ)) : ℝ)) ^ 2
        + (Real.pi ^ 2 / 6) * Real.log 2 * Kmu
            * Real.exp (-(cmu * Real.sqrt (Real.log (((N / (q * z) : ℕ)) : ℝ))))
        + KDS * (Real.log (Qf z N q) + 2) ^ 4
            * Real.exp (-(cDS * Real.sqrt (Real.log (((N / (q * z) : ℕ)) : ℝ)))) := by
  set B := N / (q * z) with hB
  have hq0 : 0 < q := by omega
  have hz0 : 0 < z := by omega
  have hN0 : 0 < N := by omega
  have hB2 : 2 ≤ B := by
    rw [hB, Nat.le_div_iff_mul_le (by positivity : 0 < q * z)]
    have hh := (Nat.le_div_iff_mul_le (by omega : 0 < z)).mp h2
    nlinarith [hh]
  have hBQ : (B : ℝ) ≤ Qf z N q := by
    rw [hB, Qf]
    simpa [Nat.cast_mul] using (Nat.cast_div_le (α := ℝ) (m := N) (n := q * z))
  have hQ0 : 0 < Qf z N q := by
    rw [Qf]
    exact div_pos (by exact_mod_cast hN0) (by positivity)
  have hds := hDSw (Qf z N q) B hB2 hBQ
  have hMd := M_decomp (Qf z N q) B (by omega) hQ0 hBQ
  have hm0 : |(∑ t ∈ Finset.Icc 1 B,
        (ArithmeticFunction.moebius t : ℝ) / (t : ℝ) * (Real.log ((B : ℝ) / (t : ℝ)) - 1)) - 1|
      ≤ KM / (Real.log (B : ℝ)) ^ 2 := by
    have hh := hMw B hB2
    have heq : (∑ t ∈ Finset.Icc 1 B,
          (ArithmeticFunction.moebius t : ℝ) / (t : ℝ) * (Real.log ((B : ℝ) / (t : ℝ)) - 1))
        = (∑ t ∈ Finset.Icc 1 B,
            (ArithmeticFunction.moebius t : ℝ) * (Real.log (B : ℝ) - Real.log (t : ℝ) - 1) / (t : ℝ)) := by
      refine Finset.sum_congr rfl fun t ht => ?_
      obtain ⟨ht1, _⟩ := Finset.mem_Icc.mp ht
      have ht0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
      have hB0 : (0 : ℝ) < (B : ℝ) := by exact_mod_cast (by omega : 0 < B)
      rw [Real.log_div (ne_of_gt hB0) (ne_of_gt ht0)]
      ring
    rw [heq]; exact hh
  have hm1 := hmuw B (by omega : 1 ≤ B)
  have hlogQB0 : 0 ≤ Real.log (Qf z N q / (B : ℝ)) := by
    apply Real.log_nonneg
    rw [one_le_div (by exact_mod_cast (by omega : 0 < B))]
    exact hBQ
  have hlogQB : Real.log (Qf z N q / (B : ℝ)) ≤ Real.log 2 := by
    apply Real.log_le_log
    · positivity
    · have hB0 : (0 : ℝ) < (B : ℝ) := by exact_mod_cast (by omega : 0 < B)
      have hlt : Qf z N q < (B : ℝ) + 1 := by
        rw [hB, Qf]
        have hh := div_lt_div_floor_add_one N (q * z) (by positivity : 0 < q * z)
        push_cast at hh
        exact hh
      have hB2R : (2 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB2
      rw [div_le_iff₀ hB0]
      linarith
  have hcomb : |(∑ t ∈ Finset.Icc 1 B,
        (ArithmeticFunction.moebius t : ℝ) / (t : ℝ) * (Real.log (Qf z N q / (t : ℝ)) - 1)) - 1|
      ≤ KM / (Real.log (B : ℝ)) ^ 2 + Real.log 2 * |Commons.NumberTheory.Moebius.muRecipSum B| := by
    rw [hMd]
    have heq : (∑ t ∈ Finset.Icc 1 B,
          (ArithmeticFunction.moebius t : ℝ) / (t : ℝ) * (Real.log ((B : ℝ) / (t : ℝ)) - 1))
        + Real.log (Qf z N q / (B : ℝ)) * Commons.NumberTheory.Moebius.muRecipSum B - 1
        = ((∑ t ∈ Finset.Icc 1 B,
              (ArithmeticFunction.moebius t : ℝ) / (t : ℝ) * (Real.log ((B : ℝ) / (t : ℝ)) - 1)) - 1)
          + Real.log (Qf z N q / (B : ℝ)) * Commons.NumberTheory.Moebius.muRecipSum B := by ring
    rw [heq]
    refine le_trans (abs_add_le _ _) ?_
    apply add_le_add hm0
    rw [abs_mul, abs_of_nonneg hlogQB0]
    exact mul_le_mul_of_nonneg_right hlogQB (abs_nonneg _)
  -- final combination
  have hζpos : (0 : ℝ) < Real.pi ^ 2 / 6 := by positivity
  set Mq := (∑ t ∈ Finset.Icc 1 B,
      (ArithmeticFunction.moebius t : ℝ) / (t : ℝ) * (Real.log (Qf z N q / (t : ℝ)) - 1)) with hMq
  have hsplit : |s3DSabs (Qf z N q) B - Real.pi ^ 2 / 6|
      ≤ |s3DSabs (Qf z N q) B - (Real.pi ^ 2 / 6) * Mq| + (Real.pi ^ 2 / 6) * |Mq - 1| := by
    have heq : s3DSabs (Qf z N q) B - Real.pi ^ 2 / 6
        = (s3DSabs (Qf z N q) B - (Real.pi ^ 2 / 6) * Mq) + (Real.pi ^ 2 / 6) * (Mq - 1) := by ring
    rw [heq]
    refine le_trans (abs_add_le _ _) ?_
    rw [abs_mul, abs_of_pos hζpos]
  have hcomb' : |Mq - 1| ≤ KM / (Real.log (B : ℝ)) ^ 2
      + Real.log 2 * (Kmu * Real.exp (-(cmu * Real.sqrt (Real.log (B : ℝ))))) := by
    refine le_trans hcomb ?_
    apply add_le_add le_rfl
    exact mul_le_mul_of_nonneg_left hm1 (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))
  refine le_trans hsplit (le_trans (add_le_add hds (mul_le_mul_of_nonneg_left hcomb' hζpos.le)) ?_)
  apply le_of_eq
  ring_nf


/-! ## The assembly -/

theorem S3ModelEval (h : Work.ZeroDensity.Jutila.KappaMertensInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z N : ℕ), 2 ≤ z → z ≤ N → N < z * z →
      |Work.ZeroDensity.Jutila.s3cont z N - (N : ℝ) * Real.log ((N : ℝ) / (z : ℝ))| ≤ C * (N : ℝ) := by
  obtain ⟨C1, hC1, hH⟩ := S3HarmonicSum
  obtain ⟨Kmu, cmu, hcmu, hKmu, hmu⟩ := Work.LinnikAreas.Density4.muRecipSum_exp_decay
  obtain ⟨KM, hKM, hMw⟩ := Work.LinnikAreas.Density4.BzHard.mertens_log_weighted_one
  obtain ⟨KDS, cDS, hKDS, hcDS, hDSw⟩ := S3ModelDSErr h
  obtain ⟨KD1, hKD1, hD1⟩ := SumInvPowLogExpDecay (min cDS cmu / 2) (by positivity) 4
  obtain ⟨KD2, hKD2, hD2⟩ := SumInvDivLogSq
  refine ⟨(Real.pi ^ 2 / 6)⁻¹ * (16 * (Real.pi ^ 2 / 6) * KM * KD2
      + (Real.pi ^ 2 / 6) * Real.log 2 * Kmu * KD1 + 16 * KDS * KD1 + 40) + C1, by positivity, ?_⟩
  intro z N hz hzN hNz
  have hz0 : 0 < z := by omega
  have hA1 : 1 ≤ N / z := (Nat.le_div_iff_mul_le hz0).mpr (by simpa using hzN)
  have hmain : |(∑ q ∈ Finset.Icc 1 (N / z), (N : ℝ) / (q : ℝ))
      - (N : ℝ) * Real.log ((N : ℝ) / (z : ℝ))| ≤ C1 * (N : ℝ) := by
    have hh := hH N z hz hzN
    have hsum : (∑ q ∈ Finset.Icc 1 (N / z), (N : ℝ) / (q : ℝ))
        = (N : ℝ) * (∑ q ∈ Finset.Icc 1 (N / z), (1 : ℝ) / (q : ℝ)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun q _ => by ring
    rw [hsum, ← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg N)]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg N)
  have hkey : |Work.ZeroDensity.Jutila.s3cont z N
      - (∑ q ∈ Finset.Icc 1 (N / z), (N : ℝ) / (q : ℝ))|
      ≤ (Real.pi ^ 2 / 6)⁻¹ * ((N : ℝ) * (16 * (Real.pi ^ 2 / 6) * KM * KD2
          + (Real.pi ^ 2 / 6) * Real.log 2 * Kmu * KD1 + 16 * KDS * KD1 + 40)) := by
    rw [S3ModelDS z N]
    have hζpos : (0 : ℝ) < Real.pi ^ 2 / 6 := by positivity
    have hζne : Real.pi ^ 2 / 6 ≠ 0 := ne_of_gt hζpos
    have hbridge : (Real.pi ^ 2 / 6)⁻¹ * (∑ q ∈ Finset.Icc 1 (N / z),
            (N : ℝ) / (q : ℝ) * s3DSabs (Qf z N q) (N / (q * z)))
        - (∑ q ∈ Finset.Icc 1 (N / z), (N : ℝ) / (q : ℝ))
        = (Real.pi ^ 2 / 6)⁻¹ * (∑ q ∈ Finset.Icc 1 (N / z),
            (N : ℝ) / (q : ℝ) * (s3DSabs (Qf z N q) (N / (q * z)) - Real.pi ^ 2 / 6)) := by
      have h1 : (∑ q ∈ Finset.Icc 1 (N / z),
            (N : ℝ) / (q : ℝ) * (s3DSabs (Qf z N q) (N / (q * z)) - Real.pi ^ 2 / 6))
          = (∑ q ∈ Finset.Icc 1 (N / z), (N : ℝ) / (q : ℝ) * s3DSabs (Qf z N q) (N / (q * z)))
            - (Real.pi ^ 2 / 6) * (∑ q ∈ Finset.Icc 1 (N / z), (N : ℝ) / (q : ℝ)) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun q _ => by ring
      rw [h1, mul_sub, ← mul_assoc, inv_mul_cancel₀ hζne, one_mul]
    rw [hbridge, abs_mul, abs_of_pos (inv_pos.mpr hζpos)]
    apply mul_le_mul_of_nonneg_left _ (le_of_lt (inv_pos.mpr hζpos))
    set A := N / z with hA
    have hA1' : 1 ≤ A := by rw [hA]; exact hA1
    have hApos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast (by omega : 0 < A)
    -- ### Piece 1: the pointwise bound on the "big" range
    have hpt_big : ∀ q ∈ (Finset.Icc 1 A).filter (fun q => 2 * q ≤ A),
        (N : ℝ) / (q : ℝ) * |s3DSabs (Qf z N q) (N / (q * z)) - Real.pi ^ 2 / 6|
          ≤ (N : ℝ) / (q : ℝ) * ((Real.pi ^ 2 / 6) * KM / (Real.log (((N / (q * z) : ℕ)) : ℝ)) ^ 2
              + (Real.pi ^ 2 / 6) * Real.log 2 * Kmu
                  * Real.exp (-(cmu * Real.sqrt (Real.log (((N / (q * z) : ℕ)) : ℝ))))
              + KDS * (Real.log (Qf z N q) + 2) ^ 4
                  * Real.exp (-(cDS * Real.sqrt (Real.log (((N / (q * z) : ℕ)) : ℝ))))) := by
      intro q hq
      rw [Finset.mem_filter] at hq
      obtain ⟨hqmem, hq2⟩ := hq
      obtain ⟨hq1, hqA⟩ := Finset.mem_Icc.mp hqmem
      have hp := per_q_big (KDS := KDS) (cDS := cDS) (KM := KM) (Kmu := Kmu) (cmu := cmu)
        hDSw hMw hmu (by omega : 1 ≤ z) (by omega : 1 ≤ N) hq1 (by rw [hA] at hq2; exact hq2)
        hKDS.le hKM.le hKmu.le
      exact mul_le_mul_of_nonneg_left hp (by positivity)
    -- ### Piece 2: the three sums on the "big" range
    have hF : (∑ q ∈ (Finset.Icc 1 A).filter (fun q => 2 * q ≤ A),
          (1 : ℝ) / (q : ℝ) * ((Real.pi ^ 2 / 6) * KM / (Real.log (((N / (q * z) : ℕ)) : ℝ)) ^ 2))
        ≤ 16 * (Real.pi ^ 2 / 6) * KM * KD2 := by
      have hpt : ∀ q ∈ (Finset.Icc 1 A).filter (fun q => 2 * q ≤ A),
          (1 : ℝ) / (q : ℝ) * ((Real.pi ^ 2 / 6) * KM / (Real.log (((N / (q * z) : ℕ)) : ℝ)) ^ 2)
            ≤ (Real.pi ^ 2 / 6) * KM * (16 * ((1 : ℝ) / (q : ℝ) * (1 / (Real.log ((A : ℝ) / (q : ℝ))) ^ 2))) := by
        intro q hq
        rw [Finset.mem_filter] at hq
        obtain ⟨hqmem, hq2⟩ := hq
        obtain ⟨hq1, hqA⟩ := Finset.mem_Icc.mp hqmem
        have hq0 : 0 < q := by omega
        have hBeq : N / (q * z) = A / q := by
          rw [hA, Nat.mul_comm q z]
          exact (Nat.div_div_eq_div_mul N z q).symm
        have hil := inv_log_sq_le (A := A) hq1 hq2
        rw [hBeq]
        have hC : (0 : ℝ) ≤ (1 : ℝ) / (q : ℝ) * ((Real.pi ^ 2 / 6) * KM) := by positivity
        calc (1 : ℝ) / (q : ℝ) * ((Real.pi ^ 2 / 6) * KM / (Real.log (((A / q : ℕ)) : ℝ)) ^ 2)
            = (1 : ℝ) / (q : ℝ) * ((Real.pi ^ 2 / 6) * KM)
                * (1 / (Real.log (((A / q : ℕ)) : ℝ)) ^ 2) := by
              rw [div_eq_mul_inv]; ring
          _ ≤ (1 : ℝ) / (q : ℝ) * ((Real.pi ^ 2 / 6) * KM)
                * (16 * (1 / (Real.log ((A : ℝ) / (q : ℝ))) ^ 2)) :=
              mul_le_mul_of_nonneg_left hil hC
          _ = (Real.pi ^ 2 / 6) * KM
                * (16 * ((1 : ℝ) / (q : ℝ) * (1 / (Real.log ((A : ℝ) / (q : ℝ))) ^ 2))) := by ring
      have hD2' := hD2 A hA1'
      rw [← Finset.sum_filter] at hD2'
      calc (∑ q ∈ (Finset.Icc 1 A).filter (fun q => 2 * q ≤ A),
            (1 : ℝ) / (q : ℝ) * ((Real.pi ^ 2 / 6) * KM / (Real.log (((N / (q * z) : ℕ)) : ℝ)) ^ 2))
          ≤ ∑ q ∈ (Finset.Icc 1 A).filter (fun q => 2 * q ≤ A),
              (Real.pi ^ 2 / 6) * KM * (16 * ((1 : ℝ) / (q : ℝ) * (1 / (Real.log ((A : ℝ) / (q : ℝ))) ^ 2))) :=
            Finset.sum_le_sum hpt
        _ = (Real.pi ^ 2 / 6) * KM * (16 * (∑ q ∈ (Finset.Icc 1 A).filter (fun q => 2 * q ≤ A),
              (1 : ℝ) / (q : ℝ) * (1 / (Real.log ((A : ℝ) / (q : ℝ))) ^ 2))) := by
            rw [Finset.mul_sum, Finset.mul_sum]
        _ ≤ (Real.pi ^ 2 / 6) * KM * (16 * KD2) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            simpa only [one_div, div_eq_mul_inv, mul_one, one_mul] using hD2'
        _ = 16 * (Real.pi ^ 2 / 6) * KM * KD2 := by ring
    have hG : (∑ q ∈ (Finset.Icc 1 A).filter (fun q => 2 * q ≤ A),
          (1 : ℝ) / (q : ℝ) * ((Real.pi ^ 2 / 6) * Real.log 2 * Kmu
              * Real.exp (-(cmu * Real.sqrt (Real.log (((N / (q * z) : ℕ)) : ℝ))))))
        ≤ (Real.pi ^ 2 / 6) * Real.log 2 * Kmu * KD1 := by
      have hpt : ∀ q ∈ (Finset.Icc 1 A).filter (fun q => 2 * q ≤ A),
          (1 : ℝ) / (q : ℝ) * ((Real.pi ^ 2 / 6) * Real.log 2 * Kmu
              * Real.exp (-(cmu * Real.sqrt (Real.log (((N / (q * z) : ℕ)) : ℝ)))))
            ≤ (Real.pi ^ 2 / 6) * Real.log 2 * Kmu * ((1 : ℝ) / (q : ℝ)
                * (Real.log ((A : ℝ) / (q : ℝ)) + 2) ^ 4
                * Real.exp (-((min cDS cmu / 2) * Real.sqrt (Real.log ((A : ℝ) / (q : ℝ)))))) := by
        intro q hq
        rw [Finset.mem_filter] at hq
        obtain ⟨hqmem, hq2⟩ := hq
        obtain ⟨hq1, hqA⟩ := Finset.mem_Icc.mp hqmem
        have hq0 : 0 < q := by omega
        have hBeq : N / (q * z) = A / q := by
          rw [hA, Nat.mul_comm q z]
          exact (Nat.div_div_eq_div_mul N z q).symm
        have hlogA0 : 0 ≤ Real.log ((A : ℝ) / (q : ℝ)) := Real.log_nonneg (by
          rw [one_le_div (by exact_mod_cast (by omega : 0 < q))]
          exact_mod_cast hqA)
        have hexp := exp_decay_le (A := A) (B := A / q) (q := q) (c := cmu)
          (c' := min cDS cmu / 2) (log_div_le_four_mul_log_floor A q hq1 hq2) hlogA0
          (by positivity) (by
            have hle : min cDS cmu ≤ cmu := min_le_right _ _
            have := lt_min hcDS hcmu
            linarith)
        rw [hBeq]
        have hone : (1 : ℝ) ≤ (Real.log ((A : ℝ) / (q : ℝ)) + 2) ^ 4 := by
          have h1 : (1 : ℝ) ≤ Real.log ((A : ℝ) / (q : ℝ)) + 2 := by linarith
          exact one_le_pow₀ h1
        have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
        have hstep : Real.exp (-(cmu * Real.sqrt (Real.log (((A / q : ℕ)) : ℝ))))
            ≤ (Real.log ((A : ℝ) / (q : ℝ)) + 2) ^ 4
              * Real.exp (-((min cDS cmu / 2) * Real.sqrt (Real.log ((A : ℝ) / (q : ℝ))))) := by
          calc Real.exp (-(cmu * Real.sqrt (Real.log (((A / q : ℕ)) : ℝ))))
              ≤ Real.exp (-((min cDS cmu / 2) * Real.sqrt (Real.log ((A : ℝ) / (q : ℝ))))) := hexp
            _ = 1 * Real.exp (-((min cDS cmu / 2) * Real.sqrt (Real.log ((A : ℝ) / (q : ℝ))))) := by ring
            _ ≤ (Real.log ((A : ℝ) / (q : ℝ)) + 2) ^ 4
                  * Real.exp (-((min cDS cmu / 2) * Real.sqrt (Real.log ((A : ℝ) / (q : ℝ))))) := by
                exact mul_le_mul_of_nonneg_right hone (Real.exp_nonneg _)
        calc (1 : ℝ) / (q : ℝ) * ((Real.pi ^ 2 / 6) * Real.log 2 * Kmu
              * Real.exp (-(cmu * Real.sqrt (Real.log (((A / q : ℕ)) : ℝ)))))
            = (1 : ℝ) / (q : ℝ) * ((Real.pi ^ 2 / 6) * Real.log 2 * Kmu)
                * Real.exp (-(cmu * Real.sqrt (Real.log (((A / q : ℕ)) : ℝ)))) := by ring
          _ ≤ (1 : ℝ) / (q : ℝ) * ((Real.pi ^ 2 / 6) * Real.log 2 * Kmu)
                * ((Real.log ((A : ℝ) / (q : ℝ)) + 2) ^ 4
                  * Real.exp (-((min cDS cmu / 2) * Real.sqrt (Real.log ((A : ℝ) / (q : ℝ)))))) :=
              mul_le_mul_of_nonneg_left hstep (by positivity)
          _ = (Real.pi ^ 2 / 6) * Real.log 2 * Kmu * ((1 : ℝ) / (q : ℝ)
                * (Real.log ((A : ℝ) / (q : ℝ)) + 2) ^ 4
                * Real.exp (-((min cDS cmu / 2) * Real.sqrt (Real.log ((A : ℝ) / (q : ℝ)))))) := by ring
      have hD1' := hD1 A hA1'
      calc (∑ q ∈ (Finset.Icc 1 A).filter (fun q => 2 * q ≤ A),
            (1 : ℝ) / (q : ℝ) * ((Real.pi ^ 2 / 6) * Real.log 2 * Kmu
              * Real.exp (-(cmu * Real.sqrt (Real.log (((N / (q * z) : ℕ)) : ℝ))))))
          ≤ ∑ q ∈ (Finset.Icc 1 A).filter (fun q => 2 * q ≤ A),
              (Real.pi ^ 2 / 6) * Real.log 2 * Kmu * ((1 : ℝ) / (q : ℝ)
                * (Real.log ((A : ℝ) / (q : ℝ)) + 2) ^ 4
                * Real.exp (-((min cDS cmu / 2) * Real.sqrt (Real.log ((A : ℝ) / (q : ℝ)))))) :=
            Finset.sum_le_sum hpt
        _ = (Real.pi ^ 2 / 6) * Real.log 2 * Kmu
              * (∑ q ∈ (Finset.Icc 1 A).filter (fun q => 2 * q ≤ A),
                  (1 : ℝ) / (q : ℝ) * (Real.log ((A : ℝ) / (q : ℝ)) + 2) ^ 4
                    * Real.exp (-((min cDS cmu / 2) * Real.sqrt (Real.log ((A : ℝ) / (q : ℝ)))))) := by
            rw [Finset.mul_sum]
        _ ≤ (Real.pi ^ 2 / 6) * Real.log 2 * Kmu * KD1 := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_) hD1'
            intro q hq1' hq2'
            positivity
    have hH2 : (∑ q ∈ (Finset.Icc 1 A).filter (fun q => 2 * q ≤ A),
          (1 : ℝ) / (q : ℝ) * (KDS * (Real.log (Qf z N q) + 2) ^ 4
              * Real.exp (-(cDS * Real.sqrt (Real.log (((N / (q * z) : ℕ)) : ℝ))))))
        ≤ 16 * KDS * KD1 := by
      have hpt : ∀ q ∈ (Finset.Icc 1 A).filter (fun q => 2 * q ≤ A),
          (1 : ℝ) / (q : ℝ) * (KDS * (Real.log (Qf z N q) + 2) ^ 4
              * Real.exp (-(cDS * Real.sqrt (Real.log (((N / (q * z) : ℕ)) : ℝ)))))
            ≤ KDS * (16 * ((1 : ℝ) / (q : ℝ) * (Real.log ((A : ℝ) / (q : ℝ)) + 2) ^ 4
                * Real.exp (-((min cDS cmu / 2) * Real.sqrt (Real.log ((A : ℝ) / (q : ℝ))))))) := by
        intro q hq
        rw [Finset.mem_filter] at hq
        obtain ⟨hqmem, hq2⟩ := hq
        obtain ⟨hq1, hqA⟩ := Finset.mem_Icc.mp hqmem
        have hq0 : 0 < q := by omega
        have hBeq : N / (q * z) = A / q := by
          rw [hA, Nat.mul_comm q z]
          exact (Nat.div_div_eq_div_mul N z q).symm
        have hlogA0 : 0 ≤ Real.log ((A : ℝ) / (q : ℝ)) := Real.log_nonneg (by
          rw [one_le_div (by exact_mod_cast (by omega : 0 < q))]
          exact_mod_cast hqA)
        have hexp := exp_decay_le (A := A) (B := A / q) (q := q) (c := cDS)
          (c' := min cDS cmu / 2) (log_div_le_four_mul_log_floor A q hq1 hq2) hlogA0
          (by positivity) (by
            have hle : min cDS cmu ≤ cDS := min_le_left _ _
            have := lt_min hcDS hcmu
            linarith)
        rw [hBeq]
        have hQpos : 0 < Qf z N q := by
          rw [Qf]; exact div_pos (by exact_mod_cast (by omega : 0 < N)) (by positivity)
        have hQ2 : Qf z N q ≤ 2 * ((A : ℝ) / (q : ℝ)) := by
          have hh := Qf_le z N q hq1 (by omega) hzN
          rw [← hA] at hh
          simpa only [mul_div_assoc] using hh
        have hlogQf : Real.log (Qf z N q) ≤ Real.log ((A : ℝ) / (q : ℝ)) + Real.log 2 := by
          have h1 : Real.log ((A : ℝ) / (q : ℝ)) + Real.log 2
              = Real.log (((A : ℝ) / (q : ℝ)) * 2) :=
            (Real.log_mul (by positivity) (by norm_num)).symm
          rw [h1]
          apply Real.log_le_log hQpos
          calc Qf z N q ≤ 2 * ((A : ℝ) / (q : ℝ)) := hQ2
            _ = (A : ℝ) / (q : ℝ) * 2 := by ring
        have hlogQf0 : 0 ≤ Real.log (Qf z N q) := by
          apply Real.log_nonneg
          have hh := Nat.cast_div_le (α := ℝ) (m := N) (n := q * z)
          rw [hBeq] at hh
          have hh' : (((A / q : ℕ)) : ℝ) ≤ Qf z N q := by
            simpa [Qf, Nat.cast_mul] using hh
          have h3 : (1 : ℝ) ≤ (((A / q : ℕ)) : ℝ) := by
            have h4 : 1 ≤ A / q := (Nat.le_div_iff_mul_le (by omega : 0 < q)).mpr (by linarith [hqA])
            exact_mod_cast h4
          linarith
        have hpow := log_add_two_pow_le (u := Real.log ((A : ℝ) / (q : ℝ)))
          (v := Real.log (Qf z N q)) hlogA0 hlogQf0 hlogQf
        have hstep : (Real.log (Qf z N q) + 2) ^ 4
            * Real.exp (-(cDS * Real.sqrt (Real.log (((A / q : ℕ)) : ℝ))))
            ≤ 16 * ((Real.log ((A : ℝ) / (q : ℝ)) + 2) ^ 4
              * Real.exp (-((min cDS cmu / 2) * Real.sqrt (Real.log ((A : ℝ) / (q : ℝ)))))) := by
          calc (Real.log (Qf z N q) + 2) ^ 4
                * Real.exp (-(cDS * Real.sqrt (Real.log (((A / q : ℕ)) : ℝ))))
              ≤ 16 * (Real.log ((A : ℝ) / (q : ℝ)) + 2) ^ 4
                * Real.exp (-(cDS * Real.sqrt (Real.log (((A / q : ℕ)) : ℝ)))) := by
                exact mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg _)
            _ ≤ 16 * (Real.log ((A : ℝ) / (q : ℝ)) + 2) ^ 4
                * Real.exp (-((min cDS cmu / 2) * Real.sqrt (Real.log ((A : ℝ) / (q : ℝ))))) := by
                exact mul_le_mul_of_nonneg_left hexp (by positivity)
            _ = 16 * ((Real.log ((A : ℝ) / (q : ℝ)) + 2) ^ 4
                * Real.exp (-((min cDS cmu / 2) * Real.sqrt (Real.log ((A : ℝ) / (q : ℝ)))))) := by ring
        calc (1 : ℝ) / (q : ℝ) * (KDS * (Real.log (Qf z N q) + 2) ^ 4
              * Real.exp (-(cDS * Real.sqrt (Real.log (((A / q : ℕ)) : ℝ)))))
            = ((1 : ℝ) / (q : ℝ) * KDS) * ((Real.log (Qf z N q) + 2) ^ 4
                * Real.exp (-(cDS * Real.sqrt (Real.log (((A / q : ℕ)) : ℝ))))) := by ring
          _ ≤ ((1 : ℝ) / (q : ℝ) * KDS) * (16 * ((Real.log ((A : ℝ) / (q : ℝ)) + 2) ^ 4
                * Real.exp (-((min cDS cmu / 2) * Real.sqrt (Real.log ((A : ℝ) / (q : ℝ))))))) :=
              mul_le_mul_of_nonneg_left hstep (by positivity)
          _ = KDS * (16 * ((1 : ℝ) / (q : ℝ) * (Real.log ((A : ℝ) / (q : ℝ)) + 2) ^ 4
                * Real.exp (-((min cDS cmu / 2) * Real.sqrt (Real.log ((A : ℝ) / (q : ℝ))))))) := by ring
      have hD1' := hD1 A hA1'
      calc (∑ q ∈ (Finset.Icc 1 A).filter (fun q => 2 * q ≤ A),
            (1 : ℝ) / (q : ℝ) * (KDS * (Real.log (Qf z N q) + 2) ^ 4
              * Real.exp (-(cDS * Real.sqrt (Real.log (((N / (q * z) : ℕ)) : ℝ))))))
          ≤ ∑ q ∈ (Finset.Icc 1 A).filter (fun q => 2 * q ≤ A),
              KDS * (16 * ((1 : ℝ) / (q : ℝ) * (Real.log ((A : ℝ) / (q : ℝ)) + 2) ^ 4
                * Real.exp (-((min cDS cmu / 2) * Real.sqrt (Real.log ((A : ℝ) / (q : ℝ))))))) :=
            Finset.sum_le_sum hpt
        _ = KDS * (16 * (∑ q ∈ (Finset.Icc 1 A).filter (fun q => 2 * q ≤ A),
                  (1 : ℝ) / (q : ℝ) * (Real.log ((A : ℝ) / (q : ℝ)) + 2) ^ 4
                    * Real.exp (-((min cDS cmu / 2) * Real.sqrt (Real.log ((A : ℝ) / (q : ℝ))))))) := by
            rw [Finset.mul_sum, Finset.mul_sum]
        _ ≤ KDS * (16 * KD1) := by
            apply mul_le_mul_of_nonneg_left _ hKDS.le
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_) hD1'
            intro q hq1' hq2'
            positivity
        _ = 16 * KDS * KD1 := by ring
    -- ### Piece 3: the "big" sum
    have hbig : (∑ q ∈ (Finset.Icc 1 A).filter (fun q => 2 * q ≤ A),
          (N : ℝ) / (q : ℝ) * |s3DSabs (Qf z N q) (N / (q * z)) - Real.pi ^ 2 / 6|)
        ≤ (N : ℝ) * (16 * (Real.pi ^ 2 / 6) * KM * KD2
            + (Real.pi ^ 2 / 6) * Real.log 2 * Kmu * KD1 + 16 * KDS * KD1) := by
      have hfac : (∑ q ∈ (Finset.Icc 1 A).filter (fun q => 2 * q ≤ A),
            (N : ℝ) / (q : ℝ) * ((Real.pi ^ 2 / 6) * KM / (Real.log (((N / (q * z) : ℕ)) : ℝ)) ^ 2
              + (Real.pi ^ 2 / 6) * Real.log 2 * Kmu
                  * Real.exp (-(cmu * Real.sqrt (Real.log (((N / (q * z) : ℕ)) : ℝ))))
              + KDS * (Real.log (Qf z N q) + 2) ^ 4
                  * Real.exp (-(cDS * Real.sqrt (Real.log (((N / (q * z) : ℕ)) : ℝ))))))
          = (N : ℝ) * (∑ q ∈ (Finset.Icc 1 A).filter (fun q => 2 * q ≤ A),
              (1 : ℝ) / (q : ℝ) * ((Real.pi ^ 2 / 6) * KM / (Real.log (((N / (q * z) : ℕ)) : ℝ)) ^ 2
                + (Real.pi ^ 2 / 6) * Real.log 2 * Kmu
                    * Real.exp (-(cmu * Real.sqrt (Real.log (((N / (q * z) : ℕ)) : ℝ))))
                + KDS * (Real.log (Qf z N q) + 2) ^ 4
                    * Real.exp (-(cDS * Real.sqrt (Real.log (((N / (q * z) : ℕ)) : ℝ)))))) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun q _ => by ring
      have hsplit : (∑ q ∈ (Finset.Icc 1 A).filter (fun q => 2 * q ≤ A),
              (1 : ℝ) / (q : ℝ) * ((Real.pi ^ 2 / 6) * KM / (Real.log (((N / (q * z) : ℕ)) : ℝ)) ^ 2
                + (Real.pi ^ 2 / 6) * Real.log 2 * Kmu
                    * Real.exp (-(cmu * Real.sqrt (Real.log (((N / (q * z) : ℕ)) : ℝ))))
                + KDS * (Real.log (Qf z N q) + 2) ^ 4
                    * Real.exp (-(cDS * Real.sqrt (Real.log (((N / (q * z) : ℕ)) : ℝ))))))
          = (∑ q ∈ (Finset.Icc 1 A).filter (fun q => 2 * q ≤ A),
                (1 : ℝ) / (q : ℝ) * ((Real.pi ^ 2 / 6) * KM / (Real.log (((N / (q * z) : ℕ)) : ℝ)) ^ 2))
            + (∑ q ∈ (Finset.Icc 1 A).filter (fun q => 2 * q ≤ A),
                (1 : ℝ) / (q : ℝ) * ((Real.pi ^ 2 / 6) * Real.log 2 * Kmu
                    * Real.exp (-(cmu * Real.sqrt (Real.log (((N / (q * z) : ℕ)) : ℝ))))))
            + (∑ q ∈ (Finset.Icc 1 A).filter (fun q => 2 * q ≤ A),
                (1 : ℝ) / (q : ℝ) * (KDS * (Real.log (Qf z N q) + 2) ^ 4
                    * Real.exp (-(cDS * Real.sqrt (Real.log (((N / (q * z) : ℕ)) : ℝ)))))) := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun q _ => by ring
      calc (∑ q ∈ (Finset.Icc 1 A).filter (fun q => 2 * q ≤ A),
            (N : ℝ) / (q : ℝ) * |s3DSabs (Qf z N q) (N / (q * z)) - Real.pi ^ 2 / 6|)
          ≤ ∑ q ∈ (Finset.Icc 1 A).filter (fun q => 2 * q ≤ A),
              (N : ℝ) / (q : ℝ) * ((Real.pi ^ 2 / 6) * KM / (Real.log (((N / (q * z) : ℕ)) : ℝ)) ^ 2
                + (Real.pi ^ 2 / 6) * Real.log 2 * Kmu
                    * Real.exp (-(cmu * Real.sqrt (Real.log (((N / (q * z) : ℕ)) : ℝ))))
                + KDS * (Real.log (Qf z N q) + 2) ^ 4
                    * Real.exp (-(cDS * Real.sqrt (Real.log (((N / (q * z) : ℕ)) : ℝ))))) :=
            Finset.sum_le_sum hpt_big
        _ = (N : ℝ) * ((∑ q ∈ (Finset.Icc 1 A).filter (fun q => 2 * q ≤ A),
                (1 : ℝ) / (q : ℝ) * ((Real.pi ^ 2 / 6) * KM / (Real.log (((N / (q * z) : ℕ)) : ℝ)) ^ 2))
            + (∑ q ∈ (Finset.Icc 1 A).filter (fun q => 2 * q ≤ A),
                (1 : ℝ) / (q : ℝ) * ((Real.pi ^ 2 / 6) * Real.log 2 * Kmu
                    * Real.exp (-(cmu * Real.sqrt (Real.log (((N / (q * z) : ℕ)) : ℝ))))))
            + (∑ q ∈ (Finset.Icc 1 A).filter (fun q => 2 * q ≤ A),
                (1 : ℝ) / (q : ℝ) * (KDS * (Real.log (Qf z N q) + 2) ^ 4
                    * Real.exp (-(cDS * Real.sqrt (Real.log (((N / (q * z) : ℕ)) : ℝ))))))) := by
            rw [hfac, hsplit]
        _ ≤ (N : ℝ) * (16 * (Real.pi ^ 2 / 6) * KM * KD2
              + (Real.pi ^ 2 / 6) * Real.log 2 * Kmu * KD1 + 16 * KDS * KD1) := by
            apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
            linarith [hF, hG, hH2]
    -- ### Piece 4: the "small" range
    have hsmall : (∑ q ∈ (Finset.Icc 1 A).filter (fun q => ¬ (2 * q ≤ A)),
          (N : ℝ) / (q : ℝ) * |s3DSabs (Qf z N q) (N / (q * z)) - Real.pi ^ 2 / 6|) ≤ (N : ℝ) * 40 := by
      have hpt : ∀ q ∈ (Finset.Icc 1 A).filter (fun q => ¬ (2 * q ≤ A)),
          (N : ℝ) / (q : ℝ) * |s3DSabs (Qf z N q) (N / (q * z)) - Real.pi ^ 2 / 6|
            ≤ (N : ℝ) / (q : ℝ) * 20 := by
        intro q hq
        rw [Finset.mem_filter] at hq
        obtain ⟨hqmem, hq2⟩ := hq
        obtain ⟨hq1, hqA⟩ := Finset.mem_Icc.mp hqmem
        have hq0 : 0 < q := by omega
        have hB1 : N / (q * z) = 1 := by
          have hle : 1 ≤ N / (q * z) := by
            rw [Nat.le_div_iff_mul_le (by positivity : 0 < q * z)]
            have h := (Nat.le_div_iff_mul_le hz0).mp hqA
            nlinarith [h]
          have hlt : N / (q * z) < 2 := by
            rw [Nat.div_lt_iff_lt_mul (by positivity : 0 < q * z)]
            have h := (Nat.div_lt_iff_lt_mul hz0).mp (not_le.mp hq2)
            nlinarith [h]
          omega
        have hBQ : ((N / (q * z) : ℕ) : ℝ) ≤ Qf z N q := by
          rw [Qf]
          simpa [Nat.cast_mul] using (Nat.cast_div_le (α := ℝ) (m := N) (n := q * z))
        have hQ1 : (1 : ℝ) ≤ Qf z N q := by
          have hh := hBQ
          rw [hB1] at hh
          simpa using hh
        have hQ2 : Qf z N q < 2 := by
          have hlt : Qf z N q < ((N / (q * z) : ℕ) : ℝ) + 1 := by
            rw [Qf]
            have hh := div_lt_div_floor_add_one N (q * z) (by positivity : 0 < q * z)
            push_cast at hh
            exact hh
          rw [hB1] at hlt; norm_num at hlt; exact hlt
        have hlogQ0 : 0 ≤ Real.log (Qf z N q) := Real.log_nonneg hQ1
        have hlogQ1 : Real.log (Qf z N q) < 1 := by
          have hQpos : 0 < Qf z N q := by linarith
          have h := Real.log_le_sub_one_of_pos hQpos
          linarith
        have hto : |(Real.log (Qf z N q) - 1) ^ 2 + 1 - Real.pi ^ 2 / 6| ≤ 20 := by
          have h2 : (Real.log (Qf z N q) - 1) ^ 2 ≤ 1 := by
            have h1 : |Real.log (Qf z N q) - 1| ≤ 1 := by
              rw [abs_le]; constructor <;> linarith
            nlinarith [abs_nonneg (Real.log (Qf z N q) - 1),
              sq_abs (Real.log (Qf z N q) - 1)]
          have h5 : |1 - Real.pi ^ 2 / 6| ≤ 2 := by
            have h3 : Real.pi ^ 2 / 6 < 3 := by nlinarith [Real.pi_lt_four, Real.pi_pos]
            rw [abs_le]; constructor <;> linarith
          have heq : (Real.log (Qf z N q) - 1) ^ 2 + 1 - Real.pi ^ 2 / 6
              = (Real.log (Qf z N q) - 1) ^ 2 + (1 - Real.pi ^ 2 / 6) := by ring
          rw [heq]
          calc |(Real.log (Qf z N q) - 1) ^ 2 + (1 - Real.pi ^ 2 / 6)|
              ≤ |(Real.log (Qf z N q) - 1) ^ 2| + |1 - Real.pi ^ 2 / 6| := abs_add_le _ _
            _ = (Real.log (Qf z N q) - 1) ^ 2 + |1 - Real.pi ^ 2 / 6| := by
                rw [abs_of_nonneg (sq_nonneg _)]
            _ ≤ 1 + 2 := by linarith
            _ ≤ 20 := by norm_num
        rw [hB1, s3DSabs_one]
        exact mul_le_mul_of_nonneg_left hto (by positivity)
      calc (∑ q ∈ (Finset.Icc 1 A).filter (fun q => ¬ (2 * q ≤ A)),
            (N : ℝ) / (q : ℝ) * |s3DSabs (Qf z N q) (N / (q * z)) - Real.pi ^ 2 / 6|)
          ≤ ∑ q ∈ (Finset.Icc 1 A).filter (fun q => ¬ (2 * q ≤ A)), (N : ℝ) / (q : ℝ) * 20 :=
            Finset.sum_le_sum hpt
        _ = (N : ℝ) * 20 * (∑ q ∈ (Finset.Icc 1 A).filter (fun q => ¬ (2 * q ≤ A)), (1 : ℝ) / (q : ℝ)) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun q _ => by ring
        _ ≤ (N : ℝ) * 20 * 2 := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            calc (∑ q ∈ (Finset.Icc 1 A).filter (fun q => ¬ (2 * q ≤ A)), (1 : ℝ) / (q : ℝ))
                ≤ ∑ q ∈ (Finset.Icc 1 A).filter (fun q => ¬ (2 * q ≤ A)), (2 : ℝ) / (A : ℝ) := by
                  apply Finset.sum_le_sum
                  intro q hq
                  rw [Finset.mem_filter] at hq
                  obtain ⟨hqmem, hq2⟩ := hq
                  obtain ⟨hq1, hqA⟩ := Finset.mem_Icc.mp hqmem
                  have hq0 : 0 < q := by omega
                  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
                  have hlt : (A : ℝ) < 2 * (q : ℝ) := by
                    have h := not_le.mp hq2
                    exact_mod_cast h
                  rw [div_le_div_iff₀ hqR hApos]
                  linarith
              _ = (((Finset.Icc 1 A).filter (fun q => ¬ (2 * q ≤ A))).card : ℕ) * (2 / (A : ℝ)) := by
                  rw [Finset.sum_const, nsmul_eq_mul]
              _ ≤ (A : ℝ) * (2 / (A : ℝ)) := by
                  apply mul_le_mul_of_nonneg_right _ (by positivity)
                  have hc : ((Finset.Icc 1 A).filter (fun q => ¬ (2 * q ≤ A))).card ≤ (Finset.Icc 1 A).card :=
                    Finset.card_le_card (Finset.filter_subset _ _)
                  have hcA : (Finset.Icc 1 A).card = A := by
                    rw [Nat.card_Icc]; omega
                  rw [hcA] at hc
                  exact_mod_cast hc
              _ = 2 := by field_simp
        _ = (N : ℝ) * 40 := by ring
    -- ### Assembly
    have habs : ∀ q ∈ Finset.Icc 1 A,
        |(N : ℝ) / (q : ℝ) * (s3DSabs (Qf z N q) (N / (q * z)) - Real.pi ^ 2 / 6)|
          = (N : ℝ) / (q : ℝ) * |s3DSabs (Qf z N q) (N / (q * z)) - Real.pi ^ 2 / 6| := by
      intro q hq
      obtain ⟨hq1, _⟩ := Finset.mem_Icc.mp hq
      rw [abs_mul, abs_of_nonneg]
      positivity
    have hsplit2 := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 A) (fun q => 2 * q ≤ A)
      (fun q => (N : ℝ) / (q : ℝ) * |s3DSabs (Qf z N q) (N / (q * z)) - Real.pi ^ 2 / 6|)
    calc |∑ q ∈ Finset.Icc 1 A, (N : ℝ) / (q : ℝ) * (s3DSabs (Qf z N q) (N / (q * z)) - Real.pi ^ 2 / 6)|
        ≤ ∑ q ∈ Finset.Icc 1 A,
            |(N : ℝ) / (q : ℝ) * (s3DSabs (Qf z N q) (N / (q * z)) - Real.pi ^ 2 / 6)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ q ∈ Finset.Icc 1 A,
            (N : ℝ) / (q : ℝ) * |s3DSabs (Qf z N q) (N / (q * z)) - Real.pi ^ 2 / 6| :=
          Finset.sum_congr rfl habs
      _ = (∑ q ∈ (Finset.Icc 1 A).filter (fun q => 2 * q ≤ A),
              (N : ℝ) / (q : ℝ) * |s3DSabs (Qf z N q) (N / (q * z)) - Real.pi ^ 2 / 6|)
          + (∑ q ∈ (Finset.Icc 1 A).filter (fun q => ¬ (2 * q ≤ A)),
              (N : ℝ) / (q : ℝ) * |s3DSabs (Qf z N q) (N / (q * z)) - Real.pi ^ 2 / 6|) := hsplit2.symm
      _ ≤ (N : ℝ) * (16 * (Real.pi ^ 2 / 6) * KM * KD2
              + (Real.pi ^ 2 / 6) * Real.log 2 * Kmu * KD1 + 16 * KDS * KD1) + (N : ℝ) * 40 :=
          add_le_add hbig hsmall
      _ = (N : ℝ) * (16 * (Real.pi ^ 2 / 6) * KM * KD2
              + (Real.pi ^ 2 / 6) * Real.log 2 * Kmu * KD1 + 16 * KDS * KD1 + 40) := by ring
  have htri := abs_sub_le (Work.ZeroDensity.Jutila.s3cont z N)
      (∑ q ∈ Finset.Icc 1 (N / z), (N : ℝ) / (q : ℝ)) ((N : ℝ) * Real.log ((N : ℝ) / (z : ℝ)))
  have hexp : (Real.pi ^ 2 / 6)⁻¹ * ((N : ℝ) * (16 * (Real.pi ^ 2 / 6) * KM * KD2
        + (Real.pi ^ 2 / 6) * Real.log 2 * Kmu * KD1 + 16 * KDS * KD1 + 40)) + C1 * (N : ℝ)
      = ((Real.pi ^ 2 / 6)⁻¹ * (16 * (Real.pi ^ 2 / 6) * KM * KD2
          + (Real.pi ^ 2 / 6) * Real.log 2 * Kmu * KD1 + 16 * KDS * KD1 + 40) + C1) * (N : ℝ) := by
    ring
  linarith [htri, hkey, hmain, hexp]

end

end Work.LinnikAreas.JutilaPieces
