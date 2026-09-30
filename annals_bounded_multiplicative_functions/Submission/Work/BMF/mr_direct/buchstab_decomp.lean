import Mathlib
import Submission.Work.BMF.mr_direct_defs
import Submission.Commons.NumberTheory.DirichletPolynomial.mv_integral_separated_frequencies

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Buchstab/Ramaré decomposition inequality (`Work.BMF.mr_direct.buchstab_decomp`)

This file proves the requested lemma in the "absolute constant first" form:

`∃ C > 0, ∀ X K P Q a b c S, (hypotheses) → ∫_{-S}^{S} ‖dirPolyM a X‖² ≤ C · [ … ]`.

The main analytic input is the Montgomery–Vaughan large-sieve mean value bound for
`δ`-separated frequencies, `Commons.NumberTheory.DirichletPolynomial.mv_integral_separated_frequencies`:

`∫_A^B ‖sg_i b_i e^{I μ_i t}‖² ≤ (B - A + C/δ) sg_i ‖b_i‖²`,   `δ ≤ |μ_i - μ_j|`.

Applying it with the (logarithmically separated) frequencies `μ_n = -log n` for
`n ∈ [X, 2X]` and coefficients `b_n = a n / n` bounds the left-hand side by
`(2S + 3C₀X) · sg_{X ≤ n ≤ 2X} ‖a n‖²/n²`, which is at most
`(3C₀+2) · (S+X)/X · sg_{X ≤ n ≤ 2X} ‖a n‖²/n` and hence at most the right-hand side
(the first bracket being a nonnegative quantity).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.BMF

open MeasureTheory intervalIntegral
open scoped BigOperators

/-! ### Elementary bounds on `natIcc` -/

lemma natIcc_bounds {X : ℝ} (hX : 1 ≤ X) {p : ℕ} (hp : p ∈ natIcc X (2 * X)) :
    X ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * X := by
  rw [natIcc, Finset.mem_Icc] at hp
  constructor
  · exact le_trans (Nat.le_ceil X) (by exact_mod_cast hp.1)
  · exact le_trans (by exact_mod_cast hp.2) (Nat.floor_le (by linarith))

/-- Distinct naturals in `[X, 2X]` have `log`-separated values by at least `1/(3X)`. -/
lemma log_sep_natIcc {X : ℝ} (hX : 1 ≤ X) {m n : ℕ}
    (hm : m ∈ natIcc X (2 * X)) (hn : n ∈ natIcc X (2 * X)) (hmn : m ≠ n) :
    1 / (3 * X) ≤ |Real.log (m : ℝ) - Real.log (n : ℝ)| := by
  have hm' := natIcc_bounds hX hm
  have hn' := natIcc_bounds hX hn
  have hmp : (0 : ℝ) < (m : ℝ) := by linarith [hm'.1]
  have hnp : (0 : ℝ) < (n : ℝ) := by linarith [hn'.1]
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · have hnl : Real.log (n : ℝ) - Real.log (m : ℝ) = Real.log ((n : ℝ) / (m : ℝ)) := by
      rw [Real.log_div hnp.ne' hmp.ne']
    have hle1 : (1 : ℝ) - (m : ℝ) / (n : ℝ) ≤ Real.log ((n : ℝ) / (m : ℝ)) := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (m : ℝ) / (n : ℝ) by positivity)
      rw [Real.log_div hmp.ne' hnp.ne'] at h
      linarith
    have hnm1 : (1 : ℝ) ≤ (n : ℝ) - (m : ℝ) := by
      have h : m + 1 ≤ n := by omega
      have h2 : ((m : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast h
      linarith
    have hstep : (1 : ℝ) / (3 * X) ≤ (1 : ℝ) - (m : ℝ) / (n : ℝ) := by
      rw [show (1 : ℝ) - (m : ℝ) / (n : ℝ) = ((n : ℝ) - (m : ℝ)) / (n : ℝ) by
            rw [sub_div, div_self hnp.ne']]
      have h1 : (1 : ℝ) / (n : ℝ) ≤ ((n : ℝ) - (m : ℝ)) / (n : ℝ) :=
        div_le_div_of_nonneg_right hnm1 hnp.le
      have h2 : (1 : ℝ) / (3 * X) ≤ (1 : ℝ) / (n : ℝ) := by
        apply one_div_le_one_div_of_le hnp
        linarith [hn'.2]
      linarith
    have hloglt : Real.log (m : ℝ) < Real.log (n : ℝ) := Real.log_lt_log hmp (by exact_mod_cast hlt)
    rw [abs_of_neg (by linarith : Real.log (m : ℝ) - Real.log (n : ℝ) < 0)]
    linarith
  · have hnl : Real.log (m : ℝ) - Real.log (n : ℝ) = Real.log ((m : ℝ) / (n : ℝ)) := by
      rw [Real.log_div hmp.ne' hnp.ne']
    have hle1 : (1 : ℝ) - (n : ℝ) / (m : ℝ) ≤ Real.log ((m : ℝ) / (n : ℝ)) := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (n : ℝ) / (m : ℝ) by positivity)
      rw [Real.log_div hnp.ne' hmp.ne'] at h
      linarith
    have hnm1 : (1 : ℝ) ≤ (m : ℝ) - (n : ℝ) := by
      have h : n + 1 ≤ m := by omega
      have h2 : ((n : ℕ) : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast h
      linarith
    have hstep : (1 : ℝ) / (3 * X) ≤ (1 : ℝ) - (n : ℝ) / (m : ℝ) := by
      rw [show (1 : ℝ) - (n : ℝ) / (m : ℝ) = ((m : ℝ) - (n : ℝ)) / (m : ℝ) by
            rw [sub_div, div_self hmp.ne']]
      have h1 : (1 : ℝ) / (m : ℝ) ≤ ((m : ℝ) - (n : ℝ)) / (m : ℝ) :=
        div_le_div_of_nonneg_right hnm1 hmp.le
      have h2 : (1 : ℝ) / (3 * X) ≤ (1 : ℝ) / (m : ℝ) := by
        apply one_div_le_one_div_of_le hmp
        linarith [hm'.2]
      linarith
    have hloglt : Real.log (n : ℝ) < Real.log (m : ℝ) := Real.log_lt_log hnp (by exact_mod_cast hgt)
    rw [abs_of_pos (by linarith : 0 < Real.log (m : ℝ) - Real.log (n : ℝ))]
    linarith

/-- `n^{-(1+it)} = n^{-1} · exp(I·(-log n)·t)` for `n ≥ 1`. -/
lemma cpow_neg_one_sub_I (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    (n : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))
      = (n : ℂ)⁻¹ *
          Complex.exp (Complex.I * (((-(Real.log (n : ℝ)) : ℝ) : ℂ) * (t : ℂ))) := by
  have h0 : (n : ℂ) ≠ 0 := by
    exact_mod_cast (by omega : n ≠ 0)
  rw [show -(1 + Complex.I * (t : ℂ)) = (-1 : ℂ) + (-(Complex.I * (t : ℂ))) by ring]
  rw [Complex.cpow_add _ _ h0, Complex.cpow_neg_one]
  congr 1
  rw [Complex.cpow_def_of_ne_zero h0, ← Complex.natCast_log]
  congr 1
  push_cast
  ring

namespace mrDirect

/-- **Mean-value reduction.**  For `X ≥ 1`, `S ≥ 0` and any coefficient sequence `a`,
the mean square of `dirPolyM a X` over `[-S, S]` is at most
`(2S + 3C₀X) · sg_{X ≤ n ≤ 2X} ‖a n‖²/n²`, where `C₀` is the constant of the
Montgomery–Vaughan large sieve inequality `mv_integral_separated_frequencies`. -/
lemma dirPolyM_mean_value (C₀ : ℝ)
    (hC₀ : ∀ (δ : ℝ), 0 < δ → ∀ (N : ℕ) (μ : Fin N → ℝ) (b : Fin N → ℂ),
      (∀ i j, i ≠ j → δ ≤ |μ i - μ j|) → ∀ (A B : ℝ), A ≤ B →
        (∫ t in A..B, ‖∑ n, b n * Complex.exp (Complex.I * ((μ n : ℂ) * (t : ℂ)))‖ ^ 2)
          ≤ (B - A + C₀ / δ) * ∑ n, ‖b n‖ ^ 2)
    (a : ℕ → ℂ) (X S : ℝ) (hX : 1 ≤ X) (hS : 0 ≤ S) :
    (∫ t in (-S)..S, ‖dirPolyM a X t‖ ^ 2)
      ≤ (2 * S + 3 * C₀ * X) * ∑ n ∈ natIcc X (2 * X), ‖a n‖ ^ 2 / (n : ℝ) ^ 2 := by
  set N := (natIcc X (2 * X)).card with hN
  set e : ↥(natIcc X (2 * X)) ≃ Fin N := Finset.equivFin _ with he
  set b : Fin N → ℂ := fun i =>
    a ((e.symm i : ↥(natIcc X (2 * X))) : ℕ) /
      (((e.symm i : ↥(natIcc X (2 * X))) : ℕ) : ℂ) with hb
  set μ : Fin N → ℝ := fun i => -(Real.log (((e.symm i : ↥(natIcc X (2 * X))) : ℕ) : ℝ)) with hmu
  have hδ : 0 < 1 / (3 * X) := by positivity
  have hsep : ∀ i j : Fin N, i ≠ j → 1 / (3 * X) ≤ |μ i - μ j| := by
    intro i j hij
    have hne : (((e.symm i : ↥(natIcc X (2 * X))) : ℕ)) ≠
        (((e.symm j : ↥(natIcc X (2 * X))) : ℕ)) := by
      intro h'
      exact hij (e.symm.injective (Subtype.coe_injective h'))
    have hi : (((e.symm i : ↥(natIcc X (2 * X))) : ℕ)) ∈ natIcc X (2 * X) := (e.symm i).2
    have hj : (((e.symm j : ↥(natIcc X (2 * X))) : ℕ)) ∈ natIcc X (2 * X) := (e.symm j).2
    have hkey := log_sep_natIcc hX hi hj hne
    rw [hmu]
    simp only []
    rw [show -(Real.log (((e.symm i : ↥(natIcc X (2 * X))) : ℕ) : ℝ))
        - -(Real.log (((e.symm j : ↥(natIcc X (2 * X))) : ℕ) : ℝ))
        = Real.log (((e.symm j : ↥(natIcc X (2 * X))) : ℕ) : ℝ)
          - Real.log (((e.symm i : ↥(natIcc X (2 * X))) : ℕ) : ℝ) by ring, abs_sub_comm]
    exact hkey
  have hsum_eq : ∀ t : ℝ, dirPolyM a X t
      = ∑ i : Fin N, b i * Complex.exp (Complex.I * ((μ i : ℂ) * (t : ℂ))) := by
    intro t
    rw [dirPolyM]
    rw [← Finset.sum_attach (natIcc X (2 * X))
          (fun n => a n * (n : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))),
        ← Finset.univ_eq_attach (natIcc X (2 * X))]
    rw [← Equiv.sum_comp e.symm (fun x : ↥(natIcc X (2 * X)) =>
          a ((x : ℕ)) * (((x : ℕ)) : ℂ) ^ (-(1 + Complex.I * (t : ℂ))))]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hb, hmu]
    have hn1 : 1 ≤ (((e.symm i : ↥(natIcc X (2 * X))) : ℕ)) := by
      have hmem : (((e.symm i : ↥(natIcc X (2 * X))) : ℕ)) ∈ natIcc X (2 * X) := (e.symm i).2
      have hb1 := natIcc_bounds hX hmem
      have : (1 : ℝ) ≤ ((((e.symm i : ↥(natIcc X (2 * X))) : ℕ)) : ℝ) := by linarith [hb1.1]
      exact_mod_cast this
    rw [cpow_neg_one_sub_I _ hn1 t]
    ring
  have hint : (∫ t in (-S)..S, ‖dirPolyM a X t‖ ^ 2)
      = ∫ t in (-S)..S,
          ‖∑ i : Fin N, b i * Complex.exp (Complex.I * ((μ i : ℂ) * (t : ℂ)))‖ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t _
    exact congrArg (fun z => ‖z‖ ^ 2) (hsum_eq t)
  have hS2 : (∑ i : Fin N, ‖b i‖ ^ 2) = ∑ n ∈ natIcc X (2 * X), ‖a n‖ ^ 2 / (n : ℝ) ^ 2 := by
    rw [← Equiv.sum_comp e (fun i : Fin N => ‖b i‖ ^ 2)]
    have h1 : ∀ x : ↥(natIcc X (2 * X)),
        ‖b (e x)‖ ^ 2 = ‖a ((x : ℕ)) / (((x : ℕ)) : ℂ)‖ ^ 2 := by
      intro x; simp only [hb]; rw [Equiv.symm_apply_apply]
    simp only [h1]
    rw [← Finset.sum_attach (natIcc X (2 * X)) (fun n => ‖a n‖ ^ 2 / (n : ℝ) ^ 2)]
    rw [Finset.univ_eq_attach]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [norm_div, Complex.norm_natCast, div_pow]
  have hls := hC₀ (1 / (3 * X)) hδ N μ b hsep (-S) S (by linarith)
  have hcoef : S - (-S) + C₀ / (1 / (3 * X)) = 2 * S + 3 * C₀ * X := by
    rw [one_div, div_inv_eq_mul]; ring
  calc (∫ t in (-S)..S, ‖dirPolyM a X t‖ ^ 2)
      = ∫ t in (-S)..S,
          ‖∑ i : Fin N, b i * Complex.exp (Complex.I * ((μ i : ℂ) * (t : ℂ)))‖ ^ 2 := hint
    _ ≤ (S - (-S) + C₀ / (1 / (3 * X))) * ∑ i : Fin N, ‖b i‖ ^ 2 := hls
    _ = (2 * S + 3 * C₀ * X) * ∑ n ∈ natIcc X (2 * X), ‖a n‖ ^ 2 / (n : ℝ) ^ 2 := by
        rw [hcoef, hS2]

end mrDirect

namespace mr_direct

open MeasureTheory intervalIntegral
open scoped BigOperators

theorem buchstab_decomp :
    ∃ C : ℝ, 0 < C ∧
      ∀ (X K P Q : ℝ) (a b c : ℕ → ℂ) (S : ℝ), 1 ≤ X → 1 ≤ K → 2 ≤ P → P ≤ Q →
      (∀ n, ‖a n‖ ≤ 1) → (∀ m, ‖b m‖ ≤ 1) → (∀ p, ‖c p‖ ≤ 1) →
      (∀ m p : ℕ, Nat.Prime p → P ≤ (p : ℝ) → (p : ℝ) ≤ Q → ¬ p ∣ m →
        a (m * p) = b m * c p) → 0 ≤ S →
      (∫ t in (-S)..S, ‖Work.BMF.mrDirect.dirPolyM a X t‖ ^ 2) ≤
        C * (K * Real.log (Q / P) *
              (∑ j ∈ Work.BMF.mrDirect.indexSet K P Q,
                ∫ t in (-S)..S,
                  ‖Work.BMF.mrDirect.primePoly c K j t *
                    Work.BMF.mrDirect.remPoly b P Q K X j t‖ ^ 2)
          + (S + X) / X * (1 / K + 1 / P +
              ∑ n ∈ Work.BMF.natIcc X (2 * X), ‖a n‖ ^ 2 / n)) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ :=
    Commons.NumberTheory.DirichletPolynomial.mv_integral_separated_frequencies
  refine ⟨3 * C₀ + 2, by positivity, ?_⟩
  intro X K P Q a b c S hX hK hP hPQ ha hb hc hmul hS
  have hXpos : 0 < X := by linarith
  have hKpos : 0 < K := by linarith
  have hPpos : 0 < P := by linarith
  set sg : ℝ := ∑ n ∈ Work.BMF.natIcc X (2 * X), ‖a n‖ ^ 2 / (n : ℝ) with hsgdef
  set sg2 : ℝ := ∑ n ∈ Work.BMF.natIcc X (2 * X), ‖a n‖ ^ 2 / (n : ℝ) ^ 2 with hsg2def
  have hsgnn : 0 ≤ sg := by
    rw [hsgdef]; exact Finset.sum_nonneg fun n _ => by positivity
  have hmain := Work.BMF.mrDirect.dirPolyM_mean_value C₀ hC₀ a X S hX hS
  rw [← hsg2def] at hmain
  have hstep1 : sg2 ≤ (1 / X) * sg := by
    rw [hsg2def, hsgdef, Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    have hnX : X ≤ (n : ℝ) := (natIcc_bounds hX hn).1
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hnn : (0 : ℝ) ≤ ‖a n‖ ^ 2 / (n : ℝ) := by positivity
    have h1n : (1 : ℝ) / (n : ℝ) ≤ 1 / X := one_div_le_one_div_of_le hXpos hnX
    have hsplit : ‖a n‖ ^ 2 / (n : ℝ) ^ 2 = (‖a n‖ ^ 2 / (n : ℝ)) * (1 / (n : ℝ)) := by
      field_simp
    calc ‖a n‖ ^ 2 / (n : ℝ) ^ 2 = (‖a n‖ ^ 2 / (n : ℝ)) * (1 / (n : ℝ)) := hsplit
      _ ≤ (‖a n‖ ^ 2 / (n : ℝ)) * (1 / X) := mul_le_mul_of_nonneg_left h1n hnn
      _ = 1 / X * (‖a n‖ ^ 2 / (n : ℝ)) := by ring
  have hstep2 : (2 * S + 3 * C₀ * X) * (1 / X) ≤ (3 * C₀ + 2) * ((S + X) / X) := by
    rw [mul_one_div, ← mul_div_assoc, div_le_div_iff_of_pos_right hXpos]
    nlinarith [hC₀pos, hS, hKpos]
  have hkey : (2 * S + 3 * C₀ * X) * sg2 ≤ (3 * C₀ + 2) * ((S + X) / X) * sg := by
    have h1 : (2 * S + 3 * C₀ * X) * sg2 ≤ (2 * S + 3 * C₀ * X) * ((1 / X) * sg) :=
      mul_le_mul_of_nonneg_left hstep1 (by positivity)
    have h2 : (2 * S + 3 * C₀ * X) * ((1 / X) * sg) ≤ ((3 * C₀ + 2) * ((S + X) / X)) * sg := by
      rw [show (2 * S + 3 * C₀ * X) * ((1 / X) * sg) = ((2 * S + 3 * C₀ * X) * (1 / X)) * sg by ring]
      exact mul_le_mul_of_nonneg_right hstep2 hsgnn
    linarith
  have hfinal : (3 * C₀ + 2) * ((S + X) / X * sg)
      ≤ (3 * C₀ + 2) * (K * Real.log (Q / P) *
            (∑ j ∈ Work.BMF.mrDirect.indexSet K P Q,
              ∫ t in (-S)..S, ‖Work.BMF.mrDirect.primePoly c K j t *
                Work.BMF.mrDirect.remPoly b P Q K X j t‖ ^ 2)
          + (S + X) / X * (1 / K + 1 / P + sg)) := by
    have hCpos : (0 : ℝ) < 3 * C₀ + 2 := by positivity
    apply mul_le_mul_of_nonneg_left _ hCpos.le
    have hlog : 0 ≤ Real.log (Q / P) :=
      Real.log_nonneg ((le_div_iff₀ hPpos).mpr (by simpa using hPQ))
    have hterm1 : 0 ≤ K * Real.log (Q / P) *
        (∑ j ∈ Work.BMF.mrDirect.indexSet K P Q,
          ∫ t in (-S)..S, ‖Work.BMF.mrDirect.primePoly c K j t *
            Work.BMF.mrDirect.remPoly b P Q K X j t‖ ^ 2) := by
      apply mul_nonneg (mul_nonneg hKpos.le hlog)
      refine Finset.sum_nonneg fun j _ => ?_
      exact intervalIntegral.integral_nonneg_of_forall (by linarith) (fun u => by positivity)
    have hterm2 : (S + X) / X * sg ≤ (S + X) / X * (1 / K + 1 / P + sg) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have h1 : (0 : ℝ) ≤ 1 / K := by positivity
      have h2 : (0 : ℝ) ≤ 1 / P := by positivity
      linarith
    linarith
  calc (∫ t in (-S)..S, ‖Work.BMF.mrDirect.dirPolyM a X t‖ ^ 2)
      ≤ (2 * S + 3 * C₀ * X) * sg2 := hmain
    _ ≤ (3 * C₀ + 2) * ((S + X) / X) * sg := hkey
    _ = (3 * C₀ + 2) * ((S + X) / X * sg) := by ring
    _ ≤ (3 * C₀ + 2) * (K * Real.log (Q / P) *
            (∑ j ∈ Work.BMF.mrDirect.indexSet K P Q,
              ∫ t in (-S)..S, ‖Work.BMF.mrDirect.primePoly c K j t *
                Work.BMF.mrDirect.remPoly b P Q K X j t‖ ^ 2)
          + (S + X) / X * (1 / K + 1 / P + sg)) := hfinal

end mr_direct

end Work.BMF
