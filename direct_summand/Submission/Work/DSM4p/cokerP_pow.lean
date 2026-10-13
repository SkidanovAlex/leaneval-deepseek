import Mathlib
import Submission.Work.DSM4p.Plan
import Submission.Work.DSM4p.cokerP
import Submission.Work.DSM4p.caseA_bound

namespace Work.DSM4p

universe a

open DSMap DSMap.Mix DSMap.Mix2

section Monomial

variable {p : ℕ} [Fact p.Prime] {R : Type a} [CommRing R]

/-- The **two-case monomial computation** of the generalised characteristic-`p` cokernel
estimate: for root systems `G`, `T`, a modulus exponent `m`, a level shift `c ≥ p^(k+1)·m`,
indices `J`, `I` and a coefficient `b0 : R`, the element
`T k · G k · b0 · x_J(N + c)^I` decomposes as `b + (T 0)^(p·m) · s` with `b ∈ R` and
`s ∈ chartLevel hG T N`.

This is `Work.DSM4p.cokerP_mono` with the extra factor `T k` and with `(m, c)` inserted:
the two cases are `I·p^k < p^J` (the fractional power of `G 0` is a genuine power, so the
element is in `R`) and `I·p^k ≥ p^J` (the `T`-exponent is at least `p·m` times `p^J`, so a
factor `(T 0)^(p·m)` can be taken out). -/
theorem cokerP_mono_pow {G T : ℕ → R} (hG : IsRootSystem p G) (hT : IsRootSystem p T)
    (k m c N J I : ℕ) (hc : p ^ (k + 1) * m ≤ c) (b0 : R) :
    ∃ b : R, ∃ s ∈ chartLevel hG T N,
      algebraMap R (ChartAmbient G) (T k * G k) *
          (algebraMap R (ChartAmbient G) b0 * (chartGen hG T (N + c) J) ^ I) =
        algebraMap R (ChartAmbient G) b +
          algebraMap R (ChartAmbient G) (T 0 ^ (p * m)) * s := by
  rcases Nat.eq_zero_or_pos I with hI0 | hIpos
  · subst hI0
    refine ⟨b0 * (T k * G k), 0, Subalgebra.zero_mem _, ?_⟩
    rw [mul_zero, add_zero, pow_zero, mul_one, ← map_mul]
    congr 1
    ring
  · by_cases hcase : I * p ^ k < p ^ J
    · -- ## Bhatt's second case : `I·p^k < p^J`, the element is in `R`
      have hkJ : k ≤ J := by
        by_contra h
        have h1 : p ^ J < p ^ k := Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (not_le.mp h)
        have h2 : p ^ k ≤ I * p ^ k := by
          calc p ^ k = 1 * p ^ k := (one_mul _).symm
            _ ≤ I * p ^ k := Nat.mul_le_mul_right _ hIpos
        exact absurd hcase (not_lt.mpr (le_trans h1.le h2))
      have hIle : I ≤ p ^ (J - k) := by
        have h3 : p ^ J = p ^ (J - k) * p ^ k := by
          rw [← pow_add, Nat.sub_add_cancel hkJ]
        rw [h3] at hcase
        exact le_of_lt (lt_of_mul_lt_mul_right hcase (Nat.zero_le _))
      have hunit : chartUnit hG k * (chartUnit hG J ^ I)⁻¹ =
          chartUnit hG J ^ (p ^ (J - k) - I) := by
        rw [← mul_right_cancel_iff (a := chartUnit hG J ^ I)]
        rw [mul_assoc, inv_mul_cancel, mul_one,
          mul_comm (chartUnit hG J ^ (p ^ (J - k) - I)) (chartUnit hG J ^ I),
          ← pow_add, Nat.add_sub_cancel' hIle]
        exact (chartUnit_pow_pow hG hkJ).symm
      have hkey : algebraMap R (ChartAmbient G) (G k) * ↑((chartUnit hG J ^ I)⁻¹) =
          algebraMap R (ChartAmbient G) (G J ^ (p ^ (J - k) - I)) := by
        rw [← chartUnit_val hG k, ← Units.val_mul, hunit, Units.val_pow_eq_pow_val,
          chartUnit_val, ← map_pow]
      have htk : T k = T J ^ p ^ (J - k) := (rootSystem_pow_pow hT hkJ).symm
      have hcomb : algebraMap R (ChartAmbient G) (T k) *
            algebraMap R (ChartAmbient G) (T J ^ ((N + c) * I)) =
          algebraMap R (ChartAmbient G) (T J ^ (p ^ (J - k) + (N + c) * I)) := by
        rw [← map_mul, htk, ← pow_add]
      refine ⟨b0 * T J ^ (p ^ (J - k) + (N + c) * I) * G J ^ (p ^ (J - k) - I), 0,
        Subalgebra.zero_mem _, ?_⟩
      rw [mul_zero, add_zero]
      rw [map_mul, chartGen_pow_eq hG T (N + c) J I]
      calc
        algebraMap R (ChartAmbient G) (T k) * algebraMap R (ChartAmbient G) (G k) *
            (algebraMap R (ChartAmbient G) b0 *
              (algebraMap R (ChartAmbient G) (T J ^ ((N + c) * I)) *
                ↑((chartUnit hG J ^ I)⁻¹)))
          = (algebraMap R (ChartAmbient G) (T k) *
              algebraMap R (ChartAmbient G) (T J ^ ((N + c) * I))) *
              (algebraMap R (ChartAmbient G) b0 *
                (algebraMap R (ChartAmbient G) (G k) *
                  ↑((chartUnit hG J ^ I)⁻¹))) := by ring
        _ = algebraMap R (ChartAmbient G) (T J ^ (p ^ (J - k) + (N + c) * I)) *
              (algebraMap R (ChartAmbient G) b0 *
                (algebraMap R (ChartAmbient G) (G k) *
                  ↑((chartUnit hG J ^ I)⁻¹))) := by rw [hcomb]
        _ = algebraMap R (ChartAmbient G) (T J ^ (p ^ (J - k) + (N + c) * I)) *
              (algebraMap R (ChartAmbient G) b0 *
                algebraMap R (ChartAmbient G) (G J ^ (p ^ (J - k) - I))) := by rw [hkey]
        _ = algebraMap R (ChartAmbient G)
              (b0 * T J ^ (p ^ (J - k) + (N + c) * I) * G J ^ (p ^ (J - k) - I)) := by
              rw [show algebraMap R (ChartAmbient G) (T J ^ (p ^ (J - k) + (N + c) * I)) *
                    (algebraMap R (ChartAmbient G) b0 *
                      algebraMap R (ChartAmbient G) (G J ^ (p ^ (J - k) - I)))
                  = (algebraMap R (ChartAmbient G) b0 *
                      algebraMap R (ChartAmbient G) (T J ^ (p ^ (J - k) + (N + c) * I))) *
                      algebraMap R (ChartAmbient G) (G J ^ (p ^ (J - k) - I))
                  from by ring,
                ← map_mul, ← map_mul]
    · -- ## Bhatt's first case : `I·p^k ≥ p^J`, the element is `(T 0)^(p·m)` times level `N`
      have hge : p ^ J ≤ I * p ^ k := le_of_not_gt hcase
      set L : ℕ := max k J with hLdef
      have hkL : k ≤ L := by rw [hLdef]; exact le_max_left k J
      have hJL : J ≤ L := by rw [hLdef]; exact le_max_right k J
      have hbound : p * m * p ^ L ≤ p ^ (L - k) + c * I * p ^ (L - J) :=
        caseA_bound hJL hge hc
      set e : ℕ := p ^ (L - k) + c * I * p ^ (L - J) - p * m * p ^ L with hedef
      have htk : T k = T L ^ p ^ (L - k) := (rootSystem_pow_pow hT hkL).symm
      have htJ : T J = T L ^ p ^ (L - J) := (rootSystem_pow_pow hT hJL).symm
      have hT0L : T L ^ p ^ L = T 0 := hT.pow_pow_zero L
      have hexp : p ^ (L - k) + c * I * p ^ (L - J) = e + p * m * p ^ L := by
        rw [hedef]; exact (Nat.sub_add_cancel hbound).symm
      have hchain : T k * T J ^ (c * I) = T 0 ^ (p * m) * T L ^ e := by
        calc T k * T J ^ (c * I)
            = T L ^ p ^ (L - k) * (T L ^ p ^ (L - J)) ^ (c * I) := by rw [htk, htJ]
          _ = T L ^ p ^ (L - k) * T L ^ (p ^ (L - J) * (c * I)) := by rw [← pow_mul]
          _ = T L ^ (p ^ (L - k) + p ^ (L - J) * (c * I)) := by rw [← pow_add]
          _ = T L ^ (e + p * m * p ^ L) := by
                congr 1
                rw [show p ^ (L - J) * (c * I) = c * I * p ^ (L - J) from by ring, hexp]
          _ = T L ^ (p * m * p ^ L) * T L ^ e := by rw [pow_add]; ring
          _ = (T L ^ p ^ L) ^ (p * m) * T L ^ e := by
                rw [show (T L ^ p ^ L) ^ (p * m) = T L ^ (p * m * p ^ L) from by
                  rw [← pow_mul]; congr 1; ring]
          _ = T 0 ^ (p * m) * T L ^ e := by rw [hT0L]
      have hchain' : algebraMap R (ChartAmbient G) (T k) *
            algebraMap R (ChartAmbient G) (T J ^ (c * I)) =
          algebraMap R (ChartAmbient G) (T 0 ^ (p * m)) *
            algebraMap R (ChartAmbient G) (T L ^ e) := by
        calc algebraMap R (ChartAmbient G) (T k) * algebraMap R (ChartAmbient G) (T J ^ (c * I))
            = algebraMap R (ChartAmbient G) (T k * T J ^ (c * I)) := by rw [map_mul]
          _ = algebraMap R (ChartAmbient G) (T 0 ^ (p * m) * T L ^ e) := by rw [hchain]
          _ = algebraMap R (ChartAmbient G) (T 0 ^ (p * m)) *
              algebraMap R (ChartAmbient G) (T L ^ e) := by rw [map_mul]
      have hcomb2 : algebraMap R (ChartAmbient G) (T L ^ e) *
            (algebraMap R (ChartAmbient G) (G k) * algebraMap R (ChartAmbient G) b0) =
          algebraMap R (ChartAmbient G) (b0 * G k * T L ^ e) := by
        rw [← map_mul, ← map_mul]
        congr 1
        ring
      refine ⟨0, algebraMap R (ChartAmbient G) (b0 * G k * T L ^ e) *
        (chartGen hG T N J) ^ I,
        Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
          (Subalgebra.pow_mem _ (chartGen_mem hG T N J) I), ?_⟩
      rw [map_zero, zero_add]
      calc
        algebraMap R (ChartAmbient G) (T k * G k) *
            (algebraMap R (ChartAmbient G) b0 * (chartGen hG T (N + c) J) ^ I)
          = (algebraMap R (ChartAmbient G) (T k) *
              algebraMap R (ChartAmbient G) (T J ^ (c * I))) *
              (algebraMap R (ChartAmbient G) (G k) * algebraMap R (ChartAmbient G) b0 *
                (chartGen hG T N J) ^ I) := by
              rw [map_mul, chartGen_pow_add_level hG T N c J I]; ring
        _ = (algebraMap R (ChartAmbient G) (T 0 ^ (p * m)) *
              algebraMap R (ChartAmbient G) (T L ^ e)) *
              (algebraMap R (ChartAmbient G) (G k) * algebraMap R (ChartAmbient G) b0 *
                (chartGen hG T N J) ^ I) := by rw [hchain']
        _ = algebraMap R (ChartAmbient G) (T 0 ^ (p * m)) *
              (algebraMap R (ChartAmbient G) (T L ^ e) *
                (algebraMap R (ChartAmbient G) (G k) *
                  algebraMap R (ChartAmbient G) b0) *
                  (chartGen hG T N J) ^ I) := by ring
        _ = algebraMap R (ChartAmbient G) (T 0 ^ (p * m)) *
              (algebraMap R (ChartAmbient G) (b0 * G k * T L ^ e) *
                (chartGen hG T N J) ^ I) := by rw [hcomb2]

end Monomial

/-- The generalised characteristic-`p` cokernel estimate: every element of the
`(N + c)`-st chart level (`c ≥ p^(k+1)·m`) is, after multiplication by `T k · G k`, a base
element plus `(T 0)^(p·m)` times an element of the `N`-th level.  This is
`Work.DSM4p.cokerP` with the modulus `(T 0)^(p·m)` and the level shift `c`. -/
theorem cokerP_pow {p : ℕ} [Fact p.Prime] {R : Type a} [CommRing R] [CharP R p]
    [PerfectRing R p] {G T : ℕ → R} (hG : Work.DSM4p.IsRootSystem p G)
    (hT : Work.DSM4p.IsRootSystem p T) (k m N c : ℕ) (hc : p ^ (k + 1) * m ≤ c)
    (r : Work.DSM4p.chartRing hG T (N + c)) :
    ∃ b : R, ∃ s ∈ Work.DSM4p.chartLevel hG T N,
      algebraMap R (Work.DSM4p.ChartAmbient G) (T k * G k) *
          (r : Work.DSM4p.ChartAmbient G) =
        algebraMap R (Work.DSM4p.ChartAmbient G) b +
          algebraMap R (Work.DSM4p.ChartAmbient G) (T 0 ^ (p * m)) * s := by
  obtain ⟨P, hP⟩ := chartLevel_mem_aeval_range hG T (N + c) r
  choose bb ss hss hdec using fun μ : ℕ →₀ ℕ =>
    cokerP_mono_pow hG hT k m c N (μ.support.sup id)
      (∑ j ∈ μ.support, μ j * p ^ (μ.support.sup id - j)) hc (P.coeff μ)
  refine ⟨∑ μ ∈ P.support, bb μ, ∑ μ ∈ P.support, ss μ,
    Subalgebra.sum_mem _ (fun μ _ => hss μ), ?_⟩
  have hexp : (r : ChartAmbient G) =
      ∑ μ ∈ P.support, algebraMap R (ChartAmbient G) (P.coeff μ) *
        ∏ j ∈ μ.support, (chartGen hG T (N + c) j) ^ (μ j) := by
    conv_lhs => rw [← hP, MvPolynomial.as_sum P]
    rw [map_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [MvPolynomial.aeval_monomial]
    rfl
  calc algebraMap R (ChartAmbient G) (T k * G k) * (r : ChartAmbient G)
      = algebraMap R (ChartAmbient G) (T k * G k) * ∑ μ ∈ P.support,
          (algebraMap R (ChartAmbient G) (P.coeff μ) *
            ∏ j ∈ μ.support, (chartGen hG T (N + c) j) ^ (μ j)) := by
        rw [hexp]
    _ = ∑ μ ∈ P.support, algebraMap R (ChartAmbient G) (T k * G k) *
          (algebraMap R (ChartAmbient G) (P.coeff μ) *
            ∏ j ∈ μ.support, (chartGen hG T (N + c) j) ^ (μ j)) := by
        rw [Finset.mul_sum]
    _ = ∑ μ ∈ P.support, (algebraMap R (ChartAmbient G) (bb μ) +
          algebraMap R (ChartAmbient G) (T 0 ^ (p * m)) * ss μ) := by
        refine Finset.sum_congr rfl fun μ _ => ?_
        rw [prod_chartGen_pow_eq G hG T hT (N + c) μ (μ.support.sup id)
              (fun j hj => Finset.le_sup (f := id) hj),
            hdec μ]
    _ = algebraMap R (ChartAmbient G) (∑ μ ∈ P.support, bb μ) +
          algebraMap R (ChartAmbient G) (T 0 ^ (p * m)) * (∑ μ ∈ P.support, ss μ) := by
        rw [map_sum, Finset.mul_sum, Finset.sum_add_distrib]

end Work.DSM4p
