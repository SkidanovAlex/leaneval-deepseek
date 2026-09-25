import Submission.Commons.Analysis.ExponentialSums.monic_poly_major_arc_approx_coeff

namespace Work.Analysis.ExponentialSums

open MeasureTheory intervalIntegral Finset
open scoped BigOperators
open Commons.Analysis.ExponentialSums

/-- **Major-arc approximation of a Weyl sum for an arbitrary integer polynomial.**  The
generalization of `Commons.Analysis.ExponentialSums.monic_poly_major_arc_approx_coeff` with the
hypothesis `P.Monic` removed (the proof of that result never uses monicity: only
`P.natDegree = d` and the coefficient bound are used).  For `P : ℤ[X]` of degree `d ≥ 2`, `q ≥ 1`,
`N ≥ 1` and `β : ℝ`,

`N⁻¹ ∑_{n<N} e((a/q + β) P n) = S_P(a/q) · ∫_0^1 e(β P(N s)) ds + O(‖coeffs‖₁ (|β| q (N+q)^d / N + q/N))`

where `S_P(a/q) = q⁻¹ ∑_{r<q} e((a/q) P r)`.  This supplies the major-arc input of the `ℓ²` circle
method for an arbitrary (non-monic) integer polynomial, which the corpus only provides for monic
polynomials.  Proof: copy `Submission.Commons.Analysis.ExponentialSums.monic_poly_major_arc_approx_coeff`
verbatim and delete the unused `P.Monic` binder (the file's other lemmas `phase_period`,
`phase_block_bound`, `inv_q_mul_integral_eq`, `card_block_bounds`,
`norm_sum_range_sub_integral_le_lipschitz` are needed too and can be copied or imported). -/
theorem poly_major_arc_approx_coeff (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N q : ℕ) (a : ℤ) (β : ℝ) (P : Polynomial ℤ),
      P.natDegree = d → 1 ≤ q → 1 ≤ N →
      ‖(N : ℂ)⁻¹ * (∑ n ∈ Finset.range N,
            Complex.exp (2 * Real.pi * Complex.I *
              ((((a : ℝ) / (q : ℝ) + β) * ((Polynomial.eval (n : ℤ) P : ℤ) : ℝ) : ℝ) : ℂ)))
          - (q : ℂ)⁻¹ * (∑ r ∈ Finset.range q,
                Complex.exp (2 * Real.pi * Complex.I *
                  (((a : ℝ) / (q : ℝ) * ((Polynomial.eval (r : ℤ) P : ℤ) : ℝ) : ℝ) : ℂ)))
              * (∫ s in (0 : ℝ)..1,
                  Complex.exp (2 * Real.pi * Complex.I *
                    ((β * (Polynomial.eval (((N : ℝ) * s) : ℝ) (P.map (Int.castRingHom ℝ)))) : ℂ)))‖
        ≤ C * (1 + ∑ i ∈ Finset.range (d + 1), |((P.coeff i : ℤ) : ℝ)|)
            * (|β| * (q : ℝ) * ((N : ℝ) + (q : ℝ)) ^ d / (N : ℝ) + (q : ℝ) / (N : ℝ)) := by
  refine ⟨4 * Real.pi * d + 1, by positivity, ?_⟩
  intro N q a β P hPdeg hq hN
  have hq0 : 0 < q := by omega
  have hd1 : 1 ≤ d := by omega
  set Q : Polynomial ℝ := P.map (Int.castRingHom ℝ) with hQdef
  set φ : ℝ → ℂ := fun x => expTwoPiI (β * Q.eval x) with hφdef
  set ψ : ℝ → ℂ := fun x => expTwoPiI (((a:ℝ)/(q:ℝ)) * x) with hψdef
  set Acoef : ℝ := ∑ i ∈ Finset.range (d + 1), |((P.coeff i : ℤ) : ℝ)| with hAcoefdef
  set M : ℝ := (N:ℝ) + (q:ℝ) with hMdef
  set Lc : ℝ := 2 * Real.pi * |β| * (Acoef * (d:ℝ) * M ^ (d-1)) with hLcdef
  set Iv : ℂ := ∫ t in (0:ℝ)..((N:ℝ)/(q:ℝ)), φ ((q:ℝ)*t) with hIvdef
  have hSc : (∑ n ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I *
        ((((a : ℝ) / (q : ℝ) + β) * ((Polynomial.eval (n : ℤ) P : ℤ) : ℝ) : ℝ) : ℂ)))
      = ∑ n ∈ Finset.range N, expTwoPiI (((a : ℝ) / (q : ℝ) + β) * Q.eval (n:ℝ)) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [expTwoPiI_def]
    have h1 : (n:ℝ) = (((n:ℤ)):ℝ) := by push_cast; ring
    rw [h1, hQdef, eval_map_int_cast]
  have hWc : (∑ r ∈ Finset.range q, Complex.exp (2 * Real.pi * Complex.I *
        (((a : ℝ) / (q : ℝ) * ((Polynomial.eval (r : ℤ) P : ℤ) : ℝ) : ℝ) : ℂ)))
      = ∑ r ∈ Finset.range q, expTwoPiI (((a : ℝ) / (q : ℝ)) * Q.eval (r:ℝ)) := by
    apply Finset.sum_congr rfl
    intro r hr
    rw [expTwoPiI_def]
    have h1 : (r:ℝ) = (((r:ℤ)):ℝ) := by push_cast; ring
    rw [h1, hQdef, eval_map_int_cast]
  have hvc : (∫ s in (0:ℝ)..1, Complex.exp (2 * Real.pi * Complex.I *
        ((β * (Polynomial.eval (((N : ℝ) * s) : ℝ) (P.map (Int.castRingHom ℝ)))) : ℂ)))
      = ∫ s in (0:ℝ)..1, φ ((N:ℝ)*s) := by
    apply intervalIntegral.integral_congr
    intro s hs
    simp only [hφdef, ← hQdef, expTwoPiI_def]
    rw [← Complex.ofReal_mul]
  rw [hSc, hWc, hvc]
  set Sp : ℂ := ∑ n ∈ Finset.range N, expTwoPiI (((a:ℝ)/(q:ℝ)+β) * Q.eval (n:ℝ)) with hSpdef
  set Wp : ℂ := ∑ r ∈ Finset.range q, expTwoPiI (((a:ℝ)/(q:ℝ)) * Q.eval (r:ℝ)) with hWpdef
  have hφcont : Continuous φ := by
    rw [hφdef]
    exact continuous_expTwoPiI.comp (continuous_const.mul Q.continuous)
  have hQdeg : Q.natDegree ≤ d := by
    rw [hQdef]
    exact le_trans (Polynomial.natDegree_map_le (f := Int.castRingHom ℝ) (p := P)) (le_of_eq hPdeg)
  have hcoef_eq : (∑ i ∈ Finset.range (d + 1), |Q.coeff i|) = Acoef := by
    rw [hAcoefdef]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hQdef]
    simp [Polynomial.coeff_map]
  have hM1 : (1:ℝ) ≤ M := by
    rw [hMdef]
    have h1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    have h2 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
    linarith
  have hφnorm : ∀ x ∈ Set.Icc (0:ℝ) M, ‖φ x‖ ≤ 1 := by
    intro x hx
    rw [hφdef]
    exact le_of_eq (norm_expTwoPiI _)
  have hLc0 : 0 ≤ Lc := by
    rw [hLcdef]; positivity
  have hφlip : ∀ x ∈ Set.Icc (0:ℝ) M, ∀ y ∈ Set.Icc (0:ℝ) M, ‖φ x - φ y‖ ≤ Lc * |x - y| := by
    intro x hx y hy
    have hb := Commons.Analysis.Polynomial.abs_eval_sub_eval_le Q d hd1 hQdeg hx.1 hy.1 hx.2 hy.2 hM1
    rw [hcoef_eq] at hb
    rw [hφdef]
    calc ‖expTwoPiI (β * Q.eval x) - expTwoPiI (β * Q.eval y)‖
        ≤ 2 * Real.pi * |β * Q.eval x - β * Q.eval y| := norm_expTwoPiI_sub_le _ _
      _ = 2 * Real.pi * |β| * |Q.eval x - Q.eval y| := by
          rw [show β * Q.eval x - β * Q.eval y = β * (Q.eval x - Q.eval y) by ring, abs_mul]
          ring
      _ ≤ 2 * Real.pi * |β| * (Acoef * (d:ℝ) * M ^ (d-1) * |x - y|) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = Lc * |x - y| := by rw [hLcdef]; ring
  have hsplit : Sp = ∑ r ∈ Finset.range q, ψ (Q.eval (r:ℝ)) *
      (∑ p ∈ Finset.range ((N+q-1-r)/q), φ (((p*q+r:ℕ)):ℝ)) := by
    rw [hSpdef]
    rw [sum_range_residue_split (fun n : ℕ => expTwoPiI (((a:ℝ)/(q:ℝ)+β) * Q.eval (n:ℝ))) N q hq0]
    apply Finset.sum_congr rfl
    intro r hr
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [hψdef, hφdef]
    rw [show ((a:ℝ)/(q:ℝ)+β) * Q.eval (((p*q+r:ℕ):ℝ))
        = ((a:ℝ)/(q:ℝ)) * Q.eval (((p*q+r:ℕ):ℝ)) + β * Q.eval (((p*q+r:ℕ):ℝ)) by ring]
    rw [expTwoPiI_add']
    congr 1
    exact phase_period P q hq0 a p r
  have hWeq : Wp = ∑ r ∈ Finset.range q, ψ (Q.eval (r:ℝ)) := by
    rw [hWpdef]
  have hblock : ∀ r ∈ Finset.range q,
      ‖(∑ p ∈ Finset.range ((N+q-1-r)/q), φ (((p*q+r:ℕ)):ℝ)) - Iv‖ ≤ 2 * Lc * M + 1 := by
    intro r hr
    have hrq : r < q := Finset.mem_range.mp hr
    obtain ⟨h1,h2⟩ := card_block_bounds N q r hq hrq
    have hP := phase_block_bound N q r ((N+q-1-r)/q) φ Lc hLc0 hφcont hφlip hφnorm hq hN hrq h1 h2
    rw [← hMdef] at hP
    rw [hIvdef]
    exact hP
  have hkey : (N:ℂ)⁻¹ * Sp - (q:ℂ)⁻¹ * Wp * (∫ s in (0:ℝ)..1, φ ((N:ℝ)*s))
      = (N:ℂ)⁻¹ * ∑ r ∈ Finset.range q, ψ (Q.eval (r:ℝ)) *
          ((∑ p ∈ Finset.range ((N+q-1-r)/q), φ (((p*q+r:ℕ)):ℝ)) - Iv) := by
    rw [hsplit, hWeq]
    have hcov := inv_q_mul_integral_eq N q hq hN φ hφcont
    have hR : (∑ r ∈ Finset.range q, ψ (Q.eval (r:ℝ)) *
          ((∑ p ∈ Finset.range ((N+q-1-r)/q), φ (((p*q+r:ℕ)):ℝ)) - Iv))
        = (∑ r ∈ Finset.range q, ψ (Q.eval (r:ℝ)) *
              (∑ p ∈ Finset.range ((N+q-1-r)/q), φ (((p*q+r:ℕ)):ℝ)))
          - (∑ r ∈ Finset.range q, ψ (Q.eval (r:ℝ))) * Iv := by
      have h1 : (∑ r ∈ Finset.range q, ψ (Q.eval (r:ℝ)) *
            ((∑ p ∈ Finset.range ((N+q-1-r)/q), φ (((p*q+r:ℕ)):ℝ)) - Iv))
          = ∑ r ∈ Finset.range q, (ψ (Q.eval (r:ℝ)) *
              (∑ p ∈ Finset.range ((N+q-1-r)/q), φ (((p*q+r:ℕ)):ℝ))
              - ψ (Q.eval (r:ℝ)) * Iv) :=
        Finset.sum_congr rfl (fun r hr => by ring)
      rw [h1, Finset.sum_sub_distrib, ← Finset.sum_mul]
    rw [hR]
    have hB : (q:ℂ)⁻¹ * (∑ r ∈ Finset.range q, ψ (Q.eval (r:ℝ))) * (∫ s in (0:ℝ)..1, φ ((N:ℝ)*s))
        = (N:ℂ)⁻¹ * ((∑ r ∈ Finset.range q, ψ (Q.eval (r:ℝ))) * Iv) := by
      rw [mul_assoc, mul_comm (∑ r ∈ Finset.range q, ψ (Q.eval (r:ℝ))) (∫ s in (0:ℝ)..1, φ ((N:ℝ)*s)),
        ← mul_assoc, hcov]
      ring
    rw [hB]
    ring
  have hmain : ‖(N:ℂ)⁻¹ * Sp - (q:ℂ)⁻¹ * Wp * (∫ s in (0:ℝ)..1, φ ((N:ℝ)*s))‖
      ≤ (N:ℝ)⁻¹ * ((q:ℝ) * (2 * Lc * M + 1)) := by
    rw [hkey, norm_mul]
    have hNn : ‖(N:ℂ)⁻¹‖ = (N:ℝ)⁻¹ := by rw [norm_inv, Complex.norm_natCast]
    rw [hNn]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc ‖∑ r ∈ Finset.range q, ψ (Q.eval (r:ℝ)) *
          ((∑ p ∈ Finset.range ((N+q-1-r)/q), φ (((p*q+r:ℕ)):ℝ)) - Iv)‖
        ≤ ∑ r ∈ Finset.range q, ‖ψ (Q.eval (r:ℝ)) *
            ((∑ p ∈ Finset.range ((N+q-1-r)/q), φ (((p*q+r:ℕ)):ℝ)) - Iv)‖ := norm_sum_le _ _
      _ = ∑ r ∈ Finset.range q, ‖(∑ p ∈ Finset.range ((N+q-1-r)/q), φ (((p*q+r:ℕ)):ℝ)) - Iv‖ := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [norm_mul, norm_expTwoPiI, one_mul]
      _ ≤ ∑ r ∈ Finset.range q, (2 * Lc * M + 1) := Finset.sum_le_sum hblock
      _ = (q:ℝ) * (2 * Lc * M + 1) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hfin : (N:ℝ)⁻¹ * ((q:ℝ) * (2 * Lc * M + 1))
      ≤ (4 * Real.pi * d + 1) * (1 + Acoef)
          * (|β| * (q:ℝ) * M ^ d / (N:ℝ) + (q:ℝ) / (N:ℝ)) := by
    have hA0 : 0 ≤ Acoef := by rw [hAcoefdef]; positivity
    have hpow : M ^ (d-1) * M = M ^ d := by
      have h := pow_succ' M (d-1)
      rw [show (d-1)+1 = d by omega] at h
      simpa [mul_comm] using h.symm
    have hLce : 2 * Lc * M = 4 * Real.pi * |β| * (Acoef * (d:ℝ)) * M ^ d := by
      rw [hLcdef]
      have : 2 * (2 * Real.pi * |β| * (Acoef * (d:ℝ) * M ^ (d-1))) * M
          = 4 * Real.pi * |β| * (Acoef * (d:ℝ)) * (M ^ (d-1) * M) := by ring
      rw [this, hpow]
    have hZ0 : 0 ≤ |β| * (q:ℝ) * M ^ d / (N:ℝ) := by positivity
    have hqN0 : 0 ≤ (q:ℝ) / (N:ℝ) := by positivity
    have hstep : (N:ℝ)⁻¹ * ((q:ℝ) * (2 * Lc * M + 1))
        = 4 * Real.pi * (d:ℝ) * Acoef * (|β| * (q:ℝ) * M ^ d / (N:ℝ)) + (q:ℝ)/(N:ℝ) := by
      rw [hLce]
      field_simp
    rw [hstep]
    have h1 : 4 * Real.pi * (d:ℝ) * Acoef * (|β| * (q:ℝ) * M ^ d / (N:ℝ))
        ≤ (4 * Real.pi * (d:ℝ) + 1) * (1 + Acoef) * (|β| * (q:ℝ) * M ^ d / (N:ℝ)) := by
      have hA : Acoef ≤ 1 + Acoef := by linarith
      have h4 : (0:ℝ) ≤ 4 * Real.pi * (d:ℝ) := by positivity
      have h1A : 0 ≤ 1 + Acoef := by linarith
      calc 4 * Real.pi * (d:ℝ) * Acoef * (|β| * (q:ℝ) * M ^ d / (N:ℝ))
          = (4 * Real.pi * (d:ℝ)) * Acoef * (|β| * (q:ℝ) * M ^ d / (N:ℝ)) := by ring
        _ ≤ (4 * Real.pi * (d:ℝ)) * (1 + Acoef) * (|β| * (q:ℝ) * M ^ d / (N:ℝ)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA h4) hZ0
        _ ≤ (4 * Real.pi * (d:ℝ) + 1) * (1 + Acoef) * (|β| * (q:ℝ) * M ^ d / (N:ℝ)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) h1A) hZ0
    have h2 : (q:ℝ) / (N:ℝ) ≤ (4 * Real.pi * (d:ℝ) + 1) * (1 + Acoef) * ((q:ℝ) / (N:ℝ)) := by
      have hC : (1:ℝ) ≤ (4 * Real.pi * (d:ℝ) + 1) * (1 + Acoef) := by
        have hp1 : (1:ℝ) ≤ 4 * Real.pi * (d:ℝ) + 1 := by
          have := Real.pi_pos; nlinarith [(by positivity : (0:ℝ) ≤ (d:ℝ))]
        nlinarith [hA0, hp1]
      nlinarith [hqN0, hC]
    calc 4 * Real.pi * (d:ℝ) * Acoef * (|β| * (q:ℝ) * M ^ d / (N:ℝ)) + (q:ℝ)/(N:ℝ)
        ≤ (4 * Real.pi * (d:ℝ) + 1) * (1 + Acoef) * (|β| * (q:ℝ) * M ^ d / (N:ℝ))
          + (4 * Real.pi * (d:ℝ) + 1) * (1 + Acoef) * ((q:ℝ)/(N:ℝ)) := add_le_add h1 h2
      _ = (4 * Real.pi * (d:ℝ) + 1) * (1 + Acoef)
            * (|β| * (q:ℝ) * M ^ d / (N:ℝ) + (q:ℝ)/(N:ℝ)) := by ring
  calc ‖(N:ℂ)⁻¹ * Sp - (q:ℂ)⁻¹ * Wp * (∫ s in (0:ℝ)..1, φ ((N:ℝ)*s))‖
      ≤ (N:ℝ)⁻¹ * ((q:ℝ) * (2 * Lc * M + 1)) := hmain
    _ ≤ (4 * Real.pi * d + 1) * (1 + Acoef)
          * (|β| * (q:ℝ) * M ^ d / (N:ℝ) + (q:ℝ) / (N:ℝ)) := hfin

end Work.Analysis.ExponentialSums
