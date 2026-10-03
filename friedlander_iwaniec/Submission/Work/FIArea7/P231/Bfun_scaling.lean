import Mathlib

namespace Work.FIArea7.P231

/-- Splitting the two real powers of the `(M/g, N/g)` factors into powers of `g`
and of `(M,N)`.  Key algebraic identity behind `Bfun_scaling`. -/
theorem Bfun_scaling {C A g M N : ℝ} (hC : 0 < C) (hA : 0 < A)
    (hM : 1 ≤ M) (hN : 1 ≤ N) (hg : 1 ≤ g) :
    C * (M / g + N / g) ^ ((1 : ℝ) / 12) * ((M / g) * (N / g)) ^ ((11 : ℝ) / 12)
        * (Real.log ((M / g) * (N / g) + 2)) ^ A
      ≤ g ^ (-(23 / 12 : ℝ)) * (C * (M + N) ^ ((1 : ℝ) / 12) * (M * N) ^ ((11 : ℝ) / 12)
          * (Real.log (M * N + 2)) ^ A) := by
  have hgpos : 0 < g := by linarith
  have hMpos : 0 < M := by linarith
  have hNpos : 0 < N := by linarith
  -- `(M/g + N/g)^(1/12) = (M+N)^(1/12) * g^(-1/12)`
  have f1 : (M / g + N / g) ^ ((1 : ℝ) / 12)
      = (M + N) ^ ((1 : ℝ) / 12) * g ^ (-((1 : ℝ) / 12)) := by
    have hMgpos : 0 < M + N := by linarith
    rw [← add_div, div_eq_mul_inv, Real.mul_rpow (le_of_lt hMgpos) (by positivity)]
    congr 1
    rw [Real.inv_rpow (le_of_lt hgpos), Real.rpow_neg (le_of_lt hgpos)]
  -- `((M/g)*(N/g))^(11/12) = (M*N)^(11/12) * g^(-11/6)`
  have f2 : ((M / g) * (N / g)) ^ ((11 : ℝ) / 12)
      = (M * N) ^ ((11 : ℝ) / 12) * g ^ (-((11 : ℝ) / 6)) := by
    have hMNpos : 0 < M * N := by positivity
    have hgg : (M / g) * (N / g) = (M * N) / g ^ 2 := by
      rw [div_mul_div_comm]; ring_nf
    rw [hgg, div_eq_mul_inv, Real.mul_rpow (le_of_lt hMNpos) (by positivity)]
    congr 1
    rw [Real.inv_rpow (by positivity), Real.rpow_neg (by positivity)]
    rw [show (g : ℝ) ^ (2 : ℕ) = g ^ (2 : ℝ) from (Real.rpow_natCast g 2).symm]
    rw [← Real.rpow_mul (le_of_lt hgpos) 2 ((11 : ℝ) / 12)]
    norm_num
  have hneg : g ^ (-((1 : ℝ) / 12)) * g ^ (-((11 : ℝ) / 6)) = g ^ (-(23 / 12 : ℝ)) := by
    rw [← Real.rpow_add hgpos]
    norm_num
  have hfac : (M / g + N / g) ^ ((1 : ℝ) / 12) * ((M / g) * (N / g)) ^ ((11 : ℝ) / 12)
      = (M + N) ^ ((1 : ℝ) / 12) * (M * N) ^ ((11 : ℝ) / 12) * g ^ (-(23 / 12 : ℝ)) := by
    calc (M / g + N / g) ^ ((1 : ℝ) / 12) * ((M / g) * (N / g)) ^ ((11 : ℝ) / 12)
        = ((M + N) ^ ((1 : ℝ) / 12) * g ^ (-((1 : ℝ) / 12)))
            * ((M * N) ^ ((11 : ℝ) / 12) * g ^ (-((11 : ℝ) / 6))) := by rw [f1, f2]
      _ = (M + N) ^ ((1 : ℝ) / 12) * (M * N) ^ ((11 : ℝ) / 12)
            * (g ^ (-((1 : ℝ) / 12)) * g ^ (-((11 : ℝ) / 6))) := by ring
      _ = (M + N) ^ ((1 : ℝ) / 12) * (M * N) ^ ((11 : ℝ) / 12) * g ^ (-(23 / 12 : ℝ)) := by
            rw [hneg]
  -- monotonicity of the logarithmic factor
  have hlogineq : (M / g) * (N / g) ≤ M * N := by
    have hMg : M / g ≤ M := by rw [div_le_iff₀ hgpos]; nlinarith
    have hNg : N / g ≤ N := by rw [div_le_iff₀ hgpos]; nlinarith
    exact mul_le_mul hMg hNg (by positivity) (le_of_lt hMpos)
  have hargpos : 0 < (M / g) * (N / g) + 2 := by positivity
  have hlogle : Real.log ((M / g) * (N / g) + 2) ≤ Real.log (M * N + 2) :=
    Real.log_le_log hargpos (by linarith)
  have hbasenn : 0 ≤ Real.log ((M / g) * (N / g) + 2) := by
    apply Real.log_nonneg
    linarith [(by positivity : (0 : ℝ) ≤ (M / g) * (N / g))]
  have hlog : (Real.log ((M / g) * (N / g) + 2)) ^ A ≤ (Real.log (M * N + 2)) ^ A :=
    Real.rpow_le_rpow hbasenn hlogle (le_of_lt hA)
  have hE : 0 ≤ C * (M + N) ^ ((1 : ℝ) / 12) * (M * N) ^ ((11 : ℝ) / 12)
      * g ^ (-(23 / 12 : ℝ)) := by positivity
  -- rewrite the `(M/g, N/g)` factors as `(M, N)` factors times a power of `g`
  have hCE : C * (M / g + N / g) ^ ((1 : ℝ) / 12) * ((M / g) * (N / g)) ^ ((11 : ℝ) / 12)
      = C * (M + N) ^ ((1 : ℝ) / 12) * (M * N) ^ ((11 : ℝ) / 12) * g ^ (-(23 / 12 : ℝ)) := by
    rw [show C * (M / g + N / g) ^ ((1 : ℝ) / 12) * ((M / g) * (N / g)) ^ ((11 : ℝ) / 12)
          = C * ((M / g + N / g) ^ ((1 : ℝ) / 12)
              * ((M / g) * (N / g)) ^ ((11 : ℝ) / 12)) from by ring]
    rw [hfac]; ring
  rw [hCE]
  rw [show g ^ (-(23 / 12 : ℝ)) * (C * (M + N) ^ ((1 : ℝ) / 12) * (M * N) ^ ((11 : ℝ) / 12)
        * (Real.log (M * N + 2)) ^ A)
      = (C * (M + N) ^ ((1 : ℝ) / 12) * (M * N) ^ ((11 : ℝ) / 12) * g ^ (-(23 / 12 : ℝ)))
        * (Real.log (M * N + 2)) ^ A from by ring]
  exact mul_le_mul_of_nonneg_left hlog hE

end Work.FIArea7.P231
