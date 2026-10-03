import Mathlib

namespace Work.Peluse.Ulower.StepLe

/-- Elementary coefficient comparison: `(9/4)·(5/2)^{2(K-1)} ≤ 4·3^{2(K-1)}`
(the geometric factor of the "cleared" estimate). -/
private lemma coef_le (K : ℕ) : (9:ℝ)/4 * ((5:ℝ)/2)^(2*(K-1)) ≤ 4 * 3^(2*(K-1)) := by
  have h5 : ((5:ℝ)/2)^(2*(K-1)) = (((5:ℝ)/2)^2)^(K-1) := by rw [← pow_mul]
  have h3 : (3:ℝ)^(2*(K-1)) = ((3:ℝ)^2)^(K-1) := by rw [← pow_mul]
  rw [h5, h3]
  have hmono : (((5:ℝ)/2)^2)^(K-1) ≤ ((3:ℝ)^2)^(K-1) :=
    pow_le_pow_left₀ (by positivity) (by norm_num) (K-1)
  have h9 : (0:ℝ) ≤ ((3:ℝ)^2)^(K-1) := by positivity
  have h1 : (9:ℝ)/4 * (((5:ℝ)/2)^2)^(K-1) ≤ (9:ℝ)/4 * ((3:ℝ)^2)^(K-1) := by linarith
  have h2 : (9:ℝ)/4 * ((3:ℝ)^2)^(K-1) ≤ 4 * ((3:ℝ)^2)^(K-1) :=
    mul_le_mul_of_nonneg_right (by norm_num : (9:ℝ)/4 ≤ 4) h9
  linarith

/-- The "cleared" form of the arithmetic step: from `θ·B ≤ (3/2)·A·Ns` and
`θ·L ≤ (5/2)·A·Ns` one gets `θ^{2K} B² L^{2(K-1)} ≤ 4·A^{2K}·3^{2(K-1)}·Ns^{2K}`. -/
private lemma mainEst {K : ℕ} (hK : 1 ≤ K) {θ B L A Ns : ℝ}
    (hθ0 : 0 < θ) (hB : 0 < B) (hL : 0 < L) (hA : 1 ≤ A) (hNs : 0 < Ns)
    (hθB : θ*B ≤ (3:ℝ)/2*(A*Ns)) (hθL : θ*L ≤ (5:ℝ)/2*(A*Ns)) :
    θ^(2*K)*B^2*L^(2*(K-1)) ≤ 4*A^(2*K)*3^(2*(K-1))*Ns^(2*K) := by
  have hid : θ^(2*K)*B^2*L^(2*(K-1)) = (θ*B)^2*(θ*L)^(2*(K-1)) := by
    have h2 : 2*K = 2*(K-1) + 2 := by omega
    rw [h2, pow_add, mul_pow]
    ring
  rw [hid]
  have h1 : (θ*B)^2 ≤ ((3:ℝ)/2*(A*Ns))^2 := pow_le_pow_left₀ (by positivity) hθB 2
  have h2 : (θ*L)^(2*(K-1)) ≤ ((5:ℝ)/2*(A*Ns))^(2*(K-1)) :=
    pow_le_pow_left₀ (by positivity) hθL _
  have h3 : (θ*B)^2*(θ*L)^(2*(K-1)) ≤ ((3:ℝ)/2*(A*Ns))^2*((5:ℝ)/2*(A*Ns))^(2*(K-1)) :=
    mul_le_mul h1 h2 (by positivity) (by positivity)
  have hAs : (A*Ns)^2 * (A*Ns)^(2*(K-1)) = (A*Ns)^(2*K) := by
    rw [← pow_add]; congr 1; omega
  have h4 : ((3:ℝ)/2*(A*Ns))^2*((5:ℝ)/2*(A*Ns))^(2*(K-1)) ≤
      4*A^(2*K)*3^(2*(K-1))*Ns^(2*K) := by
    calc ((3:ℝ)/2*(A*Ns))^2*((5:ℝ)/2*(A*Ns))^(2*(K-1))
        = (((3:ℝ)/2)^2*((5:ℝ)/2)^(2*(K-1))) * ((A*Ns)^2*(A*Ns)^(2*(K-1))) := by
          rw [mul_pow, mul_pow]; ring
      _ = (((3:ℝ)/2)^2*((5:ℝ)/2)^(2*(K-1))) * (A*Ns)^(2*K) := by rw [hAs]
      _ ≤ (4*3^(2*(K-1))) * (A*Ns)^(2*K) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have := coef_le K
          norm_num at this ⊢
          linarith
      _ = 4*A^(2*K)*3^(2*(K-1))*Ns^(2*K) := by rw [mul_pow]; ring
  linarith

lemma levelTwoArith {K : ℕ} (hK : 1 ≤ K) {cmin Cd θ eta D Ns L L₀ B A : ℝ}
    (hcmin : 0 < cmin) (hCd : 0 < Cd) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hD : 0 < D) (hNs : 0 < Ns) (hL : 0 < L) (hB : 0 < B)
    (hA : 1 ≤ A) (hL₀1 : 1 ≤ L₀) (hL₀A : L₀ ≤ A * Ns)
    (hη : cmin * θ ≤ eta)
    (hcard : θ * (2 * B + 1) ≤ 2 * L₀ + 1)
    (hLB : L ≤ L₀ + B) :
    cmin * θ * B⁻¹ ^ 2 * (Cd * eta ^ K * (D / L) ^ K * L) ^ 2 ≥
      cmin ^ (1 + 2 * K) * Cd ^ 2 / (4 * A ^ (2 * K) * 3 ^ (2 * (K - 1))) *
        θ ^ (4 * K + 1) * (D / Ns) ^ (2 * K) := by
  -- `θ·B ≤ (3/2)·L₀` and `θ·L ≤ (5/2)·L₀ ≤ (5/2)·A·Ns`
  have hθB : θ * B ≤ (3:ℝ)/2 * (A * Ns) := by
    have h1 : θ * B ≤ (3:ℝ)/2 * L₀ := by nlinarith [hcard, hθ0.le, hL₀1]
    nlinarith [h1, hL₀A]
  have hθL : θ * L ≤ (5:ℝ)/2 * (A * Ns) := by
    have h1 : θ * L ≤ θ * (L₀ + B) := by nlinarith [hLB, hθ0]
    have h2 : θ * L₀ ≤ L₀ := by nlinarith [hθ1, hL₀1]
    nlinarith [h1, h2, hθB, hL₀A]
  -- the two independent estimates
  have hβ := mainEst hK hθ0 hB hL hA hNs hθB hθL
  have hα : cmin ^ (2*K) * θ ^ (2*K) ≤ eta ^ (2*K) := by
    have h1 : (cmin*θ) ^ (2*K) ≤ eta ^ (2*K) := pow_le_pow_left₀ (by positivity) hη (2*K)
    rwa [mul_pow] at h1
  have h4nn : (0:ℝ) ≤ 4 * A ^ (2*K) * 3 ^ (2*(K-1)) * Ns ^ (2*K) := by positivity
  -- the cleared inequality
  have hk : cmin ^ (2*K) * θ ^ (4*K) * B^2 * L ^ (2*(K-1)) ≤
      (4 * A ^ (2*K) * 3 ^ (2*(K-1)) * Ns ^ (2*K)) * eta ^ (2*K) := by
    have hθ4 : θ ^ (4*K) = θ ^ (2*K) * θ ^ (2*K) := by rw [← pow_add]; congr 1; omega
    calc cmin ^ (2*K) * θ ^ (4*K) * B^2 * L ^ (2*(K-1))
        = (cmin ^ (2*K) * θ ^ (2*K)) * (θ ^ (2*K) * B^2 * L ^ (2*(K-1))) := by
          rw [hθ4]; ring
      _ ≤ (cmin ^ (2*K) * θ ^ (2*K)) * (4 * A ^ (2*K) * 3 ^ (2*(K-1)) * Ns ^ (2*K)) :=
          mul_le_mul_of_nonneg_left hβ (by positivity)
      _ ≤ eta ^ (2*K) * (4 * A ^ (2*K) * 3 ^ (2*(K-1)) * Ns ^ (2*K)) :=
          mul_le_mul_of_nonneg_right hα h4nn
      _ = (4 * A ^ (2*K) * 3 ^ (2*(K-1)) * Ns ^ (2*K)) * eta ^ (2*K) := by ring
  -- multiply `hk` by the positive common factor `M`
  have hM : (0:ℝ) ≤ cmin * θ * Cd^2 * D^(2*K) /
      (4 * A ^ (2*K) * 3 ^ (2*(K-1)) * Ns ^ (2*K) * B^2 * L ^ (2*(K-1))) := by positivity
  have hpow1 : (eta^K)^2 = eta^(2*K) := by rw [← pow_mul, Nat.mul_comm]
  have hpow2 : ((D/L)^K)^2 = D^(2*K)/L^(2*K) := by rw [← pow_mul, Nat.mul_comm, div_pow]
  have hpow3 : L^(2*(K-1)) = L^(2*K) / L^2 := by
    rw [eq_div_iff (by positivity : (L:ℝ)^2 ≠ 0)]
    rw [← pow_add]; congr 1; omega
  have eq1 : cmin * θ * (B⁻¹)^2 * (Cd * eta ^ K * (D / L) ^ K * L) ^ 2 =
      (4 * A ^ (2*K) * 3 ^ (2*(K-1)) * Ns ^ (2*K) * eta ^ (2*K)) *
        (cmin * θ * Cd^2 * D^(2*K) /
          (4 * A ^ (2*K) * 3 ^ (2*(K-1)) * Ns ^ (2*K) * B^2 * L ^ (2*(K-1)))) := by
    rw [inv_pow]
    field_simp
    rw [hpow1, hpow2, hpow3]
    field_simp
  have eq2 : cmin ^ (1 + 2 * K) * Cd ^ 2 / (4 * A ^ (2 * K) * 3 ^ (2 * (K - 1))) *
        θ ^ (4 * K + 1) * (D / Ns) ^ (2 * K) =
      (cmin ^ (2*K) * θ ^ (4*K) * B^2 * L ^ (2*(K-1))) *
        (cmin * θ * Cd^2 * D^(2*K) /
          (4 * A ^ (2*K) * 3 ^ (2*(K-1)) * Ns ^ (2*K) * B^2 * L ^ (2*(K-1)))) := by
    rw [div_pow]
    field_simp
    rw [show 1 + 2*K = 2*K + 1 by omega, pow_succ, pow_succ]
    ring
  rw [ge_iff_le, eq1, eq2]
  exact mul_le_mul_of_nonneg_right hk hM

end Work.Peluse.Ulower.StepLe
