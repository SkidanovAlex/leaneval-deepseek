import Mathlib

namespace Work.A3

/-- Bookkeeping inequality for the exponent of `N` in the §5 reduction:
with `φ = θ'/2`, `θ = (1-ε₀)θ'/2` and `qn ≤ N^ε₀`, the factor `qn` produced by
splitting `M = N/qn` is absorbed by the extra power `ε₀θ'/2` earned on `N`. -/
theorem final_exponent_bound {ε₀ θ' φ θ N qn M : ℝ} (hε₀ : ε₀ ≤ 1 / 2)
    (hθ' : 0 < θ') (hφ : φ = θ' / 2) (hθ : θ = (1 - ε₀) * θ' / 2)
    (hN : 1 ≤ N) (hqn1 : 1 ≤ qn) (hM : M = N / qn) (hqn : qn ≤ N ^ ε₀)
    (hθ'le : θ' ≤ 1) :
    qn * (2 ^ (1 - θ' + φ) * M ^ (1 - θ' + φ)) ≤ 2 ^ (1 - θ' + φ) * N ^ (1 - θ) := by
  have hNpos : (0 : ℝ) < N := by linarith
  have hqnpos : (0 : ℝ) < qn := by linarith
  -- abbreviate the common exponent `a = 1 - θ' + φ`
  set a : ℝ := 1 - θ' + φ with ha
  -- `1 - a = θ'/2`
  have hexp : 1 - a = θ' / 2 := by rw [ha]; linarith [hφ]
  -- `1 - θ = a + ε₀ * (θ'/2)`
  have htheta : 1 - θ = a + ε₀ * (θ' / 2) := by rw [ha]; nlinarith [hφ, hθ]
  -- `M^a = N^a / qn^a`
  have hMpow : M ^ a = N ^ a / qn ^ a := by
    rw [hM, Real.div_rpow (le_of_lt hNpos) (le_of_lt hqnpos) a]
  -- `qn / qn^a = qn^(θ'/2)`
  have hdiv : qn / qn ^ a = qn ^ (θ' / 2) := by
    have hsub := Real.rpow_sub hqnpos (1 : ℝ) a
    rw [Real.rpow_one] at hsub
    rw [← hsub, hexp]
  -- the core: `qn * M^a = N^a * qn^(θ'/2) ≤ N^(1-θ)`
  have hmid : qn * M ^ a = N ^ a * qn ^ (θ' / 2) := by
    rw [hMpow]
    have : qn * (N ^ a / qn ^ a) = N ^ a * (qn / qn ^ a) := by ring
    rw [this, hdiv]
  have hmain : N ^ a * qn ^ (θ' / 2) ≤ N ^ (1 - θ) := by
    rw [htheta, Real.rpow_add hNpos a]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (le_of_lt hNpos) a)
    calc qn ^ (θ' / 2) ≤ (N ^ ε₀) ^ (θ' / 2) :=
          Real.rpow_le_rpow (le_of_lt hqnpos) hqn (by linarith [hθ'])
      _ = N ^ (ε₀ * (θ' / 2)) := (Real.rpow_mul (le_of_lt hNpos) ε₀ (θ' / 2)).symm
  calc qn * (2 ^ a * M ^ a) = 2 ^ a * (qn * M ^ a) := by ring
    _ = 2 ^ a * (N ^ a * qn ^ (θ' / 2)) := by rw [hmid]
    _ ≤ 2 ^ a * N ^ (1 - θ) :=
          mul_le_mul_of_nonneg_left hmain
            (le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) a))

end Work.A3
