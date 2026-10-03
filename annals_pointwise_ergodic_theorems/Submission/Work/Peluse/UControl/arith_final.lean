import Mathlib

set_option linter.unusedVariables false

namespace Work.Peluse.UControl

/-- Elementary arithmetic bookkeeping used in the `U`-control chapter (Peluse's
theorem 3.7 route): with `N^d ≤ A' δ⁻¹ N₀` and `MA ≤ A'' N^d`, the quantity
`δ ^ (2K) / (C A' ^ K)` is dominated by `κ (δ ^ 2 N₀ ^ 2 / ((2MA+1) MA)) ^ (2K₀) / (C₀ A'' ^ K₀)`
as soon as `K ≥ 4 K₀` and `C` dominates `C₀ A'' ^ (5K₀) 3 ^ (2K₀) / κ`.

The proof proceeds by the chain
`δ^{2K}/(C A'^K) ≤ δ^{8K₀}/(C A'^{4K₀}) ≤ κ δ^{8K₀}/(C₀ A''^{5K₀} 3^{2K₀} A'^{4K₀}) ≤ RHS`,
the last step using
`((2MA+1) MA)^{2K₀} ≤ 3^{2K₀} A''^{4K₀} (A' δ⁻¹ N₀)^{4K₀}`. -/
theorem arith_final {d K K₀ : ℕ} {δ κ C₀ C A' A'' : ℝ} {N N₀ MA : ℕ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hN : 1 ≤ N) (hN₀ : 1 ≤ N₀) (hMA : 1 ≤ MA)
    (hA' : 1 ≤ A') (hA'' : 1 ≤ A'')
    (hsc2 : (N : ℝ) ^ d ≤ A' * δ⁻¹ * (N₀ : ℝ))
    (hMAub : (MA : ℝ) ≤ A'' * (N : ℝ) ^ d)
    (hK₀ : 1 ≤ K₀) (hK : 4 * K₀ ≤ K) (hC₀ : 0 < C₀) (hκ : 0 < κ) (hC : 0 < C)
    (hCbig : C₀ * A'' ^ (5 * K₀) * 3 ^ (2 * K₀) / κ ≤ C) :
    δ ^ (2 * K) / (C * A' ^ K) ≤
      κ * (δ ^ 2 * (N₀ : ℝ) ^ 2 / ((2 * (MA : ℝ) + 1) * (MA : ℝ))) ^ (2 * K₀)
        / (C₀ * A'' ^ K₀) := by
  have hmm1 : (1:ℝ) ≤ (MA:ℝ) := by exact_mod_cast hMA
  have hmmpos : 0 < (MA:ℝ) := lt_of_lt_of_le one_pos hmm1
  have hn₀1 : (1:ℝ) ≤ (N₀:ℝ) := by exact_mod_cast hN₀
  have hn₀pos : 0 < (N₀:ℝ) := lt_of_lt_of_le one_pos hn₀1
  have hn₀ne : (N₀:ℝ) ≠ 0 := ne_of_gt hn₀pos
  have hδne : δ ≠ 0 := ne_of_gt hδ0
  have hA'pos : 0 < A' := lt_of_lt_of_le one_pos hA'
  have hA''pos : 0 < A'' := lt_of_lt_of_le one_pos hA''
  have hu0 : 0 ≤ (N:ℝ)^d := by positivity
  -- Step 1: enlarge `K` to `4K₀` and `2K` to `8K₀`.
  have hstep1 : δ ^ (2*K) / (C * A' ^ K) ≤ δ ^ (8*K₀) / (C * A' ^ (4*K₀)) := by
    have h1 : δ ^ (2*K) ≤ δ ^ (8*K₀) := pow_le_pow_of_le_one (le_of_lt hδ0) hδ1 (by omega)
    have h2 : 1 / (C * A' ^ K) ≤ 1 / (C * A' ^ (4*K₀)) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hA' (by omega)) (le_of_lt hC)
    have h3 := mul_le_mul h1 h2 (by positivity) (by positivity)
    simpa only [mul_one_div] using h3
  -- Step 2: replace the constant `C` by `C₀ A''^{5K₀} 3^{2K₀} / κ`.
  have hstep2 : δ ^ (8*K₀) / (C * A' ^ (4*K₀)) ≤
      κ * δ ^ (8*K₀) / (C₀ * A'' ^ (5*K₀) * 3 ^ (2*K₀) * A' ^ (4*K₀)) := by
    have h1divC : 1 / C ≤ κ / (C₀ * A'' ^ (5*K₀) * 3 ^ (2*K₀)) := by
      simpa only [one_div_div] using one_div_le_one_div_of_le
        (show (0:ℝ) < C₀ * A'' ^ (5*K₀) * 3 ^ (2*K₀) / κ by positivity) hCbig
    have hfac1 : δ ^ (8*K₀) / (C * A' ^ (4*K₀)) = (δ^(8*K₀) / A'^(4*K₀)) * (1/C) := by
      field_simp
    have hfac2 : κ * δ ^ (8*K₀) / (C₀ * A'' ^ (5*K₀) * 3 ^ (2*K₀) * A' ^ (4*K₀))
        = (δ^(8*K₀) / A'^(4*K₀)) * (κ / (C₀ * A'' ^ (5*K₀) * 3 ^ (2*K₀))) := by
      field_simp
    rw [hfac1, hfac2]
    exact mul_le_mul_of_nonneg_left h1divC (by positivity)
  -- Core estimate: `δ^{8K₀}/(A''^{4K₀} 3^{2K₀} A'^{4K₀}) ≤ P^{2K₀}`.
  have hcore : δ ^ (8*K₀) / (A''^(4*K₀) * 3^(2*K₀) * A'^(4*K₀)) ≤
      (δ ^ 2 * (N₀:ℝ) ^ 2 / ((2 * (MA:ℝ) + 1) * (MA:ℝ))) ^ (2 * K₀) := by
    have hX0pos : 0 < (2*(MA:ℝ)+1)*(MA:ℝ) := by positivity
    have hmm3 : 2*(MA:ℝ) + 1 ≤ 3*(MA:ℝ) := by linarith
    have hX0_le : (2*(MA:ℝ)+1)*(MA:ℝ) ≤ 3*(A''*(N:ℝ)^d)^2 := by
      have hmmsq : (MA:ℝ)^2 ≤ (A''*(N:ℝ)^d)^2 := pow_le_pow_left₀ (le_of_lt hmmpos) hMAub 2
      nlinarith [hmm3, hmmsq]
    have hX_le : ((2*(MA:ℝ)+1)*(MA:ℝ))^(2*K₀) ≤
        3^(2*K₀) * A''^(4*K₀) * ((N:ℝ)^d)^(4*K₀) := by
      calc ((2*(MA:ℝ)+1)*(MA:ℝ))^(2*K₀) ≤ (3*(A''*(N:ℝ)^d)^2)^(2*K₀) :=
            pow_le_pow_left₀ (le_of_lt hX0pos) hX0_le _
        _ = 3^(2*K₀) * A''^(4*K₀) * ((N:ℝ)^d)^(4*K₀) := by
            rw [mul_pow, ← pow_mul, mul_pow]; ring_nf
    have hu_le : ((N:ℝ)^d)^(4*K₀) ≤ A'^(4*K₀)*(δ⁻¹)^(4*K₀)*(N₀:ℝ)^(4*K₀) := by
      calc ((N:ℝ)^d)^(4*K₀) ≤ (A'*δ⁻¹*(N₀:ℝ))^(4*K₀) := pow_le_pow_left₀ hu0 hsc2 _
        _ = A'^(4*K₀)*(δ⁻¹)^(4*K₀)*(N₀:ℝ)^(4*K₀) := by rw [mul_pow, mul_pow]
    have hP : (δ^2*(N₀:ℝ)^2/((2*(MA:ℝ)+1)*(MA:ℝ)))^(2*K₀)
        = δ^(4*K₀)*(N₀:ℝ)^(4*K₀)/(((2*(MA:ℝ)+1)*(MA:ℝ))^(2*K₀)) := by
      rw [div_pow, mul_pow, ← pow_mul, ← pow_mul]; ring_nf
    have hkey : δ^(8*K₀)/(A''^(4*K₀)*3^(2*K₀)*A'^(4*K₀))
        = δ^(4*K₀)*(N₀:ℝ)^(4*K₀)/
            (3^(2*K₀)*A''^(4*K₀)*A'^(4*K₀)*(δ⁻¹)^(4*K₀)*(N₀:ℝ)^(4*K₀)) := by
      have h8 : δ^(8*K₀) = δ^(4*K₀)*δ^(4*K₀) := by
        rw [show 8*K₀ = 4*K₀ + 4*K₀ by ring, pow_add]
      rw [h8, inv_pow]
      field_simp
    rw [hP, hkey]
    apply div_le_div_of_nonneg_left (by positivity) (pow_pos hX0pos _)
    calc ((2*(MA:ℝ)+1)*(MA:ℝ))^(2*K₀)
        ≤ 3^(2*K₀) * A''^(4*K₀) * ((N:ℝ)^d)^(4*K₀) := hX_le
      _ ≤ 3^(2*K₀) * A''^(4*K₀) * (A'^(4*K₀)*(δ⁻¹)^(4*K₀)*(N₀:ℝ)^(4*K₀)) := by
          exact mul_le_mul_of_nonneg_left hu_le (by positivity)
      _ = 3^(2*K₀) * A''^(4*K₀) * A'^(4*K₀) * (δ⁻¹)^(4*K₀) * (N₀:ℝ)^(4*K₀) := by ring
  -- Step 3: multiply the core estimate by the positive factor `κ / (C₀ A''^{K₀})`.
  have hstep3 : κ * δ ^ (8*K₀) / (C₀ * A'' ^ (5*K₀) * 3 ^ (2*K₀) * A' ^ (4*K₀)) ≤
      κ * (δ ^ 2 * (N₀:ℝ) ^ 2 / ((2 * (MA:ℝ) + 1) * (MA:ℝ))) ^ (2 * K₀) / (C₀ * A'' ^ K₀) := by
    have hb : A'' ^ (5*K₀) = A''^K₀ * A''^(4*K₀) := by
      rw [show 5*K₀ = K₀ + 4*K₀ by ring, pow_add]
    have hL : κ * δ ^ (8*K₀) / (C₀ * A'' ^ (5*K₀) * 3 ^ (2*K₀) * A' ^ (4*K₀))
        = (κ / (C₀ * A''^K₀)) * (δ ^ (8*K₀) / (A''^(4*K₀)*3^(2*K₀)*A'^(4*K₀))) := by
      rw [hb]; field_simp
    have hR : κ * (δ ^ 2 * (N₀:ℝ) ^ 2 / ((2*(MA:ℝ)+1)*(MA:ℝ))) ^ (2*K₀) / (C₀ * A'' ^ K₀)
        = (κ / (C₀ * A''^K₀)) *
            ((δ ^ 2 * (N₀:ℝ) ^ 2 / ((2*(MA:ℝ)+1)*(MA:ℝ))) ^ (2*K₀)) := by
      ring
    rw [hL, hR]
    exact mul_le_mul_of_nonneg_left hcore (by positivity)
  exact le_trans hstep1 (le_trans hstep2 hstep3)

end Work.Peluse.UControl
