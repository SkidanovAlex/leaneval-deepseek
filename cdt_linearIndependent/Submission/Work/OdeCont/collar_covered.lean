import Mathlib

namespace Work.OdeCont

/-- Norm of a real, viewed in `ℂ`. -/
lemma norm_ofReal_complex (x : ℝ) : ‖(x : ℂ)‖ = |x| := by
  simpa using Complex.ofRealLI.norm_map x

/-- `‖exp(a·i) - exp(b·i)‖ ≤ |a - b|` for real `a, b`. -/
lemma norm_exp_I_mul_sub_le (a b : ℝ) :
    ‖Complex.exp (a * Complex.I) - Complex.exp (b * Complex.I)‖ ≤ |a - b| := by
  have hdecomp : Complex.exp (a * Complex.I) - Complex.exp (b * Complex.I)
      = Complex.exp (b * Complex.I)
          * (Complex.exp ((a - b) * Complex.I) - 1) := by
    have hadd : Complex.exp (b * Complex.I) * Complex.exp ((a - b) * Complex.I)
        = Complex.exp (a * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    rw [mul_sub, mul_one, hadd]
  rw [hdecomp, norm_mul]
  have hb : ‖Complex.exp (b * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I b
  rw [hb, one_mul]
  have h1 : Complex.exp ((a - b) * Complex.I)
      = Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) := by
    congr 1
    push_cast
    ring
  rw [h1, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs]
  rw [show |2 * Real.sin ((a - b) / 2)| = 2 * |Real.sin ((a - b) / 2)| by
        rw [abs_mul]; norm_num]
  calc 2 * |Real.sin ((a - b) / 2)| ≤ 2 * |(a - b) / 2| := by
        exact mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (by norm_num)
      _ = |a - b| := by
        rw [abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
        ring

/-- **The collar is covered by the `N`-th roots of unity scaled by `ρ`.**

If `ρ > 0`, `ε ≥ 0` and `ε + ρ·π/N < δ`, then every point `z` of the closed
annulus `ρ ≤ ‖z‖ ≤ ρ + ε` lies within distance `δ` of one of the `N` equally
spaced points `ρ·exp(2πi k/N)`, `k ∈ {0,…,N-1}`. -/
theorem collar_covered {N : ℕ} (hN : 0 < N) {ρ δ ε : ℝ} (hρ : 0 < ρ) (hε : 0 ≤ ε)
    (h : ε + ρ * Real.pi / N < δ) :
    ∀ z : ℂ, ρ ≤ ‖z‖ → ‖z‖ ≤ ρ + ε →
      ∃ k : Fin N, ‖z - ρ * Complex.exp (2 * Real.pi * Complex.I * (k : ℕ) / N)‖ < δ := by
  intro z hz1 hz2
  have hNreal : (0:ℝ) < N := by exact_mod_cast hN
  have hNne : (N:ℕ) ≠ 0 := by omega
  have hNr : (N:ℝ) ≠ 0 := ne_of_gt hNreal
  -- ---- step 1: pick the integer grid point on the real line
  set x : ℝ := z.arg * N / (2 * Real.pi) with hx
  set n : ℤ := ⌊x + 1/2⌋ with hnd
  have hround : |x - (n:ℝ)| ≤ 1/2 := by
    have h1 : (n:ℝ) ≤ x + 1/2 := by rw [hnd]; exact Int.floor_le _
    have h2 : x + 1/2 < (n:ℝ) + 1 := by rw [hnd]; exact Int.lt_floor_add_one _
    rw [abs_le]; constructor <;> linarith
  -- ---- step 2: the angular bound
  have hangle : |z.arg - 2 * Real.pi * (n:ℝ) / N| ≤ Real.pi / N := by
    have hfac : z.arg - 2 * Real.pi * (n:ℝ) / N = (2 * Real.pi / N) * (x - n) := by
      rw [hx]; field_simp
    rw [hfac, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi / N)]
    calc (2 * Real.pi / N) * |x - n| ≤ (2 * Real.pi / N) * (1/2) := by
          exact mul_le_mul_of_nonneg_left hround (by positivity)
      _ = Real.pi / N := by ring
  -- ---- step 3: reduce the integer `n` modulo `N`
  set k : ℕ := n.natMod (N : ℤ) with hk
  have hklt : k < N := Int.natMod_lt (m := n) (n := N) hNne
  have hk_int : (k : ℤ) = n % (N : ℤ) := by
    rw [hk, Int.natMod]
    exact Int.toNat_of_nonneg (Int.emod_nonneg n (by exact_mod_cast hNne : (N:ℤ) ≠ 0))
  set q : ℤ := n / (N : ℤ) with hq
  have hq_eq : (n : ℤ) - (k : ℤ) = (N : ℤ) * q := by
    rw [hq, hk_int, Int.emod_def]
    ring
  -- ---- step 4: the angle `2πn/N` equals `2πk/N` modulo `2π`
  have hk_exp : 2 * Real.pi * Complex.I * (k : ℕ) / N
      = (((2 * Real.pi * (k:ℝ) / N : ℝ)) : ℂ) * Complex.I := by
    push_cast; ring
  have hexp_eq : Complex.exp ((((2 * Real.pi * (n:ℝ) / N : ℝ)) : ℂ) * Complex.I)
      = Complex.exp ((((2 * Real.pi * (k:ℝ) / N : ℝ)) : ℂ) * Complex.I) := by
    have hn_int : (n : ℤ) = (k : ℤ) + (N : ℤ) * q := by linarith [hq_eq]
    have hn : (n : ℝ) = (k : ℝ) + (N : ℝ) * (q : ℝ) := by exact_mod_cast hn_int
    have hphi : 2 * Real.pi * (n:ℝ) / N
        = 2 * Real.pi * (k:ℝ) / N + 2 * Real.pi * (q:ℝ) := by
      rw [hn]; field_simp
    rw [hphi]
    have hsplit : (((2 * Real.pi * (k:ℝ) / N + 2 * Real.pi * (q:ℝ) : ℝ)) : ℂ)
        = (((2 * Real.pi * (k:ℝ) / N : ℝ)) : ℂ) + (((2 * Real.pi * (q:ℝ) : ℝ)) : ℂ) := by
      push_cast; ring
    rw [hsplit, add_mul, Complex.exp_add]
    have hqone : Complex.exp ((((2 * Real.pi * (q:ℝ) : ℝ)) : ℂ) * Complex.I) = 1 := by
      rw [show ((((2 * Real.pi * (q:ℝ) : ℝ)) : ℂ) * Complex.I)
          = (q : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I q
    rw [hqone, mul_one]
  -- ---- step 5: the norm estimate
  have hEdiff : ‖Complex.exp (z.arg * Complex.I)
      - Complex.exp (2 * Real.pi * Complex.I * (k : ℕ) / N)‖ ≤ Real.pi / N := by
    rw [hk_exp, ← hexp_eq]
    exact le_trans (norm_exp_I_mul_sub_le z.arg (2 * Real.pi * (n:ℝ) / N)) hangle
  have hE1 : ‖Complex.exp (z.arg * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I z.arg
  have htri : ‖(‖z‖ : ℂ) * Complex.exp (z.arg * Complex.I)
        - (ρ : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (k : ℕ) / N)‖
      ≤ ε + ρ * Real.pi / N := by
    have h3 : ‖(‖z‖ : ℂ) * Complex.exp (z.arg * Complex.I)
          - (ρ : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (k : ℕ) / N)‖
        ≤ ‖(‖z‖ : ℂ) * Complex.exp (z.arg * Complex.I)
            - (ρ : ℂ) * Complex.exp (z.arg * Complex.I)‖
          + ‖(ρ : ℂ) * Complex.exp (z.arg * Complex.I)
            - (ρ : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (k : ℕ) / N)‖ := by
      simpa [dist_eq_norm] using
        (dist_triangle ((‖z‖ : ℂ) * Complex.exp (z.arg * Complex.I))
          ((ρ : ℂ) * Complex.exp (z.arg * Complex.I))
          ((ρ : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (k : ℕ) / N)))
    have hla : ‖(‖z‖ : ℂ) * Complex.exp (z.arg * Complex.I)
          - (ρ : ℂ) * Complex.exp (z.arg * Complex.I)‖ ≤ ε := by
      rw [← sub_mul]
      have hcast : (‖z‖ : ℂ) - (ρ : ℂ) = ((‖z‖ - ρ : ℝ) : ℂ) := by push_cast; ring
      rw [hcast, norm_mul, norm_ofReal_complex, hE1, mul_one,
        abs_of_nonneg (by linarith : (0:ℝ) ≤ ‖z‖ - ρ)]
      linarith
    have hlb : ‖(ρ : ℂ) * Complex.exp (z.arg * Complex.I)
          - (ρ : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (k : ℕ) / N)‖
        ≤ ρ * (Real.pi / N) := by
      rw [← mul_sub, norm_mul]
      have : ‖(ρ : ℂ)‖ = ρ := by rw [norm_ofReal_complex, abs_of_pos hρ]
      rw [this]
      exact mul_le_mul_of_nonneg_left hEdiff hρ.le
    calc ‖(‖z‖ : ℂ) * Complex.exp (z.arg * Complex.I)
            - (ρ : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (k : ℕ) / N)‖
        ≤ ‖(‖z‖ : ℂ) * Complex.exp (z.arg * Complex.I)
            - (ρ : ℂ) * Complex.exp (z.arg * Complex.I)‖
          + ‖(ρ : ℂ) * Complex.exp (z.arg * Complex.I)
            - (ρ : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (k : ℕ) / N)‖ := h3
      _ ≤ ε + ρ * (Real.pi / N) := add_le_add hla hlb
      _ = ε + ρ * Real.pi / N := by ring
  refine ⟨⟨k, hklt⟩, ?_⟩
  have hzE : (‖z‖ : ℂ) * Complex.exp (z.arg * Complex.I) = z :=
    Complex.norm_mul_exp_arg_mul_I z
  rw [← hzE]
  exact lt_of_le_of_lt htri h

end Work.OdeCont
