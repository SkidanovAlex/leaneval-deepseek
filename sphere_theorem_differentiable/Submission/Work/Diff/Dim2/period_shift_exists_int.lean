import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Dim2

/-- Two reals whose exponentials `exp (i ·)` agree differ by an integer multiple of `2π`. -/
private lemma exists_int_of_exp_I_eq {a b : ℝ}
    (h : Complex.exp ((a : ℂ) * Complex.I) = Complex.exp ((b : ℂ) * Complex.I)) :
    ∃ n : ℤ, a = b + (n : ℝ) * (2 * Real.pi) := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  refine ⟨n, ?_⟩
  have h2 := congrArg Complex.im hn
  simp only [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.intCast_re, Complex.intCast_im,
    Complex.re_ofNat, Complex.im_ofNat, mul_zero, add_zero, zero_mul, mul_one, sub_zero] at h2
  exact h2

/-- No integer is congruent to `1/2` modulo `1`. -/
private lemma intCast_ne_intCast_add_half (j n : ℤ) : (j : ℝ) ≠ (n : ℝ) + 1 / 2 := by
  intro h
  have h2 : ((2 * (j - n) : ℤ) : ℝ) = 1 := by push_cast; linarith
  have h3 : 2 * (j - n) = 1 := by exact_mod_cast h2
  omega

/-- **The period shift of an angle lift is an integer multiple of `2π`.**

Let `κ : ℝ → ℝ²` be `2π`-periodic and let `ρ : ℝ → ℝ` be continuous with
`cos (ρ θ) = (κ θ) 0`, `sin (ρ θ) = (κ θ) 1` for all `θ`.  Then `θ ↦ ρ (θ + 2π) − ρ θ` is a
continuous function with values in `2πℤ` (because `exp (i ρ (θ+2π)) = exp (i ρ θ)`), hence
constant: there is `n : ℤ` with `ρ (θ + 2π) = ρ θ + n * 2π` for all `θ`. -/
theorem period_shift_exists_int
    {κ : ℝ → EuclideanSpace ℝ (Fin 2)} {ρ : ℝ → ℝ}
    (hper : ∀ θ, κ (θ + 2 * Real.pi) = κ θ) (hρ : Continuous ρ)
    (hcs : ∀ θ, Real.cos (ρ θ) = κ θ 0 ∧ Real.sin (ρ θ) = κ θ 1) :
    ∃ n : ℤ, ∀ θ, ρ (θ + 2 * Real.pi) = ρ θ + (n : ℝ) * (2 * Real.pi) := by
  -- Step 1: the values of the angle lift agree on `θ` and `θ + 2π` in the sense of `exp (· * I)`,
  -- hence the period shift is an integer multiple of `2π` pointwise.
  have key : ∀ θ, ∃ n : ℤ, ρ (θ + 2 * Real.pi) = ρ θ + (n : ℝ) * (2 * Real.pi) := by
    intro θ
    refine exists_int_of_exp_I_eq ?_
    rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I, (hcs (θ + 2 * Real.pi)).1,
      (hcs (θ + 2 * Real.pi)).2, (hcs θ).1, (hcs θ).2, hper θ]
  -- Step 2: normalize the shift into a continuous function mapping into `ℤ`.
  set g : ℝ → ℝ := fun θ => (ρ (θ + 2 * Real.pi) - ρ θ) / (2 * Real.pi) with hg
  have hcont : Continuous g := by
    rw [hg]
    exact ((hρ.comp (continuous_id.add continuous_const)).sub hρ).div_const _
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have hval : ∀ θ, ∃ k : ℤ, g θ = (k : ℝ) := by
    intro θ
    obtain ⟨n, hn⟩ := key θ
    refine ⟨n, ?_⟩
    rw [hg]
    change (ρ (θ + 2 * Real.pi) - ρ θ) / (2 * Real.pi) = (n : ℝ)
    rw [hn]
    field_simp
    ring
  -- Step 3: `g` is continuous on the connected space `ℝ` with values in the discrete set `ℤ`,
  -- hence constant (intermediate value theorem: an intermediate value would be an integer `+ 1/2`).
  obtain ⟨n₀, hn₀⟩ := hval 0
  refine ⟨n₀, ?_⟩
  intro θ
  have hconst : g θ = (n₀ : ℝ) := by
    obtain ⟨m, hm⟩ := hval θ
    have hmn : m = n₀ := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · -- `m < n₀`: the value `m + 1/2` lies between `g θ` and `g 0`.
        have hmem : (m : ℝ) + 1 / 2 ∈ Set.Icc (g θ) (g 0) := by
          rw [hm, hn₀]
          constructor
          · linarith
          · have h1 : ((m + 1 : ℤ) : ℝ) ≤ (n₀ : ℝ) := by
              exact_mod_cast (show m + 1 ≤ n₀ by omega)
            push_cast at h1
            linarith
        obtain ⟨t, ht⟩ := intermediate_value_univ θ 0 hcont hmem
        obtain ⟨k, hk⟩ := hval t
        rw [hk] at ht
        exact intCast_ne_intCast_add_half k m ht
      · -- `n₀ < m`: the value `n₀ + 1/2` lies between `g 0` and `g θ`.
        have hmem : (n₀ : ℝ) + 1 / 2 ∈ Set.Icc (g 0) (g θ) := by
          rw [hm, hn₀]
          constructor
          · linarith
          · have h1 : ((n₀ + 1 : ℤ) : ℝ) ≤ (m : ℝ) := by
              exact_mod_cast (show n₀ + 1 ≤ m by omega)
            push_cast at h1
            linarith
        obtain ⟨t, ht⟩ := intermediate_value_univ 0 θ hcont hmem
        obtain ⟨k, hk⟩ := hval t
        rw [hk] at ht
        exact intCast_ne_intCast_add_half k n₀ ht
    rw [hm, hmn]
  have hfinal : ρ (θ + 2 * Real.pi) - ρ θ = (n₀ : ℝ) * (2 * Real.pi) := by
    rw [hg] at hconst
    rw [div_eq_iff hpi] at hconst
    exact hconst
  linarith

end Work.Diff.Dim2
