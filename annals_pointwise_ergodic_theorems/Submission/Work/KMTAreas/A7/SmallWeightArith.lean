import Mathlib
import Submission.Work.KMTAreas.A7.Large.Assembly

namespace Work.KMTAreas.A7

open scoped ENNReal NNReal BigOperators

/-- The elementary weight arithmetic behind the summation over the lacunary small scales: for
`C ≥ 0`, `C₀ ≥ 1` and `0 ≤ ρ ≤ 1/(4C₀)` the quantity `2^{C·max(2^{ρL}, L)}·2^{-2^{L/C₀}+2}` is
bounded uniformly in `L ∈ ℕ` by a constant `Kabs`.

This is the `L`-uniform version of "the exponential gain `2^{-2^{L/C₀}}` beats both `2^{C2^{ρL}}`
and `2^{CL}`": for `L` large the factor `2^{L/C₀}` dominates `C·max(2^{ρL}, L)`, and the finitely
many small `L` contribute a constant (using `ρ ≤ 1`, so `2^{ρL} ≤ 2^L`).  It is what allows the
*single-scale* model-approximation error `2^{C·max(2^{ρL},L)}⌊a n⌋⁻¹` to be summed over the
lacunary scales of the index set, whose reciprocal sum is `≲ 2^{-2^{L/C₀}}`
(`Work.KMTAreas.A7.invFloorSum_le`).

A suggested route: let `ε = 1/(2C₀)` and use the proved
`Work.KMTAreas.A7.rpow_poly_le_const_exp` (`(1+L)^2 ≤ K₁·2^{εL}`, in `A7/Large/Assembly.lean`)
to get `C·L + 2 ≤ K₂·2^{εL/2}` with `K₂ = C·√K₁ + C + 2`; since `2^{ρL} ≤ 2^{εL/2}` for
`ρ ≤ ε/2`, this gives `C·max(2^{ρL},L) + 2 ≤ K₂·2^{L/(4C₀)}`, and with `Z = 2^{L/(4C₀)}` one has
`2^{L/C₀} = Z⁴`, with `K₂Z ≤ Z⁴` as soon as `Z³ ≥ K₂`.  Hence for all `L` above an explicit
threshold the exponent `C·max(2^{ρL},L) + 2 - 2^{L/C₀}` is `≤ 0`, and below that threshold it is at
most `C·2^{L₀} + 2` for the threshold `L₀`. -/
theorem SmallWeightArith (C : ℝ) (hC : 0 ≤ C) (C₀ : ℕ) (hC₀ : 1 ≤ C₀) :
    ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 / (4 * (C₀ : ℝ)) → ∃ Kabs : ℝ, 1 ≤ Kabs ∧ ∀ L : ℕ,
      (2 : ℝ) ^ (C * max ((2 : ℝ) ^ (ρ * (L : ℝ))) (L : ℝ)) *
        (2 : ℝ) ^ (-((2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ))) + 2) ≤ Kabs := by
  intro ρ hρ0 hρle
  have hC0pos : (0 : ℝ) < (C₀ : ℝ) := by
    have h1 : (1 : ℝ) ≤ (C₀ : ℝ) := by exact_mod_cast hC₀
    linarith
  -- `ε = 1/(2C₀)`, so that `2^{ρL} ≤ 2^{εL}` and `(2^{εL})² = 2^{L/C₀}`.
  set ε : ℝ := 1 / (2 * (C₀ : ℝ)) with hε
  have hεpos : 0 < ε := by rw [hε]; positivity
  -- `(1+L)² ≤ K₁ · 2^{εL}` for all `L`.
  obtain ⟨K₁, hK₁ge, hK₁b⟩ := rpow_poly_le_const_exp 2 ε (by norm_num) hεpos
  have hK₁nn : 0 ≤ K₁ := le_trans zero_le_one hK₁ge
  -- the combined constant `K₂ = C·(1+K₁) + 2`
  set K₂ : ℝ := C * (1 + K₁) + 2 with hK₂
  have hK₂nn : 0 ≤ K₂ := by rw [hK₂]; nlinarith
  have hρε : ρ ≤ ε := by
    have h1 : 1 / (4 * (C₀ : ℝ)) ≤ 1 / (2 * (C₀ : ℝ)) := by
      apply one_div_le_one_div_of_le (by positivity) (by linarith)
    rw [hε]
    exact le_trans hρle h1
  refine ⟨(2 : ℝ) ^ (K₂ ^ 2 / 4), ?_, fun L => ?_⟩
  · apply Real.one_le_rpow (show (1 : ℝ) ≤ 2 by norm_num)
    positivity
  · have hLnn : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
    set Z : ℝ := (2 : ℝ) ^ (ε * (L : ℝ)) with hZ
    have hZ1 : 1 ≤ Z := by
      rw [hZ]
      exact Real.one_le_rpow (show (1 : ℝ) ≤ 2 by norm_num) (by positivity)
    have hZpos : 0 < Z := lt_of_lt_of_le zero_lt_one hZ1
    have hZnn : 0 ≤ Z := le_of_lt hZpos
    -- `2^{ρL} ≤ Z`
    have hpowZ : (2 : ℝ) ^ (ρ * (L : ℝ)) ≤ Z := by
      rw [hZ]
      exact Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
        (mul_le_mul_of_nonneg_right hρε hLnn)
    -- `L ≤ (1+L)² ≤ K₁ Z`
    have hpoly : (1 + (L : ℝ)) ^ 2 ≤ K₁ * Z := by
      rw [hZ]
      simpa using hK₁b L
    have hZle : Z ≤ (1 + K₁) * Z := by
      have : (0 : ℝ) ≤ K₁ * Z := mul_nonneg hK₁nn hZnn
      nlinarith
    have hLZ : (L : ℝ) ≤ (1 + K₁) * Z := by
      have h2 : (L : ℝ) ≤ (1 + (L : ℝ)) ^ 2 := by nlinarith [hLnn, sq_nonneg (L : ℝ)]
      linarith
    have hmax : max ((2 : ℝ) ^ (ρ * (L : ℝ))) (L : ℝ) ≤ (1 + K₁) * Z :=
      max_le (le_trans hpowZ hZle) hLZ
    have hCmax : C * max ((2 : ℝ) ^ (ρ * (L : ℝ))) (L : ℝ) ≤ C * ((1 + K₁) * Z) :=
      mul_le_mul_of_nonneg_left hmax hC
    -- `Z² = 2^{L/C₀}`
    have hZ2 : Z ^ 2 = (2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ)) := by
      have h2ε : 2 * ε * (L : ℝ) = (L : ℝ) / (C₀ : ℝ) := by
        rw [hε]
        field_simp
      have hsq : Z ^ 2 = (2 : ℝ) ^ (2 * ε * (L : ℝ)) := by
        rw [hZ, sq, ← Real.rpow_add (show (0 : ℝ) < 2 by norm_num)]
        congr 1
        ring
      rw [hsq, h2ε]
    -- the exponent is bounded: `C·max(…) + 2 - Z² ≤ K₂Z - Z² ≤ K₂²/4`
    have hmain : C * max ((2 : ℝ) ^ (ρ * (L : ℝ))) (L : ℝ)
        - (2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ)) + 2 ≤ K₂ ^ 2 / 4 := by
      rw [← hZ2]
      nlinarith [sq_nonneg (Z - K₂ / 2), hCmax, hZ1, hK₂]
    have hsplit : (2 : ℝ) ^ (C * max ((2 : ℝ) ^ (ρ * (L : ℝ))) (L : ℝ)
          + (-((2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ))) + 2))
        = (2 : ℝ) ^ (C * max ((2 : ℝ) ^ (ρ * (L : ℝ))) (L : ℝ)) *
          (2 : ℝ) ^ (-((2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ))) + 2) :=
      Real.rpow_add (show (0 : ℝ) < 2 by norm_num) _ _
    calc (2 : ℝ) ^ (C * max ((2 : ℝ) ^ (ρ * (L : ℝ))) (L : ℝ)) *
          (2 : ℝ) ^ (-((2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ))) + 2)
        = (2 : ℝ) ^ (C * max ((2 : ℝ) ^ (ρ * (L : ℝ))) (L : ℝ)
            + (-((2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ))) + 2)) := hsplit.symm
      _ = (2 : ℝ) ^ (C * max ((2 : ℝ) ^ (ρ * (L : ℝ))) (L : ℝ)
            - (2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ)) + 2) := by congr 1; ring
      _ ≤ (2 : ℝ) ^ (K₂ ^ 2 / 4) :=
            Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num) hmain

end Work.KMTAreas.A7
