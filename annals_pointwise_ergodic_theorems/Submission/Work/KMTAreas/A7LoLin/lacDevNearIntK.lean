/-
# The elementary facts about the nearest integer, the distance to it, and the exponential gap

This file proves `Work.KMTAreas.A7LoLin.lacDevNearIntK`: for every real `θ`, with
`n₀ = nearInt θ = ⌊θ + 1/2⌋`, `δ = nearDist θ = |θ - n₀|` and `zGap θ = ‖1 - e^{2πiθ}‖`,

* `δ ≤ 1/2`;
* `4 δ ≤ zGap θ ≤ 2π δ` — the two quantities are comparable;
* every other integer `k ≠ n₀` is at distance `≥ 1/2` from `θ`;
* every other integer `k ≠ n₀` satisfies `|k - n₀| ≤ 2 |θ - k|`.

The comparability of `δ` and `zGap` is the identity `‖1 - e^{ix}‖ = 2 |sin (x/2)|`
(Mathlib's `Complex.norm_exp_I_mul_ofReal_sub_one`) together with the Jordan inequality
`(2/π)|x| ≤ |sin x|` for `|x| ≤ π/2` (`Real.mul_abs_le_abs_sin`) and `|sin x| ≤ |x|`
(`Real.abs_sin_le_abs`), applied at `x = 2π(θ - n₀)`, where `|x/2| = π δ ≤ π/2`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.LacDevSymDefs

set_option autoImplicit false

namespace Work.KMTAreas.A7LoLin

noncomputable section

/-! ## The auxiliary identities and inequalities -/

/-- The nearest integer `⌊θ + 1/2⌋` is within distance `1/2` of `θ`. -/
lemma nearDist_le_half (θ : ℝ) : Work.KMTAreas.A7.nearDist θ ≤ 1 / 2 := by
  rw [Work.KMTAreas.A7.nearDist, abs_le]
  have h1 : ((Work.KMTAreas.A7.nearInt θ : ℤ) : ℝ) ≤ θ + 1 / 2 :=
    Int.floor_le (θ + 1 / 2)
  have h2 : θ + 1 / 2 < ((Work.KMTAreas.A7.nearInt θ : ℤ) : ℝ) + 1 :=
    Int.lt_floor_add_one (θ + 1 / 2)
  constructor <;> linarith

/-- The signed form of `nearDist_le_half`. -/
lemma abs_sub_nearInt_le_half (θ : ℝ) : |θ - (Work.KMTAreas.A7.nearInt θ : ℝ)| ≤ 1 / 2 := by
  have h := nearDist_le_half θ
  rwa [Work.KMTAreas.A7.nearDist] at h

/-- The character `chr 1 θ = e^{2πiθ}` differs from `e^{i x}` by a factor `e^{2πi n₀}`,
which is `1`; this is the reduction of `zGap` to the elementary function `2 |sin (x/2)|`. -/
lemma chr_one_eq_exp (θ : ℝ) :
    Work.KMTAreas.ADev.chr 1 θ
      = Complex.exp (Complex.I * ((2 * Real.pi * (θ - (Work.KMTAreas.A7.nearInt θ : ℝ)) : ℝ) : ℂ)) := by
  set n₀ : ℤ := Work.KMTAreas.A7.nearInt θ with hn₀
  have hsplit : 2 * Real.pi * Complex.I * ((1 : ℤ) : ℂ) * (θ : ℂ)
      = Complex.I * ((2 * Real.pi * (θ - (n₀ : ℝ)) : ℝ) : ℂ)
          + (n₀ : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [Work.KMTAreas.ADev.chr]
  rw [hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- `zGap θ = 2 |sin (π (θ - n₀))|`. -/
lemma zGap_eq_two_sin (θ : ℝ) :
    Work.KMTAreas.A7.zGap θ
      = 2 * |Real.sin ((2 * Real.pi * (θ - (Work.KMTAreas.A7.nearInt θ : ℝ))) / 2)| := by
  rw [Work.KMTAreas.A7.zGap, chr_one_eq_exp, norm_sub_rev,
    Complex.norm_exp_I_mul_ofReal_sub_one]
  simp

/-- The lower comparability `4 δ ≤ zGap θ`. -/
lemma zGap_lower (θ : ℝ) : 4 * Work.KMTAreas.A7.nearDist θ ≤ Work.KMTAreas.A7.zGap θ := by
  set n₀ : ℤ := Work.KMTAreas.A7.nearInt θ with hn₀
  set δ : ℝ := Work.KMTAreas.A7.nearDist θ with hδ
  have hδeq : δ = |θ - (n₀ : ℝ)| := by rw [hδ, hn₀, Work.KMTAreas.A7.nearDist]
  have hδhalf : δ ≤ 1 / 2 := by rw [hδ]; exact nearDist_le_half θ
  set x : ℝ := 2 * Real.pi * (θ - (n₀ : ℝ)) with hx
  have hchr : Work.KMTAreas.ADev.chr 1 θ = Complex.exp (Complex.I * (x : ℂ)) := by
    have hsplit : 2 * Real.pi * Complex.I * ((1 : ℤ) : ℂ) * (θ : ℂ)
        = Complex.I * (x : ℂ) + (n₀ : ℂ) * (2 * Real.pi * Complex.I) := by
      rw [hx]; push_cast; ring
    rw [Work.KMTAreas.ADev.chr]
    rw [hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hzg : Work.KMTAreas.A7.zGap θ = 2 * |Real.sin (x / 2)| := by
    rw [Work.KMTAreas.A7.zGap, hchr, norm_sub_rev, Complex.norm_exp_I_mul_ofReal_sub_one]
    simp
  have hxhalf : |x / 2| = Real.pi * δ := by
    rw [hx]
    rw [show 2 * Real.pi * (θ - (n₀ : ℝ)) / 2 = Real.pi * (θ - (n₀ : ℝ)) by ring]
    rw [abs_mul, abs_of_pos Real.pi_pos, ← hδeq]
  have hπ2 : |x / 2| ≤ Real.pi / 2 := by
    rw [hxhalf]; nlinarith [Real.pi_pos, hδhalf]
  have hkey := Real.mul_abs_le_abs_sin hπ2
  rw [hxhalf] at hkey
  have hsimp : 2 / Real.pi * (Real.pi * δ) = 2 * δ := by
    field_simp
  rw [hzg]
  linarith

/-- The upper comparability `zGap θ ≤ 2 π δ`. -/
lemma zGap_upper (θ : ℝ) :
    Work.KMTAreas.A7.zGap θ ≤ 2 * Real.pi * Work.KMTAreas.A7.nearDist θ := by
  set n₀ : ℤ := Work.KMTAreas.A7.nearInt θ with hn₀
  set δ : ℝ := Work.KMTAreas.A7.nearDist θ with hδ
  have hδeq : δ = |θ - (n₀ : ℝ)| := by rw [hδ, hn₀, Work.KMTAreas.A7.nearDist]
  set x : ℝ := 2 * Real.pi * (θ - (n₀ : ℝ)) with hx
  have hchr : Work.KMTAreas.ADev.chr 1 θ = Complex.exp (Complex.I * (x : ℂ)) := by
    have hsplit : 2 * Real.pi * Complex.I * ((1 : ℤ) : ℂ) * (θ : ℂ)
        = Complex.I * (x : ℂ) + (n₀ : ℂ) * (2 * Real.pi * Complex.I) := by
      rw [hx]; push_cast; ring
    rw [Work.KMTAreas.ADev.chr]
    rw [hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hzg : Work.KMTAreas.A7.zGap θ = 2 * |Real.sin (x / 2)| := by
    rw [Work.KMTAreas.A7.zGap, hchr, norm_sub_rev, Complex.norm_exp_I_mul_ofReal_sub_one]
    simp
  have hxhalf : |x / 2| = Real.pi * δ := by
    rw [hx]
    rw [show 2 * Real.pi * (θ - (n₀ : ℝ)) / 2 = Real.pi * (θ - (n₀ : ℝ)) by ring]
    rw [abs_mul, abs_of_pos Real.pi_pos, ← hδeq]
  have h : |Real.sin (x / 2)| ≤ |x / 2| := Real.abs_sin_le_abs
  rw [hxhalf] at h
  rw [hzg, hδ]
  linarith

/-- No integer other than the nearest one is within distance `1/2` of `θ`. -/
lemma half_le_abs_sub_of_ne_nearInt (θ : ℝ) {k : ℤ} (hk : k ≠ Work.KMTAreas.A7.nearInt θ) :
    (1 : ℝ) / 2 ≤ |θ - (k : ℝ)| := by
  have hne : k - Work.KMTAreas.A7.nearInt θ ≠ 0 := sub_ne_zero.mpr hk
  have h1 : (1 : ℤ) ≤ |k - Work.KMTAreas.A7.nearInt θ| := Int.one_le_abs hne
  have h2 : (1 : ℝ) ≤ |(k : ℝ) - (Work.KMTAreas.A7.nearInt θ : ℝ)| := by
    have h1' : (1 : ℝ) ≤ ((|k - Work.KMTAreas.A7.nearInt θ| : ℤ) : ℝ) := by
      exact_mod_cast h1
    rwa [Int.cast_abs, Int.cast_sub] at h1'
  have h4 : |(k : ℝ) - (Work.KMTAreas.A7.nearInt θ : ℝ)|
      ≤ |(k : ℝ) - θ| + |θ - (Work.KMTAreas.A7.nearInt θ : ℝ)| := abs_sub_le _ _ _
  have h5 : |θ - (Work.KMTAreas.A7.nearInt θ : ℝ)| ≤ 1 / 2 := abs_sub_nearInt_le_half θ
  rw [abs_sub_comm]
  linarith

/-- Every integer other than the nearest one is at most twice as far from `n₀` as from `θ`. -/
lemma abs_sub_nearInt_le_two_mul_abs_sub (θ : ℝ) {k : ℤ}
    (hk : k ≠ Work.KMTAreas.A7.nearInt θ) :
    |(k : ℝ) - (Work.KMTAreas.A7.nearInt θ : ℝ)| ≤ 2 * |θ - (k : ℝ)| := by
  have h4 : (1 : ℝ) / 2 ≤ |θ - (k : ℝ)| := half_le_abs_sub_of_ne_nearInt θ hk
  have h5 : |θ - (Work.KMTAreas.A7.nearInt θ : ℝ)| ≤ 1 / 2 := abs_sub_nearInt_le_half θ
  have htri : |(k : ℝ) - (Work.KMTAreas.A7.nearInt θ : ℝ)|
      ≤ |(k : ℝ) - θ| + |θ - (Work.KMTAreas.A7.nearInt θ : ℝ)| := abs_sub_le _ _ _
  have h6 : |(k : ℝ) - θ| = |θ - (k : ℝ)| := abs_sub_comm _ _
  linarith

/-- **The consolidated statement.**  All the elementary facts about `nearInt`, `nearDist` and
`zGap` that the lacunary deviation symbol bound uses. -/
theorem lacDevNearIntK (θ : ℝ) :
    Work.KMTAreas.A7.nearDist θ ≤ 1 / 2 ∧ 4 * Work.KMTAreas.A7.nearDist θ ≤ Work.KMTAreas.A7.zGap θ ∧
      Work.KMTAreas.A7.zGap θ ≤ 2 * Real.pi * Work.KMTAreas.A7.nearDist θ ∧
      (∀ k : ℤ, k ≠ Work.KMTAreas.A7.nearInt θ → (1 : ℝ) / 2 ≤ |θ - (k : ℝ)|) ∧
      (∀ k : ℤ, k ≠ Work.KMTAreas.A7.nearInt θ →
        |(k : ℝ) - (Work.KMTAreas.A7.nearInt θ : ℝ)| ≤ 2 * |θ - (k : ℝ)|) :=
  ⟨nearDist_le_half θ, zGap_lower θ, zGap_upper θ,
    fun k hk => half_le_abs_sub_of_ne_nearInt θ (k := k) hk,
    fun k hk => abs_sub_nearInt_le_two_mul_abs_sub θ (k := k) hk⟩

end

end Work.KMTAreas.A7LoLin
