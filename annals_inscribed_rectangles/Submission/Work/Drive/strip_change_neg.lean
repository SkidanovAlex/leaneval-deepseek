import Mathlib

namespace Work.Drive

/-- `Circle.exp π = -1`. -/
private lemma circle_exp_pi : Circle.exp Real.pi = -1 := by
  apply Subtype.ext
  rw [Circle.coe_exp, Complex.exp_pi_mul_I]
  simp

/-- The set `{x | sin x ≤ 0}` is the union of the closed intervals `[-π + 2πk, 2πk]`, `k ∈ ℤ`. -/
private lemma sin_le_zero_mem_Icc {x : ℝ} (hx : Real.sin x ≤ 0) :
    ∃ k : ℤ, 2 * (k : ℝ) * Real.pi - Real.pi ≤ x ∧ x ≤ 2 * (k : ℝ) * Real.pi := by
  have hp : (0 : ℝ) < Real.pi := Real.pi_pos
  set k : ℤ := ⌊(x + Real.pi) / (2 * Real.pi)⌋ with hk
  refine ⟨k, ?_, ?_⟩
  · have h := Int.floor_le ((x + Real.pi) / (2 * Real.pi))
    rw [← hk] at h
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)] at h
    nlinarith [h]
  · have hlt := Int.lt_floor_add_one ((x + Real.pi) / (2 * Real.pi))
    rw [← hk] at hlt
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)] at hlt
    have hrlt : x - 2 * (k : ℝ) * Real.pi < Real.pi := by nlinarith [hlt]
    have hsin : Real.sin (x - 2 * (k : ℝ) * Real.pi) = Real.sin x := by
      have : (2 * (k : ℝ) * Real.pi) = (k : ℝ) * (2 * Real.pi) := by ring
      rw [this, Real.sin_sub_int_mul_two_pi]
    have hrle : x - 2 * (k : ℝ) * Real.pi ≤ 0 := by
      by_contra hcon
      rw [not_le] at hcon
      have hpos : 0 < Real.sin (x - 2 * (k : ℝ) * Real.pi) :=
        Real.sin_pos_of_pos_of_lt_pi hcon hrlt
      rw [hsin] at hpos
      linarith
    nlinarith [hrle]

private lemma sin_neg_three_pi_div_two : Real.sin (-(3 * Real.pi / 2)) = 1 := by
  rw [Real.sin_neg]
  have h : 3 * Real.pi / 2 = Real.pi / 2 + Real.pi := by ring
  rw [h, Real.sin_add_pi, Real.sin_pi_div_two]
  norm_num

/-- A continuous function on `Icc a b` which vanishes at `a` and has `sin (f t) ≤ 0` everywhere
takes its values in `[-π, 0]`.  Indeed `f '' (Icc a b)` is connected, and the connected component
of `0` in `{x | sin x ≤ 0}` is `[-π, 0]`. -/
private lemma sin_le_zero_Icc_of_continuousOn {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) (hfa : f a = 0)
    (hsin : ∀ t ∈ Set.Icc a b, Real.sin (f t) ≤ 0) :
    ∀ t ∈ Set.Icc a b, -Real.pi ≤ f t ∧ f t ≤ 0 := by
  intro t ht
  have hat : a ≤ t := ht.1
  have htb : t ≤ b := ht.2
  have hcont : ContinuousOn f (Set.Icc a t) := hf.mono (Set.Icc_subset_Icc_right htb)
  constructor
  · -- `-π ≤ f t`: otherwise `f` crosses the value `-3π/2`, where `sin` is positive.
    by_contra hcon
    rw [not_le] at hcon
    obtain ⟨k, hk1, hk2⟩ := sin_le_zero_mem_Icc (hsin t ht)
    have hkneg1 : k ≤ -1 := by
      have hneg : (k : ℝ) < 0 := by nlinarith [Real.pi_pos]
      have hk0 : k < 0 := by exact_mod_cast hneg
      omega
    have hft : f t ≤ -(3 * Real.pi / 2) := by
      have h2 : 2 * (k : ℝ) * Real.pi ≤ -2 * Real.pi := by
        have hkneg : (k : ℝ) ≤ -1 := by exact_mod_cast hkneg1
        nlinarith [Real.pi_pos]
      linarith
    have hmem : -(3 * Real.pi / 2) ∈ Set.Icc (f t) (f a) := by
      refine ⟨hft, ?_⟩
      rw [hfa]; linarith [Real.pi_pos]
    obtain ⟨s, hs, hsf⟩ := (intermediate_value_Icc' hat hcont) hmem
    have hs' : s ∈ Set.Icc a b := ⟨hs.1, le_trans hs.2 htb⟩
    have h3 := hsin s hs'
    rw [hsf, sin_neg_three_pi_div_two] at h3
    linarith
  · -- `f t ≤ 0`: otherwise either `0 < f t < π` directly contradicts `sin ≥ 0` on `(0, π)`,
    -- or `π ≤ f t` and `f` crosses `π/2`.
    by_contra hcon
    rw [not_le] at hcon
    by_cases hpi : f t < Real.pi
    · have hpos := Real.sin_pos_of_pos_of_lt_pi hcon hpi
      linarith [hsin t ht]
    · rw [not_lt] at hpi
      have hmem : Real.pi / 2 ∈ Set.Icc (f a) (f t) := by
        refine ⟨?_, ?_⟩
        · rw [hfa]; linarith [Real.pi_pos]
        · linarith [hpi, Real.pi_pos]
      obtain ⟨s, hs, hsf⟩ := (intermediate_value_Icc hat hcont) hmem
      have hs' : s ∈ Set.Icc a b := ⟨hs.1, le_trans hs.2 htb⟩
      have h3 := hsin s hs'
      rw [hsf, Real.sin_pi_div_two] at h3
      linarith

/-- Angle change of a continuous lift of a path in the circle that stays in the closed upper half
plane, from the direction `-1` to the direction `1`.

Proof idea: with `f t = g t - g a` one has `f a = 0`, `f` continuous on `Icc a b` and
`sin (f t) = -sin (g t) ≤ 0`. Since `{x | sin x ≤ 0}` is the disjoint union of the closed
intervals `[-π + 2πk, 2πk]`, the connected image of `f` lies in one of them, and `f a = 0` forces
it to be `[-π, 0]`. Finally `Circle.exp (g a) = -1` gives `g a ≡ π (mod 2π)` and
`Circle.exp (g b) = 1` gives `g b ∈ 2πℤ`, so `f b ≡ -π (mod 2π)` with `f b ∈ [-π, 0]`, hence
`f b = -π`. -/
theorem strip_change_neg {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : ContinuousOn g (Set.Icc a b)) (hsin : ∀ t ∈ Set.Icc a b, 0 ≤ Real.sin (g t))
    (ha : Circle.exp (g a) = -1) (hb : Circle.exp (g b) = 1) :
    g b - g a = -Real.pi := by
  -- Write the endpoints of the lifted path in terms of integers.
  obtain ⟨m, hm⟩ : ∃ m : ℤ, g a = Real.pi + m * (2 * Real.pi) := by
    rw [← circle_exp_pi, Circle.exp_eq_exp] at ha
    exact ha
  obtain ⟨n, hn⟩ : ∃ n : ℤ, g b = n * (2 * Real.pi) := by
    rw [Circle.exp_eq_one] at hb
    exact hb
  have hsa : Real.sin (g a) = 0 := by
    rw [hm, Real.sin_add_int_mul_two_pi]; exact Real.sin_pi
  have hca : Real.cos (g a) = -1 := by
    rw [hm, Real.cos_add_int_mul_two_pi]; exact Real.cos_pi
  -- The shifted path `f t = g t - g a` starts at `0` and has `sin (f t) ≤ 0`.
  have hfcont : ContinuousOn (fun t => g t - g a) (Set.Icc a b) := hg.sub continuousOn_const
  have hsinf : ∀ t ∈ Set.Icc a b, Real.sin (g t - g a) ≤ 0 := by
    intro t ht
    rw [Real.sin_sub, hsa, hca]
    linarith [hsin t ht]
  have hmain := sin_le_zero_Icc_of_continuousOn hfcont (sub_self (g a)) hsinf
  have hbnd : g b - g a ∈ Set.Icc (-Real.pi) 0 := hmain b (Set.right_mem_Icc.mpr hab)
  -- `g b - g a = -π + 2π(n - m)` lies in `[-π, 0]`, so `n - m = 0`.
  have hval : g b - g a = -Real.pi + ((n - m : ℤ) : ℝ) * (2 * Real.pi) := by
    rw [hn, hm]; push_cast; ring
  have hzero : ((n - m : ℤ) : ℝ) * (2 * Real.pi) = 0 := by
    have h1 : 0 ≤ ((n - m : ℤ) : ℝ) * (2 * Real.pi) := by linarith [hbnd.1]
    have h2 : ((n - m : ℤ) : ℝ) * (2 * Real.pi) ≤ Real.pi := by linarith [hbnd.2]
    have hj0 : 0 ≤ ((n - m : ℤ) : ℝ) := by
      rw [mul_comm] at h1
      exact nonneg_of_mul_nonneg_right h1 (by positivity : (0 : ℝ) < 2 * Real.pi)
    have hj1 : ((n - m : ℤ) : ℝ) < 1 := by
      have h := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).mpr h2
      have h2pi : Real.pi / (2 * Real.pi) = 1 / 2 := by field_simp
      linarith
    have hz : (n - m : ℤ) = 0 := by
      have hz1 : (n - m : ℤ) < 1 := by exact_mod_cast hj1
      have hz0 : (0 : ℤ) ≤ n - m := by exact_mod_cast hj0
      omega
    rw [hz]; norm_num
  linarith [hval, hzero]

end Work.Drive
