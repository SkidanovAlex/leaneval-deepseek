import Mathlib
import Submission.Work.A7.sum_Icc_eq_endpoints_add_sum_Ico
import Submission.Work.A7.integral_Icc_eq_sum_Ico_unit

namespace Work.KMTAreas.A7

namespace Work.KMTAreas.A7

/-- **The single-unit-interval Lipschitz trapezoid comparison.**
If `u : ℝ → ℂ` is continuous and on `[c, c+1]` the two one-sided Lipschitz bounds
`‖u t - u c‖ ≤ L (t - c)` and `‖u t - u (c+1)‖ ≤ L (c+1 - t)` hold, then the average of the two
endpoint values differs from the integral over `[c, c+1]` by at most `L/2`:
`‖(u c + u (c+1))/2 - ∫_c^{c+1} u‖ ≤ L/2`.

Indeed `(u c + u (c+1))/2 - ∫_c^{c+1} u = ∫_c^{c+1} ((u c + u (c+1))/2 - u t) dt`, the pointwise
bound `‖(u c + u (c+1))/2 - u t‖ ≤ L/2` follows by averaging the two one-sided Lipschitz bounds,
and `∫_c^{c+1}` of the constant `L/2` is `L/2`. -/
theorem unit_trapezoid_lipschitz_aux {u : ℝ → ℂ} (hu : Continuous u) (c : ℝ) {L : ℝ}
    (h : ∀ t ∈ Set.Icc c (c + 1),
      ‖u t - u c‖ ≤ L * (t - c) ∧ ‖u t - u (c + 1)‖ ≤ L * (c + 1 - t)) :
    ‖(u c + u (c + 1)) / 2 - ∫ t in c..(c + 1), u t‖ ≤ L / 2 := by
  have hconst : ∫ t in c..(c + 1), ((u c + u (c + 1)) / 2 : ℂ) = (u c + u (c + 1)) / 2 := by
    rw [intervalIntegral.integral_const]
    simp
  have hid : (u c + u (c + 1)) / 2 - ∫ t in c..(c + 1), u t
      = ∫ t in c..(c + 1), ((u c + u (c + 1)) / 2 - u t) := by
    rw [intervalIntegral.integral_sub (f := fun t : ℝ => (u c + u (c + 1)) / 2) (g := u)
      (a := c) (b := c + 1) intervalIntegrable_const (hu.intervalIntegrable c (c + 1)), hconst]
  rw [hid]
  have hbound : ∀ t ∈ Set.uIoc c (c + 1), ‖(u c + u (c + 1)) / 2 - u t‖ ≤ L / 2 := by
    intro t ht
    rw [Set.uIoc_of_le (by linarith : c ≤ c + 1)] at ht
    obtain ⟨h1, h2⟩ := h t (Set.Ioc_subset_Icc_self ht)
    have h1' : ‖u c - u t‖ ≤ L * (t - c) := by rw [norm_sub_rev]; exact h1
    have h2' : ‖u (c + 1) - u t‖ ≤ L * (c + 1 - t) := by rw [norm_sub_rev]; exact h2
    have h3 : ‖(u c - u t) + (u (c + 1) - u t)‖ ≤ L * (t - c) + L * (c + 1 - t) :=
      le_trans (norm_add_le _ _) (add_le_add h1' h2')
    have heq : (u c + u (c + 1)) / 2 - u t = ((u c - u t) + (u (c + 1) - u t)) / 2 := by ring
    have h2n : ‖(2 : ℂ)‖ = 2 := by norm_num
    calc ‖(u c + u (c + 1)) / 2 - u t‖
        = ‖(u c - u t) + (u (c + 1) - u t)‖ / 2 := by rw [heq, norm_div, h2n]
      _ ≤ (L * (t - c) + L * (c + 1 - t)) / 2 := div_le_div_of_nonneg_right h3 (by norm_num)
      _ = L / 2 := by ring
  calc ‖∫ t in c..(c + 1), ((u c + u (c + 1)) / 2 - u t)‖
      ≤ (L / 2) * |(c + 1) - c| := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    _ = L / 2 := by rw [show (c + 1) - c = 1 from by ring, abs_one, mul_one]

/-- First-order (Euler–Maclaurin / trapezoid) comparison of the sum over the integers of `[a,b]`
with the integral over `[a,b]`: for a continuous `w : ℝ → ℂ` whose two endpoint values are bounded
by `B` and which is `L`-Lipschitz on `[a,b]`, the sum differs from the integral by at most
`B + L * (b - a) / 2`. -/
theorem unit_step_lipschitz_trapezoid (w : ℝ → ℂ) (hw : Continuous w) {a b : ℤ} (hab : a ≤ b)
    {B L : ℝ} (hB0 : 0 ≤ B) (hL0 : 0 ≤ L)
    (hend₁ : ‖w (a : ℝ)‖ ≤ B) (hend₂ : ‖w (b : ℝ)‖ ≤ B)
    (hLip : ∀ x ∈ Set.Icc (a : ℝ) (b : ℝ), ∀ y ∈ Set.Icc (a : ℝ) (b : ℝ),
      ‖w y - w x‖ ≤ L * |y - x|) :
    ‖(∑ n ∈ Finset.Icc a b, w (n : ℝ)) - ∫ t in (a : ℝ)..(b : ℝ), w t‖
      ≤ B + L * ((b : ℝ) - (a : ℝ)) / 2 := by
  classical
  -- Decompose both the sum and the integral into the unit pieces `[n, n+1]`, `n ∈ [a, b)`.
  have hsum := _root_.Work.A7.sum_Icc_eq_endpoints_add_sum_Ico w hab
  have hint := _root_.Work.A7.integral_Icc_eq_sum_Ico_unit w hw hab
  have hdecomp : (∑ n ∈ Finset.Icc a b, w (n : ℝ)) - ∫ t in (a : ℝ)..(b : ℝ), w t
      = (w (a : ℝ) + w (b : ℝ)) / 2
        + ∑ n ∈ Finset.Ico a b,
            ((w (n : ℝ) + w ((n : ℝ) + 1)) / 2 - ∫ t in (n : ℝ)..((n : ℝ) + 1), w t) := by
    rw [hsum, hint, Finset.sum_sub_distrib]
    ring
  rw [hdecomp]
  -- The two endpoint values contribute at most `B`.
  have hend : ‖(w (a : ℝ) + w (b : ℝ)) / 2‖ ≤ B := by
    have h2n : ‖(2 : ℂ)‖ = 2 := by norm_num
    have h : ‖(w (a : ℝ) + w (b : ℝ)) / 2‖ ≤ (‖w (a : ℝ)‖ + ‖w (b : ℝ)‖) / 2 := by
      rw [norm_div, h2n]
      exact div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)
    linarith
  -- Each unit interval contributes at most `L/2`.
  have hterm : ∀ n ∈ Finset.Ico a b,
      ‖((w (n : ℝ) + w ((n : ℝ) + 1)) / 2 - ∫ t in (n : ℝ)..((n : ℝ) + 1), w t)‖ ≤ L / 2 := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    obtain ⟨hna, hnb⟩ := hn
    have hnb1 : n + 1 ≤ b := by omega
    have hnlb : (n : ℝ) + 1 ≤ (b : ℝ) := by
      have h : ((n + 1 : ℤ) : ℝ) ≤ (b : ℝ) := by exact_mod_cast hnb1
      simpa using h
    have hnal : (a : ℝ) ≤ (n : ℝ) := by exact_mod_cast hna
    have hnub : (n : ℝ) ≤ (b : ℝ) := by exact_mod_cast (le_of_lt hnb)
    refine unit_trapezoid_lipschitz_aux hw (n : ℝ) ?_
    intro t ht
    have htI : t ∈ Set.Icc (a : ℝ) (b : ℝ) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hnI : (n : ℝ) ∈ Set.Icc (a : ℝ) (b : ℝ) := ⟨hnal, hnub⟩
    have hn1I : (n : ℝ) + 1 ∈ Set.Icc (a : ℝ) (b : ℝ) := ⟨by linarith, hnlb⟩
    constructor
    · have h := hLip (n : ℝ) hnI t htI
      rwa [abs_of_nonneg (by linarith [ht.1] : (0 : ℝ) ≤ t - (n : ℝ))] at h
    · have h := hLip ((n : ℝ) + 1) hn1I t htI
      rw [abs_sub_comm] at h
      rwa [abs_of_nonneg (by linarith [ht.2] : (0 : ℝ) ≤ ((n : ℝ) + 1) - t)] at h
  -- The interval `[a, b)` contains exactly `b - a` integers.
  have hcard : ((Finset.Ico a b).card : ℝ) = (b : ℝ) - (a : ℝ) := by
    have hZ : ((Finset.Ico a b).card : ℤ) = b - a := Int.card_Ico_of_le a b hab
    have hR := congrArg (fun z : ℤ => (z : ℝ)) hZ
    push_cast at hR
    exact hR
  calc ‖(w (a : ℝ) + w (b : ℝ)) / 2
        + ∑ n ∈ Finset.Ico a b,
            ((w (n : ℝ) + w ((n : ℝ) + 1)) / 2 - ∫ t in (n : ℝ)..((n : ℝ) + 1), w t)‖
      ≤ ‖(w (a : ℝ) + w (b : ℝ)) / 2‖
        + ‖∑ n ∈ Finset.Ico a b,
            ((w (n : ℝ) + w ((n : ℝ) + 1)) / 2 - ∫ t in (n : ℝ)..((n : ℝ) + 1), w t)‖ :=
        norm_add_le _ _
    _ ≤ B + ∑ n ∈ Finset.Ico a b,
            ‖((w (n : ℝ) + w ((n : ℝ) + 1)) / 2 - ∫ t in (n : ℝ)..((n : ℝ) + 1), w t)‖ :=
        add_le_add hend (norm_sum_le _ _)
    _ ≤ B + ∑ n ∈ Finset.Ico a b, L / 2 := add_le_add (le_refl B) (Finset.sum_le_sum hterm)
    _ = B + ((Finset.Ico a b).card : ℝ) * (L / 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = B + L * ((b : ℝ) - (a : ℝ)) / 2 := by rw [hcard]; ring

end Work.KMTAreas.A7

/-- The same statement under the module's own namespace `Work.KMTAreas.A7` (the declaration above
lives at the doubly-nested name `Work.KMTAreas.A7.Work.KMTAreas.A7.unit_step_lipschitz_trapezoid`
inherited from the statement's own `namespace` line). -/
theorem unit_step_lipschitz_trapezoid (w : ℝ → ℂ) (hw : Continuous w) {a b : ℤ} (hab : a ≤ b)
    {B L : ℝ} (hB0 : 0 ≤ B) (hL0 : 0 ≤ L)
    (hend₁ : ‖w (a : ℝ)‖ ≤ B) (hend₂ : ‖w (b : ℝ)‖ ≤ B)
    (hLip : ∀ x ∈ Set.Icc (a : ℝ) (b : ℝ), ∀ y ∈ Set.Icc (a : ℝ) (b : ℝ),
      ‖w y - w x‖ ≤ L * |y - x|) :
    ‖(∑ n ∈ Finset.Icc a b, w (n : ℝ)) - ∫ t in (a : ℝ)..(b : ℝ), w t‖
      ≤ B + L * ((b : ℝ) - (a : ℝ)) / 2 :=
  _root_.Work.KMTAreas.A7.Work.KMTAreas.A7.unit_step_lipschitz_trapezoid
    w hw hab hB0 hL0 hend₁ hend₂ hLip

end Work.KMTAreas.A7
