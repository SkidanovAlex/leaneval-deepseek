import Mathlib
import Submission.Work.CR.Flat.Cauchy.openSolDefs

namespace Work.NN.Final

open Work.CR.Flat.Cauchy

/-- **Fibre Hölder bound for functions vanishing outside the strip `‖y j‖ ≤ cutOut`.**

Let `f : (Fin n → ℂ) → ℂ` vanish strictly beyond the strip (`hvan`), be bounded by `A` on
`trackSet` (`hsup`) and Hölder of exponent `α` with constant `H` on `trackSet` (`hhol`).
Then `f` is Hölder of exponent `α` with constant `16 ^ α * (A + H)` on the larger set where only
the coordinates `l ≠ j` are tracked.  (`trTrack - cutOut = 1/16`, which is where `16` comes from.)

Proof route: for `a, a'` with `‖a l‖, ‖a' l‖ < trTrack` for `l ≠ j`, split on whether the point is
in `trackSet`; a point that is not in `trackSet` has `trTrack ≤ ‖· j‖`, hence `f = 0` there by
`hvan`.  Cases: both in `trackSet` (use `hhol`, `16 ^ α ≥ 1`); both outside (`0 = 0`); exactly one
inside, say `a` — if `‖a j‖ > cutOut` then `f a = 0`, otherwise `‖a j‖ ≤ cutOut < trTrack ≤ ‖a' j‖`
so `‖a - a'‖ ≥ 1/16` and `‖f a‖ ≤ A ≤ 16 ^ α * (A + H) * ‖a - a'‖ ^ α` using
`16 ^ α * (1/16) ^ α = 1`.  Elementary facts needed: `norm_le_pi_norm`, `Real.one_le_rpow`,
`Real.mul_rpow` / `Real.rpow_mul`, `norm_sub_rev`. -/
theorem fiber_holder_le {n : ℕ} {α : ℝ} (hα0 : 0 < α) {j : Fin n}
    {f : (Fin n → ℂ) → ℂ} {A H : ℝ} (hA0 : 0 ≤ A) (hH0 : 0 ≤ H)
    (hvan : ∀ y : Fin n → ℂ, Work.CR.Flat.Cauchy.cutOut < ‖y j‖ → f y = 0)
    (hsup : ∀ z : Fin n → ℂ, z ∈ Work.CR.Flat.Cauchy.trackSet → ‖f z‖ ≤ A)
    (hhol : ∀ x y : Fin n → ℂ, x ∈ Work.CR.Flat.Cauchy.trackSet →
      y ∈ Work.CR.Flat.Cauchy.trackSet → ‖f x - f y‖ ≤ H * ‖x - y‖ ^ α) :
    ∀ a a' : Fin n → ℂ, (∀ l, l ≠ j → ‖a l‖ < Work.CR.Flat.Cauchy.trTrack) →
      (∀ l, l ≠ j → ‖a' l‖ < Work.CR.Flat.Cauchy.trTrack) →
      ‖f a - f a'‖ ≤ 16 ^ α * (A + H) * ‖a - a'‖ ^ α := by
  have hco : cutOut < trTrack := by rw [cutOut, trTrack]; norm_num
  have hAH : 0 ≤ A + H := add_nonneg hA0 hH0
  have hRH : ∀ c : ℝ, 0 ≤ c → (0:ℝ) ≤ 16 ^ α * (A + H) * c ^ α := fun c hc =>
    mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 16) _) hAH)
      (Real.rpow_nonneg hc _)
  -- Bound by the sup-norm constant `A` when the distance is at least `1/16`.
  have hA_le : ∀ c : ℝ, (1/16 : ℝ) ≤ c → A ≤ 16 ^ α * (A + H) * c ^ α := by
    intro c hc
    have hc0 : 0 ≤ c := le_trans (by norm_num) hc
    have hkey : 1 ≤ (16:ℝ) ^ α * c ^ α := by
      rw [← Real.mul_rpow (by norm_num : (0:ℝ) ≤ 16) hc0]
      exact Real.one_le_rpow (by linarith) (le_of_lt hα0)
    have h2 : (A + H) * ((16:ℝ)^α * c^α) = 16^α * (A + H) * c^α := by ring
    calc A ≤ A + H := by linarith
      _ ≤ (A + H) * ((16:ℝ)^α * c^α) := by
          simpa using mul_le_mul_of_nonneg_left hkey hAH
      _ = 16 ^ α * (A + H) * c ^ α := h2
  -- Bound by the Hölder constant `H`.
  have hH_le : ∀ c : ℝ, 0 ≤ c → H * c ^ α ≤ 16 ^ α * (A + H) * c ^ α := by
    intro c hc
    have h16 : 1 ≤ (16:ℝ) ^ α := Real.one_le_rpow (by norm_num) (le_of_lt hα0)
    have hH1 : H ≤ (16:ℝ)^α * (A+H) := by
      calc H ≤ A + H := by linarith
        _ = 1 * (A + H) := (one_mul _).symm
        _ ≤ (16:ℝ)^α * (A+H) := mul_le_mul_of_nonneg_right h16 hAH
    calc H * c^α ≤ ((16:ℝ)^α * (A+H)) * c^α :=
          mul_le_mul_of_nonneg_right hH1 (Real.rpow_nonneg hc _)
      _ = 16 ^ α * (A + H) * c ^ α := by ring
  -- A point satisfying the outer tracking hypothesis and outside `trackSet` has `trTrack ≤ ‖· j‖`.
  have htrk : ∀ v : Fin n → ℂ, (∀ l, l ≠ j → ‖v l‖ < trTrack) → v ∉ trackSet →
      trTrack ≤ ‖v j‖ := by
    intro v hv hnv
    have hex : ∃ l, trTrack ≤ ‖v l‖ := by
      simpa only [mem_trackSet, not_forall, not_lt] using hnv
    obtain ⟨l, hl⟩ := hex
    have hlj : l = j := by
      by_contra hne
      exact absurd (hv l hne) (not_lt.mpr hl)
    subst hlj
    exact hl
  have hout : ∀ v : Fin n → ℂ, (∀ l, l ≠ j → ‖v l‖ < trTrack) → v ∉ trackSet → f v = 0 := by
    intro v hv hnv
    exact hvan v (lt_of_lt_of_le hco (htrk v hv hnv))
  -- The case "exactly one of the two points is in `trackSet`", first point inside.
  have hstep : ∀ u v : Fin n → ℂ, u ∈ trackSet → v ∉ trackSet →
      (∀ l, l ≠ j → ‖v l‖ < trTrack) →
      ‖f u - f v‖ ≤ 16 ^ α * (A + H) * ‖u - v‖ ^ α := by
    intro u v hu hv hvv
    rw [hout v hvv hv, sub_zero]
    by_cases hju : cutOut < ‖u j‖
    · rw [hvan u hju, norm_zero]
      exact hRH _ (norm_nonneg _)
    · have hju' : ‖u j‖ ≤ cutOut := not_lt.mp hju
      have hdist : (1/16 : ℝ) ≤ ‖u - v‖ := by
        have h1 : trTrack - cutOut ≤ ‖v j‖ - ‖u j‖ := by
          linarith [htrk v hvv hv, hju']
        have h2 : ‖v j‖ - ‖u j‖ ≤ ‖v j - u j‖ := norm_sub_norm_le _ _
        have h3 : ‖v j - u j‖ ≤ ‖v - u‖ := norm_le_pi_norm (v - u) j
        have h4 : ‖v - u‖ = ‖u - v‖ := norm_sub_rev _ _
        have h5 : trTrack - cutOut = 1/16 := by rw [trTrack, cutOut]; norm_num
        linarith [h1, h2, h3, h4.ge, h5]
      calc ‖f u‖ ≤ A := hsup u hu
        _ ≤ 16 ^ α * (A + H) * ‖u - v‖ ^ α := hA_le _ hdist
  intro a a' ha ha'
  by_cases h1 : a ∈ trackSet
  · by_cases h2 : a' ∈ trackSet
    · calc ‖f a - f a'‖ ≤ H * ‖a - a'‖ ^ α := hhol a a' h1 h2
        _ ≤ 16 ^ α * (A + H) * ‖a - a'‖ ^ α := hH_le _ (norm_nonneg _)
    · exact hstep a a' h1 h2 ha'
  · by_cases h2 : a' ∈ trackSet
    · have h := hstep a' a h2 h1 ha
      rw [norm_sub_rev (f a) (f a'), norm_sub_rev a a']
      exact h
    · rw [hout a ha h1, hout a' ha' h2, sub_self, norm_zero]
      exact hRH _ (norm_nonneg _)

end Work.NN.Final
