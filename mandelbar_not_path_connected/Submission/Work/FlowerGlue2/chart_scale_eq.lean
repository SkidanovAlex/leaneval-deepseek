import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.unusedVariables false

namespace Work.FlowerGlue2

/-! ## Chart scales at a parabolic fixed point are unique

If `F` is conjugated to a germ `u ↦ u + u² h u` (with `h` near `1` near `0`) by two
linear charts `u ↦ z₁ + γ u` and `u ↦ z₁ + s u` at the same point `z₁`, then the scales
coincide (`γ = s`) and so do the second-order coefficients (`a₁ = a₂`).

The mathematical content: on the common domain of the two charts one has
`s * f₂ u = γ * f₁ (s / γ * u)`, and writing `fᵢ u = u + u² hᵢ u` with
`hᵢ u = 1 + aᵢ u + O(‖u‖²)` this reads `h₂ u = c * h₁ (c * u)` with `c = s / γ`.
Comparing the identity up to order two then forces `c = 1` (hence `s = γ`) and `a₁ = a₂`.

The two auxiliary lemmas below are the analytic engine: a complex number whose norm is
bounded by `M t` (resp. `B t + C t²`) for every `0 < t < δ` vanihes. -/

/-- A complex number whose norm is bounded by `M * t` for every `0 < t < δ` is zero. -/
lemma eq_zero_of_norm_le_mul {a : ℂ} {δ M : ℝ} (hδ : 0 < δ)
    (h : ∀ t : ℝ, 0 < t → t < δ → ‖a‖ ≤ M * t) : a = 0 := by
  have hnorm : ‖a‖ ≤ 0 := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have ht : 0 < min (δ / 2) (ε / (|M| + 1)) := by
      apply lt_min (by linarith)
      exact div_pos hε (by positivity)
    have hlt : min (δ / 2) (ε / (|M| + 1)) < δ :=
      lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have h1 := h _ ht hlt
    have h2 : M * min (δ / 2) (ε / (|M| + 1))
        ≤ |M| * min (δ / 2) (ε / (|M| + 1)) :=
      mul_le_mul_of_nonneg_right (le_abs_self M) (le_of_lt ht)
    have h3 : |M| * min (δ / 2) (ε / (|M| + 1)) ≤ |M| * (ε / (|M| + 1)) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) (abs_nonneg M)
    have h4 : |M| * (ε / (|M| + 1)) < ε := by
      rw [← mul_div_assoc, div_lt_iff₀ (by positivity : (0:ℝ) < |M| + 1)]
      nlinarith [hε]
    linarith
  exact norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg a))

/-- A complex number whose norm is bounded by `B * t + C * t ^ 2` for every `0 < t < δ`
is zero. -/
lemma eq_zero_of_norm_le_quad {a : ℂ} {δ B C : ℝ} (hδ : 0 < δ)
    (h : ∀ t : ℝ, 0 < t → t < δ → ‖a‖ ≤ B * t + C * t ^ 2) : a = 0 := by
  refine eq_zero_of_norm_le_mul hδ (M := B + max C 0 * δ) ?_
  intro t ht htδ
  have h1 := h t ht htδ
  have ht2 : t ^ 2 ≤ δ * t := by nlinarith [ht, htδ]
  have hC : C * t ^ 2 ≤ max C 0 * (δ * t) := by
    calc C * t ^ 2 ≤ max C 0 * t ^ 2 :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg t)
      _ ≤ max C 0 * (δ * t) := mul_le_mul_of_nonneg_left ht2 (le_max_right _ _)
  nlinarith [h1, hC]

theorem chart_scale_eq {F : ℂ → ℂ} {z₁ γ s : ℂ} (hγ : γ ≠ 0) (hs : s ≠ 0)
    {f₁ h₁ : ℂ → ℂ} {a₁ : ℂ} {r₁ A₁ : ℝ} {f₂ h₂ : ℂ → ℂ} {a₂ : ℂ} {r₂ A₂ : ℝ}
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hf₁ : ∀ z : ℂ, ‖z‖ < r₁ → f₁ z = z + z ^ 2 * h₁ z)
    (hb₁ : ∀ z : ℂ, ‖z‖ < r₁ → ‖h₁ z - 1 - a₁ * z‖ ≤ A₁ * ‖z‖ ^ 2)
    (hc₁ : ContinuousAt h₁ 0)
    (hf₂ : ∀ z : ℂ, ‖z‖ < r₂ → f₂ z = z + z ^ 2 * h₂ z)
    (hb₂ : ∀ z : ℂ, ‖z‖ < r₂ → ‖h₂ z - 1 - a₂ * z‖ ≤ A₂ * ‖z‖ ^ 2)
    (hc₂ : ContinuousAt h₂ 0)
    (hconj₁ : ∀ u : ℂ, ‖u‖ < r₁ → F (z₁ + γ * u) = z₁ + γ * f₁ u)
    (hconj₂ : ∀ u : ℂ, ‖u‖ < r₂ → F (z₁ + s * u) = z₁ + s * f₂ u) :
    γ = s ∧ a₁ = a₂ := by
  -- the ratio of the two chart scales
  set c : ℂ := s / γ with hcdef
  have hγc : γ * c = s := by rw [hcdef]; exact mul_div_cancel₀ s hγ
  have hc_ne : c ≠ 0 := by
    intro hc0
    rw [hc0, mul_zero] at hγc
    exact hs hγc.symm
  have hnc : 0 < ‖c‖ := norm_pos_iff.mpr hc_ne
  -- a radius on which both charts are simultaneously available
  set δ : ℝ := min r₂ (r₁ / ‖c‖) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; exact lt_min hr₂ (div_pos hr₁ hnc)
  have hmain : ∀ u : ℂ, ‖u‖ < δ → ‖u‖ < r₂ ∧ ‖c * u‖ < r₁ := by
    intro u hu
    have hδ2 : δ ≤ r₂ := by rw [hδdef]; exact min_le_left _ _
    have hδ1 : δ ≤ r₁ / ‖c‖ := by rw [hδdef]; exact min_le_right _ _
    refine ⟨lt_of_lt_of_le hu hδ2, ?_⟩
    rw [norm_mul]
    calc ‖c‖ * ‖u‖ < ‖c‖ * (r₁ / ‖c‖) :=
          mul_lt_mul_of_pos_left (lt_of_lt_of_le hu hδ1) hnc
      _ = r₁ := mul_div_cancel₀ r₁ (ne_of_gt hnc)
  -- the two normal forms agree on the common domain: `h₂ u = c * h₁ (c * u)`
  have hrel : ∀ u : ℂ, u ≠ 0 → ‖u‖ < δ → h₂ u = c * h₁ (c * u) := by
    intro u hu hult
    obtain ⟨hu₂, hcu₁⟩ := hmain u hult
    have e1 : F (z₁ + s * u) = z₁ + s * f₂ u := hconj₂ u hu₂
    have e2 : F (z₁ + γ * (c * u)) = z₁ + γ * f₁ (c * u) := hconj₁ (c * u) hcu₁
    have e3 : s * u = γ * (c * u) := by rw [← hγc]; ring
    have e4 : s * f₂ u = γ * f₁ (c * u) := by
      have h := e1
      rw [e3] at h
      rw [e2] at h
      exact (add_left_cancel h).symm
    have e5 : c * f₂ u = f₁ (c * u) :=
      mul_left_cancel₀ hγ (by rw [← mul_assoc, hγc]; exact e4)
    rw [hf₂ u hu₂, hf₁ (c * u) hcu₁] at e5
    have hcu2 : c * u ^ 2 ≠ 0 := mul_ne_zero hc_ne (pow_ne_zero 2 hu)
    apply mul_left_cancel₀ hcu2
    have h := e5
    ring_nf at h ⊢
    linear_combination h
  -- comparing the identity to second order
  have hbound : ∀ u : ℂ, u ≠ 0 → ‖u‖ < δ →
      ‖(c - 1) + (a₁ * c ^ 2 - a₂) * u‖ ≤ (A₂ + ‖c‖ ^ 3 * A₁) * ‖u‖ ^ 2 := by
    intro u hu hult
    obtain ⟨hu₂, hcu₁⟩ := hmain u hult
    have hh := hrel u hu hult
    have hEq : (c - 1) + (a₁ * c ^ 2 - a₂) * u
        = (h₂ u - 1 - a₂ * u) - c * (h₁ (c * u) - 1 - a₁ * (c * u)) := by
      rw [hh]; ring
    rw [hEq]
    calc ‖(h₂ u - 1 - a₂ * u) - c * (h₁ (c * u) - 1 - a₁ * (c * u))‖
        ≤ ‖h₂ u - 1 - a₂ * u‖ + ‖c * (h₁ (c * u) - 1 - a₁ * (c * u))‖ := norm_sub_le _ _
      _ = ‖h₂ u - 1 - a₂ * u‖ + ‖c‖ * ‖h₁ (c * u) - 1 - a₁ * (c * u)‖ := by rw [norm_mul]
      _ ≤ A₂ * ‖u‖ ^ 2 + ‖c‖ * (A₁ * ‖c * u‖ ^ 2) :=
          add_le_add (hb₂ u hu₂) (mul_le_mul_of_nonneg_left (hb₁ (c * u) hcu₁) (norm_nonneg c))
      _ = (A₂ + ‖c‖ ^ 3 * A₁) * ‖u‖ ^ 2 := by rw [norm_mul]; ring
  -- first conclusion: `c = 1`
  have hc1 : c = 1 := by
    have key : c - 1 = 0 := by
      refine eq_zero_of_norm_le_quad hδpos
        (B := ‖a₁ * c ^ 2 - a₂‖) (C := A₂ + ‖c‖ ^ 3 * A₁) ?_
      intro t ht htδ
      have hut : (t : ℂ) ≠ 0 := by simp [ht.ne']
      have hnt : ‖(t : ℂ)‖ = t := by simp [abs_of_pos ht]
      have hb := hbound (t : ℂ) hut (by rw [hnt]; exact htδ)
      rw [hnt] at hb
      have hsplit : ((c - 1) + (a₁ * c ^ 2 - a₂) * (t : ℂ)) - (a₁ * c ^ 2 - a₂) * (t : ℂ)
          = c - 1 := by ring
      calc ‖c - 1‖
          = ‖((c - 1) + (a₁ * c ^ 2 - a₂) * (t : ℂ)) - (a₁ * c ^ 2 - a₂) * (t : ℂ)‖ := by
            rw [hsplit]
        _ ≤ ‖(c - 1) + (a₁ * c ^ 2 - a₂) * (t : ℂ)‖ + ‖(a₁ * c ^ 2 - a₂) * (t : ℂ)‖ :=
            norm_sub_le _ _
        _ = ‖(c - 1) + (a₁ * c ^ 2 - a₂) * (t : ℂ)‖ + ‖a₁ * c ^ 2 - a₂‖ * t := by
            rw [norm_mul, hnt]
        _ ≤ (A₂ + ‖c‖ ^ 3 * A₁) * t ^ 2 + ‖a₁ * c ^ 2 - a₂‖ * t := by linarith [hb]
        _ = ‖a₁ * c ^ 2 - a₂‖ * t + (A₂ + ‖c‖ ^ 3 * A₁) * t ^ 2 := by ring
    exact sub_eq_zero.mp key
  -- second conclusion: `a₁ = a₂`
  have ha : a₁ = a₂ := by
    have key : a₁ - a₂ = 0 := by
      refine eq_zero_of_norm_le_quad hδpos (B := A₁ + A₂) (C := 0) ?_
      intro t ht htδ
      have hut : (t : ℂ) ≠ 0 := by simp [ht.ne']
      have hnt : ‖(t : ℂ)‖ = t := by simp [abs_of_pos ht]
      have hrel' : h₂ (t : ℂ) = h₁ (t : ℂ) := by
        have hh := hrel (t : ℂ) hut (by rw [hnt]; exact htδ)
        rwa [hc1, one_mul, one_mul] at hh
      obtain ⟨ht2, ht1⟩ := hmain (t : ℂ) (by rw [hnt]; exact htδ)
      rw [hc1, one_mul] at ht1
      have hb₁' := hb₁ (t : ℂ) ht1
      have hb₂' := hb₂ (t : ℂ) ht2
      have hrepr : (a₁ - a₂) * (t : ℂ)
          = (h₂ (t : ℂ) - 1 - a₂ * (t : ℂ)) - (h₁ (t : ℂ) - 1 - a₁ * (t : ℂ)) := by
        rw [hrel']; ring
      have hbd : ‖(a₁ - a₂) * (t : ℂ)‖ ≤ (A₁ + A₂) * ‖(t : ℂ)‖ ^ 2 := by
        rw [hrepr]
        calc ‖(h₂ (t : ℂ) - 1 - a₂ * (t : ℂ)) - (h₁ (t : ℂ) - 1 - a₁ * (t : ℂ))‖
            ≤ ‖h₂ (t : ℂ) - 1 - a₂ * (t : ℂ)‖ + ‖h₁ (t : ℂ) - 1 - a₁ * (t : ℂ)‖ :=
              norm_sub_le _ _
          _ ≤ A₂ * ‖(t : ℂ)‖ ^ 2 + A₁ * ‖(t : ℂ)‖ ^ 2 := add_le_add hb₂' hb₁'
          _ = (A₁ + A₂) * ‖(t : ℂ)‖ ^ 2 := by ring
      rw [norm_mul, hnt] at hbd
      have hfin : ‖a₁ - a₂‖ ≤ (A₁ + A₂) * t := by nlinarith [ht, hbd]
      simpa using hfin
    exact sub_eq_zero.mp key
  exact ⟨by rw [hc1, mul_one] at hγc; exact hγc, ha⟩

end Work.FlowerGlue2
