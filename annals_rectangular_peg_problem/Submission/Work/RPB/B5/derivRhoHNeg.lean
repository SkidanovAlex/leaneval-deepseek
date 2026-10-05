import Mathlib

/-!
# The sign of the `ρ`-derivative of the family `ρh`

Let `ρh : ℝ → ℝ → ℝ → ℝ`, written `ρh τ t σ`, be a family which

* is `C⁸` on `[0,1] × ℝ × (-1,1)` (`hh`);
* vanishes along `σ = 0` (`hh0`);
* has nowhere vanishing `σ`-derivative on `(-1,1)` (`hhmono`);
* is positive on `(-1, 0)` (`hhpos`).

Then the `σ`-derivative is negative everywhere on `(-1,1)`.

The mathematical content is one-dimensional: the slice `σ ↦ ρh τ t σ` is `C¹` on the open
interval `(-1,1)`, so its derivative is continuous there and — by `hhmono` — nowhere zero.
Since the interval is connected and the derivative is negative at `0` (because the function is
`0` at `0` and positive immediately to its left), the derivative keeps this sign all along
`(-1,1)`. The sign at `0` follows from the one-sided slope: for `u < 0` the slope
`u⁻¹ * (ρh τ t u - ρh τ t 0) = u⁻¹ * ρh τ t u` is `< 0`, hence its limit — the derivative — is
`≤ 0`, and `hhmono` upgrades `≤` to `<`.

## Contents

* `contDiffOn_rhoH_slice` — the `σ`-slices are `C⁸` on `(-1,1)`;
* `neg_of_neg_of_contOn` — a continuous, nowhere-zero function on `(-1,1)` that is negative at
  `0` is negative on all of `(-1,1)`;
* `derivRhoHNeg` — the requested lemma.
-/

open scoped ContDiff

namespace Work.RPB.B5

/-- The `σ`-slice `σ ↦ ρh τ t σ` of a `C⁸` family `ρh` is again `C⁸` on the open interval
`(-1, 1)`: it is the composition of `z ↦ ρh z.1 z.2.1 z.2.2` with the smooth embedding
`σ ↦ (τ, (t, σ))`, whose image lies in `[0,1] × ℝ × (-1,1)` when `τ ∈ [0,1]`. -/
lemma contDiffOn_rhoH_slice (ρh : ℝ → ℝ → ℝ → ℝ)
    (hh : ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => ρh z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-1) 1))
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0:ℝ) 1) (t : ℝ) :
    ContDiffOn ℝ 8 (fun σ : ℝ => ρh τ t σ) (Set.Ioo (-1) 1) := by
  have hφ : ContDiffOn ℝ 8 (fun σ : ℝ => (τ, (t, σ))) (Set.Ioo (-1) 1) := by fun_prop
  refine hh.comp hφ ?_
  intro σ hσ
  simp only [Set.mem_prod, Set.mem_Icc, Set.mem_univ, true_and]
  exact ⟨hτ, hσ⟩

/-- A continuous function on `(-1, 1)` that never vanishes and is negative at `0` is negative
everywhere on `(-1, 1)`. Indeed, were `h σ > 0` for some `σ`, the intermediate value theorem
applied on the segment between `σ` and `0` would produce a zero of `h`. -/
lemma neg_of_neg_of_contOn (h : ℝ → ℝ)
    (hcont : ContinuousOn h (Set.Ioo (-1) 1))
    (hne : ∀ σ ∈ Set.Ioo (-1) 1, h σ ≠ 0) (h0 : h 0 < 0) :
    ∀ σ ∈ Set.Ioo (-1) 1, h σ < 0 := by
  intro σ hσ
  by_contra hcon
  have hcon' : 0 ≤ h σ := not_lt.mp hcon
  have hpos : 0 < h σ := lt_of_le_of_ne hcon' (Ne.symm (hne σ hσ))
  rcases lt_trichotomy σ 0 with hs | hs | hs
  · have hsub : Set.Icc σ 0 ⊆ Set.Ioo (-1) 1 := by
      intro x hx
      exact ⟨by linarith [hx.1, hσ.1], by linarith [hx.2]⟩
    have hcont' : ContinuousOn h (Set.Icc σ 0) := hcont.mono hsub
    have hmem : (0:ℝ) ∈ Set.Icc (h 0) (h σ) := ⟨le_of_lt h0, le_of_lt hpos⟩
    obtain ⟨c, hc, hc0⟩ := (intermediate_value_Icc' (le_of_lt hs) hcont') hmem
    exact hne c (hsub hc) hc0
  · subst hs; exact absurd h0 (not_lt_of_ge hcon')
  · have hsub : Set.Icc 0 σ ⊆ Set.Ioo (-1) 1 := by
      intro x hx
      exact ⟨by linarith [hx.1], by linarith [hx.2, hσ.2]⟩
    have hcont' : ContinuousOn h (Set.Icc 0 σ) := hcont.mono hsub
    have hmem : (0:ℝ) ∈ Set.Icc (h 0) (h σ) := ⟨le_of_lt h0, le_of_lt hpos⟩
    obtain ⟨c, hc, hc0⟩ := (intermediate_value_Icc (le_of_lt hs) hcont') hmem
    exact hne c (hsub hc) hc0

theorem derivRhoHNeg (ρh : ℝ → ℝ → ℝ → ℝ)
    (hh : ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => ρh z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-1) 1))
    (hh0 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ρh τ t 0 = 0)
    (hhmono : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-1) 1,
      deriv (fun s : ℝ => ρh τ t s) σ ≠ 0)
    (hhpos : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-1) 0, 0 < ρh τ t σ) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-1) 1,
      deriv (fun s : ℝ => ρh τ t s) σ < 0 := by
  intro τ hτ t σ hσ
  let f : ℝ → ℝ := fun s => ρh τ t s
  -- Smoothness of the slice and continuity of its derivative.
  have hslice : ContDiffOn ℝ 8 f (Set.Ioo (-1) 1) :=
    contDiffOn_rhoH_slice ρh hh hτ t
  have hcont : ContinuousOn (deriv f) (Set.Ioo (-1) 1) :=
    hslice.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hne : ∀ σ ∈ Set.Ioo (-1) 1, deriv f σ ≠ 0 :=
    fun σ hσ => hhmono τ hτ t σ hσ
  have h0mem : (0 : ℝ) ∈ Set.Ioo (-1) 1 := ⟨by norm_num, by norm_num⟩
  have hf0 : f 0 = 0 := hh0 τ hτ t
  have hderiv : HasDerivAt f (deriv f 0) 0 :=
    ((hslice.contDiffAt (isOpen_Ioo.mem_nhds h0mem)).differentiableAt (by norm_num)).hasDerivAt
  -- The derivative at `0` is `≤ 0`, from the sign of the one-sided slope.
  have hle : deriv f 0 ≤ 0 := by
    have hslope : Filter.Tendsto (fun u : ℝ => u⁻¹ * f u)
        (nhdsWithin 0 (Set.Iio 0)) (nhds (deriv f 0)) := by
      have h := hderiv.tendsto_slope_zero_left
      simpa [hf0] using h
    have hev : ∀ᶠ u in (nhdsWithin 0 (Set.Iio 0) : Filter ℝ), u⁻¹ * f u ≤ 0 := by
      have h1 : ∀ᶠ u in (nhdsWithin (0:ℝ) (Set.Iio 0)), (-1:ℝ) < u :=
        Filter.Eventually.filter_mono (nhdsWithin_le_nhds (a := (0:ℝ)) (s := Set.Iio 0))
          (Ioi_mem_nhds (by norm_num : (-1:ℝ) < 0))
      have h2 : ∀ᶠ u in (nhdsWithin (0:ℝ) (Set.Iio 0)), u < (0:ℝ) := by
        show Set.Iio (0:ℝ) ∈ nhdsWithin (0:ℝ) (Set.Iio 0)
        exact self_mem_nhdsWithin
      filter_upwards [h1, h2] with u hu1 hu2
      have hpos : 0 < f u := hhpos τ hτ t u ⟨hu1, hu2⟩
      have hinv : u⁻¹ < 0 := inv_lt_zero.mpr hu2
      exact le_of_lt (mul_neg_of_neg_of_pos hinv hpos)
    exact le_of_tendsto (hx := nhdsWithin_Iio_neBot (le_refl (0:ℝ))) hslope hev
  -- Strict negativity at `0`, using that the derivative never vanishes.
  have hlt0 : deriv f 0 < 0 := lt_of_le_of_ne hle (hne 0 h0mem)
  -- Sign propagation over the connected interval `(-1,1)`.
  exact neg_of_neg_of_contOn (deriv f) hcont hne hlt0 σ hσ

end Work.RPB.B5
