import Mathlib
import Submission.Work.RPB.B5.sqrt_sin_sq_arcsin_sq
import Submission.Work.RPB.B5.continuousAt_zero_abs_bound

namespace Work.RPB.B5

/-- Let `G` be a function with `G 0 = 0` that is negative on some `(-ε, 0)` and satisfies
`G ρ = sin²(√ρ)` for `ρ ∈ (0, π²/4]`, and let `u` be a continuous function with `u 0 = 0` and
`G (u σ) = -σ` for `σ ∈ (-κ, κ)`. Then for `σ ∈ (-min κ 1, 0)` the value `u σ` is *forced* to be
the "good branch" `(arcsin √(-σ))²` of the level set, hence lies in `(0, π²/4)`. -/
theorem level_inverse_arcsin_sq {G u : ℝ → ℝ} {κ : ℝ} (hκ : 0 < κ)
    (hG0 : G 0 = 0)
    (hGneg : ∃ ε : ℝ, 0 < ε ∧ ∀ ρ ∈ Set.Ioo (-ε) 0, G ρ < 0)
    (hGsin : ∀ ρ ∈ Set.Ioc (0 : ℝ) (Real.pi ^ 2 / 4),
      G ρ = (Real.sin (Real.sqrt ρ)) ^ 2)
    (hu : ContinuousOn u (Set.Ioo (-κ) κ)) (hu0 : u 0 = 0)
    (hlvl : ∀ σ ∈ Set.Ioo (-κ) κ, G (u σ) = -σ) :
    ∀ σ ∈ Set.Ioo (-(min κ 1)) 0,
      u σ = (Real.arcsin (Real.sqrt (-σ))) ^ 2 ∧ 0 < u σ ∧ u σ < Real.pi ^ 2 / 4 := by
  obtain ⟨ε, hεpos, hεneg⟩ := hGneg
  have hpi4pos : (0 : ℝ) < Real.pi ^ 2 / 4 :=
    div_pos (pow_pos Real.pi_pos 2) (by norm_num)
  -- The value of `G` at the right endpoint of the branch.
  have hGpi4 : G (Real.pi ^ 2 / 4) = 1 := by
    rw [hGsin (Real.pi ^ 2 / 4) ⟨hpi4pos, le_refl _⟩]
    have hs : Real.sqrt (Real.pi ^ 2 / 4) = Real.pi / 2 := by
      rw [show Real.pi ^ 2 / 4 = (Real.pi / 2) ^ 2 by ring]
      exact Real.sqrt_sq (by positivity)
    rw [hs, Real.sin_pi_div_two]
    norm_num
  -- Continuity of `u` at `0`.
  have h0mem : Set.Ioo (-κ) κ ∈ nhds (0 : ℝ) :=
    isOpen_Ioo.mem_nhds ⟨by linarith, hκ⟩
  have hcont0 : ContinuousAt u 0 := hu.continuousAt h0mem
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := continuousAt_zero_abs_bound hcont0 hu0 hεpos
  have hminpos : (0 : ℝ) < min δ₁ κ := lt_min hδ₁pos hκ
  -- Block A: `u` is positive just to the left of `0`.  Near `0`, `u` is within `(-ε, ε)`; it is
  -- nonzero there (`G (u σ) = -σ ≠ 0`), and were it negative then `G (u σ) < 0` by hypothesis
  -- although `G (u σ) = -σ > 0`.
  have keyA : ∀ σ ∈ Set.Ioo (-(min δ₁ κ)) 0, 0 < u σ := by
    intro σ hσ
    obtain ⟨hσl, hσr⟩ := hσ
    have habs : |σ| < min δ₁ κ := by
      rw [abs_lt]; exact ⟨hσl, by linarith⟩
    have hu_lt : |u σ| < ε := hδ₁ σ (lt_of_lt_of_le habs (min_le_left _ _))
    have hσκ : σ ∈ Set.Ioo (-κ) κ :=
      ⟨by linarith [min_le_right δ₁ κ], by linarith⟩
    have hlvlσ : G (u σ) = -σ := hlvl σ hσκ
    have hne : u σ ≠ 0 := by
      intro h0
      rw [h0, hG0] at hlvlσ
      linarith
    rcases lt_trichotomy (u σ) 0 with h | h | h
    · exfalso
      have hεneg' : G (u σ) < 0 :=
        hεneg (u σ) ⟨by linarith [(abs_lt.mp hu_lt).1], h⟩
      linarith
    · exact absurd h hne
    · exact h
  -- Block B: `u` does not vanish on `I = (-(min κ 1), 0)`.
  have keyB : ∀ σ ∈ Set.Ioo (-(min κ 1)) 0, u σ ≠ 0 := by
    intro σ hσ h0
    have hσκ : σ ∈ Set.Ioo (-κ) κ :=
      ⟨by linarith [hσ.1, min_le_left κ 1], by linarith [hσ.2, hκ]⟩
    have := hlvl σ hσκ
    rw [h0, hG0] at this
    linarith [hσ.2]
  -- Block C: `u` is positive on `I`.  A negative value would force, by the intermediate value
  -- theorem applied between `σ` and a point near `0⁻` where `u > 0`, an interior zero of `u`.
  have keyC : ∀ σ ∈ Set.Ioo (-(min κ 1)) 0, 0 < u σ := by
    intro σ hσ
    rcases lt_trichotomy (u σ) 0 with h | h | h
    · exfalso
      obtain ⟨σ₁, hσ₁⟩ := exists_between
        (show max σ (-(min δ₁ κ)) < 0 from max_lt hσ.2 (by linarith))
      have hσ₁_gt : σ < σ₁ := lt_of_le_of_lt (le_max_left _ _) hσ₁.1
      have hσ₁_gt_neg : -(min δ₁ κ) < σ₁ := lt_of_le_of_lt (le_max_right _ _) hσ₁.1
      have hσ₁_lt : σ₁ < 0 := hσ₁.2
      have hpos₁ : 0 < u σ₁ := keyA σ₁ ⟨hσ₁_gt_neg, hσ₁_lt⟩
      have hcont : ContinuousOn u (Set.Icc σ σ₁) := hu.mono (by
        intro x hx
        obtain ⟨hx1, hx2⟩ := hx
        have hσκ : -κ < σ := by linarith [hσ.1, min_le_left κ 1]
        have hσ₁κ : σ₁ < κ := by linarith [hσ₁_gt_neg, min_le_right δ₁ κ]
        exact ⟨by linarith, by linarith⟩)
      obtain ⟨x, hx, hxu⟩ := (intermediate_value_Ioo hσ₁_gt.le hcont)
        (show (0 : ℝ) ∈ Set.Ioo (u σ) (u σ₁) from ⟨h, hpos₁⟩)
      have hxI : x ∈ Set.Ioo (-(min κ 1)) 0 :=
        ⟨by linarith [hx.1, hσ.1], by linarith [hx.2, hσ₁_lt]⟩
      exact keyB x hxI hxu
    · exact absurd h (keyB σ hσ)
    · exact h
  -- Block D: `u` stays below `π²/4` on `I`.  A value above `π²/4` would force, by the intermediate
  -- value theorem between `σ` and `0`, an interior point with `u = π²/4`; there `G (u) = 1`, i.e.
  -- `σ = -1`, which is outside `I`.
  have keyD : ∀ σ ∈ Set.Ioo (-(min κ 1)) 0, u σ ≤ Real.pi ^ 2 / 4 := by
    intro σ hσ
    by_contra hcon
    rw [not_le] at hcon
    have hcont : ContinuousOn u (Set.Icc σ 0) := hu.mono (by
      intro x hx
      obtain ⟨hx1, hx2⟩ := hx
      have hσκ : -κ < σ := by linarith [hσ.1, min_le_left κ 1]
      exact ⟨by linarith, by linarith [hκ]⟩)
    obtain ⟨x, hx, hxu⟩ := (intermediate_value_Ioo' hσ.2.le hcont)
      (show (Real.pi ^ 2 / 4 : ℝ) ∈ Set.Ioo (u 0) (u σ) from
        ⟨by rw [hu0]; exact hpi4pos, hcon⟩)
    have hxI : x ∈ Set.Ioo (-(min κ 1)) 0 :=
      ⟨by linarith [hx.1, hσ.1], by linarith [hx.2]⟩
    have hxκ : x ∈ Set.Ioo (-κ) κ :=
      ⟨by linarith [hxI.1, min_le_left κ 1], by linarith [hx.2, hκ]⟩
    have hGx : G (u x) = -x := hlvl x hxκ
    rw [hxu, hGpi4] at hGx
    have hx1 : x = -1 := by linarith
    linarith [hxI.1, min_le_right κ 1]
  -- Assembly: on `I`, `0 < u σ ≤ π²/4`, so `G (u σ) = sin²(√(u σ)) = -σ`; the "good branch"
  -- identity then gives `u σ = (arcsin √(-σ))²`, and the strict bound follows because
  -- `u σ = π²/4` would force `σ = -1 ∉ I`.
  intro σ hσ
  have hpos : 0 < u σ := keyC σ hσ
  have hle : u σ ≤ Real.pi ^ 2 / 4 := keyD σ hσ
  have hGσ : G (u σ) = (Real.sin (Real.sqrt (u σ))) ^ 2 :=
    hGsin (u σ) ⟨hpos, hle⟩
  have hσκ : σ ∈ Set.Ioo (-κ) κ :=
    ⟨by linarith [hσ.1, min_le_left κ 1], by linarith [hσ.2, hκ]⟩
  have hlvlσ : G (u σ) = -σ := hlvl σ hσκ
  have hsin2 : (Real.sin (Real.sqrt (u σ))) ^ 2 = -σ := by
    rw [hGσ] at hlvlσ; exact hlvlσ
  have htrig : (Real.arcsin (Real.sqrt (-σ))) ^ 2 = u σ := by
    have := (sqrt_sin_sq_arcsin_sq hpos hle).2
    rw [hsin2] at this
    exact this
  refine ⟨htrig.symm, hpos, ?_⟩
  have hne : u σ ≠ Real.pi ^ 2 / 4 := by
    intro heq
    have h1 := hlvlσ
    rw [heq, hGpi4] at h1
    have h2 : σ = -1 := by linarith
    linarith [hσ.1, min_le_right κ 1]
  exact lt_of_le_of_ne hle hne

end Work.RPB.B5
