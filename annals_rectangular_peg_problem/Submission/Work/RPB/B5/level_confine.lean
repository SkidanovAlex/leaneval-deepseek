import Mathlib

namespace Work.RPB.B5

/-- Auxiliary: the level set of `G ∘ u` confines `u` in the strip `(-δ, δ)` and forces
`u` to be positive on the negative half of the interval.

The only analytic input is the intermediate value theorem applied to the continuous
function `u`; the non-continuous function `G` enters solely through the prescribed
sign/level data at `0`, `±δ/2`. -/
theorem level_confine (G u : ℝ → ℝ) (δ η κ : ℝ) (hδ : 0 < δ) (hη : 0 < η) (hκ : κ ≤ η)
    (hG0 : G 0 = 0)
    (hneg : ∀ ρ ∈ Set.Ioo (-δ) 0, G ρ < 0)
    (hGp : η ≤ G (δ / 2)) (hGm : G (-(δ / 2)) ≤ -η)
    (hu : ContinuousOn u (Set.Icc (-κ) κ)) (hu0 : u 0 = 0)
    (hlvl : ∀ σ ∈ Set.Icc (-κ) κ, G (u σ) = -σ) :
    (∀ σ ∈ Set.Icc (-κ) κ, |u σ| < δ) ∧ (∀ σ ∈ Set.Ioo (-κ) 0, 0 < u σ) := by
  have hbound : ∀ σ ∈ Set.Icc (-κ) κ, |u σ| < δ := by
    intro σ hσ
    have hκ0 : 0 ≤ κ := by linarith [hσ.1, hσ.2]
    have hm0 : -(κ) ≤ 0 := by linarith
    -- Intermediate value on any sub-interval of `Icc (-κ) κ`, stated via a disjunction
    -- so that both orderings of the endpoint values can be used.
    have hIVT : ∀ {a b c : ℝ}, a ≤ b → -(κ) ≤ a → b ≤ κ →
        ((u a ≤ c ∧ c ≤ u b) ∨ (u b ≤ c ∧ c ≤ u a)) → ∃ x ∈ Set.Icc a b, u x = c := by
      intro a b c hab ha hb hc
      have hsub : Set.Icc a b ⊆ Set.Icc (-κ) κ :=
        fun y hy => ⟨le_trans ha hy.1, le_trans hy.2 hb⟩
      have hcont : ContinuousOn u (Set.Icc a b) := hu.mono hsub
      rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact intermediate_value_Icc hab hcont ⟨h1, h2⟩
      · exact intermediate_value_Icc' hab hcont ⟨h1, h2⟩
    rw [abs_lt]
    constructor
    · -- the lower bound `-δ < u σ`
      by_contra hcon
      have hcon' : u σ ≤ -δ := not_lt.mp hcon
      rcases lt_trichotomy σ 0 with hσneg | hσ0 | hσpos
      · -- σ < 0 : the path crosses `-δ/2` at a negative level, contradicting `G (-δ/2) ≤ -η`
        have hle : u σ ≤ -(δ / 2) := by linarith
        have hle' : -(δ / 2) ≤ u 0 := by rw [hu0]; linarith
        obtain ⟨x, hx, hxu⟩ :=
          hIVT (a := σ) (b := 0) (c := -(δ / 2)) (le_of_lt hσneg) hσ.1 hκ0 (Or.inl ⟨hle, hle'⟩)
        have hx_mem : x ∈ Set.Icc (-κ) κ := ⟨le_trans hσ.1 hx.1, le_trans hx.2 hκ0⟩
        have hGx : G (-(δ / 2)) = -x := by rw [← hxu]; exact hlvl x hx_mem
        have hxne : x ≠ 0 := by intro h; rw [h, hu0] at hxu; linarith
        have hxlt : x < 0 := lt_of_le_of_ne hx.2 hxne
        linarith [hGx, hGm, hη, hxlt]
      · -- σ = 0 : then `u σ = 0 > -δ`
        have hzero : u σ = 0 := by rw [hσ0]; exact hu0
        linarith [hzero, hcon', hδ]
      · -- 0 < σ : the path crosses `-δ/2` at a positive level `≤ κ`, contradicting `G (-δ/2) ≤ -η`
        have hle : u σ ≤ -(δ / 2) := by linarith
        have hle' : -(δ / 2) ≤ u 0 := by rw [hu0]; linarith
        obtain ⟨x, hx, hxu⟩ :=
          hIVT (a := 0) (b := σ) (c := -(δ / 2)) (le_of_lt hσpos) hm0 hσ.2 (Or.inr ⟨hle, hle'⟩)
        have hx_mem : x ∈ Set.Icc (-κ) κ := ⟨le_trans hm0 hx.1, le_trans hx.2 hσ.2⟩
        have hGx : G (-(δ / 2)) = -x := by rw [← hxu]; exact hlvl x hx_mem
        have hxσ : x = σ := by linarith [hGx, hGm, hκ, hx.2, hσ.2]
        rw [hxσ] at hxu
        linarith [hxu, hcon', hδ]
    · -- the upper bound `u σ < δ`
      by_contra hcon
      have hcon' : δ ≤ u σ := not_lt.mp hcon
      rcases lt_trichotomy σ 0 with hσneg | hσ0 | hσpos
      · -- σ < 0 : the path crosses `δ/2` at a negative level `≥ -κ`, contradicting `η ≤ G (δ/2)`
        have hle1 : u 0 ≤ δ / 2 := by rw [hu0]; linarith
        have hle2 : δ / 2 ≤ u σ := by linarith
        obtain ⟨x, hx, hxu⟩ :=
          hIVT (a := σ) (b := 0) (c := δ / 2) (le_of_lt hσneg) hσ.1 hκ0 (Or.inr ⟨hle1, hle2⟩)
        have hx_mem : x ∈ Set.Icc (-κ) κ := ⟨le_trans hσ.1 hx.1, le_trans hx.2 hκ0⟩
        have hGx : G (δ / 2) = -x := by rw [← hxu]; exact hlvl x hx_mem
        have hxne : x ≠ σ := by intro h; rw [h] at hxu; linarith [hxu, hcon', hδ]
        have hxgt : σ < x := lt_of_le_of_ne hx.1 (Ne.symm hxne)
        linarith [hGx, hGp, hκ, hσ.1, hxgt]
      · -- σ = 0 : then `u σ = 0 < δ`
        have hzero : u σ = 0 := by rw [hσ0]; exact hu0
        linarith [hzero, hcon', hδ]
      · -- 0 < σ : the path crosses `δ/2` at a positive level, contradicting `η ≤ G (δ/2)`
        have hle1 : u 0 ≤ δ / 2 := by rw [hu0]; linarith
        have hle2 : δ / 2 ≤ u σ := by linarith
        obtain ⟨x, hx, hxu⟩ :=
          hIVT (a := 0) (b := σ) (c := δ / 2) (le_of_lt hσpos) hm0 hσ.2 (Or.inl ⟨hle1, hle2⟩)
        have hx_mem : x ∈ Set.Icc (-κ) κ := ⟨le_trans hm0 hx.1, le_trans hx.2 hσ.2⟩
        have hGx : G (δ / 2) = -x := by rw [← hxu]; exact hlvl x hx_mem
        have hxne : x ≠ 0 := by intro h; rw [h, hu0] at hxu; linarith
        have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hxne)
        linarith [hGx, hGp, hη, hxpos]
  have hpos : ∀ σ ∈ Set.Ioo (-κ) 0, 0 < u σ := by
    intro σ hσ
    obtain ⟨hσκ, hσ0⟩ := hσ
    have hmem : σ ∈ Set.Icc (-κ) κ := ⟨le_of_lt hσκ, by linarith⟩
    have hb := hbound σ hmem
    -- `u σ ≠ 0` because `G (u σ) = -σ` and `G 0 = 0`, while `σ ≠ 0`
    have hne : u σ ≠ 0 := by
      intro h
      have h2 := hlvl σ hmem
      rw [h, hG0] at h2
      linarith
    by_contra hcon
    have hcon' : u σ ≤ 0 := not_lt.mp hcon
    have hlt : u σ < 0 := lt_of_le_of_ne hcon' hne
    -- being nonzero, `u σ` would have to lie in `(-δ, 0)` where `G` is negative,
    -- but `G (u σ) = -σ > 0`.
    have hmem2 : u σ ∈ Set.Ioo (-δ) 0 := ⟨(abs_lt.mp hb).1, hlt⟩
    have hneg' := hneg (u σ) hmem2
    have h3 := hlvl σ hmem
    linarith [hneg', h3, hσ0]
  exact ⟨hbound, hpos⟩

end Work.RPB.B5
