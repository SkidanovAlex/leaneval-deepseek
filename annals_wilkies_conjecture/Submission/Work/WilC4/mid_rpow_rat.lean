import Mathlib
import Submission.Work.WilC4.ULPMDev

namespace Work.WilC4

/-- Membership in the range predicate `fun q : ℚ => (2:ℝ) ^ (q:ℝ)` spelled out. -/
private lemma mem_rpow_rat_range {ρ : ℝ}
    (h : ρ ∈ Set.range (fun q : ℚ => (2 : ℝ) ^ (q : ℝ))) :
    ∃ q : ℚ, (2 : ℝ) ^ (q : ℝ) = ρ := by
  rwa [Set.mem_range] at h

theorem mid_rpow_rat {E : Set ℝ}
    (hE : E ⊆ ({0} : Set ℝ) ∪ Set.range (fun q : ℚ => (2 : ℝ) ^ (q : ℝ)))
    {m : ℝ} (hm : m ∈ Work.WilC4.Mid E) : ∃ q : ℚ, m = (2 : ℝ) ^ (q : ℝ) := by
  obtain ⟨ρ₁, hρ₁E, ρ₂, hρ₂E, hρ₁pos, hlt, _hconsec, hsq, hmpos⟩ := hm
  have hρ₂pos : 0 < ρ₂ := lt_trans hρ₁pos hlt
  -- every positive element of `E` is a rational power of `2`
  have key : ∀ ρ ∈ E, 0 < ρ → ∃ q : ℚ, ρ = (2 : ℝ) ^ (q : ℝ) := by
    intro ρ hρE hρpos
    rcases hE hρE with h0 | hrange
    · -- `ρ ∈ {0}` contradicts `0 < ρ`
      exact absurd h0 (ne_of_gt hρpos)
    · obtain ⟨q, hq⟩ := mem_rpow_rat_range hrange
      exact ⟨q, hq.symm⟩
  obtain ⟨q₁, hq₁⟩ := key ρ₁ hρ₁E hρ₁pos
  obtain ⟨q₂, hq₂⟩ := key ρ₂ hρ₂E hρ₂pos
  -- the geometric mean `(ρ₁ ρ₂)^{1/2} = 2^{(q₁+q₂)/2}`
  refine ⟨(q₁ + q₂) / 2, ?_⟩
  have hcast : (((q₁ + q₂) / 2 : ℚ) : ℝ) = ((q₁ : ℝ) + (q₂ : ℝ)) / 2 := by
    push_cast; ring
  rw [hcast]
  set s : ℝ := ((q₁ : ℝ) + (q₂ : ℝ)) / 2 with hsdef
  have hpowpos : 0 < (2 : ℝ) ^ s := Real.rpow_pos_of_pos (by norm_num) s
  have hmul : (2 : ℝ) ^ s * (2 : ℝ) ^ s = m * m := by
    have h1 : (2 : ℝ) ^ s * (2 : ℝ) ^ s = (2 : ℝ) ^ (s + s) :=
      (Real.rpow_add (by norm_num : (0 : ℝ) < 2) s s).symm
    rw [h1, hsdef]
    have h2 : ((q₁ : ℝ) + (q₂ : ℝ)) / 2 + ((q₁ : ℝ) + (q₂ : ℝ)) / 2
        = (q₁ : ℝ) + (q₂ : ℝ) := by ring
    rw [h2]
    have h3 : (2 : ℝ) ^ ((q₁ : ℝ) + (q₂ : ℝ))
        = (2 : ℝ) ^ (q₁ : ℝ) * (2 : ℝ) ^ (q₂ : ℝ) :=
      Real.rpow_add (by norm_num : (0 : ℝ) < 2) _ _
    rw [h3]
    rw [hsq, hq₁, hq₂]
  -- positivity plus `(2^s)^2 = m^2` forces `m = 2^s`
  nlinarith [hpowpos, hmpos, hmul]

end Work.WilC4
