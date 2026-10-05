import Mathlib

/-!
# The diametral pair of a simple closed plane curve

`Work.RPB.B1a.maehara_diametral`: for a continuous injective plane curve `γ : Circle → ℂ`, there is a
pair `(α, β)` of points on the curve realising the diameter of the curve, and that diameter is
strictly positive.

This is the elementary (purely topological) input of the Maehara-style normalisation: the curve is
compact, so the continuous function `(z, w) ↦ ‖z - w‖` attains a maximum on `range γ × range γ`; and
since `Circle` has at least two points while `γ` is injective, some pair of points of the curve is at
positive distance, so the maximum is positive.
-/

namespace Work.RPB.B1a

/-- The two points `1` and `-1` of the unit circle are distinct. -/
lemma circle_one_ne_neg_one : (1 : Circle) ≠ (-1 : Circle) := by
  intro h
  have h2 : ((1 : Circle) : ℂ) = ((-1 : Circle) : ℂ) := congrArg Subtype.val h
  rw [show ((1 : Circle) : ℂ) = 1 from rfl, show ((-1 : Circle) : ℂ) = -1 from rfl] at h2
  norm_num at h2

theorem maehara_diametral (γ : Circle → ℂ) (hγ : Continuous γ) (hinj : Function.Injective γ) :
    ∃ α β : ℂ, α ∈ Set.range γ ∧ β ∈ Set.range γ ∧ 0 < ‖β - α‖ ∧
      ∀ z ∈ Set.range γ, ∀ w ∈ Set.range γ, ‖z - w‖ ≤ ‖β - α‖ := by
  -- The function `(z, w) ↦ ‖z - w‖` is continuous.
  have hcont : Continuous (fun p : ℂ × ℂ => ‖p.1 - p.2‖) :=
    (continuous_fst.sub continuous_snd).norm
  -- Its domain `range γ × range γ` is compact (as `Circle` is compact) and nonempty.
  have hs : IsCompact (Set.range γ ×ˢ Set.range γ) := (isCompact_range hγ).prod (isCompact_range hγ)
  have hne : (Set.range γ ×ˢ Set.range γ).Nonempty :=
    ⟨(γ 1, γ 1), ⟨1, rfl⟩, ⟨1, rfl⟩⟩
  -- Hence it attains its maximum at some pair `p` of points of the curve.
  obtain ⟨p, hp, hpmax⟩ := hs.exists_isMaxOn hne hcont.continuousOn
  refine ⟨p.1, p.2, hp.1, hp.2, ?_, ?_⟩
  · -- The diameter is positive: the two points `γ 1` and `γ (-1)` are distinct.
    have hdist : 0 < ‖γ (1 : Circle) - γ (-1 : Circle)‖ := by
      rw [norm_pos_iff, sub_ne_zero]
      intro h
      exact circle_one_ne_neg_one (hinj h)
    have := @hpmax (γ 1, γ (-1)) ⟨⟨1, rfl⟩, ⟨-1, rfl⟩⟩
    simp only [Set.mem_ofPred_eq] at this
    exact lt_of_lt_of_le hdist (by simpa [norm_sub_rev] using this)
  · -- Everything is bounded by the diameter.
    intro z hz w hw
    have := @hpmax (z, w) ⟨hz, hw⟩
    simp only [Set.mem_ofPred_eq] at this
    simpa [norm_sub_rev] using this

end Work.RPB.B1a
