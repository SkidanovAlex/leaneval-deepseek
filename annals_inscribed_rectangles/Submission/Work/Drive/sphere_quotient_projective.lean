import Mathlib
import Submission.Work.Drive.ProjectiveDefs

namespace Work.Drive

/-- A vector of norm `1` is nonzero. -/
lemma norm_eq_one_ne_zero {E : Type*} [NormedAddCommGroup E] {v : E} (hv : ‖v‖ = 1) : v ≠ 0 := by
  intro h
  rw [h, norm_zero] at hv
  exact zero_ne_one hv

/-- `projOfUnit` is `Projectivization.mk` of the vector: the non-vanishing proof is irrelevant. -/
lemma projOfUnit_eq_mk {n : ℕ} (v : EuclideanSpace ℝ (Fin (n + 1))) (hv : ‖v‖ = 1)
    (h : v ≠ 0) : projOfUnit v hv = Projectivization.mk ℝ v h := rfl

/-- Rescaling a nonzero vector does not change the projective point. -/
lemma mk_smul_eq_mk {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (c : ℝ) (hc : c ≠ 0) (v : V) (hv : v ≠ 0) :
    Projectivization.mk ℝ (c • v) (smul_ne_zero hc hv) = Projectivization.mk ℝ v hv := by
  rw [Projectivization.mk_eq_mk_iff]
  exact ⟨Units.mk0 c hc, by simp [Units.smul_def]⟩

/-- **The unit sphere covers `ℝP³` with antipodal fibres**: the model of `ℝP³` used for the capping.

`projOfUnit v hv` (`Submission.Work.Drive.ProjectiveDefs`) is the point of
`Projectivization ℝ (EuclideanSpace ℝ (Fin 4))` represented by a vector of norm `1`, so it is the map
`S³ → ℝP³`.  The assertion is:

* every point of `ℝP³` is represented by a vector of norm `1` (scale a non-zero representative);
* two vectors of norm `1` represent the same point if and only if they are equal or antipodal, `w = v`
  or `w = -v`.

Hence `ℝP³` is the quotient `S³ / {±1}`: the model on which the mod-2 counting route to
`Work.Drive.chainParity` computes, and the target of the diffeomorphism `Y ≅ ℝ × ℝP³` of Hugelmeyer's
fifth auxiliary result (the capping of the configuration Möbius strip).  The identifications built in
`Submission.Work.Drive.CappingDefs`, `Submission.Work.Drive.cappingPolar_identification`,
`Submission.Work.Drive.cappingRadial_identification` and
`Submission.Work.Drive.cappingGlue_identification` are the other side of that diffeomorphism. -/
theorem sphere_quotient_projective :
    (∀ p : Projectivization ℝ (EuclideanSpace ℝ (Fin 4)),
        ∃ v : EuclideanSpace ℝ (Fin 4), ∃ hv : ‖v‖ = 1, projOfUnit v hv = p) ∧
      (∀ v w : EuclideanSpace ℝ (Fin 4), ∀ hv : ‖v‖ = 1, ∀ hw : ‖w‖ = 1,
        (projOfUnit v hv = projOfUnit w hw ↔ w = v ∨ w = -v)) := by
  constructor
  · -- Surjectivity: normalise a representative.
    intro p
    have hc : ‖p.rep‖ ≠ 0 := norm_ne_zero_iff.mpr p.rep_nonzero
    refine ⟨(‖p.rep‖)⁻¹ • p.rep, ?_, ?_⟩
    · rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
        inv_mul_cancel₀ hc]
    · have hne : (‖p.rep‖)⁻¹ • p.rep ≠ 0 := smul_ne_zero (inv_ne_zero hc) p.rep_nonzero
      rw [projOfUnit_eq_mk ((‖p.rep‖)⁻¹ • p.rep) _ hne,
        mk_smul_eq_mk (‖p.rep‖)⁻¹ (inv_ne_zero hc) p.rep p.rep_nonzero]
      exact Projectivization.mk_rep p
  · -- The fibres are exactly the antipodal pairs.
    intro v w hv hw
    have hv0 : v ≠ 0 := norm_eq_one_ne_zero hv
    have hw0 : w ≠ 0 := norm_eq_one_ne_zero hw
    constructor
    · intro h
      rw [projOfUnit_eq_mk v hv hv0, projOfUnit_eq_mk w hw hw0] at h
      obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℝ v w hv0 hw0).mp h
      -- `v = a • w` and both have norm `1`, so `|a| = 1`.
      have ha_abs : |a| = 1 := by
        have hn : ‖a • w‖ = ‖v‖ := by rw [ha]
        rw [norm_smul, Real.norm_eq_abs, hw, mul_one, hv] at hn
        exact hn
      rcases (abs_eq (show (0 : ℝ) ≤ 1 by norm_num)).mp ha_abs with h1 | h1
      · left
        rw [h1, one_smul] at ha
        exact ha
      · right
        rw [h1, neg_one_smul] at ha
        have : w = -v := by rw [← ha]; simp
        exact this
    · rintro (rfl | hwv)
      · rfl
      · subst hwv
        have hnv0 : -v ≠ 0 := neg_ne_zero.mpr hv0
        rw [projOfUnit_eq_mk v hv hv0, projOfUnit_eq_mk (-v) hw hnv0,
          Projectivization.mk_eq_mk_iff']
        exact ⟨-1, by simp⟩

end Work.Drive
