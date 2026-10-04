import Mathlib
import Submission.Work.Diff.L.GrowthDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.L

/-- `scalAlg` is continuous: it is a finite sum of coordinate projections. -/
lemma scalAlg_continuous (n : ℕ) :
    Continuous (fun R : Submission.Diff.Alg.Curv4 n => Submission.Diff.Alg.scalAlg R) := by
  simp only [Submission.Diff.Alg.scalAlg]
  fun_prop

/-- **Pointwise description of the sublevel set of `φbar`.**  The set of pairs `(t, s)` with
`φbar n φ₀ t ≤ s` is the union of the region `t ≥ pole` (where `φbar = 0`, and the only condition
left is `0 ≤ s`) with the region `t ≤ pole`, on which the condition is the cleared inequality
`φ₀ ≤ s (1 - (2/n)φ₀ t)`.  (At `t = pole` the first piece applies, and the second is false.) -/
lemma φbar_le_iff {n : ℕ} {φ₀ : ℝ} (hφ₀ : 0 < φ₀) (t s : ℝ) :
    φbar n φ₀ t ≤ s ↔
      (pole n φ₀ ≤ t ∧ 0 ≤ s) ∨
        (t ≤ pole n φ₀ ∧ φ₀ ≤ s * (1 - (2 / (n : ℝ)) * φ₀ * t)) := by
  by_cases h : t < pole n φ₀
  · have hden : 0 < 1 - (2 / (n : ℝ)) * φ₀ * t := one_sub_mul_pos_of_lt_pole hφ₀ h
    have hphibar : φbar n φ₀ t = φ₀ / (1 - (2 / (n : ℝ)) * φ₀ * t) := φbar_of_lt h
    rw [hphibar, div_le_iff₀ hden]
    exact ⟨fun hs => Or.inr ⟨h.le, hs⟩,
      fun hh => hh.elim (fun hA => absurd hA.1 (not_le.mpr h)) (fun hB => hB.2)⟩
  · have hpole : pole n φ₀ ≤ t := not_lt.mp h
    have hphibar : φbar n φ₀ t = 0 := φbar_of_pole_le hpole
    rw [hphibar]
    refine ⟨fun hs => Or.inl ⟨hpole, hs⟩, fun hh => ?_⟩
    rcases hh with ⟨-, hs⟩ | ⟨htle, hs⟩
    · exact hs
    · -- here `t = pole`, where the denominator `1 - (2/n)φ₀ t` vanishes (for `n ≥ 1`)
      have ht : t = pole n φ₀ := le_antisymm htle hpole
      subst ht
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        have hd : 1 - (2 / ((0 : ℕ) : ℝ)) * φ₀ * pole 0 φ₀ = 1 := by norm_num [pole]
        rw [hd, mul_one] at hs
        linarith
      · have hd : 1 - (2 / (n : ℝ)) * φ₀ * pole n φ₀ = 0 := by
          have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
          rw [pole]
          field_simp
          ring
        rw [hd, mul_zero] at hs
        linarith

/-- **The space-time track of the scalar-growth family is closed.**  For a closed set `F` of
curvature arrays and `φ₀ > 0`, the set of pairs `(t, R)` with `R ∈ F` and `φbar n φ₀ t ≤ scalAlg R`
is closed in `ℝ × Curv4 n`.

Route.  `φbar` is `Work.Diff.L.φbar` (`= φ₀/(1 - (2/n)φ₀ t)` for `t < pole n φ₀ = n/(2φ₀)` and `0`
for `t ≥ pole n φ₀`).  The set is the intersection of the closed set `{p | p.2 ∈ F}` (a preimage of
`F` under the continuous projection) with

  `{p | pole n φ₀ ≤ p.1 ∧ 0 ≤ scalAlg p.2} ∪ {p | p.1 ≤ pole n φ₀ ∧ φ₀ ≤ scalAlg p.2 * (1 - (2/(n:ℝ)) * φ₀ * p.1)}`,

a union of two closed sets (all conditions are of the form `a ≤ b` for continuous real functions
`p ↦ p.1`, `p ↦ scalAlg p.2`; `scalAlg` is a finite sum of coordinate projections, so it is
continuous — `continuity`/`fun_prop`, or build the continuous linear map `scalAlgLM`/`scalAlgL` as
in `Submission/Work/Diff/GE/scal_lapl_basic.lean`).
The pointwise identity is: for `t < pole` the denominator is positive, so
`φbar t ≤ s ↔ φ₀ ≤ s * (1 - (2/n)φ₀ t)`; `t = pole` is impossible in the second piece because
`φ₀ > 0`; and for `t ≥ pole`, `φbar t = 0 ≤ s`. -/
theorem track_closed {n : ℕ} {F : Set (Submission.Diff.Alg.Curv4 n)} (hF : IsClosed F) {φ₀ : ℝ}
    (hφ₀ : 0 < φ₀) :
    IsClosed {p : ℝ × Submission.Diff.Alg.Curv4 n |
      p.2 ∈ F ∧ Work.Diff.L.φbar n φ₀ p.1 ≤ Submission.Diff.Alg.scalAlg p.2} := by
  have hcs : Continuous (fun p : ℝ × Submission.Diff.Alg.Curv4 n =>
      Submission.Diff.Alg.scalAlg p.2) :=
    (scalAlg_continuous n).comp continuous_snd
  -- The two closed pieces of the space-time track.
  have hA : IsClosed {p : ℝ × Submission.Diff.Alg.Curv4 n |
      pole n φ₀ ≤ p.1 ∧ 0 ≤ Submission.Diff.Alg.scalAlg p.2} :=
    IsClosed.inter (isClosed_Ici.preimage continuous_fst) (isClosed_Ici.preimage hcs)
  have hB : IsClosed {p : ℝ × Submission.Diff.Alg.Curv4 n |
      p.1 ≤ pole n φ₀ ∧
        φ₀ ≤ Submission.Diff.Alg.scalAlg p.2 * (1 - (2 / (n : ℝ)) * φ₀ * p.1)} :=
    IsClosed.inter (isClosed_Iic.preimage continuous_fst)
      (isClosed_le continuous_const
        (hcs.mul (continuous_const.sub (continuous_const.mul continuous_fst))))
  -- The pointwise description of `{p | φbar n φ₀ p.1 ≤ scalAlg p.2}` as the union.
  have htrack : IsClosed {p : ℝ × Submission.Diff.Alg.Curv4 n |
      Work.Diff.L.φbar n φ₀ p.1 ≤ Submission.Diff.Alg.scalAlg p.2} := by
    rw [show {p : ℝ × Submission.Diff.Alg.Curv4 n |
          Work.Diff.L.φbar n φ₀ p.1 ≤ Submission.Diff.Alg.scalAlg p.2}
        = {p : ℝ × Submission.Diff.Alg.Curv4 n |
              pole n φ₀ ≤ p.1 ∧ 0 ≤ Submission.Diff.Alg.scalAlg p.2}
          ∪ {p : ℝ × Submission.Diff.Alg.Curv4 n |
              p.1 ≤ pole n φ₀ ∧
                φ₀ ≤ Submission.Diff.Alg.scalAlg p.2 * (1 - (2 / (n : ℝ)) * φ₀ * p.1)}
        from Set.ext (fun p => φbar_le_iff hφ₀ p.1 (Submission.Diff.Alg.scalAlg p.2))]
    exact hA.union hB
  exact IsClosed.inter (hF.preimage continuous_snd) htrack

end Work.Diff.L
