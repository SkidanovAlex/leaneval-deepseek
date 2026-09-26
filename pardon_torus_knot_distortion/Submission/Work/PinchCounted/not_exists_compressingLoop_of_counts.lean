import Mathlib
import Submission.Work.PinchCounted.Counting
import Submission.Work.CoreTopology.IntersectionNumber

namespace Work.PinchCounted

/-- The intersections of the knot `K` with the boundary sphere `∂PBox s c σ` are hit by
parameters in the fundamental period `[0, 2π)`: the periodic curve of the knot meets every point of
its range at a parameter of `Ico 0 (2 * π)`. -/
private theorem encard_range_inter_sphereSet_le_param
    (K : LeanEval.KnotTheory.PardonDistortion.Knot) (c : LeanEval.KnotTheory.PardonDistortion.R3)
    (σ : Equiv.Perm (Fin 3)) (s : ℝ) :
    Set.encard (Set.range K.curve ∩ Work.BoxShrink.Core.sphereSet c σ s) ≤
      Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s} := by
  refine le_trans (Set.encard_le_encard ?_) (Set.encard_image_le K.curve _)
  rintro y ⟨⟨t, rfl⟩, hyS⟩
  have hnorm : Submission.boxNorm c σ (K.curve t) = s :=
    Work.BoxShrink.Core.mem_sphereSet.mp hyS
  have hpos : (0 : ℝ) < 2 * Real.pi := by positivity
  set n : ℤ := ⌊t / (2 * Real.pi)⌋ with hn
  have hnle : (n : ℝ) ≤ t / (2 * Real.pi) := by
    rw [hn]; exact Int.floor_le _
  have hnlt : t / (2 * Real.pi) < (n : ℝ) + 1 := by
    rw [hn]; exact Int.lt_floor_add_one _
  have hle : 0 ≤ t - (n : ℝ) * (2 * Real.pi) := by
    have := (le_div_iff₀ hpos).mp hnle
    linarith
  have hlt : t - (n : ℝ) * (2 * Real.pi) < 2 * Real.pi := by
    have := (div_lt_iff₀ hpos).mp hnlt
    linarith
  have hper : Function.Periodic K.curve (2 * Real.pi) := K.periodic
  have hcurve : K.curve (t - (n : ℝ) * (2 * Real.pi)) = K.curve t :=
    hper.sub_int_mul_eq n
  exact ⟨t - (n : ℝ) * (2 * Real.pi),
    ⟨⟨hle, hlt⟩, by rw [hcurve]; exact hnorm⟩, hcurve⟩

theorem not_exists_compressingLoop_of_counts
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : LeanEval.KnotTheory.PardonDistortion.Knot) {d : ℝ} (hd : 0 ≤ d)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hsmall : Submission.countConst * d < (Nat.min p q : ℝ))
    {s : ℝ} (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3))
    (hcount : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
      ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d))) :
    ¬ ∃ α : Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ),
        Work.CoreTopology.IsSimple (Work.Smooth.Morse.torus ψ) α ∧
        Work.CoreTopology.IsEssential (Work.Smooth.Morse.torus ψ) α ∧
        Work.CoreTopology.BoundsDiskInComplement (Work.Smooth.Morse.torus ψ) α ∧
        ∀ t : ℝ, α.γ t ∈ Work.BoxShrink.Core.sphereSet c σ s := by
  rintro ⟨α, hsimple, hess, hb, hαS⟩
  -- Pardon's invariant `I(F, β) = min p q` at the transported configuration: every simple
  -- compressing essential loop of the torus meets the knot at least `min p q` times.
  have hle : (Nat.min p q : ℕ∞) ≤ Set.encard (Set.range α.γ ∩ Set.range K.curve) := by
    rw [← Work.CoreTopology.pardonsI_standard_mapHomeomorph p q hp hq hc ψ.toHomeomorph]
    rw [himg]
    exact Work.CoreTopology.pardonsI_le hsimple hess hb
  -- those intersections lie on the boundary sphere, which itself meets the knot only at the
  -- parameters counted by `hcount`
  have hmono : Set.encard (Set.range α.γ ∩ Set.range K.curve) ≤
      Set.encard (Set.range K.curve ∩ Work.BoxShrink.Core.sphereSet c σ s) := by
    refine Set.encard_le_encard ?_
    rintro y ⟨⟨t, rfl⟩, hyK⟩
    exact ⟨hyK, hαS t⟩
  have hcount_lt : Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
      Submission.boxNorm c σ (K.curve t) = s} < (Nat.min p q : ℕ∞) :=
    Work.BoxShrink.Core.encard_lt_of_coe_le_ofReal (n := Nat.min p q) (ne_of_gt (lt_min hp hq))
      hcount (Work.BoxShrink.Core.ten_coeff_mul_lt_min hp hq hd hsmall)
  exact absurd (le_trans hle (le_trans hmono (encard_range_inter_sphereSet_le_param K c σ s)))
    (not_le.mpr hcount_lt)

end Work.PinchCounted
