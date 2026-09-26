import Mathlib
import Submission.Work.Smooth.Plane.All
import Submission.Work.PinchCounted.All
import Submission.Work.CountedPinch.Defs

namespace Work.CountedPinch

/-- **The flat disc cut out of the box carries no compressing loop of the knot's surface.**

Pardon's invariant `I(F, β) = min p q` is a lower bound for the number of intersections of the knot
`β` with any *simple*, *essential*, *compressing* loop `α` of the surface (`pardonsI_le`, transported
to the configuration through `himg` and `pardonsI_standard_mapHomeomorph`).  If `α` is moreover
contained in the flat disc `cutDisc s c σ u = PBox s c σ ∩ {y (σ 2) = c (σ 2) + u}`, then every
point of `α ∩ β` is a point of the knot with a parameter in one fundamental period `[0, 2π)` at
which the knot meets the flat disc; the counting hypothesis `hcount` bounds that number of
parameters by `5(1+ε)/ε · d < min p q` (`five_coeff_mul_lt_min`).  This contradicts the lower
bound. -/
theorem not_exists_compressingLoop_in_flatDisc
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : LeanEval.KnotTheory.PardonDistortion.Knot) {d : ℝ} (hd : 0 ≤ d)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hsmall : Submission.countConst * d < (Nat.min p q : ℝ))
    {s : ℝ} (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (hcount : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        K.curve t ∈ Submission.PBox s c σ ∧
        (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
      ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d))) :
    ¬ ∃ α : Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ),
        Work.CoreTopology.IsSimple (Work.Smooth.Morse.torus ψ) α ∧
        Work.CoreTopology.IsEssential (Work.Smooth.Morse.torus ψ) α ∧
        Work.CoreTopology.BoundsDiskInComplement (Work.Smooth.Morse.torus ψ) α ∧
        ∀ t : ℝ, α.γ t ∈ Work.BoxShrink.Core.cutDisc s c σ u := by
  rintro ⟨α, hsimple, hess, hb, hαD⟩
  -- Pardon's invariant at the transported configuration: every simple compressing essential loop
  -- of the surface meets the knot at least `min p q` times.
  have hle : (Nat.min p q : ℕ∞) ≤ Set.encard (Set.range α.γ ∩ Set.range K.curve) := by
    rw [← Work.CoreTopology.pardonsI_standard_mapHomeomorph p q hp hq hc ψ.toHomeomorph]
    rw [himg]
    exact Work.CoreTopology.pardonsI_le hsimple hess hb
  -- those intersections lie in the flat disc
  have hmono : Set.encard (Set.range α.γ ∩ Set.range K.curve) ≤
      Set.encard (Set.range K.curve ∩ Work.BoxShrink.Core.cutDisc s c σ u) := by
    refine Set.encard_le_encard ?_
    rintro y ⟨⟨t, rfl⟩, hyK⟩
    exact ⟨hyK, hαD t⟩
  -- and the flat disc meets the knot only at the counted parameters
  have hparam : Set.encard (Set.range K.curve ∩ Work.BoxShrink.Core.cutDisc s c σ u) ≤
      Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        K.curve t ∈ Submission.PBox s c σ ∧
        (K.curve t) (σ 2) = c (σ 2) + u} := by
    calc Set.encard (Set.range K.curve ∩ Work.BoxShrink.Core.cutDisc s c σ u)
        ≤ Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
            K.curve t ∈ Work.BoxShrink.Core.cutDisc s c σ u} :=
          Work.Topology.SphereSlicing.encard_range_inter_le_encard_param_of_periodic
            K.periodic (Work.BoxShrink.Core.cutDisc s c σ u)
      _ ≤ Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
            K.curve t ∈ Submission.PBox s c σ ∧
            (K.curve t) (σ 2) = c (σ 2) + u} := by
          apply Set.encard_mono
          rintro t ⟨ht, hmem⟩
          exact ⟨ht, (Work.BoxShrink.Core.mem_cutDisc.mp hmem)⟩
  have hcount_lt : Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
      K.curve t ∈ Submission.PBox s c σ ∧
      (K.curve t) (σ 2) = c (σ 2) + u} < (Nat.min p q : ℕ∞) :=
    Work.BoxShrink.Core.encard_lt_of_coe_le_ofReal (n := Nat.min p q) (ne_of_gt (lt_min hp hq))
      hcount (Work.BoxShrink.Core.five_coeff_mul_lt_min hp hq hd hsmall)
  exact absurd (le_trans hle (le_trans hmono hparam)) (not_le.mpr hcount_lt)

end Work.CountedPinch
