import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxSliding.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxSliding

/-- **The far set kills the cutoff.**  If some coordinate of `w := (ℓd)•u`
exceeds the outer half-side `A := ½ℓ(1+d)`, then the small box `B(u)` misses
the big box `{∀j, |x_j| ≤ ℓ/2}` entirely, so the two factors of
`χ_{B(u)}(x) = χ_M(x/ℓ)·χ_M(x/(ℓd) − u)` can never be simultaneously nonzero:

if both were nonzero then `|x_j| ≤ ℓ/2` and `|(x − w)_j| ≤ (ℓd)/2`, whence
`|w_j| ≤ ℓ/2 + (ℓd)/2 = ½ℓ(1+d)`, contradicting membership in `farSet`.

(For `M = 0` the normalisation integral `chiSmallNormSq 0 = ∫ 1 = 0` by the
Bochner convention, so `chiSmall 0 ≡ 0` and the claim is trivial.) -/
lemma farSet_chiSmallB_zero {M : ℕ} {ℓ d μ : ℝ} {u : EuclideanSpace ℝ (Fin 3)}
    (hℓ : 0 < ℓ) (hd : 0 < d) (hu : u ∈ Work.SmallBoxSliding.farSet ℓ d μ)
    (x : EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.chiSmallB M ℓ d u x = 0 := by
  by_cases hM : 1 ≤ M
  · rcases hu with ⟨j, hj⟩
    by_contra hx
    -- both factors nonzero: the supports force `x` into the intersection of
    -- the big box and the small box
    have hbig : |x.ofLp j| ≤ ℓ / 2 :=
      Submission.BoseGases.chiSmallB_support_big_box hM hℓ hx j
    have hdist : |((x - (ℓ * d) • u).ofLp j)| ≤ (ℓ * d) / 2 :=
      Submission.BoseGases.chiSmallB_support_small_box_dist hM hℓ hd hx j
    -- triangle inequality: `|w_j| ≤ |x_j| + |x_j − w_j|`
    have htri : |((ℓ * d) • u).ofLp j| ≤ |x.ofLp j| + |((x - (ℓ * d) • u).ofLp j)| := by
      have h1 : ((ℓ * d) • u).ofLp j = x.ofLp j + (((ℓ * d) • u).ofLp j - x.ofLp j) := by ring
      rw [h1]
      calc |x.ofLp j + (((ℓ * d) • u).ofLp j - x.ofLp j)|
          ≤ |x.ofLp j| + |((ℓ * d) • u).ofLp j - x.ofLp j| := abs_add_le _ _
        _ = |x.ofLp j| + |((x - (ℓ * d) • u).ofLp j)| := by
            congr 1
            have h2 : ((ℓ * d) • u).ofLp j - x.ofLp j = -((x - (ℓ * d) • u).ofLp j) := by
              simp
            rw [h2, abs_neg]
    nlinarith [hj, hbig, hdist, htri]
  · -- `M = 0`: the normalisation integral of `chiSmallBase 0 ≡ 1` vanishes
    push Not at hM
    have hM0 : M = 0 := by omega
    subst hM0
    have hz : ∀ w : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.chiSmall 0 w = 0 := fun w => by
      simp [Submission.BoseGases.chiSmall, Submission.BoseGases.chiSmallBase,
        Submission.BoseGases.chiSmallNormSq, MeasureTheory.Measure.real]
    simp [Submission.BoseGases.chiSmallB, hz]

end Work.SmallBoxSliding
