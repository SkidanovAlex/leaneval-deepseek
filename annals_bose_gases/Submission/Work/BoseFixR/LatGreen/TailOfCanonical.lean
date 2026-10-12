import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR.LatGreen

/-- **Tail bound from a bound of the canonical-profile form.** Let `G : ℝ → ℝ`
with `∫_{s>0} s²|G s| ds < ∞` and `G ≥ 0` a.e. on `(0,∞)`. Suppose that for every
`0 < r < R` (`R > 0`) the combination
`(1/2)·(∫_{0<s≤r} s² G s ds + r·∫_{s>r} s G s ds)` is at most `r`. Then the tail
integral `∫_{s>r} s G s ds` is at most `2` for every `0 < r < R`. Namespace
`Work.BoseFixR.LatGreen`. -/
theorem TailOfCanonical {G : ℝ → ℝ} {R : ℝ} (hR : 0 < R)
    (hInt2 : MeasureTheory.IntegrableOn (fun s : ℝ => s ^ 2 * |G s|) (Set.Ioi (0 : ℝ)))
    (hnn : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))), 0 ≤ G s)
    (hU : ∀ r : ℝ, 0 < r → r < R →
      (1 / 2) * ((∫ s in Set.Ioc (0 : ℝ) r, s ^ 2 * G s) +
        r * (∫ s in Set.Ioi r, s * G s)) ≤ r) :
    ∀ r : ℝ, 0 < r → r < R → (∫ s in Set.Ioi r, s * G s) ≤ 2 := by
  intro r hr0 hrR
  -- The hypothesis at the *same* `r` already suffices: the truncated second
  -- moment `∫_{0<s≤r} s² G s` is nonnegative, so `r·∫_{s>r} s G s ≤ 2r`.
  have h1 := hU r hr0 hrR
  have hsub : Set.Ioc (0 : ℝ) r ⊆ Set.Ioi (0 : ℝ) := fun s hs => hs.1
  have hG : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) r)] G :=
    MeasureTheory.ae_restrict_of_ae_restrict_of_subset hsub hnn
  have hnnIoc :
      0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) r)]
        (fun s : ℝ => s ^ 2 * G s) :=
    hG.mono (fun s hs => mul_nonneg (sq_nonneg s) hs)
  have hF : 0 ≤ ∫ s in Set.Ioc (0 : ℝ) r, s ^ 2 * G s :=
    MeasureTheory.integral_nonneg_of_ae hnnIoc
  nlinarith [h1, hF, hr0]

end Work.BoseFixR.LatGreen
