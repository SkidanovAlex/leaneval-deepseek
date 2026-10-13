import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.StrongEps.E5G5.mixed_intervalIntegral_eq_gen
import Submission.Work.FTS.StrongEps.E5G5.HkIntegrand_intervalIntegral_le_gen
import Submission.Work.FTS.EllExist.Honesty.HkMem_of_majorant_ae
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EpsEngine.HkMem_intervalIntegral_counterexample
import Submission.Work.FTS.EpsEngine.PerzTools.Main
import Submission.Work.FTS.EpsEngine.PerzTools.aesm_uncurry_restricted_theta
import Submission.Work.FTS.EpsEngine.PerzTools.mixed_intervalIntegral_eq_gen_restricted

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine

/-- **The interval integral of an `ℋ^k`-family, in the per-`z` form.**  See
`Submission/Work/FTS/EpsEngine/PerzTools/{Basic,Exchange,Main}.lean` for the development:

* `PerzTools/Basic.lean` — the elementary measure theory, the two interface statements
  (`CarathTheta`, `ExchMixed`) and the joint measurability of the family;
* `PerzTools/Exchange.lean` — the exchange identity at a point, the pointwise Cauchy–Schwarz
  (averaging) bound and the measurability of the primitive's `ℋ^k`-integrand;
* `PerzTools/Main.lean` — the chain `HkIntegrand α k (∫_s H s) ≤ (b-a) ∫_s HkIntegrand α k (H s)`
  integrated in `(s,z,θ)` (Tonelli against `hjoint`), giving both the per-`z` integrability and the
  norm bound;
* the two interface statements are discharged by
  `PerzTools.aesm_uncurry_restricted_theta` and
  `PerzTools.mixed_intervalIntegral_eq_gen_restricted`. -/
theorem HkMem_intervalIntegralPerz {α B : ℝ} {k : ℕ} {T a b : ℝ} {H : ℝ → ℝ → ℝ → ℝ}
    (hab : a ≤ b) (hT : 0 ≤ T) (haT : a ∈ Set.Icc 0 T) (hbT : b ∈ Set.Icc 0 T)
    (hsm : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.FTS.EllipticEst.SmoothOpen (H s))
    (hmem : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.Spaces.HkMem α k (H s))
    (hbd : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.Spaces.HkNorm α k (H s) ≤ B)
    (hmeas : ∀ (j i : ℕ), j + i ≤ k → ∀ z θ : ℝ,
      (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      MeasureTheory.AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed j i (H s) z θ)
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)))
    (hjoint : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ × ℝ => Work.Spaces.HkIntegrand α k (H p.1) p.2.1 p.2.2)
      ((MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)).prod
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))))
    (hsup : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ q ∈ K, ∀ (j i : ℕ), j + i ≤ k →
        |Work.Spaces.mixed j i (H s) q.1 q.2| ≤ C)
    (hperz : ∀ z ∈ Work.Spaces.Iz, ∃ Cz : ℝ,
      ∀ s ∈ Set.Icc (0 : ℝ) T,
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (H s) z θ) ≤ Cz) :
    Work.Spaces.HkMem α k (fun z θ => ∫ s in a..b, H s z θ) ∧
      Work.Spaces.HkNorm α k (fun z θ => ∫ s in a..b, H s z θ) ≤ B * (b - a) := by
  exact Work.FTS.EpsEngine.PerzTools.intervalIntegral_perz_aux
    Work.FTS.EpsEngine.PerzTools.aesm_uncurry_restricted_theta
    Work.FTS.EpsEngine.PerzTools.mixed_intervalIntegral_eq_gen_restricted
    hab hT haT hbT hsm hmem hbd hmeas hjoint hsup hperz

end Work.FTS.EpsEngine
