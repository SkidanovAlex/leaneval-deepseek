import Mathlib
import Submission.Work.HP.MMDefs
import Submission.Work.HP.JcVolDefs
import Submission.Work.HP.JcVolDelta
import Submission.Work.HP.JcVolAlg
import Submission.Work.HP.JcVolChain
import Submission.Work.HP.JcVolNormDet
import Submission.Work.HP.BallVolIntrinsic
import Submission.Work.HP.BallNormSqIntegral
import Submission.Work.HP.IntegralSquare
import Submission.Work.HP.IntegralQbarPow
import Submission.Work.HP.IntegralModel
import Submission.Work.HP.EstimateMu
import Submission.Work.HP.VQ_ballVol

namespace Work.HP

/-
Note for the prover. This is the paper's Lemma 4.3 ("volume loc"), with the `O(·)` unpacked;
it is TRUE despite an apparent counterexample. The reduction: let `f_3,…` be an orthonormal
basis of `(ℝw ⊕ ℝz)^⊥` and let `C` be the matrix with first two columns
`(‖z‖²w - ⟨w,z⟩z)/δ` and `(-⟨w,z⟩w + ‖w‖²z)/δ` and remaining columns `f_j`. Then
`⟨w, Cu⟩ = u₁`, `⟨z, Cu⟩ = u₂` and `‖Cu‖² = q(u₁,u₂) + ‖v‖²` where
`q(u₁,u₂) = ‖u₁z - u₂w‖²/δ ≤ (‖w‖+‖z‖)²/δ` for `|u₁|,|u₂| ≤ 1`. Also `|det C| = δ^{-1/2}`.
So with `u = (u₁,u₂,v)`, `J = δ^{-1/2} · vol{max{u₁²,u₂²} ≤ q(u₁,u₂)+‖v‖² ≤ 1}`, and the
last volume is `4 ∫_{B_{N-2}(1)}‖v‖² dv (1 + O(u)) = 4 ((N-2)/N) V_{N-2} (1+O(u))`.
Beware: `{t : |⟨w,t⟩| ≤ ‖t‖}` is a *thin double cone* (a band of angular width `~1/‖w‖`),
not the complement of a thin slab; e.g. for `w = R e₁`, `z = R e₂` one has
`δ = R⁴` and `JcVol = 8/(3R²)(1+O(1/R²)) → 0`, consistent with the claimed main term
`4(N-2)/N V_{N-2}/R²` when `N = 3`.
-/
theorem JcVolAsymp (ι : Type) [Fintype ι] (hN : 3 ≤ Fintype.card ι) :
    ∃ C : ℝ, 0 < C ∧ ∀ (w z : EuclideanSpace ℝ ι), LinearIndependent ℝ ![w, z] →
      |JcVol w z - 4 * ((Fintype.card ι : ℝ) - 2) / (Fintype.card ι : ℝ) *
          ballVol (Fintype.card ι - 2) / Real.sqrt (deltaV w z)| ≤
      C * (4 * ((Fintype.card ι : ℝ) - 2) / (Fintype.card ι : ℝ) *
          ballVol (Fintype.card ι - 2) / Real.sqrt (deltaV w z)) *
        min 1 ((‖w‖ + ‖z‖) ^ 2 / deltaV w z) := by
  refine JcVolChain.JcVolAsymp_aux (ι := ι) hN
    (fun w z h => JcVolNormDet h) ?_ (fun w z h => VQ_ballVol hN h)
  intro w z h
  have hqmeas : Measurable (qform w z) := (JcVolChain.continuous_qform w z).measurable
  have hε : 0 ≤ (‖w‖ + ‖z‖) ^ 2 / deltaV w z := div_nonneg (sq_nonneg _) (JcVolDelta h).le
  have hq0 : ∀ u, qbar u ≤ 1 → 0 ≤ qform w z u := fun u _ => JcVolChain.qform_nonneg w z h u
  have hqε : ∀ u, qbar u ≤ 1 → qform w z u ≤ (‖w‖ + ‖z‖) ^ 2 / deltaV w z := by
    intro u hu
    obtain ⟨h0, h1⟩ := JcVolChain.abs_coord_le_one hu
    exact JcVolChain.qform_bound w z h u h0 h1
  have := EstimateMuStrong hN (qform w z) hqmeas ((‖w‖ + ‖z‖) ^ 2 / deltaV w z) hε hq0 hqε
  simpa only [mu, nu] using this

end Work.HP
