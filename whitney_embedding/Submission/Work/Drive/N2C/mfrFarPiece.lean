import Mathlib
import Submission.Work.Drive.N2C.mfrFootPlumbing
import Submission.Work.Drive.N2Lead.mobiusUpperFootKit
import Submission.Work.Drive.N2C.lowerCert
import Submission.Work.Drive.N2Lead.twistToolkit

/-!
# The far piece of the twisted Möbius upper picture

At the level `u⁺ = f p + 3η/2`, a point `y` outside the model (saddle) region whose foot
`footMap D.Φ f (f p - 3η/2) y` lands on a *parked* component `S.L.γ j t₀` (`j ≠ S.i`) of the anchor
level has its twisted Möbius picture on the round circle of radius `1` about the *shifted parking
spot* `proj2 (farPos S.n j) + Dp·I`; the three rows of this file are

* the picture lies in the **left** half-plane (`re < 0` — the parking spots of the packet have real
  part `-20` and the circle has radius `1`, so the picture stays below `-19`),
* the picture never reaches the centre of that circle, and
* the tangent line of the picture never passes through that centre (`mfrFarPiece`), i.e. the parked
  branch is star-shaped about the shifted parking spot.

The value row is `Work.Drive.N2Lead.mobiusTwisted_far_proj`
(`Submission/Work/Drive/N2Lead/mobiusUpperFootKit.lean`) and the two rate rows are
`Work.Drive.N2Lead.mobiusUpperFarRate`
(`Submission/Work/Drive/N2Lead/mobiusUpperFarRate.lean`, whose chain rule along the foot map lands
in the kernel of `df` at the foot and where the pushed park circle's non-radiality is
`Work.Drive.N2C.farCurve_deriv_not_radial`).  This file only packages them in the form consumed by
the far piece of the upper certificate.
-/

namespace Work.Drive.N2C

open scoped Manifold ContDiff Topology

theorem mfrFarPiece {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {η : ℝ}
    (hη : 0 < η) (hsmall : Work.Drive.N2.packetEtaB D η < 1 / 200)
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (S : Work.Drive.N2Lead.MobiusPacket D η)
    {ε εp Dp : ℝ} (hε : 0 < ε) (hε19 : ε ≤ 19) (hεp : 0 < εp) (hεp19 : εp ≤ 19) (hDp : 0 ≤ Dp)
    {j : Fin S.n} (hj : j ≠ S.i) {y : M} {t₀ : ℝ}
    (hy : f y = f p + 3 * η / 2)
    (hyD : y ∉ Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j))
      S.Z (39 / 20))
    (hfoot : Work.Drive.N2.footMap D.Φ f (f p - 3 * η / 2) y = S.L.γ j t₀) :
    (Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp y)).re < 0 ∧
      Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp y)
        ≠ Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farPos S.n j) + (Dp : ℂ) * Complex.I ∧
      ∀ v : TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) y,
        mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (modelWithCornersSelf ℝ ℝ) f y v = 0 →
        v ≠ 0 →
        ¬ (∃ t : ℝ, mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (modelWithCornersSelf ℝ ℂ)
            (fun z : M => Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp z)) y v
          = t • (Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp y)
              - (Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farPos S.n j) + (Dp : ℂ) * Complex.I))) := by
  -- the value: the picture is the round circle about the shifted parking spot
  have hval := Work.Drive.N2Lead.mobiusTwisted_far_proj (D := D) (S := S) (ε := ε) (εp := εp)
    (Dp := Dp) hε hε19 hεp hεp19 hj hyD hfoot
  -- the rate rows of `mobiusUpperFarRate`
  have hrate := Work.Drive.N2Lead.mobiusUpperFarRate (D := D) (Dp := Dp) (S := S) hη hsmall
    hε hε19 hεp hεp19 j hj
  refine ⟨?_, ?_, ?_⟩
  · -- the left half-plane: `re = -20 + cos (2π t₀) ≤ -19`
    rw [hval]
    have hre : (Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farPos S.n j) + (Dp : ℂ) * Complex.I
        + Work.Drive.N2Lead.proj2 (Work.Drive.N2.ang t₀)).re
        = -20 + Real.cos (2 * Real.pi * t₀) := by
      rw [Complex.add_re, Complex.add_re, proj2_farPos, re_proj2_ang]
      simp [Complex.mul_re]
    rw [hre]
    linarith [Real.cos_le_one (2 * Real.pi * t₀)]
  · -- the picture misses the centre (the round circle has radius `1`)
    intro hcon
    have hZ : Work.Drive.N2Lead.proj2 (Work.Drive.N2.ang t₀) ≠ 0 := by
      intro h0
      have h1 := norm_proj2_ang t₀
      rw [h0] at h1
      simp at h1
    have h2 : (Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farPos S.n j) + (Dp : ℂ) * Complex.I)
        + Work.Drive.N2Lead.proj2 (Work.Drive.N2.ang t₀)
        = (Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farPos S.n j)
            + (Dp : ℂ) * Complex.I) + 0 := by
      rw [← hval, hcon, add_zero]
    exact hZ (add_left_cancel h2)
  · -- the rate row: the tangent line of the picture misses the centre
    intro v hv hvne
    exact (hrate y t₀ v hy hyD hfoot).2 hv hvne

end Work.Drive.N2C
