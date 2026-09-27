import Mathlib
import Submission.Work.Drive.N2Lead.mobiusUpperDefs
import Submission.Work.Drive.N2Lead.mobiusArcDefs
import Submission.Work.Drive.N2Lead.mobius_pushedStar
import Submission.Work.Drive.N2Lead.mobiusGoodDrawing
import Submission.Work.Drive.N2Lead.saddleArcs
import Submission.Work.Drive.N2Lead.saddlePacket

/-!
# The `mobiusUpperStarRows` kit: the parts of the star rows that need no profile input

See `NOTES_S48_starRows_DIAGNOSIS.md` for the analysis and for the two profile rows that are missing
from `MobiusPacket` (and that the split-case upper certificate takes as hypotheses).
-/

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Filter

noncomputable section

variable {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]

/-- `S.lam0 = D.ρ D.j / 8` and `packetEta_law` together give the level of the scaled coordinate. -/
theorem lam0_sq_mul_packetEta {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {η : ℝ}
    (S : MobiusPacket D η) :
    S.lam0 ^ 2 * Work.Drive.N2.packetEta D η = 3 * η / 2 := by
  rw [S.hlam0, Work.Drive.N2.packetEta_law]

/-- The smallness `packetEtaB D η < 1/200` of the window datum gives `packetEta D η < 3/800`. -/
theorem packetEta_lt_three_eightieth {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p)
    {η : ℝ} (hsmall : Work.Drive.N2.packetEtaB D η < 1 / 200) :
    Work.Drive.N2.packetEta D η < 3 / 800 := by
  have h := Work.Drive.N2.packetEtaB_eq D η
  linarith

/-- On the model region at the level `f p + 3η/2`, the scaled square `(Z y)^2` has real part
`packetEta D η` and imaginary part of modulus `< 39/20`. -/
theorem model_zeta {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {η : ℝ}
    (S : MobiusPacket D η) {y : M} (hy : f y = f p + 3 * η / 2)
    (hreg : y ∈ Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) S.Z
      (39 / 20)) :
    ((S.Z y) ^ 2).re = Work.Drive.N2.packetEta D η ∧ |((S.Z y) ^ 2).im| < 39 / 20 := by
  refine ⟨?_, hreg.2⟩
  have h1 := S.hlev y hreg.1
  rw [hy] at h1
  have hlaw := lam0_sq_mul_packetEta (D := D) S
  have hne : S.lam0 ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt S.hlam0pos)
  have h2 : S.lam0 ^ 2 * ((S.Z y) ^ 2).re = S.lam0 ^ 2 * Work.Drive.N2.packetEta D η := by
    rw [hlaw]
    linarith
  exact mul_left_cancel₀ hne h2

/-- The model picture of a level-`(f p + 3η/2)` point of the model region, in `ζ = Z^2` coordinates. -/
theorem model_psi_sq {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {η : ℝ}
    (S : MobiusPacket D η) {y : M} (hy : f y = f p + 3 * η / 2)
    (hreg : y ∈ Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) S.Z
      (39 / 20)) :
    (Work.Drive.N2.saddlePsi (Work.Drive.N2.packetEta D η) (1 / 20) (S.Z y)) ^ 2
      = (mobiusRho (Work.Drive.N2.packetEta D η) (1 / 20) (Work.Drive.N2.packetEta D η)
          (((S.Z y) ^ 2).im)) ^ 2 := by
  obtain ⟨hre, him⟩ := model_zeta (D := D) S hy hreg
  have hδ : (0 : ℝ) < 1 / 20 := by norm_num
  have h2 : (0 : ℝ) ≤ 2 - 4 * (1 / 20) := by norm_num
  rw [Work.Drive.N2.saddlePsi_sq hδ h2, mobiusRho]
  apply Complex.ext <;>
    simp only [Work.Drive.N2.saddlePhi_re, Work.Drive.N2.saddlePhi_im,
      Work.Drive.N2.saddleSigma_apply, complex_sqrt_sq', Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, zero_add, hre]

/-- Consequently `Ψ (Z y) = ± ρ w` on the model region of the upper level. -/
theorem model_psi_eq_or {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {η : ℝ}
    (S : MobiusPacket D η) {y : M} (hy : f y = f p + 3 * η / 2)
    (hreg : y ∈ Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) S.Z
      (39 / 20)) :
    Work.Drive.N2.saddlePsi (Work.Drive.N2.packetEta D η) (1 / 20) (S.Z y)
        = mobiusRho (Work.Drive.N2.packetEta D η) (1 / 20) (Work.Drive.N2.packetEta D η)
            (((S.Z y) ^ 2).im) ∨
      Work.Drive.N2.saddlePsi (Work.Drive.N2.packetEta D η) (1 / 20) (S.Z y)
        = -mobiusRho (Work.Drive.N2.packetEta D η) (1 / 20) (Work.Drive.N2.packetEta D η)
            (((S.Z y) ^ 2).im) :=
  sq_eq_sq_iff_eq_or_eq_neg.mp (model_psi_sq (D := D) S hy hreg)

/-- **(M) the picture value on the model region**: the twisted picture of a level point of the model
region is one of the two pushed, twisted Möbius arcs, evaluated at `w = ((Z y)^2).im`. -/
theorem model_value {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {η : ℝ}
    (S : MobiusPacket D η) {ε εp Dp : ℝ} {y : M} (hy : f y = f p + 3 * η / 2)
    (hreg : y ∈ Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) S.Z
      (39 / 20)) :
    mobiusTwisted D η S ε εp Dp y
        = pushY Dp εp 1
            (mobiusAlpha (Work.Drive.N2.packetEta D η) (1 / 20) (Work.Drive.N2.packetEta D η)
              S.a' ε (((S.Z y) ^ 2).im)) ∨
      mobiusTwisted D η S ε εp Dp y
        = pushY Dp εp 1
            (mobiusBeta (Work.Drive.N2.packetEta D η) (1 / 20) (Work.Drive.N2.packetEta D η)
              S.a' ε (((S.Z y) ^ 2).im)) := by
  rcases model_psi_eq_or (D := D) S hy hreg with h | h
  · right
    rw [mobiusTwisted, mobiusWindowDrawing, if_pos hreg, h]
    rfl
  · left
    rw [mobiusTwisted, mobiusWindowDrawing, if_pos hreg, h]
    rfl

/-- The derivative of the square on `ℂ` is multiplication by `2 a`. -/
theorem fderiv_sq_apply (a z : ℂ) : fderiv ℝ (fun w : ℂ => w ^ 2) a z = 2 * a * z := by
  have h := (hasStrictFDerivAt_pow (𝕜 := ℝ) 2 (x := a)).hasFDerivAt.fderiv
  rw [h]
  simp

end

end Work.Drive.N2Lead
