import Mathlib
import Submission.Work.Mostow.cegDefs
import Submission.Work.Mostow.stabFlatActionCanon
import Submission.Work.Mostow.levYcFormula
import Submission.Work.Mostow.hptOf_level
import Submission.Work.Mostow.hptOf_yc
import Submission.Work.Mostow.hptOf_hdist
import Submission.Work.Mostow.StabHorosphereBase
import Submission.Work.Mostow.egacYcFlatAction
import Submission.Work.Mostow.egacLevelBounds
import Submission.Work.Mostow.egacCoshEstimate

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

/-- **The geometric estimate behind the elliptic gap.**  Let `γ` fix `ξ ∈ ∂ℍⁿ`, preserve the
horosphere levels `lev ξ ·`, have flat rotation at most `θ₀` (`cegSmall ξ θ₀ γ`) and fix a point
`p`.  If `θ₀` is small compared with `η` and `L > 0` is small compared with `1/‖yc ξ p‖`, then `γ`
is `η`-close to the identity on the unit ball around the deep point `hptOf ξ 0 L`.

Route: `cosh (hdist u (γ • u)) = 1 + (lev ξ u)^2 / 2 * ‖(flatLin ξ (Λγ) - id) (yc ξ u - yc ξ p)‖^2`
(`levYcFormula` + `stabFlatActionCanon` — `hlev` at `u = 0` gives `busemann ξ (γ • 0) = 0` — using
that `p` is fixed so that `flatTrans ξ (Λγ) = yc ξ p - flatLin ξ (Λγ) (yc ξ p)`);
for `hdist (hptOf ξ 0 L) u ≤ 1` one has `lev ξ u ≤ e * L` and `‖yc ξ u‖ ≤ 4 / L`
(`busemann_lipschitz` + `levYcFormula` at the point `hptOf ξ 0 L`, whose flat coordinate is `0`),
whence `cosh (hdist u (γ • u)) - 1 ≤ (e^2/2) (4 θ₀ + θ₀ L ‖yc ξ p‖)^2 ≤ η^2/2 ≤ cosh η - 1`. -/
theorem egacNearIdOfSmallRot (n : ℕ) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n) {ξ : Submission.Mostow.E n}
    (hξ : ξ ∈ Submission.Mostow.Sph n) {γ : LeanEval.Geometry.MostowRigidity.PO n 1}
    (hγbd : Submission.Mostow.bd γ ξ = ξ)
    (hlev : ∀ u : Submission.Mostow.E n, Work.Mostow.lev ξ (γ • u) = Work.Mostow.lev ξ u)
    {θ₀ : ℝ} (hθ₀ : 0 < θ₀) (hsmall : Work.Mostow.cegSmall ξ θ₀ γ)
    (p : Submission.Mostow.E n) (hp : γ • p = p)
    {η : ℝ} (hη : 0 < η) (hη8 : η ≤ 1 / 8) (hθ₀η : 4 * θ₀ ≤ η / 16)
    {L : ℝ} (hL : 0 < L) (hLb : θ₀ * L * ‖Work.Mostow.yc ξ p‖ ≤ η / 8) :
    Submission.Mostow.NearIdAt γ (Work.Mostow.hptOf ξ 0 L) η := by
  -- `NearIdAt` unfolds to a bound on the displacement of every point of the unit ball.
  intro u hu
  -- the flat coordinate of `γ • u` is the affine image of that of `u`
  have hycA : ∀ v : Submission.Mostow.E n, yc ξ (γ • v) =
      flatLin ξ (LambdaMat γ) (yc ξ v) + flatTrans ξ (LambdaMat γ) :=
    egacYcFlatAction n hA hI hξ hγbd hlev
  -- the translation part is determined by the fixed point `p`
  have hT : flatTrans ξ (LambdaMat γ) = yc ξ p - flatLin ξ (LambdaMat γ) (yc ξ p) := by
    have h := hycA p
    rw [hp] at h
    have h' : yc ξ p - flatLin ξ (LambdaMat γ) (yc ξ p) = flatTrans ξ (LambdaMat γ) := by
      nth_rewrite 1 [h]
      abel
    exact h'.symm
  -- hence the flat displacement of `γ` at `u` is `(flatLin ξ (Λγ) - id) (yc ξ u - yc ξ p)`
  have hnorm : ∀ v : Submission.Mostow.E n, yc ξ v - yc ξ (γ • v) =
      -(flatLin ξ (LambdaMat γ) (yc ξ v - yc ξ p) - (yc ξ v - yc ξ p)) := by
    intro v
    rw [hycA v, hT, map_sub]
    abel
  -- the horospherical form of the distance, at common level
  have hcosh : Real.cosh (Submission.Mostow.hdist u (γ • u)) =
      1 + (lev ξ u) ^ 2 / 2 * ‖yc ξ u - yc ξ (γ • u)‖ ^ 2 := by
    have h := levYcFormula hξ u (γ • u)
    rw [hlev u] at h
    rw [div_self (ne_of_gt (lev_pos ξ hξ u)), Real.log_one, Real.cosh_zero] at h
    rw [h]; ring
  -- the level and flat-coordinate bounds near the deep point
  obtain ⟨hlevle, hycle⟩ := egacLevelBounds n hI hξ hL u hu
  -- orthogonality of `yc ξ ·`, so that the rotation hypothesis applies
  have hYc : ∀ v : Submission.Mostow.E n, inner ℝ (yc ξ v) ξ = 0 := by
    intro v
    have hξ1 : inner ℝ ξ ξ = 1 := by
      rw [real_inner_self_eq_norm_sq]
      have h1 : ‖ξ‖ = 1 := by simpa [Sph, Metric.mem_sphere, dist_eq_norm] using hξ
      rw [h1]; norm_num
    have hw : inner ℝ (wc ξ v) ξ = 0 := by
      simp only [wc, inner_sub_left, real_inner_smul_left, hξ1, mul_one]
      ring
    simp only [yc, real_inner_smul_left, hw, mul_zero]
  -- the flat displacement is at most `θ₀` times the distance of `yc ξ u` to `yc ξ p`
  have hrot : ‖yc ξ u - yc ξ (γ • u)‖ ≤ θ₀ * ‖yc ξ u - yc ξ p‖ := by
    rw [hnorm u, norm_neg]
    have hx : inner ℝ (yc ξ u - yc ξ p) ξ = 0 := by
      rw [inner_sub_left, hYc u, hYc p, sub_zero]
    exact hsmall (yc ξ u - yc ξ p) hx
  have hnormyc : ‖yc ξ u - yc ξ p‖ ≤ 4 / L + ‖yc ξ p‖ := by
    calc ‖yc ξ u - yc ξ p‖ ≤ ‖yc ξ u‖ + ‖yc ξ p‖ := norm_sub_le _ _
      _ ≤ 4 / L + ‖yc ξ p‖ := by linarith
  -- the estimate `cosh (hdist u (γ • u)) - 1 ≤ (e²/2) (4 θ₀ + θ₀ L ‖yc ξ p‖)²`
  have hmain : (lev ξ u) ^ 2 / 2 * ‖yc ξ u - yc ξ (γ • u)‖ ^ 2 ≤
      (Real.exp 1) ^ 2 / 2 * (4 * θ₀ + θ₀ * L * ‖yc ξ p‖) ^ 2 := by
    have hrot' : ‖yc ξ u - yc ξ (γ • u)‖ ≤ θ₀ * (4 / L + ‖yc ξ p‖) :=
      hrot.trans (mul_le_mul_of_nonneg_left hnormyc (le_of_lt hθ₀))
    have hstep : (lev ξ u) ^ 2 / 2 * ‖yc ξ u - yc ξ (γ • u)‖ ^ 2 ≤
        (Real.exp 1 * L) ^ 2 / 2 * (θ₀ * (4 / L + ‖yc ξ p‖)) ^ 2 := by
      have h2 : (0:ℝ) ≤ θ₀ * (4 / L + ‖yc ξ p‖) := by
        have h3 : (0:ℝ) ≤ 4 / L + ‖yc ξ p‖ := by positivity
        exact mul_nonneg (le_of_lt hθ₀) h3
      have hb : (0:ℝ) ≤ (Real.exp 1 * L) ^ 2 / 2 := by positivity
      refine mul_le_mul ?_ ?_ (pow_nonneg (norm_nonneg _) 2) hb
      · exact div_le_div_of_nonneg_right
          (pow_le_pow_left₀ (le_of_lt (lev_pos ξ hξ u)) hlevle 2) (by norm_num)
      · exact pow_le_pow_left₀ (norm_nonneg _) hrot' 2
    refine hstep.trans (le_of_eq ?_)
    field_simp
    try ring
  have hfinal : Real.cosh (Submission.Mostow.hdist u (γ • u)) - 1 ≤
      (Real.exp 1) ^ 2 / 2 * (4 * θ₀ + θ₀ * L * ‖yc ξ p‖) ^ 2 := by
    rw [hcosh]; linarith
  -- the numerical gap
  have hA0 : (0:ℝ) ≤ 4 * θ₀ + θ₀ * L * ‖yc ξ p‖ := by
    have h1 : 0 ≤ θ₀ * L * ‖yc ξ p‖ :=
      mul_nonneg (mul_nonneg (le_of_lt hθ₀) (le_of_lt hL)) (norm_nonneg _)
    nlinarith
  have hAb : 4 * θ₀ + θ₀ * L * ‖yc ξ p‖ ≤ 3 * η / 16 := by
    have h1 : 4 * θ₀ ≤ η / 16 := hθ₀η
    have h2 : θ₀ * L * ‖yc ξ p‖ ≤ η / 8 := hLb
    linarith
  have hest := egacCoshEstimate hη hA0 hAb
  have hlt : Real.cosh (Submission.Mostow.hdist u (γ • u)) < Real.cosh η := by
    linarith
  -- conclude that the displacement is below `η`
  have h := Real.cosh_lt_cosh.mp hlt
  rw [abs_of_nonneg (hI.1 u (γ • u)), abs_of_pos hη] at h
  exact h

end Work.Mostow
