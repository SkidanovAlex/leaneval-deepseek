import Mathlib
import Submission.Work.Drive.N2.windowDatum
import Submission.Work.Drive.N2.saddleModelPsi
import Submission.Work.Drive.N2Lead.saddlePinFunction
import Submission.Work.Drive.N2Lead.modelArc_im_strictMonoOn
import Submission.Work.Drive.N2Lead.mobiusGeomDefs
import Submission.Work.Drive.N2Lead.modelArc_cross_about_one

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology

/-- The principal square root of a complex number that is not a non-positive real has positive real
part. -/
lemma upperMem_sqrt_re_pos {z : ℂ} (hz : z.im ≠ 0 ∨ 0 < z.re) : 0 < (Complex.sqrt z).re := by
  rw [sqrt_re_eq]
  apply Real.sqrt_pos.mpr
  have h2 : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rcases hz with hz | hz
  · have h3 : z.re ^ 2 < z.re ^ 2 + z.im ^ 2 := by
      have : 0 < z.im ^ 2 := by positivity
      linarith
    have h4 : |z.re| < ‖z‖ := by
      have h5 : Real.sqrt (z.re ^ 2) < Real.sqrt (z.re ^ 2 + z.im ^ 2) :=
        Real.sqrt_lt_sqrt (by positivity) h3
      rw [Real.sqrt_sq_eq_abs, ← h2, Real.sqrt_sq (norm_nonneg z)] at h5
      exact h5
    linarith [neg_le_abs z.re]
  · linarith [norm_nonneg z]

/-- **The model picture of a level-`u⁺` point of the model region lies in `Ω_R ∪ Ω_L`.**  For `y ∈ U`
with `f y = c + lam * η` (`lam ≠ 0`) and `|Im (Z y)²| < c₀ ≤ 2`, the picture
`Work.Drive.N2.saddlePsi η δ (Z y)` of the model piece has non-zero real part and norm `< 5`.  The
route: `(Z y)² = η + i w` with `w = Im (Z y)²`, `(saddlePsi η δ (Z y))² = (σ : ℂ) + w I` with
`σ = saddleSigma η δ (η, w) ∈ [-η, η]` (`saddleM ∈ [0,1]`), and `(mobiusRho η δ η w)²` is the same
complex number, so the picture is `±ρ`; `Re ρ > 0` because `ρ` is the principal square root of the
non-real (or positive real) number `σ + i w`; and `‖saddlePsi η δ (Z y)‖² = ‖σ + i w‖ = √(σ² + w²)`
with `|σ| ≤ η`, `|w| < c₀ ≤ 2`, so it is `< 5²`. -/
theorem upperRegionMem {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} {c lam η δ c₀ : ℝ} {U : Set M} {Z : M → ℂ} {y : M}
    (hlev : ∀ x ∈ U, f x = c + lam * ((Z x) ^ 2).re)
    (hlam : lam ≠ 0) (hη : 0 < η) (hη' : η < 1 / 10) (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    (hc₀ : c₀ ≤ 2)
    (hyU : y ∈ U) (hyw : |((Z y) ^ 2).im| < c₀) (hyval : f y = c + lam * η) :
    (0 < (Work.Drive.N2.saddlePsi η δ (Z y)).re ∨ (Work.Drive.N2.saddlePsi η δ (Z y)).re < 0) ∧
      ‖Work.Drive.N2.saddlePsi η δ (Z y)‖ < 5 := by
  have h2 : 0 ≤ 2 - 4 * δ := by linarith
  have hM0 : Work.Drive.N2.saddleM δ 0 = 0 :=
    Work.Drive.N2Lead.saddleM_zero_of_lt_half hδ hδ'
  set w : ℝ := ((Z y) ^ 2).im with hwdef
  set σ : ℝ := Work.Drive.N2.saddleSigma η δ (η, w) with hσdef
  have hre : ((Z y) ^ 2).re = η := by
    have h := hlev y hyU
    rw [hyval] at h
    exact mul_left_cancel₀ hlam (by linarith : lam * ((Z y) ^ 2).re = lam * η)
  have hσeq : σ = η + Work.Drive.N2.saddleM δ w * (-η - η) := by
    rw [hσdef, Work.Drive.N2.saddleSigma_apply]
  have hPsi : (Work.Drive.N2.saddlePsi η δ (Z y)) ^ 2 = (σ : ℂ) + (w : ℂ) * Complex.I := by
    rw [Work.Drive.N2.saddlePsi_sq hδ h2]
    show Work.Drive.N2.saddlePhi η δ ((Z y) ^ 2) = (σ : ℂ) + (w : ℂ) * Complex.I
    rw [Work.Drive.N2.saddlePhi]
    rw [hre, ← hwdef]
  have hρ : (Work.Drive.N2Lead.mobiusRho η δ η w) ^ 2 = (σ : ℂ) + (w : ℂ) * Complex.I := by
    rw [Work.Drive.N2Lead.mobiusRho, Work.Drive.N2.saddleSigma]
    exact Work.Drive.N2.complex_sqrt_sq _
  have hbranch : Work.Drive.N2.saddlePsi η δ (Z y) = Work.Drive.N2Lead.mobiusRho η δ η w ∨
      Work.Drive.N2.saddlePsi η δ (Z y) = -(Work.Drive.N2Lead.mobiusRho η δ η w) := by
    have hsq : (Work.Drive.N2.saddlePsi η δ (Z y)) ^ 2
        = (Work.Drive.N2Lead.mobiusRho η δ η w) ^ 2 := by rw [hPsi, hρ]
    exact sq_eq_sq_iff_eq_or_eq_neg.mp hsq
  have hρre : 0 < (Work.Drive.N2Lead.mobiusRho η δ η w).re := by
    rw [Work.Drive.N2Lead.mobiusRho]
    refine upperMem_sqrt_re_pos ?_
    by_cases hw : w = 0
    · right
      have hsig : Work.Drive.N2.saddleSigma η δ (η, w) = η := by
        rw [Work.Drive.N2.saddleSigma_apply, hw, hM0]; ring
      have h1 : ((Work.Drive.N2.saddleSigma η δ (η, w) : ℂ) + (w : ℂ) * Complex.I).re = η := by
        rw [hsig]; simp
      rw [h1]
      exact hη
    · left
      have : ((Work.Drive.N2.saddleSigma η δ (η, w) : ℂ) + (w : ℂ) * Complex.I).im = w := by
        simp
      rw [this]; exact hw
  constructor
  · rcases hbranch with h | h
    · left; rw [h]; exact hρre
    · right; rw [h]; simpa using hρre
  · have hnorm2 : ‖Work.Drive.N2.saddlePsi η δ (Z y)‖ ^ 2 = ‖(σ : ℂ) + (w : ℂ) * Complex.I‖ := by
      rw [← hPsi, norm_pow]
    have hnormζ : ‖(σ : ℂ) + (w : ℂ) * Complex.I‖ = Real.sqrt (σ ^ 2 + w ^ 2) := by
      have h1 : ‖(σ : ℂ) + (w : ℂ) * Complex.I‖ ^ 2 = σ ^ 2 + w ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, sub_zero, Complex.add_im,
          Complex.mul_im, sq_abs]
        ring
      calc ‖(σ : ℂ) + (w : ℂ) * Complex.I‖
          = Real.sqrt (‖(σ : ℂ) + (w : ℂ) * Complex.I‖ ^ 2) :=
            (Real.sqrt_sq (norm_nonneg _)).symm
        _ = Real.sqrt (σ ^ 2 + w ^ 2) := by rw [h1]
    have hσle : |σ| ≤ η := by
      have hM : Work.Drive.N2.saddleM δ w ∈ Set.Icc (0:ℝ) 1 :=
        Work.Drive.N2Lead.saddleM_mem_Icc δ w
      rw [hσeq, abs_le]
      constructor <;> nlinarith [hM.1, hM.2]
    have hb : Real.sqrt (σ ^ 2 + w ^ 2) < 5 ^ 2 := by
      have h1 : σ ^ 2 + w ^ 2 < 5 ^ 4 := by
        nlinarith [abs_le.mp hσle, abs_lt.mp hyw, hc₀, hη, hη', sq_nonneg σ, sq_nonneg w,
          abs_nonneg w, le_of_lt hη]
      calc Real.sqrt (σ ^ 2 + w ^ 2) < Real.sqrt ((5:ℝ) ^ 4) := Real.sqrt_lt_sqrt (by positivity) h1
        _ = 5 ^ 2 := by
            rw [show ((5:ℝ) ^ 4) = (5 ^ 2) ^ 2 by ring, Real.sqrt_sq (by norm_num)]
    have : ‖Work.Drive.N2.saddlePsi η δ (Z y)‖ ^ 2 < 5 ^ 2 := by rw [hnorm2, hnormζ]; exact hb
    nlinarith [norm_nonneg (Work.Drive.N2.saddlePsi η δ (Z y))]

end Work.Drive.N2Lead

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology

/-- **The anchor level's region points are pinned**: for `y` in the model ball with `f y = c - lam·η`
and `|Im (Z y)²| < c₀ ≤ 39/20`, the pin function is `1`.  This is the row that makes the engine's
two-piece drawing `W` agree with the packet picture `A` on the *anchor* level (the lower
certificate): on the region `W = cE3 ∘ Ψ ∘ Z = A` by `hApin`, and off it `foot y = y` so
`W y = A y` anyway. -/
theorem pinTheta_anchor_region {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {Z : M → ℂ}
    {c lam η c₀ : ℝ}
    (hlev : ∀ x ∈ Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j),
      f x = c + lam * ((Z x) ^ 2).re)
    (hlam : lam ≠ 0) (hη : 0 < η) (hη' : η < 1 / 10) (hc₀ : c₀ ≤ 39 / 20)
    {y : M} (hyU : y ∈ Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j))
    (hyw : |((Z y) ^ 2).im| < c₀) (hyval : f y = c - lam * η) :
    Work.Drive.N2Lead.pinTheta D Z (99 / 50) y = 1 := by
  have hysrc : y ∈ (D.φ D.j).source := hyU.1
  rw [Work.Drive.N2Lead.pinTheta_eq_one_iff D (by norm_num) hysrc]
  have hre : ((Z y) ^ 2).re = -η := by
    have h := hlev y hyU
    rw [hyval] at h
    exact mul_left_cancel₀ hlam (by linarith : lam * ((Z y) ^ 2).re = lam * (-η))
  constructor
  · linarith
  · set w : ℝ := ((Z y) ^ 2).im with hwdef
    have hζ : (Z y) ^ 2 = (((-η : ℝ)) : ℂ) + (w : ℂ) * Complex.I := by
      apply Complex.ext
      · simpa [hre] using hre.symm
      · simpa [hwdef]
    have hsq : ‖(Z y) ^ 2‖ ^ 2 = η ^ 2 + w ^ 2 := by
      rw [hζ]
      have h1 : ‖(((-η : ℝ)) : ℂ) + (w : ℂ) * Complex.I‖ ^ 2 = η ^ 2 + w ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, sub_zero, Complex.add_im,
          Complex.mul_im, sq_abs]
        ring
      exact h1
    have hnorm : ‖Z y‖ ^ 2 = ‖(Z y) ^ 2‖ := by rw [norm_pow]
    have hw2 : w ^ 2 < c₀ ^ 2 := by
      have h := abs_lt.mp hyw
      nlinarith [h.1, h.2, hwdef, abs_nonneg w]
    have hZ : ‖Z y‖ ^ 2 = Real.sqrt (η ^ 2 + w ^ 2) := by
      rw [hnorm]
      exact (Real.sqrt_sq (norm_nonneg _)).symm.trans (by rw [hsq])
    rw [hZ]
    have hle : Real.sqrt (η ^ 2 + w ^ 2) ≤ Real.sqrt (η ^ 2 + c₀ ^ 2) := by
      apply Real.sqrt_le_sqrt
      nlinarith [hw2, sq_nonneg η]
    have hlt : Real.sqrt (η ^ 2 + c₀ ^ 2) < 4 := by
      have hc₀0 : 0 < c₀ := lt_of_le_of_lt (abs_nonneg _) hyw
      have h5 : η ^ 2 + c₀ ^ 2 < 4 ^ 2 := by nlinarith [hη, hη', hc₀, hc₀0, sq_nonneg η]
      calc Real.sqrt (η ^ 2 + c₀ ^ 2) < Real.sqrt ((4 : ℝ) ^ 2) :=
            Real.sqrt_lt_sqrt (by positivity) h5
        _ = 4 := Real.sqrt_sq (by norm_num)
    linarith
end Work.Drive.N2Lead
