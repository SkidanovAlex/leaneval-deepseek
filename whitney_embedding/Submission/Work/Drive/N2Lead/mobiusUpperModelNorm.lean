import Mathlib
import Submission.Work.Drive.N2Lead.mobiusUpperFootKit
import Submission.Work.Drive.N2Lead.mobiusUpperStarRowKit
import Submission.Work.Drive.N2Lead.modelArc_cross_about_one

namespace Work.Drive.N2Lead

open Set Filter
open scoped Manifold ContDiff Topology

noncomputable section

/-! ## The norm of the principal square root

`mobiusRho η δ s w = √(σ (s, w) + i w)` (`mobiusRho_eq_sqrt_modelZeta`), so its *square* is the
model coordinate `modelZeta η δ s w` and hence
`‖mobiusRho η δ s w‖ ^ 2 = ‖modelZeta η δ s w‖ = √(σ ^ 2 + w ^ 2)`.  This is the estimate the model
arcs of the upper level need: on the model region of the level `f p + 3η/2` the level coordinate is
`σ = packetEta D η (1 - 2 M)`, of modulus at most `packetEta D η < 3/800`, while `|w| < 39/20`, so
`‖√(σ + i w)‖ ≤ 2` with a wide margin. -/

/-- `‖√z‖ ^ 2 = ‖z‖` for the principal square root of a complex number. -/
lemma norm_sq_sqrt_eq_norm (z : ℂ) : ‖z.sqrt‖ ^ 2 = ‖z‖ := by
  by_cases hz : z = 0
  · rw [hz, Complex.sqrt_zero]; simp
  · calc ‖z.sqrt‖ ^ 2 = ‖z.sqrt‖ * ‖z.sqrt‖ := by rw [pow_two]
      _ = ‖z.sqrt * z.sqrt‖ := by rw [norm_mul]
      _ = ‖z‖ := by rw [sqrt_mul_self_of_ne_zero hz]

/-- The squared norm of `mobiusRho` is the norm of the model coordinate. -/
lemma norm_mobiusRho_sq (η δ s w : ℝ) :
    ‖mobiusRho η δ s w‖ ^ 2 = ‖modelZeta η δ s w‖ := by
  rw [mobiusRho_eq_sqrt_modelZeta]
  exact norm_sq_sqrt_eq_norm _

/-- The model arcs of the upper level, on the model region of the level `f p + 3η/2`: the argument
of the square root has real part `σ (η, w) = η (1 - 2 M w)` of modulus at most `η` and imaginary
part `w` with `|w| < 39/20`; since `η < 3/800` the norm is at most `2`. -/
lemma mobiusRho_norm_le {η δ : ℝ} (hη : 0 ≤ η) (hη' : η < 3 / 800)
    (w : ℝ) (hw : |w| < 39 / 20) : ‖mobiusRho η δ η w‖ ≤ 2 := by
  have hσ : (modelSigma η δ η w) ^ 2 ≤ η ^ 2 :=
    Work.Drive.N2.saddleSigma_sq_le (by rw [abs_of_nonneg hη]) (Work.Drive.N2.saddleM_nonneg δ w)
      (Work.Drive.N2.saddleM_le_one δ w)
  have hw2 : w ^ 2 < (39 / 20 : ℝ) ^ 2 := by
    have h1 : |w| < |(39 / 20 : ℝ)| := by
      rwa [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 39 / 20)]
    exact sq_lt_sq.mpr h1
  have hη2 : η ^ 2 < (3 / 800 : ℝ) ^ 2 := by
    have h1 : |η| < |(3 / 800 : ℝ)| := by
      rwa [abs_of_nonneg hη, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 800)]
    exact sq_lt_sq.mpr h1
  have hbound : ‖mobiusRho η δ η w‖ ^ 2 ≤ 2 := by
    rw [norm_mobiusRho_sq, norm_modelZeta, Real.sqrt_le_iff]
    refine ⟨by norm_num, ?_⟩
    nlinarith [hσ, hη2, hw2]
  refine le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (by norm_num) ?_
  calc ‖mobiusRho η δ η w‖ ^ 2 ≤ 2 := hbound
    _ ≤ (2 : ℝ) ^ 2 := by norm_num

/-- **The norm bound for the two untwisted model arcs of the upper level**: on the model region of
the level `f p + 3η/2` the arcs `α`, `β` lie in the ball of radius `2`.  The two slab twists are
isometries, so it suffices to bound `mobiusRho`. -/
lemma mobiusArc_norm_le {η δ a' ε : ℝ} (hη : 0 ≤ η) (hη' : η < 3 / 800)
    (w : ℝ) (hw : |w| < 39 / 20) :
    ‖mobiusAlpha η δ η a' ε w‖ ≤ 2 ∧ ‖mobiusBeta η δ η a' ε w‖ ≤ 2 := by
  have h : ‖mobiusRho η δ η w‖ ≤ 2 := mobiusRho_norm_le (δ := δ) hη hη' w hw
  constructor
  · rw [mobiusAlpha, norm_twistX, norm_twistY, norm_cE3_eq_engine, norm_neg]
    exact h
  · rw [mobiusBeta, norm_twistX, norm_twistY, norm_cE3_eq_engine]
    exact h

/-- **The norm bound of the twisted picture on the model region.**  For `y` at the level
`f p + 3η/2` and in the scaled model ball `{|Im ((Z y)^2)| < 39/20}` of a Möbius packet, the twisted
picture is the pushed model arc of the level, so its norm is at most `Dp + 2`. -/
theorem mobiusUpperModelNorm {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {η : ℝ}
    (hη : 0 < η) (hsmall : Work.Drive.N2.packetEtaB D η < 1 / 200)
    (S : Work.Drive.N2Lead.MobiusPacket D η) {ε εp Dp : ℝ} (hDp : 0 ≤ Dp) :
    ∀ (y : M), f y = f p + 3 * η / 2 →
      y ∈ Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) S.Z (39 / 20) →
      ‖Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp y‖ ≤ Dp + 2 := by
  intro y hy hreg
  obtain ⟨-, him⟩ := model_zeta (D := D) S hy hreg
  have hηpos : 0 ≤ Work.Drive.N2.packetEta D η :=
    le_of_lt (Work.Drive.N2.packetEta_pos D hη)
  have hηsmall : Work.Drive.N2.packetEta D η < 3 / 800 :=
    packetEta_lt_three_eightieth (D := D) hsmall
  have harc := mobiusArc_norm_le (η := Work.Drive.N2.packetEta D η) (δ := 1 / 20)
    (a' := S.a') (ε := ε) hηpos hηsmall ((S.Z y) ^ 2).im him
  rcases model_value (D := D) S hy hreg with h | h
  · rw [h]
    have hb := norm_pushY_le Dp εp hDp
      (mobiusAlpha (Work.Drive.N2.packetEta D η) (1 / 20) (Work.Drive.N2.packetEta D η) S.a' ε
        (((S.Z y) ^ 2).im))
    linarith [hb, harc.1]
  · rw [h]
    have hb := norm_pushY_le Dp εp hDp
      (mobiusBeta (Work.Drive.N2.packetEta D η) (1 / 20) (Work.Drive.N2.packetEta D η) S.a' ε
        (((S.Z y) ^ 2).im))
    linarith [hb, harc.2]

end

end Work.Drive.N2Lead
