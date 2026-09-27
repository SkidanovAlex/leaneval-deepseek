import Mathlib
import Submission.Work.Surf.defs
import Submission.Work.Drive.finite_of_isCompact_of_isolated

/-!
# The zeros of a `C¹` map of the plane in the unit square are finite

For `F : 𝔼² → 𝔼²` of class `C¹` which does not vanish on the boundary of the unit square
`Work.Surf.sqBox` and whose derivative is surjective at every zero in the square, the set of zeros of
`F` in the square is finite.

The two ingredients are the classical ones:

* at a zero `p` with surjective derivative, `fderiv ℝ F p` is an invertible continuous linear map (the
  two spaces have the same finite dimension), so the inverse function theorem
  (`HasStrictFDerivAt.eventually_left_inverse`) makes `F` injective on a neighbourhood of `p`: the
  zeros are *isolated*;
* the zero set is closed in the compact square, hence compact, and a compact set all of whose points
  are isolated is finite (`Work.Drive.finite_of_isCompact_of_isolated`).
-/

namespace Work.Surf

open Set Filter
open scoped Topology

noncomputable section

/-- The unit square is compact: it is the preimage of `[0,1]×[0,1] ⊂ (Fin 2 → ℝ)` under the
homeomorphism `𝔼² ≃ₜ (Fin 2 → ℝ)`. -/
lemma isCompact_sqBox_euc : IsCompact sqBox := by
  have h : sqBox = (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)) ⁻¹'
      (Set.univ.pi fun _ : Fin 2 => Set.Icc (0 : ℝ) 1) := by
    ext x
    rw [Set.mem_preimage, show (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)) x = x.ofLp from rfl]
    simp only [Set.mem_univ_pi]
    rw [sqBox, Fin.forall_fin_two]
    simp only [Set.mem_ofPred_eq, Set.mem_Icc]
  rw [h]
  exact (Homeomorph.isCompact_preimage _).mpr (isCompact_univ_pi fun _ => isCompact_Icc)

/-- The unit square is closed. -/
lemma isClosed_sqBox_euc : IsClosed sqBox := isCompact_sqBox_euc.isClosed

/-- **A `C¹` map with invertible derivative at `a` is injective near `a`**: the inverse function
theorem applied at `a`. -/
lemma euc_eventually_eq {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {f' : E ≃L[ℝ] F} {a : E} (hf : HasStrictFDerivAt f (f' : E →L[ℝ] F) a) :
    ∀ᶠ y in 𝓝 a, f y = f a → y = a := by
  filter_upwards [hf.eventually_left_inverse] with y hy hfy
  rw [← hy, hfy, hf.localInverse_apply_image]

/-- **A regular zero of a `C¹` map of the plane is isolated in the zero set.** -/
lemma exists_nhds_inter_zero_eq_euc {F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hF : ContDiff ℝ 1 F) {p : EuclideanSpace ℝ (Fin 2)} (hp0 : F p = 0)
    (hsurj : Function.Surjective (fderiv ℝ F p)) :
    ∃ U : Set (EuclideanSpace ℝ (Fin 2)), IsOpen U ∧ p ∈ U ∧ U ∩ {q | F q = 0} ⊆ {p} := by
  have hker : (fderiv ℝ F p).ker = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).mpr hsurj
  have hran : (fderiv ℝ F p).range = ⊤ := LinearMap.range_eq_top.mpr hsurj
  set L' : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    ContinuousLinearEquiv.ofBijective (fderiv ℝ F p) hker hran with hL'
  have hcoe : (L' : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) =
      fderiv ℝ F p := by
    rw [hL']
    exact ContinuousLinearEquiv.coe_ofBijective _ _ _
  have hstrict : HasStrictFDerivAt F
      (L' : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) p := by
    rw [hcoe]
    exact hF.contDiffAt.hasStrictFDerivAt (by norm_num)
  obtain ⟨ε, hεpos, hε⟩ := Metric.eventually_nhds_iff.mp (euc_eventually_eq hstrict)
  refine ⟨Metric.ball p ε, Metric.isOpen_ball, Metric.mem_ball_self hεpos, ?_⟩
  rintro q ⟨hq, hq0⟩
  rw [Metric.mem_ball] at hq
  simp only [Set.mem_singleton_iff]
  exact hε hq (by rw [hq0, hp0])

/-- **The zeros of `F` in the unit square are finite**, when `F` is `C¹`, nonzero on the boundary of
the square, and every zero in the square is a regular point of `F`. -/
theorem zeros_finite_euc
    (F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) (hF : ContDiff ℝ 1 F)
    (hbdry : ∀ x ∈ Work.Surf.sqBdry, F x ≠ 0)
    (hreg : ∀ x ∈ Work.Surf.sqBox, F x = 0 → Function.Surjective (fderiv ℝ F x)) :
    ({x : EuclideanSpace ℝ (Fin 2) | x ∈ Work.Surf.sqBox ∧ F x = 0}).Finite := by
  -- the zeros of `F` in the square avoid its boundary
  have hnotbdry : ∀ x ∈ sqBox, F x = 0 → x ∉ sqBdry := fun x _ hx hb => hbdry x hb hx
  have hZclosed : IsClosed ({x : EuclideanSpace ℝ (Fin 2) | x ∈ sqBox ∧ F x = 0}) :=
    isClosed_sqBox_euc.inter (isClosed_eq hF.continuous continuous_const)
  have hZcpt : IsCompact ({x : EuclideanSpace ℝ (Fin 2) | x ∈ sqBox ∧ F x = 0}) :=
    isCompact_sqBox_euc.of_isClosed_subset hZclosed fun x hx => hx.1
  refine Work.Drive.finite_of_isCompact_of_isolated hZcpt (fun p hp => ?_)
  obtain ⟨U, hUo, hpU, hUZ⟩ := exists_nhds_inter_zero_eq_euc hF hp.2 (hreg p hp.1 hp.2)
  exact ⟨U, hUo, hpU, fun x hx => hUZ ⟨hx.1, hx.2.2⟩⟩

end

end Work.Surf
