import Mathlib
import Submission.Work.Whitney.CutPush.lipschitz_smooth_cutoff
import Submission.Work.Whitney.CutPush.lipschitz_cutoff_rescale
import Submission.Work.Whitney.CutPush.exists_fderiv_close_of_contDiff

/-!
# The numerical setup of the germ assembly (step (c), first half)

STATUS: **statement only, body is a `sorry`.**  This file isolates the statement of the setup lemma
of the germ assembly (`NOTES_hasFingerData_S33.md` §15) so that it can be made to elaborate on its
own, before the proof is written.  The proof inputs are all proved and on disk:
`exists_lipschitz_smooth_cutoff` (fixed shape at radii `(1,3)`, constant `C₁`),
`lipschitz_cutoff_rescale` (any scale `r`, `Lip χ_r = C₁/r`), and
`exists_fderiv_close_of_contDiff''` (`Ae` in, ball at prescribed `c` out).
-/

open scoped ContDiff Topology NNReal

namespace Work.Whitney.CutPush

/-- **The numerical setup of the germ assembly**: the linear part `Ae`, a fixed-shape cutoff constant
`C`, a prescribed tolerance `c`, a radius `r` and a cutoff `χ` at scale `r`, with
`‖Ae.symm‖ * (c * (3 * C + 1)) < 1 / 2` — the `< 1` needed by
`exists_global_diffeo_of_small_perturbation`. -/
theorem exists_germ_setup {N : ℕ}
    (Φ : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (hd : Function.Injective (fderiv ℝ Φ 0)) :
    ∃ (Ae : EuclideanSpace ℝ (Fin N) ≃L[ℝ] EuclideanSpace ℝ (Fin N)),
    ∃ (C : ℝ), ∃ (c : ℝ), ∃ (r : ℝ),
    ∃ (χ : EuclideanSpace ℝ (Fin N) → ℝ),
      (0 < c) ∧ (0 < r) ∧ (0 ≤ C) ∧
      ((Ae : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) = fderiv ℝ Φ 0) ∧
      (ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) ∧
      (∀ (u : EuclideanSpace ℝ (Fin N)), 0 ≤ χ u ∧ χ u ≤ 1) ∧
      (∀ (u : EuclideanSpace ℝ (Fin N)), ‖u‖ ≤ r → χ u = 1) ∧
      (∀ (u : EuclideanSpace ℝ (Fin N)), 3 * r ≤ ‖u‖ → χ u = 0) ∧
      (∀ (x : EuclideanSpace ℝ (Fin N)) (y : EuclideanSpace ℝ (Fin N)),
        ‖χ x - χ y‖ ≤ (C / r) * ‖x - y‖) ∧
      (‖(Ae.symm : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N))‖
        * (c * (3 * C + 1)) < 1 / 2) ∧
      (∀ (y : EuclideanSpace ℝ (Fin N)), ‖y‖ < 3 * r →
        ‖fderiv ℝ (fun z : EuclideanSpace ℝ (Fin N) => Φ z - Φ 0 - Ae z) y‖ ≤ c) := by
  classical
  -- ## first step: the linear part, built by hand (trap 13c: the packaged lemma returns `Ae`,
  -- but the tolerance `c` below has to be read off `‖(Ae.symm : E →L)‖` first)
  have hker : (fderiv ℝ Φ 0).ker = ⊥ := LinearMap.ker_eq_bot.mpr hd
  have hsurj : (fderiv ℝ Φ 0).range = ⊤ :=
    LinearMap.range_eq_top.mpr (LinearMap.injective_iff_surjective.mp hd)
  let Ae : EuclideanSpace ℝ (Fin N) ≃L[ℝ] EuclideanSpace ℝ (Fin N) :=
    ContinuousLinearEquiv.ofBijective (fderiv ℝ Φ 0) hker hsurj
  have hAe : (Ae : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) = fderiv ℝ Φ 0 :=
    DFunLike.coe_injective
      (ContinuousLinearEquiv.coeFn_ofBijective (fderiv ℝ Φ 0) hker hsurj)
  -- ## second step: the fixed-shape cutoff at radii `(1, 3)` (trap 13b)
  obtain ⟨χ1, C, hC, hχ1, hb1, h11, h01, hlip1⟩ :=
    exists_lipschitz_smooth_cutoff (N := N) (R := 1) (R' := 3) one_pos (by norm_num)
  -- ## third step: the prescribed tolerance (traps 13a and 13c)
  let c : ℝ := (2 * (‖(Ae.symm : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N))‖
    * (3 * C + 1) + 1))⁻¹
  have hcpos : 0 < c := by
    have h1 : (0 : ℝ) ≤ ‖(Ae.symm : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N))‖ :=
      norm_nonneg _
    have h2 : (0 : ℝ) ≤ 3 * C + 1 := by linarith
    have h3 : 0 < 2 * (‖(Ae.symm : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N))‖
        * (3 * C + 1) + 1) := by positivity
    exact inv_pos.mpr h3
  -- ## fourth step: the ball on which the first-order remainder has small derivative
  obtain ⟨ρ, hρ, hclose⟩ := exists_fderiv_close_of_contDiff'' Φ hΦ Ae hAe c hcpos
  -- ## fifth step: the radius of the support, inside that ball
  let r : ℝ := min 1 (ρ / 3)
  have hrpos : 0 < r := lt_min one_pos (div_pos hρ (by norm_num))
  have hrρ : 3 * r ≤ ρ := by
    have h1 : r ≤ ρ / 3 := min_le_right _ _
    linarith
  -- ## sixth step: the cutoff at the chosen scale (trap 13b)
  obtain ⟨χ, hχ, hb, h1χ, h0χ, hlipχ⟩ :=
    lipschitz_cutoff_rescale χ1 C hC hχ1 hb1 h11 h01 hlip1 r hrpos
  refine ⟨Ae, C, c, r, χ, hcpos, hrpos, hC, hAe, hχ, hb, h1χ, h0χ, hlipχ, ?_, ?_⟩
  · -- the numeric side condition (the `+ 1` in `c` disposes of `Ae.symm = 0`, i.e. `N = 0`)
    have hnorm : (0 : ℝ) ≤
        ‖(Ae.symm : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N))‖ := norm_nonneg _
    have h3C : (0 : ℝ) ≤ 3 * C + 1 := by linarith
    have hden : 0 < 2 * (‖(Ae.symm : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N))‖
        * (3 * C + 1) + 1) := by positivity
    rw [show c = (2 * (‖(Ae.symm : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N))‖
      * (3 * C + 1) + 1))⁻¹ from rfl]
    field_simp
    nlinarith [hnorm, h3C]
  · -- the derivative bound on the support
    intro y hy
    exact hclose y (lt_of_lt_of_le hy hrρ)

end Work.Whitney.CutPush
