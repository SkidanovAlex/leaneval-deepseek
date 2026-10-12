import ChallengeDeps
import Submission.Work.BoseBogFS.Defs
import Submission.Work.BoseFixB2.DvApriori.exists_adm_chiR0_ge
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The admissible regime of the Bogoliubov chapter

The box side `ℓ(μ) = sideAt μ (a v)` blows up like `a (μa³)^{-163/323}` as the diluteness
`μa³` tends to `0` (`Work.BoseBox.sideAt_eq_rpow`).  The admissible set
`Work.BoseBoxFix.Adm v ε₀ μ` of the a-priori chapter is `0 < μ ∧ μ (a v)³ ≤ ε₀ ∧ ParamsOK`,
i.e. it has no lower bound on `μ` and constrains the diluteness only from above.  Hence *all*
conditions of the shape "`ℓ(μ)` is large" — the large-box condition `R ≤ ℓ chiR0`, the
support-radius condition `R / ℓ ≤ r₁`, and the quadratic-boundedness condition
`C (R/ℓ)² ≤ 1/2` — hold simultaneously on the whole admissible region once `ε₀` is small
enough.

This is the pointwise-in-`μ` version of `Work.BoseBox.sideAt_large` (an `∀ᶠ` statement at
`μ → 0⁺`), in the same style as `Work.BoseFixB2.DvApriori.exists_adm_chiR0_ge`.
-/

namespace Work.BoseBogFS

/-- **The box side exceeds any prescribed positive scale on a diluteness interval.**
If `0 < μ` and `μ A³ ≤ (M/A)^{-323/163}` then `M ≤ sideAt μ A = A (μA³)^{-163/323}`:
the exponent `-163/323` is negative, so the bound `μA³ ≤ (M/A)^{-323/163}` converts into
the lower bound `(μA³)^{-163/323} ≥ M/A`. -/
lemma sideAt_ge_of_mul_le {A M : ℝ} (hA : 0 < A) (hM : 0 < M) {μ : ℝ} (hμ : 0 < μ)
    (h : μ * A ^ 3 ≤ (M / A) ^ (-(323 / 163 : ℝ))) : M ≤ Work.BoseBox.sideAt μ A := by
  have hμA3 : 0 < μ * A ^ 3 := by positivity
  have hMA : 0 < M / A := div_pos hM hA
  have h1 : ((M / A) ^ (-(323 / 163 : ℝ))) ^ (-(163 / 323 : ℝ))
      ≤ (μ * A ^ 3) ^ (-(163 / 323 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hμA3 h (by norm_num)
  have h2 : ((M / A) ^ (-(323 / 163 : ℝ))) ^ (-(163 / 323 : ℝ)) = M / A := by
    rw [← Real.rpow_mul hMA.le,
      show (-(323 / 163 : ℝ)) * (-(163 / 323 : ℝ)) = 1 by norm_num, Real.rpow_one]
  rw [h2] at h1
  rw [Work.BoseBox.sideAt_eq_rpow hA hμ]
  calc M = A * (M / A) := by field_simp
    _ ≤ A * (μ * A ^ 3) ^ (-(163 / 323 : ℝ)) := mul_le_mul_of_nonneg_left h1 hA.le

/-- **The diluteness threshold making the box side exceed `M`.**  For every `M > 0` there is
`ε₀ > 0` such that every admissible chemical potential (`Adm v ε₀ μ`, whose diluteness clause
is `μ (a v)³ ≤ ε₀`) has box side `ℓ v μ = sideAt μ (a v) ≥ M`. -/
lemma exists_adm_ell_ge {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hav : 0 < _root_.BoseGases.a v)
    {M : ℝ} (hM : 0 < M) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → M ≤ Work.BoseFixR.ell v μ := by
  have hdv : 0 < M / _root_.BoseGases.a v := div_pos hM hav
  refine ⟨min 1 ((M / _root_.BoseGases.a v) ^ (-(323 / 163 : ℝ))),
    lt_min one_pos (Real.rpow_pos_of_pos hdv _), ?_⟩
  intro μ hμ
  have hle : μ * (_root_.BoseGases.a v) ^ 3 ≤ (M / _root_.BoseGases.a v) ^ (-(323 / 163 : ℝ)) :=
    le_trans hμ.2.1 (min_le_right _ _)
  rw [Work.BoseFixR.ell_eq]
  exact sideAt_ge_of_mul_le hav hM hμ.1 hle

/-- **The three regime conditions from a single lower bound for `ℓ`.**  If `ℓ ≥ M` where
`M ≥ R/r₁`, `M ≥ R√(2C)` and `M ≥ R/chiR0`, and `C ≥ 0`, then the large-box condition, the
support-radius condition and the quadratic condition `C (R/ℓ)² ≤ 1/2` all hold. -/
lemma regimeArith {R C r₁ M ell : ℝ} (hR : 0 < R) (hC : 0 ≤ C) (hr₁ : 0 < r₁)
    (hMr₁ : R / r₁ ≤ M) (hMC : R * Real.sqrt (2 * C) ≤ M)
    (hMr0 : R / Submission.BoseGases.chiR0 ≤ M) (hMpos : 0 < M) (hell : M ≤ ell) :
    R ≤ ell * Submission.BoseGases.chiR0 ∧ R / ell ≤ r₁ ∧ C * (R / ell) ^ 2 ≤ 1 / 2 := by
  have hχ := Submission.BoseGases.chiR0_pos
  have hellpos : 0 < ell := lt_of_lt_of_le hMpos hell
  refine ⟨?_, ?_, ?_⟩
  · have h : R / Submission.BoseGases.chiR0 * Submission.BoseGases.chiR0 = R := by field_simp
    rw [← h]
    exact mul_le_mul_of_nonneg_right (le_trans hMr0 hell) hχ.le
  · have h1 : R / ell ≤ R / M := div_le_div_of_nonneg_left hR.le hMpos hell
    have h2 : R / M ≤ r₁ := by
      rw [div_le_iff₀ hMpos]
      rw [div_le_iff₀ hr₁] at hMr₁
      linarith
    exact le_trans h1 h2
  · have h0 : (0 : ℝ) ≤ R * Real.sqrt (2 * C) := by positivity
    have hsq : (R * Real.sqrt (2 * C)) ^ 2 ≤ ell ^ 2 :=
      pow_le_pow_left₀ h0 (le_trans hMC hell) 2
    have hsq' : R ^ 2 * (2 * C) ≤ ell ^ 2 := by
      rwa [mul_pow, Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 2 * C)] at hsq
    rw [div_pow, ← mul_div_assoc, div_le_iff₀ (by positivity : (0 : ℝ) < ell ^ 2)]
    nlinarith [hsq']

/-- **The regime of the dilute Bose gas, at a common threshold.**  For every support radius
`R > 0`, every `C ≥ 0` and every `r₁ > 0` there is `ε₀ > 0` such that on the whole admissible
region the box side `ℓ(μ)` satisfies the large-box condition, keeps `R/ℓ ≤ r₁`, and makes
`C (R/ℓ)² ≤ 1/2`. -/
theorem existsAdmRegime {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R C r₁ : ℝ}
    (hR : 0 < R) (hav : 0 < _root_.BoseGases.a v) (hC : 0 ≤ C) (hr₁ : 0 < r₁) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      R ≤ Work.BoseFixR.ell v μ * Submission.BoseGases.chiR0 ∧
      R / Work.BoseFixR.ell v μ ≤ r₁ ∧
      C * (R / Work.BoseFixR.ell v μ) ^ 2 ≤ 1 / 2 := by
  have hχ := Submission.BoseGases.chiR0_pos
  have hMpos : 0 < max (R / r₁)
      (max (R * Real.sqrt (2 * C)) (R / Submission.BoseGases.chiR0)) :=
    lt_of_lt_of_le (div_pos hR hχ)
      (le_trans (le_max_right _ _) (le_max_right _ _))
  obtain ⟨ε₀, hε₀pos, hε₀⟩ := exists_adm_ell_ge hav hMpos
  refine ⟨ε₀, hε₀pos, fun μ hμ => ?_⟩
  exact regimeArith hR hC hr₁ (le_max_left _ _)
    (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_trans (le_max_right _ _) (le_max_right _ _)) hMpos (hε₀ μ hμ)

end Work.BoseBogFS
