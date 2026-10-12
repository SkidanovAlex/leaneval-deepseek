import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseBoxFock.L1Tails.chiChiCoulAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.L1Tails.chiScale_le_of_gap` — the window gap at a lattice image

**The statement.**  For every `N` there is `C ≥ 0` such that for all `ℓ, R > 0` with `R ≤ ℓ/4`,
all nonzero lattice vectors `m` and all `z, y` with `‖z‖ ≤ 2R`:

    chiScale ℓ (z + y − ℓ • latVec m) ≠ 0   ⟹   chiScale ℓ y ≤ C (R/ℓ)^N .

**The mathematics.**  The support of `chiScale ℓ` is the open ball of radius `ℓ/2`
(`Work.BoseFixB1.chiScale_ne_zero_iff`).  The hypothesis says that the *translated* window
`chiScale ℓ (· + y − ℓ•latVec m)` is non-zero at `z`, i.e.

    ‖z + y − ℓ • latVec m‖ < ℓ/2 .

Since `m ≠ 0` has integer coordinates, `‖latVec m‖ ≥ 1`
(`one_le_norm_latVec_local` below), so `‖ℓ • latVec m‖ ≥ ℓ`; decomposing
`ℓ • latVec m = (z + y) − (z + y − ℓ • latVec m)` and using the triangle inequality together
with `‖z‖ ≤ 2R ≤ ℓ/2` gives the **gap estimate**

    ℓ/2 − ‖y‖ < 2R .

Thus `y` lies strictly inside the support ball but within `2R` of its boundary.  The corpus bump
`χ = chi` is `C^∞` and supported in the closed ball of radius `1/2`, hence **flat to all orders**
at its boundary (`Work.BoseFixB1.chi_boundary_taylor`):

    χ u ≤ C_N (1/2 − ‖u‖)^N   for ‖u‖ ≤ 1/2 .

Applying this at `u = ℓ⁻¹ • y`, and using `1/2 − ‖ℓ⁻¹ • y‖ = (ℓ/2 − ‖y‖)/ℓ ≤ 2R/ℓ`, gives
`chiScale ℓ y = χ (ℓ⁻¹ • y) ≤ C_N (2R/ℓ)^N = C_N 2^N (R/ℓ)^N`.

The point of the lemma is exactly the resulting factor `(R/ℓ)^N`: the window at the *image*
`ℓ • latVec m` can only see the part of the box within `2R` of the boundary of its support ball.
-/

noncomputable section

open scoped Real

namespace Work.BoseBoxFock.L1Tails

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- `‖latVec m‖ ≥ 1` for a nonzero lattice vector `m` (the coordinates of `latVec m` are the
integers `m i`). -/
private lemma one_le_norm_latVec_local {m : Fin 3 → ℤ} (hm : m ≠ 0) :
    (1 : ℝ) ≤ ‖Work.BoseBoxFock.latVec m‖ := by
  obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
    by_contra h
    rw [not_exists] at h
    simp only [ne_eq, not_not] at h
    exact hm (funext h)
  have h1 : (1 : ℝ) ≤ |((m i : ℤ) : ℝ)| := by
    have h2 : (1 : ℤ) ≤ |m i| := Int.one_le_abs hi
    exact_mod_cast h2
  have h2 : ‖(Work.BoseBoxFock.latVec m).ofLp i‖ = |((m i : ℤ) : ℝ)| := by
    have h3 : (Work.BoseBoxFock.latVec m).ofLp i = ((m i : ℤ) : ℝ) := by
      simp [Work.BoseBoxFock.latVec, WithLp.ofLp_toLp]
    rw [h3, Real.norm_eq_abs]
  calc (1 : ℝ) ≤ ‖(Work.BoseBoxFock.latVec m).ofLp i‖ := by rw [h2]; exact h1
    _ ≤ ‖Work.BoseBoxFock.latVec m‖ := PiLp.norm_apply_le (Work.BoseBoxFock.latVec m) i

theorem chiScale_le_of_gap (N : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ {ℓ R : ℝ}, 0 < ℓ → 0 < R → R ≤ ℓ / 4 →
    ∀ {m : Fin 3 → ℤ}, m ≠ 0 → ∀ {z y : EuclideanSpace ℝ (Fin 3)}, ‖z‖ ≤ 2 * R →
      Submission.BoseGases.chiScale ℓ (z + y - ℓ • Work.BoseBoxFock.latVec m) ≠ 0 →
      Submission.BoseGases.chiScale ℓ y ≤ C * (R / ℓ) ^ N := by
  obtain ⟨CN, hCNpos, hCN⟩ := Work.BoseFixB1.chi_boundary_taylor N
  refine ⟨CN * 2 ^ N, by positivity, ?_⟩
  intro ℓ R hℓ hR hRℓ m hm z y hz hne
  -- the translated window being non-zero means `z + y − ℓ•latVec m` lies in the support ball
  have hw : ‖z + y - ℓ • Work.BoseBoxFock.latVec m‖ < ℓ / 2 :=
    (Work.BoseFixB1.chiScale_ne_zero_iff hℓ _).1 hne
  by_cases hy : ℓ / 2 ≤ ‖y‖
  · -- outside the support ball the window vanishes, and the right-hand side is non-negative
    rw [Work.BoseFixB1.chiScale_eq_zero_of_half_le_norm hℓ hy]
    exact mul_nonneg (by positivity) (pow_nonneg (div_nonneg hR.le hℓ.le) N)
  · rw [not_le] at hy
    -- ### Step 1: the gap estimate `ℓ/2 − ‖y‖ < 2R`
    have hm1 : (1 : ℝ) ≤ ‖Work.BoseBoxFock.latVec m‖ := one_le_norm_latVec_local hm
    have hgeom : ℓ / 2 - ‖y‖ < 2 * R := by
      have hnorm_smul : ‖ℓ • Work.BoseBoxFock.latVec m‖ = ℓ * ‖Work.BoseBoxFock.latVec m‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hℓ]
      have hdecomp : ℓ • Work.BoseBoxFock.latVec m
          = (z + y) - (z + y - ℓ • Work.BoseBoxFock.latVec m) := by abel
      have hA : ℓ ≤ ‖z + y - ℓ • Work.BoseBoxFock.latVec m‖ + ‖z + y‖ := by
        calc ℓ = ℓ * 1 := by ring
          _ ≤ ℓ * ‖Work.BoseBoxFock.latVec m‖ := mul_le_mul_of_nonneg_left hm1 hℓ.le
          _ = ‖ℓ • Work.BoseBoxFock.latVec m‖ := hnorm_smul.symm
          _ = ‖(z + y) - (z + y - ℓ • Work.BoseBoxFock.latVec m)‖ :=
                congrArg Norm.norm hdecomp
          _ ≤ ‖z + y‖ + ‖z + y - ℓ • Work.BoseBoxFock.latVec m‖ := norm_sub_le _ _
          _ = ‖z + y - ℓ • Work.BoseBoxFock.latVec m‖ + ‖z + y‖ := by ring
      have hzy : ‖z + y‖ ≤ ‖z‖ + ‖y‖ := norm_add_le _ _
      linarith
    -- ### Step 2: the face distance of `ℓ⁻¹ • y`
    have hface : (1 / 2 : ℝ) - ‖(ℓ⁻¹ : ℝ) • y‖ = (ℓ / 2 - ‖y‖) / ℓ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hℓ), inv_mul_eq_div]
      field_simp
    have hnn : 0 ≤ (1 / 2 : ℝ) - ‖(ℓ⁻¹ : ℝ) • y‖ := by
      rw [hface]
      exact div_nonneg (by linarith) hℓ.le
    -- ### Step 3: flatness of the bump at the boundary of its support ball
    have hbound : Submission.BoseGases.chiScale ℓ y
        ≤ CN * ((1 / 2 : ℝ) - ‖(ℓ⁻¹ : ℝ) • y‖) ^ N := by
      rw [Submission.BoseGases.chiScale]
      exact hCN _ (by linarith)
    have hfac : (1 / 2 : ℝ) - ‖(ℓ⁻¹ : ℝ) • y‖ ≤ 2 * (R / ℓ) := by
      rw [hface, show 2 * (R / ℓ) = (2 * R) / ℓ by ring, div_le_div_iff_of_pos_right hℓ]
      linarith
    calc Submission.BoseGases.chiScale ℓ y
        ≤ CN * ((1 / 2 : ℝ) - ‖(ℓ⁻¹ : ℝ) • y‖) ^ N := hbound
      _ ≤ CN * (2 * (R / ℓ)) ^ N :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnn hfac N) hCNpos.le
      _ = CN * 2 ^ N * (R / ℓ) ^ N := by rw [mul_pow]; ring

end Work.BoseBoxFock.L1Tails
