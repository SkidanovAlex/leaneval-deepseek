/-
# `Work.FTS_RegExport.RXT.st1_stdata` — the pointwise fields of `St1Class`

The two pointwise pieces of the `St1` export (`Work.FTS_RegExport.RXT.st1_of_weighted`):

* `st1_dthvan` — `|D_θ g̃| ≤ Cθ·z²Γ(θ)`: the `(0,1)`-slot bound `|D_θ g| ≤ Kω` together with
  `ω ≤ z²Γ` and the vanishing `g z 0 τ = g z (π/2) τ = 0` at the two angular endpoints.
* `st1_quad` — the Taylor data at `z = 0`: `|g̃| ≤ Kz²` and `|∂_z g̃| ≤ Kz`, i.e. the
  `(0,0)`- and `(1,0)`-slots with `ω ≤ z²Γ ≤ z²` resp. `ω/z ≤ Γ ≤ 1`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS_RegExport.RXT.st1_prelim

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_RegExport.RXT

/-- The `Γ`-vanishing of the angular derivative of `g̃`. -/
theorem st1_dthvan {α : ℝ} (hα : 0 < α) {g : Work.FTS.Galerkin.Fam} {S K : ℝ}
    (hmin : Work.FTS.StrongGlobal.RegPkgMin (Work.FTS.Regularity.pExp α) g) (hS : 0 < S)
    (hw : ∀ k : Fin 6, ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed (Work.FTS.RegExportIface.RXT.idx k).1
        (Work.FTS.RegExportIface.RXT.idx k).2
        (Work.FTS.Galerkin.slice g τ) z θ| ≤ K * Work.FTS.RegExportIface.ω α z θ) :
    ∃ Cθ : ℝ, 0 ≤ Cθ ∧ ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z θ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.Dth (Work.FTS.Regularity.gSlice (GG α g) τ) z θ|
        ≤ Cθ * z ^ 2 * Work.FTS.Regularity.Gamma α θ := by
  refine ⟨|K|, abs_nonneg K, ?_⟩
  intro τ hτ z θ hz hθ
  rcases eq_or_lt_of_le hz with hz0 | hzpos
  · -- `z = 0`: the `GG`-slice at `z = 0` is identically zero
    subst hz0
    have hfun : (fun θ' : ℝ => GG α g 0 θ' τ) = fun _ => (0:ℝ) :=
      funext (fun θ' => GG_of_nonpos α le_rfl)
    have hD0 : Work.Spaces.Dth (Work.FTS.Regularity.gSlice (GG α g) τ) 0 θ = 0 := by
      show Real.sin (2 * θ) * deriv (fun θ' => GG α g 0 θ' τ) θ = 0
      rw [hfun, deriv_const, mul_zero]
    rw [hD0, abs_zero]
    simp
  · rcases eq_or_lt_of_le hθ.1 with hθ0 | hθpos
    · -- `θ = 0`
      subst hθ0
      have hD0 : Work.Spaces.Dth (Work.FTS.Regularity.gSlice (GG α g) τ) z 0 = 0 := by
        show Real.sin (2 * (0:ℝ)) * deriv (fun θ' => GG α g z θ' τ) 0 = 0
        rw [mul_zero, Real.sin_zero, zero_mul]
      rw [hD0, abs_zero, Gamma_zero_left hα]
      simp
    · rcases eq_or_lt_of_le hθ.2 with hθπ | hθlt
      · -- `θ = π/2`
        subst hθπ
        have hD0 : Work.Spaces.Dth (Work.FTS.Regularity.gSlice (GG α g) τ) z (π / 2) = 0 := by
          show Real.sin (2 * (π / 2)) * deriv (fun θ' => GG α g z θ' τ) (π / 2) = 0
          rw [show Real.sin (2 * (π / 2)) = 0 by
            rw [show 2 * (π / 2) = π by ring, Real.sin_pi], zero_mul]
        rw [hD0, abs_zero, Gamma_zero_right hα]
        simp
      · -- interior: the `(0,1)`-slot
        have hD : Work.Spaces.Dth (Work.FTS.Regularity.gSlice (GG α g) τ) z θ
            = Work.Spaces.mixed 0 1 (Work.FTS.Galerkin.slice g τ) z θ := by
          rw [Dth_GG_eq α hτ.1 hzpos hθpos hθlt]
          rfl
        rw [hD]
        have h2 := hw (2 : Fin 6) τ hτ z θ hzpos hθpos hθlt
        norm_num [Work.FTS.RegExportIface.RXT.idx] at h2
        calc |Work.Spaces.mixed 0 1 (Work.FTS.Galerkin.slice g τ) z θ|
            ≤ K * Work.FTS.RegExportIface.ω α z θ := h2
          _ ≤ |K| * Work.FTS.RegExportIface.ω α z θ :=
              mul_le_mul_of_nonneg_right (le_abs_self K) (omega_nonneg_of α z θ hzpos.le hθ)
          _ ≤ |K| * (z ^ 2 * Work.FTS.Regularity.Gamma α θ) :=
              mul_le_mul_of_nonneg_left (omega_le_zsq_mul_Gamma α z θ hzpos.le hθ) (abs_nonneg K)
          _ = |K| * z ^ 2 * Work.FTS.Regularity.Gamma α θ := by ring

/-- The Taylor data at `z = 0`. -/
theorem st1_quad {α : ℝ} (hα : 0 < α) {g : Work.FTS.Galerkin.Fam} {S K : ℝ}
    (hmin : Work.FTS.StrongGlobal.RegPkgMin (Work.FTS.Regularity.pExp α) g) (hS : 0 < S)
    (hK0 : 0 ≤ K)
    (hw : ∀ k : Fin 6, ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed (Work.FTS.RegExportIface.RXT.idx k).1
        (Work.FTS.RegExportIface.RXT.idx k).2
        (Work.FTS.Galerkin.slice g τ) z θ| ≤ K * Work.FTS.RegExportIface.ω α z θ) :
    ∃ Kq Q : ℝ, 0 ≤ Kq ∧ 0 ≤ Q ∧ ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ θ ∈ Work.Spaces.Iθ,
      (∀ z : ℝ, 0 ≤ z → z ≤ 2 → |GG α g z θ τ| ≤ Kq * z ^ 2) ∧
        ∀ z : ℝ, 0 ≤ z → z ≤ 2 →
          |Work.Spaces.pz (Work.FTS.Regularity.gSlice (GG α g) τ) z θ| ≤ Q * z := by
  have hv : ∀ τ : ℝ, 0 ≤ τ → ∀ z : ℝ, 0 ≤ z → g z 0 τ = 0 ∧ g z (π / 2) τ = 0 :=
    fun τ hτ z hz => hmin.vanish τ hτ z hz
  refine ⟨|K|, |K|, abs_nonneg K, abs_nonneg K, ?_⟩
  intro τ hτ θ hθ
  refine ⟨?_, ?_⟩
  · intro z hz hz2
    rcases eq_or_lt_of_le hz with hz0 | hzpos
    · subst hz0
      rw [GG_of_nonpos α le_rfl, abs_zero]
      positivity
    · rcases eq_or_lt_of_le hθ.1 with hθ0 | hθpos
      · subst hθ0
        rw [GG_eq_zero_left α hτ.1 hzpos hv, abs_zero]
        positivity
      · rcases eq_or_lt_of_le hθ.2 with hθπ | hθlt
        · subst hθπ
          rw [GG_eq_zero_right α hτ.1 hzpos hv, abs_zero]
          positivity
        · rw [GG_of_mem α hτ.1 hzpos hθ]
          have h0 := hw (0 : Fin 6) τ hτ z θ hzpos hθpos hθlt
          norm_num [Work.FTS.RegExportIface.RXT.idx] at h0
          have hΓ1 : Work.FTS.Regularity.Gamma α θ ≤ 1 :=
            Work.ConstructionInstance.Gamma_le_one hα.le hθ
          have hΓ0 : 0 ≤ Work.FTS.Regularity.Gamma α θ :=
            Work.ConstructionInstance.Gamma_nonneg hθ
          calc |Work.FTS.Galerkin.slice g τ z θ|
              = |Work.Spaces.mixed 0 0 (Work.FTS.Galerkin.slice g τ) z θ| := rfl
            _ ≤ K * Work.FTS.RegExportIface.ω α z θ := h0
            _ ≤ |K| * Work.FTS.RegExportIface.ω α z θ :=
                mul_le_mul_of_nonneg_right (le_abs_self K) (omega_nonneg_of α z θ hzpos.le hθ)
            _ ≤ |K| * (z ^ 2 * Work.FTS.Regularity.Gamma α θ) :=
                mul_le_mul_of_nonneg_left (omega_le_zsq_mul_Gamma α z θ hzpos.le hθ)
                  (abs_nonneg K)
            _ ≤ |K| * z ^ 2 := by
                have h := mul_le_mul_of_nonneg_left hΓ1 (mul_nonneg (abs_nonneg K) (sq_nonneg z))
                simpa only [mul_assoc, mul_one] using h
  · intro z hz hz2
    rcases eq_or_lt_of_le hz with hz0 | hzpos
    · subst hz0
      have h0 : Work.Spaces.pz (Work.FTS.Regularity.gSlice (GG α g) τ) 0 θ = 0 := by
        show deriv (fun z' => GG α g z' θ τ) 0 = 0
        exact deriv_eq_zero_of_eq_zero_of_nonpos (fun y hy => GG_of_nonpos α hy)
      rw [h0, abs_zero]
      positivity
    · rcases eq_or_lt_of_le hθ.1 with hθ0 | hθpos
      · subst hθ0
        rw [pz_GG_eq_zero_left α hτ.1 hzpos hv, abs_zero]
        positivity
      · rcases eq_or_lt_of_le hθ.2 with hθπ | hθlt
        · subst hθπ
          rw [pz_GG_eq_zero_right α hτ.1 hzpos hv, abs_zero]
          positivity
        · rw [pz_GG_eq α hτ.1 hzpos hθ]
          have h1 := hw (1 : Fin 6) τ hτ z θ hzpos hθpos hθlt
          norm_num [Work.FTS.RegExportIface.RXT.idx] at h1
          have hΓ1 : Work.FTS.Regularity.Gamma α θ ≤ 1 :=
            Work.ConstructionInstance.Gamma_le_one hα.le hθ
          have hΓ0 : 0 ≤ Work.FTS.Regularity.Gamma α θ :=
            Work.ConstructionInstance.Gamma_nonneg hθ
          have hkey : |Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z θ| * z
              ≤ K * Work.FTS.RegExportIface.ω α z θ := by
            have h2 : |Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z θ| * z
                = |Work.Spaces.mixed 1 0 (Work.FTS.Galerkin.slice g τ) z θ| := by
              show |Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z θ| * z
                = |z * Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z θ|
              rw [abs_mul, abs_of_pos hzpos]; ring
            rw [h2]; exact h1
          have h4 : |Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z θ|
              ≤ K * (Work.FTS.RegExportIface.ω α z θ / z) := by
            have h5 : |Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z θ|
                ≤ K * Work.FTS.RegExportIface.ω α z θ / z := (le_div_iff₀ hzpos).mpr hkey
            rwa [mul_div_assoc] at h5
          have h6 : K * (Work.FTS.RegExportIface.ω α z θ / z)
              ≤ K * (z * Work.FTS.Regularity.Gamma α θ) :=
            mul_le_mul_of_nonneg_left (omega_div_z_le_z_mul_Gamma α z θ hzpos.le hθ) hK0
          calc |Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z θ|
              ≤ K * (Work.FTS.RegExportIface.ω α z θ / z) := h4
            _ ≤ K * (z * Work.FTS.Regularity.Gamma α θ) := h6
            _ ≤ |K| * z := by
                have hA : K * (z * Work.FTS.Regularity.Gamma α θ) ≤ K * z :=
                  mul_le_mul_of_nonneg_left
                    (by simpa using mul_le_mul_of_nonneg_left hΓ1 hzpos.le) hK0
                have hB : K * z ≤ |K| * z := mul_le_mul_of_nonneg_right (le_abs_self K) hzpos.le
                linarith

end Work.FTS_RegExport.RXT
