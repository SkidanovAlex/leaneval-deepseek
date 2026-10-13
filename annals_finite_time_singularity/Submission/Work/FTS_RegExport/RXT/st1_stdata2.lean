/-
# `Work.FTS_RegExport.RXT.st1_stdata2` — the second-order `z`-class datum of `St1Class`

`st1_quad2`: `|∂_z² g̃| ≤ Q₂` on `0 < z ≤ 2`, uniformly in `(θ,τ)`.

Since `D_z = z∂_z`, the expansion `D_z² = z∂_z + z²∂_z²` at a `C²` point turns the two weighted
bounds (`(2,0)` and `(1,0)`) into `z²|∂_z²g̃| ≤ 2Kω ≤ 2Kz²Γ`, i.e. `|∂_z²g̃| ≤ 2KΓ ≤ 2K`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS_RegExport.RXT.st1_prelim
import Submission.Work.FTS_RegExport.RXT.st1_fb_dz

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_RegExport.RXT

/-- The second `z`-derivative at the origin. -/
theorem st1_quad2 {α : ℝ} (hα : 0 < α) {g : Work.FTS.Galerkin.Fam} {S K : ℝ}
    (hmin : Work.FTS.StrongGlobal.RegPkgMin (Work.FTS.Regularity.pExp α) g) (hS : 0 < S)
    (hK0 : 0 ≤ K)
    (hw : ∀ k : Fin 6, ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed (Work.FTS.RegExportIface.RXT.idx k).1
        (Work.FTS.RegExportIface.RXT.idx k).2
        (Work.FTS.Galerkin.slice g τ) z θ| ≤ K * Work.FTS.RegExportIface.ω α z θ) :
    ∃ Q₂ : ℝ, 0 ≤ Q₂ ∧ ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ θ ∈ Work.Spaces.Iθ,
      ∀ z : ℝ, 0 < z → z ≤ 2 →
        |Work.Spaces.pz (Work.Spaces.pz (Work.FTS.Regularity.gSlice (GG α g) τ)) z θ| ≤ Q₂ := by
  have hv : ∀ τ : ℝ, 0 ≤ τ → ∀ z : ℝ, 0 ≤ z → g z 0 τ = 0 ∧ g z (π / 2) τ = 0 :=
    fun τ hτ z hz => hmin.vanish τ hτ z hz
  refine ⟨2 * |K|, by positivity, ?_⟩
  intro τ hτ θ hθ z hz hz2
  rcases eq_or_lt_of_le hθ.1 with hθ0 | hθpos
  · -- `θ = 0`: the slice of `g̃` vanishes identically at this angle
    subst hθ0
    have h1 : Work.Spaces.pz
        (Work.Spaces.pz (Work.FTS.Regularity.gSlice (GG α g) τ)) z 0 = 0 := by
      show deriv (fun z' => Work.Spaces.pz (Work.FTS.Regularity.gSlice (GG α g) τ) z' 0) z = 0
      have hev : (fun z' : ℝ => Work.Spaces.pz (Work.FTS.Regularity.gSlice (GG α g) τ) z' 0)
          =ᶠ[𝓝 z] (fun _ => (0:ℝ)) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact pz_GG_eq_zero_left α hτ.1 hz' hv
      rw [hev.deriv_eq, deriv_const]
    rw [h1, abs_zero]
    positivity
  · rcases eq_or_lt_of_le hθ.2 with hθπ | hθlt
    · -- `θ = π/2`
      subst hθπ
      have h1 : Work.Spaces.pz
          (Work.Spaces.pz (Work.FTS.Regularity.gSlice (GG α g) τ)) z (π / 2) = 0 := by
        show deriv (fun z' =>
            Work.Spaces.pz (Work.FTS.Regularity.gSlice (GG α g) τ) z' (π / 2)) z = 0
        have hev : (fun z' : ℝ =>
              Work.Spaces.pz (Work.FTS.Regularity.gSlice (GG α g) τ) z' (π / 2))
            =ᶠ[𝓝 z] (fun _ => (0:ℝ)) := by
          filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
          exact pz_GG_eq_zero_right α hτ.1 hz' hv
        rw [hev.deriv_eq, deriv_const]
      rw [h1, abs_zero]
      positivity
    · -- interior
      rw [pz_pz_GG_eq α hτ.1 hz hθ]
      have h1 := hw (1 : Fin 6) τ hτ z θ hz hθpos hθlt
      norm_num [Work.FTS.RegExportIface.RXT.idx] at h1
      have h2 := hw (3 : Fin 6) τ hτ z θ hz hθpos hθlt
      norm_num [Work.FTS.RegExportIface.RXT.idx] at h2
      have hΓ1 : Work.FTS.Regularity.Gamma α θ ≤ 1 :=
        Work.ConstructionInstance.Gamma_le_one hα.le hθ
      have hΓ0 : 0 ≤ Work.FTS.Regularity.Gamma α θ :=
        Work.ConstructionInstance.Gamma_nonneg hθ
      -- `C²` at the interior point, and the `D_z²`-expansion
      have hnb : Work.FTS.EllipticEst.Q0 ∈ 𝓝 (z, θ) :=
        (isOpen_Ioi.prod isOpen_Ioo).mem_nhds ⟨hz, hθpos, hθlt⟩
      have hct : ContDiffAt ℝ 2 (Function.uncurry (Work.FTS.Galerkin.slice g τ)) (z, θ) :=
        ((hmin.c4 τ hτ.1).contDiffAt hnb).of_le (by norm_num)
      have hexp : Work.Spaces.DzIter 2 (Work.FTS.Galerkin.slice g τ) z θ
          = z * Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z θ
            + z ^ 2 * Work.Spaces.pz (Work.Spaces.pz (Work.FTS.Galerkin.slice g τ)) z θ :=
        dziter_two_fb hct
      have hbz : |Work.Spaces.DzIter 2 (Work.FTS.Galerkin.slice g τ) z θ|
          ≤ K * (z ^ 2 * Work.FTS.Regularity.Gamma α θ) :=
        le_trans h2 (mul_le_mul_of_nonneg_left
          (omega_le_zsq_mul_Gamma α z θ hz.le hθ) hK0)
      have hbz1 : |z * Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z θ|
          ≤ K * (z ^ 2 * Work.FTS.Regularity.Gamma α θ) := by
        have h2' : |Work.Spaces.mixed 1 0 (Work.FTS.Galerkin.slice g τ) z θ|
            ≤ K * (z ^ 2 * Work.FTS.Regularity.Gamma α θ) :=
          le_trans h1 (mul_le_mul_of_nonneg_left
            (omega_le_zsq_mul_Gamma α z θ hz.le hθ) hK0)
        simpa only [show Work.Spaces.mixed 1 0 (Work.FTS.Galerkin.slice g τ)
              = fun z θ => z * Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z θ from rfl]
          using h2'
      have hb : z ^ 2 * |Work.Spaces.pz
            (Work.Spaces.pz (Work.FTS.Galerkin.slice g τ)) z θ| ≤ (2 * |K|) * z ^ 2 := by
        have h0 : z ^ 2 * |Work.Spaces.pz
              (Work.Spaces.pz (Work.FTS.Galerkin.slice g τ)) z θ|
            = |z ^ 2 * Work.Spaces.pz
                (Work.Spaces.pz (Work.FTS.Galerkin.slice g τ)) z θ| := by
          rw [abs_mul, abs_of_nonneg (sq_nonneg z)]
        rw [h0]
        have hsplit : z ^ 2 * Work.Spaces.pz
              (Work.Spaces.pz (Work.FTS.Galerkin.slice g τ)) z θ
            = Work.Spaces.DzIter 2 (Work.FTS.Galerkin.slice g τ) z θ
              - z * Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z θ := by
          rw [hexp]; ring
        rw [hsplit]
        calc |Work.Spaces.DzIter 2 (Work.FTS.Galerkin.slice g τ) z θ
              - z * Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z θ|
            ≤ |Work.Spaces.DzIter 2 (Work.FTS.Galerkin.slice g τ) z θ|
              + |z * Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z θ| := by
                simpa only [sub_eq_add_neg, abs_neg] using
                  abs_add_le (Work.Spaces.DzIter 2 (Work.FTS.Galerkin.slice g τ) z θ)
                    (-(z * Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z θ))
          _ ≤ K * (z ^ 2 * Work.FTS.Regularity.Gamma α θ)
              + K * (z ^ 2 * Work.FTS.Regularity.Gamma α θ) := add_le_add hbz hbz1
          _ = (2 * K) * (z ^ 2 * Work.FTS.Regularity.Gamma α θ) := by ring
          _ ≤ (2 * K) * z ^ 2 :=
              mul_le_mul_of_nonneg_left (by nlinarith [hΓ1, hΓ0, sq_nonneg z])
                (by linarith)
          _ ≤ (2 * |K|) * z ^ 2 :=
              mul_le_mul_of_nonneg_right (by linarith [le_abs_self K]) (sq_nonneg z)
      have hfin : |Work.Spaces.pz (Work.Spaces.pz (Work.FTS.Galerkin.slice g τ)) z θ|
          ≤ 2 * |K| := by
        have h1 : |Work.Spaces.pz (Work.Spaces.pz (Work.FTS.Galerkin.slice g τ)) z θ| * z ^ 2
            ≤ (2 * |K|) * z ^ 2 := by
          simpa only [mul_comm (z ^ 2)] using hb
        have h2 : |Work.Spaces.pz (Work.Spaces.pz (Work.FTS.Galerkin.slice g τ)) z θ|
            ≤ (2 * |K|) * z ^ 2 / z ^ 2 := (le_div_iff₀ (pow_pos hz 2)).mpr h1
        rwa [mul_div_assoc, div_self (ne_of_gt (pow_pos hz 2)), mul_one] at h2
      exact hfin

end Work.FTS_RegExport.RXT
