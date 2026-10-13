import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_RegExport.THL.Defs
import Submission.Work.FTS_RegExport.RXT.st1_angle
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.FinCalc

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.THL.L.DthG_theta_mod` — the `θ`-modulus of `D_θ g̃` (leaf **B2** of O1)

The family `DthG α g z θ τ = D_θ (gS α (tauExt g)) (z,θ,τ) = sin(2θ)·∂_θ (gS α (tauExt g))` is
`α`-Hölder in `θ`, uniformly on `τ ∈ [0,S]` and on `z ≥ 0`, with a constant depending only on the
six weighted slot bounds `WSys α S K g`.

Route (the sibling of `RXT.st1_hhθ`, one order up).

* On `z > 0, θ ∈ (0,π/2), τ ≥ 0` the sanitiser and the right-Taylor extension are invisible
  (`gS α h z θ τ = h z θ τ` for `0 < z`, `θ ∈ Iθ`; `tauExt g = g` for `τ ≥ 0`), so
  `DthG α g z θ τ = mixed 0 1 (slice g τ) z θ` (the `(0,1)`-slot of `WSys`).
* The engine `RXT.theta_modulus_uniform_fb` only needs, for the `θ`-slice
  `u = fun x => DthG α g z x τ`,
  * `|u x| ≤ K·Γ(θ)` on `Iθ` — the `(0,1)`-slot plus `ω ≤ Γ`, and `u = 0` at both endpoints
    because of the factor `sin 2θ`;
  * `|u'| ≤ K·Γ/sin(2θ)` on `(0,π/2)` with `u' x = mixed 0 2 (slice g τ) z x / sin(2x)` — the
    `(0,2)`-slot plus `ω ≤ Γ`; this is the only place where two slots (`k = 2, 5` of `idx`) are
    consumed.
* The `HasDerivAt` of `u` is the `θ`-slice derivative of the mixed jet `mixed 0 1 (slice g τ)`
  (`RXT.hasDerivAt_slice_snd_of_contDiffOn` + `E2pkg.contDiffOn_uncurry_mixed_le`, at order `4`
  from `RegPkgMin.c4`), moved over to `gS α (tauExt g)` by eventual equality, and its value
  `pth (mixed 0 1 …)` rewritten as `mixed 0 2 … / sin 2θ` (definitional, `mixed 0 2 = D_θ(mixed 0 1)`).
* At `z = 0` everything vanishes (`gS` is `0` for `z ≤ 0`), so the bound is trivial.
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.THL.L

set_option autoImplicit false

/-- The sanitiser is invisible on `z > 0`, `θ ∈ Iθ`. -/
private lemma gS_apply_of_mem (α : ℝ) {h : Work.FTS.Galerkin.Fam} {z θ τ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.FTS.FinalV2.gS α h z θ τ = h z θ τ := by
  simp [Work.FTS.FinalV2.gS, hz, hθ.1, hθ.2]

/-- **The `(0,1)`-slot**: on the open quadrant at a nonnegative fake time, the `O1` family
`DthG` is the mixed jet `D_θ (slice g τ)`. -/
private lemma DthG_eq_mixed {α : ℝ} (g : Work.FTS.Galerkin.Fam) {τ z θ : ℝ} (hτ : 0 ≤ τ)
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0:ℝ) (π / 2)) :
    Work.FTS_RegExport.THL.DthG α g z θ τ
      = Work.Spaces.mixed 0 1 (Work.FTS.Galerkin.slice g τ) z θ := by
  have hev : (fun θ' => Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z θ' τ)
      =ᶠ[𝓝 θ] (fun θ' => Work.FTS.Galerkin.slice g τ z θ') := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
    rw [gS_apply_of_mem α hz ⟨hθ'.1.le, hθ'.2.le⟩,
      Work.FTS.FinalV2.tauExt_of_nonneg g hτ]
    rfl
  change Real.sin (2 * θ)
      * deriv (fun θ' => Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z θ' τ) θ
    = Real.sin (2 * θ) * deriv (fun θ' => Work.FTS.Galerkin.slice g τ z θ') θ
  rw [hev.deriv_eq]

/-- The family vanishes on the left angular edge `θ = 0` (the factor `sin 2θ`). -/
private lemma DthG_zero_theta {α : ℝ} (g : Work.FTS.Galerkin.Fam) (z τ : ℝ) :
    Work.FTS_RegExport.THL.DthG α g z 0 τ = 0 := by
  change Real.sin (2 * (0:ℝ))
      * deriv (fun θ' => Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z θ' τ) 0 = 0
  rw [show (2:ℝ) * 0 = 0 by ring, Real.sin_zero, zero_mul]

/-- The family vanishes on the right angular edge `θ = π/2`. -/
private lemma DthG_zero_pi_div_two {α : ℝ} (g : Work.FTS.Galerkin.Fam) (z τ : ℝ) :
    Work.FTS_RegExport.THL.DthG α g z (π / 2) τ = 0 := by
  change Real.sin (2 * (π / 2))
      * deriv (fun θ' => Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z θ' τ) (π / 2) = 0
  rw [show (2:ℝ) * (π / 2) = π by ring, Real.sin_pi, zero_mul]

/-- The family vanishes for `z = 0` (the sanitiser is `0` there). -/
private lemma DthG_zero_rad {α : ℝ} (g : Work.FTS.Galerkin.Fam) (θ τ : ℝ) :
    Work.FTS_RegExport.THL.DthG α g 0 θ τ = 0 := by
  have hfun : (fun θ' : ℝ => Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) 0 θ' τ)
      = fun _ => (0:ℝ) := by
    funext θ'; simp only [Work.FTS.FinalV2.gS, lt_irrefl, ite_false]
  change Real.sin (2 * θ)
      * deriv (fun θ' => Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) 0 θ' τ) θ = 0
  rw [hfun, deriv_const, mul_zero]

theorem DthG_theta_mod {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) {g : Work.FTS.Galerkin.Fam} {S K : ℝ}
    (hmin : Work.FTS.StrongGlobal.RegPkgMin (Work.FTS.Regularity.pExp α) g) (hS : 0 < S) (hK0 : 0 ≤ K)
    (hw : Work.FTS_RegExport.THL.WSys α S K g) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z : ℝ, 0 ≤ z →
      ∀ θ ∈ Work.Spaces.Iθ, ∀ θ' ∈ Work.Spaces.Iθ,
        |Work.FTS_RegExport.THL.DthG α g z θ τ - Work.FTS_RegExport.THL.DthG α g z θ' τ|
          ≤ L * |θ - θ'| ^ α := by
  obtain ⟨L, hL0, hL⟩ := Work.FTS_RegExport.RXT.theta_modulus_uniform_fb
    (α := α) (C := K) (K := K) hα hα13 hK0 hK0
  refine ⟨L, hL0, ?_⟩
  intro τ hτ z hz θ hθ θ' hθ'
  rcases eq_or_lt_of_le hz with hz0 | hzpos
  · -- `z = 0`: both values vanish
    subst hz0
    rw [DthG_zero_rad g θ τ, DthG_zero_rad g θ' τ, sub_zero, abs_zero]
    exact mul_nonneg hL0 (Real.rpow_nonneg (abs_nonneg _) _)
  · -- `z > 0`: the uniform `θ`-modulus engine on the slice `x ↦ DthG α g z x τ`
    refine hL (u := fun x => Work.FTS_RegExport.THL.DthG α g z x τ)
      (u' := fun x => Work.Spaces.mixed 0 2 (Work.FTS.Galerkin.slice g τ) z x / Real.sin (2 * x))
      ?_ ?_ ?_ θ hθ θ' hθ'
    · -- the derivative: `θ`-slice derivative of the mixed jet `D_θ (slice g τ)`
      intro x hx
      have hsin : Real.sin (2 * x) ≠ 0 :=
        ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2]))
      have hW1 : ContDiffOn ℝ 1
          (Function.uncurry (Work.Spaces.mixed 0 1 (Work.FTS.Galerkin.slice g τ)))
          Work.FTS.EllipticEst.Q0 :=
        Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_uncurry_mixed_le
          Work.FTS.EllipticEst.isOpen_Q0 1 0 1 (by norm_num) (hmin.c4 τ hτ.1)
      have hbase := Work.FTS_RegExport.RXT.hasDerivAt_slice_snd_of_contDiffOn
        Work.FTS.EllipticEst.isOpen_Q0 hW1 (z := z) (θ := x) ⟨hzpos, hx⟩
      have hval : Work.Spaces.pth (Work.Spaces.mixed 0 1 (Work.FTS.Galerkin.slice g τ)) z x
          = Work.Spaces.mixed 0 2 (Work.FTS.Galerkin.slice g τ) z x / Real.sin (2 * x) := by
        rw [eq_div_iff hsin, mul_comm]
        rfl
      rw [hval] at hbase
      have hev : (fun x' => Work.FTS_RegExport.THL.DthG α g z x' τ)
          =ᶠ[𝓝 x] (fun θ' => Work.Spaces.mixed 0 1 (Work.FTS.Galerkin.slice g τ) z θ') := by
        filter_upwards [isOpen_Ioo.mem_nhds hx] with θ' hθ'
        exact DthG_eq_mixed g hτ.1 hzpos hθ'
      exact hbase.congr_of_eventuallyEq hev
    · -- the derivative bound `|u'| ≤ K·Γ/sin 2θ` from the `(0,2)`-slot
      intro x hx
      have hsin : 0 < Real.sin (2 * x) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2])
      have h := hw 5 τ hτ z x hzpos hx.1 hx.2
      norm_num [Work.FTS.RegExportIface.RXT.idx] at h
      have hKΓ : |Work.Spaces.mixed 0 2 (Work.FTS.Galerkin.slice g τ) z x|
          ≤ K * Work.FTS.Regularity.Gamma α x :=
        le_trans h (mul_le_mul_of_nonneg_left
          (Work.FTS_RegExport.RXT.omega_le_Gamma α z x hzpos.le ⟨hx.1.le, hx.2.le⟩) hK0)
      rw [abs_div, abs_of_pos hsin, ← mul_div_assoc]
      exact div_le_div_of_nonneg_right hKΓ hsin.le
    · -- the value bound `|u| ≤ K·Γ` on the closed interval
      intro x hx
      rcases eq_or_lt_of_le hx.1 with hx0 | hxpos
      · subst hx0
        rw [DthG_zero_theta g z τ, Work.FTS_RegExport.RXT.Gamma_zero_left hα, mul_zero, abs_zero]
      · rcases eq_or_lt_of_le hx.2 with hxπ | hxlt
        · subst hxπ
          rw [DthG_zero_pi_div_two g z τ, Work.FTS_RegExport.RXT.Gamma_zero_right hα, mul_zero,
            abs_zero]
        · -- the interior: the `(0,1)`-slot and `ω ≤ Γ`
          rw [DthG_eq_mixed g hτ.1 hzpos ⟨hxpos, hxlt⟩]
          have h := hw 2 τ hτ z x hzpos hxpos hxlt
          norm_num [Work.FTS.RegExportIface.RXT.idx] at h
          exact le_trans h (mul_le_mul_of_nonneg_left
            (Work.FTS_RegExport.RXT.omega_le_Gamma α z x hzpos.le hx) hK0)

end Work.FTS_RegExport.THL.L
