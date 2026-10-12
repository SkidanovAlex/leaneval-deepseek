import ChallengeDeps
import Submission.ShellAssemblyChild
import Submission.ShellSplitChild
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Shell formula for the Newton potential of a radial function (Layer 3)

For a **radial** integrable function `g : ℝ³ → ℝ` the Newton potential
`N(x) := ∫_y g(y)·‖x−y‖⁻¹ dy` admits the closed radial form (shell theorem)

    N(x) = 4π · ∫_{s>0} s²·(radialProfile g s) / max(‖x‖, s) ds
         = 4π · [ (1/‖x‖)·∫_{s≤‖x‖} s²·gprof(s)ds  +  ∫_{s>‖x‖} s·gprof(s)ds ]

(the mean of `1/‖x−y‖` over the sphere `‖y‖=s` is `1/max(‖x‖,s)`; the surface
integral of a radial function is `4πs²·gprof(s)`).

The hard analysis is in `Submission.ShellMean` and its satellites:
`shell_axis_reduce` reduces the centre to the axis `shellE0`;
`shell_potential_axis` (in `Submission.ShellAssemblyChild`) proves the axis
formula by the polar decomposition and the spherical mean identity
`shell_mean_e0`; `shell_max_split` (in `Submission.ShellSplitChild`) is the
one-dimensional domain split.
-/

noncomputable section

open _root_.BoseGases
set_option autoImplicit false

namespace Submission.BoseGases

open Filter Metric MeasureTheory Laplacian
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **Shell formula** (single-integral form).  For a radial integrable `g`
with `g y = 0` for all `‖y‖ ≥ R` and any `x ≠ 0`,
`∫_y g(y)·‖x−y‖⁻¹ dy = 4π·∫_{s>0} s²·(radialProfile g s)/max ‖x‖ s ds`. -/
theorem newton_potential_shell_integral {g : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R)
    (hgrad : IsRadial g) (hgsupp : ∀ y : ℝ³, R ≤ ‖y‖ → g y = 0)
    (hg : MeasureTheory.Integrable g) :
    ∀ x : ℝ³, x ≠ 0 →
      (∫ y : ℝ³, g y * (‖x - y‖ : ℝ)⁻¹) =
        4 * π * (∫ s in Set.Ioi (0 : ℝ), (s ^ 2 * radialProfile g s) / max ‖x‖ s) := by
  intro x hx
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  calc
    (∫ y : ℝ³, g y * (‖x - y‖ : ℝ)⁻¹)
        = ∫ y : ℝ³, g y * (‖(‖x‖ • shellE0) - y‖ : ℝ)⁻¹ := by
            exact shell_axis_reduce hgrad hx
    _ = 4 * π * (∫ s in Set.Ioi (0 : ℝ), (s ^ 2 * radialProfile g s) / max ‖x‖ s) := by
            exact shell_potential_axis hR hgrad hgsupp hg hr

/-- **Shell formula** (split form).  With `r := ‖x‖ ≠ 0`,
`∫_y g(y)·‖x−y‖⁻¹ dy = 4π·[(1/r)·∫_{s≤r} s²·gprof(s)ds + ∫_{s>r} s·gprof(s)ds]`,
where `gprof := radialProfile g`.  (The tail `∫_{s>r}` is over `s ∈ (r, R)`
by the support assumption.) -/
theorem newton_potential_shell_split {g : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R)
    (hgrad : IsRadial g) (hgsupp : ∀ y : ℝ³, R ≤ ‖y‖ → g y = 0)
    (hg : MeasureTheory.Integrable g) :
    ∀ x : ℝ³, x ≠ 0 →
      (∫ y : ℝ³, g y * (‖x - y‖ : ℝ)⁻¹) =
        4 * π * ((1 / ‖x‖) * (∫ s in Set.Ioc (0 : ℝ) ‖x‖, s ^ 2 * radialProfile g s) +
          (∫ s in Set.Ioi ‖x‖, s * radialProfile g s)) := by
  intro x hx
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hrad : IntegrableOn (fun s : ℝ => s ^ 2 * |radialProfile g s|) (Set.Ioi (0 : ℝ)) volume :=
    shell_profile_integrable hg hgrad
  have hfae : AEStronglyMeasurable (fun s : ℝ => radialProfile g s)
      (volume.restrict (Set.Ioi (0 : ℝ))) := shell_gprof_ae_strong hg hgrad
  calc
    (∫ y : ℝ³, g y * (‖x - y‖ : ℝ)⁻¹)
        = 4 * π * (∫ s in Set.Ioi (0 : ℝ), (s ^ 2 * radialProfile g s) / max ‖x‖ s) := by
            exact newton_potential_shell_integral hR hgrad hgsupp hg x hx
    _ = 4 * π * ((1 / ‖x‖) * (∫ s in Set.Ioc (0 : ℝ) ‖x‖, s ^ 2 * radialProfile g s) +
          (∫ s in Set.Ioi ‖x‖, s * radialProfile g s)) := by
          congr 1
          exact shell_max_split hr hrad hfae

end Submission.BoseGases
