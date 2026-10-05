import Mathlib
import Submission.Work.RPB.Defs
import Submission.Work.RPB.B5.exists_eps_neg_of_deriv_pos
import Submission.Work.RPB.B5.chartJets_chartLev_slice
import Submission.Work.RPB.B5.component_mono
import Submission.Work.RPB.B5.chartLev_pi_div_four
import Submission.Work.RPB.B5.chord_pi_lower_bound

/-!
# B5: the range of the level inversion `ρh` on the negative side (`κ`-parametrised)

`Work.RPB.B5.rho_range_kappa` is the `κ`-parametrised version of `Work.RPB.B5.noL_range`:
the level inversion `ρh` of the chart `W` is only known on the *arbitrary* interval
`(-κ, κ)` (`κ > 0`), the level equation `K₀ (W τ t (ρh τ t σ)) + 1 = -σ` and the range
condition `ρh τ t σ ∈ (-ρ₀, ρ₀)` holding there, and the uniform interval of negative levels
produced is required to lie inside that interval, i.e. `ε ≤ κ`.

The argument is the same connected-component argument as in `noL_range` (which is the same
statement with `κ = 1`); only the constant `1` is replaced by `κ` throughout, and the
conclusion is `ε ≤ κ` instead of `ε < 1`:

write `F τ t ρ = K₀ (W τ t ρ) + 1` for the level function and fix `(τ,t)`.  The chart lemma
`Work.RPB.B5.chartJets_chartLev_slice` gives `F τ t 0 = 0` and `∂_ρ F τ t 0 = ‖c_τ'(t)‖² > 0`.
Let `C` be the connected component of `0` in `U = {ρ ∈ (-ρ₀,ρ₀) : ∂_ρ F τ t ρ ≠ 0}`.
Differentiating `F τ t (ρh τ t σ) = -σ` in `σ` (chain rule) gives
`∂_ρ F τ t (ρh τ t σ) · ∂_σ ρh τ t σ = -1`, so `ρh τ t ·` maps the interval `(-κ,κ)` (which is
connected and contains `0`) into `U`, hence into `C`; and `Work.RPB.B5.component_mono` says that
`F τ t` is *strictly increasing* on `C`.  Hence

* for `σ < 0`, `F τ t (ρh τ t σ) = -σ > 0 = F τ t 0` with both points in `C`, so
  `ρh τ t σ > 0`;
* if additionally `ρh τ t σ ≥ π²/4`, then `π²/4` lies between `0` and `ρh τ t σ`, hence in `C`,
  so `-σ = F τ t (ρh τ t σ) ≥ F τ t (π²/4) = ‖c_τ(t+π/2) - c_τ(t-π/2)‖²/4`, and the right-hand
  side is bounded below by the *uniform* constant `μ²/4 > 0` of
  `Work.RPB.B5.chord_pi_lower_bound` (`μ` is the infimum of the length of the `π/2`-chord).
  Thus `σ ≤ -μ²/4`, which is impossible as soon as `-σ < min κ (min (1/2) (μ²/4))`.

This gives the uniform `ε = min κ (min (1/2) (μ²/4)) ≤ κ`, and the proof is uniform in `(τ,t)`
although `W` and `ρh` are not assumed periodic in `t`.
-/

open RectangularPegProblem
open Manifold Complex Real
open scoped ContDiff Topology
open Filter

set_option autoImplicit false

-- The binder `ha` is part of the requested (fixed) statement and is not needed by this proof;
-- silence the warning without touching the statement.
set_option linter.unusedVariables false

noncomputable section

namespace Work.RPB.B5

theorem rho_range_kappa (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a)
    (ρ₀ : ℝ) (hρ₀ : 0 < ρ₀)
    (W : ℝ → ℝ → ℝ → Work.RPV.PS) (ρh : ℝ → ℝ → ℝ → ℝ)
    {κ : ℝ} (hκ : 0 < κ)
    (hW : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀))
    (hWchord : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ r ∈ Set.Ioc (0 : ℝ) (Real.pi / 2),
      W τ t (r ^ 2) = Work.RPB.chordSurf CI.c a τ t r)
    (hρh : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => ρh z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ))
    (hρh0 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ρh τ t 0 = 0)
    (hρhv : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      ρh τ t σ ∈ Set.Ioo (-ρ₀) ρ₀)
    (hρhl : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      Work.RPV.K0 (W τ t (ρh τ t σ)) + 1 = -σ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ κ ∧ ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
      ∀ σ ∈ Set.Ioo (-ε) 0, ρh τ t σ ∈ Set.Ioo (0 : ℝ) (Real.pi ^ 2 / 4) := by
  -- the uniform lower bound `μ` for the `π/2`-chord
  obtain ⟨μ, hμpos, hμ⟩ := chord_pi_lower_bound CI
  have hεpos : 0 < min κ (min (1/2) (μ^2/4)) := lt_min hκ (lt_min (by norm_num) (by positivity))
  have hεleκ : min κ (min (1/2) (μ^2/4)) ≤ κ := min_le_left _ _
  refine ⟨min κ (min (1/2) (μ^2/4)), hεpos, hεleκ, ?_⟩
  intro τ hτ t σ hσ
  -- `σ` also lies in the interval where the hypotheses of `hρh`/`hρhl` hold
  have hσIoo : σ ∈ Set.Ioo (-κ) κ := by
    refine ⟨?_, by linarith [hσ.2, hκ]⟩
    linarith [hσ.1, hεleκ]
  -- the `ρ`-slice of `W` at this `(τ,t)` is `C¹²`
  have hWslice : ContDiffOn ℝ 12 (fun ρ : ℝ => W τ t ρ) (Set.Ioo (-ρ₀) ρ₀) :=
    (hW.comp (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)).contDiffOn
      (fun ρ hρ => ⟨hτ, Set.mem_univ _, hρ⟩)).congr (fun _ _ => rfl)
  -- the level function and the level inverse of this slice
  let F : ℝ → ℝ := fun ρ => Work.RPV.K0 (W τ t ρ) + 1
  let g : ℝ → ℝ := fun u => ρh τ t u
  have hFsm : ContDiffOn ℝ 12 F (Set.Ioo (-ρ₀) ρ₀) := by
    have hK : ContDiff ℝ 12 (fun x : Work.RPV.PS => Work.RPV.K0 x + 1) := by
      simp only [Work.RPV.K0]; fun_prop
    exact hK.comp_contDiffOn hWslice
  have hFsm1 : ContDiffOn ℝ 1 F (Set.Ioo (-ρ₀) ρ₀) := hFsm.of_le (by norm_num)
  have hgsm : ContDiffOn ℝ 12 g (Set.Ioo (-κ) κ) :=
    (hρh.comp (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)).contDiffOn
      (fun σ hσ => ⟨hτ, Set.mem_univ _, hσ⟩)).congr (fun _ _ => rfl)
  -- the level function vanishes at `0` and grows there
  have hchart := chartJets_chartLev_slice CI a ρ₀ hρ₀ W
    (hW.of_le (by norm_num)) hWchord τ hτ t
  have hF0 : F 0 = 0 := hchart.1
  have hFd0 : 0 < deriv F 0 := by
    rw [hchart.2.1]
    exact pow_pos (norm_pos_iff.mpr (CI.imm τ hτ t)) 2
  have hg0 : g 0 = 0 := hρh0 τ hτ t
  have hlev : ∀ u ∈ Set.Ioo (-κ) κ, F (g u) = -u := fun u hu => hρhl τ hτ t u hu
  have hgmem : ∀ u ∈ Set.Ioo (-κ) κ, g u ∈ Set.Ioo (-ρ₀) ρ₀ := fun u hu => hρhv τ hτ t u hu
  -- the component of `0` in `{ρ ∈ (-ρ₀,ρ₀) : F' ρ ≠ 0}`
  let U : Set ℝ := {ρ : ℝ | ρ ∈ Set.Ioo (-ρ₀) ρ₀ ∧ deriv F ρ ≠ 0}
  let C : Set ℝ := connectedComponentIn U 0
  have h0U : (0:ℝ) ∈ U := ⟨⟨by linarith, hρ₀⟩, ne_of_gt hFd0⟩
  have h0C : (0:ℝ) ∈ C := mem_connectedComponentIn h0U
  have hCpre : IsPreconnected C := isPreconnected_connectedComponentIn
  have hCord : C.OrdConnected := hCpre.ordConnected
  -- the chain rule: `F'` does not vanish at any `g u`
  have hchain : ∀ u ∈ Set.Ioo (-κ) κ, deriv F (g u) ≠ 0 := by
    intro u hu
    have hd1 : deriv (fun v : ℝ => F (g v)) u = -1 := by
      have heq : (fun v : ℝ => F (g v)) =ᶠ[𝓝 u] (fun v : ℝ => -v) := by
        filter_upwards [isOpen_Ioo.mem_nhds hu] with v hv
        exact hlev v hv
      rw [heq.deriv_eq]
      simp
    have hFdiffAt : DifferentiableAt ℝ F (g u) :=
      hFsm1.differentiableOn (by norm_num) (g u) (hgmem u hu) |>.differentiableAt
        (isOpen_Ioo.mem_nhds (hgmem u hu))
    have hgdiffAt : DifferentiableAt ℝ g u :=
      hgsm.differentiableOn (by norm_num) u hu |>.differentiableAt (isOpen_Ioo.mem_nhds hu)
    have hd2 : deriv (fun v : ℝ => F (g v)) u = deriv F (g u) * deriv g u :=
      deriv_comp u hFdiffAt hgdiffAt
    intro h0
    rw [hd2, h0, zero_mul] at hd1
    norm_num at hd1
  -- the whole image of `g` lies in the component `C`
  have hgC : ∀ u ∈ Set.Ioo (-κ) κ, g u ∈ C := by
    have himg : IsPreconnected (g '' Set.Ioo (-κ) κ) :=
      (isPreconnected_Ioo (a := (-κ)) (b := κ)).image g hgsm.continuousOn
    have hsub : g '' Set.Ioo (-κ) κ ⊆ U := by
      rintro _ ⟨u, hu, rfl⟩
      exact ⟨hgmem u hu, hchain u hu⟩
    have hsubC : g '' Set.Ioo (-κ) κ ⊆ C :=
      himg.subset_connectedComponentIn (x := 0) ⟨0, ⟨by linarith, hκ⟩, by rw [hg0]⟩ hsub
    intro u hu
    exact hsubC (Set.mem_image_of_mem g hu)
  -- `F` is strictly increasing on the component
  obtain ⟨_, hCmono⟩ := component_mono (f := F) (a := -ρ₀) (b := ρ₀)
    (by linarith) hρ₀ hFsm1 hFd0
  -- `g σ > 0`
  have hgpos : 0 < g σ := by
    have hlt : F 0 < F (g σ) := by
      rw [hF0, hlev σ hσIoo]
      linarith [hσ.2]
    have hle : 0 ≤ g σ := (hCmono.le_iff_le h0C (hgC σ hσIoo)).mp hlt.le
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exfalso
      have hz : F (g σ) = 0 := by rw [← h, hF0]
      rw [hlev σ hσIoo] at hz
      linarith [hσ.2]
  -- `g σ < π²/4`
  have hgupper : g σ < Real.pi^2/4 := by
    by_contra hcon
    push Not at hcon
    have hpiC : Real.pi^2/4 ∈ C := by
      refine hCord.out (x := 0) (y := g σ) h0C (hgC σ hσIoo) ?_
      rw [Set.mem_Icc]
      exact ⟨by positivity, hcon⟩
    have hle : F (Real.pi^2/4) ≤ F (g σ) := (hCmono.le_iff_le hpiC (hgC σ hσIoo)).mpr hcon
    rw [hlev σ hσIoo] at hle
    have hFpi : F (Real.pi^2/4) = ‖CI.c τ (t + Real.pi/2) - CI.c τ (t - Real.pi/2)‖^2/4 :=
      chartLev_pi_div_four CI a W hWchord τ hτ t
    rw [hFpi] at hle
    have hμle : μ^2/4 ≤ ‖CI.c τ (t + Real.pi/2) - CI.c τ (t - Real.pi/2)‖^2/4 := by
      have h1 := hμ τ hτ t
      nlinarith [hμpos, norm_nonneg (CI.c τ (t + Real.pi/2) - CI.c τ (t - Real.pi/2))]
    have hσle : σ ≤ -(μ^2/4) := by linarith
    have h2 : -(min κ (min (1/2) (μ^2/4))) < σ := hσ.1
    have h3 : min κ (min (1/2) (μ^2/4)) ≤ μ^2/4 := le_trans (min_le_right _ _) (min_le_right _ _)
    linarith
  exact ⟨hgpos, hgupper⟩

end Work.RPB.B5
