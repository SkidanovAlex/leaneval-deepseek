import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.RegPkgGal.Defs
import Submission.Work.FTS.RegPkgGal.R1
import Submission.Work.FTS.RegPkgGal.R1b.extG_cont

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Filter Topology MeasureTheory
open scoped Topology Real

namespace Work.FTS.RegPkgGal.Der

set_option autoImplicit false

/-! ## Slice smoothness of the extension `g̃`

The hypothesis `hcont` of `htaumodp` gives joint `C¹` smoothness of `(z,τ) ↦ g̃ z θ τ` on the
open rectangle `(-1,S+1) × (-1,S+1)`, at every fixed angle `θ ∈ Iθ`.  The two `HasDerivAt`
facts below are its one-variable slices; the `τ`-slice is the one that carries the equation
`∂_τg̃ = R`. -/

lemma contDiffOn_extG_tauSlice {g : Work.FTS.RegPkgGal.Fam} {S θ z : ℝ}
    (hcont : ∀ θ ∈ Work.Spaces.Iθ,
      ContDiffOn ℝ 1 (fun q : ℝ × ℝ => Work.FTS.RegPkgGal.extG g q.1 θ q.2)
        (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1)))
    (hθ : θ ∈ Work.Spaces.Iθ) (hz : z ∈ Set.Ioi (-1)) :
    ContDiffOn ℝ 1 (fun σ : ℝ => Work.FTS.RegPkgGal.extG g z θ σ)
      (Set.Ioo (-1) (S + 1)) := by
  have hmap : ContDiffOn ℝ 1 (fun σ : ℝ => (z, σ)) (Set.Ioo (-1) (S + 1)) := by fun_prop
  exact (hcont θ hθ).comp hmap (fun σ hσ => ⟨hz, hσ⟩)

lemma contDiffOn_extG_zSlice {g : Work.FTS.RegPkgGal.Fam} {S θ τ : ℝ}
    (hcont : ∀ θ ∈ Work.Spaces.Iθ,
      ContDiffOn ℝ 1 (fun q : ℝ × ℝ => Work.FTS.RegPkgGal.extG g q.1 θ q.2)
        (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1)))
    (hθ : θ ∈ Work.Spaces.Iθ) (hτ : τ ∈ Set.Ioo (-1) (S + 1)) :
    ContDiffOn ℝ 1 (fun ζ : ℝ => Work.FTS.RegPkgGal.extG g ζ θ τ) (Set.Ioi (-1)) := by
  have hmap : ContDiffOn ℝ 1 (fun ζ : ℝ => (ζ, τ)) (Set.Ioi (-1)) := by fun_prop
  exact (hcont θ hθ).comp hmap (fun ζ hζ => ⟨hζ, hτ⟩)

/-- The `τ`-slice of `g̃` at height `z > 0` has derivative `R z θ ·` (the equation `hid`). -/
lemma hasDerivAt_extG_tau {g : Work.FTS.RegPkgGal.Fam} {R : ℝ → ℝ → ℝ → ℝ} {S θ z x : ℝ}
    (hcont : ∀ θ ∈ Work.Spaces.Iθ,
      ContDiffOn ℝ 1 (fun q : ℝ × ℝ => Work.FTS.RegPkgGal.extG g q.1 θ q.2)
        (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1)))
    (hid : ∀ z θ τ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → τ ∈ Set.Icc 0 S →
      deriv (fun s => Work.FTS.RegPkgGal.extG g z θ s) τ = R z θ τ)
    (hθ : θ ∈ Work.Spaces.Iθ) (hz : 0 < z) (hx : x ∈ Set.Icc 0 S) :
    HasDerivAt (fun σ => Work.FTS.RegPkgGal.extG g z θ σ) (R z θ x) x := by
  have hz' : (-1 : ℝ) < z := by linarith
  have hcd := contDiffOn_extG_tauSlice hcont hθ hz'
  have hxmem : x ∈ Set.Ioo (-1) (S + 1) := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hca : ContDiffAt ℝ 1 (fun σ => Work.FTS.RegPkgGal.extG g z θ σ) x :=
    hcd.contDiffAt (isOpen_Ioo.mem_nhds hxmem)
  have hd := hca.differentiableAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have hh := hd.hasDerivAt
  rwa [hid z θ x (le_of_lt hz) hθ hx] at hh

/-- The `z`-slice of `g̃` at time `τ` is differentiable everywhere on `z > -1`. -/
lemma hasDerivAt_extG_z {g : Work.FTS.RegPkgGal.Fam} {S θ z τ : ℝ}
    (hcont : ∀ θ ∈ Work.Spaces.Iθ,
      ContDiffOn ℝ 1 (fun q : ℝ × ℝ => Work.FTS.RegPkgGal.extG g q.1 θ q.2)
        (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1)))
    (hθ : θ ∈ Work.Spaces.Iθ) (hτ : τ ∈ Set.Ioo (-1) (S + 1)) (hz : z ∈ Set.Ioi (-1)) :
    HasDerivAt (fun ζ => Work.FTS.RegPkgGal.extG g ζ θ τ)
      (Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ) z θ) z := by
  have hcd := contDiffOn_extG_zSlice hcont hθ hτ
  have hca : ContDiffAt ℝ 1 (fun ζ => Work.FTS.RegPkgGal.extG g ζ θ τ) z :=
    hcd.contDiffAt (isOpen_Ioi.mem_nhds hz)
  have hd := hca.differentiableAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  simpa only [Work.Spaces.pz] using hd.hasDerivAt

/-! ## The two mean-value steps -/

/-- The right-hand side `R` is `z`-Lipschitz with constant `N1` on the open half-line. -/
lemma R_z_mvt {R : ℝ → ℝ → ℝ → ℝ} {S N1 : ℝ}
    (hRHz : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0 : ℝ),
      ∃ d : ℝ, HasDerivAt (fun z' => R z' θ τ) d z ∧ |d| ≤ N1)
    {θ σ z z' : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) (hσ : σ ∈ Set.Icc 0 S)
    (hz : 0 < z) (hz' : 0 < z') :
    |R z θ σ - R z' θ σ| ≤ N1 * |z - z'| := by
  have hdiff : ∀ x ∈ Set.Ioi (0 : ℝ), DifferentiableAt ℝ (fun ζ => R ζ θ σ) x :=
    fun x hx => ((hRHz σ hσ θ hθ x hx).choose_spec.1).differentiableAt
  have hbnd : ∀ x ∈ Set.Ioi (0 : ℝ), ‖deriv (fun ζ => R ζ θ σ) x‖ ≤ N1 := by
    intro x hx
    obtain ⟨d, hd, hdle⟩ := hRHz σ hσ θ hθ x hx
    rw [hd.deriv, Real.norm_eq_abs]
    exact hdle
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.Ioi (0 : ℝ)) (x := z) (y := z')
    hdiff hbnd (convex_Ioi (0 : ℝ)) hz hz'
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_sub_comm (R z' θ σ) (R z θ σ),
    abs_sub_comm z' z] at h
  exact h

/-- The key mean-value step in the *fake time* variable: the `τ`-difference of `g̃` is itself
`z`-Lipschitz, with the product constant `N1·|z-z'|·|τ-τ'|`. -/
lemma extG_tau_diff_mvt {g : Work.FTS.RegPkgGal.Fam} {R : ℝ → ℝ → ℝ → ℝ} {S N1 θ z z' τ τ' : ℝ}
    (hcont : ∀ θ ∈ Work.Spaces.Iθ,
      ContDiffOn ℝ 1 (fun q : ℝ × ℝ => Work.FTS.RegPkgGal.extG g q.1 θ q.2)
        (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1)))
    (hid : ∀ z θ τ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → τ ∈ Set.Icc 0 S →
      deriv (fun s => Work.FTS.RegPkgGal.extG g z θ s) τ = R z θ τ)
    (hRHz : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0 : ℝ),
      ∃ d : ℝ, HasDerivAt (fun z' => R z' θ τ) d z ∧ |d| ≤ N1)
    (hθ : θ ∈ Work.Spaces.Iθ) (hz : 0 < z) (hz' : 0 < z')
    (hτ : τ ∈ Set.Icc 0 S) (hτ' : τ' ∈ Set.Icc 0 S) :
    |(Work.FTS.RegPkgGal.extG g z θ τ - Work.FTS.RegPkgGal.extG g z θ τ')
        - (Work.FTS.RegPkgGal.extG g z' θ τ - Work.FTS.RegPkgGal.extG g z' θ τ')|
      ≤ N1 * |z - z'| * |τ - τ'| := by
  have hderiv : ∀ x ∈ Set.Icc 0 S,
      HasDerivAt (fun σ => Work.FTS.RegPkgGal.extG g z θ σ - Work.FTS.RegPkgGal.extG g z' θ σ)
        (R z θ x - R z' θ x) x := fun x hx =>
    (hasDerivAt_extG_tau hcont hid hθ hz hx).sub (hasDerivAt_extG_tau hcont hid hθ hz' hx)
  have hdiff : ∀ x ∈ Set.Icc 0 S, DifferentiableAt ℝ
      (fun σ => Work.FTS.RegPkgGal.extG g z θ σ - Work.FTS.RegPkgGal.extG g z' θ σ) x :=
    fun x hx => (hderiv x hx).differentiableAt
  have hbnd : ∀ x ∈ Set.Icc 0 S,
      ‖deriv (fun σ => Work.FTS.RegPkgGal.extG g z θ σ - Work.FTS.RegPkgGal.extG g z' θ σ) x‖
        ≤ N1 * |z - z'| := by
    intro x hx
    rw [(hderiv x hx).deriv, Real.norm_eq_abs]
    exact R_z_mvt hRHz hθ hx hz hz'
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.Icc 0 S) (x := τ) (y := τ')
    hdiff hbnd (convex_Icc 0 S) hτ hτ'
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_sub_comm τ' τ] at h
  have hgoal : |(Work.FTS.RegPkgGal.extG g z θ τ - Work.FTS.RegPkgGal.extG g z θ τ')
        - (Work.FTS.RegPkgGal.extG g z' θ τ - Work.FTS.RegPkgGal.extG g z' θ τ')|
      = |(Work.FTS.RegPkgGal.extG g z θ τ' - Work.FTS.RegPkgGal.extG g z' θ τ')
        - (Work.FTS.RegPkgGal.extG g z θ τ - Work.FTS.RegPkgGal.extG g z' θ τ)| := by
    rw [show (Work.FTS.RegPkgGal.extG g z θ τ - Work.FTS.RegPkgGal.extG g z θ τ')
        - (Work.FTS.RegPkgGal.extG g z' θ τ - Work.FTS.RegPkgGal.extG g z' θ τ')
        = -((Work.FTS.RegPkgGal.extG g z θ τ' - Work.FTS.RegPkgGal.extG g z' θ τ')
        - (Work.FTS.RegPkgGal.extG g z θ τ - Work.FTS.RegPkgGal.extG g z' θ τ)) from by ring,
      abs_neg]
  rw [hgoal]
  exact h

/-! ## The `τ`-modulus of `∂_zg̃` -/

/-- **The pointwise bound for `z > 0`.**  `∂_zg̃(·,θ,τ)` is `τ`-Lipschitz with constant `N1`. -/
lemma pz_tau_le {g : Work.FTS.RegPkgGal.Fam} {R : ℝ → ℝ → ℝ → ℝ} {S N1 θ z τ τ' : ℝ}
    (hcont : ∀ θ ∈ Work.Spaces.Iθ,
      ContDiffOn ℝ 1 (fun q : ℝ × ℝ => Work.FTS.RegPkgGal.extG g q.1 θ q.2)
        (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1)))
    (hid : ∀ z θ τ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → τ ∈ Set.Icc 0 S →
      deriv (fun s => Work.FTS.RegPkgGal.extG g z θ s) τ = R z θ τ)
    (hRHz : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0 : ℝ),
      ∃ d : ℝ, HasDerivAt (fun z' => R z' θ τ) d z ∧ |d| ≤ N1)
    (hN1 : 0 ≤ N1) (hθ : θ ∈ Work.Spaces.Iθ) (hz : 0 < z)
    (hτ : τ ∈ Set.Icc 0 S) (hτ' : τ' ∈ Set.Icc 0 S) :
    |Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ) z θ
      - Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ') z θ|
      ≤ N1 * |τ - τ'| := by
  have hlip : LipschitzOnWith ⟨N1 * |τ - τ'|, mul_nonneg hN1 (abs_nonneg _)⟩
      (fun ζ => Work.FTS.RegPkgGal.extG g ζ θ τ - Work.FTS.RegPkgGal.extG g ζ θ τ')
      (Set.Ioi (0 : ℝ)) := by
    refine LipschitzOnWith.of_dist_le_mul ?_
    intro x hx y hy
    rw [Real.dist_eq, Real.dist_eq]
    have hm := extG_tau_diff_mvt hcont hid hRHz hθ hx hy hτ hτ'
    calc |(Work.FTS.RegPkgGal.extG g x θ τ - Work.FTS.RegPkgGal.extG g x θ τ')
          - (Work.FTS.RegPkgGal.extG g y θ τ - Work.FTS.RegPkgGal.extG g y θ τ')|
        ≤ N1 * |x - y| * |τ - τ'| := hm
      _ = (N1 * |τ - τ'|) * |x - y| := by ring
  have hnd := norm_deriv_le_of_lipschitzOn (isOpen_Ioi.mem_nhds hz) hlip
  have hd : HasDerivAt
      (fun ζ => Work.FTS.RegPkgGal.extG g ζ θ τ - Work.FTS.RegPkgGal.extG g ζ θ τ')
      (Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ) z θ
        - Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ') z θ) z := by
    have hz1 : (-1 : ℝ) < z := by linarith
    have hm1 : τ ∈ Set.Ioo (-1) (S + 1) := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    have hm2 : τ' ∈ Set.Ioo (-1) (S + 1) := ⟨by linarith [hτ'.1], by linarith [hτ'.2]⟩
    exact (hasDerivAt_extG_z hcont hθ hm1 hz1).sub (hasDerivAt_extG_z hcont hθ hm2 hz1)
  rw [hd.deriv, Real.norm_eq_abs] at hnd
  exact hnd

/-- **The endpoint `z = 0`.**  The bound of `pz_tau_le` extends to `z = 0` by continuity of
`z ↦ ∂_zg̃(z,θ,τ)` at `0` (which is `C¹` smoothness). -/
lemma pz_zero_tau_le {g : Work.FTS.RegPkgGal.Fam} {R : ℝ → ℝ → ℝ → ℝ} {S N1 θ τ τ' : ℝ}
    (hcont : ∀ θ ∈ Work.Spaces.Iθ,
      ContDiffOn ℝ 1 (fun q : ℝ × ℝ => Work.FTS.RegPkgGal.extG g q.1 θ q.2)
        (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1)))
    (hid : ∀ z θ τ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → τ ∈ Set.Icc 0 S →
      deriv (fun s => Work.FTS.RegPkgGal.extG g z θ s) τ = R z θ τ)
    (hRHz : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0 : ℝ),
      ∃ d : ℝ, HasDerivAt (fun z' => R z' θ τ) d z ∧ |d| ≤ N1)
    (hN1 : 0 ≤ N1) (hθ : θ ∈ Work.Spaces.Iθ)
    (hτ : τ ∈ Set.Icc 0 S) (hτ' : τ' ∈ Set.Icc 0 S) :
    |Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ) 0 θ
      - Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ') 0 θ|
      ≤ N1 * |τ - τ'| := by
  have hm1 : τ ∈ Set.Ioo (-1) (S + 1) := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  have hm2 : τ' ∈ Set.Ioo (-1) (S + 1) := ⟨by linarith [hτ'.1], by linarith [hτ'.2]⟩
  have hmono : Set.Ioi (0 : ℝ) ⊆ Set.Ioi (-1 : ℝ) :=
    Set.Ioi_subset_Ioi (by norm_num : (-1 : ℝ) ≤ 0)
  have hcont1 : ContinuousWithinAt
      (fun ζ => deriv (fun ζ' => Work.FTS.RegPkgGal.extG g ζ' θ τ) ζ) (Set.Ioi 0) 0 :=
    (((contDiffOn_extG_zSlice hcont hθ hm1).continuousOn_deriv_of_isOpen
        isOpen_Ioi le_rfl).continuousWithinAt (by norm_num)).mono hmono
  have hcont2 : ContinuousWithinAt
      (fun ζ => deriv (fun ζ' => Work.FTS.RegPkgGal.extG g ζ' θ τ') ζ) (Set.Ioi 0) 0 :=
    (((contDiffOn_extG_zSlice hcont hθ hm2).continuousOn_deriv_of_isOpen
        isOpen_Ioi le_rfl).continuousWithinAt (by norm_num)).mono hmono
  have hlim : Filter.Tendsto
      (fun ζ => |deriv (fun ζ' => Work.FTS.RegPkgGal.extG g ζ' θ τ) ζ
        - deriv (fun ζ' => Work.FTS.RegPkgGal.extG g ζ' θ τ') ζ|) (𝓝[Set.Ioi 0] 0)
      (𝓝 |deriv (fun ζ' => Work.FTS.RegPkgGal.extG g ζ' θ τ) 0
        - deriv (fun ζ' => Work.FTS.RegPkgGal.extG g ζ' θ τ') 0|) :=
    (hcont1.tendsto.sub hcont2.tendsto).abs
  have hev : ∀ᶠ ζ in 𝓝[Set.Ioi 0] 0,
      |deriv (fun ζ' => Work.FTS.RegPkgGal.extG g ζ' θ τ) ζ
        - deriv (fun ζ' => Work.FTS.RegPkgGal.extG g ζ' θ τ') ζ| ≤ N1 * |τ - τ'| := by
    filter_upwards [self_mem_nhdsWithin] with ζ hζ
    exact pz_tau_le hcont hid hRHz hN1 hθ hζ hτ hτ'
  have hfin := le_of_tendsto hlim hev
  simpa only [Work.Spaces.pz] using hfin

/-! ## The theorem -/

theorem htaumodp {α S : ℝ} {g : Work.FTS.RegPkgGal.Fam} {R : ℝ → ℝ → ℝ → ℝ} (hα : 0 < α)
    (hα1 : α ≤ 1) (hS : 0 < S)
    (hcont : ∀ θ ∈ Work.Spaces.Iθ,
      ContDiffOn ℝ 1 (fun q : ℝ × ℝ => Work.FTS.RegPkgGal.extG g q.1 θ q.2)
        (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1)))
    (hid : ∀ z θ τ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → τ ∈ Set.Icc 0 S →
      deriv (fun s => Work.FTS.RegPkgGal.extG g z θ s) τ = R z θ τ)
    (hRHz : ∃ N1 : ℝ, 0 ≤ N1 ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ,
      ∀ z ∈ Set.Ioi (0 : ℝ),
      ∃ d : ℝ, HasDerivAt (fun z' => R z' θ τ) d z ∧ |d| ≤ N1)
    (hvan : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z → g z 0 τ = 0 ∧ g z (π / 2) τ = 0)
    (hsup : ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ) z θ| ≤ M) :
    ∃ Nt : ℝ, 0 ≤ Nt ∧ ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z →
      ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ) z θ
          - Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ') z θ|
          ≤ Nt * |τ - τ'| ^ α := by
  obtain ⟨M, hMnn, hM⟩ := hsup
  obtain ⟨N1, hN1nn, hN1⟩ := hRHz
  have hNt0 : (0 : ℝ) ≤ max N1 (2 * M) := le_trans hN1nn (le_max_left _ _)
  refine ⟨max N1 (2 * M), hNt0, ?_⟩
  intro τ hτ τ' hτ' z hz θ hθ
  have hkey : |Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ) z θ
      - Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ') z θ|
      ≤ N1 * |τ - τ'| := by
    rcases lt_or_eq_of_le hz with hzpos | hz0
    · exact pz_tau_le hcont hid hN1 hN1nn hθ hzpos hτ hτ'
    · rw [← hz0]
      exact pz_zero_tau_le hcont hid hN1 hN1nn hθ hτ hτ'
  have hbd : |Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ) z θ
      - Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ') z θ| ≤ 2 * M := by
    have h1 := hM τ hτ z θ hz hθ
    have h2 := hM τ' hτ' z θ hz hθ
    have h3 := abs_sub (Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ) z θ)
      (Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ') z θ)
    linarith
  rcases le_or_gt |τ - τ'| 1 with hle | hgt
  · have hrpow : |τ - τ'| ≤ |τ - τ'| ^ α := by
      rcases eq_or_lt_of_le (abs_nonneg (τ - τ')) with h0 | h0
      · rw [← h0, Real.zero_rpow hα.ne']
      · have hh := Real.rpow_le_rpow_of_exponent_ge h0 hle hα1
        rwa [Real.rpow_one] at hh
    calc |Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ) z θ
          - Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ') z θ|
        ≤ N1 * |τ - τ'| := hkey
      _ ≤ max N1 (2 * M) * |τ - τ'| ^ α :=
          mul_le_mul (le_max_left N1 (2 * M)) hrpow (abs_nonneg _) hNt0
  · have hrpow : 1 ≤ |τ - τ'| ^ α := Real.one_le_rpow hgt.le (le_of_lt hα)
    calc |Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ) z θ
          - Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ') z θ|
        ≤ 2 * M := hbd
      _ ≤ max N1 (2 * M) * |τ - τ'| ^ α := by
          calc 2 * M ≤ max N1 (2 * M) * 1 := by rw [mul_one]; exact le_max_right N1 (2 * M)
            _ ≤ max N1 (2 * M) * |τ - τ'| ^ α := mul_le_mul_of_nonneg_left hrpow hNt0

end Work.FTS.RegPkgGal.Der
