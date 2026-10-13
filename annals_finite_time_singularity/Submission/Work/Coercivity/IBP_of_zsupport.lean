/-
# The `IBP` hypothesis package for functions supported in a compact `z`-interval

This file proves `Work.Coercivity.IBP_of_zsupport`: every function `v` which is smooth
on a neighbourhood of the closed quadrant `[0,∞) × [0,π/2]` and vanishes for `z ≤ a`
(`a > 0`) as well as for `z ≥ R` satisfies the analytic hypothesis package `IBP v`
(see `Submission/Work/Coercivity/Defs.lean`) on which the `z`-integration by parts of
the coercivity chapter rests.

This is the formal counterpart of the paper's approximation device: the Hardy lemma
("We will establish the result for smooth functions with `f` and `L₁₂(f)` vanishing (at
least) quadratically at zero. The general case will follow by approximation.", Elgindi,
Annals 194 (3) 2021) is proved for smooth *compactly supported* functions, for which
every boundary term in `IBP` vanishes, every slice integral is that of a continuous
function of compact support, and the derivative of the boundary term is again of
compact support.

## Structure of the proof

Fix `a > 0` with `v ≡ 0` on `{z ≤ a}` and `R` with `v ≡ 0` on `{z ≥ R}`, and let
`d = max R (a+1)`, so that `a ≤ d`, `0 < a ≤ d`, and `v z θ = 0` whenever `z ∉ [a,d]`
and `θ ∈ Iθ`.  Then

* `smooth` is the hypothesis;
* `bd0`/`bdTop`: on `(0,a]` resp. `[d,∞)` the boundary term `z (v w)²` is *identically*
  zero, so the limits are those of the constant function `0`;
* `intSq`, `intDeriv`: the `θ`-slices of `(v w)²` and of `∂_z(z (v w)²)` are continuous
  on `(0,∞)` and vanish off `[a,d]`, hence integrable on `(0,∞)`
  (`integrableOn_Ioi_of_Icc_support`);
* `intSqProd`, `intL`: the joint integrands are continuous on the compact box
  `[a,d] × Iθ` and vanish on `[0,∞) × Iθ` outside that box, hence integrable
  (`integrableOn_prod_of_box`).
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Coercivity.thetaAux
import Submission.Work.Spaces.HardyZ
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.Spaces.HkAux
import Submission.Work.Coercivity.integrableOn_Ioi_of_Icc_support
import Submission.Work.Coercivity.integrableOn_prod_of_box

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-! ## Smoothness of the weight `w` on `(0,∞)` -/

/-- The radial weight `w(z) = (1+z)²/z²` is smooth on `(0,∞)`. -/
theorem contDiffOn_w_Ioi : ContDiffOn ℝ ⊤ (fun z : ℝ => Spaces.w z) (Set.Ioi 0) := by
  have h : ContDiffOn ℝ ⊤ (fun z : ℝ => (1 + z) ^ 2 * (z⁻¹) ^ 2) (Set.Ioi 0) :=
    ((contDiffOn_const.add contDiffOn_id).pow 2).mul
      ((contDiffOn_id.inv fun z hz => ne_of_gt hz).pow 2)
  refine h.congr (fun z _ => ?_)
  rw [Spaces.w, div_eq_mul_inv, inv_pow]

/-- The radial weight `w` is continuous on every `z`-box `[c,d] × [0,π/2]` with `c > 0`. -/
theorem continuousOn_box_w (c d : ℝ) (hc : 0 < c) :
    ContinuousOn (fun p : ℝ × ℝ => Spaces.w p.1) (Set.Icc c d ×ˢ Spaces.Iθ) := by
  unfold Spaces.w
  refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) (fun p hp => ?_)
  exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le hc hp.1.1))

/-! ## Continuity of the derivative of the boundary term, slicewise -/

/-- For every `θ ∈ Iθ` the `z`-derivative of the boundary term `z (v w)²` is continuous
on `(0,∞)`: the boundary term is smooth there (`v(·,θ)` is smooth on `(-1,∞)` and `w` is
smooth off `0`). -/
theorem deriv_zw_sq_continuousOn (v : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd v) {θ : ℝ}
    (hθ : θ ∈ Spaces.Iθ) :
    ContinuousOn (fun z => deriv (fun z' => z' * (v z' θ * Spaces.w z') ^ 2) z) (Set.Ioi 0) := by
  have hvs : ContDiffOn ℝ ⊤ (fun z => v z θ) (Set.Ioi 0) :=
    (Spaces.hardyZ_contDiffOn_slice v hsm hθ).mono (fun z hz => by
      simp only [Set.mem_Ioi] at hz ⊢
      linarith)
  have hF : ContDiffOn ℝ ⊤ (fun z => z * (v z θ * Spaces.w z) ^ 2) (Set.Ioi 0) :=
    contDiffOn_id.mul ((hvs.mul contDiffOn_w_Ioi).pow 2)
  have hcd : ContinuousOn (derivWithin (fun z => z * (v z θ * Spaces.w z) ^ 2) (Set.Ioi 0))
      (Set.Ioi 0) :=
    hF.continuousOn_derivWithin isOpen_Ioi.uniqueDiffOn le_top
  refine hcd.congr (fun x hx => ?_)
  exact (derivWithin_of_isOpen isOpen_Ioi hx).symm

/-! ## Continuity of the joint integrands on the box -/

/-- The map `(z,θ) ↦ (v z θ · w z)²` is continuous on the box `[c,d] × [0,π/2]`. -/
theorem box_sq_w_continuousOn (v : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd v) {c d : ℝ}
    (hc : 0 < c) :
    ContinuousOn (Function.uncurry (fun z θ => (v z θ * Spaces.w z) ^ 2))
      (Set.Icc c d ×ˢ Spaces.Iθ) := by
  have hboxU : Set.Icc c d ×ˢ Spaces.Iθ ⊆ Spaces.U := by
    rintro ⟨z, θ⟩ hz
    exact Spaces.mem_U_of_box (R := d) ⟨le_of_lt (lt_of_lt_of_le hc hz.1.1), hz.1.2⟩ hz.2
  have hv : ContinuousOn (Function.uncurry v) (Set.Icc c d ×ˢ Spaces.Iθ) :=
    hsm.continuousOn.mono hboxU
  have hw := continuousOn_box_w c d hc
  have hfun : Function.uncurry (fun z θ => (v z θ * Spaces.w z) ^ 2)
      = fun p : ℝ × ℝ => (Function.uncurry v p * Spaces.w p.1) ^ 2 := by
    funext p
    rfl
  rw [hfun]
  exact (hv.mul hw).pow 2

/-- The map `(z,θ) ↦ 𝓛v(z,θ) · v(z,θ) · w(z)²` is continuous on the box
`[c,d] × [0,π/2]` (with `c > 0`, so that `w` is smooth on the box). -/
theorem box_Lprod_continuousOn (v : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd v) {c d : ℝ}
    (hc : 0 < c) :
    ContinuousOn (Function.uncurry (fun z θ => L v z θ * v z θ * Spaces.w z ^ 2))
      (Set.Icc c d ×ˢ Spaces.Iθ) := by
  have hboxU : Set.Icc c d ×ˢ Spaces.Iθ ⊆ Spaces.U := by
    rintro ⟨z, θ⟩ hz
    exact Spaces.mem_U_of_box (R := d) ⟨le_of_lt (lt_of_lt_of_le hc hz.1.1), hz.1.2⟩ hz.2
  have hv : ContinuousOn (Function.uncurry v) (Set.Icc c d ×ˢ Spaces.Iθ) :=
    hsm.continuousOn.mono hboxU
  have hpzv : ContinuousOn (Function.uncurry (Spaces.pz v)) (Set.Icc c d ×ˢ Spaces.Iθ) :=
    (Spaces.contDiffOn_uncurry_pz Spaces.isOpen_U hsm).continuousOn.mono hboxU
  have hDz : ContinuousOn (Function.uncurry (Spaces.Dz v)) (Set.Icc c d ×ˢ Spaces.Iθ) := by
    have hfun : Function.uncurry (Spaces.Dz v)
        = fun p : ℝ × ℝ => p.1 * Function.uncurry (Spaces.pz v) p := by
      funext p
      rfl
    rw [hfun]
    exact continuousOn_fst.mul hpzv
  have hden0 : ∀ p ∈ Set.Icc c d ×ˢ Spaces.Iθ, (1 + p.1 : ℝ) ≠ 0 := by
    intro p hp
    have : (0 : ℝ) < p.1 := lt_of_lt_of_le hc hp.1.1
    linarith
  have hL : ContinuousOn (Function.uncurry (L v)) (Set.Icc c d ×ˢ Spaces.Iθ) := by
    have hfun : Function.uncurry (L v) = fun p : ℝ × ℝ =>
        Function.uncurry v p + Function.uncurry (Spaces.Dz v) p
          - 2 * Function.uncurry v p / (1 + p.1) := by
      funext p
      rfl
    rw [hfun]
    exact (hv.add hDz).sub
      ((continuousOn_const.mul hv).div (continuousOn_const.add continuousOn_fst) hden0)
  have hw2 : ContinuousOn (fun p : ℝ × ℝ => Spaces.w p.1 ^ 2)
      (Set.Icc c d ×ˢ Spaces.Iθ) := (continuousOn_box_w c d hc).pow 2
  have hfun : Function.uncurry (fun z θ => L v z θ * v z θ * Spaces.w z ^ 2)
      = fun p : ℝ × ℝ => Function.uncurry (L v) p * Function.uncurry v p * Spaces.w p.1 ^ 2 := by
    funext p
    rfl
  rw [hfun]
  exact (hL.mul hv).mul hw2

/-! ## The main theorem -/

theorem IBP_of_zsupport (v : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd v) (h0 : ∃ a : ℝ, 0 < a ∧ ∀ z, z ≤ a → ∀ θ, v z θ = 0) (hR : ∃ R : ℝ, ∀ z, R ≤ z → ∀ θ, v z θ = 0) : IBP v := by
  obtain ⟨a, ha_pos, ha⟩ := h0
  obtain ⟨R, hR'⟩ := hR
  set d := max R (a + 1) with hd
  have hdR : R ≤ d := le_max_left _ _
  have had : a ≤ d := by
    rw [hd]
    exact le_trans (by linarith : a ≤ a + 1) (le_max_right _ _)
  -- `v` vanishes off the box `[a,d]`
  have hvzero : ∀ z, z ∉ Set.Icc a d → ∀ θ, v z θ = 0 := by
    intro z hznot θ
    rcases lt_or_ge z a with h | h
    · exact ha z (le_of_lt h) θ
    · have hdg : d < z := by
        by_contra hcon
        exact hznot ⟨h, not_lt.mp hcon⟩
      exact hR' z (le_trans hdR (le_of_lt hdg)) θ
  refine ⟨hsm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `bd0`
    intro θ hθ
    have hmem : Set.Iic a ∈ 𝓝[>] (0 : ℝ) :=
      nhdsWithin_le_nhds (Filter.mem_of_superset (Iio_mem_nhds ha_pos)
        (fun x hx => le_of_lt (Set.mem_Iio.mp hx)))
    have hev : (fun z => z * (v z θ * Spaces.w z) ^ 2) =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => (0 : ℝ)) := by
      filter_upwards [hmem] with z hz
      rw [ha z hz θ]
      ring
    rw [Filter.tendsto_congr' hev]
    exact tendsto_const_nhds
  · -- `bdTop`
    intro θ hθ
    have hev : (fun z => z * (v z θ * Spaces.w z) ^ 2) =ᶠ[Filter.atTop] (fun _ => (0 : ℝ)) := by
      filter_upwards [eventually_ge_atTop d] with z hz
      rw [hR' z (le_trans hdR hz) θ]
      ring
    rw [Filter.tendsto_congr' hev]
    exact tendsto_const_nhds
  · -- `intSq`
    intro θ hθ
    refine integrableOn_Ioi_of_Icc_support (c := a) (d := d) ha_pos ?_ ?_
    · have hv : ContinuousOn (fun z => v z θ) (Set.Ioi 0) :=
        ((Spaces.hardyZ_contDiffOn_slice v hsm hθ).mono (fun z hz => by
          simp only [Set.mem_Ioi] at hz ⊢
          linarith)).continuousOn
      exact ((hv.mul contDiffOn_w_Ioi.continuousOn).pow 2).mono
        (fun z hz => lt_of_lt_of_le ha_pos hz.1)
    · intro z hz hznot
      rw [hvzero z hznot θ]
      ring
  · -- `intSqProd`
    refine integrableOn_prod_of_box (G := fun z θ => (v z θ * Spaces.w z) ^ 2)
      (c := a) (d := d) ha_pos (box_sq_w_continuousOn v hsm ha_pos) ?_
    intro z _hz θ _hθ hznot
    rw [hvzero z hznot θ]
    ring
  · -- `intDeriv`
    intro θ hθ
    refine integrableOn_Ioi_of_Icc_support (c := a) (d := d) ha_pos ?_ ?_
    · exact (deriv_zw_sq_continuousOn v hsm hθ).mono (fun z hz => lt_of_lt_of_le ha_pos hz.1)
    · intro z _hz hznot
      rcases lt_or_ge z a with h | h
      · have hev : (fun z' => z' * (v z' θ * Spaces.w z') ^ 2) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
          filter_upwards [isOpen_Iio.mem_nhds h] with z' hz'
          rw [ha z' (le_of_lt hz') θ]
          ring
        rw [Filter.EventuallyEq.deriv_eq hev, deriv_const]
      · have hdg : d < z := by
          by_contra hcon
          exact hznot ⟨h, not_lt.mp hcon⟩
        have hev : (fun z' => z' * (v z' θ * Spaces.w z') ^ 2) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
          filter_upwards [isOpen_Ioi.mem_nhds hdg] with z' hz'
          rw [hR' z' (le_trans hdR (le_of_lt hz')) θ]
          ring
        rw [Filter.EventuallyEq.deriv_eq hev, deriv_const]
  · -- `intL`
    refine integrableOn_prod_of_box (G := fun z θ => L v z θ * v z θ * Spaces.w z ^ 2)
      (c := a) (d := d) ha_pos (box_Lprod_continuousOn v hsm ha_pos) ?_
    intro z _hz θ _hθ hznot
    rw [hvzero z hznot θ]
    ring

end Work.Coercivity
