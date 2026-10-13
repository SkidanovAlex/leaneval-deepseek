import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.LocData.SmoothQuad_Fstar
import Submission.Work.FM.Core

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.StrongPersist.H6Pair6Aux.SmoothN0`

The term `N₀ α (F_* + f) f` of the modulation (§Modulation of Elgindi's paper) is `C^∞` on the
*open* quadrant `(0,∞) × (0,π/2)` as soon as the perturbation `f` and the *radial* function
`z ↦ L₁₂(f)(z)` are.

`N₀` is a sum of six products of the angular factors `sin 2θ`, `c2m θ = cos 2θ - sin²θ`, the
radial factors `z ↦ L₁₂(F_*)(z)`, `z ↦ L₁₂(f)(z)`, and the fields `f`, `∂_θf`, `D_zf`,
`∂_θ(F_*+f)`, `D_z(F_*+f)`, `∂_θF_*`, `D_zF_*`.

* `F_*` is `C^∞` on the open quadrant for **every real** `α` (`LocData.SmoothQuad_Fstar`, no
  hypothesis on `α`), and the class `SmoothOpen` is closed under `+`, `-`, `·`, constants and
  the operators `pz`, `pth`, `Dz`;
* `z ↦ L₁₂(F_*)(z)` is smooth *without* any hypothesis on `α`: the angular and radial variables
  of `L₁₂(F_*)` separate,
  `L₁₂(F_*)(z) = C(α) · (2/(1+z))` with `C(α) = ∫_0^{π/2} K(θ)·α·(Γ(θ)/c(α)) dθ` a constant
  (this is the `α ≤ 1`-free form of `Construction.L12_Fstar_eq`, whose hypothesis `α ≤ 1` only
  serves to produce `c(α) ≠ 0` for the cancellation `C(α) = α`; the *smoothness* never needs
  the cancellation);
* `z ↦ L₁₂(f)(z)` is smooth on `(0,∞)` by hypothesis (`hL`).

Everything is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

open Work.FTS.EllipticEst

/-! ## Elementary closure of `SmoothOpen`

Local copies (the tree's `SmoothOpen`-API modules are partly unbuildable), proved directly from
Mathlib's `ContDiffOn` API. -/

theorem so_add {f g : ℝ → ℝ → ℝ} (hf : SmoothOpen f) (hg : SmoothOpen g) :
    SmoothOpen (fun z θ => f z θ + g z θ) := by
  unfold Work.FTS.EllipticEst.SmoothOpen at hf hg ⊢
  have h : Function.uncurry (fun z θ => f z θ + g z θ)
      = Function.uncurry f + Function.uncurry g := by
    funext p; obtain ⟨z, θ⟩ := p; rfl
  rw [h]
  exact hf.add hg

theorem so_sub {f g : ℝ → ℝ → ℝ} (hf : SmoothOpen f) (hg : SmoothOpen g) :
    SmoothOpen (fun z θ => f z θ - g z θ) := by
  unfold Work.FTS.EllipticEst.SmoothOpen at hf hg ⊢
  have h : Function.uncurry (fun z θ => f z θ - g z θ)
      = Function.uncurry f - Function.uncurry g := by
    funext p; obtain ⟨z, θ⟩ := p; rfl
  rw [h]
  exact hf.sub hg

theorem so_mul {f g : ℝ → ℝ → ℝ} (hf : SmoothOpen f) (hg : SmoothOpen g) :
    SmoothOpen (fun z θ => f z θ * g z θ) := by
  unfold Work.FTS.EllipticEst.SmoothOpen at hf hg ⊢
  have h : Function.uncurry (fun z θ => f z θ * g z θ)
      = Function.uncurry f * Function.uncurry g := by
    funext p; obtain ⟨z, θ⟩ := p; rfl
  rw [h]
  exact hf.mul hg

theorem so_const_mul (c : ℝ) {f : ℝ → ℝ → ℝ} (hf : SmoothOpen f) :
    SmoothOpen (fun z θ => c * f z θ) := by
  unfold Work.FTS.EllipticEst.SmoothOpen at hf ⊢
  have h : Function.uncurry (fun z θ => c * f z θ) = c • Function.uncurry f := by
    funext p; obtain ⟨z, θ⟩ := p; rfl
  rw [h]
  exact hf.const_smul c

/-- The constant function is `C^∞` on the open quadrant. -/
theorem so_const (c : ℝ) : SmoothOpen (fun _ _ : ℝ => c) := by
  unfold Work.FTS.EllipticEst.SmoothOpen
  exact contDiffOn_const

/-- A function of `z` alone which is `C^n` on `(0,∞)` for every `n` is `C^∞` on the open
quadrant. -/
theorem so_radial {r : ℝ → ℝ} (hr : ∀ n : ℕ, ContDiffOn ℝ n r (Set.Ioi 0)) :
    SmoothOpen (fun z _ => r z) := by
  refine smoothOpen_of_forall fun n => ?_
  exact (hr n).comp contDiffOn_fst (fun p hp => (mem_Q0.mp hp).1)

/-- A function of `θ` alone which is `C^∞` on `ℝ` is `C^∞` on the open quadrant. -/
theorem so_snd {g : ℝ → ℝ} (hg : ContDiff ℝ Work.Stability.smoothOrder g) :
    SmoothOpen (fun _ (θ : ℝ) => g θ) := by
  unfold Work.FTS.EllipticEst.SmoothOpen
  exact (hg.comp_contDiffOn contDiff_snd.contDiffOn).mono (Set.subset_univ _)

/-- `sin(2·)` is `C^∞`. -/
theorem contDiff_s2 : ContDiff ℝ Work.Stability.smoothOrder Work.Construction.s2 := by
  unfold Work.Construction.s2
  exact Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)

/-- `c2m θ = cos 2θ - sin²θ` is `C^∞`. -/
theorem contDiff_c2m : ContDiff ℝ Work.Stability.smoothOrder Work.Construction.c2m := by
  unfold Work.Construction.c2m
  have h1 : ContDiff ℝ Work.Stability.smoothOrder (fun θ : ℝ => Real.cos (2 * θ)) :=
    Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)
  have h2 : ContDiff ℝ Work.Stability.smoothOrder (fun θ : ℝ => Real.sin θ ^ 2) :=
    Real.contDiff_sin.pow 2
  exact h1.sub h2

/-! ## `F_*` and the radial function `L₁₂(F_*)` -/

/-- The model profile `F_*` is `C^∞` on the open quadrant, for every real `α`. -/
theorem smoothOpen_Fstar (α : ℝ) : SmoothOpen (Work.Construction.Fstar α) :=
  (Work.FTS.LocData.SmoothQuad_Fstar α).mono
    (Set.prod_mono (Set.Ioi_subset_Ioi (by norm_num : (-1 : ℝ) ≤ 0)) subset_rfl)

/-- **The angular density of `L₁₂(F_*)` is a *constant* times `F_*(s)/s`**, for every real `α`
(no hypothesis on `α`, and in particular no use of `c(α) ≠ 0`): the angle and the radius
separate in `F_*(s,θ) = α·(Γ(θ)/c(α))·F_*(s)`. -/
theorem L12dens_Fstar_mul_const (α s : ℝ) :
    Work.FM.L12dens Work.Spaces.K (Work.Construction.Fstar α) s
      = (∫ θ in Set.Icc 0 (Real.pi / 2),
          Work.Spaces.K θ * (α * (Work.Spaces.Gam α θ / Work.Spaces.c α)))
        * (Work.FM.Fstar s / s) := by
  rw [Work.FM.L12dens]
  have hpoint : ∀ θ : ℝ, Work.Spaces.K θ * Work.Construction.Fstar α s θ / s
      = (Work.Spaces.K θ * (α * (Work.Spaces.Gam α θ / Work.Spaces.c α)))
        * (Work.FM.Fstar s / s) := by
    intro θ
    simp only [Work.Construction.Fstar]
    ring
  rw [setIntegral_congr_fun measurableSet_Icc (fun θ _ => hpoint θ)]
  rw [MeasureTheory.integral_mul_const]

/-- **`L₁₂(F_*)(z) = C(α)·2/(1+z)` for every real `α` and every `z ≥ 0`**, the `α ≤ 1`-free
form of `Construction.L12_Fstar_eq`. -/
theorem L12_Fstar_mul_const (α z : ℝ) (hz : 0 ≤ z) :
    Work.Construction.L12 (Work.Construction.Fstar α) z
      = (∫ θ in Set.Icc 0 (Real.pi / 2),
          Work.Spaces.K θ * (α * (Work.Spaces.Gam α θ / Work.Spaces.c α)))
        * (2 / (1 + z)) := by
  rw [Work.Construction.L12, Work.FM.L12]
  rw [setIntegral_congr_fun measurableSet_Ioi (fun s _ => L12dens_Fstar_mul_const α s)]
  rw [MeasureTheory.integral_const_mul, Work.FM.integral_Ioi_Fstar_div z hz]

/-- **The radial function `z ↦ L₁₂(F_*)(z)` is `C^∞` on `(0,∞)`**, for every real `α`. -/
theorem smoothOpen_L12_Fstar (α : ℝ) :
    SmoothOpen (fun z _ => Work.Construction.L12 (Work.Construction.Fstar α) z) := by
  refine so_radial (fun n => ?_)
  have hc : ContDiffOn ℝ n (fun z : ℝ =>
      (∫ θ in Set.Icc 0 (Real.pi / 2),
          Work.Spaces.K θ * (α * (Work.Spaces.Gam α θ / Work.Spaces.c α)))
        * (2 / (1 + z))) (Set.Ioi 0) := by
    refine contDiffOn_const.mul ?_
    refine contDiffOn_const.div (contDiffOn_const.add contDiffOn_id) ?_
    intro z hz
    have hz' : (0 : ℝ) < z := hz
    show (1 : ℝ) + z ≠ 0
    linarith
  exact hc.congr (fun z hz => L12_Fstar_mul_const α z (le_of_lt hz))

/-! ## The target -/

theorem SmoothN0 {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ}
      (hf : Work.FTS.EllipticEst.SmoothOpen f)
      (hL : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 f z)) :
      Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
        Work.Construction.N0 α (fun z θ => Work.Construction.Fstar α z θ + f z θ) f z θ) := by
  have hFstar : SmoothOpen (Work.Construction.Fstar α) := smoothOpen_Fstar α
  have hT : SmoothOpen (fun z θ => Work.Construction.Fstar α z θ + f z θ) :=
    so_add hFstar hf
  have hLF : SmoothOpen (fun z _ => Work.Construction.L12 (Work.Construction.Fstar α) z) :=
    smoothOpen_L12_Fstar α
  -- the six summands of `N₀`
  have hT1 : SmoothOpen (fun z θ => (3 / (2 * α)) * Work.Construction.s2 θ
      * Work.Construction.L12 (Work.Construction.Fstar α) z
      * Work.Spaces.pth (Work.Construction.Fstar α) z θ) :=
    so_mul (so_mul (so_const_mul (3 / (2 * α)) (so_snd contDiff_s2)) hLF) hFstar.pth
  have hT2 : SmoothOpen (fun z θ => Work.Construction.c2m θ
      * Work.Construction.L12 (Work.Construction.Fstar α) z
      * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) :=
    so_mul (so_mul (so_snd contDiff_c2m) hLF) hFstar.Dz
  have hT3 : SmoothOpen (fun z θ => (1 / α) * Work.Construction.L12 f z * f z θ) :=
    so_mul (so_const_mul (1 / α) hL) hf
  have hT4 : SmoothOpen (fun z θ => (3 / (2 * α)) * Work.Construction.s2 θ
      * Work.Construction.L12 f z
      * Work.Spaces.pth (fun z θ => Work.Construction.Fstar α z θ + f z θ) z θ) :=
    so_mul (so_mul (so_const_mul (3 / (2 * α)) (so_snd contDiff_s2)) hL) hT.pth
  have hT5 : SmoothOpen (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 f z
      * Work.Spaces.Dz (fun z θ => Work.Construction.Fstar α z θ + f z θ) z θ) :=
    so_mul (so_mul (so_snd contDiff_c2m) hL) hT.Dz
  have hT6 : SmoothOpen (fun z θ => Work.Construction.c2m θ
      * Work.Construction.L12 (Work.Construction.Fstar α) z
      * Work.Spaces.Dz f z θ) :=
    so_mul (so_mul (so_snd contDiff_c2m) hLF) hf.Dz
  have key : SmoothOpen (fun z θ =>
      (3 / (2 * α)) * Work.Construction.s2 θ
          * Work.Construction.L12 (Work.Construction.Fstar α) z
          * Work.Spaces.pth (Work.Construction.Fstar α) z θ
        - Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z
          * Work.Spaces.Dz (Work.Construction.Fstar α) z θ
        + (1 / α) * Work.Construction.L12 f z * f z θ
        + (3 / (2 * α)) * Work.Construction.s2 θ * Work.Construction.L12 f z
          * Work.Spaces.pth (fun z θ => Work.Construction.Fstar α z θ + f z θ) z θ
        - Work.Construction.c2m θ * Work.Construction.L12 f z
          * Work.Spaces.Dz (fun z θ => Work.Construction.Fstar α z θ + f z θ) z θ
        - Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z
          * Work.Spaces.Dz f z θ) :=
    ((((hT1.sub hT2).add hT3).add hT4).sub hT5).sub hT6
  refine ContDiffOn.congr
    (f₁ := Function.uncurry (fun z θ =>
      Work.Construction.N0 α (fun z θ => Work.Construction.Fstar α z θ + f z θ) f z θ))
    key ?_
  intro p hp
  simp only [Function.uncurry, Work.Construction.N0]

end Work.FTS.StrongPersist.H6Pair6Aux
