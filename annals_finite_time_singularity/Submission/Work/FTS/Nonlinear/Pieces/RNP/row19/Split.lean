/-
# Row 19 of the N4 table — the split `V(Φ̃_*) = V₀ + W`

The piece of row 19 is `N₃^{**} = -2α · V(Φ̃_*) · D_zF_*` (`Work.FTS.Nonlin.N3ss`), where

  `V(Φ̃_*) = ∂_θΦ̃_* - tan θ · Φ̃_*`   (`Work.Construction.Vop`, abbreviated `Vs`),

and the frozen `StarPkg` bounds it only by `WlInfMem α 4` (`V`), i.e. by the *weighted*
derivatives `(z+1)^k ∂_z^k V` and `(z+1)^k ∂_z^k D_θ^j V · sin(2θ)^{-α/5}/(α + sin 2θ)`.

This file performs the *splitting* that makes the row provable from those fields:

  `V(Φ̃_*)(z,θ) = V₀(θ) + W(z,θ)`,   `V₀(θ) := V(Φ̃_*)(0,θ)`,  `W := V - V₀`,

together with the structural facts about `W` that the estimate needs:

* `W` vanishes at `z = 0`, which upgrades the `𝒲^{4,∞}`-bound on `V` to the *Lipschitz*
  bound `|W(z,θ)| ≤ M·z` (`Vs_lipschitz`), and gives
  `|D_θ^i W(z,θ)| ≤ C M z (α+sin 2θ) sin(2θ)^{α/5}` for `i ≤ 3`;
* the *bare* pointwise bounds of `V₀(θ) = V(0,θ)`, which make the split-off part
  `V₀·D_zF_*` degenerate (see `V0Part.lean`).

All the constants below are of the form `K · max Cs 0 · α` with `K` universal.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row19aux
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.Vs_lipschitz
import Submission.Work.Spaces.WlInf_terms
import Submission.Work.Spaces.ProductRuleInW
import Submission.Work.FTS.LocData.SmoothChain

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP.row19

set_option autoImplicit false
set_option linter.unusedVariables false

open Work.FTS.Nonlinear.Pieces.RNP (Vs Gs)

/-- `V₀(θ) = V(Φ̃_*)(0,θ)`: the value of the coefficient at `z = 0`. -/
abbrev Vs0 (α : ℝ) (Φs : Work.FTS.Galerkin.Fn) : ℝ → ℝ := fun θ => Vs α Φs 0 θ

/-- `V₀` viewed as a function of `(z,θ)`: constant in `z`. -/
abbrev Vs0f (α : ℝ) (Φs : Work.FTS.Galerkin.Fn) : ℝ → ℝ → ℝ := fun _ θ => Vs0 α Φs θ

/-- `W = V(Φ̃_*) - V₀`: the part of the coefficient that vanishes at `z = 0`. -/
abbrev VsW (α : ℝ) (Φs : Work.FTS.Galerkin.Fn) : ℝ → ℝ → ℝ :=
  fun z θ => Vs α Φs z θ - Vs0 α Φs θ

@[simp] theorem Vs0f_apply (α : ℝ) (Φs : Work.FTS.Galerkin.Fn) (z θ : ℝ) :
    Vs0f α Φs z θ = Vs α Φs 0 θ := rfl

@[simp] theorem VsW_apply (α : ℝ) (Φs : Work.FTS.Galerkin.Fn) (z θ : ℝ) :
    VsW α Φs z θ = Vs α Φs z θ - Vs0 α Φs θ := rfl

/-- The defining decomposition `V = V₀ + W`. -/
theorem Vs_eq_Vs0f_add_VsW (α : ℝ) (Φs : Work.FTS.Galerkin.Fn) :
    Vs α Φs = Vs0f α Φs + VsW α Φs := by
  funext z θ
  simp only [Pi.add_apply, VsW_apply, Vs0f_apply]
  ring

/-- `W` vanishes at `z = 0`. -/
@[simp] theorem VsW_zero (α : ℝ) (Φs : Work.FTS.Galerkin.Fn) (θ : ℝ) :
    VsW α Φs 0 θ = 0 := by
  simp only [VsW_apply, sub_self]

/-! ## Smoothness -/

/-- `V₀` is `C^∞` on the half strip (it is the `z = 0` slice of `V`). -/
theorem contDiffOn_Vs0f {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (Vs0f α Φs))
      (Set.Ioi (-1) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hV := Vs_smoothQuad (α := α) (Cs := Cs) (Φs := Φs) hα hs
  have hslice : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ : ℝ => Vs α Φs 0 θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hV.curry_θ (show (0 : ℝ) ∈ Set.Ioi (-1) by norm_num)
  have hfun : Function.uncurry (Vs0f α Φs) = fun p : ℝ × ℝ => Vs α Φs 0 p.2 := rfl
  rw [hfun]
  exact hslice.comp contDiff_snd.contDiffOn (fun p hp => hp.2)

/-- `W = V - V₀` is `C^∞` on the half strip (`SmoothQuad`). -/
theorem smoothQuad_VsW {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    Work.FTS.LocData.SmoothQuad (VsW α Φs) := by
  have hV := Vs_smoothQuad (α := α) (Cs := Cs) (Φs := Φs) hα hs
  have h0 : Work.FTS.LocData.SmoothQuad (Vs0f α Φs) :=
    Work.FTS.LocData.smoothQuad_of_contDiffOn_uncurry (contDiffOn_Vs0f hα hs)
  have hsub := Work.FTS.LocData.smoothQuad_sub hV h0
  refine hsub.congr ?_
  intro p _
  obtain ⟨z, θ⟩ := p
  rfl

/-- The `z`-slices of the `D_θ`-iterates of a `SmoothQuad` function are differentiable. -/
theorem differentiableAt_slice_DthIter_z {G : ℝ → ℝ → ℝ} (hG : Work.FTS.LocData.SmoothQuad G)
    (i : ℕ) {z : ℝ} (hz : -1 < z) {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    DifferentiableAt ℝ (fun z' => Work.Spaces.DthIter i G z' θ) z := by
  have h := hG.differentiableAt_slice_mixed 0 i hz hθ
  simpa only [Work.Spaces.mixed_zero_left] using h

/-! ## Identities: the iterated derivatives of `W` against those of `V` -/

/-- Iterated `∂_z` of a function minus a constant is the iterated `∂_z` of the function. -/
theorem iter_deriv_sub_const (a : ℕ) (ha : 1 ≤ a) (f : ℝ → ℝ) (c : ℝ) :
    deriv^[a] (fun x => f x - c) = deriv^[a] f := by
  induction a with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      funext x
      simpa using deriv_sub_const (f := f) (x := x) c
    · have hprev : deriv^[n] (fun x => f x - c) = deriv^[n] f := ih (by omega)
      funext x
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hprev]

/-- `pzIter a f z θ` is the `a`-th plain `z`-derivative of the `z`-slice. -/
theorem pzIter_eq_iter_deriv (a : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pzIter a f z θ = deriv^[a] (fun t => f t θ) z := by
  induction a generalizing z with
  | zero => simp
  | succ n ih =>
    simp only [Work.Spaces.pzIter_succ, Work.Spaces.pz]
    rw [show (fun z' => Work.Spaces.pzIter n f z' θ) = deriv^[n] (fun t => f t θ) from
      funext (fun z' => ih z')]
    exact congrFun (Function.iterate_succ_apply' deriv n (fun t => f t θ)).symm z

/-- For `a ≥ 1` the `z`-derivatives of `W` and of `V` agree (a constant is subtracted). -/
theorem pzIter_VsW_eq (α : ℝ) (Φs : Work.FTS.Galerkin.Fn) (a : ℕ) (ha : 1 ≤ a) (z θ : ℝ) :
    Work.Spaces.pzIter a (VsW α Φs) z θ = Work.Spaces.pzIter a (Vs α Φs) z θ := by
  rw [pzIter_eq_iter_deriv, pzIter_eq_iter_deriv]
  have hfun : (fun t : ℝ => VsW α Φs t θ) = fun t => Vs α Φs t θ - Vs0 α Φs θ := by
    funext t
    simp only [VsW_apply]
  rw [hfun, iter_deriv_sub_const a ha]

/-- `D_θ^i f = 0` at an angle outside the open interval (where `sin 2θ = 0`), for `i ≥ 1`. -/
theorem DthIter_eq_zero_of_not_Ioo {f : ℝ → ℝ → ℝ} {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    (h : θ ∉ Set.Ioo (0 : ℝ) (Real.pi / 2)) (i : ℕ) (hi : 1 ≤ i) (z : ℝ) :
    Work.Spaces.DthIter i f z θ = 0 :=
  Work.Spaces.DthIter_eq_zero_of_sin (Work.Spaces.sin_two_eq_zero_of_not_Ioo hθ h) i hi z

/-- `D_θ^i W(z,θ) = D_θ^i V(z,θ) - D_θ^i V(0,θ)` on the open quadrant. -/
theorem DthIter_VsW_eq {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) (i : ℕ) :
    ∀ z θ, -1 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DthIter i (VsW α Φs) z θ
        = Work.Spaces.DthIter i (Vs α Φs) z θ - Work.Spaces.DthIter i (Vs α Φs) 0 θ := by
  have hsq : Work.FTS.LocData.SmoothQuad (Vs α Φs) :=
    Vs_smoothQuad (α := α) (Cs := Cs) (Φs := Φs) hα hs
  induction i with
  | zero => intro z θ _ _ _; simp only [Work.Spaces.DthIter_zero]
  | succ n ih =>
    intro z θ hz h1 h2
    have heq : (fun θ' => Work.Spaces.DthIter n (VsW α Φs) z θ')
        =ᶠ[𝓝 θ] fun θ' => Work.Spaces.DthIter n (Vs α Φs) z θ'
            - Work.Spaces.DthIter n (Vs α Φs) 0 θ' := by
      filter_upwards [isOpen_Ioo.mem_nhds (show θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) from ⟨h1, h2⟩)]
        with θ' hθ'
      exact ih z θ' hz hθ'.1 hθ'.2
    have hd1 : DifferentiableAt ℝ (fun θ' => Work.Spaces.DthIter n (Vs α Φs) z θ') θ :=
      hsq.differentiableAt_slice_DthIter n hz ⟨h1, h2⟩
    have hd2 : DifferentiableAt ℝ (fun θ' => Work.Spaces.DthIter n (Vs α Φs) 0 θ') θ :=
      hsq.differentiableAt_slice_DthIter n (show (0 : ℝ) ∈ Set.Ioi (-1) by norm_num) ⟨h1, h2⟩
    have hd : deriv (fun θ' => Work.Spaces.DthIter n (Vs α Φs) z θ'
          - Work.Spaces.DthIter n (Vs α Φs) 0 θ') θ
        = deriv (fun θ' => Work.Spaces.DthIter n (Vs α Φs) z θ') θ
          - deriv (fun θ' => Work.Spaces.DthIter n (Vs α Φs) 0 θ') θ :=
      deriv_sub hd1 hd2
    simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
    rw [heq.deriv_eq, hd]
    ring

/-- The angular derivatives of `W` vanish at `z = 0`. -/
theorem DthIter_VsW_zero (α : ℝ) (Φs : Work.FTS.Galerkin.Fn) (i : ℕ) (θ : ℝ) :
    Work.Spaces.DthIter i (VsW α Φs) 0 θ = 0 := by
  induction i generalizing θ with
  | zero => simp
  | succ i ih =>
    simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
    have h0 : (fun θ' : ℝ => Work.Spaces.DthIter i (VsW α Φs) 0 θ')
        = fun _ : ℝ => (0 : ℝ) := funext (fun θ' => ih θ')
    rw [h0]
    simp

/-- Iterated `deriv` respects eventual equality. -/
theorem eventuallyEq_iter_deriv {f g : ℝ → ℝ} {z : ℝ} (h : f =ᶠ[𝓝 z] g) :
    ∀ a : ℕ, deriv^[a] f =ᶠ[𝓝 z] deriv^[a] g
  | 0 => by simpa using h
  | a + 1 => by
    have h' : deriv^[a] f =ᶠ[𝓝 z] deriv^[a] g := eventuallyEq_iter_deriv h a
    have h'' : deriv (deriv^[a] f) =ᶠ[𝓝 z] deriv (deriv^[a] g) := h'.deriv
    have e1 : deriv^[a + 1] f = deriv (deriv^[a] f) :=
      Function.iterate_succ_apply' deriv a f
    have e2 : deriv^[a + 1] g = deriv (deriv^[a] g) :=
      Function.iterate_succ_apply' deriv a g
    rw [e1, e2]
    exact h''

/-- `deriv^[a]` is a local operation: functions agreeing near the point have equal iterated
derivatives there. -/
theorem iter_deriv_congr_of_eventuallyEq {f g : ℝ → ℝ} {z : ℝ} (h : f =ᶠ[𝓝 z] g) (a : ℕ) :
    deriv^[a] f z = deriv^[a] g z :=
  (eventuallyEq_iter_deriv h a).eq_of_nhds

/-- For `a ≥ 1` and `z > -1` the `z`-derivatives of `D_θ^i W` and of `D_θ^i V` agree. -/
theorem pzIter_DthIter_VsW_eq {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) (i a : ℕ) (ha : 1 ≤ a) {z θ : ℝ}
    (hz : -1 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.pzIter a (fun z θ => Work.Spaces.DthIter i (VsW α Φs) z θ) z θ
      = Work.Spaces.pzIter a (fun z θ => Work.Spaces.DthIter i (Vs α Φs) z θ) z θ := by
  rw [pzIter_eq_iter_deriv, pzIter_eq_iter_deriv]
  have h1 : deriv^[a] (fun t : ℝ => Work.Spaces.DthIter i (VsW α Φs) t θ) z
      = deriv^[a] (fun t : ℝ => Work.Spaces.DthIter i (Vs α Φs) t θ
          - Work.Spaces.DthIter i (Vs α Φs) 0 θ) z := by
    refine iter_deriv_congr_of_eventuallyEq ?_ a
    filter_upwards [isOpen_Ioi.mem_nhds hz] with t ht
    exact DthIter_VsW_eq hα hs i t θ ht hθ.1 hθ.2
  rw [h1]
  exact congrFun (iter_deriv_sub_const a ha (fun t : ℝ => Work.Spaces.DthIter i (Vs α Φs) t θ)
    (Work.Spaces.DthIter i (Vs α Φs) 0 θ)) z

/-- The Lipschitz bound of `Vs_lipschitz`, in the form used by the row. -/
theorem abs_VsW_le_lip {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |VsW α Φs z θ| ≤ max Cs 0 * α * z := by
  intro z hz θ hθ
  have h := Vs_lipschitz (α := α) (Cs := Cs) (Φs := Φs) hα hs z hz θ hθ
  simpa only [VsW_apply, Vs0] using h

/-- The global bound `|W| ≤ 2 max Cs 0 · α`. -/
theorem abs_VsW_le {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |VsW α Φs z θ| ≤ 2 * (max Cs 0 * α) := by
  intro z hz θ hθ
  have h1 := Work.FTS.Nonlinear.Pieces.RNP.abs_Vs_le (α := α) (Cs := Cs) (Φs := Φs) hα hs
  have h2 := h1 z hz θ hθ
  have h3 := h1 0 (Set.mem_Ici.mpr (le_refl (0 : ℝ))) θ hθ
  have h4 : |VsW α Φs z θ|
      ≤ |Vs α Φs z θ| + |Vs0 α Φs θ| := by
    simp only [VsW_apply, Vs0]
    exact abs_sub _ _
  linarith

/-- `|W(z,θ)| ≤ 2 max Cs 0 · α · min z 1` on the open angular interval: the Lipschitz
bound together with global boundedness. -/
theorem abs_VsW_le_min {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |VsW α Φs z θ| ≤ 2 * (max Cs 0 * α) * min z 1 := by
  intro z hz θ hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have hz0 : 0 ≤ z := hz
  have hM0 : 0 ≤ max Cs 0 * α := mul_nonneg (le_max_right _ _) hα.le
  have h1 : |VsW α Φs z θ| ≤ max Cs 0 * α * z := by
    rcases eq_or_lt_of_le hz0 with h | h
    · rw [← h, VsW_zero]; simp
    · exact abs_VsW_le_lip hα hs z hz θ hθ
  have h2 : |VsW α Φs z θ| ≤ 2 * (max Cs 0 * α) := abs_VsW_le hα hs z hz θ hθI
  rcases le_total z 1 with hz1 | hz1
  · rw [min_eq_left hz1]
    nlinarith
  · rw [min_eq_right hz1]
    nlinarith
/-- The angular weight of every angular bound of this file is nonnegative on the open
angular interval. -/
theorem angular_weight_nonneg {α θ : ℝ} (hα : 0 < α)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) := by
  have h2θ : (2 * θ) ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  exact mul_nonneg (by linarith [Real.sin_nonneg_of_mem_Icc h2θ, hα])
    (Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc h2θ) _)

/-- **The weighted `z`-derivative bounds of `W`**: `|z^a ∂_z^a W| ≤ 2 max Cs 0 α · min z 1`
for `a ≤ 4` on the open angular interval. -/
theorem abs_zpow_pzIter_VsW_le {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    ∀ a : ℕ, a ≤ 4 → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |z ^ a * Work.Spaces.pzIter a (VsW α Φs) z θ|
        ≤ 2 * (max Cs 0 * α) * min z 1 := by
  intro a ha z hz θ hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  rcases Nat.eq_zero_or_pos a with h0 | hapos
  · subst h0
    simpa using abs_VsW_le_min (α := α) (Cs := Cs) (Φs := Φs) hα hs z hz θ hθ
  · have hder : Work.Spaces.pzIter a (VsW α Φs) z θ
        = Work.Spaces.pzIter a (Vs α Φs) z θ := pzIter_VsW_eq α Φs a hapos z θ
    rw [hder, abs_mul, abs_of_nonneg (pow_nonneg hz a)]
    have hz0 : 0 ≤ z := hz
    have hM0 : 0 ≤ max Cs 0 * α := mul_nonneg (le_max_right _ _) hα.le
    have hle : Work.Spaces.WlInf α 4 (Vs α Φs) ≤ max Cs 0 * α :=
      le_trans hs.V.2 (mul_le_mul_of_nonneg_right (le_max_left _ _) hα.le)
    have hzp : (0 : ℝ) < z + 1 := by linarith
    have hw := Work.Spaces.WlInf_z_bound α 4 (Vs α Φs) hs.V.1 a ha z θ hz hθI
    have hw' : (z + 1) ^ a * |Work.Spaces.pzIter a (Vs α Φs) z θ| ≤ max Cs 0 * α := by
      rw [abs_mul, abs_of_nonneg (le_of_lt (pow_pos hzp a))] at hw
      exact le_trans hw hle
    have hratio : z / (z + 1) ≤ min z 1 := by
      rcases le_total z 1 with h | h
      · rw [min_eq_left h, div_le_iff₀ hzp]; nlinarith
      · rw [min_eq_right h, div_le_one hzp]; linarith
    have hratio0 : 0 ≤ z / (z + 1) := div_nonneg hz0 (le_of_lt hzp)
    have hratio1 : z / (z + 1) ≤ 1 := by rw [div_le_one hzp]; linarith
    have hmin0 : 0 ≤ min z 1 := le_min hz0 zero_le_one
    have hpowle : (z / (z + 1)) ^ a ≤ min z 1 :=
      calc (z / (z + 1)) ^ a ≤ (z / (z + 1)) ^ 1 :=
            pow_le_pow_of_le_one hratio0 hratio1 hapos
        _ = z / (z + 1) := pow_one _
        _ ≤ min z 1 := hratio
    have hsplit : z ^ a * |Work.Spaces.pzIter a (Vs α Φs) z θ|
        = (z / (z + 1)) ^ a * ((z + 1) ^ a * |Work.Spaces.pzIter a (Vs α Φs) z θ|) := by
      rw [div_pow]
      field_simp
    rw [hsplit]
    calc (z / (z + 1)) ^ a * ((z + 1) ^ a * |Work.Spaces.pzIter a (Vs α Φs) z θ|)
        ≤ min z 1 * (max Cs 0 * α) :=
          mul_le_mul hpowle hw' (mul_nonneg (by positivity) (abs_nonneg _)) hmin0
      _ ≤ 2 * (max Cs 0 * α) * min z 1 := by nlinarith

/-- **The angular-derivative bounds of `W`**, first form: `|D_θ^i W| ≤ 2 max Cs 0 α ·
(α + sin 2θ) sin(2θ)^{α/5}` for `1 ≤ i ≤ 4`, on the closed domain. -/
theorem abs_DthIter_VsW_le {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (VsW α Φs) z θ|
        ≤ 2 * (max Cs 0 * α)
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
  intro i hi1 hi4 z hz θ hθ
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have hle : Work.Spaces.WlInf α 4 (Vs α Φs) ≤ max Cs 0 * α :=
    le_trans hs.V.2 (mul_le_mul_of_nonneg_right (le_max_left _ _) hα.le)
  have hθ0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have harg : 0 ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) :=
    mul_nonneg (by linarith) (Real.rpow_nonneg hθ0 _)
  have key : ∀ z' ∈ Work.Spaces.Iz,
      |Work.Spaces.DthIter (j + 1) (Vs α Φs) z' θ|
        ≤ max Cs 0 * α * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
    intro z' hz'
    have h := Work.Spaces.pz_Dth_sup_bound α hα 4 (Vs α Φs) hs.V.1 (j + 1) 0 (by omega)
      (by omega) z' θ hz' hθ
    simp only [Work.Spaces.pzIter_zero, pow_zero, div_one] at h
    exact le_trans h (mul_le_mul_of_nonneg_right hle harg)
  rcases eq_or_lt_of_le hθ.1 with hθzero | hθpos
  · rw [← hθzero, Work.Spaces.DthIter_apply_zero (VsW α Φs) j z, abs_zero]
    have hsin : Real.sin (2 * (0 : ℝ)) = 0 := by simp
    rw [hsin, Real.zero_rpow (ne_of_gt (by positivity : (0 : ℝ) < α / 5)), mul_zero, mul_zero]
  rcases eq_or_lt_of_le hθ.2 with hθpi | hθlt
  · rw [hθpi, Work.Spaces.DthIter_apply_pi_half (VsW α Φs) j z, abs_zero]
    have hsin : Real.sin (2 * (Real.pi / 2)) = 0 := by
      rw [show 2 * (Real.pi / 2) = Real.pi from by ring, Real.sin_pi]
    rw [hsin, Real.zero_rpow (ne_of_gt (by positivity : (0 : ℝ) < α / 5)), mul_zero, mul_zero]
  have hz0' : (0 : ℝ) ≤ z := hz
  have hid := DthIter_VsW_eq hα hs (j + 1) z θ (by linarith) hθpos hθlt
  rw [hid]
  refine le_trans (abs_sub_le (Work.Spaces.DthIter (j + 1) (Vs α Φs) z θ) 0
    (Work.Spaces.DthIter (j + 1) (Vs α Φs) 0 θ)) ?_
  rw [sub_zero, zero_sub, abs_neg]
  have h1 := key z hz
  have h2 := key 0 (Set.mem_Ici.mpr (le_refl (0 : ℝ)))
  linarith

/-- **The angular-derivative bounds of `W`**, with the `z`-vanishing, for `i ≤ 3`. -/
theorem abs_DthIter_VsW_le_min {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    ∀ i : ℕ, 1 ≤ i → i ≤ 3 → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Spaces.DthIter i (VsW α Φs) z θ|
        ≤ 2 * (max Cs 0 * α)
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) * min z 1 := by
  intro i hi1 hi3 z hz θ hθ
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have hsq : Work.FTS.LocData.SmoothQuad (Vs α Φs) :=
    Vs_smoothQuad (α := α) (Cs := Cs) (Φs := Φs) hα hs
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have hM0 : 0 ≤ max Cs 0 * α := mul_nonneg (le_max_right _ _) hα.le
  have harg : 0 ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) :=
    angular_weight_nonneg hα hθ
  have hle : Work.Spaces.WlInf α 4 (Vs α Φs) ≤ max Cs 0 * α :=
    le_trans hs.V.2 (mul_le_mul_of_nonneg_right (le_max_left _ _) hα.le)
  have hz0 : 0 ≤ z := hz
  have hglobal := abs_DthIter_VsW_le (α := α) (Cs := Cs) (Φs := Φs) hα hs (j + 1) (by omega)
    (by omega) z hz θ hθI
  -- the mean value theorem in `z` on `[0,z]`
  have hmvt : |Work.Spaces.DthIter (j + 1) (VsW α Φs) z θ|
      ≤ max Cs 0 * α * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) * z := by
    rcases eq_or_lt_of_le hz0 with h0 | hpos
    · rw [← h0, DthIter_VsW_zero α Φs (j + 1) θ, abs_zero]
      nlinarith [mul_nonneg hM0 harg]
    · have hdiff : ∀ x ∈ Set.Icc (0 : ℝ) z,
          DifferentiableAt ℝ (fun t : ℝ => Work.Spaces.DthIter (j + 1) (Vs α Φs) t θ) x := by
        intro x hx
        exact differentiableAt_slice_DthIter_z hsq (j + 1) (by linarith [hx.1]) hθ
      have hbdd : ∀ x ∈ Set.Icc (0 : ℝ) z,
          ‖deriv (fun t : ℝ => Work.Spaces.DthIter (j + 1) (Vs α Φs) t θ) x‖
            ≤ max Cs 0 * α * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
        intro x hx
        have hxI : x ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hx.1
        have h := Work.Spaces.pz_Dth_sup_bound α hα 4 (Vs α Φs) hs.V.1 (j + 1) 1 (by omega)
          (by omega) x θ hxI hθI
        rw [show Work.Spaces.pzIter 1 (Work.Spaces.DthIter (j + 1) (Vs α Φs)) x θ
            = deriv (fun t : ℝ => Work.Spaces.DthIter (j + 1) (Vs α Φs) t θ) x from rfl] at h
        rw [Real.norm_eq_abs]
        refine le_trans h ?_
        have hx1 : (0 : ℝ) < x + 1 := by linarith [hx.1]
        have hdiv : ((x + 1 : ℝ))⁻¹ ≤ 1 := by
          rw [inv_le_one₀ hx1]; linarith [hx.1]
        calc Work.Spaces.WlInf α 4 (Vs α Φs) / (x + 1) ^ 1
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
            = (Work.Spaces.WlInf α 4 (Vs α Φs) * (x + 1)⁻¹)
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
              rw [pow_one, div_eq_mul_inv]
          _ ≤ (max Cs 0 * α) * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
              refine mul_le_mul_of_nonneg_right ?_ harg
              calc Work.Spaces.WlInf α 4 (Vs α Φs) * (x + 1)⁻¹
                  ≤ (max Cs 0 * α) * (x + 1)⁻¹ := mul_le_mul_of_nonneg_right hle (by positivity)
                _ ≤ (max Cs 0 * α) * 1 := mul_le_mul_of_nonneg_left hdiv hM0
                _ = max Cs 0 * α := mul_one _
      have hmain := (convex_Icc (0 : ℝ) z).norm_image_sub_le_of_norm_deriv_le hdiff hbdd
        (left_mem_Icc.mpr hz0) (right_mem_Icc.mpr hz0)
      rw [Real.norm_eq_abs, sub_zero, Real.norm_eq_abs, abs_of_nonneg hpos.le] at hmain
      have hid := DthIter_VsW_eq hα hs (j + 1) z θ (by linarith) hθ.1 hθ.2
      rw [hid]
      exact hmain
  rcases le_total z 1 with hz1 | hz1
  · rw [min_eq_left hz1]
    nlinarith [hmvt, hglobal, mul_nonneg (mul_nonneg hM0 harg) hz0]
  · rw [min_eq_right hz1]
    nlinarith [hmvt, hglobal, mul_nonneg hM0 harg]

/-- **The mixed bounds of `W`**: `|z^a ∂_z^a D_θ^i W| ≤ 2 max Cs 0 α (α+sin 2θ) sin(2θ)^{α/5}
· min z 1` for `1 ≤ i`, `1 ≤ a`, `a + i ≤ 4`. -/
theorem abs_zpow_pzIter_DthIter_VsW_le {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    ∀ i a : ℕ, 1 ≤ i → 1 ≤ a → a + i ≤ 4 →
      ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        |z ^ a * Work.Spaces.pzIter a (fun z θ => Work.Spaces.DthIter i (VsW α Φs) z θ) z θ|
          ≤ 2 * (max Cs 0 * α)
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) * min z 1 := by
  intro i a hi1 ha1 hai z hz θ hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have hM0 : 0 ≤ max Cs 0 * α := mul_nonneg (le_max_right _ _) hα.le
  have harg : 0 ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) :=
    angular_weight_nonneg hα hθ
  have hle : Work.Spaces.WlInf α 4 (Vs α Φs) ≤ max Cs 0 * α :=
    le_trans hs.V.2 (mul_le_mul_of_nonneg_right (le_max_left _ _) hα.le)
  have hz0 : 0 ≤ z := hz
  rw [pzIter_DthIter_VsW_eq hα hs i a ha1 (by linarith) hθ,
    abs_mul, abs_of_nonneg (pow_nonneg hz0 a)]
  have h := Work.Spaces.pz_Dth_sup_bound α hα 4 (Vs α Φs) hs.V.1 i a hi1 (by omega)
    z θ hz hθI
  have hzp : (0 : ℝ) < z + 1 := by linarith
  have hsplit : z ^ a * (Work.Spaces.WlInf α 4 (Vs α Φs) / (z + 1) ^ a
        * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
      = (z / (z + 1)) ^ a * (Work.Spaces.WlInf α 4 (Vs α Φs)
        * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) := by
    rw [div_pow]
    field_simp
  have hratio : z / (z + 1) ≤ min z 1 := by
    rcases le_total z 1 with h1 | h1
    · rw [min_eq_left h1, div_le_iff₀ hzp]; nlinarith
    · rw [min_eq_right h1, div_le_one hzp]; linarith
  have hratio0 : 0 ≤ z / (z + 1) := div_nonneg hz0 (le_of_lt hzp)
  have hratio1 : z / (z + 1) ≤ 1 := by rw [div_le_one hzp]; linarith
  have hpowle : (z / (z + 1)) ^ a ≤ min z 1 :=
    calc (z / (z + 1)) ^ a ≤ (z / (z + 1)) ^ 1 :=
          pow_le_pow_of_le_one hratio0 hratio1 ha1
      _ = z / (z + 1) := pow_one _
      _ ≤ min z 1 := hratio
  have hmin0 : 0 ≤ min z 1 := le_min hz0 zero_le_one
  calc z ^ a * |Work.Spaces.pzIter a (fun z θ => Work.Spaces.DthIter i (Vs α Φs) z θ) z θ|
      ≤ z ^ a * (Work.Spaces.WlInf α 4 (Vs α Φs) / (z + 1) ^ a
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
        mul_le_mul_of_nonneg_left h (pow_nonneg hz0 a)
    _ = (z / (z + 1)) ^ a * (Work.Spaces.WlInf α 4 (Vs α Φs)
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) := hsplit
    _ ≤ min z 1 * ((max Cs 0 * α)
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) := by
        refine le_trans (mul_le_mul_of_nonneg_right hpowle
          (mul_nonneg (Work.Spaces.WlInf_nonneg α 4 (Vs α Φs) hs.V.1) harg)) ?_
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hle harg) hmin0
    _ ≤ 2 * (max Cs 0 * α)
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) * min z 1 := by
        rw [show 2 * (max Cs 0 * α)
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) * min z 1
            = 2 * (min z 1 * ((max Cs 0 * α)
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))) from by ring]
        have hxy : (0 : ℝ) ≤ min z 1 * ((max Cs 0 * α)
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
          mul_nonneg hmin0 (mul_nonneg hM0 harg)
        linarith

end Work.FTS.Nonlinear.Pieces.RNP.row19
