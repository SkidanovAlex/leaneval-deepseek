import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.Construction.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.SB2

open scoped Real Topology
open Set Filter

set_option autoImplicit false

/-!
# `Work.FTS_StreamBdry.SB2.BrMirFacts`

The reflection `θ ↦ π - θ` acting on the angular variable of the self-similar strip:
if `P` is `C²` on the open quadrant `Qd = (0,∞) × (0,π/2)`, then the *mirrored*
function `Q(w,θ) = -P(w, π-θ)` is `C²` on the reflected strip
`(0,∞) × (π/2, π)`, and the plain partial derivatives `∂_z`, `∂_θ` — and all the
second-order combinations of them — transform by the expected signs:

* `∂_z` and `∂_z²` pick up a sign `-1` (the reflection swaps the orientation of the
  `z`-axis relative to the sign of the function);
* `∂_θ` picks up a sign `+1`, and `∂_θ(∂_z)`, `∂_z(∂_θ)` pick up `+1` as well, while
  `∂_θ²` picks up `-1` (each `θ`-derivative contributes `-1` from the chain rule,
  cancelling against the `-1` of the mirrored function).

The pointwise identities are the content of the second conjunct; the first is the
`C²`-statement on the mirrored strip.  Everything is proved from `hP` and the
elementary chain rule for the reflection; the second derivatives use that
`uncurry (∂_zP)` and `uncurry (∂_θP)` are `C¹` on `Qd` (a fact about the curried
partials of a `C²` function, `Work.Spaces.uncurry_partial_c1`).
-/

/-! ## §0 The elementary calculus of the reflection `t ↦ c - t` -/

/-- Chain rule for the reflection `t ↦ c - t`: for `F` differentiable at `c - x`,
the derivative of `F (c - ·)` at `x` is minus the derivative of `F` at `c - x`. -/
private lemma deriv_comp_reflect {F : ℝ → ℝ} {c x : ℝ}
    (hF : DifferentiableAt ℝ F (c - x)) :
    deriv (fun t => F (c - t)) x = - deriv F (c - x) := by
  have hlin : HasDerivAt (fun t : ℝ => c - t) (-1) x := (hasDerivAt_id x).const_sub c
  have h := (hF.hasDerivAt.comp x hlin).deriv
  rw [mul_neg_one] at h
  exact h

/-- `∂_z` of a mirrored function: the sign is `-1`, and no differentiability is
needed (both sides are totalised by `deriv`). -/
private lemma pz_neg_reflect (F : ℝ → ℝ → ℝ) (w θ : ℝ) :
    Work.Spaces.pz (fun w θ => -F w (π - θ)) w θ = -Work.Spaces.pz F w (π - θ) := by
  show deriv (fun x => -F x (π - θ)) w = -deriv (fun x => F x (π - θ)) w
  exact deriv.neg

/-- `∂_θ` of a mirrored function: the sign is `+1`, the two `-1`'s (one from the
negation of the function, one from the chain rule) cancelling. -/
private lemma pth_neg_reflect {F : ℝ → ℝ → ℝ} {w θ : ℝ}
    (hF : DifferentiableAt ℝ (fun s => F w s) (π - θ)) :
    Work.Spaces.pth (fun w θ => -F w (π - θ)) w θ = Work.Spaces.pth F w (π - θ) := by
  show deriv (fun t => -F w (π - t)) θ = deriv (fun s => F w s) (π - θ)
  rw [show (fun t => -F w (π - t)) = - (fun t => F w (π - t)) from rfl]
  rw [deriv.neg]
  rw [deriv_comp_reflect hF]
  ring

/-- The `z`-partials of a mirrored function, as a global function identity. -/
private lemma pz_neg_reflect_fun (F : ℝ → ℝ → ℝ) :
    Work.Spaces.pz (fun w θ => -F w (π - θ))
      = fun a b => -Work.Spaces.pz F a (π - b) := by
  funext a b
  exact pz_neg_reflect F a b

/-! ## §1 The main statement -/

theorem BrMirFacts {P : ℝ → ℝ → ℝ}
    (hP : ContDiffOn ℝ 2 (Function.uncurry P) Work.Construction.Qd) :
    ContDiffOn ℝ 2 (Function.uncurry (fun w θ => -P w (Real.pi - θ)))
        (Set.Ioi 0 ×ˢ Set.Ioo (Real.pi / 2) Real.pi) ∧
    (∀ w θ, 0 < w → Real.pi / 2 < θ → θ < Real.pi →
      Work.Spaces.pz (fun w θ => -P w (Real.pi - θ)) w θ
          = -Work.Spaces.pz P w (Real.pi - θ) ∧
      Work.Spaces.pth (fun w θ => -P w (Real.pi - θ)) w θ
          = Work.Spaces.pth P w (Real.pi - θ) ∧
      Work.Spaces.pz (Work.Spaces.pz (fun w θ => -P w (Real.pi - θ))) w θ
        = -Work.Spaces.pz (Work.Spaces.pz P) w (Real.pi - θ) ∧
      Work.Spaces.pth (Work.Spaces.pz (fun w θ => -P w (Real.pi - θ))) w θ
        = Work.Spaces.pth (Work.Spaces.pz P) w (Real.pi - θ) ∧
      Work.Spaces.pz (Work.Spaces.pth (fun w θ => -P w (Real.pi - θ))) w θ
        = Work.Spaces.pz (Work.Spaces.pth P) w (Real.pi - θ) ∧
      Work.Spaces.pth (Work.Spaces.pth (fun w θ => -P w (Real.pi - θ))) w θ
        = -Work.Spaces.pth (Work.Spaces.pth P) w (Real.pi - θ)) := by
  have hQdopen : IsOpen Work.Construction.Qd := isOpen_Ioi.prod isOpen_Ioo
  -- differentiability of `P` on the open quadrant, as a function of two variables
  have hPd : ∀ p ∈ Work.Construction.Qd, DifferentiableAt ℝ (Function.uncurry P) p :=
    fun p hp => (hP.differentiableOn (by norm_num)).differentiableAt (hQdopen.mem_nhds hp)
  -- the curried partials of `P` are `C¹` on the open quadrant
  have hpart := Work.Spaces.uncurry_partial_c1 hQdopen hP
  refine ⟨?_, ?_⟩
  · -- the mirrored function is `C²` on the reflected strip
    have hR : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => (p.1, Real.pi - p.2))
        (Set.Ioi 0 ×ˢ Set.Ioo (Real.pi / 2) Real.pi) :=
      contDiff_fst.contDiffOn.prodMk
        (contDiffOn_const.sub contDiff_snd.contDiffOn)
    have hmap : Set.MapsTo (fun p : ℝ × ℝ => (p.1, Real.pi - p.2))
        (Set.Ioi 0 ×ˢ Set.Ioo (Real.pi / 2) Real.pi) Work.Construction.Qd := by
      rintro ⟨a, b⟩ hab
      obtain ⟨ha, hb⟩ := hab
      rw [Set.mem_Ioi] at ha
      rw [Set.mem_Ioo] at hb
      show (a, Real.pi - b) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)
      rw [Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
      exact ⟨ha, ⟨by linarith [hb.2, Real.pi_pos], by linarith [hb.1, Real.pi_pos]⟩⟩
    refine ((hP.neg).comp hR hmap).congr ?_
    rintro ⟨a, b⟩ _
    rfl
  · -- the six derivative identities
    intro w θ hw hθ1 hθ2
    have hmem : (w, Real.pi - θ) ∈ Work.Construction.Qd := by
      show (w, Real.pi - θ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)
      rw [Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
      exact ⟨hw, ⟨by linarith [hθ2, Real.pi_pos], by linarith [hθ1, Real.pi_pos]⟩⟩
    -- differentiability of the three slices of `P` at the reflected angle
    have hPslice : DifferentiableAt ℝ (fun s => P w s) (Real.pi - θ) :=
      Work.Spaces.differentiableAt_curry_right (hPd (w, Real.pi - θ) hmem)
    have hpzslice : DifferentiableAt ℝ (fun s => Work.Spaces.pz P w s) (Real.pi - θ) :=
      Work.Spaces.differentiableAt_curry_right
        ((hpart.1.differentiableOn (by norm_num)).differentiableAt (hQdopen.mem_nhds hmem))
    have hpthslice : DifferentiableAt ℝ (fun s => Work.Spaces.pth P w s) (Real.pi - θ) :=
      Work.Spaces.differentiableAt_curry_right
        ((hpart.2.differentiableOn (by norm_num)).differentiableAt (hQdopen.mem_nhds hmem))
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- `∂_z`
      exact pz_neg_reflect P w θ
    · -- `∂_θ`
      exact pth_neg_reflect (F := P) (w := w) (θ := θ) hPslice
    · -- `∂_z²`
      rw [pz_neg_reflect_fun P]
      exact pz_neg_reflect (Work.Spaces.pz P) w θ
    · -- `∂_θ∂_z`
      rw [pz_neg_reflect_fun P]
      exact pth_neg_reflect (F := Work.Spaces.pz P) (w := w) (θ := θ) hpzslice
    · -- `∂_z∂_θ`
      show deriv (fun a => Work.Spaces.pth (fun w θ => -P w (Real.pi - θ)) a θ) w
          = deriv (fun a => Work.Spaces.pth P a (Real.pi - θ)) w
      refine Filter.EventuallyEq.deriv_eq ?_
      have hset : {a : ℝ | (a, Real.pi - θ) ∈ Work.Construction.Qd} ∈ 𝓝 w :=
        (hQdopen.preimage (continuous_id.prodMk continuous_const)).mem_nhds hmem
      filter_upwards [hset] with a ha
      exact pth_neg_reflect (F := P) (w := a) (θ := θ)
        (Work.Spaces.differentiableAt_curry_right (hPd (a, Real.pi - θ) ha))
    · -- `∂_θ²`
      show deriv (fun t => Work.Spaces.pth (fun w θ => -P w (Real.pi - θ)) w t) θ
          = -deriv (fun s => Work.Spaces.pth P w s) (Real.pi - θ)
      have hev : (fun t => Work.Spaces.pth (fun w θ => -P w (Real.pi - θ)) w t)
          =ᶠ[𝓝 θ] (fun t => Work.Spaces.pth P w (Real.pi - t)) := by
        have hset : {t : ℝ | (w, Real.pi - t) ∈ Work.Construction.Qd} ∈ 𝓝 θ :=
          (hQdopen.preimage
            (continuous_const.prodMk (continuous_const.sub continuous_id))).mem_nhds hmem
        filter_upwards [hset] with t ht
        exact pth_neg_reflect (F := P) (w := w) (θ := t)
          (Work.Spaces.differentiableAt_curry_right (hPd (w, Real.pi - t) ht))
      rw [hev.deriv_eq]
      exact deriv_comp_reflect (F := fun s => Work.Spaces.pth P w s) (c := Real.pi)
        (x := θ) hpthslice

end Work.FTS_StreamBdry.SB2
