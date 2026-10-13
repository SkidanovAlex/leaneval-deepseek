/-
Copyright: work module for the Elgindi finite-time singularity project.

# Commutation of the iterated slice derivatives `∂_z^i` and `∂_θ^j`

For a function `F : ℝ → ℝ → ℝ` of class `C^n` at a point `(z,θ)`, and any `i + j ≤ n`,
the iterated partial derivatives commute:
`∂_z^i ∂_θ^j F (z,θ) = ∂_θ^j ∂_z^i F (z,θ)`.

This is the higher order Clairaut (Schwarz) theorem for the totalized partial
derivatives `Work.Spaces.pzIter` (iterated `∂_z`) and `Work.Spaces.pthIter` (iterated
`∂_θ`) used throughout the project.

The proof is an induction that moves the `∂_z`'s through the `∂_θ`'s one at a time,
each step being an instance of the second order Clairaut theorem
`Work.Spaces.pz_pth_comm`.  The only bookkeeping needed is the smoothness of the
intermediate functions (`pzIter`/`pthIter` lower the smoothness class by their order,
proved here as `pzIter_contDiffAt`/`pthIter_contDiffAt`) and the congruence of the
slice derivatives under equality in a neighbourhood (`pz_congr_ev`/`pth_congr_ev`).
-/
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.mixed_comm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Filter

namespace Work.FTS.GalBasis.GalApprox

namespace PzIterAux

/-! ## Smoothness of the iterated slice derivatives -/

/-- `∂_z` lowers the smoothness class by one.  (On a neighbourhood of the point, the
slice derivative `pz G` is the `(1,0)`-component of `fderiv ℝ (uncurry G)`.) -/
lemma pz_contDiffAt {G : ℝ → ℝ → ℝ} {y : ℝ × ℝ} {m : ℕ}
    (h : ContDiffAt ℝ (m + 1) (Function.uncurry G) y) :
    ContDiffAt ℝ m (Function.uncurry (Work.Spaces.pz G)) y := by
  have hfd : ContDiffAt ℝ m (fderiv ℝ (Function.uncurry G)) y := by
    have := ContDiffAt.fderiv_right (𝕜 := ℝ) h
      (by norm_num : ((m : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((m + 1 : ℕ) : ℕ∞))
    simpa using this
  have hfun : ContDiffAt ℝ m
      (fun y' : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) y') (1, 0)) y :=
    hfd.clm_apply contDiffAt_const
  refine ContDiffAt.congr_of_eventuallyEq hfun ?_
  filter_upwards [h.eventually (by simp)] with y' hy'
  have hd : DifferentiableAt ℝ (Function.uncurry G) y' := hy'.differentiableAt (by norm_num)
  have := Work.Spaces.deriv_slice_fst (Function.uncurry G) y'.1 y'.2 hd
  show Work.Spaces.pz G y'.1 y'.2 = _
  rw [show Work.Spaces.pz G y'.1 y'.2
      = deriv (fun z' => Function.uncurry G (z', y'.2)) y'.1 from rfl]
  exact this

/-- `∂_θ` lowers the smoothness class by one. -/
lemma pth_contDiffAt {G : ℝ → ℝ → ℝ} {y : ℝ × ℝ} {m : ℕ}
    (h : ContDiffAt ℝ (m + 1) (Function.uncurry G) y) :
    ContDiffAt ℝ m (Function.uncurry (Work.Spaces.pth G)) y := by
  have hfd : ContDiffAt ℝ m (fderiv ℝ (Function.uncurry G)) y := by
    have := ContDiffAt.fderiv_right (𝕜 := ℝ) h
      (by norm_num : ((m : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((m + 1 : ℕ) : ℕ∞))
    simpa using this
  have hfun : ContDiffAt ℝ m
      (fun y' : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) y') (0, 1)) y :=
    hfd.clm_apply contDiffAt_const
  refine ContDiffAt.congr_of_eventuallyEq hfun ?_
  filter_upwards [h.eventually (by simp)] with y' hy'
  have hd : DifferentiableAt ℝ (Function.uncurry G) y' := hy'.differentiableAt (by norm_num)
  have := Work.Spaces.deriv_slice_snd (Function.uncurry G) y'.1 y'.2 hd
  show Work.Spaces.pth G y'.1 y'.2 = _
  rw [show Work.Spaces.pth G y'.1 y'.2
      = deriv (fun θ' => Function.uncurry G (y'.1, θ')) y'.2 from rfl]
  exact this

/-- `∂_z^i` lowers the smoothness class by `i`. -/
lemma pzIter_contDiffAt {F : ℝ → ℝ → ℝ} {y : ℝ × ℝ} :
    ∀ (i m : ℕ), ContDiffAt ℝ (m + i) (Function.uncurry F) y →
      ContDiffAt ℝ m (Function.uncurry (Work.Spaces.pzIter i F)) y := by
  intro i
  induction i with
  | zero => intro m h; simpa using h
  | succ i ih =>
      intro m h
      have h' : ContDiffAt ℝ ((m + 1) + i) (Function.uncurry F) y := by
        convert h using 1
        push_cast
        ring
      have hG : ContDiffAt ℝ (m + 1) (Function.uncurry (Work.Spaces.pzIter i F)) y :=
        ih (m + 1) h'
      exact pz_contDiffAt hG

/-- `∂_θ^j` lowers the smoothness class by `j`. -/
lemma pthIter_contDiffAt {F : ℝ → ℝ → ℝ} {y : ℝ × ℝ} :
    ∀ (j m : ℕ), ContDiffAt ℝ (m + j) (Function.uncurry F) y →
      ContDiffAt ℝ m (Function.uncurry (Work.Spaces.pthIter j F)) y := by
  intro j
  induction j with
  | zero => intro m h; simpa using h
  | succ j ih =>
      intro m h
      have h' : ContDiffAt ℝ ((m + 1) + j) (Function.uncurry F) y := by
        convert h using 1
        push_cast
        ring
      have hG : ContDiffAt ℝ (m + 1) (Function.uncurry (Work.Spaces.pthIter j F)) y :=
        ih (m + 1) h'
      exact pth_contDiffAt hG

/-! ## Congruence of the slice derivatives -/

/-- The slice derivative `∂_z` only depends on the germ of the function. -/
lemma pz_congr_ev {g g' : ℝ → ℝ → ℝ} {y : ℝ × ℝ}
    (h : Function.uncurry g =ᶠ[𝓝 y] Function.uncurry g') :
    Work.Spaces.pz g y.1 y.2 = Work.Spaces.pz g' y.1 y.2 := by
  have hd := (h.comp_tendsto (Continuous.prodMk_left y.2).continuousAt).deriv_eq
  show deriv (fun z' => g z' y.2) y.1 = deriv (fun z' => g' z' y.2) y.1
  exact hd

/-- The slice derivative `∂_θ` only depends on the germ of the function. -/
lemma pth_congr_ev {g g' : ℝ → ℝ → ℝ} {y : ℝ × ℝ}
    (h : Function.uncurry g =ᶠ[𝓝 y] Function.uncurry g') :
    Work.Spaces.pth g y.1 y.2 = Work.Spaces.pth g' y.1 y.2 := by
  have hd := (h.comp_tendsto (Continuous.prodMk_right y.1).continuousAt).deriv_eq
  show deriv (fun θ' => g y.1 θ') y.2 = deriv (fun θ' => g' y.1 θ') y.2
  exact hd

/-! ## Moving a single `∂_z` through `j` iterated `∂_θ`'s -/

/-- One `∂_z` can be moved through `j` iterated `∂_θ`'s, at the cost of one order of
smoothness (Clairaut at every stage). -/
lemma pz_pthIter_eq : ∀ (j : ℕ) (F : ℝ → ℝ → ℝ) (y : ℝ × ℝ),
    ContDiffAt ℝ (j + 1) (Function.uncurry F) y →
    Work.Spaces.pz (Work.Spaces.pthIter j F) y.1 y.2
      = Work.Spaces.pthIter j (Work.Spaces.pz F) y.1 y.2 := by
  intro j
  induction j with
  | zero => intro F y h; rfl
  | succ j ih =>
      intro F y h
      have hG : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.pthIter j F)) y := by
        have := pthIter_contDiffAt (F := F) (y := y) j 2 (by
          convert h using 1
          push_cast
          ring)
        simpa using this
      have hcl := Work.Spaces.pz_pth_comm (f := Work.Spaces.pthIter j F) hG
      have hev : Function.uncurry (Work.Spaces.pz (Work.Spaces.pthIter j F)) =ᶠ[𝓝 y]
          Function.uncurry (Work.Spaces.pthIter j (Work.Spaces.pz F)) := by
        filter_upwards [h.eventually (by simp)] with y' hy'
        exact ih F y' (hy'.of_le (by norm_num))
      have hstep := pth_congr_ev hev
      show Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.pthIter j F)) y.1 y.2
          = Work.Spaces.pth (Work.Spaces.pthIter j (Work.Spaces.pz F)) y.1 y.2
      rw [hcl, hstep]

/-! ## The main commutation -/

/-- The general statement: if `F` is `C^n` at `y` and `i + j ≤ n` then
`∂_z^i ∂_θ^j F = ∂_θ^j ∂_z^i F` at `y`.  (Stated with a fixed `n` so that the
smoothness class is a single natural number, which keeps the "eventually" arguments
clean.) -/
lemma pzIter_pthIter_comm_aux (n : ℕ) :
    ∀ (i j : ℕ) (F : ℝ → ℝ → ℝ) (y : ℝ × ℝ), i + j ≤ n →
      ContDiffAt ℝ n (Function.uncurry F) y →
      Work.Spaces.pzIter i (Work.Spaces.pthIter j F) y.1 y.2
        = Work.Spaces.pthIter j (Work.Spaces.pzIter i F) y.1 y.2 := by
  intro i
  induction i with
  | zero => intro j F y hij h; rfl
  | succ i ih =>
      intro j F y hij h
      have hij' : i + j ≤ n := by omega
      -- the induction hypothesis at nearby points, as an eventual equality
      have hev : Function.uncurry (Work.Spaces.pzIter i (Work.Spaces.pthIter j F))
          =ᶠ[𝓝 y]
          Function.uncurry (Work.Spaces.pthIter j (Work.Spaces.pzIter i F)) := by
        filter_upwards [h.eventually (by simp)] with y' hy'
        exact ih j F y' hij' hy'
      have hpz := pz_congr_ev hev
      -- move the outer `∂_z` through the remaining `j` iterated `∂_θ`'s
      have hG : ContDiffAt ℝ (j + 1) (Function.uncurry (Work.Spaces.pzIter i F)) y := by
        have h1 : ContDiffAt ℝ ((j + 1) + i) (Function.uncurry F) y :=
          h.of_le (by exact_mod_cast (by omega : (j + 1) + i ≤ n))
        exact pzIter_contDiffAt (F := F) (y := y) i (j + 1) h1
      have hA := pz_pthIter_eq j (Work.Spaces.pzIter i F) y hG
      rw [Work.Spaces.pzIter_succ, hpz]
      exact hA

end PzIterAux

theorem pzIter_pthIter_comm {F : ℝ → ℝ → ℝ} {z θ : ℝ} {n : ℕ}
    (h : ContDiffAt ℝ n (Function.uncurry F) (z, θ)) (i j : ℕ) (hij : i + j ≤ n) :
    Work.Spaces.pzIter i (Work.Spaces.pthIter j F) z θ =
      Work.Spaces.pthIter j (Work.Spaces.pzIter i F) z θ :=
  PzIterAux.pzIter_pthIter_comm_aux n i j F (z, θ) hij h

end Work.FTS.GalBasis.GalApprox
