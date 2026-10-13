/-
Copyright: work module for the Elgindi finite-time singularity project.

# `∂_z^k` commutes with the iterates of `D_θ = sin(2θ) ∂_θ`

The curvilinear angular derivative `D_θ f = sin(2θ) ∂_θ f` is a differential operator of
order one whose coefficient `sin(2θ)` does not depend on `z`.  Consequently every iterate
`D_θ^i` commutes with every iterate `∂_z^k` of the plain radial derivative, and the present
file proves the resulting identity

`∂_z^k (D_θ^i (∂_θ f)) = D_θ^i (∂_θ (∂_z^k f))`

at any point `(z,θ)` at which `f` is `C^{k+i+1}`.

The proof is a Clairaut/Schwarz induction in the style of
`Submission.Work.FTS.GalBasis.GalApprox.pzIter_pthIter_comm`: the smoothness of the
intermediate functions (`pzIter`, `pth`, `DthIter`, ... lower the order of
differentiability by their order) is tracked with natural-number orders, and the
congruence lemmas `pz_congr_ev`/`pth_congr_ev` move derivatives across functions that only
agree in a neighbourhood of the point.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.pz_aux
import Submission.Work.Spaces.mixed_comm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open Set Filter

namespace Work.FTS.PhiStar.FlatWAux

namespace PzDthAux

set_option autoImplicit false

/-! ## Smoothness of the slice derivatives -/

/-- `∂_z` lowers the order of differentiability by one. -/
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

/-- `∂_θ` lowers the order of differentiability by one. -/
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

/-- `ContDiffAt` of a natural order holds at all nearby points. -/
lemma contDiffAt_eventually_nat {F : ℝ → ℝ → ℝ} {x : ℝ × ℝ} {m : ℕ}
    (h : ContDiffAt ℝ m (Function.uncurry F) x) :
    ∀ᶠ y in 𝓝 x, ContDiffAt ℝ m (Function.uncurry F) y :=
  h.eventually (by simp)

/-- `∂_z^i` lowers the order of differentiability by `i`. -/
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

/-- `D_θ = sin(2θ) ∂_θ` lowers the order of differentiability by one (the coefficient
`sin(2θ)` is smooth, so it costs nothing). -/
lemma Dth_contDiffAt {G : ℝ → ℝ → ℝ} {y : ℝ × ℝ} {m : ℕ}
    (h : ContDiffAt ℝ (m + 1) (Function.uncurry G) y) :
    ContDiffAt ℝ m (Function.uncurry (Work.Spaces.Dth G)) y := by
  have hp : ContDiffAt ℝ m (Function.uncurry (Work.Spaces.pth G)) y := pth_contDiffAt h
  have hs : ContDiffAt ℝ m (fun p : ℝ × ℝ => Real.sin (2 * p.2)) y := by fun_prop
  have hmul : ContDiffAt ℝ m ((fun p : ℝ × ℝ => Real.sin (2 * p.2))
      * (Function.uncurry (Work.Spaces.pth G))) y := hs.mul hp
  have hfun : ((fun p : ℝ × ℝ => Real.sin (2 * p.2))
      * (Function.uncurry (Work.Spaces.pth G)))
      = Function.uncurry (Work.Spaces.Dth G) := by
    funext p
    rfl
  rw [hfun] at hmul
  exact hmul

/-- `D_θ^j` lowers the order of differentiability by `j`. -/
lemma DthIter_contDiffAt {F : ℝ → ℝ → ℝ} {y : ℝ × ℝ} :
    ∀ (j m : ℕ), ContDiffAt ℝ (m + j) (Function.uncurry F) y →
      ContDiffAt ℝ m (Function.uncurry (Work.Spaces.DthIter j F)) y := by
  intro j
  induction j with
  | zero => intro m h; simpa using h
  | succ j ih =>
      intro m h
      have h' : ContDiffAt ℝ ((m + 1) + j) (Function.uncurry F) y := by
        convert h using 1
        push_cast
        ring
      have hG : ContDiffAt ℝ (m + 1) (Function.uncurry (Work.Spaces.DthIter j F)) y :=
        ih (m + 1) h'
      exact Dth_contDiffAt hG

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

/-- The slice derivative `∂_θ` only depends on the values on an open set. -/
lemma pth_congr_isOpen {X Y : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry X) (Function.uncurry Y) V) {p : ℝ × ℝ} (hp : p ∈ V) :
    Work.Spaces.pth X p.1 p.2 = Work.Spaces.pth Y p.1 p.2 := by
  have hnb : ∀ᶠ θ' in 𝓝 p.2, (p.1, θ') ∈ V :=
    (Continuous.prodMk_right p.1).continuousAt.eventually (hV.mem_nhds hp)
  have hslice : (fun θ' => X p.1 θ') =ᶠ[𝓝 p.2] (fun θ' => Y p.1 θ') := by
    filter_upwards [hnb] with θ' hθ'
    exact h hθ'
  have hd := hslice.deriv_eq
  show deriv (fun θ' => X p.1 θ') p.2 = deriv (fun θ' => Y p.1 θ') p.2
  exact hd

/-- Functions that agree on an open set have agreeing `D_θ`-iterates there. -/
lemma DthIter_congr_eqOn {X Y : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry X) (Function.uncurry Y) V) (i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DthIter i X))
      (Function.uncurry (Work.Spaces.DthIter i Y)) V := by
  induction i with
  | zero => exact h
  | succ i ih =>
      intro p hp
      have h1 : Work.Spaces.pth (Work.Spaces.DthIter i X) p.1 p.2
          = Work.Spaces.pth (Work.Spaces.DthIter i Y) p.1 p.2 :=
        pth_congr_isOpen hV ih hp
      show Real.sin (2 * p.2) * Work.Spaces.pth (Work.Spaces.DthIter i X) p.1 p.2
        = Real.sin (2 * p.2) * Work.Spaces.pth (Work.Spaces.DthIter i Y) p.1 p.2
      rw [h1]

/-! ## A single `∂_z` through the iterates of `D_θ` -/

/-- One `∂_z` can be moved through `j` iterated `D_θ`'s, at the cost of one order of
smoothness. -/
lemma pz_DthIter_eq : ∀ (j : ℕ) (F : ℝ → ℝ → ℝ) (y : ℝ × ℝ),
    ContDiffAt ℝ (j + 1) (Function.uncurry F) y →
    Work.Spaces.pz (Work.Spaces.DthIter j F) y.1 y.2
      = Work.Spaces.DthIter j (Work.Spaces.pz F) y.1 y.2 := by
  intro j
  induction j with
  | zero => intro F y h; rfl
  | succ j ih =>
      intro F y h
      have hF2 : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.DthIter j F)) y := by
        have h1 : ContDiffAt ℝ (2 + j) (Function.uncurry F) y := by
          convert h using 1
          push_cast
          ring
        exact DthIter_contDiffAt (F := F) (y := y) j 2 h1
      have hev : Function.uncurry (Work.Spaces.pz (Work.Spaces.DthIter j F))
          =ᶠ[𝓝 y] Function.uncurry (Work.Spaces.DthIter j (Work.Spaces.pz F)) := by
        filter_upwards [h.eventually (by simp)] with y' hy'
        exact ih F y' (hy'.of_le (by exact_mod_cast (show j + 1 ≤ (j + 1) + 1 by omega)))
      have hcl := Work.Spaces.pz_pth_comm (f := Work.Spaces.DthIter j F)
        (z := y.1) (θ := y.2) hF2
      have hstep := pth_congr_ev hev
      have hcoef : Work.Spaces.pz (Work.Spaces.Dth (Work.Spaces.DthIter j F)) y.1 y.2
          = Real.sin (2 * y.2)
              * Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.DthIter j F)) y.1 y.2 := by
        show deriv (fun z' => Real.sin (2 * y.2)
          * Work.Spaces.pth (Work.Spaces.DthIter j F) z' y.2) y.1 = _
        rw [deriv_const_mul_field]
        rfl
      show Work.Spaces.pz (Work.Spaces.Dth (Work.Spaces.DthIter j F)) y.1 y.2
        = Work.Spaces.Dth (Work.Spaces.DthIter j (Work.Spaces.pz F)) y.1 y.2
      rw [hcoef, hcl, hstep]
      rfl

/-! ## The main commutation -/

/-- `∂_z^i` commutes with `D_θ^j`, at the cost of `i + j` orders of smoothness. -/
lemma pzIter_DthIter_comm_aux (n : ℕ) :
    ∀ (i j : ℕ) (F : ℝ → ℝ → ℝ) (y : ℝ × ℝ), i + j ≤ n →
      ContDiffAt ℝ n (Function.uncurry F) y →
      Work.Spaces.pzIter i (Work.Spaces.DthIter j F) y.1 y.2
        = Work.Spaces.DthIter j (Work.Spaces.pzIter i F) y.1 y.2 := by
  intro i
  induction i with
  | zero => intro j F y hij h; rfl
  | succ i ih =>
      intro j F y hij h
      have hij' : i + j ≤ n := by omega
      have hev : Function.uncurry (Work.Spaces.pzIter i (Work.Spaces.DthIter j F))
          =ᶠ[𝓝 y] Function.uncurry (Work.Spaces.DthIter j (Work.Spaces.pzIter i F)) := by
        filter_upwards [h.eventually (by simp)] with y' hy'
        exact ih j F y' hij' hy'
      have hpz := pz_congr_ev hev
      have hG : ContDiffAt ℝ (j + 1) (Function.uncurry (Work.Spaces.pzIter i F)) y := by
        have h1 : ContDiffAt ℝ ((j + 1) + i) (Function.uncurry F) y :=
          h.of_le (by exact_mod_cast (show (j + 1) + i ≤ n by omega))
        exact pzIter_contDiffAt (F := F) (y := y) i (j + 1) h1
      have hA := pz_DthIter_eq j (Work.Spaces.pzIter i F) y hG
      simp only [Work.Spaces.pzIter_succ]
      exact hpz.trans hA

/-- `∂_z^k` commutes with `∂_θ`, at the cost of `k + 1` orders of smoothness. -/
lemma pzIter_pth_eq : ∀ (k : ℕ) (F : ℝ → ℝ → ℝ) (y : ℝ × ℝ),
    ContDiffAt ℝ (k + 1) (Function.uncurry F) y →
    Work.Spaces.pzIter k (Work.Spaces.pth F) y.1 y.2
      = Work.Spaces.pth (Work.Spaces.pzIter k F) y.1 y.2 := by
  intro k
  induction k with
  | zero => intro F y h; rfl
  | succ k ih =>
      intro F y h
      have hF2 : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.pzIter k F)) y := by
        have h1 : ContDiffAt ℝ (2 + k) (Function.uncurry F) y := by
          convert h using 1
          push_cast
          ring
        exact pzIter_contDiffAt (F := F) (y := y) k 2 h1
      have hev : Function.uncurry (Work.Spaces.pzIter k (Work.Spaces.pth F))
          =ᶠ[𝓝 y] Function.uncurry (Work.Spaces.pth (Work.Spaces.pzIter k F)) := by
        filter_upwards [h.eventually (by simp)] with y' hy'
        exact ih F y' (hy'.of_le (by exact_mod_cast (show k + 1 ≤ (k + 1) + 1 by omega)))
      have hpz := pz_congr_ev hev
      have hcl := Work.Spaces.pz_pth_comm (f := Work.Spaces.pzIter k F)
        (z := y.1) (θ := y.2) hF2
      simp only [Work.Spaces.pzIter_succ]
      exact hpz.trans hcl

end PzDthAux

theorem PzDthComm (i k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ)
    (h : ContDiffAt ℝ (k + i + 1) (Function.uncurry f) (z, θ)) :
    Work.Spaces.pzIter k (Work.Spaces.DthIter i (Work.Spaces.pth f)) z θ
      = Work.Spaces.DthIter i (Work.Spaces.pth (Work.Spaces.pzIter k f)) z θ := by
  -- `∂_θ f` is `C^{k+i}`
  have h1 : ContDiffAt ℝ (k + i) (Function.uncurry (Work.Spaces.pth f)) (z, θ) :=
    PzDthAux.pth_contDiffAt (m := k + i) h
  -- `∂_z^k` moves across `D_θ^i`
  have hA : Work.Spaces.pzIter k (Work.Spaces.DthIter i (Work.Spaces.pth f)) z θ
      = Work.Spaces.DthIter i (Work.Spaces.pzIter k (Work.Spaces.pth f)) z θ :=
    PzDthAux.pzIter_DthIter_comm_aux (k + i) k i (Work.Spaces.pth f) (z, θ)
      (by omega) h1
  -- `∂_z^k (∂_θ f) = ∂_θ (∂_z^k f)` on a neighbourhood of the point
  have hk : ContDiffAt ℝ (k + 1) (Function.uncurry f) (z, θ) :=
    h.of_le (by exact_mod_cast (show k + 1 ≤ k + i + 1 by omega))
  have hEv : Function.uncurry (Work.Spaces.pzIter k (Work.Spaces.pth f))
      =ᶠ[𝓝 (z, θ)] Function.uncurry (Work.Spaces.pth (Work.Spaces.pzIter k f)) := by
    filter_upwards [PzDthAux.contDiffAt_eventually_nat (m := k + 1) hk] with y' hy'
    exact PzDthAux.pzIter_pth_eq k f y' hy'
  obtain ⟨W, hWsub, hWopen, hzθW⟩ := mem_nhds_iff.mp
    (show {p : ℝ × ℝ | Function.uncurry (Work.Spaces.pzIter k (Work.Spaces.pth f)) p
        = Function.uncurry (Work.Spaces.pth (Work.Spaces.pzIter k f)) p} ∈ 𝓝 (z, θ) from hEv)
  have hWeq : Set.EqOn (Function.uncurry (Work.Spaces.pzIter k (Work.Spaces.pth f)))
      (Function.uncurry (Work.Spaces.pth (Work.Spaces.pzIter k f))) W :=
    fun p hp => hWsub hp
  -- hence also `D_θ^i (∂_z^k (∂_θ f)) = D_θ^i (∂_θ (∂_z^k f))`
  have hDth := PzDthAux.DthIter_congr_eqOn hWopen hWeq i hzθW
  rw [hA]
  exact hDth

end Work.FTS.PhiStar.FlatWAux
