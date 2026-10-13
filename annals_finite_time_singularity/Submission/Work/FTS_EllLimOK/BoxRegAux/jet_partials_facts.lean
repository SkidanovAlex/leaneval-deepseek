import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_EllLimOK.BoxReg
import Submission.Work.Spaces.CurrySmooth

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.BoxRegAux

open Set Filter
open scoped Real Topology

/-! ## Auxiliary objects and lemmas

The six partials of `f` of order `≤ 2` are identified with the `iteratedFDeriv` of
`F = Function.uncurry f` evaluated on the coordinate directions `(1,0)`, `(0,1)`; continuity, the
bounds and the Lipschitz bounds are all read off from the operator norms of
`iteratedFDeriv ℝ k F` (and its derivative).  The key structural facts used are

* `iteratedFDeriv_one_apply` / `iteratedFDeriv_succ_apply_left`, which express the evaluations of
  `iteratedFDeriv` on a `Fin n`-tuple of directions;
* `fderiv_continuousMultilinear_apply_const`, which computes the derivative of
  `p ↦ iteratedFDeriv ℝ n F p m` at fixed `m` as `(fderiv (iteratedFDeriv ℝ n F) p).flipMultilinear m`;
* `norm_fderiv_iteratedFDeriv`, giving `‖fderiv (iteratedFDeriv ℝ n F) p‖ = ‖iteratedFDeriv ℝ (n+1) F p‖`;
* the mean value inequality `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le` on the convex box.

Everything here is `sorry`-free. -/

/-- The open smoothness set `(-1,∞) × (-1, π/2+1)` of the hypothesis. -/
abbrev nbhU : Set (ℝ × ℝ) := Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1)

/-- The coordinate direction `e_z = (1,0)`. -/
def dz : ℝ × ℝ := (1, 0)

/-- The coordinate direction `e_θ = (0,1)`. -/
def dth : ℝ × ℝ := (0, 1)

/-- The constant family `Fin 1 → ℝ × ℝ` with value `u`. -/
def dir1 (u : ℝ × ℝ) : Fin 1 → ℝ × ℝ := fun _ => u

/-- Prepending `u` to a family `m : Fin n → ℝ × ℝ`. -/
def consD {n : ℕ} (u : ℝ × ℝ) (m : Fin n → ℝ × ℝ) : Fin (n + 1) → ℝ × ℝ := Fin.cases u m

theorem nbhU_open : IsOpen nbhU := isOpen_Ioi.prod isOpen_Ioo

theorem norm_dz_le_one : ‖dz‖ ≤ 1 := by simp [dz, Prod.norm_def]

theorem norm_dth_le_one : ‖dth‖ ≤ 1 := by simp [dth, Prod.norm_def]

/-- The product of the norms of a constant `Fin 1`-family. -/
theorem prod_dir1_le_one (u : ℝ × ℝ) (hu : ‖u‖ ≤ 1) : ∏ i : Fin 1, ‖dir1 u i‖ ≤ 1 := by
  rw [Fin.prod_univ_succ]; simpa [dir1] using hu

/-- The product of the norms of `Fin.cons w (fun _ => u)`. -/
theorem prod_consD_dir1_le_one (u w : ℝ × ℝ) (hu : ‖u‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    ∏ i : Fin 2, ‖consD w (dir1 u) i‖ ≤ 1 := by
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp only [Fin.prod_univ_zero, mul_one, consD, dir1, Fin.cases_zero, Fin.cases_succ]
  nlinarith [norm_nonneg u, norm_nonneg w]

/-- The closed box lies in the open smoothness set. -/
theorem cbox_subset_nbhU {a b : ℝ} (ha : 0 < a) : Work.FTS_EllLimOK.cbox a b ⊆ nbhU := by
  intro p hp
  rw [Work.FTS_EllLimOK.mem_cbox] at hp
  refine ⟨lt_of_lt_of_le (by linarith : (-1:ℝ) < a) hp.1.1, ?_⟩
  exact ⟨by linarith [hp.2.1], by linarith [hp.2.2, Real.pi_pos]⟩

/-- The closed box is convex. -/
theorem convex_cbox (a b : ℝ) : Convex ℝ (Work.FTS_EllLimOK.cbox a b) :=
  Convex.prod (convex_Icc a b : Convex ℝ (Set.Icc a b))
    (convex_Icc (0:ℝ) (Real.pi / 2) : Convex ℝ (Set.Icc (0:ℝ) (Real.pi / 2)))

/-- Continuity of `p ↦ iteratedFDeriv ℝ n F p m` on the open smoothness set. -/
theorem continuousOn_iterDF {F : ℝ × ℝ → ℝ} {n : ℕ} (hsm : ContDiffOn ℝ 4 F nbhU) (hn : n ≤ 4)
    (m : Fin n → ℝ × ℝ) :
    ContinuousOn (fun p => iteratedFDeriv ℝ n F p m) nbhU := by
  have hK : ContinuousOn (iteratedFDeriv ℝ n F) nbhU :=
    ContinuousOn.continuousOn_iteratedFDeriv hsm nbhU_open (k := n) (by exact_mod_cast hn)
  exact (continuous_eval_const m).comp_continuousOn hK

/-- Differentiability of `iteratedFDeriv ℝ n F` (`n ≤ 3`) inside the smoothness set. -/
theorem differentiableAt_iterDF {F : ℝ × ℝ → ℝ} {n : ℕ} (hsm : ContDiffOn ℝ 4 F nbhU)
    (hn : n ≤ 3) {p : ℝ × ℝ} (hp : p ∈ nbhU) : DifferentiableAt ℝ (iteratedFDeriv ℝ n F) p := by
  have hcd : ContDiffAt ℝ 4 F p := hsm.contDiffAt (nbhU_open.mem_nhds hp)
  have h : ContDiffAt ℝ (1 : WithTop ℕ∞) (iteratedFDeriv ℝ n F) p :=
    hcd.iteratedFDeriv_right (m := (1 : WithTop ℕ∞)) (i := n)
      (by exact_mod_cast (by omega : 1 + n ≤ 4))
  exact h.differentiableAt (by norm_num)

/-- **Norm bound for the Fréchet derivative** of `p ↦ iteratedFDeriv ℝ n F p m`: it is at most
`‖iteratedFDeriv ℝ (n+1) F p‖ · ∏ ‖m i‖`. -/
theorem norm_fderiv_iterDF_apply_le {F : ℝ × ℝ → ℝ} {n : ℕ} {p : ℝ × ℝ} {m : Fin n → ℝ × ℝ}
    {C : ℝ} (hC : 0 ≤ C) (hprod : ∏ i, ‖m i‖ ≤ 1)
    (hK : ‖iteratedFDeriv ℝ (n + 1) F p‖ ≤ C)
    (hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ n F) p) :
    ‖fderiv ℝ (fun q => iteratedFDeriv ℝ n F q m) p‖ ≤ C := by
  rw [fderiv_continuousMultilinear_apply_const hdiff m]
  refine ContinuousLinearMap.opNorm_le_bound _ hC (fun u => ?_)
  rw [ContinuousLinearMap.flipMultilinear_apply_apply]
  have hprod0 : 0 ≤ ∏ i, ‖m i‖ := Finset.prod_nonneg (fun i _ => norm_nonneg _)
  have h1 : ‖(fderiv ℝ (iteratedFDeriv ℝ n F) p u) m‖
      ≤ ‖fderiv ℝ (iteratedFDeriv ℝ n F) p u‖ * ∏ i, ‖m i‖ :=
    ContinuousMultilinearMap.le_opNorm _ _
  have h2 : ‖fderiv ℝ (iteratedFDeriv ℝ n F) p u‖
      ≤ ‖fderiv ℝ (iteratedFDeriv ℝ n F) p‖ * ‖u‖ := ContinuousLinearMap.le_opNorm _ _
  have h3 : ‖fderiv ℝ (iteratedFDeriv ℝ n F) p‖ ≤ C := by
    rw [norm_fderiv_iteratedFDeriv]; exact hK
  nlinarith [norm_nonneg u, h1, h2, h3, hprod, hprod0,
    norm_nonneg ((fderiv ℝ (iteratedFDeriv ℝ n F) p) u)]

/-- **Pointwise bound** for `iteratedFDeriv ℝ n F · m` on the box from the operator-norm bound. -/
theorem abs_iterDF_apply_le {F : ℝ × ℝ → ℝ} {a b C : ℝ} {n : ℕ} (_hC : 0 ≤ C)
    (hb : ∀ p ∈ Work.FTS_EllLimOK.cbox a b, ‖iteratedFDeriv ℝ n F p‖ ≤ C)
    {m : Fin n → ℝ × ℝ} (hprod : ∏ i, ‖m i‖ ≤ 1) :
    ∀ p ∈ Work.FTS_EllLimOK.cbox a b, |iteratedFDeriv ℝ n F p m| ≤ C := by
  intro p hp
  have h1 : ‖iteratedFDeriv ℝ n F p m‖ ≤ ‖iteratedFDeriv ℝ n F p‖ * ∏ i, ‖m i‖ :=
    ContinuousMultilinearMap.le_opNorm _ _
  have hprod0 : 0 ≤ ∏ i, ‖m i‖ := Finset.prod_nonneg (fun i _ => norm_nonneg _)
  have h3 : ‖iteratedFDeriv ℝ n F p m‖ ≤ C := by
    nlinarith [h1, hb p hp, hprod, hprod0, norm_nonneg (iteratedFDeriv ℝ n F p)]
  simpa [Real.norm_eq_abs] using h3

/-- **Lipschitz bound** for `iteratedFDeriv ℝ n F · m` on the box (`n ≤ 2`), from the mean value
inequality applied to the continuously differentiable function `p ↦ iteratedFDeriv ℝ n F p m`. -/
theorem lipschitz_iterDF {F : ℝ × ℝ → ℝ} {a b C : ℝ} (hsm : ContDiffOn ℝ 4 F nbhU)
    (hbox : Work.FTS_EllLimOK.cbox a b ⊆ nbhU) (hC : 0 ≤ C) {n : ℕ} (hn : n ≤ 2)
    (hb : ∀ p ∈ Work.FTS_EllLimOK.cbox a b, ‖iteratedFDeriv ℝ (n + 1) F p‖ ≤ C)
    {m : Fin n → ℝ × ℝ} (hprod : ∏ i, ‖m i‖ ≤ 1) :
    ∀ p ∈ Work.FTS_EllLimOK.cbox a b, ∀ q ∈ Work.FTS_EllLimOK.cbox a b,
      |iteratedFDeriv ℝ n F p m - iteratedFDeriv ℝ n F q m| ≤ C * ‖p - q‖ := by
  intro p hp q hq
  have hdiff : ∀ r ∈ Work.FTS_EllLimOK.cbox a b, DifferentiableAt ℝ (iteratedFDeriv ℝ n F) r :=
    fun r hr => differentiableAt_iterDF hsm (by omega) (hbox hr)
  have hderiv : ∀ r ∈ Work.FTS_EllLimOK.cbox a b,
      HasFDerivWithinAt (fun s => iteratedFDeriv ℝ n F s m)
        ((fderiv ℝ (iteratedFDeriv ℝ n F) r).flipMultilinear m) (Work.FTS_EllLimOK.cbox a b) r :=
    fun r hr => ((hdiff r hr).hasFDerivAt.continuousMultilinear_apply_const m).hasFDerivWithinAt
  have hbound : ∀ r ∈ Work.FTS_EllLimOK.cbox a b,
      ‖(fderiv ℝ (iteratedFDeriv ℝ n F) r).flipMultilinear m‖ ≤ C := by
    intro r hr
    rw [← fderiv_continuousMultilinear_apply_const (hdiff r hr) m]
    exact norm_fderiv_iterDF_apply_le hC hprod (hb r hr) (hdiff r hr)
  have key := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hderiv hbound
    (convex_cbox a b) hp hq
  simpa [Real.norm_eq_abs, norm_neg, norm_sub_rev] using key

/-! ## The identification of the partials with `iteratedFDeriv` -/

/-- The `z`-partial is `iteratedFDeriv ℝ 1 F` on the direction family `dir1 dz`. -/
theorem pz_eq_iterDF1 {f : ℝ → ℝ → ℝ} (hsm : ContDiffOn ℝ 4 (Function.uncurry f) nbhU) :
    ∀ p ∈ nbhU, Work.Spaces.pz f p.1 p.2
      = iteratedFDeriv ℝ 1 (Function.uncurry f) p (dir1 dz) := by
  intro p hp
  rw [Work.Spaces.pz_eq_fderiv
    ((hsm.contDiffAt (nbhU_open.mem_nhds hp)).differentiableAt (by norm_num))]
  simp [iteratedFDeriv_one_apply, dir1, dz]

/-- The `θ`-partial is `iteratedFDeriv ℝ 1 F` on the direction family `dir1 dth`. -/
theorem pth_eq_iterDF1 {f : ℝ → ℝ → ℝ} (hsm : ContDiffOn ℝ 4 (Function.uncurry f) nbhU) :
    ∀ p ∈ nbhU, Work.Spaces.pth f p.1 p.2
      = iteratedFDeriv ℝ 1 (Function.uncurry f) p (dir1 dth) := by
  intro p hp
  rw [Work.Spaces.pth_eq_fderiv
    ((hsm.contDiffAt (nbhU_open.mem_nhds hp)).differentiableAt (by norm_num))]
  simp [iteratedFDeriv_one_apply, dir1, dth]

/-- The eventual-equality form of `pz_eq_iterDF1`. -/
theorem evEq_uncurry_pz {f : ℝ → ℝ → ℝ} (hsm : ContDiffOn ℝ 4 (Function.uncurry f) nbhU) :
    EqOn (Function.uncurry (Work.Spaces.pz f))
      (fun p => iteratedFDeriv ℝ 1 (Function.uncurry f) p (dir1 dz)) nbhU := by
  intro p hp
  change Work.Spaces.pz f p.1 p.2 = _
  exact pz_eq_iterDF1 hsm p hp

/-- The eventual-equality form of `pth_eq_iterDF1`. -/
theorem evEq_uncurry_pth {f : ℝ → ℝ → ℝ} (hsm : ContDiffOn ℝ 4 (Function.uncurry f) nbhU) :
    EqOn (Function.uncurry (Work.Spaces.pth f))
      (fun p => iteratedFDeriv ℝ 1 (Function.uncurry f) p (dir1 dth)) nbhU := by
  intro p hp
  change Work.Spaces.pth f p.1 p.2 = _
  exact pth_eq_iterDF1 hsm p hp

/-- **The Fréchet derivative of the first partial in an arbitrary direction `w`**: for a function
`g` whose uncurried form agrees with `q ↦ iteratedFDeriv ℝ 1 F q (dir1 u)` near `p`, the
derivative in the direction `w` is the `iteratedFDeriv ℝ 2` evaluated on the two directions `w`
and `u`. -/
theorem fderiv_uncurry_eq_iterDF2 {f g : ℝ → ℝ → ℝ}
    (hsm : ContDiffOn ℝ 4 (Function.uncurry f) nbhU) {p : ℝ × ℝ} (hp : p ∈ nbhU)
    {u : ℝ × ℝ}
    (hg : Function.uncurry g =ᶠ[𝓝 p]
      (fun q => iteratedFDeriv ℝ 1 (Function.uncurry f) q (dir1 u)))
    (w : ℝ × ℝ) :
    fderiv ℝ (Function.uncurry g) p w
      = iteratedFDeriv ℝ 2 (Function.uncurry f) p (consD w (dir1 u)) := by
  have hK1diff : DifferentiableAt ℝ (iteratedFDeriv ℝ 1 (Function.uncurry f)) p :=
    differentiableAt_iterDF hsm (by norm_num) hp
  rw [hg.fderiv_eq, fderiv_continuousMultilinear_apply_const hK1diff,
    ContinuousLinearMap.flipMultilinear_apply_apply, iteratedFDeriv_succ_apply_left]
  rfl

/-- The eventual-equality form of `evEq_uncurry_pz`. -/
theorem evEqAt_uncurry_pz {f : ℝ → ℝ → ℝ} (hsm : ContDiffOn ℝ 4 (Function.uncurry f) nbhU)
    {p : ℝ × ℝ} (hp : p ∈ nbhU) :
    Function.uncurry (Work.Spaces.pz f) =ᶠ[𝓝 p]
      (fun q => iteratedFDeriv ℝ 1 (Function.uncurry f) q (dir1 dz)) := by
  filter_upwards [nbhU_open.mem_nhds hp] with q hq
  exact evEq_uncurry_pz hsm hq

/-- The eventual-equality form of `evEq_uncurry_pth`. -/
theorem evEqAt_uncurry_pth {f : ℝ → ℝ → ℝ} (hsm : ContDiffOn ℝ 4 (Function.uncurry f) nbhU)
    {p : ℝ × ℝ} (hp : p ∈ nbhU) :
    Function.uncurry (Work.Spaces.pth f) =ᶠ[𝓝 p]
      (fun q => iteratedFDeriv ℝ 1 (Function.uncurry f) q (dir1 dth)) := by
  filter_upwards [nbhU_open.mem_nhds hp] with q hq
  exact evEq_uncurry_pth hsm hq

/-- `∂_z∂_z f` as an `iteratedFDeriv ℝ 2`. -/
theorem pz_pz_eq {f : ℝ → ℝ → ℝ} (hsm : ContDiffOn ℝ 4 (Function.uncurry f) nbhU)
    {p : ℝ × ℝ} (hp : p ∈ nbhU) :
    Work.Spaces.pz (Work.Spaces.pz f) p.1 p.2
      = iteratedFDeriv ℝ 2 (Function.uncurry f) p (consD dz (dir1 dz)) := by
  have hdiff : DifferentiableAt ℝ (Function.uncurry (Work.Spaces.pz f)) p :=
    DifferentiableAt.congr_of_eventuallyEq
      ((differentiableAt_iterDF hsm (by norm_num) hp).continuousMultilinear_apply_const (dir1 dz))
      (evEqAt_uncurry_pz hsm hp)
  rw [Work.Spaces.pz_eq_fderiv hdiff]
  change fderiv ℝ (Function.uncurry (Work.Spaces.pz f)) p dz = _
  rw [fderiv_uncurry_eq_iterDF2 hsm hp (evEqAt_uncurry_pz hsm hp) dz]

/-- `∂_θ∂_z f` as an `iteratedFDeriv ℝ 2`. -/
theorem pth_pz_eq {f : ℝ → ℝ → ℝ} (hsm : ContDiffOn ℝ 4 (Function.uncurry f) nbhU)
    {p : ℝ × ℝ} (hp : p ∈ nbhU) :
    Work.Spaces.pth (Work.Spaces.pz f) p.1 p.2
      = iteratedFDeriv ℝ 2 (Function.uncurry f) p (consD dth (dir1 dz)) := by
  have hdiff : DifferentiableAt ℝ (Function.uncurry (Work.Spaces.pz f)) p :=
    DifferentiableAt.congr_of_eventuallyEq
      ((differentiableAt_iterDF hsm (by norm_num) hp).continuousMultilinear_apply_const (dir1 dz))
      (evEqAt_uncurry_pz hsm hp)
  rw [Work.Spaces.pth_eq_fderiv hdiff]
  change fderiv ℝ (Function.uncurry (Work.Spaces.pz f)) p dth = _
  rw [fderiv_uncurry_eq_iterDF2 hsm hp (evEqAt_uncurry_pz hsm hp) dth]

/-- `∂_z∂_θ f` as an `iteratedFDeriv ℝ 2`. -/
theorem pz_pth_eq {f : ℝ → ℝ → ℝ} (hsm : ContDiffOn ℝ 4 (Function.uncurry f) nbhU)
    {p : ℝ × ℝ} (hp : p ∈ nbhU) :
    Work.Spaces.pz (Work.Spaces.pth f) p.1 p.2
      = iteratedFDeriv ℝ 2 (Function.uncurry f) p (consD dz (dir1 dth)) := by
  have hdiff : DifferentiableAt ℝ (Function.uncurry (Work.Spaces.pth f)) p :=
    DifferentiableAt.congr_of_eventuallyEq
      ((differentiableAt_iterDF hsm (by norm_num) hp).continuousMultilinear_apply_const (dir1 dth))
      (evEqAt_uncurry_pth hsm hp)
  rw [Work.Spaces.pz_eq_fderiv hdiff]
  change fderiv ℝ (Function.uncurry (Work.Spaces.pth f)) p dz = _
  rw [fderiv_uncurry_eq_iterDF2 hsm hp (evEqAt_uncurry_pth hsm hp) dz]

/-- `∂_θ∂_θ f` as an `iteratedFDeriv ℝ 2`. -/
theorem pth_pth_eq {f : ℝ → ℝ → ℝ} (hsm : ContDiffOn ℝ 4 (Function.uncurry f) nbhU)
    {p : ℝ × ℝ} (hp : p ∈ nbhU) :
    Work.Spaces.pth (Work.Spaces.pth f) p.1 p.2
      = iteratedFDeriv ℝ 2 (Function.uncurry f) p (consD dth (dir1 dth)) := by
  have hdiff : DifferentiableAt ℝ (Function.uncurry (Work.Spaces.pth f)) p :=
    DifferentiableAt.congr_of_eventuallyEq
      ((differentiableAt_iterDF hsm (by norm_num) hp).continuousMultilinear_apply_const (dir1 dth))
      (evEqAt_uncurry_pth hsm hp)
  rw [Work.Spaces.pth_eq_fderiv hdiff]
  change fderiv ℝ (Function.uncurry (Work.Spaces.pth f)) p dth = _
  rw [fderiv_uncurry_eq_iterDF2 hsm hp (evEqAt_uncurry_pth hsm hp) dth]

/-- **The six order-`≤ 2` partials of `f`: continuity, bounds and Lipschitz bounds on the closed
box.**  For `f` of class `C⁴` on the open neighbourhood `(-1,∞) × (-1, π/2+1)` of the closed box
`cbox a b = [a,b] × [0,π/2]` (with `0 < a ≤ b`, so the box lies strictly inside the smoothness
region) whose iterated Fréchet derivatives of order `k ≤ 3` are bounded by `C` on the box, the six
partials `∂_z f`, `∂_θ f`, `∂_z∂_z f`, `∂_θ∂_z f`, `∂_z∂_θ f`, `∂_θ∂_θ f` are continuous on the box,
bounded by `C` on the box, and `C`-Lipschitz on the box.

Intended proof: `Work.Spaces.pz_eq_fderiv`/`pth_eq_fderiv` identify the first partials with the
Fréchet derivative evaluated at `(1,0)`, resp. `(0,1)`; then
`iteratedFDeriv_succ_eq_comp_left` together with the fact that
`continuousMultilinearCurryLeftEquiv` is a *linear isometry equivalence* identifies
`fderiv ℝ (fderiv ℝ (uncurry f)) p` with `iteratedFDeriv ℝ 2 (uncurry f) p` (up to the isometry),
and likewise one level higher; the bounds are then immediate from the operator norms and the
Lipschitz bounds from the mean value theorem
(`Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le`) applied to
`fderiv ℝ (uncurry f)` and to `fderiv ℝ (fderiv ℝ (uncurry f))` on the convex box.  The second
partials like `∂_θ∂_z f` are the `(1,0)`-component of the Fréchet derivative of the function
`p ↦ ∂_z f p.1 p.2`, which is `ev_{(1,0)} ∘ fderiv ℝ (fderiv ℝ (uncurry f))` on the neighbourhood
of the box.  Please write the file in the namespace `Work.FTS_EllLimOK`. -/
theorem jet_partials_facts {f : ℝ → ℝ → ℝ} {a b C : ℝ} (hC : 0 ≤ C) (ha : 0 < a) (hab : a ≤ b)
    (hsm : ContDiffOn ℝ 4 (Function.uncurry f) (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1)))
    (hbnd : ∀ k : ℕ, k ≤ 3 → ∀ p ∈ Work.FTS_EllLimOK.cbox a b,
      ‖iteratedFDeriv ℝ k (Function.uncurry f) p‖ ≤ C) :
    (ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz f p.1 p.2) (Work.FTS_EllLimOK.cbox a b) ∧
     ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pth f p.1 p.2) (Work.FTS_EllLimOK.cbox a b) ∧
     ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz (Work.Spaces.pz f) p.1 p.2)
       (Work.FTS_EllLimOK.cbox a b) ∧
     ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pth (Work.Spaces.pz f) p.1 p.2)
       (Work.FTS_EllLimOK.cbox a b) ∧
     ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz (Work.Spaces.pth f) p.1 p.2)
       (Work.FTS_EllLimOK.cbox a b) ∧
     ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pth (Work.Spaces.pth f) p.1 p.2)
       (Work.FTS_EllLimOK.cbox a b)) ∧
    (∀ p ∈ Work.FTS_EllLimOK.cbox a b,
      |Work.Spaces.pz f p.1 p.2| ≤ C ∧ |Work.Spaces.pth f p.1 p.2| ≤ C ∧
      |Work.Spaces.pz (Work.Spaces.pz f) p.1 p.2| ≤ C ∧
      |Work.Spaces.pth (Work.Spaces.pz f) p.1 p.2| ≤ C ∧
      |Work.Spaces.pz (Work.Spaces.pth f) p.1 p.2| ≤ C ∧
      |Work.Spaces.pth (Work.Spaces.pth f) p.1 p.2| ≤ C) ∧
    (∀ p ∈ Work.FTS_EllLimOK.cbox a b, ∀ q ∈ Work.FTS_EllLimOK.cbox a b,
      |Work.Spaces.pz f p.1 p.2 - Work.Spaces.pz f q.1 q.2| ≤ C * ‖p - q‖ ∧
      |Work.Spaces.pth f p.1 p.2 - Work.Spaces.pth f q.1 q.2| ≤ C * ‖p - q‖ ∧
      |Work.Spaces.pz (Work.Spaces.pz f) p.1 p.2 - Work.Spaces.pz (Work.Spaces.pz f) q.1 q.2|
        ≤ C * ‖p - q‖ ∧
      |Work.Spaces.pth (Work.Spaces.pz f) p.1 p.2 - Work.Spaces.pth (Work.Spaces.pz f) q.1 q.2|
        ≤ C * ‖p - q‖ ∧
      |Work.Spaces.pz (Work.Spaces.pth f) p.1 p.2 - Work.Spaces.pz (Work.Spaces.pth f) q.1 q.2|
        ≤ C * ‖p - q‖ ∧
      |Work.Spaces.pth (Work.Spaces.pth f) p.1 p.2 - Work.Spaces.pth (Work.Spaces.pth f) q.1 q.2|
        ≤ C * ‖p - q‖) := by
  have hbox : Work.FTS_EllLimOK.cbox a b ⊆ nbhU := cbox_subset_nbhU ha
  -- continuity of the six witness functions on the open set
  have hEpz : EqOn (fun p : ℝ × ℝ => Work.Spaces.pz f p.1 p.2)
      (fun p => iteratedFDeriv ℝ 1 (Function.uncurry f) p (dir1 dz)) (Work.FTS_EllLimOK.cbox a b) :=
    (evEq_uncurry_pz hsm).mono hbox
  have hEpth : EqOn (fun p : ℝ × ℝ => Work.Spaces.pth f p.1 p.2)
      (fun p => iteratedFDeriv ℝ 1 (Function.uncurry f) p (dir1 dth)) (Work.FTS_EllLimOK.cbox a b) :=
    (evEq_uncurry_pth hsm).mono hbox
  -- bounds for the witnesses
  have hbz : ∀ p ∈ Work.FTS_EllLimOK.cbox a b,
      |iteratedFDeriv ℝ 1 (Function.uncurry f) p (dir1 dz)| ≤ C :=
    abs_iterDF_apply_le hC (hbnd 1 (by norm_num)) (prod_dir1_le_one dz norm_dz_le_one)
  have hbt : ∀ p ∈ Work.FTS_EllLimOK.cbox a b,
      |iteratedFDeriv ℝ 1 (Function.uncurry f) p (dir1 dth)| ≤ C :=
    abs_iterDF_apply_le hC (hbnd 1 (by norm_num)) (prod_dir1_le_one dth norm_dth_le_one)
  have hbzz : ∀ p ∈ Work.FTS_EllLimOK.cbox a b,
      |iteratedFDeriv ℝ 2 (Function.uncurry f) p (consD dz (dir1 dz))| ≤ C :=
    abs_iterDF_apply_le hC (hbnd 2 (by norm_num))
      (prod_consD_dir1_le_one dz dz norm_dz_le_one norm_dz_le_one)
  have hbtz : ∀ p ∈ Work.FTS_EllLimOK.cbox a b,
      |iteratedFDeriv ℝ 2 (Function.uncurry f) p (consD dth (dir1 dz))| ≤ C :=
    abs_iterDF_apply_le hC (hbnd 2 (by norm_num))
      (prod_consD_dir1_le_one dz dth norm_dz_le_one norm_dth_le_one)
  have hbzt : ∀ p ∈ Work.FTS_EllLimOK.cbox a b,
      |iteratedFDeriv ℝ 2 (Function.uncurry f) p (consD dz (dir1 dth))| ≤ C :=
    abs_iterDF_apply_le hC (hbnd 2 (by norm_num))
      (prod_consD_dir1_le_one dth dz norm_dth_le_one norm_dz_le_one)
  have hbtt : ∀ p ∈ Work.FTS_EllLimOK.cbox a b,
      |iteratedFDeriv ℝ 2 (Function.uncurry f) p (consD dth (dir1 dth))| ≤ C :=
    abs_iterDF_apply_le hC (hbnd 2 (by norm_num))
      (prod_consD_dir1_le_one dth dth norm_dth_le_one norm_dth_le_one)
  -- Lipschitz bounds for the witnesses
  have hlz : ∀ p ∈ Work.FTS_EllLimOK.cbox a b, ∀ q ∈ Work.FTS_EllLimOK.cbox a b,
      |iteratedFDeriv ℝ 1 (Function.uncurry f) p (dir1 dz)
        - iteratedFDeriv ℝ 1 (Function.uncurry f) q (dir1 dz)| ≤ C * ‖p - q‖ :=
    lipschitz_iterDF hsm hbox hC (by norm_num) (hbnd 2 (by norm_num))
      (prod_dir1_le_one dz norm_dz_le_one)
  have hlt : ∀ p ∈ Work.FTS_EllLimOK.cbox a b, ∀ q ∈ Work.FTS_EllLimOK.cbox a b,
      |iteratedFDeriv ℝ 1 (Function.uncurry f) p (dir1 dth)
        - iteratedFDeriv ℝ 1 (Function.uncurry f) q (dir1 dth)| ≤ C * ‖p - q‖ :=
    lipschitz_iterDF hsm hbox hC (by norm_num) (hbnd 2 (by norm_num))
      (prod_dir1_le_one dth norm_dth_le_one)
  have hlzz : ∀ p ∈ Work.FTS_EllLimOK.cbox a b, ∀ q ∈ Work.FTS_EllLimOK.cbox a b,
      |iteratedFDeriv ℝ 2 (Function.uncurry f) p (consD dz (dir1 dz))
        - iteratedFDeriv ℝ 2 (Function.uncurry f) q (consD dz (dir1 dz))| ≤ C * ‖p - q‖ :=
    lipschitz_iterDF hsm hbox hC (by norm_num) (hbnd 3 (by norm_num))
      (prod_consD_dir1_le_one dz dz norm_dz_le_one norm_dz_le_one)
  have hltz : ∀ p ∈ Work.FTS_EllLimOK.cbox a b, ∀ q ∈ Work.FTS_EllLimOK.cbox a b,
      |iteratedFDeriv ℝ 2 (Function.uncurry f) p (consD dth (dir1 dz))
        - iteratedFDeriv ℝ 2 (Function.uncurry f) q (consD dth (dir1 dz))| ≤ C * ‖p - q‖ :=
    lipschitz_iterDF hsm hbox hC (by norm_num) (hbnd 3 (by norm_num))
      (prod_consD_dir1_le_one dz dth norm_dz_le_one norm_dth_le_one)
  have hlzt : ∀ p ∈ Work.FTS_EllLimOK.cbox a b, ∀ q ∈ Work.FTS_EllLimOK.cbox a b,
      |iteratedFDeriv ℝ 2 (Function.uncurry f) p (consD dz (dir1 dth))
        - iteratedFDeriv ℝ 2 (Function.uncurry f) q (consD dz (dir1 dth))| ≤ C * ‖p - q‖ :=
    lipschitz_iterDF hsm hbox hC (by norm_num) (hbnd 3 (by norm_num))
      (prod_consD_dir1_le_one dth dz norm_dth_le_one norm_dz_le_one)
  have hltt : ∀ p ∈ Work.FTS_EllLimOK.cbox a b, ∀ q ∈ Work.FTS_EllLimOK.cbox a b,
      |iteratedFDeriv ℝ 2 (Function.uncurry f) p (consD dth (dir1 dth))
        - iteratedFDeriv ℝ 2 (Function.uncurry f) q (consD dth (dir1 dth))| ≤ C * ‖p - q‖ :=
    lipschitz_iterDF hsm hbox hC (by norm_num) (hbnd 3 (by norm_num))
      (prod_consD_dir1_le_one dth dth norm_dth_le_one norm_dth_le_one)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact ((continuousOn_iterDF hsm (by norm_num) (dir1 dz)).mono hbox).congr hEpz
  · exact ((continuousOn_iterDF hsm (by norm_num) (dir1 dth)).mono hbox).congr hEpth
  · exact ((continuousOn_iterDF hsm (by norm_num) (consD dz (dir1 dz))).mono hbox).congr
      (fun p hp => pz_pz_eq hsm (hbox hp))
  · exact ((continuousOn_iterDF hsm (by norm_num) (consD dth (dir1 dz))).mono hbox).congr
      (fun p hp => pth_pz_eq hsm (hbox hp))
  · exact ((continuousOn_iterDF hsm (by norm_num) (consD dz (dir1 dth))).mono hbox).congr
      (fun p hp => pz_pth_eq hsm (hbox hp))
  · exact ((continuousOn_iterDF hsm (by norm_num) (consD dth (dir1 dth))).mono hbox).congr
      (fun p hp => pth_pth_eq hsm (hbox hp))
  · intro p hp
    exact ⟨by rw [pz_eq_iterDF1 hsm p (hbox hp)]; exact hbz p hp,
           by rw [pth_eq_iterDF1 hsm p (hbox hp)]; exact hbt p hp,
           by rw [pz_pz_eq hsm (hbox hp)]; exact hbzz p hp,
           by rw [pth_pz_eq hsm (hbox hp)]; exact hbtz p hp,
           by rw [pz_pth_eq hsm (hbox hp)]; exact hbzt p hp,
           by rw [pth_pth_eq hsm (hbox hp)]; exact hbtt p hp⟩
  · intro p hp q hq
    exact ⟨by rw [pz_eq_iterDF1 hsm p (hbox hp), pz_eq_iterDF1 hsm q (hbox hq)]
              exact hlz p hp q hq,
           by rw [pth_eq_iterDF1 hsm p (hbox hp), pth_eq_iterDF1 hsm q (hbox hq)]
              exact hlt p hp q hq,
           by rw [pz_pz_eq hsm (hbox hp), pz_pz_eq hsm (hbox hq)]
              exact hlzz p hp q hq,
           by rw [pth_pz_eq hsm (hbox hp), pth_pz_eq hsm (hbox hq)]
              exact hltz p hp q hq,
           by rw [pz_pth_eq hsm (hbox hp), pz_pth_eq hsm (hbox hq)]
              exact hlzt p hp q hq,
           by rw [pth_pth_eq hsm (hbox hp), pth_pth_eq hsm (hbox hq)]
              exact hltt p hp q hq⟩

end Work.FTS_EllLimOK.BoxRegAux
