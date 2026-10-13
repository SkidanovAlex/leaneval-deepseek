/-
Copyright: work module for the Elgindi finite-time singularity project.

# Row 15: the angular limits of the `z`-jets of `𝒰(Φ̃_*)` at `θ = 0⁺`

Let `𝒰 := 𝒰(Φ̃_*) = Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)` be the
coefficient of `∂_θΩ` in the self-similar vorticity equation, evaluated at the elliptic
residual `Φ̃_*` of the `F_*`-package.  This module proves

  `∃ L, Tendsto (fun θ ↦ ∂_z^k 𝒰(z,θ)) (𝓝[>] 0) (𝓝 L)`   for every `k ≤ 5`,

i.e. the right limit at `θ = 0` of every `z`-jet of `𝒰` up to order `5` exists.  This is
the hypothesis `hLim` of `row15_notGood`, which extracts the "first bad angular jet" of the
row 15 estimate.

## The mathematics

`StarPkg.dU` bounds the mixed derivatives: `∂_θ𝒰 ∈ 𝒲^{5,∞}`, i.e.

  `|(z+1)^k ∂_z^k ∂_θ𝒰(z,θ)| ≤ |∂_θ𝒰|_{𝒲^{5,∞}} < ∞`   for `k ≤ 5`, `(z,θ) ∈ [0,∞) × Iθ`.

For fixed `z > 0` and `k ≤ 5` set `g(θ) := ∂_z^k 𝒰(z,θ)`.  The quadrant `(0,π/2)` is open
and `Φ̃_*` is `C^∞` there, so Clairaut's theorem in the form
`∂_θ(∂_z^k𝒰) = ∂_z^k(∂_θ𝒰)` (`Work.Spaces.pz_pth_comm`) identifies

  `g'(θ) = ∂_z^k ∂_θ𝒰(z,θ)`,  so  `|g'| ≤ |∂_θ𝒰|_{𝒲^{5,∞}}`   on `(0,π/2)`.

Thus `g` is Lipschitz on `(0,π/2)`, hence Cauchy along `𝓝[>] 0` (two points `x,y` below `δ`
differ by at most `C·δ` in value), and `ℝ` is complete, so the limit exists.  Note that the
limit need *not* be `0`: only the *boundedness* of the derivative is used, and no continuity
of `𝒰` at `θ = 0` is assumed (that is precisely why the statement is the weak `∃ L`-form).

## Layout

* `row15_smoothQuad_Uop_local`, `row15_smoothQuad_pzIter` — `𝒰` and its `z`-jets are `C^∞`
  on the open quadrant;
* `row15_pth_pzIter_eq_quad` — the Clairaut identity `∂_θ ∂_z^k = ∂_z^k ∂_θ` on the quadrant;
* `row15_tendsto_of_deriv_bounded` — the abstract Lipschitz ⟹ limit lemma (via
  `Cauchy (map g 𝓝[>]0)` and completeness of `ℝ`);
* `row15_pzIter_tendsto` — the statement.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.Uop_PhiTs_slice_zero
import Submission.Work.Spaces.WlInf_terms
import Submission.Work.Spaces.DzDthIterCommOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP.row15aux

set_option autoImplicit false

/-! ## `C^∞`-regularity of `𝒰` and of its `z`-jets on the open quadrant -/

/-- `𝒰 = Uop α ·` preserves `C^∞`-regularity on the open quadrant:
`𝒰(Ψ) = -3Ψ - α z ∂_zΨ`. -/
theorem row15_smoothQuad_Uop_local {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.LocData.SmoothQuad Ψ) :
    Work.FTS.LocData.SmoothQuad (Work.Construction.Uop α Ψ) := by
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => -3 * Function.uncurry Ψ p) Work.Spaces.quadU :=
    (contDiffOn_const (c := (-3 : ℝ))).mul h
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => p.1 * Function.uncurry (Work.Spaces.pz Ψ) p) Work.Spaces.quadU :=
    contDiffOn_fst.mul (Work.FTS.LocData.contDiffOn_pz Work.Spaces.isOpen_quadU h)
  have h3 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => -3 * Function.uncurry Ψ p
        - α * (p.1 * Function.uncurry (Work.Spaces.pz Ψ) p)) Work.Spaces.quadU :=
    h1.sub ((contDiffOn_const (c := α)).mul h2)
  refine h3.congr ?_
  intro p hp
  rcases p with ⟨z, θ⟩
  show Work.Construction.Uop α Ψ z θ
    = -3 * Function.uncurry Ψ (z, θ)
      - α * ((z, θ).1 * Function.uncurry (Work.Spaces.pz Ψ) (z, θ))
  simp only [Work.Construction.Uop, Work.Spaces.pz, Function.uncurry]
  ring

/-- Every `z`-jet of a `SmoothQuad` function is `SmoothQuad`. -/
theorem row15_smoothQuad_pzIter {Ψ : ℝ → ℝ → ℝ} (h : Work.FTS.LocData.SmoothQuad Ψ)
    (m : ℕ) : Work.FTS.LocData.SmoothQuad (Work.Spaces.pzIter m Ψ) := by
  induction m with
  | zero => simpa using h
  | succ n ih =>
    show Work.FTS.LocData.SmoothQuad (Work.Spaces.pz (Work.Spaces.pzIter n Ψ))
    exact Work.FTS.LocData.contDiffOn_pz Work.Spaces.isOpen_quadU ih

/-! ## The Clairaut identity `∂_θ ∂_z^m = ∂_z^m ∂_θ` on the open quadrant -/

/-- On the open quadrant, `∂_θ` commutes with every iterate of `∂_z`. -/
theorem row15_pth_pzIter_eq_quad {Ψ : ℝ → ℝ → ℝ} (h : Work.FTS.LocData.SmoothQuad Ψ)
    (m : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.pth (Work.Spaces.pzIter m Ψ)))
      (Function.uncurry (Work.Spaces.pzIter m (Work.Spaces.pth Ψ))) Work.Spaces.quadU := by
  induction m with
  | zero => intro p hp; rfl
  | succ n ih =>
    intro p hp
    have hsq : Work.FTS.LocData.SmoothQuad (Work.Spaces.pzIter n Ψ) :=
      row15_smoothQuad_pzIter h n
    have h2 : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.pzIter n Ψ)) p :=
      (hsq.contDiffAt (Work.Spaces.isOpen_quadU.mem_nhds hp)).of_le
        (by exact WithTop.coe_le_coe.mpr le_top)
    have key : Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pzIter n Ψ)) p.1 p.2
        = Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.pzIter n Ψ)) p.1 p.2 :=
      (Work.Spaces.pz_pth_comm h2).symm
    show Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pzIter n Ψ)) p.1 p.2
        = Work.Spaces.pz (Work.Spaces.pzIter n (Work.Spaces.pth Ψ)) p.1 p.2
    rw [key]
    exact Work.Spaces.pz_congr_of_isOpen Work.Spaces.isOpen_quadU ih hp

/-! ## A Lipschitz function on `(0,π/2)` has a limit at `0⁺` -/

/-- A function with bounded derivative on `(0,π/2)` is Lipschitz there, hence Cauchy along
`𝓝[>] 0`; since `ℝ` is complete, the right limit at `0` exists. -/
theorem row15_tendsto_of_deriv_bounded {g : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hdiff : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), DifferentiableAt ℝ g θ)
    (hb : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), |deriv g θ| ≤ C) :
    ∃ L : ℝ, Tendsto g (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds L) := by
  have hlip : ∀ a ∈ Set.Ioo (0 : ℝ) (π / 2), ∀ b ∈ Set.Ioo (0 : ℝ) (π / 2),
      |g a - g b| ≤ C * |a - b| := by
    intro a ha b hb'
    have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := g)
      (s := Set.Ioo (0 : ℝ) (π / 2)) (C := C) hdiff
      (fun x hx => by rw [Real.norm_eq_abs]; exact hb x hx) (convex_Ioo 0 (π / 2)) hb' ha
    rwa [Real.norm_eq_abs, Real.norm_eq_abs] at h
  refine cauchy_map_iff_exists_tendsto.mp ?_
  rw [cauchy_map_iff']
  rw [Metric.uniformity_basis_dist.tendsto_right_iff]
  intro ε hε
  set δ : ℝ := ε / (2 * (C + 1)) with hδ
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hmn : 0 < min (π / 2) δ := lt_min (by linarith [Real.pi_pos]) hδpos
  set S : Set ℝ := Set.Ioo (0 : ℝ) (min (π / 2) δ) with hS
  have hSmem : S ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
    have hsub : Set.Ioi (0 : ℝ) ∩ Set.Iio (min (π / 2) δ) = S := rfl
    rw [← hsub]
    exact Filter.inter_mem self_mem_nhdsWithin
      (nhdsWithin_le_nhds (isOpen_Iio.mem_nhds hmn))
  refine Filter.eventually_prod_iff.mpr ⟨fun x => x ∈ S, hSmem, fun y => y ∈ S, hSmem, ?_⟩
  intro x hx y hy
  have hxI : x ∈ Set.Ioo (0 : ℝ) (π / 2) := ⟨hx.1, lt_of_lt_of_le hx.2 (min_le_left _ _)⟩
  have hyI : y ∈ Set.Ioo (0 : ℝ) (π / 2) := ⟨hy.1, lt_of_lt_of_le hy.2 (min_le_left _ _)⟩
  have hxy : |x - y| ≤ min (π / 2) δ := by
    rw [abs_le]
    exact ⟨by linarith [hx.1, hy.2], by linarith [hy.1, hx.2]⟩
  have h1 : |g x - g y| ≤ C * min (π / 2) δ :=
    le_trans (hlip x hxI y hyI) (mul_le_mul_of_nonneg_left hxy hC)
  have h2 : C * min (π / 2) δ ≤ C * δ := mul_le_mul_of_nonneg_left (min_le_right _ _) hC
  have h3 : C * δ < ε := by
    rw [hδ, mul_div, div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (C + 1))]
    nlinarith [hC, hε]
  show dist (g x) (g y) < ε
  rw [Real.dist_eq]
  linarith [h1, h2, h3]

/-! ## The statement -/

theorem row15_pzIter_tendsto {α Cs z : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα1 : α ≤ 1) (hS : Work.FTS.Nonlin.StarPkg α Cs Φs) (hz : 0 < z)
    (k : ℕ) (hk : k ≤ 5) :
    ∃ L : ℝ, Filter.Tendsto (fun θ => Work.Spaces.pzIter k
        (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds L) := by
  set U : ℝ → ℝ → ℝ := Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) with hUdef
  have hsqU : Work.FTS.LocData.SmoothQuad U :=
    row15_smoothQuad_Uop_local (smoothQuad_PhiTs_cc hα hS)
  have hmem : Work.Spaces.WlInfMem α 5 (Work.Spaces.pth U) := hS.dU.1
  have hWnn : 0 ≤ Work.Spaces.WlInf α 5 (Work.Spaces.pth U) := by
    rw [Work.Spaces.WlInf]
    exact add_nonneg (Work.Spaces.wlZSum_nonneg α 5 _ hmem)
      (Work.Spaces.wlThSum_nonneg α 5 _ hmem)
  have hzI : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr (le_of_lt hz)
  have hzq : z ∈ Set.Ioi (-1 : ℝ) := Set.mem_Ioi.mpr (by linarith)
  -- the `θ`-derivative of the `k`-th `z`-jet of `𝒰` is the `k`-th `z`-jet of `∂_θ𝒰`
  have hderiv : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      deriv (fun θ' => Work.Spaces.pzIter k U z θ') θ
        = Work.Spaces.pzIter k (Work.Spaces.pth U) z θ := by
    intro θ hθ
    have hp : (z, θ) ∈ Work.Spaces.quadU := ⟨hzq, hθ⟩
    have hcomm := row15_pth_pzIter_eq_quad hsqU k hp
    show Work.Spaces.pth (Work.Spaces.pzIter k U) z θ
      = Work.Spaces.pzIter k (Work.Spaces.pth U) z θ
    exact hcomm
  -- the uniform bound on that derivative, from `StarPkg.dU`
  have hbnd : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |deriv (fun θ' => Work.Spaces.pzIter k U z θ') θ|
        ≤ Work.Spaces.WlInf α 5 (Work.Spaces.pth U) := by
    intro θ hθ
    rw [hderiv θ hθ]
    have h1 := Work.Spaces.pz_sup_bound α 5 (Work.Spaces.pth U) hmem k hk z θ hzI
      (Set.mem_Icc.mpr ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
    have hpow : (1 : ℝ) ≤ (z + 1) ^ k := one_le_pow₀ (by linarith)
    have hdiv : Work.Spaces.WlInf α 5 (Work.Spaces.pth U) / (z + 1) ^ k
        ≤ Work.Spaces.WlInf α 5 (Work.Spaces.pth U) := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < (z + 1) ^ k)]
      nlinarith [hWnn, hpow]
    linarith [h1, hdiv]
  -- the `θ`-slices of the jet are differentiable on the open interval
  have hdiff : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      DifferentiableAt ℝ (fun θ' => Work.Spaces.pzIter k U z θ') θ := by
    intro θ hθ
    have hsp : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun θ' => Work.Spaces.pzIter k U z θ') (Set.Ioo (0 : ℝ) (π / 2)) :=
      Work.FTS.LocData.SmoothQuad.curry_θ (row15_smoothQuad_pzIter hsqU k) hzq
    exact (hsp.differentiableOn Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
      (isOpen_Ioo.mem_nhds hθ)
  obtain ⟨L, hL⟩ := row15_tendsto_of_deriv_bounded
    (g := fun θ' => Work.Spaces.pzIter k U z θ') hWnn hdiff hbnd
  exact ⟨L, hL⟩

end Work.FTS.Nonlinear.Pieces.RNP.row15aux
