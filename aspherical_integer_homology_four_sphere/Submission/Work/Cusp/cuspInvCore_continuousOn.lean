/-
# Continuity of the inverse of the core chart

`cuspInvCore v : E4 → E2 × E2` (`Work.Cusp.Basic`) is the explicit inverse of the core chart
`ThetaCore v` of the `v`-th cusp: from the Cartesian coordinates `q = (a, b, w₁, w₂)` it recovers
`r = √(a²+b²)`, `θ = argOf b a = atan2 b a`, and then runs the inner-chart inverse `cuspInvInner`
on the polar coordinates `(r, θ, w₁, w₂)`.

The only discontinuous ingredient is the angle `θ = argOf (q 1) (q 0)`, which has a jump of `2π`
along the negative `a`-axis and is undefined (set to `0`) at the origin.  Both defects are harmless
here:

* the perimeter parameter `uu = θ/(2π) − c` of `cuspInvInner` enters only through `bndOfU`, which
  is `1`-periodic and continuous, so the jump `θ ↦ θ + 2π` of the angle does not change the value.
  Formally we read `θ` as an element of `ℝ/2πℤ` (`Real.Angle`) — `Complex.continuousAt_arg_coe_angle`
  says that this is continuous at every nonzero complex number — rescale it to `ℝ/ℤ` by the
  continuous group isomorphism `AddCircle.equivAddCircle (2π) 1`, and use the continuous lift
  `Bar = AddCircle.liftIco 1 0 bndOfU` of `bndOfU` to `ℝ/ℤ` (`AddCircle.liftIco_zero_continuous`).
* at the origin `r = 0`, so the scalar `r/(2 r_J)` kills the (bounded) factor `bndOfU uu`; this is
  the only place where we need the bound `‖bndOfU t‖ ≤ √2` (`bndOfU_mem`).

Consequently `cuspInvCore v` is continuous on all of `E4`, and in particular on the core box
`coreBox = {q | √(q 0² + q 1²) < 1/2}`, which is the requested statement.
-/
import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.Charts
import Submission.Work.Cusp.bndOfU_add_int
import Submission.Work.Cusp.bndOfU_mem
import Submission.Work.Cusp.isOpen_coreBox
import Submission.Work.Cusp.beta_add_int
import Submission.Work.Cusp.cuspInvCore_mem_coreStratum

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open scoped Real InnerProductSpace Topology
open Filter

namespace Work.Cusp

/-! ### `bndOfU` is continuous

`bndOfU u = F (Int.fract u)` for the four-branched piecewise affine function `F` whose branches
agree at the corners of `Sq`; `ContinuousOn.comp_fract''` glues them. -/

private def bF1 (s : ℝ) : E2 := !₂[(1 : ℝ), 1 - 8 * s]
private def bF2 (s : ℝ) : E2 := !₂[3 - 8 * s, (-1 : ℝ)]
private def bF3 (s : ℝ) : E2 := !₂[(-1 : ℝ), 8 * s - 5]
private def bF4 (s : ℝ) : E2 := !₂[8 * s - 7, (1 : ℝ)]
private def bG3 (s : ℝ) : E2 := if s < 3 / 4 then bF3 s else bF4 s
private def bG2 (s : ℝ) : E2 := if s < 1 / 2 then bF2 s else bG3 s
private def bG1 (s : ℝ) : E2 := if s < 1 / 4 then bF1 s else bG2 s

private lemma bG1_zero_eq_one : bG1 0 = bG1 1 := by
  simp only [bG1, bG2, bG3, bF1, bF4]
  norm_num

private lemma bG1_cont : Continuous bG1 := by
  have h3 : Continuous bG3 := by
    unfold bG3
    refine Continuous.if ?_ ?_ ?_
    · intro s hs
      have hs' : s ∈ frontier (Set.Iio (3 / 4 : ℝ)) := hs
      rw [frontier_Iio] at hs'
      simp only [Set.mem_singleton_iff] at hs'
      subst hs'
      simp only [bF3, bF4]
      norm_num
    · unfold bF3; fun_prop
    · unfold bF4; fun_prop
  have h2 : Continuous bG2 := by
    unfold bG2
    refine Continuous.if ?_ ?_ h3
    · intro s hs
      have hs' : s ∈ frontier (Set.Iio (1 / 2 : ℝ)) := hs
      rw [frontier_Iio] at hs'
      simp only [Set.mem_singleton_iff] at hs'
      subst hs'
      simp only [bF2]
      rw [show bG3 (1 / 2) = bF3 (1 / 2) from by
        simp only [bG3]
        rw [ite_eq_left (by norm_num : (1 : ℝ) / 2 < 3 / 4)]]
      simp only [bF3]
      norm_num
    · unfold bF2; fun_prop
  unfold bG1
  refine Continuous.if ?_ ?_ h2
  · intro s hs
    have hs' : s ∈ frontier (Set.Iio (1 / 4 : ℝ)) := hs
    rw [frontier_Iio] at hs'
    simp only [Set.mem_singleton_iff] at hs'
    subst hs'
    simp only [bF1]
    rw [show bG2 (1 / 4) = bF2 (1 / 4) from by
      simp only [bG2]
      rw [ite_eq_left (by norm_num : (1 : ℝ) / 4 < 1 / 2)]]
    simp only [bF2]
    norm_num
  · unfold bF1; fun_prop

private lemma bndOfU_eq : bndOfU = bG1 ∘ Int.fract := rfl

private lemma bndOfU_zero_eq_one : bndOfU (0 : ℝ) = bndOfU 1 := by
  simp [bndOfU, Int.fract_zero, Int.fract_one]

private lemma bndOfU_cont : Continuous bndOfU := by
  have h : Continuous (bG1 ∘ Int.fract) :=
    ContinuousOn.comp_fract'' (f := bG1) bG1_cont.continuousOn bG1_zero_eq_one
  rwa [bndOfU_eq]

/-! ### The continuous lift `Bar : ℝ/ℤ → E2` of `bndOfU` -/

/-- The `1`-periodic function `bndOfU` descended to the circle `ℝ/ℤ = AddCircle 1`. -/
private def Bar : AddCircle (1 : ℝ) → E2 := AddCircle.liftIco (1 : ℝ) 0 bndOfU

private lemma Bar_cont : Continuous Bar :=
  AddCircle.liftIco_zero_continuous bndOfU_zero_eq_one bndOfU_cont.continuousOn

/-- `Bar` is the lift of `bndOfU`: at any real representative it takes the value `bndOfU`. -/
private lemma Bar_coe (x : ℝ) : Bar (x : AddCircle (1 : ℝ)) = bndOfU x := by
  obtain ⟨y, hy_mem, hy_eq⟩ :
      ∃ y ∈ Set.Ico (0 : ℝ) (0 + 1), (y : AddCircle (1 : ℝ)) = (x : AddCircle (1 : ℝ)) :=
    ⟨(AddCircle.equivIco (1 : ℝ) 0 (x : AddCircle (1 : ℝ))).1,
     (AddCircle.equivIco (1 : ℝ) 0 (x : AddCircle (1 : ℝ))).2,
     AddCircle.coe_equivIco⟩
  have hbar : Bar (x : AddCircle (1 : ℝ)) = bndOfU y := by
    rw [← hy_eq]
    exact AddCircle.liftIco_coe_apply hy_mem
  rw [hbar]
  have hsub : y - x ∈ AddSubgroup.zmultiples (1 : ℝ) := QuotientAddGroup.eq_iff_sub_mem.mp hy_eq
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hsub
  have hyx : y = x + (k : ℝ) := by
    have hk' : (k : ℝ) = y - x := by simpa using hk
    linarith
  rw [hyx, bndOfU_add_int]

/-! ### The bound `‖bndOfU t‖ ≤ √2` -/

private lemma norm_bndOfU_le (t : ℝ) : ‖bndOfU t‖ ≤ Real.sqrt 2 := by
  have hmem := bndOfU_mem t
  have hs : ‖bndOfU t‖ ^ 2 ≤ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
    have e0 : ‖(bndOfU t).ofLp 0‖ ^ 2 ≤ 1 := by
      rw [Real.norm_eq_abs]
      nlinarith [hmem.1, abs_nonneg ((bndOfU t).ofLp 0)]
    have e1 : ‖(bndOfU t).ofLp 1‖ ^ 2 ≤ 1 := by
      rw [Real.norm_eq_abs]
      nlinarith [hmem.2, abs_nonneg ((bndOfU t).ofLp 1)]
    linarith
  calc ‖bndOfU t‖ = Real.sqrt (‖bndOfU t‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt 2 := Real.sqrt_le_sqrt hs

/-! ### The complex number `q 0 + i q 1` and its angle -/

/-- The complex number `q 0 + i q 1` attached to a point of `E4`; `argOf (q 1) (q 0)` is its
argument and `√(q 0² + q 1²)` its modulus. -/
private def zOf (q : E4) : ℂ := ⟨q 0, q 1⟩

private lemma continuous_zOf : Continuous zOf := by
  have h : zOf = fun q : E4 => (q 0 : ℂ) + (q 1 : ℂ) * Complex.I := by
    funext q
    apply Complex.ext <;>
      simp [zOf, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  rw [h]; fun_prop

/-! ### The rescaling `ℝ/2πℤ → ℝ/ℤ` -/

/-- The continuous group isomorphism `ℝ/2πℤ → ℝ/ℤ`, `x ↦ x/(2π)`. -/
private def scale : Real.Angle → AddCircle (1 : ℝ) :=
  ⇑(AddCircle.equivAddCircle (2 * π) (1 : ℝ) (by positivity) one_ne_zero)

private lemma scale_cont : Continuous scale :=
  AddCircle.continuous_equivAddCircle (2 * π) (1 : ℝ) (by positivity) one_ne_zero

private lemma scale_apply_div (x : ℝ) :
    scale (x : Real.Angle) = ((x / (2 * π)) : AddCircle (1 : ℝ)) := by
  rw [show scale (x : Real.Angle) = (x * ((2 * π)⁻¹ * 1) : AddCircle (1 : ℝ)) from
    AddCircle.equivAddCircle_apply_mk (2 * π) (1 : ℝ) (by positivity) one_ne_zero x]
  congr 1
  ring

/-! ### The components of the core inverse -/

/-- The `y`-part `invY v (w)` of the core inverse. -/
private def coreSnd (v : Fin 5) (q : E4) : E2 := invY v !₂[q 2, q 3]

/-- The inner product `⟪cuspY v y, σ_v⟫/‖σ_v‖²` of the recovered `y`-part. -/
private def cq (v : Fin 5) (q : E4) : ℝ :=
  ⟪cuspY v (invY v !₂[q 2, q 3]), slope v⟫_ℝ / ‖slope v‖ ^ 2

/-- The first component of the core inverse: `t • bndOfU uu` with `t = √(q 0² + q 1²)/(2 r_J)` and
`uu = (θ - 2π c)/(2π)`, `θ = argOf (q 1) (q 0)`. -/
private def coreFst (v : Fin 5) (q : E4) : E2 :=
  (Real.sqrt (q 0 ^ 2 + q 1 ^ 2) / (2 * rJ)) •
    bndOfU ((argOf (q 1) (q 0)
      - 2 * π * (⟪cuspY v (invY v !₂[q 2, q 3]), slope v⟫_ℝ / ‖slope v‖ ^ 2)) / (2 * π))

private lemma continuous_coreSnd (v : Fin 5) : Continuous (coreSnd v) := by
  unfold coreSnd invY; fun_prop

private lemma continuous_cq (v : Fin 5) : Continuous (cq v) := by
  unfold cq cuspY invY; fun_prop

/-! ### Continuity of `bndOfU` composed with the recovered perimeter parameter -/

/-- The core perimeter factor `bndOfU (θ/(2π) - c)` as a function of the *angle class* of `zOf q`
and of `c`: this is `Bar ∘ (scale ∘ arg - c)`, hence continuous away from the origin. -/
private def V (v : Fin 5) (q : E4) : E2 :=
  bndOfU (Complex.arg (zOf q) / (2 * π) - cq v q)

private lemma V_eq (v : Fin 5) (q : E4) :
    V v q = Bar (scale ((Complex.arg (zOf q) : Real.Angle)) - (cq v q : AddCircle (1 : ℝ))) := by
  rw [V, scale_apply_div]
  rw [← AddCircle.coe_sub, Bar_coe]

private lemma continuousAt_V (v : Fin 5) (q : E4) (hq : zOf q ≠ 0) : ContinuousAt (V v) q := by
  have hmain : ContinuousAt
      (fun q : E4 => Bar (scale ((Complex.arg (zOf q) : Real.Angle))
        - (cq v q : AddCircle (1 : ℝ)))) q := by
    refine Bar_cont.continuousAt.comp ?_
    have h1 : ContinuousAt (fun q : E4 => scale ((Complex.arg (zOf q) : Real.Angle))) q :=
      scale_cont.continuousAt.comp
        ((Complex.continuousAt_arg_coe_angle hq).comp continuous_zOf.continuousAt)
    have hcoe : Continuous (fun x : ℝ => (x : AddCircle (1 : ℝ))) := by continuity
    have h2 : ContinuousAt (fun q : E4 => (cq v q : AddCircle (1 : ℝ))) q :=
      (hcoe.comp (continuous_cq v)).continuousAt
    exact h1.sub h2
  have hfun : V v = fun q : E4 =>
      Bar (scale ((Complex.arg (zOf q) : Real.Angle)) - (cq v q : AddCircle (1 : ℝ))) :=
    funext (V_eq v)
  rw [hfun]
  exact hmain

/-! ### The first component is continuous -/

/-- `(θ - 2πP)/(2π) = θ/(2π) - P`. -/
private lemma div_sub_two_pi_mul (θ P : ℝ) :
    (θ - 2 * π * P) / (2 * π) = θ / (2 * π) - P := by
  rw [sub_div, mul_div_cancel_left₀ P (by positivity : (2 * π : ℝ) ≠ 0)]

private lemma coreFst_eq_V (v : Fin 5) (q : E4) :
    coreFst v q = (Real.sqrt (q 0 ^ 2 + q 1 ^ 2) / (2 * rJ)) • V v q := by
  have h : (argOf (q 1) (q 0)
        - 2 * π * (⟪cuspY v (invY v !₂[q 2, q 3]), slope v⟫_ℝ / ‖slope v‖ ^ 2)) / (2 * π)
      = Complex.arg (zOf q) / (2 * π) - cq v q := by
    rw [div_sub_two_pi_mul]
    rfl
  unfold coreFst V
  rw [h]

private lemma continuous_coreFst (v : Fin 5) : Continuous (coreFst v) := by
  rw [show coreFst v = fun q : E4 => (Real.sqrt (q 0 ^ 2 + q 1 ^ 2) / (2 * rJ)) • V v q from
    funext (coreFst_eq_V v)]
  rw [continuous_iff_continuousAt]
  intro q
  by_cases hq : zOf q = 0
  · have hq0 : q 0 = 0 := by
      have := congrArg Complex.re hq
      simpa [zOf] using this
    have hq1 : q 1 = 0 := by
      have := congrArg Complex.im hq
      simpa [zOf] using this
    have hsq : Real.sqrt (q 0 ^ 2 + q 1 ^ 2) = 0 := by rw [hq0, hq1]; norm_num
    have hval : (Real.sqrt (q 0 ^ 2 + q 1 ^ 2) / (2 * rJ)) • V v q = 0 := by
      rw [hsq, zero_div, zero_smul]
    have hle : ∀ q' : E4, ‖(Real.sqrt (q' 0 ^ 2 + q' 1 ^ 2) / (2 * rJ)) • V v q'‖
        ≤ (Real.sqrt 2 / (2 * rJ)) * Real.sqrt (q' 0 ^ 2 + q' 1 ^ 2) := by
      intro q'
      have hrJ2 : (0 : ℝ) ≤ 2 * rJ := by norm_num [rJ]
      have hnn : (0 : ℝ) ≤ Real.sqrt (q' 0 ^ 2 + q' 1 ^ 2) / (2 * rJ) :=
        div_nonneg (Real.sqrt_nonneg _) hrJ2
      have h1 : ‖(Real.sqrt (q' 0 ^ 2 + q' 1 ^ 2) / (2 * rJ)) • V v q'‖
          = (Real.sqrt (q' 0 ^ 2 + q' 1 ^ 2) / (2 * rJ)) * ‖V v q'‖ := by
        rw [norm_smul, Real.norm_of_nonneg hnn]
      rw [h1]
      calc (Real.sqrt (q' 0 ^ 2 + q' 1 ^ 2) / (2 * rJ)) * ‖V v q'‖
          ≤ (Real.sqrt (q' 0 ^ 2 + q' 1 ^ 2) / (2 * rJ)) * Real.sqrt 2 :=
            mul_le_mul_of_nonneg_left (norm_bndOfU_le _) hnn
        _ = Real.sqrt 2 / (2 * rJ) * Real.sqrt (q' 0 ^ 2 + q' 1 ^ 2) := by ring
    have hup : Tendsto (fun q' : E4 => Real.sqrt 2 / (2 * rJ) * Real.sqrt (q' 0 ^ 2 + q' 1 ^ 2))
        (𝓝 q) (𝓝 0) := by
      have h3 : (Real.sqrt 2 / (2 * rJ)) * Real.sqrt (q 0 ^ 2 + q 1 ^ 2) = 0 := by
        rw [hsq, mul_zero]
      have h2 : Tendsto (fun x : E4 => Real.sqrt 2 / (2 * rJ) * Real.sqrt (x 0 ^ 2 + x 1 ^ 2))
          (𝓝 q) (𝓝 ((Real.sqrt 2 / (2 * rJ)) * Real.sqrt (q 0 ^ 2 + q 1 ^ 2))) :=
        (continuous_sqrt_sq_add_sq.continuousAt (x := q)).const_mul (Real.sqrt 2 / (2 * rJ))
      rw [h3] at h2
      exact h2
    have hsqueeze : Tendsto
        (fun q' : E4 => ‖(Real.sqrt (q' 0 ^ 2 + q' 1 ^ 2) / (2 * rJ)) • V v q'‖) (𝓝 q) (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le (tendsto_const_nhds) hup
        (fun q' => norm_nonneg _) hle
    have htend : Tendsto
        (fun q' : E4 => (Real.sqrt (q' 0 ^ 2 + q' 1 ^ 2) / (2 * rJ)) • V v q') (𝓝 q) (𝓝 0) :=
      tendsto_zero_iff_norm_tendsto_zero.mpr hsqueeze
    rw [← hval] at htend
    exact htend
  · exact ((continuous_sqrt_sq_add_sq.div_const (2 * rJ)).continuousAt.smul
      (continuousAt_V v q hq))

/-! ### Unfolding `cuspInvInner` at the core polar coordinates -/

private lemma coreFst_eq (v : Fin 5) (q : E4) (r θ : ℝ) (h : r ≤ rJ) :
    (cuspInvInner v (!₂[r, θ, q 2, q 3] : E4)).1
      = (r / (2 * rJ)) • bndOfU ((θ
          - 2 * π * (⟪cuspY v (invY v !₂[q 2, q 3]), slope v⟫_ℝ / ‖slope v‖ ^ 2)) / (2 * π)) := by
  simp [cuspInvInner, h]

private lemma coreSnd_eq (v : Fin 5) (q : E4) (r θ : ℝ) :
    (cuspInvInner v (!₂[r, θ, q 2, q 3] : E4)).2 = coreSnd v q := by
  simp [cuspInvInner, coreSnd]

private lemma cuspInvCore_eq (v : Fin 5) (q : E4) (h : Real.sqrt (q 0 ^ 2 + q 1 ^ 2) ≤ rJ) :
    cuspInvCore v q = (coreFst v q, coreSnd v q) := by
  refine Prod.ext ?_ ?_
  · rw [fst_cuspInvCore_eq,
      coreFst_eq v q (Real.sqrt (q 0 ^ 2 + q 1 ^ 2)) (argOf (q 1) (q 0)) h]
    rfl
  · rw [show (cuspInvCore v q).2
        = (cuspInvInner v (!₂[Real.sqrt (q 0 ^ 2 + q 1 ^ 2), argOf (q 1) (q 0), q 2, q 3] : E4)).2
        from rfl,
      coreSnd_eq v q (Real.sqrt (q 0 ^ 2 + q 1 ^ 2)) (argOf (q 1) (q 0))]

/-! ### The requested statement -/

theorem cuspInvCore_continuousOn (v : Fin 5) : ContinuousOn (cuspInvCore v) coreBox := by
  have hEqOn : Set.EqOn (cuspInvCore v) (fun q => (coreFst v q, coreSnd v q)) coreBox := by
    intro q hq
    have h1 : Real.sqrt (q 0 ^ 2 + q 1 ^ 2) < 1 / 2 := hq
    have hrJ : Real.sqrt (q 0 ^ 2 + q 1 ^ 2) ≤ rJ := by
      rw [show rJ = 3 from rfl]; linarith
    exact cuspInvCore_eq v q hrJ
  have hcont : ContinuousOn (fun q => (coreFst v q, coreSnd v q)) coreBox :=
    (continuous_coreFst v).continuousOn.prodMk (continuous_coreSnd v).continuousOn
  exact hcont.congr hEqOn

end Work.Cusp
