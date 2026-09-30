/-
# The polar map of the filling piece, and the junction/core coordinate identity

This file collects the elementary facts behind the transition `jkTransMap`/`kjTransMap` of
`Submission/Work/RTOwed/jTrans_core.lean`: the *polar map* `jPolMap` of the filling piece (the
change of variables `(r,θ,w₁,w₂) ↦ (r cos θ, r sin θ, w₁, w₂)` from the polar coordinate of the
junction charts to the Cartesian coordinate of the core charts), its smoothness and derivative, and
the identity `jCoordM = coreCoordM ∘ jPolMap` on the core part of a junction box.
-/
import Mathlib
import Submission.Work.RTOwed.FillAtlas
import Submission.Work.RTOwed.jTransCollAux
import Submission.Work.RTOwed.coreTrans
import Submission.Work.RTOwed.flatModel_polar_change
import Submission.Work.Cusp.ThetaPolar_cuspInvInner
import Submission.Work.Cusp.cuspInvInner_add_int_mul_two_pi
import Submission.Work.Cusp.cuspInvCore_mem_coreStratum
import Submission.Work.Cusp.cuspInvCore_ThetaCore
import Submission.Work.Cusp.ThetaCore_cuspInvCore
import Submission.Work.Cusp.ThetaCore_eq_polar
import Submission.Work.Cusp.cuspInvInner_nrm
import Submission.Work.Cusp.wOf_invY

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function
open scoped Real RealInnerProductSpace

namespace Work.RTOwed

/-! ## The polar map -/

/-- **The polar map of the filling piece**: `(r,θ,w₁,w₂) ↦ (r cos θ, r sin θ, w₁, w₂)`.  It is the
change of variables between the polar coordinates of the junction charts and the Cartesian
coordinates of the core charts. -/
def jPolMap (q : Work.Cusp.E4) : Work.Cusp.E4 :=
  !₂[q 0 * Real.cos (q 1), q 0 * Real.sin (q 1), q 2, q 3]

@[simp] theorem jPolMap_apply_zero (q : Work.Cusp.E4) :
    (jPolMap q) 0 = q 0 * Real.cos (q 1) := rfl

@[simp] theorem jPolMap_apply_one (q : Work.Cusp.E4) :
    (jPolMap q) 1 = q 0 * Real.sin (q 1) := rfl

@[simp] theorem jPolMap_apply_two (q : Work.Cusp.E4) : (jPolMap q) 2 = q 2 := rfl

@[simp] theorem jPolMap_apply_three (q : Work.Cusp.E4) : (jPolMap q) 3 = q 3 := rfl

theorem jPolMap_zero_zero (q : Work.Cusp.E4) : jPolMap q 0 = q 0 * Real.cos (q 1) := rfl

/-! ## Elementary algebra -/

/-- `√((r cos θ)² + (r sin θ)²) = r` for `r ≥ 0`. -/
theorem sqrt_cos_sin_sq (r θ : ℝ) (hr : 0 ≤ r) :
    Real.sqrt ((r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2) = r := by
  have h : (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [h, Real.sqrt_sq_eq_abs, abs_of_nonneg hr]

/-- For `r > 0`, the argument `argOf (r sin θ) (r cos θ)` of the point `(r cos θ, r sin θ)` is
`θ` up to an integer multiple of `2π`. -/
theorem argOf_cos_sin (r θ : ℝ) (hr : 0 < r) :
    ∃ m : ℤ, θ = Work.Cusp.argOf (r * Real.sin θ) (r * Real.cos θ) + (m : ℝ) * (2 * Real.pi) := by
  have harg : Work.Cusp.argOf (r * Real.sin θ) (r * Real.cos θ)
      = toIocMod Real.two_pi_pos (-Real.pi) θ := by
    rw [Work.Cusp.argOf]
    have hc : (⟨r * Real.cos θ, r * Real.sin θ⟩ : ℂ)
        = (r : ℂ) * (↑(Real.cos θ) + ↑(Real.sin θ) * Complex.I) := by
      rw [Complex.mk_eq_add_mul_I, Complex.ofReal_mul, Complex.ofReal_mul, mul_add, mul_assoc]
    rw [hc, Complex.ofReal_cos, Complex.ofReal_sin]
    exact Complex.arg_mul_cos_add_sin_mul_I_eq_toIocMod hr θ
  refine ⟨toIocDiv Real.two_pi_pos (-Real.pi) θ, ?_⟩
  have h := toIocMod_add_toIocDiv_zsmul Real.two_pi_pos (-Real.pi) θ
  rw [harg]
  rw [zsmul_eq_mul] at h
  linarith [h]

/-- **The inverse polar chart of the core agrees with the polar chart**: for `r > 0`, inverting the
core chart at the Cartesian point `(r cos θ, r sin θ, w)` gives the same point of the cover of the
filling piece as inverting the polar chart at `(r, θ, w)`. -/
theorem cuspInvInner_polar_eq_core (v : Work.Space.Cusp) (r θ w0 w1 : ℝ) (hr : 0 < r) :
    Work.Cusp.cuspInvInner v (!₂[r, θ, w0, w1] : Work.Cusp.E4)
      = Work.Cusp.cuspInvCore v (!₂[r * Real.cos θ, r * Real.sin θ, w0, w1] : Work.Cusp.E4) := by
  obtain ⟨m, hm⟩ := argOf_cos_sin r θ hr
  simp only [Work.Cusp.cuspInvCore, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
  rw [sqrt_cos_sin_sq r θ (le_of_lt hr)]
  have hvec : (!₂[r, θ, w0, w1] : Work.Cusp.E4)
      = !₂[r, Work.Cusp.argOf (r * Real.sin θ) (r * Real.cos θ) + (m : ℝ) * (2 * Real.pi),
          w0, w1] := by
    conv_lhs => rw [hm]
  rw [hvec]
  simpa using Work.Cusp.cuspInvInner_add_int_mul_two_pi v m r
    (Work.Cusp.argOf (r * Real.sin θ) (r * Real.cos θ)) (!₂[w0, w1] : Work.Cusp.E2)

/-- The polar map takes `q` to the Cartesian core point with the same `w`-coordinates. -/
theorem jPolMap_mem_coreBoxSect {W : Set Work.Cusp.E2} {q : Work.Cusp.E4}
    (hq0 : 0 < q 0) (hq1 : q 0 < 1/2) (hW : (!₂[q 2, q 3] : Work.Cusp.E2) ∈ W) :
    jPolMap q ∈ Work.Cusp.coreBoxSect W := by
  refine ⟨?_, ?_⟩
  · show Real.sqrt ((jPolMap q) 0 ^ 2 + (jPolMap q) 1 ^ 2) < 1/2
    rw [jPolMap_apply_zero, jPolMap_apply_one,
      sqrt_cos_sin_sq (q 0) (q 1) (le_of_lt hq0)]
    exact hq1
  · show (!₂[(jPolMap q) 2, (jPolMap q) 3] : Work.Cusp.E2) ∈ W
    rwa [jPolMap_apply_two, jPolMap_apply_three]

/-! ## The layer parameter of `cuspInvInner` -/

/-- In the collar branch (`r_J < q 0`) the layer parameter recovered by `cuspInvInner` is `> 1/2`. -/
theorem cuspInvInner_nrm_gt_half (v : Work.Space.Cusp) {q : Work.Cusp.E4}
    (hq : q ∈ Work.Cusp.polarBox) (h : ¬ q 0 ≤ Work.Cusp.rJ) :
    1/2 < Work.Cusp.nrm (Work.Cusp.cuspInvInner v q).1 := by
  have hq0gt : Work.Cusp.rJ < q 0 := lt_of_not_ge h
  have hrJ3 : Work.Cusp.rJ = 3 := rfl
  simp only [Work.Cusp.cuspInvInner]
  set y : Work.Cusp.E2 := Work.Cusp.invY v !₂[q 2, q 3] with hy
  set uu : ℝ := (q 1 - 2 * Real.pi *
    (inner ℝ (Work.Cusp.cuspY v y) (Work.Cusp.slope v) / ‖Work.Cusp.slope v‖ ^ 2)) /
      (2 * Real.pi) with huu
  set b : ℝ := Work.Cusp.beta (Work.Cusp.cuspX v uu y) with hb
  have hbpos : 0 < b := by rw [hb]; exact Work.Cusp.beta_pos _
  have hblt : b < Work.Cusp.sJ := by rw [hb]; exact Work.Cusp.beta_lt_sJ _
  set t : ℝ := (if q 0 ≤ Work.Cusp.rJ then q 0 / (2 * Work.Cusp.rJ)
    else 1 + (Work.Cusp.R0 - q 0 - Real.log b) /
      (2 * (Real.log b - Real.log Work.Cusp.sJ))) with ht
  have hloglt : Real.log b < Real.log Work.Cusp.sJ := Real.log_lt_log hbpos hblt
  have htgt : 1/2 < t := by
    rw [ht, if_neg h]
    exact Work.Cusp.cuspInvRate_gt_half hloglt hq0gt
  rw [Work.Cusp.nrm_smul, Work.Cusp.nrm_bndOfU, mul_one,
    abs_of_pos (lt_trans (by norm_num) htgt)]
  exact htgt

/-- **The contrapositive of the layer computation**: if the layer parameter recovered by
`cuspInvInner` is `< 1/12` then the polar coordinate is below the core/junction threshold
`q 0 < 1/2`. -/
theorem cuspInvInner_nrm_lt_half (v : Work.Space.Cusp) {q : Work.Cusp.E4}
    (hq : q ∈ Work.Cusp.polarBox) (h : Work.Cusp.nrm (Work.Cusp.cuspInvInner v q).1 < 1/12) :
    q 0 < 1/2 := by
  by_cases hc : q 0 ≤ Work.Cusp.rJ
  · rw [Work.Cusp.cuspInvInner_nrm v q hq hc] at h
    have h2rJ : Work.Cusp.rJ = 3 := rfl
    rw [h2rJ] at h
    linarith
  · have hgt := cuspInvInner_nrm_gt_half v hq hc
    linarith


/-! ## The junction/core coordinate identities -/

/-- **A collar point of a junction box is not a core point**: on the collar branch (`r_J < q 0`) the
junction coordinate inclusion lands in the collar of the filling piece (layer parameter `> 1/2`) or
in the hyperbolic piece, while every point of the core chart has layer parameter `< 1/12`. -/
theorem jCoordM_of_gt_ne_coreCoordM (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (P : JPin a v) (W : Set Work.Cusp.E2)
    {q : Work.Cusp.E4} (hq : q ∈ jBox v P.cU P.k P.W P.kx P.δ) (hqgt : ¬ q 0 ≤ Work.Cusp.rJ)
    {x : Work.Cusp.E4} (hx : x ∈ Work.Cusp.coreBoxSect W) :
    jCoordM a v (D v) P.cU P.k P.W P.kx P.δ ⟨q, hq⟩
      ≠ Work.Cusp.coreCoordM a v (D v).tor W ⟨x, hx⟩ := by
  rintro hXY
  rw [jCoordM_of_gt a v (D v) P.cU P.k P.W P.kx P.δ hq hqgt] at hXY
  set z : {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v P.kx P.δ} :=
    ⟨Work.Cusp.polarToUHS v q,
      polarToUHS_mem_cuspBoxTop v P.kx P.δ hq.2.2.2.2.2 (not_le.mp hqgt) hq.2.1⟩ with hzdef
  have h : Work.Cusp.cuspCoordMTop a v (D v) P.kx P.δ z
      = Work.Cusp.coreCoordM a v (D v).tor W ⟨x, hx⟩ := hXY
  by_cases hb : (z : Work.Cusp.E4) 3 < Work.Cusp.beta (Work.Cusp.xOf (z : Work.Cusp.E4))
  · rw [cuspCoordMTop_of_lt a v (D v) P.kx P.δ z hb] at h
    simp only [Work.Cusp.coreCoordM] at h
    exact a.incMbar_ne_incY
      (fun ⟨hxT, _⟩ => (D v).mbarLow_not_TsetTop P.kx P.δ z.2 hb hxT) h
  · rw [cuspCoordMTop_of_ge a v (D v) P.kx P.δ z hb] at h
    simp only [Work.Cusp.coreCoordM] at h
    have hpair := a.incW_injective v h
    have hnrm : Work.Cusp.nrm (Work.Cusp.cuspInvOuter v (z : Work.Cusp.E4)).1
        = Work.Cusp.nrm (Work.Cusp.cuspInvCore v x).1 := by
      have := congrArg (fun w : Work.Space.SquarePt × a.Torus v =>
        Work.Cusp.nrm ((w.1 : Work.Space.SquarePt) : Work.Cusp.E2)) hpair
      simpa using this
    have hzge : Work.Cusp.beta (Work.Cusp.xOf (z : Work.Cusp.E4)) ≤ (z : Work.Cusp.E4) 3 :=
      not_lt.mp hb
    have hz3 : (z : Work.Cusp.E4) 3 < Work.Cusp.sJ := by
      show (Work.Cusp.polarToUHS v q) 3 < Work.Cusp.sJ
      rw [polarToUHS_three, show Work.Cusp.sJ = Real.exp (1/2) from rfl]
      refine Real.exp_lt_exp.mpr ?_
      have hgt := lt_of_not_ge hqgt
      rw [Work.Cusp.rJ] at hgt
      rw [Work.Cusp.R0]; linarith
    have h1 : 1/2 < Work.Cusp.nrm (Work.Cusp.cuspInvOuter v (z : Work.Cusp.E4)).1 :=
      nrm_cuspInvOuter_gt_half v P.kx P.δ ⟨z.2, hzge⟩ hz3
    have h2 : Work.Cusp.nrm (Work.Cusp.cuspInvCore v x).1 < 1/12 :=
      Work.Cusp.cuspInvCore_mem_coreStratum v x hx.1
    rw [← hnrm] at h2
    linarith

/-- **The junction coordinate and the shifted core coordinate of a common point agree**: on the
inner branch of a junction box with `0 < q 0 < 1/2`, the junction coordinate inclusion of `q` is the
core coordinate inclusion, with respect to the same `w`-section box `W`, of the lattice shift
`kkShift v m` of the polar map `jPolMap q`. -/
theorem jCoordM_eq_coreCoordM_shift (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (P : JPin a v) (W : Set Work.Cusp.E2)
    {q : Work.Cusp.E4} (hq : q ∈ jBox v P.cU P.k P.W P.kx P.δ)
    (hq0pos : 0 < q 0) (hq0 : q 0 < 1/2) (m : Fin 2 → ℤ)
    (h : kkShift v m (jPolMap q) ∈ Work.Cusp.coreBoxSect W) :
    jCoordM a v (D v) P.cU P.k P.W P.kx P.δ ⟨q, hq⟩
      = Work.Cusp.coreCoordM a v (D v).tor W ⟨kkShift v m (jPolMap q), h⟩ := by
  have hle : q 0 ≤ Work.Cusp.rJ := by rw [Work.Cusp.rJ]; linarith
  have hcbox : jPolMap q ∈ Work.Cusp.coreBox := by
    rw [Work.Cusp.coreBox, Set.mem_ofPred_eq, jPolMap_apply_zero, jPolMap_apply_one,
      sqrt_cos_sin_sq (q 0) (q 1) (le_of_lt hq0pos)]
    exact hq0
  have hqq : (!₂[q 0, q 1, q 2, q 3] : Work.Cusp.E4) = q := by ext i; fin_cases i <;> rfl
  have hp : Work.Cusp.cuspInvCore v (jPolMap q) = Work.Cusp.cuspInvInner v q := by
    have h1 := cuspInvInner_polar_eq_core v (q 0) (q 1) (q 2) (q 3) hq0pos
    rw [hqq] at h1
    exact h1.symm
  have hcc := cuspInvCore_kkShift v m (jPolMap q) hcbox
  rw [jCoordM_of_le a v (D v) P.cU P.k P.W P.kx P.δ hq hle]
  simp only [Work.Cusp.coreCoordM]
  congr 1
  have he2 : (Work.Cusp.cuspInvInner v q).1
      = (Work.Cusp.cuspInvCore v (kkShift v m (jPolMap q))).1 := by
    rw [hcc, hp]
  have hcc2 : (Work.Cusp.cuspInvCore v (kkShift v m (jPolMap q))).2
      = (Work.Cusp.cuspInvInner v q).2 + Work.Cusp.ofInt2 m := by
    rw [hcc, hp]
  refine Prod.ext (Subtype.ext he2) ?_
  show (D v).tor.symm (fun i => (((Work.Cusp.cuspInvInner v q).2.ofLp i : ℝ) : AddCircle (1:ℝ)))
      = (D v).tor.symm (fun i =>
          (((Work.Cusp.cuspInvCore v (kkShift v m (jPolMap q))).2.ofLp i : ℝ) :
            AddCircle (1:ℝ)))
  rw [hcc2]
  congr 1
  funext i
  exact (kk_coe_ofInt2 (Work.Cusp.cuspInvInner v q).2 m i).symm

/-- The polar change of the flat model, in the vocabulary of `jPolMap`. -/
theorem flatModel_jPolMap (h₀ : ℝ) (q U V : Work.Cusp.E4) :
    Work.RTInstance.flatModel h₀ (jPolMap q) (fderiv ℝ jPolMap q U) (fderiv ℝ jPolMap q V)
      = Work.RTInstance.diagQuad ![1, q 0 ^ 2, h₀ ^ 2, h₀ ^ 2] U V :=
  flatModel_polar_change h₀ q U V

/-- **The lattice shift `kkShift v m` is an isometry of the flat core model.** -/
theorem flatModel_kkShift (h₀ : ℝ) (v : Work.Space.Cusp) (m : Fin 2 → ℤ)
    (x U V : Work.Cusp.E4) :
    Work.RTInstance.flatModel h₀ (kkShift v m x)
        (kkLin (Real.cos (kkAng v m))
          (Real.sin (kkAng v m)) U)
        (kkLin (Real.cos (kkAng v m))
          (Real.sin (kkAng v m)) V)
      = Work.RTInstance.flatModel h₀ x U V := by
  rw [Work.RTInstance.flatModel_apply, Work.RTInstance.flatModel_apply,
    kkLin_apply, kkLin_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.cons_val_three] at *
  have hcs : Real.cos (kkAng v m) ^ 2 + Real.sin (kkAng v m) ^ 2 = 1 :=
    Real.cos_sq_add_sin_sq _
  linear_combination (U 0 * V 0 + U 1 * V 1) * hcs

end Work.RTOwed
