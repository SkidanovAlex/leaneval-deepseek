import Mathlib
import Submission.Work.RTOwed.FillAtlas

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The transition between two core charts of one cusp is a flat isometry

`Work.RTOwed.kkTransMap` is the transition between the two core charts `Work.RTOwed.kChartOf a tor v W`
of the `v`-th filling piece on `M̂`, and `Work.RTOwed.kkTransSrc` its source.  Both charts have the
same metric layer `Work.RTOwed.kLayer v = ChartLayer.flat (fillProf v).h₀`, so `coreTrans` says that
the transition (and its inverse) is smooth and is an isometry of the flat core metric.

The two core charts differ by *which lift of the torus coordinate is used*: the core coordinate
`q = Θ_v(p, y) = (r cos θ, r sin θ, w)` pins the lift `y` of the torus point by requiring its
`w`-coordinates `wOf v y = (q 2, q 3)` to lie in the box `W`.  Replacing the lift `y` by `y + n`
with `n ∈ ℤ² ⊂ ℝ²` changes `q` by

* the rotation of `(q 0, q 1)` by the phase `2π⟪cuspY v n, σ_v⟫/‖σ_v‖²` (the angle coordinate
  `thetaAng` is normalised against the σ-component of `y`), and
* the translation of `(q 2, q 3)` by `wOf v n`.

This is `Work.Cusp.ThetaCore_add_int`, and the rotation-translation `kkShift v m` is exactly the
classical form the isometry is proved in: `kkShift v m = kkLin (cos Δ) (sin Δ) + const`, with
`kkLin` a block-diagonal (rotation ⊕ identity) linear map, which is orthogonal for the flat model
`flatModel h₀ q u w = u₀w₀ + u₁w₁ + h₀²(u₂w₂ + u₃w₃)`.
-/

noncomputable section

open Set Topology Function Filter
open scoped RealInnerProductSpace Real Topology Manifold ContDiff

namespace Work.RTOwed

open Work.RTInstance

def kkAng (v : Work.Space.Cusp) (m : Fin 2 → ℤ) : ℝ :=
  2 * π * inner ℝ (Work.Cusp.cuspY v (Work.Cusp.ofInt2 m)) (Work.Cusp.slope v) /
    ‖Work.Cusp.slope v‖ ^ 2

def kkShift (v : Work.Space.Cusp) (m : Fin 2 → ℤ) : Work.Cusp.E4 → Work.Cusp.E4 :=
  fun x => !₂[Real.cos (kkAng v m) * x 0 - Real.sin (kkAng v m) * x 1,
              Real.sin (kkAng v m) * x 0 + Real.cos (kkAng v m) * x 1,
              x 2 + (Work.Cusp.wOf v (Work.Cusp.ofInt2 m)) 0,
              x 3 + (Work.Cusp.wOf v (Work.Cusp.ofInt2 m)) 1]

def kkLin (c s : ℝ) : Work.Cusp.E4 →L[ℝ] Work.Cusp.E4 :=
  (Work.RTInstance.coord4 0).smulRight (!₂[c, s, 0, 0] : Work.Cusp.E4)
  + (Work.RTInstance.coord4 1).smulRight (!₂[-s, c, 0, 0] : Work.Cusp.E4)
  + (Work.RTInstance.coord4 2).smulRight (!₂[0, 0, 1, 0] : Work.Cusp.E4)
  + (Work.RTInstance.coord4 3).smulRight (!₂[0, 0, 0, 1] : Work.Cusp.E4)

@[simp] lemma kkLin_apply (c s : ℝ) (x : Work.Cusp.E4) :
    kkLin c s x = !₂[c * x 0 - s * x 1, s * x 0 + c * x 1, x 2, x 3] := by
  ext i
  fin_cases i <;>
    simp [kkLin, Work.RTInstance.coord4_apply, ContinuousLinearMap.smulRight_apply] <;> ring

lemma kkShift_eq (v : Work.Space.Cusp) (m : Fin 2 → ℤ) :
    kkShift v m = fun x => kkLin (Real.cos (kkAng v m)) (Real.sin (kkAng v m)) x
      + (!₂[0, 0, (Work.Cusp.wOf v (Work.Cusp.ofInt2 m)) 0,
            (Work.Cusp.wOf v (Work.Cusp.ofInt2 m)) 1] : Work.Cusp.E4) := by
  funext x
  rw [kkLin_apply]
  ext i
  fin_cases i <;> simp [kkShift]

lemma continuous_kkShift (v : Work.Space.Cusp) (m : Fin 2 → ℤ) : Continuous (kkShift v m) := by
  rw [kkShift_eq]
  exact ((kkLin _ _).continuous).add continuous_const

lemma kk_ofInt2_apply (m : Fin 2 → ℤ) (i : Fin 2) : Work.Cusp.ofInt2 m i = ((m i : ℤ) : ℝ) := by
  fin_cases i <;> simp [Work.Cusp.ofInt2]

lemma kk_coe_ofInt2 (y : Work.Cusp.E2) (m : Fin 2 → ℤ) (i : Fin 2) :
    (((y + Work.Cusp.ofInt2 m) i : ℝ) : AddCircle (1 : ℝ)) = ((y i : ℝ) : AddCircle (1 : ℝ)) := by
  have hm : (Work.Cusp.ofInt2 m i : ℝ) = (m i : ℤ) • (1 : ℝ) := by
    rw [kk_ofInt2_apply, zsmul_one]
  rw [show (y + Work.Cusp.ofInt2 m) i = y i + (Work.Cusp.ofInt2 m i : ℝ) from rfl,
    hm, AddCircle.coe_add, AddCircle.coe_zsmul, AddCircle.coe_period, smul_zero, add_zero]

lemma ThetaCore_kkShift (v : Work.Space.Cusp) (p y : Work.Cusp.E2) (m : Fin 2 → ℤ) :
    Work.Cusp.ThetaCore v p (y + Work.Cusp.ofInt2 m)
      = kkShift v m (Work.Cusp.ThetaCore v p y) := by
  rw [Work.Cusp.ThetaCore_add_int v p y m]
  ext i
  fin_cases i <;> simp [kkShift, kkAng] <;> ring

lemma cuspInvCore_kkShift (v : Work.Space.Cusp) (m : Fin 2 → ℤ) (x : Work.Cusp.E4)
    (hx : x ∈ Work.Cusp.coreBox) :
    Work.Cusp.cuspInvCore v (kkShift v m x)
      = ((Work.Cusp.cuspInvCore v x).1, (Work.Cusp.cuspInvCore v x).2 + Work.Cusp.ofInt2 m) := by
  have h : Work.Cusp.ThetaCore v (Work.Cusp.cuspInvCore v x).1
        ((Work.Cusp.cuspInvCore v x).2 + Work.Cusp.ofInt2 m) = kkShift v m x := by
    rw [ThetaCore_kkShift v (Work.Cusp.cuspInvCore v x).1 (Work.Cusp.cuspInvCore v x).2 m,
      Work.Cusp.ThetaCore_cuspInvCore v x hx]
  rw [← h]
  exact Work.Cusp.cuspInvCore_ThetaCore v _ _

lemma coreCoordM_shift (a : Work.Space.Assembly)
    (tor : ∀ v : Work.Space.Cusp, a.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ)))
    (v : Work.Space.Cusp) {W₁ W₂ : Set Work.Cusp.E2} (m : Fin 2 → ℤ) (x : Work.Cusp.E4)
    (hx : x ∈ Work.Cusp.coreBoxSect W₁) (hx' : kkShift v m x ∈ Work.Cusp.coreBoxSect W₂) :
    Work.Cusp.coreCoordM a v (tor v) W₁ ⟨x, hx⟩
      = Work.Cusp.coreCoordM a v (tor v) W₂ ⟨kkShift v m x, hx'⟩ := by
  have hbox : x ∈ Work.Cusp.coreBox := Work.Cusp.CoreChartM.ccm_coreBoxSect_subset_coreBox W₁ hx
  have hcc := cuspInvCore_kkShift v m x hbox
  have hp : (Work.Cusp.cuspInvCore v (kkShift v m x)).1 = (Work.Cusp.cuspInvCore v x).1 := by
    rw [hcc]
  have hy : (Work.Cusp.cuspInvCore v (kkShift v m x)).2
      = (Work.Cusp.cuspInvCore v x).2 + Work.Cusp.ofInt2 m := by rw [hcc]
  simp only [Work.Cusp.coreCoordM]
  congr 1
  refine Prod.ext (Subtype.ext hp.symm) ?_
  show (tor v).symm (fun i => (((Work.Cusp.cuspInvCore v x).2 i : ℝ) : AddCircle (1 : ℝ)))
      = (tor v).symm (fun i => (((Work.Cusp.cuspInvCore v (kkShift v m x)).2 i : ℝ) : AddCircle (1 : ℝ)))
  rw [hy]
  congr 1
  funext i
  exact (kk_coe_ofInt2 (Work.Cusp.cuspInvCore v x).2 m i).symm

lemma kChartOf_symm_apply (a : Work.Space.Assembly)
    (tor : ∀ v : Work.Space.Cusp, a.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ)))
    (v : Work.Space.Cusp) (W : Set Work.Cusp.E2) (hW : IsOpen W)
    (hsec : ∀ y y' : Work.Cusp.E2, Work.Cusp.wOf v y ∈ W → Work.Cusp.wOf v y' ∈ W →
      (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y')
    (q : Work.Cusp.E4) (hq : q ∈ Work.Cusp.coreBoxSect W) :
    (kChartOf a tor v W hW hsec).symm q = Work.Cusp.coreCoordM a v (tor v) W ⟨q, hq⟩ := by
  have hmem : Work.Cusp.coreCoordM a v (tor v) W ⟨q, hq⟩ ∈ (kChartOf a tor v W hW hsec).source := by
    rw [kChartOf_source]
    exact ⟨⟨q, hq⟩, Set.mem_univ _, rfl⟩
  have h1 : kChartOf a tor v W hW hsec (Work.Cusp.coreCoordM a v (tor v) W ⟨q, hq⟩) = q :=
    kChartOf_apply a tor v W hW hsec q hq
  conv_lhs => rw [← h1]
  exact (kChartOf a tor v W hW hsec).left_inv hmem

lemma kkTransSrc_unfold (a : Work.Space.Assembly)
    (tor : ∀ v : Work.Space.Cusp, a.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ)))
    (v : Work.Space.Cusp) (W₁ W₂ : Set Work.Cusp.E2) (hW₁ : IsOpen W₁) (hW₂ : IsOpen W₂)
    (hsec₁ : ∀ y y' : Work.Cusp.E2, Work.Cusp.wOf v y ∈ W₁ → Work.Cusp.wOf v y' ∈ W₁ →
      (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y')
    (hsec₂ : ∀ y y' : Work.Cusp.E2, Work.Cusp.wOf v y ∈ W₂ → Work.Cusp.wOf v y' ∈ W₂ →
      (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y') :
    kkTransSrc a tor v W₁ W₂ hW₁ hW₂ hsec₁ hsec₂
      = (Work.Cusp.coreBoxSect W₁) ∩
        {q : Work.Cusp.E4 | (kChartOf a tor v W₁ hW₁ hsec₁).symm q
          ∈ (kChartOf a tor v W₂ hW₂ hsec₂).source} := by
  rw [kkTransSrc, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    kChartOf_target]
  rfl

lemma kkTrans_src_shift (a : Work.Space.Assembly)
    (tor : ∀ v : Work.Space.Cusp, a.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ)))
    (v : Work.Space.Cusp) {W₁ W₂ : Set Work.Cusp.E2} (hW₁ : IsOpen W₁) (hW₂ : IsOpen W₂)
    (hsec₁ : ∀ y y' : Work.Cusp.E2, Work.Cusp.wOf v y ∈ W₁ → Work.Cusp.wOf v y' ∈ W₁ →
      (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y')
    (hsec₂ : ∀ y y' : Work.Cusp.E2, Work.Cusp.wOf v y ∈ W₂ → Work.Cusp.wOf v y' ∈ W₂ →
      (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y')
    {q : Work.Cusp.E4} (hq : q ∈ kkTransSrc a tor v W₁ W₂ hW₁ hW₂ hsec₁ hsec₂) :
    ∃ m : Fin 2 → ℤ,
      (∀ᶠ x in 𝓝 q, kkTransMap a tor v W₁ W₂ hW₁ hW₂ hsec₁ hsec₂ x = kkShift v m x) := by
  rw [kkTransSrc_unfold a tor v W₁ W₂ hW₁ hW₂ hsec₁ hsec₂] at hq
  obtain ⟨hq₁, hq₂⟩ := hq
  simp only [Set.mem_ofPred_eq] at hq₂
  have hsymm := kChartOf_symm_apply a tor v W₁ hW₁ hsec₁ q hq₁
  rw [hsymm] at hq₂
  rw [kChartOf_source, Set.image_univ] at hq₂
  obtain ⟨z, hz⟩ := hq₂
  simp only [Work.Cusp.coreCoordM] at hz
  have hpair : ((⟨(Work.Cusp.cuspInvCore v (z : Work.Cusp.E4)).1, _⟩ : Work.Space.SquarePt),
      (tor v).symm (fun i => (((Work.Cusp.cuspInvCore v (z : Work.Cusp.E4)).2 i : ℝ) : AddCircle (1 : ℝ))))
      = ((⟨(Work.Cusp.cuspInvCore v q).1, _⟩ : Work.Space.SquarePt),
      (tor v).symm (fun i => (((Work.Cusp.cuspInvCore v q).2 i : ℝ) : AddCircle (1 : ℝ)))) :=
    a.incW_injective v hz
  have hp1 : (Work.Cusp.cuspInvCore v (z : Work.Cusp.E4)).1 = (Work.Cusp.cuspInvCore v q).1 := by
    have h := congrArg (fun w : Work.Space.SquarePt × a.Torus v => ((w.1 : Work.Space.SquarePt) : Work.Cusp.E2)) hpair
    simpa using h
  have hcl : ∀ i, (((Work.Cusp.cuspInvCore v (z : Work.Cusp.E4)).2 i : ℝ) : AddCircle (1 : ℝ))
      = (((Work.Cusp.cuspInvCore v q).2 i : ℝ) : AddCircle (1 : ℝ)) := by
    intro i
    have h2 := congrArg (fun w : Work.Space.SquarePt × a.Torus v => w.2) hpair
    have h3 : (fun i => (((Work.Cusp.cuspInvCore v (z : Work.Cusp.E4)).2 i : ℝ) : AddCircle (1 : ℝ)))
        = (fun i => (((Work.Cusp.cuspInvCore v q).2 i : ℝ) : AddCircle (1 : ℝ))) := by
      have h4 := congrArg (fun t : a.Torus v => (tor v) t) h2
      simpa using h4
    exact congrFun h3 i
  classical
  have hmi : ∀ i : Fin 2, ∃ k : ℤ,
      (Work.Cusp.cuspInvCore v (z : Work.Cusp.E4)).2 i - (Work.Cusp.cuspInvCore v q).2 i = (k : ℝ) := by
    intro i
    have h0 : ((((Work.Cusp.cuspInvCore v (z : Work.Cusp.E4)).2 i - (Work.Cusp.cuspInvCore v q).2 i : ℝ)) : AddCircle (1 : ℝ)) = 0 := by
      rw [AddCircle.coe_sub, hcl i, sub_self]
    rw [AddCircle.coe_eq_zero_iff] at h0
    obtain ⟨k, hk⟩ := h0
    exact ⟨k, by rw [← hk, zsmul_one]⟩
  let m : Fin 2 → ℤ := fun i => Classical.choose (hmi i)
  have hm : ∀ i, (Work.Cusp.cuspInvCore v (z : Work.Cusp.E4)).2 i - (Work.Cusp.cuspInvCore v q).2 i = (m i : ℝ) :=
    fun i => Classical.choose_spec (hmi i)
  have hyz : (Work.Cusp.cuspInvCore v (z : Work.Cusp.E4)).2
      = (Work.Cusp.cuspInvCore v q).2 + Work.Cusp.ofInt2 m := by
    ext i
    simp only [PiLp.add_apply, kk_ofInt2_apply]
    linarith [hm i]
  have hqbox : q ∈ Work.Cusp.coreBox :=
    Work.Cusp.CoreChartM.ccm_coreBoxSect_subset_coreBox W₁ hq₁
  have hzval : (z : Work.Cusp.E4) = kkShift v m q := by
    have h1 : (z : Work.Cusp.E4) = Work.Cusp.ThetaCore v (Work.Cusp.cuspInvCore v (z : Work.Cusp.E4)).1
        (Work.Cusp.cuspInvCore v (z : Work.Cusp.E4)).2 :=
      (Work.Cusp.ThetaCore_cuspInvCore v (z : Work.Cusp.E4)
        (Work.Cusp.CoreChartM.ccm_coreBoxSect_subset_coreBox W₂ z.2)).symm
    rw [h1, hp1, hyz,
      ThetaCore_kkShift v (Work.Cusp.cuspInvCore v q).1 (Work.Cusp.cuspInvCore v q).2 m,
      Work.Cusp.ThetaCore_cuspInvCore v q hqbox]
  have hshift : kkShift v m q ∈ Work.Cusp.coreBoxSect W₂ := by
    rw [← hzval]; exact z.2
  refine ⟨m, ?_⟩
  have hU : (Work.Cusp.coreBoxSect W₁ ∩ kkShift v m ⁻¹' Work.Cusp.coreBoxSect W₂) ∈ 𝓝 q :=
    ((Work.Cusp.CoreChartM.ccm_isOpen_coreBoxSect W₁ hW₁).inter
      ((Work.Cusp.CoreChartM.ccm_isOpen_coreBoxSect W₂ hW₂).preimage (continuous_kkShift v m))).mem_nhds
      ⟨hq₁, hshift⟩
  refine Filter.eventually_of_mem hU ?_
  intro x hx
  obtain ⟨hx₁, hx₂⟩ := hx
  simp only [kkTransMap]
  rw [kChartOf_symm_apply a tor v W₁ hW₁ hsec₁ x hx₁,
    coreCoordM_shift a tor v m x hx₁ hx₂]
  exact kChartOf_apply a tor v W₂ hW₂ hsec₂ (kkShift v m x) hx₂

end Work.RTOwed

namespace Work.RTOwed

open Work.RTInstance

lemma contDiff_kkShift (v : Work.Space.Cusp) (m : Fin 2 → ℤ) : ContDiff ℝ ∞ (kkShift v m) := by
  rw [kkShift_eq]
  exact ((kkLin _ _).contDiff).add contDiff_const

lemma fderiv_kkShift (v : Work.Space.Cusp) (m : Fin 2 → ℤ) (x : Work.Cusp.E4) :
    fderiv ℝ (kkShift v m) x = kkLin (Real.cos (kkAng v m)) (Real.sin (kkAng v m)) := by
  rw [kkShift_eq]
  exact ((kkLin _ _).hasFDerivAt.add_const _).fderiv

lemma kkTrans_iso (a : Work.Space.Assembly)
    (tor : ∀ v : Work.Space.Cusp, a.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ)))
    (v : Work.Space.Cusp) (W₁ W₂ : Set Work.Cusp.E2) (hW₁ : IsOpen W₁) (hW₂ : IsOpen W₂)
    (hsec₁ : ∀ y y' : Work.Cusp.E2, Work.Cusp.wOf v y ∈ W₁ → Work.Cusp.wOf v y' ∈ W₁ →
      (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y')
    (hsec₂ : ∀ y y' : Work.Cusp.E2, Work.Cusp.wOf v y ∈ W₂ → Work.Cusp.wOf v y' ∈ W₂ →
      (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y') :
    TransIso2 (kLayer v).model (kLayer v).model
      (kkTransMap a tor v W₁ W₂ hW₁ hW₂ hsec₁ hsec₂)
      (kkTransSrc a tor v W₁ W₂ hW₁ hW₂ hsec₁ hsec₂) := by
  constructor
  · intro q hq
    obtain ⟨m, hm⟩ := kkTrans_src_shift a tor v hW₁ hW₂ hsec₁ hsec₂ hq
    exact (((contDiff_kkShift v m).contDiffAt).contDiffWithinAt).congr_of_eventuallyEq_insert
      (Filter.Eventually.filter_mono nhdsWithin_le_nhds hm)
  · intro q hq u w
    obtain ⟨m, hm⟩ := kkTrans_src_shift a tor v hW₁ hW₂ hsec₁ hsec₂ hq
    have hfd : fderiv ℝ (kkTransMap a tor v W₁ W₂ hW₁ hW₂ hsec₁ hsec₂) q
        = kkLin (Real.cos (kkAng v m)) (Real.sin (kkAng v m)) := by
      rw [Filter.EventuallyEq.fderiv_eq hm, fderiv_kkShift]
    rw [hfd]
    show flatModel ((fillProf v).h₀)
        (kkTransMap a tor v W₁ W₂ hW₁ hW₂ hsec₁ hsec₂ q)
        (kkLin (Real.cos (kkAng v m)) (Real.sin (kkAng v m)) u)
        (kkLin (Real.cos (kkAng v m)) (Real.sin (kkAng v m)) w)
      = flatModel ((fillProf v).h₀) q u w
    rw [flatModel_apply, flatModel_apply, kkLin_apply, kkLin_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.cons_val_three]
    have hcs : Real.cos (kkAng v m) ^ 2 + Real.sin (kkAng v m) ^ 2 = 1 :=
      Real.cos_sq_add_sin_sq _
    linear_combination (u 0 * w 0 + u 1 * w 1) * hcs


/-! ## The transition of two core charts of one cusp is a flat isometry -/

theorem coreTrans (a : Work.Space.Assembly)
    (tor : ∀ v : Work.Space.Cusp, a.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ)))
    (v : Work.Space.Cusp) (W₁ W₂ : Set Work.Cusp.E2) (hW₁ : IsOpen W₁) (hW₂ : IsOpen W₂)
    (hsec₁ : ∀ y y' : Work.Cusp.E2, Work.Cusp.wOf v y ∈ W₁ → Work.Cusp.wOf v y' ∈ W₁ →
      (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y')
    (hsec₂ : ∀ y y' : Work.Cusp.E2, Work.Cusp.wOf v y ∈ W₂ → Work.Cusp.wOf v y' ∈ W₂ →
      (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y') :
    Work.RTOwed.TransIso2 (Work.RTOwed.kLayer v).model (Work.RTOwed.kLayer v).model
        (Work.RTOwed.kkTransMap a tor v W₁ W₂ hW₁ hW₂ hsec₁ hsec₂)
        (Work.RTOwed.kkTransSrc a tor v W₁ W₂ hW₁ hW₂ hsec₁ hsec₂) ∧
      Work.RTOwed.TransIso2 (Work.RTOwed.kLayer v).model (Work.RTOwed.kLayer v).model
        (Work.RTOwed.kkTransMap a tor v W₂ W₁ hW₂ hW₁ hsec₂ hsec₁)
        (Work.RTOwed.kkTransSrc a tor v W₂ W₁ hW₂ hW₁ hsec₂ hsec₁) :=
  ⟨kkTrans_iso a tor v W₁ W₂ hW₁ hW₂ hsec₁ hsec₂,
    kkTrans_iso a tor v W₂ W₁ hW₂ hW₁ hsec₂ hsec₁⟩

end Work.RTOwed
