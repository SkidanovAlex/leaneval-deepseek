/-
# Auxiliaries for the junction ↔ collar transitions of the filling atlas of `M̂`

This file collects the definition-level and analytic facts used by
`Work.RTOWed.jTrans_coll_iso`:

* the explicit inverse `Work.RTOWed.polarToUHSInv` of the polar ↔ upper-half-space coordinate
  change `Work.Cusp.polarToUHS` of a cusp, together with its smoothness on `{q 3 > 0}`;
* the smoothness of `Work.Cusp.polarToUHS`;
* the basic API of the junction and collar charts (`jChart`, `cChart`) and of their transition
  sources `jcTransSrc`, `cjTransSrc`;
* the two-branch computation of `Work.Cusp.cuspCoordMTop` and the norm comparisons that show that
  the collar branch of a junction chart lies in the collar of the filling piece.
-/
import Mathlib
import Submission.Work.RTOwed.FillAtlas

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function
open scoped RealInnerProductSpace

namespace Work.RTOwed

/-! ## The polar ↔ upper half space coordinate change of a cusp -/

/-- The horizontal part of `polarToUHS v q`. -/
def uhsX (v : Work.Space.Cusp) (q : Work.Cusp.E4) : Work.Cusp.E3 :=
  (‖Work.Cusp.slope v‖ / (2 * Real.pi) * q 1) • Work.Cusp.frame1 v
    + q 2 • Work.Cusp.frame2 v + q 3 • Work.Cusp.frame3 v

/-- The horizontal part of `polarToUHS v q` is `uhsX v q`. -/
theorem xOf_polarToUHS (v : Work.Space.Cusp) (q : Work.Cusp.E4) :
    Work.Cusp.xOf (Work.Cusp.polarToUHS v q) = uhsX v q := by
  unfold Work.Cusp.polarToUHS Work.Cusp.xOf uhsX
  ext i
  fin_cases i <;> simp [PiLp.add_apply, PiLp.smul_apply]

/-- **The explicit inverse of the polar ↔ upper half space coordinate change**: given a UHS
coordinate `q` with `0 < q 3`, recover the polar coordinates `(r, θ, w₁, w₂)`:
`r = R₀ − log (q 3)`, `w_i = ⟪x, frame_i⟫`, `θ = (2π/‖σ_v‖)⟪x, frame₁⟫`. -/
def polarToUHSInv (v : Work.Space.Cusp) (q : Work.Cusp.E4) : Work.Cusp.E4 :=
  !₂[Work.Cusp.R0 - Real.log (q 3),
     (2 * Real.pi / ‖Work.Cusp.slope v‖) * inner ℝ (Work.Cusp.xOf q) (Work.Cusp.frame1 v),
     inner ℝ (Work.Cusp.xOf q) (Work.Cusp.frame2 v),
     inner ℝ (Work.Cusp.xOf q) (Work.Cusp.frame3 v)]

@[simp] theorem polarToUHSInv_apply_zero (v : Work.Space.Cusp) (q : Work.Cusp.E4) :
    polarToUHSInv v q 0 = Work.Cusp.R0 - Real.log (q 3) := by simp [polarToUHSInv]

@[simp] theorem polarToUHSInv_apply_one (v : Work.Space.Cusp) (q : Work.Cusp.E4) :
    polarToUHSInv v q 1
      = (2 * Real.pi / ‖Work.Cusp.slope v‖) * inner ℝ (Work.Cusp.xOf q)
          (Work.Cusp.frame1 v) := by
  simp [polarToUHSInv]

@[simp] theorem polarToUHSInv_apply_two (v : Work.Space.Cusp) (q : Work.Cusp.E4) :
    polarToUHSInv v q 2 = inner ℝ (Work.Cusp.xOf q) (Work.Cusp.frame2 v) := by
  simp [polarToUHSInv]

@[simp] theorem polarToUHSInv_apply_three (v : Work.Space.Cusp) (q : Work.Cusp.E4) :
    polarToUHSInv v q 3 = inner ℝ (Work.Cusp.xOf q) (Work.Cusp.frame3 v) := by
  simp [polarToUHSInv]

/-- The slope of a cusp is nonzero. -/
theorem slope_norm_ne_zero (v : Work.Space.Cusp) : ‖Work.Cusp.slope v‖ ≠ 0 := by
  intro h
  have hf : Work.Cusp.frame1 v = 0 := by rw [Work.Cusp.frame1, h]; simp
  have := (Work.Cusp.frame_orthonormal v).2.2.2.1
  rw [hf] at this; simp at this

theorem inner_polarToUHS_frame1 (v : Work.Space.Cusp) (q : Work.Cusp.E4) :
    inner ℝ (Work.Cusp.xOf (Work.Cusp.polarToUHS v q)) (Work.Cusp.frame1 v)
      = ‖Work.Cusp.slope v‖ / (2 * Real.pi) * q 1 := by
  rw [xOf_polarToUHS]
  obtain ⟨h12, h13, h23, h1, h2, h3⟩ := Work.Cusp.frame_orthonormal v
  have h21 : inner ℝ (Work.Cusp.frame2 v) (Work.Cusp.frame1 v) = 0 := by
    rw [real_inner_comm]; exact h12
  have h31 : inner ℝ (Work.Cusp.frame3 v) (Work.Cusp.frame1 v) = 0 := by
    rw [real_inner_comm]; exact h13
  rw [uhsX, inner_add_left, inner_add_left, inner_smul_left, inner_smul_left, inner_smul_left,
    h21, h31, real_inner_self_eq_norm_sq, h1]
  ring_nf; simp

theorem inner_polarToUHS_frame2 (v : Work.Space.Cusp) (q : Work.Cusp.E4) :
    inner ℝ (Work.Cusp.xOf (Work.Cusp.polarToUHS v q)) (Work.Cusp.frame2 v) = q 2 := by
  rw [xOf_polarToUHS]
  obtain ⟨h12, h13, h23, h1, h2, h3⟩ := Work.Cusp.frame_orthonormal v
  have h32 : inner ℝ (Work.Cusp.frame3 v) (Work.Cusp.frame2 v) = 0 := by
    rw [real_inner_comm]; exact h23
  rw [uhsX, inner_add_left, inner_add_left, inner_smul_left, inner_smul_left, inner_smul_left,
    h12, h32, real_inner_self_eq_norm_sq, h2]
  ring_nf; simp

theorem inner_polarToUHS_frame3 (v : Work.Space.Cusp) (q : Work.Cusp.E4) :
    inner ℝ (Work.Cusp.xOf (Work.Cusp.polarToUHS v q)) (Work.Cusp.frame3 v) = q 3 := by
  rw [xOf_polarToUHS]
  obtain ⟨h12, h13, h23, h1, h2, h3⟩ := Work.Cusp.frame_orthonormal v
  rw [uhsX, inner_add_left, inner_add_left, inner_smul_left, inner_smul_left, inner_smul_left,
    h13, h23, real_inner_self_eq_norm_sq, h3]
  ring_nf; simp

/-- `polarToUHSInv` is a left inverse of `polarToUHS`. -/
theorem polarToUHSInv_polarToUHS (v : Work.Space.Cusp) (q : Work.Cusp.E4) :
    polarToUHSInv v (Work.Cusp.polarToUHS v q) = q := by
  ext i
  fin_cases i <;> dsimp only
  · show polarToUHSInv v (Work.Cusp.polarToUHS v q) 0 = q 0
    rw [polarToUHSInv_apply_zero]
    rw [show (Work.Cusp.polarToUHS v q) 3 = Real.exp (Work.Cusp.R0 - q 0) from rfl, Real.log_exp]
    ring
  · show polarToUHSInv v (Work.Cusp.polarToUHS v q) 1 = q 1
    rw [polarToUHSInv_apply_one, inner_polarToUHS_frame1]
    field_simp [slope_norm_ne_zero v, Real.pi_ne_zero]
  · show polarToUHSInv v (Work.Cusp.polarToUHS v q) 2 = q 2
    rw [polarToUHSInv_apply_two, inner_polarToUHS_frame2]
  · show polarToUHSInv v (Work.Cusp.polarToUHS v q) 3 = q 3
    rw [polarToUHSInv_apply_three, inner_polarToUHS_frame3]

theorem contDiff_xOf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.Cusp.xOf) := by
  unfold Work.Cusp.xOf
  rw [contDiff_piLp]
  intro i
  fin_cases i <;> simp <;> fun_prop

/-- `polarToUHSInv v` is smooth on the upper half space `{q 3 > 0}`. -/
theorem polarToUHSInv_contDiffOn (v : Work.Space.Cusp) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (polarToUHSInv v) {q : Work.Cusp.E4 | 0 < q 3} := by
  rw [contDiffOn_piLp]
  intro i
  fin_cases i <;> simp only [polarToUHSInv, PiLp.toLp_apply] <;> simp
  · exact (contDiffOn_const (c := Work.Cusp.R0)).sub
      (ContDiffOn.log (f := fun x : Work.Cusp.E4 => x 3) (by fun_prop)
        (fun q hq => ne_of_gt hq))
  · exact (ContDiff.mul contDiff_const (ContDiff.inner ℝ contDiff_xOf contDiff_const)).contDiffOn
  · exact (ContDiff.inner ℝ contDiff_xOf contDiff_const).contDiffOn
  · exact (ContDiff.inner ℝ contDiff_xOf contDiff_const).contDiffOn

/-- `Work.Cusp.polarToUHS v` is smooth. -/
theorem cusp_polarToUHS_contDiff (v : Work.Space.Cusp) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.Cusp.polarToUHS v) := by
  unfold Work.Cusp.polarToUHS
  rw [contDiff_piLp]
  intro i
  fin_cases i <;> simp <;> fun_prop



/-! ## The API of the junction and collar charts -/

theorem jChart_target (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (P : JPin a v) :
    (jChart a D v P).target = jBoxR a v P := by
  rw [jChart, OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.ofSet_target,
    jChartOf_target, OpenPartialHomeomorph.ofSet_symm, OpenPartialHomeomorph.ofSet_apply,
    Set.preimage_id]
  ext q
  simp only [Set.mem_inter_iff]
  constructor
  · rintro ⟨h1, h2⟩; exact h1
  · intro h1; exact ⟨h1, h1.1⟩

theorem jChart_symm (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (P : JPin a v) {q : Work.Cusp.E4} (hq : q ∈ jBoxR a v P) :
    (jChart a D v P).symm q = jCoordM a v (D v) P.cU P.k P.W P.kx P.δ ⟨q, hq.1⟩ := by
  have h : (jChart a D v P) (jCoordM a v (D v) P.cU P.k P.W P.kx P.δ ⟨q, hq.1⟩) = q :=
    jChart_apply a D v P q hq
  have h2 : jCoordM a v (D v) P.cU P.k P.W P.kx P.δ ⟨q, hq.1⟩ ∈ (jChart a D v P).source := by
    rw [jChart_source]
    show _ ∈ jCoordM a v (D v) P.cU P.k P.W P.kx P.δ ''
      {q : {q : Work.Cusp.E4 // q ∈ jBox v P.cU P.k P.W P.kx P.δ} |
        (q : Work.Cusp.E4) ∈ jBoxR a v P}
    exact ⟨⟨q, hq.1⟩, hq, rfl⟩
  have h3 := OpenPartialHomeomorph.left_inv (jChart a D v P) h2
  rw [h] at h3
  exact h3

theorem cChart_target (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (c : Work.Cusp.E3) (δ : ℝ) (hδ : δ ≤ 1/2)
    (hne : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c δ}) :
    (cChart a D v c δ hδ hne).target = cBoxR v c δ := by
  rw [cChart, OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.ofSet_target,
    cChartOf_target, OpenPartialHomeomorph.ofSet_symm, OpenPartialHomeomorph.ofSet_apply,
    Set.preimage_id]
  ext q
  simp only [Set.mem_inter_iff]
  constructor
  · rintro ⟨h1, h2⟩; exact h1
  · intro h1; exact ⟨h1, h1.1⟩

theorem cChart_symm (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (c : Work.Cusp.E3) (δ : ℝ) (hδ : δ ≤ 1/2)
    (hne : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c δ})
    {q : Work.Cusp.E4} (hq : q ∈ cBoxR v c δ) :
    (cChart a D v c δ hδ hne).symm q
      = Work.Cusp.cuspCoordMTop a v (D v) c δ ⟨q, hq.1⟩ := by
  have h : cChart a D v c δ hδ hne (Work.Cusp.cuspCoordMTop a v (D v) c δ ⟨q, hq.1⟩) = q :=
    cChart_apply a D v c δ hδ hne q hq.1 hq
  have h2 : Work.Cusp.cuspCoordMTop a v (D v) c δ ⟨q, hq.1⟩ ∈ (cChart a D v c δ hδ hne).source := by
    rw [cChart_source]
    exact ⟨⟨q, hq.1⟩, hq, rfl⟩
  have h3 := OpenPartialHomeomorph.left_inv (cChart a D v c δ hδ hne) h2
  rw [h] at h3
  exact h3

theorem mem_jcTransSrc (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (P : JPin a v) (c : Work.Cusp.E3) (δ : ℝ) (hδ : δ ≤ 1/2)
    (hne : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c δ}) (q : Work.Cusp.E4) :
    q ∈ jcTransSrc a D v P c δ hδ hne ↔
      q ∈ jBoxR a v P ∧ (jChart a D v P).symm q ∈ (cChart a D v c δ hδ hne).source := by
  rw [jcTransSrc, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    jChart_target]
  rfl

theorem mem_cjTransSrc (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (P : JPin a v) (c : Work.Cusp.E3) (δ : ℝ) (hδ : δ ≤ 1/2)
    (hne : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c δ}) (q : Work.Cusp.E4) :
    q ∈ cjTransSrc a D v P c δ hδ hne ↔
      q ∈ cBoxR v c δ ∧ (cChart a D v c δ hδ hne).symm q ∈ (jChart a D v P).source := by
  rw [cjTransSrc, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    cChart_target]
  rfl

/-! ## The two branches of `cuspCoordMTop` -/

theorem cuspCoordMTop_of_lt (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (D : Work.Cusp.CuspGlueData a v) (c : Work.Cusp.E3) (δ : ℝ)
    (x : {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c δ})
    (h : (x : Work.Cusp.E4) 3 < Work.Cusp.beta (Work.Cusp.xOf (x : Work.Cusp.E4))) :
    Work.Cusp.cuspCoordMTop a v D c δ x = a.incMbar (D.mbarLow (x : Work.Cusp.E4)) := by
  rw [Work.Cusp.cuspCoordMTop]
  exact dite_eq_left h

theorem cuspCoordMTop_of_ge (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (D : Work.Cusp.CuspGlueData a v) (c : Work.Cusp.E3) (δ : ℝ)
    (x : {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c δ})
    (h : ¬ (x : Work.Cusp.E4) 3 < Work.Cusp.beta (Work.Cusp.xOf (x : Work.Cusp.E4))) :
    Work.Cusp.cuspCoordMTop a v D c δ x =
      a.incW v
        ((⟨(Work.Cusp.cuspInvOuter v (x : Work.Cusp.E4)).1, by
            simpa only [Work.Space.Sq, Work.Cusp.Sq] using
              Work.Cusp.cuspInvOuter_mem_SqTop v c δ (x : Work.Cusp.E4) ⟨x.2, not_lt.mp h⟩⟩ :
            Work.Space.SquarePt),
          D.tor.symm (fun i =>
            (((Work.Cusp.cuspInvOuter v (x : Work.Cusp.E4)).2 i : ℝ) : AddCircle (1 : ℝ)))) := by
  rw [Work.Cusp.cuspCoordMTop]
  exact dite_eq_right h

/-! ## Norm comparisons for the two branches -/

theorem nrm_cuspInvInner_le_half (v : Work.Space.Cusp) {q : Work.Cusp.E4}
    (hq : q ∈ Work.Cusp.polarBox) (h : q 0 ≤ Work.Cusp.rJ) :
    Work.Cusp.nrm (Work.Cusp.cuspInvInner v q).1 ≤ 1/2 := by
  rw [Work.Cusp.cuspInvInner_nrm v q hq h]
  have h2 : q 0 / (2 * Work.Cusp.rJ) ≤ Work.Cusp.rJ / (2 * Work.Cusp.rJ) := by
    apply div_le_div_of_nonneg_right h
    rw [Work.Cusp.rJ]; norm_num
  have h3 : Work.Cusp.rJ / (2 * Work.Cusp.rJ) = 1/2 := by rw [Work.Cusp.rJ]; norm_num
  linarith

theorem nrm_cuspInvOuter_gt_half (v : Work.Space.Cusp) (c : Work.Cusp.E3) (δ : ℝ)
    {x : Work.Cusp.E4} (hx : x ∈ Work.Cusp.cuspSourceTop v c δ) (hx3 : x 3 < Work.Cusp.sJ) :
    1/2 < Work.Cusp.nrm (Work.Cusp.cuspInvOuter v x).1 := by
  by_contra h
  push Not at h
  have hheight := Work.Cusp.cuspInvOuter_heightTop v c δ x hx
  have hle : Work.Cusp.sJ ≤ Work.Cusp.collarS v (Work.Cusp.cuspInvOuter v x).1
      (Work.Cusp.cuspInvOuter v x).2 := by
    rw [Work.Cusp.collarS]
    have hanti := Work.Cusp.collarHeight_strictAntiOn
      (Work.Cusp.beta (Work.Cusp.cuspX v (Work.Cusp.u (Work.Cusp.cuspInvOuter v x).1)
        (Work.Cusp.cuspInvOuter v x).2)) (Work.Cusp.beta_pos _)
      (lt_of_le_of_lt (Work.Cusp.beta_le_max _) Work.Cusp.betaMax_lt_sJ)
    have h2 := (hanti.le_iff_ge (a := (1/2 : ℝ))
      (b := Work.Cusp.nrm (Work.Cusp.cuspInvOuter v x).1) (by trivial) (by trivial)).mpr h
    rwa [Work.Cusp.collarHeight_half] at h2
  linarith

/-! ## The collar branch of a junction chart is above the junction -/

theorem jcTransSrc_gt (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (P : JPin a v) (c : Work.Cusp.E3) (δ : ℝ) (hδ : δ ≤ 1/2)
    (hne : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c δ})
    {q : Work.Cusp.E4} (hq : q ∈ jcTransSrc a D v P c δ hδ hne) :
    Work.Cusp.rJ < q 0 := by
  rw [mem_jcTransSrc] at hq
  obtain ⟨hqR, hqin⟩ := hq
  by_contra hle
  have hle' : q 0 ≤ Work.Cusp.rJ := not_lt.mp hle
  have hqin2 : jCoordM a v (D v) P.cU P.k P.W P.kx P.δ ⟨q, hqR.1⟩ ∈
      (cChart a D v c δ hδ hne).source := by
    rwa [jChart_symm a D v P hqR] at hqin
  rw [cChart_source] at hqin2
  obtain ⟨x, hxmem, hxeq⟩ := hqin2
  by_cases hxlt : (x : Work.Cusp.E4) 3 < Work.Cusp.beta (Work.Cusp.xOf (x : Work.Cusp.E4))
  · rw [cuspCoordMTop_of_lt a v (D v) c δ x hxlt] at hxeq
    rw [jCoordM_of_le (a := a) (v := v) (D := D v) (cU := P.cU) (k := P.k) (W := P.W)
      (kx := P.kx) (δ := P.δ) hqR.1 hle'] at hxeq
    exact a.incMbar_ne_incY (fun ⟨hxT, _⟩ => (D v).mbarLow_not_TsetTop c δ x.2 hxlt hxT) hxeq
  · have hxge : Work.Cusp.beta (Work.Cusp.xOf (x : Work.Cusp.E4)) ≤ (x : Work.Cusp.E4) 3 :=
      not_lt.mp hxlt
    have hxsrc : (x : Work.Cusp.E4) ∈ Work.Cusp.cuspSourceTop v c δ := ⟨x.2, hxge⟩
    have hnrmX' : 1/2 < Work.Cusp.nrm (Work.Cusp.cuspInvOuter v (x : Work.Cusp.E4)).1 :=
      nrm_cuspInvOuter_gt_half v c δ hxsrc hxmem.2
    rw [cuspCoordMTop_of_ge a v (D v) c δ x hxlt] at hxeq
    rw [jCoordM_of_le (a := a) (v := v) (D := D v) (cU := P.cU) (k := P.k) (W := P.W)
      (kx := P.kx) (δ := P.δ) hqR.1 hle'] at hxeq
    have hpair := a.incW_injective v hxeq
    have hnrmeq : Work.Cusp.nrm (Work.Cusp.cuspInvOuter v (x : Work.Cusp.E4)).1 =
        Work.Cusp.nrm (Work.Cusp.cuspInvInner v q).1 := by
      have h := congrArg (fun z : Work.Space.SquarePt × a.Torus v =>
        Work.Cusp.nrm ((z.1 : Work.Space.SquarePt) : Work.Cusp.E2)) hpair
      simpa using h
    have hnrmX : Work.Cusp.nrm (Work.Cusp.cuspInvInner v q).1 ≤ 1/2 :=
      nrm_cuspInvInner_le_half v (jBox_subset_polarBox v P.cU P.k P.W P.kx P.δ hqR.1) hle'
    linarith

end Work.RTOwed
