import Mathlib
import Submission.Work.Sphere.Basic

noncomputable section

open scoped Topology
open Submission.Sphere (Sph pole polePt negPolePt)

namespace Work.Sphere

/-! ### The coordinate maps `dV` (delete the last coordinate) and `lV` (append a zero)

For `v : ℝ^{n+2}` we write `dV v : ℝ^{n+1}` for `v` with its last coordinate deleted, and for
`y : ℝ^{n+1}` we write `lV y : ℝ^{n+2}` for `y` with a zero appended.  The pole
`e = pole (n+1)` is the last standard basis vector of `ℝ^{n+2}`. -/

/-- Delete the last coordinate of a vector of `ℝ^{n+2}`. -/
noncomputable def dV {n : ℕ} (v : EuclideanSpace ℝ (Fin (n+2))) : EuclideanSpace ℝ (Fin (n+1)) :=
  WithLp.toLp 2 (fun i : Fin (n+1) => v (Fin.castSucc i))

/-- Append a zero coordinate at the end of a vector of `ℝ^{n+1}`. -/
noncomputable def lV {n : ℕ} (y : EuclideanSpace ℝ (Fin (n+1))) : EuclideanSpace ℝ (Fin (n+2)) :=
  WithLp.toLp 2 (@Fin.snoc (n+1) (fun _ : Fin (n+2) => ℝ) (fun i : Fin (n+1) => y i) 0)

@[simp] lemma dV_ofLp {n : ℕ} (v : EuclideanSpace ℝ (Fin (n+2))) (i : Fin (n+1)) :
    (dV v).ofLp i = v.ofLp (Fin.castSucc i) := by
  rw [dV, PiLp.toLp_apply]

@[simp] lemma lV_ofLp_castSucc {n : ℕ} (y : EuclideanSpace ℝ (Fin (n+1))) (i : Fin (n+1)) :
    (lV y).ofLp (Fin.castSucc i) = y.ofLp i := by
  rw [lV, PiLp.toLp_apply, Fin.snoc_castSucc]

@[simp] lemma lV_ofLp_last {n : ℕ} (y : EuclideanSpace ℝ (Fin (n+1))) :
    (lV y).ofLp (Fin.last (n+1)) = 0 := by
  rw [lV, PiLp.toLp_apply, Fin.snoc_last]

@[simp] lemma pole_ofLp_castSucc {n : ℕ} (i : Fin (n+1)) :
    (pole (n+1) : EuclideanSpace ℝ (Fin (n+2))).ofLp (Fin.castSucc i) = 0 := by
  rw [Submission.Sphere.pole, PiLp.single_apply, if_neg (Fin.castSucc_ne_last i)]

@[simp] lemma pole_ofLp_last {n : ℕ} :
    (pole (n+1) : EuclideanSpace ℝ (Fin (n+2))).ofLp (Fin.last (n+1)) = 1 := by
  rw [Submission.Sphere.pole, PiLp.single_apply, if_pos rfl]

@[simp] lemma negPole_ofLp_last {n : ℕ} :
    (-pole (n+1) : EuclideanSpace ℝ (Fin (n+2))).ofLp (Fin.last (n+1)) = -1 := by
  simp

@[simp] lemma dV_lV {n : ℕ} (y : EuclideanSpace ℝ (Fin (n+1))) : dV (lV y) = y := by
  apply PiLp.ext; intro i; simp

@[simp] lemma dV_zero {n : ℕ} : dV (0 : EuclideanSpace ℝ (Fin (n+2))) = 0 := by
  apply PiLp.ext; intro i; simp

@[simp] lemma dV_pole {n : ℕ} : dV (pole (n+1) : EuclideanSpace ℝ (Fin (n+2))) = 0 := by
  apply PiLp.ext; intro i; simp

lemma dV_smul {n : ℕ} (a : ℝ) (v : EuclideanSpace ℝ (Fin (n+2))) : dV (a • v) = a • dV v := by
  apply PiLp.ext; intro i; simp [smul_eq_mul]

lemma dV_sub_smul_pole {n : ℕ} (v : EuclideanSpace ℝ (Fin (n+2))) (c : ℝ) :
    dV (v - c • pole (n+1)) = dV v := by
  apply PiLp.ext; intro i; simp [smul_eq_mul]

/-- The decomposition of `v` into its equatorial part and its last coordinate. -/
lemma decomp {n : ℕ} (v : EuclideanSpace ℝ (Fin (n+2))) :
    lV (dV v) = v - (v.ofLp (Fin.last (n+1))) • pole (n+1) := by
  apply PiLp.ext; intro j
  rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl <;> simp [smul_eq_mul]

lemma lV_smul {n : ℕ} (a : ℝ) (y : EuclideanSpace ℝ (Fin (n+1))) : lV (a • y) = a • lV y := by
  apply PiLp.ext; intro j
  rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl <;> simp [smul_eq_mul]

@[simp] lemma norm_lV {n : ℕ} (y : EuclideanSpace ℝ (Fin (n+1))) : ‖lV y‖ = ‖y‖ := by
  rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  congr 1
  rw [Fin.sum_univ_castSucc]
  simp

lemma eq_smul_pole_of_dV_eq_zero {n : ℕ} {v : EuclideanSpace ℝ (Fin (n+2))} (h : dV v = 0) :
    v = (v.ofLp (Fin.last (n+1))) • pole (n+1) := by
  have h2 := decomp v
  rw [h] at h2
  have h3 : lV (0 : EuclideanSpace ℝ (Fin (n+1))) = 0 := by
    apply PiLp.ext; intro j
    rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl <;> simp
  rw [h3] at h2
  exact sub_eq_zero.mp h2.symm

lemma eq_pole_or_negPole_of_eq_smul {n : ℕ} {v : EuclideanSpace ℝ (Fin (n+2))} {c : ℝ}
    (hv : ‖v‖ = 1) (h : v = c • pole (n+1)) : v = pole (n+1) ∨ v = -pole (n+1) := by
  have hn : |c| = 1 := by
    calc |c| = ‖c‖ := (Real.norm_eq_abs c).symm
      _ = ‖c‖ * ‖pole (n+1)‖ := by rw [Submission.Sphere.norm_pole, mul_one]
      _ = ‖c • pole (n+1)‖ := (norm_smul c (pole (n+1))).symm
      _ = ‖v‖ := by rw [← h]
      _ = 1 := hv
  rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp hn with hc | hc
  · left; rw [h, hc, one_smul]
  · right; rw [h, hc, neg_one_smul]

lemma dV_ne_zero_of {n : ℕ} {v : EuclideanSpace ℝ (Fin (n+2))} (hv : ‖v‖ = 1)
    (h1 : v ≠ pole (n+1)) (h2 : v ≠ -pole (n+1)) : dV v ≠ 0 := by
  intro h
  rcases eq_pole_or_negPole_of_eq_smul hv (eq_smul_pole_of_dV_eq_zero h) with h' | h'
  · exact h1 h'
  · exact h2 h'

/-! ### Continuity of `dV` and `lV` -/

lemma continuous_dV {n : ℕ} : Continuous (dV (n := n)) := by
  unfold dV
  refine (PiLp.continuous_toLp 2 (fun _ : Fin (n+1) => ℝ)).comp (continuous_pi fun i => ?_)
  exact (continuous_apply (Fin.castSucc i)).comp (PiLp.continuous_ofLp 2 (fun _ : Fin (n+2) => ℝ))

lemma continuous_lV {n : ℕ} : Continuous (lV (n := n)) := by
  unfold lV
  refine (PiLp.continuous_toLp 2 (fun _ : Fin (n+2) => ℝ)).comp (continuous_pi fun j => ?_)
  rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
  · have h : Continuous (fun a : EuclideanSpace ℝ (Fin (n+1)) => a.ofLp i) :=
      (continuous_apply i).comp (PiLp.continuous_ofLp 2 (fun _ : Fin (n+1) => ℝ))
    refine h.congr ?_
    intro a; rw [Fin.snoc_castSucc]
  · have h : Continuous (fun _ : EuclideanSpace ℝ (Fin (n+1)) => (0:ℝ)) := continuous_const
    refine h.congr ?_
    intro a; rw [Fin.snoc_last]

/-! ### The doubly punctured sphere -/

/-- The doubly punctured sphere `S^{n+1} ∖ {±e}`. -/
abbrev DP (n : ℕ) : Type :=
  {x : Sph (n+1) // x ≠ polePt (n+1) ∧ x ≠ negPolePt (n+1)}

/-- The underlying vector of a point of the doubly punctured sphere. -/
noncomputable def vOf {n : ℕ} (x : DP n) : EuclideanSpace ℝ (Fin (n+2)) := x.1.1

lemma norm_eq_one_of_mem_sphere {k : ℕ} {x : EuclideanSpace ℝ (Fin k)}
    (h : x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1) : ‖x‖ = 1 := by
  have h' : dist x 0 = 1 := Metric.mem_sphere.mp h
  rwa [dist_eq_norm, sub_zero] at h'

lemma mem_sphere_of_norm_eq_one {k : ℕ} {x : EuclideanSpace ℝ (Fin k)} (h : ‖x‖ = 1) :
    x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1 := by
  rw [Metric.mem_sphere, dist_eq_norm, sub_zero, h]

lemma norm_vOf {n : ℕ} (x : DP n) : ‖vOf x‖ = 1 :=
  norm_eq_one_of_mem_sphere x.1.2

lemma vOf_ne_pole {n : ℕ} (x : DP n) : vOf x ≠ pole (n+1) := by
  intro h; exact x.2.1 (Subtype.ext h)

lemma vOf_ne_negPole {n : ℕ} (x : DP n) : vOf x ≠ -pole (n+1) := by
  intro h; exact x.2.2 (Subtype.ext h)

lemma continuous_vOf {n : ℕ} : Continuous (vOf (n := n)) := by
  show Continuous (fun x : DP n => (x.1.1 : EuclideanSpace ℝ (Fin (n+2))))
  exact continuous_subtype_val.comp continuous_subtype_val

lemma dV_ne_zero_vOf {n : ℕ} (x : DP n) : dV (vOf x) ≠ 0 :=
  dV_ne_zero_of (norm_vOf x) (vOf_ne_pole x) (vOf_ne_negPole x)

/-- The unit vector in the direction of `w` (`0` stays `0`). -/
noncomputable def uvec {k : ℕ} (w : EuclideanSpace ℝ (Fin k)) : EuclideanSpace ℝ (Fin k) :=
  ‖w‖⁻¹ • w

@[simp] lemma norm_uvec {k : ℕ} {w : EuclideanSpace ℝ (Fin k)} (h : w ≠ 0) : ‖uvec w‖ = 1 := by
  rw [uvec, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg w)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)]

lemma uvec_of_norm_one {k : ℕ} {w : EuclideanSpace ℝ (Fin k)} (h : ‖w‖ = 1) : uvec w = w := by
  rw [uvec, h, inv_one, one_smul]

lemma uvec_lV {n : ℕ} (w : EuclideanSpace ℝ (Fin (n+1))) : uvec (lV w) = lV (uvec w) := by
  simp only [uvec, norm_lV, lV_smul]

/-- A vector on the unit sphere avoiding `± e` gives a point of `S^{n+1}` avoiding `± e`. -/
lemma subtype_ne_polePt_of {n : ℕ} {v : EuclideanSpace ℝ (Fin (n+2))}
    (hv : v ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+2))) 1) (h : v ≠ pole (n+1)) :
    (⟨v, hv⟩ : Sph (n+1)) ≠ polePt (n+1) := by
  intro hh; exact h (Subtype.ext_iff.mp hh)

lemma subtype_ne_negPolePt_of {n : ℕ} {v : EuclideanSpace ℝ (Fin (n+2))}
    (hv : v ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+2))) 1) (h : v ≠ -pole (n+1)) :
    (⟨v, hv⟩ : Sph (n+1)) ≠ negPolePt (n+1) := by
  intro hh; exact h (Subtype.ext_iff.mp hh)

/-! ### The forward map `A → S^n` -/

noncomputable def fFun {n : ℕ} (x : DP n) : Sph n :=
  ⟨uvec (dV (vOf x)), mem_sphere_of_norm_eq_one (norm_uvec (dV_ne_zero_vOf x))⟩

lemma continuous_fFun {n : ℕ} : Continuous (fFun (n := n)) := by
  have hc : Continuous (fun x : DP n => uvec (dV (vOf x))) := by
    have hw : Continuous (fun x : DP n => dV (vOf x)) := continuous_dV.comp continuous_vOf
    have hinv : Continuous (fun x : DP n => (‖dV (vOf x)‖)⁻¹) :=
      (continuous_norm.comp hw).inv₀ (fun x => norm_ne_zero_iff.mpr (dV_ne_zero_vOf x))
    exact (hinv.smul hw).congr (fun x => rfl)
  exact Continuous.subtype_mk hc
    (fun x => mem_sphere_of_norm_eq_one (norm_uvec (dV_ne_zero_vOf x)))

noncomputable def f {n : ℕ} : C(DP n, Sph n) := ⟨fFun, continuous_fFun⟩

/-! ### The backward map `S^n → A` -/

noncomputable def gVec {n : ℕ} (y : Sph n) : EuclideanSpace ℝ (Fin (n+2)) :=
  lV (y.1 : EuclideanSpace ℝ (Fin (n+1)))

lemma norm_sph {n : ℕ} (y : Sph n) : ‖(y.1 : EuclideanSpace ℝ (Fin (n+1)))‖ = 1 :=
  norm_eq_one_of_mem_sphere y.2

lemma gVec_ne_pole {n : ℕ} (y : Sph n) : gVec y ≠ (pole (n+1) : EuclideanSpace ℝ (Fin (n+2))) := by
  intro h
  have h' := congrArg (fun z => z.ofLp (Fin.last (n+1))) h
  rw [gVec, lV_ofLp_last, pole_ofLp_last] at h'
  exact one_ne_zero h'.symm

lemma gVec_ne_negPole {n : ℕ} (y : Sph n) :
    gVec y ≠ (-pole (n+1) : EuclideanSpace ℝ (Fin (n+2))) := by
  intro h
  have h' := congrArg (fun z => z.ofLp (Fin.last (n+1))) h
  rw [gVec, lV_ofLp_last, negPole_ofLp_last] at h'
  exact (by norm_num : (0:ℝ) ≠ -1) h'

lemma gVec_mem_sphere {n : ℕ} (y : Sph n) :
    gVec y ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+2))) 1 := by
  rw [Metric.mem_sphere, dist_eq_norm, sub_zero, gVec, norm_lV]
  exact norm_sph y

noncomputable def gFun {n : ℕ} (y : Sph n) : DP n :=
  ⟨⟨gVec y, gVec_mem_sphere y⟩,
    ⟨subtype_ne_polePt_of (gVec_mem_sphere y) (gVec_ne_pole y),
     subtype_ne_negPolePt_of (gVec_mem_sphere y) (gVec_ne_negPole y)⟩⟩

lemma continuous_gFun {n : ℕ} : Continuous (gFun (n := n)) := by
  have hc : Continuous (fun y : Sph n => lV (y.1 : EuclideanSpace ℝ (Fin (n+1)))) :=
    continuous_lV.comp continuous_subtype_val
  exact Continuous.subtype_mk
    (Continuous.subtype_mk hc (fun y => gVec_mem_sphere y))
    (fun y => ⟨subtype_ne_polePt_of (gVec_mem_sphere y) (gVec_ne_pole y),
               subtype_ne_negPolePt_of (gVec_mem_sphere y) (gVec_ne_negPole y)⟩)

noncomputable def g {n : ℕ} : C(Sph n, DP n) := ⟨gFun, continuous_gFun⟩

/-! ### The retracting homotopy -/

/-- `v` with its last coordinate scaled by `t`; the straight line from `v` to the equator. -/
noncomputable def projV {n : ℕ} (t : ℝ) (v : EuclideanSpace ℝ (Fin (n+2))) :
    EuclideanSpace ℝ (Fin (n+2)) :=
  v - (t * v.ofLp (Fin.last (n+1))) • pole (n+1)

@[simp] lemma projV_zero {n : ℕ} (v : EuclideanSpace ℝ (Fin (n+2))) : projV 0 v = v := by
  rw [projV]; simp

lemma projV_one {n : ℕ} (v : EuclideanSpace ℝ (Fin (n+2))) : projV 1 v = lV (dV v) := by
  rw [projV, one_mul]; exact (decomp v).symm

lemma dV_projV {n : ℕ} (t : ℝ) (v : EuclideanSpace ℝ (Fin (n+2))) : dV (projV t v) = dV v :=
  dV_sub_smul_pole v _

lemma projV_ne_zero_of_dV_ne_zero {n : ℕ} {v : EuclideanSpace ℝ (Fin (n+2))} (hv : dV v ≠ 0)
    (t : ℝ) : projV t v ≠ 0 := by
  intro h
  exact hv (by rw [← dV_projV t v, h, dV_zero])

lemma projV_not_smul_pole {n : ℕ} {v : EuclideanSpace ℝ (Fin (n+2))} (hv : dV v ≠ 0)
    (t c : ℝ) : projV t v ≠ c • pole (n+1) := by
  intro h
  have h1 : dV (projV t v) = dV v := dV_projV t v
  rw [h, dV_smul, dV_pole, smul_zero] at h1
  exact hv h1.symm

lemma projV_uvec_ne_pole {n : ℕ} {v : EuclideanSpace ℝ (Fin (n+2))} (hv : dV v ≠ 0) (t : ℝ) :
    uvec (projV t v) ≠ pole (n+1) := by
  intro h
  have hw0 : projV t v ≠ 0 := projV_ne_zero_of_dV_ne_zero hv t
  have hw : projV t v = ‖projV t v‖ • pole (n+1) := by
    have h2 := congrArg (fun z => ‖projV t v‖ • z) h
    rw [uvec, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hw0), one_smul] at h2
    exact h2
  exact projV_not_smul_pole hv t ‖projV t v‖ hw

lemma projV_uvec_ne_negPole {n : ℕ} {v : EuclideanSpace ℝ (Fin (n+2))} (hv : dV v ≠ 0)
    (t : ℝ) : uvec (projV t v) ≠ -pole (n+1) := by
  intro h
  have hw0 : projV t v ≠ 0 := projV_ne_zero_of_dV_ne_zero hv t
  have hw : projV t v = (-‖projV t v‖) • pole (n+1) := by
    have h2 := congrArg (fun z => ‖projV t v‖ • z) h
    rw [uvec, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hw0), one_smul, smul_neg,
      ← neg_smul] at h2
    exact h2
  exact projV_not_smul_pole hv t (-‖projV t v‖) hw

lemma uvecProjV_mem {n : ℕ} (p : unitInterval × DP n) :
    uvec (projV (p.1 : ℝ) (vOf p.2)) ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+2))) 1 :=
  mem_sphere_of_norm_eq_one
    (norm_uvec (projV_ne_zero_of_dV_ne_zero (dV_ne_zero_vOf p.2) (p.1 : ℝ)))

noncomputable def hFun {n : ℕ} (p : unitInterval × DP n) : DP n :=
  ⟨⟨uvec (projV (p.1 : ℝ) (vOf p.2)), uvecProjV_mem p⟩,
    ⟨subtype_ne_polePt_of (uvecProjV_mem p)
        (projV_uvec_ne_pole (dV_ne_zero_vOf p.2) (p.1 : ℝ)),
     subtype_ne_negPolePt_of (uvecProjV_mem p)
        (projV_uvec_ne_negPole (dV_ne_zero_vOf p.2) (p.1 : ℝ))⟩⟩

lemma continuous_hFun {n : ℕ} : Continuous (hFun (n := n)) := by
  have ht : Continuous (fun p : unitInterval × DP n => (p.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hv : Continuous (fun p : unitInterval × DP n => vOf p.2) := continuous_vOf.comp continuous_snd
  have hlast : Continuous (fun p : unitInterval × DP n => (vOf p.2).ofLp (Fin.last (n+1))) :=
    ((continuous_apply (Fin.last (n+1))).comp
      (PiLp.continuous_ofLp 2 (fun _ : Fin (n+2) => ℝ))).comp hv
  have hproj : Continuous (fun p : unitInterval × DP n => projV (p.1 : ℝ) (vOf p.2)) := by
    rw [show (fun p : unitInterval × DP n => projV (p.1 : ℝ) (vOf p.2))
        = fun p => vOf p.2 - ((p.1 : ℝ) * (vOf p.2).ofLp (Fin.last (n+1))) • pole (n+1)
        from rfl]
    exact hv.sub ((ht.mul hlast).smul continuous_const)
  have huvec : Continuous (fun p : unitInterval × DP n => uvec (projV (p.1 : ℝ) (vOf p.2))) := by
    rw [show (fun p : unitInterval × DP n => uvec (projV (p.1 : ℝ) (vOf p.2)))
        = fun p => (‖projV (p.1 : ℝ) (vOf p.2)‖)⁻¹ • projV (p.1 : ℝ) (vOf p.2) from rfl]
    exact ((continuous_norm.comp hproj).inv₀ (fun p =>
      norm_ne_zero_iff.mpr (projV_ne_zero_of_dV_ne_zero (dV_ne_zero_vOf p.2) (p.1 : ℝ)))).smul hproj
  exact Continuous.subtype_mk
    (Continuous.subtype_mk huvec (fun p => uvecProjV_mem p))
    (fun p => ⟨subtype_ne_polePt_of (uvecProjV_mem p)
                 (projV_uvec_ne_pole (dV_ne_zero_vOf p.2) (p.1 : ℝ)),
               subtype_ne_negPolePt_of (uvecProjV_mem p)
                 (projV_uvec_ne_negPole (dV_ne_zero_vOf p.2) (p.1 : ℝ))⟩)

noncomputable def homotopyMap {n : ℕ} : C(unitInterval × DP n, DP n) :=
  ⟨hFun, continuous_hFun⟩

lemma homotopyMap_zero {n : ℕ} (x : DP n) : homotopyMap (0, x) = x := by
  apply Subtype.ext
  apply Subtype.ext
  show uvec (projV ((0 : unitInterval) : ℝ) (vOf x)) = vOf x
  rw [show ((0 : unitInterval) : ℝ) = 0 from rfl, projV_zero, uvec_of_norm_one (norm_vOf x)]

lemma homotopyMap_one {n : ℕ} (x : DP n) : homotopyMap (1, x) = g (f x) := by
  apply Subtype.ext
  apply Subtype.ext
  show uvec (projV ((1 : unitInterval) : ℝ) (vOf x)) = lV (uvec (dV (vOf x)))
  rw [show ((1 : unitInterval) : ℝ) = 1 from rfl, projV_one, uvec_lV]

noncomputable def hom {n : ℕ} : (ContinuousMap.id (DP n)).Homotopy (g.comp f) :=
  ContinuousMap.Homotopy.mk homotopyMap (fun x => homotopyMap_zero x) (fun x => homotopyMap_one x)

lemma fFun_gFun {n : ℕ} (y : Sph n) : fFun (gFun y) = y := by
  apply Subtype.ext
  show uvec (dV (vOf (gFun y))) = (y.1 : EuclideanSpace ℝ (Fin (n+1)))
  have h : vOf (gFun y) = lV (y.1 : EuclideanSpace ℝ (Fin (n+1))) := rfl
  rw [h, dV_lV, uvec_of_norm_one (norm_sph y)]

lemma f_comp_g {n : ℕ} : (f (n := n)).comp (g (n := n)) = ContinuousMap.id (Sph n) := by
  apply ContinuousMap.ext
  intro y
  change fFun (gFun y) = y
  exact fFun_gFun y

/-! ### The homotopy equivalence -/

noncomputable def heq {n : ℕ} : ContinuousMap.HomotopyEquiv (DP n) (Sph n) where
  toFun := f
  invFun := g
  left_inv := ⟨hom.symm⟩
  right_inv := by
    rw [f_comp_g]

end Work.Sphere

end

namespace Work.Sphere

open Submission.Sphere (Sph pole polePt negPolePt)

/-- **The doubly punctured sphere is homotopy equivalent to `Sⁿ`.**  Deleting the two antipodal
points `±e` (`e = pole (n+1)`, the last standard basis vector of `ℝ^{n+2}`) from `S^{n+1}` leaves a
space homotopy equivalent to `Sⁿ`: the normalised homotopy
`(t,x) ↦ ‖x - t (x·e) e‖⁻¹ • (x - t (x·e) e)` retracts `S^{n+1} \ {±e}` onto its equator
`{y : y·e = 0}`, which is isometric to `Sⁿ` by dropping the last coordinate
(`x ↦ x ∘ Fin.castSucc`, inverse `y ↦ Fin.snoc y 0`).  The normalisation is legitimate because
`x - t (x·e) e = 0` forces `x` to be a real multiple of `e`, hence `x = ±e`, which is excluded. -/
theorem sphere_doublePunctured_homotopyEquiv (n : ℕ) :
    Nonempty (ContinuousMap.HomotopyEquiv
      {x : Submission.Sphere.Sph (n+1) // x ≠ Submission.Sphere.polePt (n+1) ∧
        x ≠ Submission.Sphere.negPolePt (n+1)}
      (Submission.Sphere.Sph n)) :=
  ⟨heq⟩

end Work.Sphere
