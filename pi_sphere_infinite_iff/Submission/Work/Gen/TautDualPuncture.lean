import Mathlib
import Submission.Work.Gen.Basic
import Submission.Work.Gen.PuncturedComplexThree
import Submission.Work.Thom.realification_homeo

set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

/-!
# The punctured total space of the tautological dual line bundle on `ℂPⁿ`

`Work.Gen.tautDual n` is the dual `O(1)` of the tautological line bundle on `ℂPⁿ`, as gluing data
with transition functions `coordChange i j x = homCoord n j i x` (`= z_i/z_j`).

This module proves that the complement of its zero section is the punctured model space
`ℂ^{n+1} ∖ {0}`:
`tautDualPunctHomeo n : ↥(zeroComplementCore (tautDual n)) ≃ₜ {z : CPV n // z ≠ 0}`.

The homeomorphism is `(x,c) ↦ c⁻¹ • u_i(x)` where `c` is the fibre coordinate of the point in the
chart `i = indexAt x` and `u_i(x) = Fin.insertNth i 1 (chartFun i x)` is the spanning vector of the
line `x` normalised to have `i`-th coordinate `1`.  The cocycle identity `homCoord_mul` makes this
independent of the chart, which is what makes the map well defined and continuous.
-/

namespace Work.Gen

open Work.Projective Work.Thom Filter
open scoped Topology

noncomputable section

/-! ## The one-dimensional fibre `F = ℂ`

The fibre of `tautDual n` is `EuclideanSpace ℂ (Fin 1)`, i.e. `ℂ` in the single coordinate.  We use
the linear equivalence `EuclideanSpace.equiv (Fin 1) ℂ` to pass between the fibre and the scalar
field. -/

/-- The coordinate of an element of the one-dimensional fibre. -/
def scF (c : EuclideanSpace ℂ (Fin 1)) : ℂ := (EuclideanSpace.equiv (Fin 1) ℂ c) 0

/-- The element of the one-dimensional fibre with a given coordinate. -/
def mkF (z : ℂ) : EuclideanSpace ℂ (Fin 1) :=
  (EuclideanSpace.equiv (Fin 1) ℂ).symm (fun _ => z)

@[simp] theorem scF_mkF (z : ℂ) : scF (mkF z) = z := by
  simp [scF, mkF]

@[simp] theorem mkF_scF (c : EuclideanSpace ℂ (Fin 1)) : mkF (scF c) = c := by
  apply (EuclideanSpace.equiv (Fin 1) ℂ).injective
  simp only [mkF, scF, ContinuousLinearEquiv.apply_symm_apply]
  funext i
  fin_cases i
  rfl

theorem scF_smul (z : ℂ) (c : EuclideanSpace ℂ (Fin 1)) : scF (z • c) = z * scF c := by
  simp [scF, map_smul]

theorem mkF_mul (z w : ℂ) : mkF (z * w) = z • mkF w := by
  have h : (fun _ : Fin 1 => z * w) = z • (fun _ : Fin 1 => w) := by
    funext i; simp [Pi.smul_apply]
  simp only [mkF]
  rw [h, map_smul]

theorem mkF_ne_zero {z : ℂ} (hz : z ≠ 0) : mkF z ≠ 0 := by
  intro h
  have h2 := congrArg scF h
  rw [scF_mkF] at h2
  simp only [scF, map_zero, Pi.zero_apply] at h2
  exact hz h2

theorem continuous_mkF : Continuous mkF :=
  (EuclideanSpace.equiv (Fin 1) ℂ).symm.continuous.comp (continuous_pi fun _ => continuous_id)

theorem continuous_scF : Continuous scF :=
  continuous_apply 0 |>.comp (EuclideanSpace.equiv (Fin 1) ℂ).continuous

/-- `scF c = 0` iff `c = 0`. -/
theorem scF_eq_zero_iff (c : EuclideanSpace ℂ (Fin 1)) : scF c = 0 ↔ c = 0 := by
  constructor
  · intro h
    rw [← mkF_scF c, h]
    simp only [mkF]
    ext i
    simp
  · intro h
    rw [h]
    simp [scF]

/-! ## The normalised spanning vector of a line in `ℂPⁿ` -/

/-- **The spanning vector of the line `x ∈ ℂPⁿ` in the chart `i`**, normalised so that its `i`-th
coordinate is `1`: the vector `(z_0/z_i, …, 1, …, z_n/z_i)`. -/
def uVec {n : ℕ} (i : Fin (n + 1)) (x : CP n) : CPV n :=
  Fin.insertNth (α := fun _ => ℂ) i (1 : ℂ) (chartFun i x)

theorem uVec_apply_self {n : ℕ} (i : Fin (n + 1)) (x : CP n) : uVec i x i = 1 :=
  Fin.insertNth_apply_same (α := fun _ => ℂ) i 1 (chartFun i x)

theorem uVec_ne_zero {n : ℕ} (i : Fin (n + 1)) (x : CP n) : uVec i x ≠ 0 := by
  intro h
  have := congrFun h i
  rw [uVec_apply_self, Pi.zero_apply] at this
  exact one_ne_zero this

/-- The `j`-th coordinate of the normalised spanning vector is the homogeneous ratio
`z_j/z_i = homCoord n i j x`. -/
theorem uVec_apply {n : ℕ} (i j : Fin (n + 1)) (x : CP n) :
    uVec i x j = homCoord n i j x := by
  by_cases h : j = i
  · subst h
    rw [uVec_apply_self, homCoord_self]
  · rw [uVec, insertNth_apply_of_ne i j h, homCoord_of_ne h]

/-- **The spanning vector normalised in the chart `i` represents the line `x`.** -/
theorem cpMk_uVec {n : ℕ} (i : Fin (n + 1)) (x : CP n) (hx : x ∈ chartSet i) :
    cpMk n ⟨uVec i x, uVec_ne_zero i x⟩ = x := by
  have h1 : chartInv i (chartFun i x) = x := chartInv_chartFun i x hx
  have h2 : cpMk n ⟨Fin.insertNth (α := fun _ => ℂ) i (1 : ℂ) (chartFun i x),
      insertNth_one_ne_zero i (chartFun i x)⟩ = x := by
    conv_rhs => rw [← h1]
    rw [chartInv_apply]
  simpa [uVec] using h2

/-- **The homogeneous ratio `z_j/z_i` is nonzero on the overlap of the charts `i` and `j`.** -/
theorem homCoord_ne_zero_of_mem {n : ℕ} {i j : Fin (n + 1)} {x : CP n}
    (hi : x ∈ chartSet i) (hj : x ∈ chartSet j) : homCoord n i j x ≠ 0 := by
  obtain ⟨w, rfl⟩ := hi
  have hwj : (Fin.insertNth (α := fun _ => ℂ) i (1 : ℂ) w) j ≠ 0 :=
    (mem_chartSet_iff j ⟨_, insertNth_one_ne_zero i w⟩).mp (by rwa [chartInv_apply] at hj)
  by_cases hji : j = i
  · subst hji; simp
  · rw [homCoord_of_ne hji, chartInv_apply, chartFun_cpMk, chartFunAux,
      succAbove_removeAbove]
    simpa using hwj

/-- **A nonzero vector is a scalar multiple of the normalised spanning vector of its line.** -/
theorem eq_smul_uVec {n : ℕ} (i : Fin (n + 1)) (w : CPV n) (hw : w ≠ 0) (hwi : w i ≠ 0) :
    w = (w i) • uVec i (cpMk n ⟨w, hw⟩) := by
  have h1 : uVec i (cpMk n ⟨w, hw⟩) = (w i)⁻¹ • w := by
    rw [uVec, chartFun_cpMk]
    exact insertNth_chartFunAux i ⟨w, hw⟩ hwi
  rw [h1, smul_smul, mul_inv_cancel₀ hwi, one_smul]

/-- **Chart independence of the normalised spanning vector**: on the overlap of the charts `i` and
`j` the two normalisations differ by the homogeneous ratio. -/
theorem uVec_indep {n : ℕ} (i j : Fin (n + 1)) {x : CP n}
    (hx : x ∈ chartSet i ∩ chartSet j) :
    uVec j x = (homCoord n i j x)⁻¹ • uVec i x := by
  have hne := homCoord_ne_zero_of_mem hx.1 hx.2
  have hv : uVec i x ≠ 0 := uVec_ne_zero i x
  have hvj : uVec i x j ≠ 0 := by
    rw [uVec_apply]; exact hne
  have hcmp : cpMk n ⟨uVec i x, hv⟩ = x := cpMk_uVec i x hx.1
  have hstep : uVec i x = (uVec i x j) • uVec j x := by
    have h := eq_smul_uVec j (uVec i x) hv hvj
    rwa [hcmp] at h
  have hstep' : uVec i x = homCoord n i j x • uVec j x := by
    rw [hstep, uVec_apply]
  rw [hstep', smul_smul, inv_mul_cancel₀ hne, one_smul]

/-! ## The fibre coordinates of `tautDual n` -/

/-- The two coordinate orders of `homCoord` are mutually inverse on the overlap. -/
theorem homCoord_mul_comm {n : ℕ} {i j : Fin (n + 1)} {x : CP n}
    (hi : x ∈ chartSet i) (hj : x ∈ chartSet j) :
    homCoord n j i x * homCoord n i j x = 1 := by
  have h := homCoord_mul i j i hi hj hi
  rw [homCoord_self] at h
  exact h.symm

theorem homCoord_inv {n : ℕ} {i j : Fin (n + 1)} {x : CP n}
    (hi : x ∈ chartSet i) (hj : x ∈ chartSet j) :
    (homCoord n i j x)⁻¹ = homCoord n j i x :=
  (eq_inv_of_mul_eq_one_left (homCoord_mul_comm hi hj)).symm

variable {n : ℕ}

/-- **The change of the fibre coordinate of `tautDual n` between two charts.**  For a point of the
total space over `x` in the overlap of the charts `i` and `j`, the `j`-coordinate is the
`i`-coordinate multiplied by `homCoord n j i x = z_i/z_j`. -/
theorem tautDual_localTriv_snd {i j : Fin (n + 1)} {p : (tautDual n).TotalSpace}
    (hi : p.1 ∈ (tautDual n).baseSet i) (hj : p.1 ∈ (tautDual n).baseSet j) :
    ((tautDual n).localTriv j p).2
      = homCoord n j i p.1 • ((tautDual n).localTriv i p).2 := by
  have hx : p.1 ∈ (tautDual n).baseSet ((tautDual n).indexAt p.1) ∩ (tautDual n).baseSet i
      ∩ (tautDual n).baseSet j :=
    ⟨⟨(tautDual n).mem_baseSet_at p.1, hi⟩, hj⟩
  have h := (tautDual n).coordChange_comp ((tautDual n).indexAt p.1) i j p.1 hx p.2
  simp only [tautDual_coordChange, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply] at h
  rw [VectorBundleCore.localTriv_apply, VectorBundleCore.localTriv_apply]
  simp only [tautDual_coordChange, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply]
  exact h.symm

/-- The scalar version of the coordinate change. -/
theorem tautDual_scF_localTriv_snd {i j : Fin (n + 1)} {p : (tautDual n).TotalSpace}
    (hi : p.1 ∈ (tautDual n).baseSet i) (hj : p.1 ∈ (tautDual n).baseSet j) :
    scF (((tautDual n).localTriv j p).2)
      = homCoord n j i p.1 * scF (((tautDual n).localTriv i p).2) := by
  rw [tautDual_localTriv_snd hi hj, scF_smul]

/-! ## The homeomorphism onto the punctured model space -/

/-- **The map from the punctured total space of `tautDual n` to `ℂ^{n+1} ∖ {0}`**: in the chart
`i = indexAt x` of the base point `x`, a point with fibre coordinate `c` is sent to `c⁻¹ • u_i(x)`,
the reciprocal of the coordinate times the normalised spanning vector of the line. -/
def theta (n : ℕ) (p : ↥(zeroComplementCore (tautDual n))) : CPV n :=
  (scF (((tautDual n).localTriv ((tautDual n).indexAt p.1.1) p.1).2))⁻¹
    • uVec ((tautDual n).indexAt p.1.1) p.1.1

/-- The chart coordinate at the chosen index is nonzero. -/
theorem theta_coord_ne_zero {p : ↥(zeroComplementCore (tautDual n))} :
    scF (((tautDual n).localTriv ((tautDual n).indexAt p.1.1) p.1).2) ≠ 0 := by
  have hmem := (tautDual n).mem_baseSet_at p.1.1
  have h : ((tautDual n).localTriv ((tautDual n).indexAt p.1.1) p.1).2 = p.1.2 := by
    rw [VectorBundleCore.localTriv_apply]
    exact (tautDual n).coordChange_self ((tautDual n).indexAt p.1.1) p.1.1 hmem p.1.2
  rw [h]
  exact fun h0 => p.2 ((scF_eq_zero_iff p.1.2).mp h0)

theorem theta_ne_zero {p : ↥(zeroComplementCore (tautDual n))} : theta n p ≠ 0 := by
  rw [theta, smul_ne_zero_iff]
  exact ⟨inv_ne_zero (theta_coord_ne_zero), uVec_ne_zero _ _⟩

/-- **Chart independence of `theta`**: for any chart `i` containing the base point, `theta` is
`c_i⁻¹ • u_i`. -/
theorem theta_eq_chart (i : Fin (n + 1)) {p : ↥(zeroComplementCore (tautDual n))}
    (hi : p.1.1 ∈ (tautDual n).baseSet i) :
    theta n p = (scF (((tautDual n).localTriv i p.1).2))⁻¹ • uVec i p.1.1 := by
  have h0 : p.1.1 ∈ (tautDual n).baseSet ((tautDual n).indexAt p.1.1) :=
    (tautDual n).mem_baseSet_at p.1.1
  have hcoord := tautDual_scF_localTriv_snd (n := n) (i := (tautDual n).indexAt p.1.1)
    (j := i) h0 hi
  have hu := uVec_indep ((tautDual n).indexAt p.1.1) i (x := p.1.1) ⟨h0, hi⟩
  have hg : homCoord n i ((tautDual n).indexAt p.1.1) p.1.1
      = (homCoord n ((tautDual n).indexAt p.1.1) i p.1.1)⁻¹ :=
    eq_inv_of_mul_eq_one_right (homCoord_mul_comm hi h0)
  have hne : homCoord n ((tautDual n).indexAt p.1.1) i p.1.1 ≠ 0 :=
    homCoord_ne_zero_of_mem h0 hi
  rw [theta, hcoord, hu, hg]
  have hscalar : (scF (((tautDual n).localTriv ((tautDual n).indexAt p.1.1) p.1).2))⁻¹
      = ((homCoord n ((tautDual n).indexAt p.1.1) i p.1.1)⁻¹
          * scF (((tautDual n).localTriv ((tautDual n).indexAt p.1.1) p.1).2))⁻¹
        * (homCoord n ((tautDual n).indexAt p.1.1) i p.1.1)⁻¹ := by
    rw [mul_inv_rev, inv_inv]
    rw [mul_assoc, mul_inv_cancel₀ hne, mul_one]
  rw [hscalar, smul_smul]

/-! ## The inverse map and the homeomorphism -/

/-- `cpMk` is invariant under nonzero scalar multiplication. -/
theorem cpMk_smul {v : CPV n} (hv : v ≠ 0) (c : ℂ) (hc : c ≠ 0) :
    cpMk n ⟨c • v, smul_ne_zero hc hv⟩ = cpMk n ⟨v, hv⟩ :=
  (cpMk_eq_iff n _ _).mpr ⟨c, rfl⟩

/-- The homogeneous ratio read at `cpMk w` is the ratio of the coordinates of `w`. -/
theorem homCoord_cpMk {i j : Fin (n + 1)} (w : {w : CPV n // w ≠ 0}) (hwi : w.1 i ≠ 0) :
    homCoord n i j (cpMk n w) = w.1 j / w.1 i := by
  by_cases h : j = i
  · subst h; rw [homCoord_self, div_self hwi]
  · rw [homCoord_of_ne h, chartFun_cpMk, chartFunAux, succAbove_removeAbove]

/-- Two points of the total space over the same base point are equal as soon as their coordinates
in one common chart agree. -/
theorem TotalSpace.ext {i : Fin (n + 1)} {q q' : (tautDual n).TotalSpace}
    (hbase : q.1 = q'.1) (hq : q.1 ∈ (tautDual n).baseSet i)
    (hcoord : ((tautDual n).localTriv i q).2 = ((tautDual n).localTriv i q').2) : q = q' := by
  have hq' : q'.1 ∈ (tautDual n).baseSet i := hbase ▸ hq
  have hsrc : q ∈ ((tautDual n).localTriv i).source :=
    (VectorBundleCore.mem_localTriv_source _ _ _).mpr hq
  have hsrc' : q' ∈ ((tautDual n).localTriv i).source :=
    (VectorBundleCore.mem_localTriv_source _ _ _).mpr hq'
  have hf : ((tautDual n).localTriv i) q = ((tautDual n).localTriv i) q' := by
    refine Prod.ext ?_ ?_
    · rw [Bundle.Trivialization.coe_fst _ hsrc, Bundle.Trivialization.coe_fst _ hsrc', hbase]
    · exact hcoord
  exact ((tautDual n).localTriv i).toOpenPartialHomeomorph.injOn hsrc hsrc' hf

/-- **The inverse map**: a nonzero vector `w` is sent to the point of the total space over the line
`ℂw` whose fibre coordinate (in the chart `indexAt (cpMk w)`) is the reciprocal of the corresponding
coordinate of `w`. -/
def phi (n : ℕ) (w : {w : CPV n // w ≠ 0}) : ↥(zeroComplementCore (tautDual n)) :=
  ⟨⟨cpMk n w, mkF ((w.1 ((tautDual n).indexAt (cpMk n w)))⁻¹)⟩, by
    have hmem : cpMk n w ∈ (tautDual n).baseSet ((tautDual n).indexAt (cpMk n w)) :=
      (tautDual n).mem_baseSet_at (cpMk n w)
    have hne : w.1 ((tautDual n).indexAt (cpMk n w)) ≠ 0 :=
      (mem_chartSet_iff _ w).mp (by rwa [tautDual_baseSet] at hmem)
    exact mkF_ne_zero (inv_ne_zero hne)⟩

@[simp] theorem phi_base (n : ℕ) (w : {w : CPV n // w ≠ 0}) :
    (phi n w).1.1 = cpMk n w := rfl

/-- The `indexAt`-coordinate of `phi w` is the reciprocal of the corresponding coordinate of `w`. -/
theorem phi_localTriv (n : ℕ) (w : {w : CPV n // w ≠ 0}) :
    ((tautDual n).localTriv ((tautDual n).indexAt (cpMk n w)) (phi n w).1).2
      = mkF ((w.1 ((tautDual n).indexAt (cpMk n w)))⁻¹) := by
  have hmem := (tautDual n).mem_baseSet_at (cpMk n w)
  rw [VectorBundleCore.localTriv_apply]
  exact (tautDual n).coordChange_self _ _ hmem _

/-- **`phi` is a left inverse of `theta`.** -/
theorem theta_phi (n : ℕ) (w : {w : CPV n // w ≠ 0}) : theta n (phi n w) = w.1 := by
  set i0 : Fin (n + 1) := (tautDual n).indexAt (cpMk n w) with hi0
  have hmem : cpMk n w ∈ (tautDual n).baseSet i0 := (tautDual n).mem_baseSet_at (cpMk n w)
  have hne : w.1 i0 ≠ 0 :=
    (mem_chartSet_iff _ w).mp (by rwa [tautDual_baseSet] at hmem)
  have hchart : (phi n w).1.1 ∈ (tautDual n).baseSet i0 := hmem
  rw [theta_eq_chart i0 hchart, phi_localTriv, scF_mkF, inv_inv]
  exact (eq_smul_uVec i0 w.1 w.2 hne).symm

/-- **`phi` is a right inverse of `theta`.** -/
theorem phi_theta (n : ℕ) (p : ↥(zeroComplementCore (tautDual n))) :
    phi n ⟨theta n p, theta_ne_zero⟩ = p := by
  set i0 : Fin (n + 1) := (tautDual n).indexAt p.1.1 with hi0
  have hmem : p.1.1 ∈ (tautDual n).baseSet i0 := (tautDual n).mem_baseSet_at p.1.1
  have hc : (scF (((tautDual n).localTriv i0 p.1).2))⁻¹ ≠ 0 :=
    inv_ne_zero (theta_coord_ne_zero (p := p))
  have hcmp : cpMk n ⟨theta n p, theta_ne_zero⟩ = p.1.1 := by
    have h1 : cpMk n ⟨theta n p, theta_ne_zero⟩
        = cpMk n ⟨uVec i0 p.1.1, uVec_ne_zero i0 p.1.1⟩ :=
      (cpMk_eq_iff n _ _).mpr ⟨(scF (((tautDual n).localTriv i0 p.1).2))⁻¹,
        (theta_eq_chart i0 hmem).symm⟩
    exact h1.trans (cpMk_uVec i0 p.1.1 hmem)
  have hphi2 : ((tautDual n).localTriv i0 (phi n ⟨theta n p, theta_ne_zero⟩).1).2
      = mkF ((theta n p) i0)⁻¹ := by
    have hi : (tautDual n).indexAt (cpMk n ⟨theta n p, theta_ne_zero⟩) = i0 := by
      rw [hcmp]
    rw [← hi]
    exact phi_localTriv n ⟨theta n p, theta_ne_zero⟩
  have hkey : (theta n p) i0 = (scF (((tautDual n).localTriv i0 p.1).2))⁻¹ := by
    rw [theta_eq_chart i0 hmem]
    simp [uVec_apply_self]
  refine Subtype.ext (TotalSpace.ext (i := i0) ?_ ?_ ?_)
  · show (phi n ⟨theta n p, theta_ne_zero⟩).1.1 = p.1.1
    rw [phi_base, hcmp]
  · show (phi n ⟨theta n p, theta_ne_zero⟩).1.1 ∈ (tautDual n).baseSet i0
    rw [phi_base, hcmp]; exact hmem
  · rw [hphi2, hkey, inv_inv]
    exact mkF_scF _

/-! ## Continuity -/

/-- The `i`-coordinate of a point in the complement of the zero section is nonzero. -/
theorem scF_localTriv_snd_ne_zero {i : Fin (n + 1)} {p : (tautDual n).TotalSpace}
    (hi : p.1 ∈ (tautDual n).baseSet i) (hp : p.2 ≠ 0) :
    scF (((tautDual n).localTriv i p).2) ≠ 0 := by
  rw [VectorBundleCore.localTriv_apply, tautDual_coordChange,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, scF_smul]
  refine mul_ne_zero ?_ (fun h => hp ((scF_eq_zero_iff p.2).mp h))
  exact homCoord_ne_zero_of_mem (i := i) (j := (tautDual n).indexAt p.1)
    (by rw [← tautDual_baseSet]; exact hi)
    (by rw [← tautDual_baseSet]; exact (tautDual n).mem_baseSet_at p.1)

/-- **`theta` is continuous.** -/
theorem continuous_theta (n : ℕ) : Continuous (theta n) := by
  rw [continuous_iff_continuousAt]
  intro p
  set i0 : Fin (n + 1) := (tautDual n).indexAt p.1.1 with hi0
  have hmem : p.1.1 ∈ (tautDual n).baseSet i0 := (tautDual n).mem_baseSet_at p.1.1
  have hbase_cont : Continuous
      (fun q : ↥(zeroComplementCore (tautDual n)) => q.1.1) :=
    ((tautDual n).continuous_proj.comp continuous_subtype_val)
  have hWopen : IsOpen {q : ↥(zeroComplementCore (tautDual n)) | q.1.1 ∈ (tautDual n).baseSet i0} :=
    ((tautDual n).isOpen_baseSet i0).preimage hbase_cont
  have hWmem : p ∈ {q : ↥(zeroComplementCore (tautDual n)) | q.1.1 ∈ (tautDual n).baseSet i0} := hmem
  -- the explicit chart expression is continuous
  have htriv : ContinuousOn (fun q : ↥(zeroComplementCore (tautDual n)) =>
      ((tautDual n).localTriv i0 q.1).2)
      {q : ↥(zeroComplementCore (tautDual n)) | q.1.1 ∈ (tautDual n).baseSet i0} :=
    ((((tautDual n).localTriv i0).continuousOn).comp continuous_subtype_val.continuousOn
      (fun q hq => (VectorBundleCore.mem_localTriv_source _ _ _).mpr hq)).snd
  have hsc : ContinuousOn (fun q : ↥(zeroComplementCore (tautDual n)) =>
      scF (((tautDual n).localTriv i0 q.1).2))
      {q : ↥(zeroComplementCore (tautDual n)) | q.1.1 ∈ (tautDual n).baseSet i0} :=
    continuous_scF.comp_continuousOn htriv
  have hinv : ContinuousOn (fun q : ↥(zeroComplementCore (tautDual n)) =>
      (scF (((tautDual n).localTriv i0 q.1).2))⁻¹)
      {q : ↥(zeroComplementCore (tautDual n)) | q.1.1 ∈ (tautDual n).baseSet i0} :=
    hsc.inv₀ (fun q hq => scF_localTriv_snd_ne_zero hq q.2)
  have huvec : ContinuousOn (fun q : ↥(zeroComplementCore (tautDual n)) => uVec i0 q.1.1)
      {q : ↥(zeroComplementCore (tautDual n)) | q.1.1 ∈ (tautDual n).baseSet i0} :=
    ((continuous_insertNth_one i0).comp_continuousOn
      ((continuousOn_chartFun i0).comp hbase_cont.continuousOn (fun q hq => hq)) :
      ContinuousOn (fun q : ↥(zeroComplementCore (tautDual n)) =>
        Fin.insertNth (α := fun _ => ℂ) i0 (1 : ℂ) (chartFun i0 q.1.1)) _).congr
      (fun q _ => rfl)
  have hcontOn : ContinuousOn (fun q : ↥(zeroComplementCore (tautDual n)) =>
      (scF (((tautDual n).localTriv i0 q.1).2))⁻¹ • uVec i0 q.1.1)
      {q : ↥(zeroComplementCore (tautDual n)) | q.1.1 ∈ (tautDual n).baseSet i0} :=
    hinv.smul huvec
  have hev : theta n =ᶠ[𝓝 p] (fun q : ↥(zeroComplementCore (tautDual n)) =>
      (scF (((tautDual n).localTriv i0 q.1).2))⁻¹ • uVec i0 q.1.1) := by
    filter_upwards [hWopen.mem_nhds hWmem] with q hq
    exact theta_eq_chart i0 hq
  exact (hcontOn.continuousAt (hWopen.mem_nhds hWmem)).congr hev.symm

/-- The point of the total space of `tautDual n` whose coordinate in the chart `i` is `v`, over the
base point `b`. -/
def chartPt (n : ℕ) (i : Fin (n + 1)) (b : CP n) (v : EuclideanSpace ℂ (Fin 1)) :
    (tautDual n).TotalSpace :=
  ⟨b, ((tautDual n).localTriv i).symm b v⟩

theorem localTriv_chartPt (n : ℕ) (i : Fin (n + 1)) {b : CP n}
    (hb : b ∈ (tautDual n).baseSet i) (v : EuclideanSpace ℂ (Fin 1)) :
    ((tautDual n).localTriv i) (chartPt n i b v) = (b, v) := by
  rw [chartPt, VectorBundleCore.localTriv_apply, VectorBundleCore.localTriv_symm_apply _ i hb]
  congr 1
  have hx : b ∈ (tautDual n).baseSet i ∩ (tautDual n).baseSet ((tautDual n).indexAt b)
      ∩ (tautDual n).baseSet i :=
    ⟨⟨hb, (tautDual n).mem_baseSet_at b⟩, hb⟩
  have h := (tautDual n).coordChange_comp i ((tautDual n).indexAt b) i b hx v
  rw [show (tautDual n).coordChange i i b v = v from
    (tautDual n).coordChange_self i b hb v] at h
  exact h

theorem chartPt_mem_zeroComplementCore (n : ℕ) (i : Fin (n + 1)) {b : CP n}
    (hb : b ∈ (tautDual n).baseSet i) {v : EuclideanSpace ℂ (Fin 1)} (hv : v ≠ 0) :
    chartPt n i b v ∈ zeroComplementCore (tautDual n) := by
  show ((tautDual n).localTriv i).symm b v ≠ 0
  rw [VectorBundleCore.localTriv_symm_apply _ i hb, tautDual_coordChange,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
  exact smul_ne_zero
    (homCoord_ne_zero_of_mem (i := (tautDual n).indexAt b) (j := i)
      (by rw [← tautDual_baseSet]; exact (tautDual n).mem_baseSet_at b)
      (by rw [← tautDual_baseSet]; exact hb)) hv

/-- **Chart independence of `phi`**: reading the fibre coordinate in any chart containing the base
point gives the same point. -/
theorem phi_eq_symm (i : Fin (n + 1)) (w : {w : CPV n // w ≠ 0}) (hwi : w.1 i ≠ 0) :
    (phi n w).1 = chartPt n i (cpMk n w) (mkF ((w.1 i)⁻¹)) := by
  have hmem : cpMk n w ∈ (tautDual n).baseSet i := by
    rw [tautDual_baseSet]; exact (mem_chartSet_iff i w).mpr hwi
  refine TotalSpace.ext (i := i) ?_ hmem ?_
  · rw [phi_base]; rfl
  · rw [localTriv_chartPt n i hmem]
    set i0 : Fin (n + 1) := (tautDual n).indexAt (cpMk n w) with hi0
    have h1 : ((tautDual n).localTriv i (phi n w).1).2
        = (tautDual n).coordChange i0 i (cpMk n w) (mkF ((w.1 i0)⁻¹)) := by
      rw [VectorBundleCore.localTriv_apply]
      rfl
    rw [h1, tautDual_coordChange, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      ← mkF_mul]
    congr 1
    have h0 : w.1 i0 ≠ 0 := (mem_chartSet_iff i0 w).mp (by
      rw [← tautDual_baseSet]
      exact (tautDual n).mem_baseSet_at (cpMk n w))
    rw [homCoord_cpMk w hwi, div_eq_mul_inv, mul_assoc,
      mul_comm (w.1 i)⁻¹ (w.1 i0)⁻¹, ← mul_assoc, mul_inv_cancel₀ h0, one_mul]

/-- **`phi` is continuous.** -/
theorem continuous_phi (n : ℕ) : Continuous (phi n) := by
  rw [continuous_iff_continuousAt]
  intro w
  set i0 : Fin (n + 1) := (tautDual n).indexAt (cpMk n w) with hi0
  have hmem : cpMk n w ∈ (tautDual n).baseSet i0 := (tautDual n).mem_baseSet_at _
  have hwi0 : w.1 i0 ≠ 0 := (mem_chartSet_iff _ w).mp (by rwa [tautDual_baseSet] at hmem)
  set U : Set {v : CPV n // v ≠ 0} := {w | w.1 i0 ≠ 0} with hU
  have hUopen : IsOpen U :=
    isOpen_ne.preimage ((continuous_apply i0).comp continuous_subtype_val)
  have hmemset : ∀ w' : {v : CPV n // v ≠ 0}, w' ∈ U →
      cpMk n w' ∈ (tautDual n).baseSet i0 := fun w' hw' => by
    rw [tautDual_baseSet]; exact (mem_chartSet_iff i0 w').mpr hw'
  have hpair : ContinuousOn (fun w' : {v : CPV n // v ≠ 0} =>
      (cpMk n w', mkF ((w'.1 i0)⁻¹))) U :=
    ((continuous_cpMk n).continuousOn).prodMk
      (continuous_mkF.comp_continuousOn
        ((((continuous_apply i0).comp continuous_subtype_val).continuousOn).inv₀
          (fun w' hw' => hw')))
  have htot : ContinuousOn (fun w' : {v : CPV n // v ≠ 0} =>
      chartPt n i0 (cpMk n w') (mkF ((w'.1 i0)⁻¹))) U :=
    ((Bundle.Trivialization.continuousOn_symm ((tautDual n).localTriv i0)).comp hpair
      (fun w' hw' => ⟨hmemset w' hw', Set.mem_univ _⟩))
  have hmk : ∀ w' : {v : CPV n // v ≠ 0}, w' ∈ U →
      chartPt n i0 (cpMk n w') (mkF ((w'.1 i0)⁻¹)) ∈ zeroComplementCore (tautDual n) :=
    fun w' hw' => chartPt_mem_zeroComplementCore n i0 (hmemset w' hw')
      (mkF_ne_zero (inv_ne_zero hw'))
  have hcont_res : Continuous (fun w' : ↥U =>
      (⟨chartPt n i0 (cpMk n w'.1) (mkF (((w'.1 : CPV n) i0)⁻¹)),
        hmk w'.1 w'.2⟩ : ↥(zeroComplementCore (tautDual n)))) :=
    (htot.domRestrict).subtype_mk (fun w' => hmk w'.1 w'.2)
  have hcongr : U.domRestrict (fun w' => phi n w')
      = fun w' : ↥U => (⟨chartPt n i0 (cpMk n w'.1) (mkF (((w'.1 : CPV n) i0)⁻¹)),
        hmk w'.1 w'.2⟩ : ↥(zeroComplementCore (tautDual n))) := by
    funext w'
    exact Subtype.ext (phi_eq_symm i0 w'.1 w'.2)
  have hcontOn : ContinuousOn (fun w' => phi n w') U := by
    rw [continuousOn_iff_continuous_domRestrict, hcongr]
    exact hcont_res
  exact hcontOn.continuousAt (hUopen.mem_nhds hwi0)

/-- `theta`, with the nonzero-vector subtype as codomain. -/
def thetaSub (n : ℕ) (p : ↥(zeroComplementCore (tautDual n))) : {w : CPV n // w ≠ 0} :=
  ⟨theta n p, theta_ne_zero⟩

theorem continuous_thetaSub (n : ℕ) : Continuous (thetaSub n) :=
  (continuous_theta n).subtype_mk (fun p => theta_ne_zero)

theorem thetaSub_phi (n : ℕ) (w : {w : CPV n // w ≠ 0}) (hw : w.1 ≠ 0 := w.2) :
    thetaSub n (phi n w) = w :=
  Subtype.ext (theta_phi n w)

theorem phi_thetaSub (n : ℕ) (p : ↥(zeroComplementCore (tautDual n))) :
    phi n (thetaSub n p) = p :=
  phi_theta n p

/-- **The complement of the zero section of the tautological dual line bundle on `ℂPⁿ` is the
punctured model space `ℂ^{n+1} ∖ {0}`.** -/
theorem tautDualPunctHomeo (n : ℕ) :
    Nonempty (↥(zeroComplementCore (tautDual n)) ≃ₜ {w : CPV n // w ≠ 0}) :=
  ⟨{ toFun := thetaSub n
     invFun := phi n
     left_inv := phi_thetaSub n
     right_inv := thetaSub_phi n
     continuous_toFun := continuous_thetaSub n
     continuous_invFun := continuous_phi n }⟩

/-- **`H²` of the complement of the zero section of `realification (tautDual 2)` vanishes.** -/
theorem subsingleton_zeroComplement_tautDualTwo :
    Subsingleton (Work.Thom.Coh ℤ 2
      (Work.Thom.zeroComplement (Work.Thom.realification (Work.Gen.tautDual 2)))) := by
  obtain ⟨e1⟩ := tautDualPunctHomeo 2
  have e2 : ↥(Work.Thom.zeroComplement (Work.Thom.realification (Work.Gen.tautDual 2)))
      ≃ₜ {w : EuclideanSpace ℂ (Fin 3) // w ≠ 0} :=
    (Work.Thom.zeroComplementHomeomorph (Work.Gen.tautDual 2)).trans
      (e1.trans (Work.Gen.puncturedComplexEuclideanHomeo).symm)
  obtain ⟨iso⟩ := Work.Cohomology.cohomologyIso_of_homotopyEquiv e2.toHomotopyEquiv 2
  haveI : Subsingleton (Work.Thom.Coh ℤ 2 {w : EuclideanSpace ℂ (Fin 3) // w ≠ 0}) :=
    PuncturedComplexThree
  haveI : Subsingleton (Work.Thom.Coh ℤ 2 {w : EuclideanSpace ℂ (Fin 3) // w ≠ 0}) :=
    PuncturedComplexThree
  exact ⟨fun a b => (ModuleCat.mono_iff_injective iso.hom).mp inferInstance
    (Subsingleton.elim (iso.hom a) (iso.hom b))⟩

end

end Work.Gen
