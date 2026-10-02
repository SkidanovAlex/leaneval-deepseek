import Mathlib
import Submission.Work.Thom.ModelGeometry
import Submission.Work.Thom.Cohomology
import Submission.Work.Thom.subsingleton_relComplex_euclidean_punctured

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.Thom

open ContinuousMap

noncomputable section

/-!
# The inclusion of the sphere bundle into the complement of the zero section

For the trivial bundle `B × ℝⁿ` we prove that the inclusion of the sphere part `B × S^{n-1}` into
the punctured part `{p : B × ℝⁿ | p.2 ≠ 0}` is a homotopy equivalence of the underlying spaces,
with the radial normalization as homotopy inverse.  This is the geometric input of
`Work.Thom.bijective_relCohMap_spherePunctured`.
-/

/-- The punctured Euclidean space `ℝⁿ ∖ {0}`, as a subspace. -/
abbrev punctEucl (n : ℕ) : Type := {v : EuclideanSpace ℝ (Fin n) // v ≠ 0}

/-- The sphere part of the pair `(B × ℝⁿ, B × S^{n-1})`, split off as `B × S^{n-1}`. -/
def sphPairHomeo (B : Type) [TopologicalSpace B] (n : ℕ) :
    ↥{p : B × EuclideanSpace ℝ (Fin n) | p.2 ∈ mSph n} ≃ₜ B × MSph n where
  toFun p := (p.1.1, ⟨p.1.2, p.2⟩)
  invFun q := ⟨(q.1, q.2.1), q.2.2⟩
  left_inv p := rfl
  right_inv q := rfl
  continuous_toFun := (continuous_fst.comp continuous_subtype_val).prodMk
    (Continuous.subtype_mk (continuous_snd.comp continuous_subtype_val) _)
  continuous_invFun := Continuous.subtype_mk
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)) _

/-- The punctured part of the pair `(B × ℝⁿ, B × (ℝⁿ∖0))`, split off as `B × (ℝⁿ∖0)`. -/
def punctPairHomeo (B : Type) [TopologicalSpace B] (n : ℕ) :
    ↥{p : B × EuclideanSpace ℝ (Fin n) | p.2 ≠ 0} ≃ₜ B × punctEucl n where
  toFun p := (p.1.1, ⟨p.1.2, p.2⟩)
  invFun q := ⟨(q.1, q.2.1), q.2.2⟩
  left_inv p := rfl
  right_inv q := rfl
  continuous_toFun := (continuous_fst.comp continuous_subtype_val).prodMk
    (Continuous.subtype_mk (continuous_snd.comp continuous_subtype_val) _)
  continuous_invFun := Continuous.subtype_mk
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)) _

/-! ## The inclusion `S^{n-1} ↪ ℝⁿ ∖ 0` is a homotopy equivalence -/

/-- The inclusion of the unit sphere `S^{n-1}` into the punctured space `ℝⁿ ∖ 0`. -/
def sphIncl (n : ℕ) : C(MSph n, punctEucl n) :=
  ⟨fun q => ⟨q.1, fun h0 => by
      have h : ‖q.1‖ = 1 := q.2
      rw [h0, norm_zero] at h
      exact zero_ne_one h⟩,
    Continuous.subtype_mk continuous_subtype_val _⟩

/-- Radial normalization from the punctured space onto the unit sphere. -/
def sphNormalize (n : ℕ) : C(punctEucl n, MSph n) :=
  ⟨fun v => ⟨(‖(v : EuclideanSpace ℝ (Fin n))‖)⁻¹ • (v : EuclideanSpace ℝ (Fin n)), by
      have hv : (0 : ℝ) < ‖(v : EuclideanSpace ℝ (Fin n))‖ := norm_pos_iff.mpr v.2
      show ‖(‖(v : EuclideanSpace ℝ (Fin n))‖)⁻¹ • (v : EuclideanSpace ℝ (Fin n))‖ = 1
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
        inv_mul_cancel₀ (ne_of_gt hv)]⟩,
    Continuous.subtype_mk
      (((continuous_subtype_val.norm : Continuous fun v : punctEucl n =>
          ‖(v : EuclideanSpace ℝ (Fin n))‖).inv₀
          (fun v => norm_ne_zero_iff.mpr v.2)).smul continuous_subtype_val) _⟩

theorem sphNormalize_comp_sphIncl (n : ℕ) :
    (sphNormalize n).comp (sphIncl n) = ContinuousMap.id (MSph n) := by
  apply ContinuousMap.ext
  intro q
  apply Subtype.ext
  change (‖(q : EuclideanSpace ℝ (Fin n))‖)⁻¹ • (q : EuclideanSpace ℝ (Fin n)) =
    (q : EuclideanSpace ℝ (Fin n))
  have h : ‖(q : EuclideanSpace ℝ (Fin n))‖ = 1 := q.2
  rw [h, inv_one, one_smul]

/-- The scaling coefficient of the straight-line homotopy from the radial normalization to the
identity of the punctured space. -/
def sphCoeff (n : ℕ) (x : unitInterval × punctEucl n) : ℝ :=
  (1 - (x.1 : ℝ)) * (‖(x.2 : EuclideanSpace ℝ (Fin n))‖)⁻¹ + (x.1 : ℝ)

theorem sphCoeff_pos (n : ℕ) (x : unitInterval × punctEucl n) : 0 < sphCoeff n x := by
  have ht0 : (0 : ℝ) ≤ (x.1 : ℝ) := x.1.2.1
  have ht1 : (x.1 : ℝ) ≤ 1 := x.1.2.2
  have ha : (0 : ℝ) < (‖(x.2 : EuclideanSpace ℝ (Fin n))‖)⁻¹ :=
    inv_pos.mpr (norm_pos_iff.mpr x.2.2)
  rw [sphCoeff]
  rcases eq_or_lt_of_le ht1 with h | h
  · rw [h, sub_self, zero_mul, zero_add]; norm_num
  · have h1 : 0 < 1 - (x.1 : ℝ) := by linarith
    have h2 : 0 < (1 - (x.1 : ℝ)) * (‖(x.2 : EuclideanSpace ℝ (Fin n))‖)⁻¹ := mul_pos h1 ha
    linarith

theorem continuous_sphCoeff (n : ℕ) : Continuous (sphCoeff n) := by
  have ht : Continuous fun x : unitInterval × punctEucl n => (x.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  have hv : Continuous fun x : unitInterval × punctEucl n => (x.2 : EuclideanSpace ℝ (Fin n)) :=
    continuous_subtype_val.comp continuous_snd
  have hn : Continuous fun x : unitInterval × punctEucl n =>
      (‖(x.2 : EuclideanSpace ℝ (Fin n))‖)⁻¹ :=
    hv.norm.inv₀ (fun x => norm_ne_zero_iff.mpr x.2.2)
  change Continuous fun x : unitInterval × punctEucl n =>
      (1 - (x.1 : ℝ)) * (‖(x.2 : EuclideanSpace ℝ (Fin n))‖)⁻¹ + (x.1 : ℝ)
  exact ((continuous_const.sub ht).mul hn).add ht

/-- The straight-line homotopy from the radial normalization composed with the inclusion to the
identity of the punctured space, as a map. -/
def sphHomotopyMap (n : ℕ) : C(unitInterval × punctEucl n, punctEucl n) :=
  ⟨fun x => ⟨sphCoeff n x • (x.2 : EuclideanSpace ℝ (Fin n)),
      smul_ne_zero (ne_of_gt (sphCoeff_pos n x)) x.2.2⟩,
    Continuous.subtype_mk ((continuous_sphCoeff n).smul
      (continuous_subtype_val.comp continuous_snd)) _⟩

theorem sphHomotopyMap_zero (n : ℕ) (v : punctEucl n) :
    sphHomotopyMap n (0, v) = (sphIncl n).comp (sphNormalize n) v := by
  apply Subtype.ext
  simp only [sphHomotopyMap, sphIncl, sphNormalize, sphCoeff, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk, Subtype.coe_mk]
  rw [show ((0 : unitInterval) : ℝ) = 0 from rfl]
  simp

theorem sphHomotopyMap_one (n : ℕ) (v : punctEucl n) :
    sphHomotopyMap n (1, v) = v := by
  apply Subtype.ext
  simp only [sphHomotopyMap, sphCoeff, ContinuousMap.coe_mk, Subtype.coe_mk]
  rw [show ((1 : unitInterval) : ℝ) = 1 from rfl]
  simp

/-- **The unit sphere `S^{n-1}` is a homotopy equivalence of `ℝⁿ ∖ 0`**, realized by the
inclusion with the radial normalization as homotopy inverse. -/
def sphPunctEquiv (n : ℕ) : ContinuousMap.HomotopyEquiv (MSph n) (punctEucl n) where
  toFun := sphIncl n
  invFun := sphNormalize n
  left_inv := by
    rw [sphNormalize_comp_sphIncl n]
  right_inv := ⟨ContinuousMap.Homotopy.mk (sphHomotopyMap n)
    (sphHomotopyMap_zero n) (sphHomotopyMap_one n)⟩

/-- **The inclusion of the sphere part into the punctured part induces an isomorphism on relative
cohomology.**  For the trivial bundle `B × ℝⁿ` over any base `B`, the map of pairs
`(B × ℝⁿ, B × S^{n-1}) → (B × ℝⁿ, B × (ℝⁿ∖0))` given by the identity on the total space is a
homotopy equivalence of pairs: the identity is a homotopy equivalence of the total spaces and the
inclusion `S^{n-1} ↪ ℝⁿ∖0` (equivalently `B × S^{n-1} ↪ B × (ℝⁿ∖0)`) is a homotopy equivalence of
the subspaces (`sphPunctEquiv`).  Hence the induced map on relative cohomology is a bijection. -/
theorem bijective_relCohMap_spherePunctured (B : Type) [TopologicalSpace B] (n m : ℕ) :
    Function.Bijective
      ((relCohMap (ContinuousMap.id (B × EuclideanSpace ℝ (Fin n)))
          {p : B × EuclideanSpace ℝ (Fin n) | p.2 ∈ mSph n}
          {p : B × EuclideanSpace ℝ (Fin n) | p.2 ≠ 0}
          (fun p hp => by
            intro h0
            simp only [ContinuousMap.id_apply] at h0
            have hp' : ‖p.2‖ = 1 := hp
            rw [h0, norm_zero] at hp'
            exact zero_ne_one hp') ℤ m).hom) := by
  let e2 : ContinuousMap.HomotopyEquiv
      ↥{p : B × EuclideanSpace ℝ (Fin n) | p.2 ∈ mSph n}
      ↥{p : B × EuclideanSpace ℝ (Fin n) | p.2 ≠ 0} :=
    (sphPairHomeo B n).toHomotopyEquiv.trans
      (((ContinuousMap.HomotopyEquiv.refl B).prodCongr (sphPunctEquiv n)).trans
        (punctPairHomeo B n).symm.toHomotopyEquiv)
  have he2 : ∀ q : ↥{p : B × EuclideanSpace ℝ (Fin n) | p.2 ∈ mSph n},
      ((e2.toFun q : ↥{p : B × EuclideanSpace ℝ (Fin n) | p.2 ≠ 0}) :
        B × EuclideanSpace ℝ (Fin n)) =
      (ContinuousMap.id (B × EuclideanSpace ℝ (Fin n)))
        (q : B × EuclideanSpace ℝ (Fin n)) :=
    fun _ => rfl
  exact EuclCleanInfra.bijective_relCohMap_of_homotopyEquiv
    (X := B × EuclideanSpace ℝ (Fin n)) (Y := B × EuclideanSpace ℝ (Fin n))
    {p : B × EuclideanSpace ℝ (Fin n) | p.2 ∈ mSph n}
    {p : B × EuclideanSpace ℝ (Fin n) | p.2 ≠ 0}
    (ContinuousMap.id (B × EuclideanSpace ℝ (Fin n)))
    (fun p hp => by
      intro h0
      simp only [ContinuousMap.id_apply] at h0
      have hp' : ‖p.2‖ = 1 := hp
      rw [h0, norm_zero] at hp'
      exact zero_ne_one hp')
    (Homeomorph.refl (B × EuclideanSpace ℝ (Fin n))).toHomotopyEquiv rfl e2 he2 m

end

end Work.Thom
