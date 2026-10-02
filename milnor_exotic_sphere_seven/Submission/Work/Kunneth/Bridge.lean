import Submission.Work.Kunneth.PointDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# The `WithLp` identification of the projective spaces

The two presentations of `ℂP^{n}` used in this workspace are

* `ℙ ℂ (EuclideanSpace ℂ (Fin (n+1)))` — the "Leray–Hirsch" side (`Work.LerayHirsch.tautLineP`,
  `Work.LerayHirsch.zetaP`), where the model fibre `ℂ^{n+1}` is the Euclidean space
  `WithLp 2 (Fin (n+1) → ℂ)`;
* `Work.Projective.CP n = ℙ ℂ (Fin (n+1) → ℂ)` — the "Gen" side (`Work.Gen.tautLine`).

They are identified by the continuous linear equivalence `PiLp.continuousLinearEquiv`, hence by the
homeomorphism `Work.Kunneth.wkHomeo`.
-/

open scoped LinearAlgebra.Projectivization

namespace Work.Kunneth

noncomputable section

/-- **The `ℂ`-linear identification `ℂ^{n+1} ≃ₗ[ℂ] (Fin (n+1) → ℂ)`** of the Euclidean space
`WithLp 2 (Fin (n+1) → ℂ)` with the plain function space. -/
def wkLE (m : ℕ) : EuclideanSpace ℂ (Fin m) ≃ₗ[ℂ] (Fin m → ℂ) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin m => ℂ)).toLinearEquiv

@[simp] theorem wkLE_apply (m : ℕ) (v : EuclideanSpace ℂ (Fin m)) :
    wkLE m v = WithLp.ofLp v := rfl

theorem wkLE_symm_apply (m : ℕ) (v : Fin m → ℂ) :
    (wkLE m).symm v = (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin m => ℂ)).symm v := rfl

/-- `wkLE` is continuous (it is the underlying map of the continuous linear equivalence
`PiLp.continuousLinearEquiv`). -/
theorem continuous_wkLE (m : ℕ) : Continuous (wkLE m) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin m => ℂ)).continuous

/-- Non-vanishing is preserved by `wkLE`. -/
theorem wkLE_ne_zero (m : ℕ) {v : EuclideanSpace ℂ (Fin m)} (hv : v ≠ 0) :
    wkLE m v ≠ 0 := fun h => hv ((wkLE m).injective (by simpa using h))

/-- The underlying map of the `WithLp` identification of projective spaces. -/
def wkMap (n : ℕ) : ℙ ℂ (EuclideanSpace ℂ (Fin (n + 1))) → Work.Projective.CP n :=
  Projectivization.map (wkLE (n + 1) : EuclideanSpace ℂ (Fin (n + 1)) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    (wkLE (n + 1)).injective

/-- The inverse direction of `wkMap`. -/
def wkMapInv (n : ℕ) : Work.Projective.CP n → ℙ ℂ (EuclideanSpace ℂ (Fin (n + 1))) :=
  Projectivization.map ((wkLE (n + 1)).symm : (Fin (n + 1) → ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin (n + 1)))
    (wkLE (n + 1)).symm.injective

theorem wkMap_mk (n : ℕ) (v : EuclideanSpace ℂ (Fin (n + 1))) (hv : v ≠ 0) :
    wkMap n (Projectivization.mk ℂ v hv) =
      Projectivization.mk ℂ (wkLE (n + 1) v) (wkLE_ne_zero (n + 1) hv) :=
  Projectivization.map_mk _ _ v hv

theorem wkMapInv_mk (n : ℕ) (v : Fin (n + 1) → ℂ) (hv : v ≠ 0) :
    wkMapInv n (Projectivization.mk ℂ v hv) =
      Projectivization.mk ℂ ((wkLE (n + 1)).symm v)
        (fun h => hv ((wkLE (n + 1)).symm.injective (by simpa using h))) :=
  Projectivization.map_mk _ _ v hv

/-- On representatives, `wkMap` is `WithLp.ofLp`, whence continuous by the quotient universal
property. -/
theorem continuous_wkMap (n : ℕ) : Continuous (wkMap n) := by
  have hq : Topology.IsQuotientMap (Projectivization.mk' ℂ :
      {v : EuclideanSpace ℂ (Fin (n + 1)) // v ≠ 0} →
        ℙ ℂ (EuclideanSpace ℂ (Fin (n + 1)))) :=
    isQuotientMap_quotient_mk'
  have hqt : Topology.IsQuotientMap (Projectivization.mk' ℂ :
      {v : Fin (n + 1) → ℂ // v ≠ 0} → Work.Projective.CP n) :=
    isQuotientMap_quotient_mk'
  refine hq.continuous_iff.mpr ?_
  have hcomp : (wkMap n) ∘ (Projectivization.mk' ℂ :
        {v : EuclideanSpace ℂ (Fin (n + 1)) // v ≠ 0} →
          ℙ ℂ (EuclideanSpace ℂ (Fin (n + 1))))
      = (Projectivization.mk' ℂ :
          {v : Fin (n + 1) → ℂ // v ≠ 0} → Work.Projective.CP n) ∘
        (fun v : {v : EuclideanSpace ℂ (Fin (n + 1)) // v ≠ 0} =>
          (⟨wkLE (n + 1) v.1, wkLE_ne_zero (n + 1) v.2⟩ :
            {v : Fin (n + 1) → ℂ // v ≠ 0})) := by
    funext v
    exact wkMap_mk n v.1 v.2
  rw [hcomp]
  exact Continuous.comp hqt.continuous (Continuous.subtype_mk
    ((continuous_wkLE (n + 1)).comp continuous_subtype_val) _)

theorem continuous_wkMapInv (n : ℕ) : Continuous (wkMapInv n) := by
  have hq : Topology.IsQuotientMap (Projectivization.mk' ℂ :
      {v : Fin (n + 1) → ℂ // v ≠ 0} → Work.Projective.CP n) :=
    isQuotientMap_quotient_mk'
  have hqt : Topology.IsQuotientMap (Projectivization.mk' ℂ :
      {v : EuclideanSpace ℂ (Fin (n + 1)) // v ≠ 0} →
        ℙ ℂ (EuclideanSpace ℂ (Fin (n + 1)))) :=
    isQuotientMap_quotient_mk'
  refine hq.continuous_iff.mpr ?_
  have hcomp : (wkMapInv n) ∘ (Projectivization.mk' ℂ :
        {v : Fin (n + 1) → ℂ // v ≠ 0} → Work.Projective.CP n)
      = (Projectivization.mk' ℂ :
          {v : EuclideanSpace ℂ (Fin (n + 1)) // v ≠ 0} →
            ℙ ℂ (EuclideanSpace ℂ (Fin (n + 1)))) ∘
        (fun v : {v : Fin (n + 1) → ℂ // v ≠ 0} =>
          (⟨(wkLE (n + 1)).symm v.1,
              fun h => v.2 ((wkLE (n + 1)).symm.injective (by simpa using h))⟩ :
            {v : EuclideanSpace ℂ (Fin (n + 1)) // v ≠ 0})) := by
    funext v
    exact wkMapInv_mk n v.1 v.2
  rw [hcomp]
  refine Continuous.comp hqt.continuous (Continuous.subtype_mk ?_ _)
  exact (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin (n + 1) => ℂ)).symm.continuous.comp
    continuous_subtype_val

theorem wkMap_wkMapInv (n : ℕ) (x : Work.Projective.CP n) : wkMap n (wkMapInv n x) = x := by
  refine Projectivization.ind (K := ℂ) (V := Fin (n + 1) → ℂ) ?_ x
  intro v hv
  rw [wkMapInv_mk]
  show wkMap n (Projectivization.mk ℂ ((wkLE (n + 1)).symm v) _) = Projectivization.mk ℂ v hv
  rw [wkMap_mk]
  rw [Projectivization.mk_eq_mk_iff]
  exact ⟨1, by rw [one_smul, LinearEquiv.apply_symm_apply]⟩

theorem wkMapInv_wkMap (n : ℕ) (x : ℙ ℂ (EuclideanSpace ℂ (Fin (n + 1)))) :
    wkMapInv n (wkMap n x) = x := by
  refine Projectivization.ind (K := ℂ) (V := EuclideanSpace ℂ (Fin (n + 1))) ?_ x
  intro v hv
  rw [wkMap_mk]
  show wkMapInv n (Projectivization.mk ℂ (wkLE (n + 1) v) _) =
    Projectivization.mk ℂ v hv
  rw [wkMapInv_mk]
  rw [Projectivization.mk_eq_mk_iff]
  exact ⟨1, by rw [one_smul, LinearEquiv.symm_apply_apply]⟩

/-- **The identification of the two presentations of `ℂP^{n}`**: the homeomorphism
`ℙ ℂ (EuclideanSpace ℂ (Fin (n+1))) ≃ₜ ℙ ℂ (Fin (n+1) → ℂ)` induced by `WithLp.equiv`. -/
def wkHomeo (n : ℕ) : ℙ ℂ (EuclideanSpace ℂ (Fin (n + 1))) ≃ₜ Work.Projective.CP n where
  toFun := wkMap n
  invFun := wkMapInv n
  left_inv := wkMapInv_wkMap n
  right_inv := wkMap_wkMapInv n
  continuous_toFun := continuous_wkMap n
  continuous_invFun := continuous_wkMapInv n

@[simp] theorem wkHomeo_apply (n : ℕ) (x : ℙ ℂ (EuclideanSpace ℂ (Fin (n + 1)))) :
    wkHomeo n x = wkMap n x := rfl

@[simp] theorem wkHomeo_mk (n : ℕ) (v : EuclideanSpace ℂ (Fin (n + 1))) (hv : v ≠ 0) :
    wkHomeo n (Projectivization.mk ℂ v hv) =
      Projectivization.mk ℂ (WithLp.ofLp v) (wkLE_ne_zero (n + 1) hv) :=
  wkMap_mk n v hv



/-! ## 2. The identification of the tautological line bundles

`Work.LerayHirsch.tautLineP (n+1)` (over `ℙ ℂ (EuclideanSpace ℂ (Fin (n+1)))`) and
`Work.Thom.bundleComap (Work.Gen.tautLine n) (Work.Kunneth.wkCM n)` are two presentations of the
tautological line bundle `O(-1)` of `ℂP^{n}`: the same charts and the same transition functions
(ratios of homogeneous coordinates).  The isomorphism is therefore the identity on the fibres up to
a scalar gauge `Work.Kunneth.gauge` comparing the two *preferred* frames.
-/

/-- The homeomorphism `wkHomeo n`, as a continuous map (the form in which `bundleComap` uses it). -/
def wkCM (n : ℕ) : C(ℙ ℂ (EuclideanSpace ℂ (Fin (n + 1))), Work.Projective.CP n) :=
  ⟨wkHomeo n, (wkHomeo n).continuous_toFun⟩

@[simp] theorem wkCM_apply (n : ℕ) (b : ℙ ℂ (EuclideanSpace ℂ (Fin (n + 1)))) :
    wkCM n b = wkHomeo n b := rfl

/-- The `Fin (n+1)`-part of the preferred index of `tautLineP (n+1)`. -/
def pref1 (n : ℕ) (b : ℙ ℂ (EuclideanSpace ℂ (Fin (n + 1)))) : Fin (n + 1) :=
  ((Work.LerayHirsch.tautLineP (n + 1)).indexAt b).2

/-- The preferred index of `Gen.tautLine n` at `wkHomeo n b`. -/
def pref2 (n : ℕ) (b : ℙ ℂ (EuclideanSpace ℂ (Fin (n + 1)))) : Fin (n + 1) :=
  (Work.Gen.tautLine n).indexAt (wkCM n b)

/-- The scalar gauge comparing the two preferred frames: the ratio of the two preferred
homogeneous coordinates of a representative. -/
def gauge (n : ℕ) (b : ℙ ℂ (EuclideanSpace ℂ (Fin (n + 1)))) : ℂ :=
  Work.Gen.homCoord n (pref1 n b) (pref2 n b) (wkCM n b)

/-- The representative of `b`, as a vector of `Fin (n+1) → ℂ`. -/
def repVec (n : ℕ) (b : ℙ ℂ (EuclideanSpace ℂ (Fin (n + 1)))) : Fin (n + 1) → ℂ :=
  (b.rep).ofLp

theorem repVec_apply (n : ℕ) (b : ℙ ℂ (EuclideanSpace ℂ (Fin (n + 1)))) (k : Fin (n + 1)) :
    repVec n b k = (b.rep).ofLp k := rfl

/-- **The `k`-th coordinate as a `ℂ`-linear functional** on `EuclideanSpace ℂ (Fin m)`. -/
def coordLM (m : ℕ) (k : Fin m) : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] ℂ :=
  (LinearMap.proj k : (Fin m → ℂ) →ₗ[ℂ] ℂ).comp (wkLE m).toLinearMap

theorem coordLM_apply (m : ℕ) (k : Fin m) (v : EuclideanSpace ℂ (Fin m)) :
    coordLM m k v = (wkLE m v) k := rfl

theorem coordLM_eq_ofLp (m : ℕ) (k : Fin m) (v : EuclideanSpace ℂ (Fin m)) :
    coordLM m k v = v.ofLp k := by
  rw [coordLM_apply, wkLE_apply]

/-- The chart coordinates of the trivial bundle are the vector coordinates. -/
theorem chartCoord_trivCore (n : ℕ) (i : PUnit)
    (p : ↥(Work.Thom.zeroComplement (Work.Thom.realification
      (Work.LerayHirsch.trivCore (n + 1))))) :
    Work.LerayHirsch.chartCoord (Work.LerayHirsch.trivCore (n + 1)) i p =
      (show EuclideanSpace ℂ (Fin (n + 1)) from p.1.2) := rfl

/-- The punctured point of `trivCore (n+1)` corresponding to the representative of `b`. -/
def repP (n : ℕ) (b : ℙ ℂ (EuclideanSpace ℂ (Fin (n + 1)))) :
    ↥(Work.Thom.zeroComplement (Work.Thom.realification (Work.LerayHirsch.trivCore (n + 1)))) :=
  ⟨⟨PUnit.unit, b.rep⟩, by
    rw [Work.Thom.mem_zeroComplement]
    exact Projectivization.rep_nonzero b⟩

theorem repVec_ne_zero' (n : ℕ) (b : ℙ ℂ (EuclideanSpace ℂ (Fin (n + 1)))) :
    repVec n b ≠ 0 := by
  intro h
  refine Projectivization.rep_nonzero b (WithLp.ofLp_injective 2 ?_)
  rw [show (b.rep).ofLp = repVec n b from rfl, h]
  rfl

theorem mkP_eq_mk (m : ℕ) (v : {v : EuclideanSpace ℂ (Fin m) // v ≠ 0}) :
    Work.LerayHirsch.mkP m v = Projectivization.mk ℂ v.1 v.2 := rfl

/-- **The base sets of the two presentations agree**: the `k`-th chart of `tautLineP (n+1)` is the
preimage under `wkHomeo n` of the `k`-th chart of `Gen.tautLine n`. -/
theorem mem_tautLineP_iff (n : ℕ) (k : Fin (n + 1)) (b : ℙ ℂ (EuclideanSpace ℂ (Fin (n + 1)))) :
    b ∈ (Work.LerayHirsch.tautLineP (n + 1)).baseSet (PUnit.unit, k) ↔
      wkHomeo n b ∈ Work.Projective.chartSet k := by
  revert b
  refine Projectivization.ind (K := ℂ) (V := EuclideanSpace ℂ (Fin (n + 1))) ?_
  intro v hv
  rw [Work.LerayHirsch.mem_tautLineP_baseSet,
    show wkHomeo n (Projectivization.mk ℂ v hv) =
      Work.Projective.cpMk n ⟨v.ofLp, wkLE_ne_zero (n + 1) hv⟩ from rfl]
  rw [Work.Projective.mem_chartSet_iff]
  constructor
  · rintro ⟨w, hw, hk⟩
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff ℂ w.1 v w.2 hv).mp hw
    rw [Units.smul_def] at ha
    have hk' : coordLM (n + 1) k w.1 ≠ 0 := by rwa [coordLM_eq_ofLp]
    have h1 : coordLM (n + 1) k w.1 = (a : ℂ) * coordLM (n + 1) k v := by
      rw [← ha, map_smul, smul_eq_mul]
    intro h0
    have h0' : coordLM (n + 1) k v = 0 := by rwa [coordLM_eq_ofLp]
    exact hk' (by rw [h1, h0', mul_zero])
  · intro hk
    exact ⟨⟨v, hv⟩, rfl, hk⟩

/-- The representative's `k`-th coordinate is nonzero on the `k`-th chart of `tautLineP`. -/
theorem repVec_ne_zero_of_mem (n : ℕ) (k : Fin (n + 1))
    {b : ℙ ℂ (EuclideanSpace ℂ (Fin (n + 1)))}
    (hb : b ∈ (Work.LerayHirsch.tautLineP (n + 1)).baseSet (PUnit.unit, k)) :
    repVec n b k ≠ 0 := by
  rw [Work.LerayHirsch.mem_tautLineP_baseSet] at hb
  obtain ⟨w, hw, hk⟩ := hb
  have hrep : Projectivization.mk ℂ b.rep b.rep_nonzero = Projectivization.mk ℂ w.1 w.2 := by
    rw [Projectivization.mk_rep, ← hw, ← mkP_eq_mk]
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff ℂ b.rep w.1 b.rep_nonzero w.2).mp hrep
  rw [Units.smul_def] at ha
  have hk' : coordLM (n + 1) k w.1 ≠ 0 := by rwa [coordLM_eq_ofLp]
  have h1 : coordLM (n + 1) k b.rep = (a : ℂ) * coordLM (n + 1) k w.1 := by
    rw [← ha, map_smul, smul_eq_mul]
  rw [repVec_apply, ← coordLM_eq_ofLp, h1]
  exact mul_ne_zero (Units.ne_zero a) hk'

/-- The preferred chart of `Gen.tautLine n` contains `wkHomeo n b`. -/
theorem mem_chartSet_pref2 (n : ℕ) (b : ℙ ℂ (EuclideanSpace ℂ (Fin (n + 1)))) :
    wkHomeo n b ∈ Work.Projective.chartSet (pref2 n b) := by
  have h := (Work.Gen.tautLine n).mem_baseSet_at (wkCM n b)
  rw [Work.Gen.tautLine_baseSet] at h
  rw [pref2, Work.Gen.tautLine_indexAt]
  exact h

/-- The preferred chart of `tautLineP (n+1)` (transported by `wkHomeo n`) contains `wkHomeo n b`. -/
theorem mem_chartSet_pref1 (n : ℕ) (b : ℙ ℂ (EuclideanSpace ℂ (Fin (n + 1)))) :
    wkHomeo n b ∈ Work.Projective.chartSet (pref1 n b) := by
  have h := (Work.LerayHirsch.tautLineP (n + 1)).mem_baseSet_at b
  have h' : b ∈ (Work.LerayHirsch.tautLineP (n + 1)).baseSet (PUnit.unit, pref1 n b) := h
  exact (mem_tautLineP_iff n (pref1 n b) b).mp h'

/-- The gauge does not vanish. -/
theorem gauge_ne_zero (n : ℕ) (b : ℙ ℂ (EuclideanSpace ℂ (Fin (n + 1)))) : gauge n b ≠ 0 :=
  Work.Gen.homCoord_ne_zero_of_mem (pref1 n b) (pref2 n b) (mem_chartSet_pref1 n b)
    (mem_chartSet_pref2 n b)

/-- **`wkHomeo n b` is the class of `repVec n b`**. -/
theorem wkHomeo_rep (n : ℕ) (b : ℙ ℂ (EuclideanSpace ℂ (Fin (n + 1)))) :
    wkHomeo n b = Work.Projective.cpMk n ⟨repVec n b, repVec_ne_zero' n b⟩ := by
  conv_lhs => rw [← Projectivization.mk_rep b]
  rw [wkHomeo_mk]
  congr 1

/-- **`homCoord` in terms of the representative's coordinates.** -/
theorem homCoord_eq_repVec (n : ℕ) (i j : Fin (n + 1))
    (b : ℙ ℂ (EuclideanSpace ℂ (Fin (n + 1)))) (h : repVec n b i ≠ 0) :
    Work.Gen.homCoord n i j (wkCM n b) = repVec n b j / repVec n b i := by
  rw [wkCM_apply, wkHomeo_rep n b]
  exact Work.Gen.ChernGen.homCoord_cpMk (n := n) i ⟨repVec n b, repVec_ne_zero' n b⟩ h j

theorem projUniv_rep (n : ℕ) (b : ℙ ℂ (EuclideanSpace ℂ (Fin (n + 1)))) :
    (Work.LerayHirsch.projUniv (n + 1)) b =
      Work.LerayHirsch.mkProj (Work.LerayHirsch.trivCore (n + 1)) (repP n b) := by
  conv_lhs => rw [← Projectivization.mk_rep b]
  rw [show Projectivization.mk ℂ b.rep b.rep_nonzero =
      Work.LerayHirsch.mkP (n + 1) ⟨b.rep, b.rep_nonzero⟩ from rfl]
  rw [Work.LerayHirsch.projUniv_mkP]
  exact congrArg (Work.LerayHirsch.mkProj (Work.LerayHirsch.trivCore (n + 1)))
    (Subtype.ext rfl)

theorem indexAt_tautLineP (n : ℕ) (b : ℙ ℂ (EuclideanSpace ℂ (Fin (n + 1)))) :
    (Work.LerayHirsch.tautLineP (n + 1)).indexAt b = (PUnit.unit, pref1 n b) := rfl

theorem eq_unit_pair (n : ℕ) (ik : PUnit × Fin (n + 1)) : ik = (PUnit.unit, ik.2) :=
  Prod.ext (Subsingleton.elim _ _) rfl

/-- **The transition coefficient of `tautLineP (n+1)` at the preferred chart.** -/
theorem tautCoeffLift_rep (n : ℕ) (ik jl : PUnit × Fin (n + 1))
    (b : ℙ ℂ (EuclideanSpace ℂ (Fin (n + 1)))) (h : repVec n b ik.2 ≠ 0) :
    Work.LerayHirsch.tautCoeffLift (Work.LerayHirsch.trivCore (n + 1)) ik jl
        ((Work.LerayHirsch.projUniv (n + 1)) b)
      = repVec n b jl.2 / repVec n b ik.2 := by
  rw [projUniv_rep]
  rw [Work.LerayHirsch.tautLine_coordChange_eq_ratio (Work.LerayHirsch.trivCore (n + 1)) ik jl
    (repP n b) ?_]
  · rfl
  · exact h

/-- **The transition function of `tautLineP (n+1)` in coordinates.** -/
theorem coordChange_tautLineP (n : ℕ) (ik jl : PUnit × Fin (n + 1))
    (b : ℙ ℂ (EuclideanSpace ℂ (Fin (n + 1)))) (h : repVec n b ik.2 ≠ 0) :
    (Work.LerayHirsch.tautLineP (n + 1)).coordChange ik jl b
      = (repVec n b jl.2 / repVec n b ik.2) •
          ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1)) := by
  rw [Work.LerayHirsch.tautLineP, Work.Thom.bundleComap_coordChange,
    Work.LerayHirsch.tautLine_coordChange, Work.LerayHirsch.tautCoeffCLM,
    tautCoeffLift_rep n ik jl b h]

/-- **The transition function of the pulled-back `Gen.tautLine n` in coordinates.** -/
theorem coordChange_tautLine (n : ℕ) (i j : Fin (n + 1))
    (b : ℙ ℂ (EuclideanSpace ℂ (Fin (n + 1)))) :
    (Work.Thom.bundleComap (Work.Gen.tautLine n) (wkCM n)).coordChange i j b
      = (Work.Gen.homCoord n i j (wkCM n b)) •
          ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1)) :=
  (Work.Thom.bundleComap_coordChange (Work.Gen.tautLine n) (wkCM n) i j b).trans
    (Work.Gen.tautLine_coordChange n i j (wkCM n b))

theorem indexAt_bundleComap_tautLine (n : ℕ) (b : ℙ ℂ (EuclideanSpace ℂ (Fin (n + 1)))) :
    (Work.Thom.bundleComap (Work.Gen.tautLine n) (wkCM n)).indexAt b = pref2 n b :=
  (Work.Thom.bundleComap_indexAt (Work.Gen.tautLine n) (wkCM n) b).trans rfl

theorem baseSet_bundleComap_tautLine (n : ℕ) (i : Fin (n + 1)) :
    (Work.Thom.bundleComap (Work.Gen.tautLine n) (wkCM n)).baseSet i =
      (wkCM n) ⁻¹' (Work.Projective.chartSet i) := by
  rw [Work.Thom.bundleComap_baseSet, Work.Gen.tautLine_baseSet]

/-- **The scalar identity underlying the isomorphism.** -/
theorem gauge_scalar (n : ℕ) (i₁ : PUnit × Fin (n + 1)) (i₂ : Fin (n + 1))
    (b : ℙ ℂ (EuclideanSpace ℂ (Fin (n + 1))))
    (h : repVec n b i₁.2 ≠ 0) (hi₂ : wkHomeo n b ∈ Work.Projective.chartSet i₂) :
    Work.Gen.homCoord n (pref2 n b) i₂ (wkCM n b) *
        (gauge n b * (repVec n b (pref1 n b) / repVec n b i₁.2))
      = Work.Gen.homCoord n i₁.2 i₂ (wkCM n b) := by
  have hpref1 : repVec n b (pref1 n b) ≠ 0 := by
    refine repVec_ne_zero_of_mem n (pref1 n b) ?_
    exact (Work.LerayHirsch.tautLineP (n + 1)).mem_baseSet_at b
  have hc2 : wkCM n b ∈ Work.Projective.chartSet (pref2 n b) := by
    simpa using mem_chartSet_pref2 n b
  have hc1 : wkCM n b ∈ Work.Projective.chartSet (pref1 n b) := by
    simpa using mem_chartSet_pref1 n b
  have hc3 : wkCM n b ∈ Work.Projective.chartSet i₂ := by simpa using hi₂
  have hprod : Work.Gen.homCoord n (pref2 n b) i₂ (wkCM n b) *
      Work.Gen.homCoord n (pref1 n b) (pref2 n b) (wkCM n b)
      = Work.Gen.homCoord n (pref1 n b) i₂ (wkCM n b) :=
    (Work.Gen.homCoord_mul (i := pref1 n b) (j := pref2 n b) (k := i₂) hc1 hc2 hc3).symm
  rw [gauge,
    show Work.Gen.homCoord n (pref2 n b) i₂ (wkCM n b) *
        (Work.Gen.homCoord n (pref1 n b) (pref2 n b) (wkCM n b) *
          (repVec n b (pref1 n b) / repVec n b i₁.2))
        = Work.Gen.homCoord n (pref1 n b) i₂ (wkCM n b) *
          (repVec n b (pref1 n b) / repVec n b i₁.2) from by
      rw [← mul_assoc, hprod],
    homCoord_eq_repVec n (pref1 n b) i₂ b hpref1, homCoord_eq_repVec n i₁.2 i₂ b h]
  field_simp

end

end Work.Kunneth

namespace Work.Kunneth

open scoped LinearAlgebra.Projectivization

noncomputable section

/-- **The trivialised matrix of the bundle isomorphism.**  On the chart overlap, the composite of
the two transition functions and the gauge is multiplication by `homCoord n i₁.2 i₂ (wkCM n b)`. -/
theorem repVec_ne_zero_of_chart (n : ℕ) (k : Fin (n + 1))
    {b : ℙ ℂ (EuclideanSpace ℂ (Fin (n + 1)))}
    (h : wkCM n b ∈ Work.Projective.chartSet k) : repVec n b k ≠ 0 := by
  rw [wkCM_apply, wkHomeo_rep n b] at h
  exact (Work.Projective.mem_chartSet_iff k ⟨repVec n b, repVec_ne_zero' n b⟩).mp h

/-- The composite of three scalar multiples of the identity. -/
theorem smul_id_comp (a b c : ℂ) :
    (a • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1))) ∘SL
      ((b • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1))) ∘SL
        (c • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1))))
      = (a * (b * c)) • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1)) := by
  ext v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply]
  rw [smul_smul, smul_smul, mul_assoc]

/-- **The trivialised matrix of the bundle isomorphism.**  On the chart overlap, the composite of
the two transition functions and the gauge is multiplication by `homCoord n i₁.2 i₂ (wkCM n b)`. -/
theorem bridge_composite_point (n : ℕ) (i₁ : PUnit × Fin (n + 1)) (i₂ : Fin (n + 1))
    {b : ℙ ℂ (EuclideanSpace ℂ (Fin (n + 1)))}
    (hb : b ∈ (Work.LerayHirsch.tautLineP (n + 1)).baseSet i₁ ∩
        (Work.Thom.bundleComap (Work.Gen.tautLine n) (wkCM n)).baseSet i₂) :
    (Work.Thom.bundleComap (Work.Gen.tautLine n) (wkCM n)).coordChange
        ((Work.Thom.bundleComap (Work.Gen.tautLine n) (wkCM n)).indexAt b) i₂ b ∘SL
      ((gauge n b • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1))) ∘SL
        (Work.LerayHirsch.tautLineP (n + 1)).coordChange i₁
          ((Work.LerayHirsch.tautLineP (n + 1)).indexAt b) b)
      = (Work.Gen.homCoord n i₁.2 i₂ (wkCM n b)) •
          ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1)) := by
  obtain ⟨hb₁, hb₂⟩ := hb
  have hb₁' : b ∈ (Work.LerayHirsch.tautLineP (n + 1)).baseSet (PUnit.unit, i₁.2) := by
    rw [eq_unit_pair n i₁] at hb₁; exact hb₁
  have hb₂' : wkCM n b ∈ Work.Projective.chartSet i₂ := by
    rw [baseSet_bundleComap_tautLine n i₂] at hb₂
    exact hb₂
  have h₁ : (Work.LerayHirsch.tautLineP (n + 1)).coordChange i₁
      ((Work.LerayHirsch.tautLineP (n + 1)).indexAt b) b
      = (repVec n b (pref1 n b) / repVec n b i₁.2) •
          ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1)) := by
    rw [indexAt_tautLineP n b, eq_unit_pair n i₁]
    exact coordChange_tautLineP n (PUnit.unit, i₁.2) (PUnit.unit, pref1 n b) b
      (repVec_ne_zero_of_mem n i₁.2 hb₁')
  have h₂ : (Work.Thom.bundleComap (Work.Gen.tautLine n) (wkCM n)).coordChange
      ((Work.Thom.bundleComap (Work.Gen.tautLine n) (wkCM n)).indexAt b) i₂ b
      = (Work.Gen.homCoord n (pref2 n b) i₂ (wkCM n b)) •
          ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1)) := by
    rw [indexAt_bundleComap_tautLine n b]
    exact coordChange_tautLine n (pref2 n b) i₂ b
  rw [h₁, h₂, smul_id_comp,
    gauge_scalar n i₁ i₂ b (repVec_ne_zero_of_mem n i₁.2 hb₁') hb₂']

/-- **The trivialised matrix of the inverse isomorphism.** -/
theorem bridge_composite_inv_point (n : ℕ) (i₂ : Fin (n + 1)) (i₁ : PUnit × Fin (n + 1))
    {b : ℙ ℂ (EuclideanSpace ℂ (Fin (n + 1)))}
    (hb : b ∈ (Work.Thom.bundleComap (Work.Gen.tautLine n) (wkCM n)).baseSet i₂ ∩
        (Work.LerayHirsch.tautLineP (n + 1)).baseSet i₁) :
    (Work.LerayHirsch.tautLineP (n + 1)).coordChange
        ((Work.LerayHirsch.tautLineP (n + 1)).indexAt b) i₁ b ∘SL
      (((gauge n b)⁻¹ • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1))) ∘SL
        (Work.Thom.bundleComap (Work.Gen.tautLine n) (wkCM n)).coordChange i₂
          ((Work.Thom.bundleComap (Work.Gen.tautLine n) (wkCM n)).indexAt b) b)
      = (Work.Gen.homCoord n i₁.2 i₂ (wkCM n b))⁻¹ •
          ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1)) := by
  obtain ⟨hb₂, hb₁⟩ := hb
  have hb₁' : b ∈ (Work.LerayHirsch.tautLineP (n + 1)).baseSet (PUnit.unit, i₁.2) := by
    rw [eq_unit_pair n i₁] at hb₁; exact hb₁
  have hb₂' : wkCM n b ∈ Work.Projective.chartSet i₂ := by
    rw [baseSet_bundleComap_tautLine n i₂] at hb₂
    exact hb₂
  have hi₁ : repVec n b i₁.2 ≠ 0 := repVec_ne_zero_of_mem n i₁.2 hb₁'
  have hpref1 : repVec n b (pref1 n b) ≠ 0 :=
    repVec_ne_zero_of_mem n (pref1 n b) ((Work.LerayHirsch.tautLineP (n + 1)).mem_baseSet_at b)
  have hi₂ : repVec n b i₂ ≠ 0 := repVec_ne_zero_of_chart n i₂ hb₂'
  have hc1 : wkCM n b ∈ Work.Projective.chartSet (pref1 n b) := by
    simpa using mem_chartSet_pref1 n b
  have hc2 : wkCM n b ∈ Work.Projective.chartSet (pref2 n b) := by
    simpa using mem_chartSet_pref2 n b
  have h₁ : (Work.LerayHirsch.tautLineP (n + 1)).coordChange
      ((Work.LerayHirsch.tautLineP (n + 1)).indexAt b) i₁ b
      = (repVec n b i₁.2 / repVec n b (pref1 n b)) •
          ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1)) := by
    rw [indexAt_tautLineP n b, eq_unit_pair n i₁]
    exact coordChange_tautLineP n (PUnit.unit, pref1 n b) (PUnit.unit, i₁.2) b hpref1
  have h₂ : (Work.Thom.bundleComap (Work.Gen.tautLine n) (wkCM n)).coordChange i₂
      ((Work.Thom.bundleComap (Work.Gen.tautLine n) (wkCM n)).indexAt b) b
      = (Work.Gen.homCoord n i₂ (pref2 n b) (wkCM n b)) •
          ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1)) := by
    rw [indexAt_bundleComap_tautLine n b]
    exact coordChange_tautLine n i₂ (pref2 n b) b
  -- the scalar identities
  have hrel : repVec n b i₁.2 / repVec n b (pref1 n b) =
      (repVec n b (pref1 n b) / repVec n b i₁.2)⁻¹ := (inv_div _ _).symm
  have hrel2 : Work.Gen.homCoord n i₂ (pref2 n b) (wkCM n b) =
      (Work.Gen.homCoord n (pref2 n b) i₂ (wkCM n b))⁻¹ := by
    rw [homCoord_eq_repVec n i₂ (pref2 n b) b hi₂,
      homCoord_eq_repVec n (pref2 n b) i₂ b
        (repVec_ne_zero_of_chart n (pref2 n b) hc2), inv_div]
  rw [h₁, h₂, smul_id_comp, hrel, hrel2]
  rw [show (repVec n b (pref1 n b) / repVec n b i₁.2)⁻¹ *
        ((gauge n b)⁻¹ * (Work.Gen.homCoord n (pref2 n b) i₂ (wkCM n b))⁻¹)
      = (Work.Gen.homCoord n i₁.2 i₂ (wkCM n b))⁻¹ from by
    rw [← gauge_scalar n i₁ i₂ b hi₁ hb₂', mul_inv_rev, mul_inv_rev]
    ring]

/-- **Continuity of the trivialised matrix of the bundle isomorphism.** -/
theorem bridge_composite (n : ℕ) (i₁ : PUnit × Fin (n + 1)) (i₂ : Fin (n + 1)) :
    ContinuousOn (fun b : ℙ ℂ (EuclideanSpace ℂ (Fin (n + 1))) =>
        (Work.Thom.bundleComap (Work.Gen.tautLine n) (wkCM n)).coordChange
            ((Work.Thom.bundleComap (Work.Gen.tautLine n) (wkCM n)).indexAt b) i₂ b ∘SL
          ((gauge n b • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1))) ∘SL
            (Work.LerayHirsch.tautLineP (n + 1)).coordChange i₁
              ((Work.LerayHirsch.tautLineP (n + 1)).indexAt b) b))
      ((Work.LerayHirsch.tautLineP (n + 1)).baseSet i₁ ∩
        (Work.Thom.bundleComap (Work.Gen.tautLine n) (wkCM n)).baseSet i₂) := by
  have hcont : ContinuousOn (fun b : ℙ ℂ (EuclideanSpace ℂ (Fin (n + 1))) =>
      (Work.Gen.homCoord n i₁.2 i₂ (wkCM n b)) •
        ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1)))
      ((Work.LerayHirsch.tautLineP (n + 1)).baseSet i₁ ∩
        (Work.Thom.bundleComap (Work.Gen.tautLine n) (wkCM n)).baseSet i₂) := by
    have hc : ContinuousOn (fun b : ℙ ℂ (EuclideanSpace ℂ (Fin (n + 1))) =>
        Work.Gen.homCoord n i₁.2 i₂ (wkCM n b))
        ((Work.LerayHirsch.tautLineP (n + 1)).baseSet i₁ ∩
          (Work.Thom.bundleComap (Work.Gen.tautLine n) (wkCM n)).baseSet i₂) := by
      refine (Work.Gen.continuousOn_homCoord i₁.2 i₂).comp
        ((wkCM n).continuous.continuousOn) ?_
      intro b hb
      have hb₁ : b ∈ (Work.LerayHirsch.tautLineP (n + 1)).baseSet i₁ := hb.1
      have h' : b ∈ (Work.LerayHirsch.tautLineP (n + 1)).baseSet (PUnit.unit, i₁.2) := by
        rw [eq_unit_pair n i₁] at hb₁; exact hb₁
      exact (mem_tautLineP_iff n i₁.2 b).mp h'
    exact hc.smul (continuousOn_const : ContinuousOn
      (fun _ : ℙ ℂ (EuclideanSpace ℂ (Fin (n + 1))) =>
        (ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1)) :
          EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1))) _)
  exact hcont.congr (fun b hb => (bridge_composite_point n i₁ i₂ hb))

/-- **Continuity of the trivialised matrix of the inverse isomorphism.** -/
theorem bridge_composite_inv (n : ℕ) (i₂ : Fin (n + 1)) (i₁ : PUnit × Fin (n + 1)) :
    ContinuousOn (fun b : ℙ ℂ (EuclideanSpace ℂ (Fin (n + 1))) =>
        (Work.LerayHirsch.tautLineP (n + 1)).coordChange
            ((Work.LerayHirsch.tautLineP (n + 1)).indexAt b) i₁ b ∘SL
          (((gauge n b)⁻¹ • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1))) ∘SL
            (Work.Thom.bundleComap (Work.Gen.tautLine n) (wkCM n)).coordChange i₂
              ((Work.Thom.bundleComap (Work.Gen.tautLine n) (wkCM n)).indexAt b) b))
      ((Work.Thom.bundleComap (Work.Gen.tautLine n) (wkCM n)).baseSet i₂ ∩
        (Work.LerayHirsch.tautLineP (n + 1)).baseSet i₁) := by
  have hnonzero : ∀ b ∈ ((Work.Thom.bundleComap (Work.Gen.tautLine n) (wkCM n)).baseSet i₂ ∩
      (Work.LerayHirsch.tautLineP (n + 1)).baseSet i₁),
      Work.Gen.homCoord n i₁.2 i₂ (wkCM n b) ≠ 0 := by
    intro b hb
    have hb₁ : b ∈ (Work.LerayHirsch.tautLineP (n + 1)).baseSet i₁ := hb.2
    have h' : b ∈ (Work.LerayHirsch.tautLineP (n + 1)).baseSet (PUnit.unit, i₁.2) := by
      rw [eq_unit_pair n i₁] at hb₁; exact hb₁
    have hc1 : wkCM n b ∈ Work.Projective.chartSet i₁.2 := (mem_tautLineP_iff n i₁.2 b).mp h'
    have hb₂ : b ∈ (Work.Thom.bundleComap (Work.Gen.tautLine n) (wkCM n)).baseSet i₂ := hb.1
    simp only [Work.Thom.bundleComap_baseSet, Set.mem_preimage] at hb₂
    rw [Work.Gen.tautLine_baseSet] at hb₂
    have hc2 : wkCM n b ∈ Work.Projective.chartSet i₂ := by rwa [wkCM_apply] at hb₂
    exact Work.Gen.homCoord_ne_zero_of_mem i₁.2 i₂ hc1 hc2
  have hcont : ContinuousOn (fun b : ℙ ℂ (EuclideanSpace ℂ (Fin (n + 1))) =>
      (Work.Gen.homCoord n i₁.2 i₂ (wkCM n b))⁻¹ •
        ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1)))
      ((Work.Thom.bundleComap (Work.Gen.tautLine n) (wkCM n)).baseSet i₂ ∩
        (Work.LerayHirsch.tautLineP (n + 1)).baseSet i₁) := by
    have hc : ContinuousOn (fun b : ℙ ℂ (EuclideanSpace ℂ (Fin (n + 1))) =>
        Work.Gen.homCoord n i₁.2 i₂ (wkCM n b))
        ((Work.Thom.bundleComap (Work.Gen.tautLine n) (wkCM n)).baseSet i₂ ∩
          (Work.LerayHirsch.tautLineP (n + 1)).baseSet i₁) := by
      refine (Work.Gen.continuousOn_homCoord i₁.2 i₂).comp
        ((wkCM n).continuous.continuousOn) ?_
      intro b hb
      have hb₁ : b ∈ (Work.LerayHirsch.tautLineP (n + 1)).baseSet i₁ := hb.2
      have h' : b ∈ (Work.LerayHirsch.tautLineP (n + 1)).baseSet (PUnit.unit, i₁.2) := by
        rw [eq_unit_pair n i₁] at hb₁; exact hb₁
      exact (mem_tautLineP_iff n i₁.2 b).mp h'
    exact (hc.inv₀ hnonzero).smul (continuousOn_const : ContinuousOn
      (fun _ : ℙ ℂ (EuclideanSpace ℂ (Fin (n + 1))) =>
        (ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1)) :
          EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1))) _)
  exact hcont.congr (fun b hb => (bridge_composite_inv_point n i₂ i₁ hb))

/-- **The bundle isomorphism** between the two presentations of the tautological line bundle. -/
def bridgeIso (n : ℕ) : Work.Thom.BundleIso (Work.LerayHirsch.tautLineP (n + 1))
    (Work.Thom.bundleComap (Work.Gen.tautLine n) (wkCM n)) where
  hom b := gauge n b • (LinearMap.id : EuclideanSpace ℂ (Fin 1) →ₗ[ℂ] EuclideanSpace ℂ (Fin 1))
  inv b := (gauge n b)⁻¹ • (LinearMap.id : EuclideanSpace ℂ (Fin 1) →ₗ[ℂ] EuclideanSpace ℂ (Fin 1))
  left_inv b x := by
    change (gauge n b)⁻¹ • (gauge n b • x) = x
    rw [smul_smul, inv_mul_cancel₀ (gauge_ne_zero n b), one_smul]
  right_inv b x := by
    change (gauge n b) • ((gauge n b)⁻¹ • x) = x
    rw [smul_smul, mul_inv_cancel₀ (gauge_ne_zero n b), one_smul]
  continuous_hom := by
    refine (Work.Thom.continuous_totalSpaceMap_clm
      (Work.LerayHirsch.tautLineP (n + 1))
      (Work.Thom.bundleComap (Work.Gen.tautLine n) (wkCM n)) (ContinuousMap.id _)
      (fun b => gauge n b • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1)))
      (fun i₁ i₂ => bridge_composite n i₁ i₂)).congr (fun p => rfl)
  continuous_inv := by
    refine (Work.Thom.continuous_totalSpaceMap_clm
      (Work.Thom.bundleComap (Work.Gen.tautLine n) (wkCM n))
      (Work.LerayHirsch.tautLineP (n + 1)) (ContinuousMap.id _)
      (fun b => (gauge n b)⁻¹ • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1)))
      (fun i₂ i₁ => bridge_composite_inv n i₂ i₁)).congr (fun p => rfl)

/-- **The existence of the bridge isomorphism.** -/
theorem nonempty_bridgeIso (n : ℕ) :
    Nonempty (Work.Thom.BundleIso (Work.LerayHirsch.tautLineP (n + 1))
      (Work.Thom.bundleComap (Work.Gen.tautLine n) (wkCM n))) :=
  ⟨bridgeIso n⟩

/-- **The first Chern class of the tautological bundle in the two presentations.** -/
theorem zetaP_eq_chernClass (n : ℕ) :
    Work.Thom.chernClass 1 1 (Work.LerayHirsch.tautLineP (n + 1)) =
      (Work.Thom.CohMap (wkCM n) ℤ 2).hom (Work.Thom.chernClass 1 1 (Work.Gen.tautLine n)) :=
  (Work.Thom.chernClass_homeo (wkHomeo n) (Work.LerayHirsch.tautLineP (n + 1))
    (Work.Gen.tautLine n) (bridgeIso n)).symm

end

end Work.Kunneth
