import Mathlib
import Submission.Work.ThomBordism.Grassmann.PlaneEval
import Submission.Work.ThomBordism.Grassmann.IncidenceVector

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-!
# The rotation action on the total space of the tautological bundle

For a linear isometry `R` of the ambient space `Amb (k+m)` this module defines

* `planeAct R P` — the image of the oriented plane `P` under `R`;
* `rotE R x` — the "parallel transport" of a point `x` of the zero complement `E` of the
  tautological bundle (both the plane and the vector of the plane are rotated).

The key computations are `planeAct_memPlane` (`w ∈ P ⇒ R w ∈ R • P`) and `evalVec_rotE`
(`evalVec (rotE R x) = R (evalVec x)`).
-/

open scoped Topology

namespace Work.ThomBordism.Grassmann

noncomputable section

variable {k m : ℕ}

/-! ## The action on oriented planes -/

/-- **The action of a linear isometry of the ambient space on oriented planes.**  The map on frames
`f ↦ (R ∘ f)` preserves orthonormality and commutes with the `SO(k)`-action (linearity of `R`), so
it descends to the oriented Grassmannian. -/
def planeAct (R : Amb (k+m) →ₗᵢ[ℝ] Amb (k+m)) (P : OG k m) : OG k m :=
  Quotient.liftOn P
    (fun f => Quotient.mk'' (⟨fun i => R (f.1 i), ⟨fun i => by
        rw [LinearIsometry.norm_map]; exact f.2.1 i, fun i j hij => by
        show inner ℝ (R (f.1 i)) (R (f.1 j)) = 0
        rw [LinearIsometry.inner_map_map, f.2.2 hij]⟩⟩ : Stiefel k m))
    (by
      intro f g hfg
      obtain ⟨A, rfl⟩ := hfg
      apply Quotient.sound
      refine ⟨A, ?_⟩
      apply Subtype.ext
      funext i
      show R (soActFun A.1 f.1 i) = soActFun A.1 (fun i => R (f.1 i)) i
      simp only [soActFun, map_sum, map_smul])

/-- The computation rule for `planeAct` on a representative frame. -/
theorem planeAct_mk (R : Amb (k+m) →ₗᵢ[ℝ] Amb (k+m)) (f : Stiefel k m) :
    planeAct R (Quotient.mk'' f)
      = Quotient.mk'' (⟨fun i => R (f.1 i), ⟨fun i => by
          rw [LinearIsometry.norm_map]; exact f.2.1 i, fun i j hij => by
          show inner ℝ (R (f.1 i)) (R (f.1 j)) = 0
          rw [LinearIsometry.inner_map_map, f.2.2 hij]⟩⟩ : Stiefel k m) := by
  rw [planeAct]
  exact Quotient.liftOn_mk _ _ f

/-- **`planeAct` carries vectors of a plane to vectors of its image.** -/
theorem planeAct_memPlane (R : Amb (k+m) →ₗᵢ[ℝ] Amb (k+m)) {P : OG k m} {w : Amb (k+m)}
    (hw : memPlane P w) : memPlane (planeAct R P) (R w) := by
  obtain ⟨f, hf, hwspan⟩ := hw
  subst hf
  refine ⟨⟨fun i => R (f.1 i), ⟨fun i => by
      rw [LinearIsometry.norm_map]; exact f.2.1 i, fun i j hij => by
      show inner ℝ (R (f.1 i)) (R (f.1 j)) = 0
      rw [LinearIsometry.inner_map_map, f.2.2 hij]⟩⟩, ?_, ?_⟩
  · exact (planeAct_mk R f).symm
  · obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hwspan
    rw [← hc]
    simp only [map_sum, map_smul]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- **`evalVec` is a vector of the plane.** -/
theorem evalVec_memPlane (p : (tautologicalBundle k m).TotalSpace) : memPlane p.1 (evalVec p) := by
  obtain ⟨f, hf⟩ := Quotient.exists_rep p.1
  obtain ⟨S, hSdet⟩ := exists_chartIdx_det_ne_zero (k := k) (m := m) f.1 f.2.linearIndependent
  have hS : f ∈ chartSet S := (mem_chartSet S f).mpr hSdet
  refine ⟨f, hf, ?_⟩
  have hpS : p.1 ∈ (tautologicalBundle k m).baseSet S := by
    rw [← hf]; exact (mem_baseSet_iff S f).mpr hS
  rw [evalVec_apply_chart p S hpS]
  have hspec := evalChartO_spec (k := k) (m := m) S f hS
    ((tautologicalBundle k m).localTriv S p).2
  rw [show (⟨p.1, hpS⟩ : ↥(baseSet S)) = ⟨Quotient.mk'' f, (mem_baseSet_iff S f).mpr hS⟩ from
    Subtype.ext hf.symm]
  rw [hspec, coordEval]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (coordVec_mem_span S f i)

/-! ## The rotation `rotMap v u` as a linear isometry -/

/-- The rotation `rotMap v u` as a linear map of the ambient space. -/
noncomputable def rotLM (v u : Amb (k+m)) : Amb (k+m) →ₗ[ℝ] Amb (k+m) where
  toFun := rotMap v u
  map_add' x y := by simpa using rotMap_linear v u 1 1 x y
  map_smul' c x := by simpa using rotMap_linear v u c 0 x 0

@[simp] theorem rotLM_apply (v u : Amb (k+m)) (x : Amb (k+m)) :
    rotLM v u x = rotMap v u x := rfl

/-- **`rotLM v u` is an inner-product preserving linear map.** -/
theorem rotLM_inner {v u : Amb (k+m)} (hv : ‖v‖ = 1) (hu : ‖u‖ = 1)
    (h : 1 + inner ℝ v u ≠ 0) :
    ∀ x y : Amb (k+m), inner ℝ (rotLM v u x) (rotLM v u y) = inner ℝ x y := by
  intro x y
  simpa using rotMap_inner (n := k+m) (u := v) (e := u) (x := x) (y := y) hv hu h

/-- The linear map `rotLM v u` is injective. -/
theorem rotLM_eq_zero_iff {v u : Amb (k+m)} (horth : ∀ x y, inner ℝ (rotLM v u x) (rotLM v u y)
    = inner ℝ x y) (a : Amb (k+m)) : rotLM v u a = 0 ↔ a = 0 := by
  constructor
  · intro h0
    have h1 : inner ℝ a a = 0 := by
      rw [← horth a a, h0]
      simp
    rwa [inner_self_eq_zero] at h1
  · intro h0; rw [h0, map_zero]

/-- **The rotation `rotMap v u` as a linear isometry of the ambient space.** -/
noncomputable def rotLI (v u : Amb (k+m)) (hv : ‖v‖ = 1) (hu : ‖u‖ = 1)
    (h : 1 + inner ℝ v u ≠ 0) : Amb (k+m) →ₗᵢ[ℝ] Amb (k+m) where
  toLinearMap := rotLM v u
  norm_map' x := by
    have h1 : ‖rotLM v u x‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, rotLM_inner hv hu h]
    nlinarith [norm_nonneg (rotLM v u x), norm_nonneg x]

@[simp] theorem rotLI_apply (v u : Amb (k+m)) (hv : ‖v‖ = 1) (hu : ‖u‖ = 1)
    (h : 1 + inner ℝ v u ≠ 0) (x : Amb (k+m)) :
    rotLI v u hv hu h x = rotMap v u x := rfl

/-! ## Points of the total space and their evaluation -/

/-- A point of the total space of the tautological bundle from a plane and a fibre coordinate. -/
def mkTotal (P : OG k m) (c : Amb k) : (tautologicalBundle k m).TotalSpace := ⟨P, c⟩

/-- **The evaluation on `mkTotal`, in the chart of the plane.** -/
theorem evalVec_mkTotal (P : OG k m) (c : Amb k) :
    evalVec (mkTotal P c)
      = evalChartO ((tautologicalBundle k m).indexAt P)
          ⟨P, (tautologicalBundle k m).mem_baseSet_at P⟩ c := by
  rw [evalVec_apply_chart (mkTotal P c) ((tautologicalBundle k m).indexAt P)
    ((tautologicalBundle k m).mem_baseSet_at P)]
  congr 1
  rw [VectorBundleCore.localTriv_apply]
  show (tautologicalBundle k m).coordChange ((tautologicalBundle k m).indexAt P)
      ((tautologicalBundle k m).indexAt P) P c = c
  exact VectorBundleCore.coordChange_self (tautologicalBundle k m) _ P
    ((tautologicalBundle k m).mem_baseSet_at P) c

/-- **The defining property of `toE`**: the vector of the plane at that point is the prescribed
vector. -/
theorem evalVec_toE (P : OG k m) (w : Amb (k+m)) (hw0 : w ≠ 0) (hw : memPlane P w) :
    evalVec (toE P w hw0 hw : (tautologicalBundle k m).TotalSpace) = w := by
  show evalVec (mkTotal P (toECoordAt ((tautologicalBundle k m).indexAt P) P w)) = w
  rw [evalVec_mkTotal]
  exact evalChartO_toECoordAt ((tautologicalBundle k m).indexAt P) P
    ((tautologicalBundle k m).mem_baseSet_at P) w hw

/-! ## The rotation action on the zero complement -/

/-- **The rotation `R` acting on the zero complement of the tautological bundle**: both the plane
and the vector of the plane are transported. -/
noncomputable def rotE (R : Amb (k+m) →ₗᵢ[ℝ] Amb (k+m)) (x : ↥(incZero k m)) : ↥(incZero k m) :=
  toE (planeAct R x.1.1) (R (evalVec x.1))
    (by
      intro h0
      have h1 : evalVec x.1 = 0 := by
        have h2 : ‖R (evalVec x.1)‖ = ‖evalVec x.1‖ := LinearIsometry.norm_map R _
        rw [h0, norm_zero] at h2
        exact norm_eq_zero.mp h2.symm
      exact evalVec_ne_zero_of_mem_zeroComplement x.1 x.2 h1)
    (planeAct_memPlane R (evalVec_memPlane x.1))

/-- **The rotation acts on the incidence data by `(P, w) ↦ (R • P, R w)`.** -/
theorem evalVec_rotE (R : Amb (k+m) →ₗᵢ[ℝ] Amb (k+m)) (x : ↥(incZero k m)) :
    evalVec (rotE R x).1 = R (evalVec x.1) :=
  evalVec_toE _ _ _ _

/-- **The plane of a rotated point.** -/
theorem rotE_proj (R : Amb (k+m) →ₗᵢ[ℝ] Amb (k+m)) (x : ↥(incZero k m)) :
    (rotE R x).1.1 = planeAct R x.1.1 := rfl




/-! ## Continuity of the plane action -/

/-- **The plane action is continuous, jointly in the linear isometry (through its values) and the
plane.**  Stated for `Quot (grassmannSetoid k m).r` (definitionally the oriented Grassmannian),
where the quotient topology is the registered instance. -/
theorem continuous_planeAct_family {ι : Type} [TopologicalSpace ι] [LocallyCompactSpace ι]
    (R : ι → Amb (k+m) →ₗᵢ[ℝ] Amb (k+m))
    (hR : Continuous fun q : ι × Amb (k+m) => R q.1 q.2) :
    Continuous fun q : Quot (grassmannSetoid k m).r × ι => planeAct (R q.2) q.1 := by
  have hq : Topology.IsQuotientMap
      (Quot.mk (grassmannSetoid k m).r : Stiefel k m → Quot (grassmannSetoid k m).r) :=
    isQuotientMap_quot_mk
  refine hq.continuous_lift_prod_left
    (g := fun q : Quot (grassmannSetoid k m).r × ι => planeAct (R q.2) q.1) ?_
  have hcont : Continuous fun p : Stiefel k m × ι =>
      Quot.mk (grassmannSetoid k m).r (⟨fun j => R p.2 (p.1.1 j), ⟨fun j => by
        rw [LinearIsometry.norm_map]; exact p.1.2.1 j, fun i j hij => by
        show inner ℝ (R p.2 (p.1.1 i)) (R p.2 (p.1.1 j)) = 0
        rw [LinearIsometry.inner_map_map, p.1.2.2 hij]⟩⟩ : Stiefel k m) := by
    refine continuous_quot_mk.comp (Continuous.subtype_mk ?_ _)
    refine continuous_pi fun j => ?_
    have hm : Continuous fun a : Stiefel k m × ι => (a.2, (a.1.1 : Fin k → Amb (k+m)) j) :=
      continuous_snd.prodMk
        ((continuous_apply j).comp (continuous_subtype_val.comp continuous_fst))
    exact hR.comp hm
  exact hcont.congr (fun p => (planeAct_mk (R p.2) p.1).symm)

end

end Work.ThomBordism.Grassmann
