import Mathlib
import Submission.Work.Projective.Cover
import Submission.Work.Projective.nonempty_homeo_cp_one_sphere
import Submission.Work.Cohomology.sphereCohomologyTop
import Submission.Work.Cohomology.sphereCohomologyZero
import Submission.Work.Cohomology.MVCohomology

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The cohomology of the complement of a point in `ℂP²`

The open set `V = cp2V = chartSet 1 ∪ chartSet 2 ⊆ ℂP²` is the complement of the point
`[1 : 0 : 0]`.  The map `[z₀ : z₁ : z₂] ↦ [z₁ : z₂]` retracts `V` onto the hyperplane
`ℂP¹ = {[0 : z₁ : z₂]} ⊆ V`, and `[t z₀ : z₁ : z₂]` is a homotopy from the composite
`V → ℂP¹ → V` to the identity.  Hence `V` and `ℂP¹ ≅ S²` are homotopy equivalent, and the
cohomology of `V` is that of `S²`: `H⁰ = ℤ`, `H² = ℤ`, and everything else vanishes.

Everything is built from Mathlib's `Projectivization.lift`, the quotient map
`cpMk 2 : ℂ³ ∖ {0} → ℂP²` (a quotient map by construction of the topology of `ℂP²`), and the
cohomology of the sphere established in `Submission/Work/Cohomology/`.
-/

open scoped LinearAlgebra.Projectivization Manifold ContDiff Topology
open CategoryTheory

namespace Work.Projective

noncomputable section

/-! ## The hyperplane `ℂP¹ ⊆ ℂP²` -/

/-- The nonzero vector `(0, v 0, v 1) ∈ ℂ³` attached to a nonzero vector `v ∈ ℂ²`. -/
def insVec (v : {v : CPV 1 // v ≠ 0}) : {w : CPV 2 // w ≠ 0} :=
  ⟨![0, v.1 0, v.1 1], by
    intro h
    have h0 : v.1 0 = 0 := by simpa using congrFun h 1
    have h1 : v.1 1 = 0 := by simpa using congrFun h 2
    exact v.2 (funext fun i => by fin_cases i <;> simp [h0, h1])⟩

/-- The hyperplane inclusion on the level of vectors: `v ↦ [0 : v 0 : v 1]`. -/
def insAux (v : {v : CPV 1 // v ≠ 0}) : CP 2 := cpMk 2 (insVec v)

theorem insAux_wd (a b : {v : CPV 1 // v ≠ 0}) (t : ℂ) (h : (a : CPV 1) = t • (b : CPV 1)) :
    insAux a = insAux b := by
  refine (cpMk_eq_iff 2 (insVec a) (insVec b)).mpr ⟨t, ?_⟩
  ext j
  fin_cases j <;> simp [insVec, Pi.smul_apply, h]

/-- **The hyperplane inclusion** `ℂP¹ → ℂP²`, `[z₀ : z₁] ↦ [0 : z₀ : z₁]`. -/
def ins : CP 1 → CP 2 := Projectivization.lift insAux insAux_wd

theorem ins_cpMk (v : {v : CPV 1 // v ≠ 0}) : ins (cpMk 1 v) = insAux v := by
  rw [ins, cpMk_apply, Projectivization.lift_mk]

theorem continuous_insVec : Continuous insVec := by
  refine Continuous.subtype_mk (continuous_pi fun j => ?_) _
  fin_cases j <;> simp
  · fun_prop
  · exact (continuous_apply 0).comp continuous_subtype_val
  · exact (continuous_apply 1).comp continuous_subtype_val

theorem continuous_insAux : Continuous insAux := (continuous_cpMk 2).comp continuous_insVec

theorem continuous_ins : Continuous ins := by
  rw [(isQuotientMap_cpMk 1).continuous_iff]
  have h : ins ∘ cpMk 1 = insAux := funext ins_cpMk
  rw [h]
  exact continuous_insAux

theorem insAux_mem (v : {v : CPV 1 // v ≠ 0}) : insAux v ∈ cp2V := by
  have hv : v.1 0 ≠ 0 ∨ v.1 1 ≠ 0 := by
    by_contra h
    push Not at h
    exact v.2 (funext fun i => by fin_cases i <;> simp [h.1, h.2])
  rw [cp2V, Set.mem_union]
  rcases hv with h | h
  · exact Or.inl ((mem_chartSet_iff 1 (insVec v)).mpr (by simpa [insVec] using h))
  · exact Or.inr ((mem_chartSet_iff 2 (insVec v)).mpr (by simpa [insVec] using h))

theorem ins_mem (p : CP 1) : ins p ∈ cp2V := by
  obtain ⟨v, rfl⟩ := cpMk_surjective 1 p
  rw [ins_cpMk]
  exact insAux_mem v

/-- **The hyperplane inclusion** as a continuous map into `cp2V`. -/
def hypIncl_n2 : C(CP 1, ↥cp2V) :=
  ⟨fun p => ⟨ins p, ins_mem p⟩, continuous_ins.subtype_mk ins_mem⟩

/-! ## The preimage of `cp2V` in the punctured vector space -/

/-- A nonzero vector of `ℂ³` represents a point of `cp2V` exactly when its `1`-st or `2`-nd
coordinate is nonzero. -/
theorem mem_preimage_cp2V_iff (v : {v : CPV 2 // v ≠ 0}) :
    cpMk 2 v ∈ cp2V ↔ v.1 1 ≠ 0 ∨ v.1 2 ≠ 0 := by
  rw [cp2V, Set.mem_union, mem_chartSet_iff 1 v, mem_chartSet_iff 2 v]

/-- The preimage of `cp2V` under `cpMk 2`, as a subtype. -/
abbrev PreV_n2 : Type := ↥((cpMk 2) ⁻¹' cp2V)

/-- The restriction of the quotient map `cpMk 2` to `cp2V`: a quotient map onto `↥cp2V`. -/
def qW_n2 : C(PreV_n2, ↥cp2V) :=
  ⟨cp2V.restrictPreimage (cpMk 2), Continuous.subtype_mk ((continuous_cpMk 2).comp
    continuous_subtype_val) _⟩

theorem isQuotientMap_qW_n2 : Topology.IsQuotientMap qW_n2 :=
  (isQuotientMap_cpMk 2).restrictPreimage_isOpen isOpen_cp2V

theorem qW_surjective_n2 : Function.Surjective qW_n2 := isQuotientMap_qW_n2.surjective

/-! ## The retraction `[z₀ : z₁ : z₂] ↦ [z₁ : z₂]` -/

/-- **The retraction** `[z₀ : z₁ : z₂] ↦ [z₁ : z₂]`, on the level of representatives. -/
def rhoAux_n2 (v : PreV_n2) : CP 1 :=
  cpMk 1 ⟨![v.1.1 1, v.1.1 2], fun hz => by
    rcases (mem_preimage_cp2V_iff v.1).mp v.2 with h | h
    · exact h (by simpa using congrFun hz 0)
    · exact h (by simpa using congrFun hz 1)⟩

theorem continuous_rhoVec : Continuous fun v : PreV_n2 => (![v.1.1 1, v.1.1 2] : CPV 1) := by
  refine continuous_pi fun j => ?_
  fin_cases j <;> simp
  · exact (continuous_apply 1).comp (continuous_subtype_val.comp continuous_subtype_val)
  · exact (continuous_apply 2).comp (continuous_subtype_val.comp continuous_subtype_val)

theorem continuous_rhoAux_n2 : Continuous rhoAux_n2 :=
  (continuous_cpMk 1).comp (Continuous.subtype_mk continuous_rhoVec _)

theorem rhoAux_wd_n2 (a b : PreV_n2) (h : qW_n2 a = qW_n2 b) : rhoAux_n2 a = rhoAux_n2 b := by
  have h' : cpMk 2 a.1 = cpMk 2 b.1 := congrArg Subtype.val h
  obtain ⟨s, hs⟩ := (cpMk_eq_iff 2 a.1 b.1).mp h'
  refine (cpMk_eq_iff 1 _ _).mpr ⟨s, ?_⟩
  ext j
  fin_cases j <;> simp only [Pi.smul_apply]
  · simpa using congrFun hs 1
  · simpa using congrFun hs 2

/-- **The retraction** `V → ℂP¹`, `[z₀ : z₁ : z₂] ↦ [z₁ : z₂]`, descended along the quotient
map `cpMk 2`. -/
def rho_n2 : C(↥cp2V, CP 1) :=
  isQuotientMap_qW_n2.lift ⟨rhoAux_n2, continuous_rhoAux_n2⟩ rhoAux_wd_n2

theorem rho_apply_n2 (v : PreV_n2) : rho_n2 (qW_n2 v) = rhoAux_n2 v :=
  congrFun (congrArg (fun (k : C(PreV_n2, CP 1)) => (k : PreV_n2 → CP 1))
    (isQuotientMap_qW_n2.lift_comp ⟨rhoAux_n2, continuous_rhoAux_n2⟩ rhoAux_wd_n2)) v

theorem rhoAux_insVec (v : {v : CPV 1 // v ≠ 0}) :
    rhoAux_n2 ⟨insVec v, insAux_mem v⟩ = cpMk 1 v := by
  show cpMk 1 ⟨![(insVec v).1 1, (insVec v).1 2], _⟩ = cpMk 1 v
  refine (cpMk_eq_iff 1 _ v).mpr ⟨1, ?_⟩
  ext j
  fin_cases j <;> simp [insVec]

/-- The retraction followed by the inclusion of the hyperplane is the identity of `ℂP¹`. -/
theorem rho_comp_hypIncl_n2 : rho_n2.comp hypIncl_n2 = ContinuousMap.id (CP 1) := by
  ext p
  obtain ⟨v, rfl⟩ := cpMk_surjective 1 p
  change rho_n2 (hypIncl_n2 (cpMk 1 v)) = cpMk 1 v
  have h1 : (hypIncl_n2 (cpMk 1 v) : ↥cp2V) = qW_n2 ⟨insVec v, insAux_mem v⟩ := by
    refine Subtype.ext ?_
    change ins (cpMk 1 v) = cpMk 2 (insVec v)
    rw [ins_cpMk]
    rfl
  rw [h1, rho_apply_n2, rhoAux_insVec]

/-! ## The homotopy `[t z₀ : z₁ : z₂]` -/

/-- The straight-line homotopy `(t, z) ↦ (t z₀, z₁, z₂)` in `ℂ³`. -/
def shiftVec_n2 (t : ℝ) (v : CPV 2) : CPV 2 := ![t * v 0, v 1, v 2]

@[simp] theorem shiftVec_apply_zero (t : ℝ) (v : CPV 2) : shiftVec_n2 t v 0 = t * v 0 := rfl

@[simp] theorem shiftVec_apply_one (t : ℝ) (v : CPV 2) : shiftVec_n2 t v 1 = v 1 := rfl

@[simp] theorem shiftVec_apply_two (t : ℝ) (v : CPV 2) : shiftVec_n2 t v 2 = v 2 := rfl

/-- The vector `(0, v 1, v 2) ∈ ℂ³` attached to a vector of `ℂ²` whose `1`-st and `2`-nd
coordinates do not both vanish. -/
def zeroConsVec (v : CPV 2) (hv : v 1 ≠ 0 ∨ v 2 ≠ 0) : {w : CPV 2 // w ≠ 0} :=
  ⟨![0, v 1, v 2], fun hz => by
    rcases hv with h | h
    · exact h (by simpa using congrFun hz 1)
    · exact h (by simpa using congrFun hz 2)⟩

/-- The homotopy `[t z₀ : z₁ : z₂]` on representatives. -/
def Psi_n2 (p : unitInterval × PreV_n2) : CP 2 :=
  cpMk 2 ⟨shiftVec_n2 (p.1 : ℝ) p.2.1.1, fun hz => by
    rcases (mem_preimage_cp2V_iff p.2.1).mp p.2.2 with h | h
    · exact h (by simpa [shiftVec_n2] using congrFun hz 1)
    · exact h (by simpa [shiftVec_n2] using congrFun hz 2)⟩

theorem continuous_shiftVec_n2 :
    Continuous fun p : unitInterval × PreV_n2 => shiftVec_n2 (p.1 : ℝ) p.2.1.1 := by
  refine continuous_pi fun j => ?_
  fin_cases j <;> simp [shiftVec_n2]
  · refine Continuous.mul (g := fun p : unitInterval × PreV_n2 => p.2.1.1 0) ?_ ?_
    · exact Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)
    · exact (continuous_apply 0).comp (continuous_subtype_val.comp (continuous_subtype_val.comp
        continuous_snd))
  · exact (continuous_apply 1).comp (continuous_subtype_val.comp (continuous_subtype_val.comp
      continuous_snd))
  · exact (continuous_apply 2).comp (continuous_subtype_val.comp (continuous_subtype_val.comp
      continuous_snd))

theorem continuous_Psi_n2 : Continuous Psi_n2 :=
  (continuous_cpMk 2).comp (Continuous.subtype_mk continuous_shiftVec_n2 _)

theorem Psi_wd_n2 (t : unitInterval) (a b : PreV_n2) (h : qW_n2 a = qW_n2 b) : Psi_n2 (t, a) = Psi_n2 (t, b) := by
  have h' : cpMk 2 a.1 = cpMk 2 b.1 := congrArg Subtype.val h
  obtain ⟨s, hs⟩ := (cpMk_eq_iff 2 a.1 b.1).mp h'
  have h0 : (a.1.1 : CPV 2) 0 = s * b.1.1 0 := by simpa using (congrFun hs 0).symm
  have h1 : (a.1.1 : CPV 2) 1 = s * b.1.1 1 := by simpa using (congrFun hs 1).symm
  have h2 : (a.1.1 : CPV 2) 2 = s * b.1.1 2 := by simpa using (congrFun hs 2).symm
  refine (cpMk_eq_iff 2 _ _).mpr ⟨s, ?_⟩
  ext j
  fin_cases j <;> simp [Pi.smul_apply, h0, h1, h2]
  ring

theorem Psi_mem_n2 (p : unitInterval × PreV_n2) : Psi_n2 p ∈ cp2V :=
  (mem_preimage_cp2V_iff ⟨shiftVec_n2 (p.1 : ℝ) p.2.1.1, fun hz => by
      rcases (mem_preimage_cp2V_iff p.2.1).mp p.2.2 with h | h
      · exact h (by simpa [shiftVec_n2] using congrFun hz 1)
      · exact h (by simpa [shiftVec_n2] using congrFun hz 2)⟩).mpr (by
    rcases (mem_preimage_cp2V_iff p.2.1).mp p.2.2 with h | h
    · exact Or.inl (by simpa [shiftVec_n2] using h)
    · exact Or.inr (by simpa [shiftVec_n2] using h))

theorem hypIncl_cpMk_n2 (w : {w : CPV 1 // w ≠ 0}) :
    (hypIncl_n2 (cpMk 1 w) : CP 2) = cpMk 2 (insVec w) := by
  show ins (cpMk 1 w) = cpMk 2 (insVec w)
  rw [ins_cpMk]
  rfl

theorem Psi_zero_n2 (v : PreV_n2) : Psi_n2 ((0 : unitInterval), v) = (hypIncl_n2 (rhoAux_n2 v) : CP 2) := by
  have hv : v.1.1 1 ≠ 0 ∨ v.1.1 2 ≠ 0 := (mem_preimage_cp2V_iff v.1).mp v.2
  have hL : Psi_n2 ((0 : unitInterval), v) = cpMk 2 (zeroConsVec v.1.1 hv) := by
    refine congrArg (cpMk 2) (Subtype.ext ?_)
    ext j
    fin_cases j <;> simp [zeroConsVec]
  have hR : (hypIncl_n2 (rhoAux_n2 v) : CP 2) = cpMk 2 (zeroConsVec v.1.1 hv) := by
    rw [show rhoAux_n2 v = cpMk 1 ⟨![v.1.1 1, v.1.1 2], _⟩ from rfl]
    rw [hypIncl_cpMk_n2]
    refine congrArg (cpMk 2) (Subtype.ext ?_)
    ext j
    fin_cases j <;> simp [zeroConsVec, insVec]
  rw [hL, hR]

theorem Psi_one_n2 (v : PreV_n2) : Psi_n2 ((1 : unitInterval), v) = (qW_n2 v : CP 2) := by
  have hL : Psi_n2 ((1 : unitInterval), v) = cpMk 2 ⟨shiftVec_n2 1 v.1.1, _⟩ := rfl
  have hR : (qW_n2 v : CP 2) = cpMk 2 v.1 := rfl
  rw [hL, hR]
  refine congrArg (cpMk 2) (Subtype.ext ?_)
  ext j
  fin_cases j <;> simp

/-! ## The homotopy, descended to `cp2V` -/

/-- The homotopy `[t z₀ : z₁ : z₂]` as a map of `ℂP²`, defined along a chosen representative. -/
def phiRaw_n2 (p : unitInterval × ↥cp2V) : CP 2 :=
  Psi_n2 (p.1, Function.surjInv qW_surjective_n2 p.2)

theorem phiRaw_eq_n2 (t : unitInterval) (v : PreV_n2) : phiRaw_n2 (t, qW_n2 v) = Psi_n2 (t, v) :=
  Psi_wd_n2 t _ _ (Function.surjInv_eq qW_surjective_n2 (qW_n2 v))

theorem continuous_phiRaw_n2 : Continuous phiRaw_n2 := by
  refine isQuotientMap_qW_n2.continuous_lift_prod_right (g := phiRaw_n2) ?_
  have h : (fun p : unitInterval × PreV_n2 => phiRaw_n2 (p.1, qW_n2 p.2)) = Psi_n2 := funext fun p => phiRaw_eq_n2 p.1 p.2
  rw [h]
  exact continuous_Psi_n2

theorem phiRaw_mem_n2 (p : unitInterval × ↥cp2V) : phiRaw_n2 p ∈ cp2V := by
  obtain ⟨v, hv⟩ := qW_surjective_n2 p.2
  have h : phiRaw_n2 p = Psi_n2 (p.1, v) :=
    Psi_wd_n2 p.1 _ _ (by rw [Function.surjInv_eq qW_surjective_n2 p.2, hv])
  rw [h]
  exact Psi_mem_n2 (p.1, v)

/-- The homotopy `[t z₀ : z₁ : z₂]` on `cp2V`. -/
def phi_n2 : C(unitInterval × ↥cp2V, ↥cp2V) :=
  ⟨fun p => ⟨phiRaw_n2 p, phiRaw_mem_n2 p⟩, Continuous.subtype_mk continuous_phiRaw_n2 _⟩

theorem phi_zero_n2 (p : ↥cp2V) : phi_n2 (0, p) = hypIncl_n2 (rho_n2 p) := by
  obtain ⟨v, hv⟩ := qW_surjective_n2 p
  rw [← hv]
  refine Subtype.ext ?_
  show phiRaw_n2 ((0 : unitInterval), qW_n2 v) = (hypIncl_n2 (rho_n2 (qW_n2 v)) : CP 2)
  rw [phiRaw_eq_n2, rho_apply_n2]
  exact Psi_zero_n2 v

theorem phi_one_n2 (p : ↥cp2V) : phi_n2 (1, p) = p := by
  obtain ⟨v, hv⟩ := qW_surjective_n2 p
  rw [← hv]
  refine Subtype.ext ?_
  show phiRaw_n2 ((1 : unitInterval), qW_n2 v) = (qW_n2 v : CP 2)
  rw [phiRaw_eq_n2]
  exact Psi_one_n2 v

/-- The homotopy from the composite `V → ℂP¹ → V` to the identity of `V`. -/
def phiHom_n2 : (hypIncl_n2.comp rho_n2).Homotopy (ContinuousMap.id ↥cp2V) :=
  ContinuousMap.Homotopy.mk phi_n2 (fun p => phi_zero_n2 p) (fun p => phi_one_n2 p)

/-- **`V = cp2V` is homotopy equivalent to `ℂP¹`, hence to `S²`.** -/
theorem nonempty_homotopyEquiv_cp2V_cpOne : Nonempty (ContinuousMap.HomotopyEquiv ↥cp2V (CP 1)) := by
  have h1 : (hypIncl_n2.comp rho_n2).Homotopic (ContinuousMap.id ↥cp2V) := ⟨phiHom_n2⟩
  have h2 : (rho_n2.comp hypIncl_n2).Homotopic (ContinuousMap.id (CP 1)) := by
    rw [rho_comp_hypIncl_n2]
  exact ⟨ContinuousMap.HomotopyEquiv.mk rho_n2 hypIncl_n2 h1 h2⟩

/-- **`V = cp2V` is homotopy equivalent to `S²`.** -/
theorem nonempty_homotopyEquiv_cp2V_sphere :
    Nonempty (ContinuousMap.HomotopyEquiv ↥cp2V
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) := by
  obtain ⟨e⟩ := nonempty_homotopyEquiv_cp2V_cpOne
  obtain ⟨h⟩ := nonempty_homeo_cp_one_sphere
  exact ⟨e.trans h.toHomotopyEquiv⟩

/-- **The cohomology of the complement of a point in `ℂP²`**: `V = chartSet 1 ∪ chartSet 2` is
homotopy equivalent to the hyperplane `ℂP¹ ⊆ V` (via the retraction
`[z₀ : z₁ : z₂] ↦ [0 : z₁ : z₂]`, whose homotopy is `[t z₀ : z₁ : z₂]`), hence to `S²`, so
`H⁰(V) = ℤ`, `H²(V) = ℤ` and `Hⁿ(V) = 0` otherwise. -/
theorem cp2V_cohomology (n : ℕ) :
    Nonempty (Work.Cohomology.singularCohomology ℤ n (TopCat.of ↥(cp2V)) ≅
      ModuleCat.of ℤ (Fin ((if n = 0 then 1 else 0) + (if n = 2 then 1 else 0)) → ℤ)) := by
  obtain ⟨e1⟩ := Work.Cohomology.cohomologyIso_of_homotopyEquiv
    nonempty_homotopyEquiv_cp2V_sphere.some n
  by_cases h0 : n = 0
  · subst h0
    have hk : (if (0 : ℕ) = 0 then 1 else 0) + (if (0 : ℕ) = 2 then 1 else 0) = 1 := by norm_num
    rw [hk]
    have hpc : PathConnectedSpace ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
      have hsphere : IsPathConnected (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
        refine isPathConnected_sphere ?_ 0 (by norm_num)
        rw [show Module.rank ℝ (EuclideanSpace ℝ (Fin 3)) = (3 : Cardinal) from by
          have h2 := LinearEquiv.rank_eq (EuclideanSpace.equiv (Fin 3) ℝ).toLinearEquiv
          rw [h2]
          exact rank_fin_fun 3]
        norm_num
      exact isPathConnected_iff_pathConnectedSpace.mp hsphere
    obtain ⟨e0⟩ := Work.Cohomology.singularCohomology_zero ℤ
      (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1))
    exact ⟨e1 ≪≫ e0 ≪≫ (LinearEquiv.funUnique (Fin 1) ℤ ℤ).toModuleIso.symm⟩
  · by_cases h2 : n = 2
    · subst h2
      have hk : (if (2 : ℕ) = 0 then 1 else 0) + (if (2 : ℕ) = 2 then 1 else 0) = 1 := by norm_num
      rw [hk]
      obtain ⟨e2⟩ := Work.Cohomology.sphereCohomologyTop 2 (by norm_num)
      exact ⟨e1 ≪≫ e2 ≪≫ (LinearEquiv.funUnique (Fin 1) ℤ ℤ).toModuleIso.symm⟩
    · have hk : (if n = 0 then 1 else 0) + (if n = 2 then 1 else 0) = 0 := by
        rw [if_neg h0, if_neg h2]
      rw [hk]
      exact ⟨e1 ≪≫ CategoryTheory.Limits.IsZero.iso
        (Work.Cohomology.sphereCohomologyZero 2 n (by norm_num) h0 h2)
        (ModuleCat.isZero_of_subsingleton (ModuleCat.of ℤ (Fin 0 → ℤ)))⟩

end

end Work.Projective
