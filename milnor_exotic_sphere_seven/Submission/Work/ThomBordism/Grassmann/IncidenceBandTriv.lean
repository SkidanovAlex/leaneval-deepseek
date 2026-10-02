import Mathlib
import Submission.Work.ThomBordism.Grassmann.BandModel
import Submission.Work.ThomBordism.Grassmann.IncidenceBandParam
import Submission.Work.ThomBordism.Grassmann.IncidenceReduce

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-!
# The trivialisation of the equatorial band of the incidence space

The band `bandSet k m = upSet k m ∩ downSet k m` of the incidence space is the set of points whose
direction lies in the equatorial band `bandSph k m` of the unit sphere of `Amb (k+m)`.  Rotating a
point of the fibre over `baseVec` by the rotation that carries `baseVec` to the direction, we obtain
a homeomorphism

`bandSet k m ≃ₜ fibreVec k m × bandSph k m`,

where the parameter space `bandSph k m` is the equatorial band of the unit sphere of `Amb (k+m)` in
the direction of `baseVec`.

The consequence used by the incidence computation is that the restriction
`H^i(upSet) → H^i(bandSet)` is a bijection for `i ≤ k+m-3` (`restU_band_bijective`), and the same
for the lower half (`restV_band_bijective`), obtained from the first by the negation symmetry
`(P,w) ↦ (-P,-w)` of the incidence space.
-/

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial Topology

namespace Work.ThomBordism.Grassmann

noncomputable section

open Work.Cohomology

variable {k m : ℕ}

theorem bandBaseVec_norm (k m : ℕ) (hk : 1 ≤ k) : ‖baseVec k m‖ = 1 :=
  norm_baseVec (by omega)

/-! ## The reindexing isometry `Amb ((k+m-1)+1) ≃ₗᵢ[ℝ] Amb (k+m)` -/

/-- The identification of the two indexings of the ambient space: `(k+m-1)+1 = k+m`. -/
noncomputable def bandCast (k m : ℕ) (hk : 1 ≤ k) : Amb ((k+m-1)+1) ≃ₗᵢ[ℝ] Amb (k+m) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr (by omega))

/-- The last basis vector of `Amb ((k+m-1)+1)`. -/
noncomputable def bandLast (k m : ℕ) : Amb ((k+m-1)+1) :=
  EuclideanSpace.single (Fin.last (k+m-1)) (1 : ℝ)

theorem bandCast_bandLast (k m : ℕ) (hk : 1 ≤ k) :
    bandCast k m hk (bandLast k m) = baseVec k m := by
  have hfin : finCongr (by omega : (k+m-1)+1 = k+m) (Fin.last (k+m-1))
      = (⟨k+m-1, by omega⟩ : Fin (k+m)) := by
    apply Fin.ext
    rw [finCongr_apply, Fin.val_cast, Fin.val_last]
  rw [bandCast, bandLast, EuclideanSpace.piLpCongrLeft_single, baseVec,
    dif_neg (by omega : ¬ (k + m = 0)), hfin]

/-- The natural pairing of an element of `Amb (k+m)` with `baseVec`, in the coordinates of the
reindexed model. -/
theorem inner_bandCast_baseVec (k m : ℕ) (hk : 1 ≤ k) (u : Amb ((k+m-1)+1)) :
    inner ℝ (bandCast k m hk u) (baseVec k m) = u (Fin.last (k+m-1)) := by
  rw [← bandCast_bandLast k m hk, LinearIsometryEquiv.inner_map_map, bandLast,
    EuclideanSpace.inner_single_right]
  simp

/-- The pairing of the inverse cast with `baseVec`. -/
theorem bandCast_symm_apply_last (k m : ℕ) (hk : 1 ≤ k) (u : Amb (k+m)) :
    ((bandCast k m hk).symm u) (Fin.last (k+m-1)) = inner ℝ u (baseVec k m) := by
  rw [← inner_bandCast_baseVec k m hk ((bandCast k m hk).symm u),
    LinearIsometryEquiv.apply_symm_apply]

theorem bandCast_norm (k m : ℕ) (hk : 1 ≤ k) (u : Amb ((k+m-1)+1)) :
    ‖bandCast k m hk u‖ = ‖u‖ :=
  (bandCast k m hk).norm_map u

/-- The cast sends the standard band into the band of the sphere. -/
theorem bandCast_mem_bandSph (k m : ℕ) (hk : 1 ≤ k) (u : Amb ((k+m-1)+1))
    (hu : u ∈ bandStd (k+m-1)) : bandCast k m hk u ∈ bandSph k m := by
  refine ⟨?_, ?_, ?_⟩
  · rw [bandCast_norm]; exact hu.1
  · have h := hu.2.1
    rw [inner_bandCast_baseVec]; exact h
  · have h := hu.2.2
    rw [inner_bandCast_baseVec]; exact h

/-- The inverse cast sends the band of the sphere into the standard band. -/
theorem bandCast_symm_mem_bandStd (k m : ℕ) (hk : 1 ≤ k) (u : Amb (k+m))
    (hu : u ∈ bandSph k m) : (bandCast k m hk).symm u ∈ bandStd (k+m-1) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [(bandCast k m hk).symm.norm_map]; exact hu.1
  · rw [bandCast_symm_apply_last]; exact hu.2.1
  · rw [bandCast_symm_apply_last]; exact hu.2.2

/-- The band of the sphere in the direction of `baseVec` is the reindexed standard band. -/
theorem bandSph_homeo (k m : ℕ) (hk : 1 ≤ k) :
    Nonempty (↥(bandStd (k+m-1)) ≃ₜ ↥(bandSph k m)) :=
  ⟨Homeomorph.subtype (bandCast k m hk).toHomeomorph (fun x => ⟨
    fun hx => bandCast_mem_bandSph k m hk x hx,
    fun hx => by
      have h := bandCast_symm_mem_bandStd k m hk (bandCast k m hk x) hx
      rwa [LinearIsometryEquiv.symm_apply_apply] at h⟩)⟩

/-! ## Two points of the incidence space with the same plane and vector agree -/

/-- A point of the incidence space is determined by its plane and its vector of the plane. -/
theorem incZero_ext {p q : ↥(incZero k m)} (hP : (p.1).1 = (q.1).1)
    (hw : evalVec p.1 = evalVec q.1) : p = q :=
  ((toE_self p).symm.trans (toE_congr hP hw _ _ _ _)).trans (toE_self q)

/-- **`rotE` respects composition of isometries.** -/
theorem rotE_liComp (k m : ℕ) (R S : Amb (k+m) →ₗᵢ[ℝ] Amb (k+m)) (x : ↥(incZero k m)) :
    rotE (liComp R S) x = rotE R (rotE S x) := by
  refine incZero_ext ?_ ?_
  · simp only [rotE_proj]
    exact (planeAct_comp R S (x.1).1).symm
  · simp only [evalVec_rotE, liComp_apply]

/-! ## Continuity of a rotation family in the second slot -/

/-- **The rotation `rotMap e u` is continuous in `(u,y)`** (the parameter in the second slot). -/
theorem continuous_rotMap_family {ι : Type} [TopologicalSpace ι]
    (e : Amb (k+m)) (u : ι → Amb (k+m)) (hu : Continuous u)
    (hne : ∀ i, 1 + inner ℝ (u i) e ≠ 0) :
    Continuous fun q : ι × Amb (k+m) => rotMap e (u q.1) q.2 := by
  have hu' : Continuous fun q : ι × Amb (k+m) => u q.1 := hu.comp continuous_fst
  have hx : Continuous fun q : ι × Amb (k+m) => q.2 := continuous_snd
  have h1 : Continuous fun q : ι × Amb (k+m) => inner ℝ q.2 e :=
    continuous_inner.comp (hx.prodMk continuous_const)
  have h2 : Continuous fun q : ι × Amb (k+m) => inner ℝ q.2 (u q.1) :=
    continuous_inner.comp (hx.prodMk hu')
  have h3 : Continuous fun q : ι × Amb (k+m) => inner ℝ e (u q.1) :=
    continuous_inner.comp (continuous_const.prodMk hu')
  have hden : Continuous fun q : ι × Amb (k+m) => 1 + inner ℝ e (u q.1) :=
    continuous_const.add h3
  have hnum : Continuous fun q : ι × Amb (k+m) =>
      inner ℝ q.2 (u q.1) - inner ℝ q.2 e * inner ℝ e (u q.1) := h2.sub (h1.mul h3)
  have hquot : Continuous fun q : ι × Amb (k+m) =>
      (inner ℝ q.2 (u q.1) - inner ℝ q.2 e * inner ℝ e (u q.1)) / (1 + inner ℝ e (u q.1)) :=
    hnum.div hden (fun q => by
      have h := hne q.1
      rwa [real_inner_comm] at h)
  have hfun : (fun q : ι × Amb (k+m) => rotMap e (u q.1) q.2) =
      fun q => q.2 + (inner ℝ q.2 e) • (u q.1 - e) -
        ((inner ℝ q.2 (u q.1) - inner ℝ q.2 e * inner ℝ e (u q.1)) / (1 + inner ℝ e (u q.1))) •
          (e + u q.1) := rfl
  rw [hfun]
  exact (hx.add (h1.smul (hu'.sub continuous_const))).sub (hquot.smul (continuous_const.add hu'))

/-! ## The upper and lower inclusions of the band -/

/-- The band sits in the upper half. -/
noncomputable def bandInclUp (k m : ℕ) : C(↥(bandSet k m), ↥(upSet k m)) :=
  ⟨fun x => ⟨x.1, x.2.1⟩, continuous_subtype_val.subtype_mk _⟩

/-- The band sits in the lower half. -/
noncomputable def bandInclDown (k m : ℕ) : C(↥(bandSet k m), ↥(downSet k m)) :=
  ⟨fun x => ⟨x.1, x.2.2⟩, continuous_subtype_val.subtype_mk _⟩

/-! ## The rotations of the band -/

/-- The rotation carrying `baseVec` to the direction `u` of the band of the sphere. -/
noncomputable def bandRot (k m : ℕ) (hk : 1 ≤ k) (u : ↥(bandSph k m)) :
    Amb (k+m) →ₗᵢ[ℝ] Amb (k+m) :=
  rotLI (baseVec k m) (u : Amb (k+m)) (bandBaseVec_norm k m hk) u.2.1 (by
    have h : inner ℝ (baseVec k m) (u : Amb (k+m)) = inner ℝ (u : Amb (k+m)) (baseVec k m) :=
      real_inner_comm _ _
    rw [h]
    have h1 := u.2.2.1
    intro h0
    linarith)

@[simp] theorem bandRot_apply (k m : ℕ) (hk : 1 ≤ k) (u : ↥(bandSph k m)) (y : Amb (k+m)) :
    bandRot k m hk u y = rotMap (baseVec k m) (u : Amb (k+m)) y := rfl

theorem bandRot_ne (k m : ℕ) (hk : 1 ≤ k) (u : ↥(bandSph k m)) :
    1 + inner ℝ (baseVec k m) (u : Amb (k+m)) ≠ 0 := by
  have h : inner ℝ (baseVec k m) (u : Amb (k+m)) = inner ℝ (u : Amb (k+m)) (baseVec k m) :=
    real_inner_comm _ _
  rw [h]
  have h1 := u.2.2.1
  intro h0
  linarith

/-- The same nonvanishing condition in the reverse order. -/
theorem bandDir_ne (k m : ℕ) (hk : 1 ≤ k) (u : ↥(bandSph k m)) :
    1 + inner ℝ (u : Amb (k+m)) (baseVec k m) ≠ 0 := by
  rw [real_inner_comm]
  exact bandRot_ne k m hk u

/-- The inverse rotation, carrying the direction `u` back to `baseVec`. -/
noncomputable def bandRotInv (k m : ℕ) (hk : 1 ≤ k) (u : ↥(bandSph k m)) :
    Amb (k+m) →ₗᵢ[ℝ] Amb (k+m) :=
  rotLI (u : Amb (k+m)) (baseVec k m) u.2.1 (bandBaseVec_norm k m hk) (bandDir_ne k m hk u)

@[simp] theorem bandRotInv_apply (k m : ℕ) (hk : 1 ≤ k) (u : ↥(bandSph k m)) (y : Amb (k+m)) :
    bandRotInv k m hk u y = rotMap (u : Amb (k+m)) (baseVec k m) y := rfl

/-- The two rotations are inverse to each other. -/
theorem bandRotInv_bandRot (k m : ℕ) (hk : 1 ≤ k) (u : ↥(bandSph k m)) (y : Amb (k+m)) :
    bandRotInv k m hk u (bandRot k m hk u y) = y := by
  rw [bandRotInv_apply, bandRot_apply]
  exact rotMap_rotMap (bandBaseVec_norm k m hk) u.2.1 (bandRot_ne k m hk u)

/-- The other order of the two rotations. -/
theorem bandRot_bandRotInv (k m : ℕ) (hk : 1 ≤ k) (u : ↥(bandSph k m)) (y : Amb (k+m)) :
    bandRot k m hk u (bandRotInv k m hk u y) = y := by
  rw [bandRotInv_apply, bandRot_apply]
  exact rotMap_rotMap u.2.1 (bandBaseVec_norm k m hk) (bandDir_ne k m hk u)

/-- The rotation carrying the direction of a point of the band back to `baseVec`. -/
noncomputable def bandRotF (k m : ℕ) (hk : 1 ≤ k) (x : ↥(bandSet k m)) :
    Amb (k+m) →ₗᵢ[ℝ] Amb (k+m) :=
  rotLI (dirVec (x : ↥(incZero k m))) (baseVec k m) (norm_dirVec (x : ↥(incZero k m)))
    (bandBaseVec_norm k m hk) (upSet_angle (bandInclUp k m x))

@[simp] theorem bandRotF_apply (k m : ℕ) (hk : 1 ≤ k) (x : ↥(bandSet k m)) (y : Amb (k+m)) :
    bandRotF k m hk x y = rotMap (dirVec (x : ↥(incZero k m))) (baseVec k m) y := rfl

/-- The direction coordinate of a point of the band. -/
noncomputable def bandCoordF (k m : ℕ) (x : ↥(bandSet k m)) : ↥(bandSph k m) :=
  ⟨dirVec (x : ↥(incZero k m)), mem_bandSet_iff_dirVec.mp x.2⟩

/-- The rotation attached to the direction of a point of the band is `bandRotF`. -/
theorem bandRotInv_bandCoordF (k m : ℕ) (hk : 1 ≤ k) (x : ↥(bandSet k m)) :
    bandRotInv k m hk (bandCoordF k m x) = bandRotF k m hk x := by
  apply LinearIsometry.ext
  intro y
  simp only [bandRotInv_apply, bandRotF_apply, bandCoordF]

/-! ## The two maps of the trivialisation -/

/-- The underlying point of the trivialisation: rotate the fibre point by the rotation carrying
`baseVec` to the direction `u`. -/
noncomputable def bandTrivBval (k m : ℕ) (hk : 1 ≤ k)
    (p : ↥(fibreVec k m) × ↥(bandSph k m)) : ↥(incZero k m) :=
  rotE (bandRot k m hk p.2) (p.1 : ↥(incZero k m))

theorem bandTrivBval_mem (k m : ℕ) (hk : 1 ≤ k) (p : ↥(fibreVec k m) × ↥(bandSph k m)) :
    bandTrivBval k m hk p ∈ bandSet k m := by
  refine mem_bandSet_of_dirVec_mem ?_
  rw [bandTrivBval, dirVec_rotE, bandRot_apply, mem_fibreVec_iff.mp p.1.2,
    rotMap_self (bandBaseVec_norm k m hk) p.2.2.1]
  exact p.2.2

/-- **The trivialisation of the band**: `fibreVec × bandSph → bandSet`. -/
noncomputable def bandTrivB (k m : ℕ) (hk : 1 ≤ k)
    (p : ↥(fibreVec k m) × ↥(bandSph k m)) : ↥(bandSet k m) :=
  ⟨bandTrivBval k m hk p, bandTrivBval_mem k m hk p⟩

theorem bandTrivB_eq (k m : ℕ) (hk : 1 ≤ k) (p : ↥(fibreVec k m) × ↥(bandSph k m)) :
    ((bandTrivB k m hk p : ↥(bandSet k m)) : ↥(incZero k m))
      = rotE (bandRot k m hk p.2) (p.1 : ↥(incZero k m)) := rfl

theorem continuous_bandRot (k m : ℕ) (hk : 1 ≤ k) :
    Continuous fun q : (↥(fibreVec k m) × ↥(bandSph k m)) × Amb (k+m) =>
      bandRot k m hk q.1.2 q.2 := by
  have hu : Continuous fun p : ↥(fibreVec k m) × ↥(bandSph k m) => (p.2 : Amb (k+m)) :=
    continuous_subtype_val.comp continuous_snd
  have h := continuous_rotMap_family (k := k) (m := m) (e := baseVec k m)
    (u := fun p : ↥(fibreVec k m) × ↥(bandSph k m) => (p.2 : Amb (k+m))) hu
    (fun p => bandDir_ne k m hk p.2)
  simpa only [rotLI_apply, bandRot, Function.comp_def] using h

theorem continuous_bandTrivB (k m : ℕ) (hk : 1 ≤ k) : Continuous (bandTrivB k m hk) := by
  refine Continuous.subtype_mk ?_ _
  exact continuous_rotE_comp' (k := k) (m := m)
    (ι := ↥(fibreVec k m) × ↥(bandSph k m))
    (R := fun p => bandRot k m hk p.2) (continuous_bandRot k m hk)
    (fun p : ↥(fibreVec k m) × ↥(bandSph k m) => (p.1 : ↥(incZero k m)))
    (continuous_subtype_val.comp continuous_fst)

/-- The fibre coordinate of a point of the band: the retraction onto the fibre over `baseVec`. -/
noncomputable def bandFibreF (k m : ℕ) (hk : 1 ≤ k) (x : ↥(bandSet k m)) : ↥(fibreVec k m) :=
  sPlusFibre hk (bandInclUp k m x)

/-- **The trivialisation of the band**: `bandSet → fibreVec × bandSph`. -/
noncomputable def bandTrivF (k m : ℕ) (hk : 1 ≤ k) (x : ↥(bandSet k m)) :
    ↥(fibreVec k m) × ↥(bandSph k m) :=
  (bandFibreF k m hk x, bandCoordF k m x)

theorem continuous_bandFibreF (k m : ℕ) (hk : 1 ≤ k) : Continuous (bandFibreF k m hk) :=
  (sPlusFibre hk).continuous.comp (bandInclUp k m).continuous

theorem continuous_bandCoordF (k m : ℕ) : Continuous (bandCoordF k m) :=
  Continuous.subtype_mk (continuous_dirVec.comp continuous_subtype_val) _

theorem continuous_bandTrivF (k m : ℕ) (hk : 1 ≤ k) : Continuous (bandTrivF k m hk) :=
  (continuous_bandFibreF k m hk).prodMk (continuous_bandCoordF k m)

/-- The underlying point of the fibre coordinate. -/
theorem bandFibreF_eq (k m : ℕ) (hk : 1 ≤ k) (x : ↥(bandSet k m)) :
    ((bandFibreF k m hk x : ↥(fibreVec k m)) : ↥(incZero k m))
      = rotE (bandRotF k m hk x) (x : ↥(incZero k m)) := rfl

/-- The direction of the point produced by the trivialisation is the parameter. -/
theorem dirVec_bandTrivB (k m : ℕ) (hk : 1 ≤ k) (p : ↥(fibreVec k m) × ↥(bandSph k m)) :
    dirVec ((bandTrivB k m hk p : ↥(bandSet k m)) : ↥(incZero k m)) = (p.2 : Amb (k+m)) := by
  show dirVec (bandTrivBval k m hk p) = (p.2 : Amb (k+m))
  rw [bandTrivBval, dirVec_rotE, bandRot_apply, mem_fibreVec_iff.mp p.1.2,
    rotMap_self (bandBaseVec_norm k m hk) p.2.2.1]

/-! ## The two inverse identities -/

/-- The fibre coordinate of the trivialisation inverts the trivialisation. -/
theorem bandFibreF_bandTrivB (k m : ℕ) (hk : 1 ≤ k) (p : ↥(fibreVec k m) × ↥(bandSph k m)) :
    bandFibreF k m hk (bandTrivB k m hk p) = p.1 := by
  refine Subtype.ext ?_
  calc ((bandFibreF k m hk (bandTrivB k m hk p) : ↥(fibreVec k m)) : ↥(incZero k m))
      = rotE (bandRotInv k m hk p.2) ((bandTrivB k m hk p : ↥(bandSet k m)) : ↥(incZero k m)) := by
        rw [bandFibreF_eq]
        exact rotE_congr (fun y => by
          rw [bandRotInv_apply, bandRotF_apply, dirVec_bandTrivB k m hk p]) _
    _ = rotE (bandRotInv k m hk p.2) (rotE (bandRot k m hk p.2) (p.1 : ↥(incZero k m))) :=
        congrArg (rotE (bandRotInv k m hk p.2)) (bandTrivB_eq k m hk p)
    _ = rotE (liComp (bandRotInv k m hk p.2) (bandRot k m hk p.2)) (p.1 : ↥(incZero k m)) :=
        (rotE_liComp (k := k) (m := m) (R := bandRotInv k m hk p.2)
          (S := bandRot k m hk p.2) (x := (p.1 : ↥(incZero k m)))).symm
    _ = rotE 1 (p.1 : ↥(incZero k m)) :=
        rotE_congr (fun y => by
          show liComp (bandRotInv k m hk p.2) (bandRot k m hk p.2) y
            = (1 : Amb (k+m) →ₗᵢ[ℝ] Amb (k+m)) y
          rw [liComp_apply, show (1 : Amb (k+m) →ₗᵢ[ℝ] Amb (k+m)) y = y from
            LinearIsometry.id_apply y]
          exact bandRotInv_bandRot k m hk p.2 y) _
    _ = (p.1 : ↥(incZero k m)) := rotE_one _

/-- The direction coordinate of the trivialisation inverts the trivialisation. -/
theorem bandCoordF_bandTrivB (k m : ℕ) (hk : 1 ≤ k) (p : ↥(fibreVec k m) × ↥(bandSph k m)) :
    bandCoordF k m (bandTrivB k m hk p) = p.2 :=
  Subtype.ext (dirVec_bandTrivB k m hk p)

theorem bandTrivF_bandTrivB (k m : ℕ) (hk : 1 ≤ k) (p : ↥(fibreVec k m) × ↥(bandSph k m)) :
    bandTrivF k m hk (bandTrivB k m hk p) = p :=
  Prod.ext (bandFibreF_bandTrivB k m hk p) (bandCoordF_bandTrivB k m hk p)

/-- The trivialisation inverts the fibre coordinate. -/
theorem bandTrivB_bandTrivF (k m : ℕ) (hk : 1 ≤ k) (x : ↥(bandSet k m)) :
    bandTrivB k m hk (bandTrivF k m hk x) = x := by
  refine Subtype.ext ?_
  calc ((bandTrivB k m hk (bandTrivF k m hk x) : ↥(bandSet k m)) : ↥(incZero k m))
      = rotE (bandRot k m hk (bandCoordF k m x))
          ((bandFibreF k m hk x : ↥(fibreVec k m)) : ↥(incZero k m)) := rfl
    _ = rotE (bandRot k m hk (bandCoordF k m x))
          (rotE (bandRotInv k m hk (bandCoordF k m x)) (x : ↥(incZero k m))) := by
        rw [bandFibreF_eq]
        exact congrArg (rotE (bandRot k m hk (bandCoordF k m x)))
          (rotE_congr (fun y => by rw [← bandRotInv_bandCoordF k m hk x])
            (x : ↥(incZero k m)))
    _ = rotE (liComp (bandRot k m hk (bandCoordF k m x))
          (bandRotInv k m hk (bandCoordF k m x))) (x : ↥(incZero k m)) :=
        (rotE_liComp (k := k) (m := m) (R := bandRot k m hk (bandCoordF k m x))
          (S := bandRotInv k m hk (bandCoordF k m x)) (x := (x : ↥(incZero k m)))).symm
    _ = rotE 1 (x : ↥(incZero k m)) :=
        rotE_congr (fun y => by
          show liComp (bandRot k m hk (bandCoordF k m x))
            (bandRotInv k m hk (bandCoordF k m x)) y
            = (1 : Amb (k+m) →ₗᵢ[ℝ] Amb (k+m)) y
          rw [liComp_apply, show (1 : Amb (k+m) →ₗᵢ[ℝ] Amb (k+m)) y = y from
            LinearIsometry.id_apply y]
          exact bandRot_bandRotInv k m hk (bandCoordF k m x) y) _
    _ = (x : ↥(incZero k m)) := rotE_one _

/-! ## The homeomorphism -/

/-- **The band of the incidence space is the product of the fibre with the band of the sphere.** -/
noncomputable def bandTrivHomeo (k m : ℕ) (hk : 1 ≤ k) :
    ↥(bandSet k m) ≃ₜ ↥(fibreVec k m) × ↥(bandSph k m) where
  toFun := bandTrivF k m hk
  invFun := bandTrivB k m hk
  left_inv := bandTrivB_bandTrivF k m hk
  right_inv := bandTrivF_bandTrivB k m hk
  continuous_toFun := continuous_bandTrivF k m hk
  continuous_invFun := continuous_bandTrivB k m hk

end

end Work.ThomBordism.Grassmann
