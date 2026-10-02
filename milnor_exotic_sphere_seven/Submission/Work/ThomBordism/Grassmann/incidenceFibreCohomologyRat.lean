import Mathlib
import Submission.Work.ThomBordism.Grassmann.Model
import Submission.Work.SignatureBordism.Rationalisation
import Submission.Work.ThomBordism.Grassmann.SphereCover
import Submission.Work.ThomBordism.Grassmann.IncidenceReduce
import Submission.Work.ThomBordism.Grassmann.Retraction
import Submission.Work.ThomBordism.Grassmann.UpSetRetract
import Submission.Work.ThomBordism.Grassmann.FibreModel
import Submission.Work.ThomBordism.Grassmann.OCPlaneHomeo
import Submission.Work.ThomBordism.Grassmann.IncidenceBandRestrict
import Submission.Work.Cohomology.totallyDisconnected
import Submission.Work.Cohomology.cohomology_prod_contractible

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.ThomBordism.Grassmann

open scoped Topology
open CategoryTheory Limits

noncomputable section

variable {k m : ℕ}

/-!
# The incidence fibre isomorphism, rationally

The target: for `1 ≤ k`, `1 ≤ j`, `j ≤ k + m - 3` the rational cohomology of the sphere bundle of
the tautological bundle over `G̃r_k(ℝ^{k+m})` agrees with that of `G̃r_{k-1}(ℝ^{k+m-1}) = OG (k-1) m`.

The proof goes through the incidence fibration whose fibre over the distinguished vector
`baseVec k m` is the space of `k`-planes containing it; this file identifies that fibre with
`OG (k-1) m`.
-/

/-- **The standard basis vectors of `Amb (k+m)` at the first `(k-1)+m` positions are orthonormal.** -/
theorem orthonormal_single_castLE (k m : ℕ) :
    Orthonormal ℝ (fun i : Fin ((k-1)+m) =>
      EuclideanSpace.single (Fin.castLE (show (k-1)+m ≤ k+m by omega) i) (1 : ℝ)) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [EuclideanSpace.inner_single_left, PiLp.single_apply, map_one, one_mul]
  by_cases h : i = j
  · rw [if_pos h, if_pos (by rw [h])]
  · rw [if_neg h, if_neg (fun hc => h (Fin.castLE_injective _ hc))]

/-- **Inserting a zero in the last coordinate of `Amb ((k-1)+m)`.**  The formula is written with
`Fin.castLE` so that no type casts are needed. -/
def insFun (k m : ℕ) (x : EuclideanSpace ℝ (Fin ((k-1)+m))) :
    EuclideanSpace ℝ (Fin (k+m)) :=
  ∑ i : Fin ((k-1)+m),
    (x.ofLp i) • EuclideanSpace.single (Fin.castLE (show (k-1)+m ≤ k+m by omega) i) (1 : ℝ)

theorem insFun_add (k m : ℕ) (x y : EuclideanSpace ℝ (Fin ((k-1)+m))) :
    insFun k m (x + y) = insFun k m x + insFun k m y := by
  simp only [insFun, PiLp.add_apply, add_smul, Finset.sum_add_distrib]

theorem insFun_smul (k m : ℕ) (c : ℝ) (x : EuclideanSpace ℝ (Fin ((k-1)+m))) :
    insFun k m (c • x) = c • insFun k m x := by
  simp only [insFun, PiLp.smul_apply]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_assoc]

/-- **`insFun` preserves the norm**: it is the orthogonal embedding of `Amb ((k-1)+m)` into
`Amb (k+m)` with image the orthogonal complement of the last basis vector. -/
theorem norm_insFun (k m : ℕ) (x : EuclideanSpace ℝ (Fin ((k-1)+m))) :
    ‖insFun k m x‖ = ‖x‖ := by
  have h1 : ‖insFun k m x‖ ^ 2 = ∑ i : Fin ((k-1)+m), (x.ofLp i) * (x.ofLp i) := by
    rw [insFun, ← real_inner_self_eq_norm_sq]
    rw [Orthonormal.inner_sum (orthonormal_single_castLE k m) (fun i => x.ofLp i)
      (fun i => x.ofLp i) Finset.univ]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp
  have h2 : ‖x‖ ^ 2 = ∑ i : Fin ((k-1)+m), (x.ofLp i) * (x.ofLp i) := by
    rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [pow_two]
  have h3 : ‖insFun k m x‖ ^ 2 = ‖x‖ ^ 2 := by rw [h1, h2]
  nlinarith [norm_nonneg (insFun k m x), norm_nonneg x]

/-- **The linear isometry `Amb ((k-1)+m) → e^⊥ ⊆ Amb (k+m)`**, the "insert a zero in the last
coordinate" embedding, whose image is the orthogonal complement of `baseVec k m`. -/
def insE (k m : ℕ) : EuclideanSpace ℝ (Fin ((k-1)+m)) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (k+m)) where
  toLinearMap :=
    { toFun := insFun k m
      map_add' := insFun_add k m
      map_smul' := insFun_smul k m }
  norm_map' := fun x => by
    show ‖insFun k m x‖ = ‖x‖
    exact norm_insFun k m x


/-- **The coordinate formula of `insFun`**: on the first `(k-1)+m` coordinates it is the identity. -/
theorem insFun_apply_castLE (k m : ℕ) (x : EuclideanSpace ℝ (Fin ((k-1)+m)))
    (i : Fin ((k-1)+m)) :
    (insFun k m x).ofLp (Fin.castLE (show (k-1)+m ≤ k+m by omega) i) = x.ofLp i := by
  simp only [insFun]
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  rw [Finset.sum_eq_single i]
  · rw [WithLp.ofLp_smul, Pi.smul_apply, PiLp.single_apply, if_pos rfl, smul_eq_mul, mul_one]
  · intro j _ hj
    rw [WithLp.ofLp_smul, Pi.smul_apply, PiLp.single_apply,
      if_neg (fun hc => hj (Fin.castLE_injective _ hc).symm), smul_eq_mul, mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- **The last coordinate of `insFun` vanishes** (for `1 ≤ k`, where the last coordinate is not
among the first `(k-1)+m`). -/
theorem insFun_apply_last (k m : ℕ) (hk : 1 ≤ k) (x : EuclideanSpace ℝ (Fin ((k-1)+m))) :
    (insFun k m x).ofLp ⟨k+m-1, by omega⟩ = 0 := by
  simp only [insFun]
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [WithLp.ofLp_smul, Pi.smul_apply, PiLp.single_apply]
  rw [if_neg, smul_eq_mul, mul_zero]
  intro hc
  have hv := congrArg Fin.val hc
  simp only [Fin.val_castLE] at hv
  omega

/-- **The coordinate projection onto the first `(k-1)+m` coordinates. -/
def projFun (k m : ℕ) (y : EuclideanSpace ℝ (Fin (k+m))) :
    EuclideanSpace ℝ (Fin ((k-1)+m)) :=
  ∑ i : Fin ((k-1)+m),
    (y.ofLp (Fin.castLE (show (k-1)+m ≤ k+m by omega) i)) • EuclideanSpace.single i (1 : ℝ)

/-- The coordinate formula of `projFun`. -/
theorem projFun_apply (k m : ℕ) (y : EuclideanSpace ℝ (Fin (k+m))) (i : Fin ((k-1)+m)) :
    (projFun k m y).ofLp i = y.ofLp (Fin.castLE (show (k-1)+m ≤ k+m by omega) i) := by
  simp only [projFun]
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  rw [Finset.sum_eq_single i]
  · rw [WithLp.ofLp_smul, Pi.smul_apply, PiLp.single_apply, if_pos rfl, smul_eq_mul, mul_one]
  · intro j _ hj
    rw [WithLp.ofLp_smul, Pi.smul_apply, PiLp.single_apply,
      if_neg (fun hc => hj hc.symm), smul_eq_mul, mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- **`projFun` is a left inverse of `insFun`.** -/
theorem projFun_insFun (k m : ℕ) (x : EuclideanSpace ℝ (Fin ((k-1)+m))) :
    projFun k m (insFun k m x) = x := by
  ext1 i
  rw [projFun_apply, insFun_apply_castLE]

/-- **`insFun` is a left inverse of `projFun`** on the orthogonal complement of the last basis
vector. -/
theorem insFun_projFun (k m : ℕ) (hk : 1 ≤ k) (y : EuclideanSpace ℝ (Fin (k+m)))
    (hy : y.ofLp ⟨k+m-1, by omega⟩ = 0) :
    insFun k m (projFun k m y) = y := by
  ext1 j
  rw [insFun]
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  by_cases hj : ∃ i : Fin ((k-1)+m),
      Fin.castLE (show (k-1)+m ≤ k+m by omega) i = j
  · obtain ⟨i, rfl⟩ := hj
    rw [Finset.sum_eq_single i]
    · rw [WithLp.ofLp_smul, Pi.smul_apply, PiLp.single_apply, if_pos rfl, smul_eq_mul, mul_one,
        projFun_apply]
    · intro l _ hl
      rw [WithLp.ofLp_smul, Pi.smul_apply, PiLp.single_apply,
        if_neg (fun hc => hl (Fin.castLE_injective _ hc).symm), smul_eq_mul, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  · push_neg at hj
    rw [Finset.sum_eq_zero]
    · have hjl : j = ⟨k+m-1, by omega⟩ := by
        apply Fin.ext
        have h1 : (j : ℕ) < k + m := j.2
        have h2 : ¬ (j : ℕ) < (k-1) + m := fun hlt => hj ⟨j, hlt⟩ rfl
        simp only [Fin.val_mk] at h2 ⊢
        omega
      rw [hjl, hy]
    · intro i _
      rw [WithLp.ofLp_smul, Pi.smul_apply, PiLp.single_apply,
        if_neg (fun hc => hj i hc.symm), smul_eq_mul, mul_zero]



/-! ## The `k`-frame spanned by `baseVec` and a `(k-1)`-frame in its orthogonal complement -/

/-- **The `k`-frame `(e, f_1, …)`** obtained from a vector `e` and a `(k-1)`-frame `f`. -/
def frameOf (k m : ℕ) (e : Amb (k+m)) (f : Fin (k-1) → Amb (k+m)) : Fin k → Amb (k+m) :=
  fun i => if h : (i : ℕ) = 0 then e else f ⟨(i : ℕ) - 1, by have := i.2; omega⟩

theorem frameOf_zero (k m : ℕ) (e : Amb (k+m)) (f : Fin (k-1) → Amb (k+m)) (hk : 1 ≤ k) :
    frameOf k m e f ⟨0, by omega⟩ = e := by
  rw [frameOf]
  exact dif_pos rfl

/-- **The `j`-th vector, for `j ≥ 1`, is `f (j-1)`.** -/
theorem frameOf_succ (k m : ℕ) (e : Amb (k+m)) (f : Fin (k-1) → Amb (k+m))
    (j : Fin (k-1)) :
    frameOf k m e f ⟨(j : ℕ) + 1, by have := j.2; omega⟩ = f j := by
  rw [frameOf]
  rw [dif_neg (by simp)]
  exact congrArg f (Fin.ext (by simp))

/-- **The `k`-frame `(e, f_1, …)` is orthonormal** when `e` is a unit vector orthogonal to the
`(k-1)`-frame `f`. -/
theorem orthonormal_frameOf (k m : ℕ) (hk : 1 ≤ k) (e : Amb (k+m))
    (f : Fin (k-1) → Amb (k+m)) (he : ‖e‖ = 1) (hf : Orthonormal ℝ f)
    (hef : ∀ j, inner ℝ e (f j) = 0) :
    Orthonormal ℝ (frameOf k m e f) := by
  rw [orthonormal_iff_ite]
  intro i j
  have hsplit : ∀ i : Fin k, (i : ℕ) = 0 ∨ ∃ i' : Fin (k-1),
      i = ⟨(i' : ℕ) + 1, by have := i'.2; omega⟩ := by
    intro i
    by_cases h : (i : ℕ) = 0
    · exact Or.inl h
    · right
      refine ⟨⟨(i : ℕ) - 1, by have := i.2; omega⟩, Fin.ext (by simp; omega)⟩
  rcases hsplit i with hi | ⟨i', rfl⟩
  · have hiz : i = ⟨0, by omega⟩ := Fin.ext (by simpa using hi)
    rw [hiz, frameOf_zero k m e f hk]
    rcases hsplit j with hj | ⟨j', rfl⟩
    · have hjz : j = ⟨0, by omega⟩ := Fin.ext (by simpa using hj)
      rw [hjz, frameOf_zero k m e f hk, if_pos rfl, real_inner_self_eq_norm_sq, he]
      norm_num
    · rw [frameOf_succ, hef, if_neg]
      intro hc
      have hval : (j' : ℕ) + 1 = 0 := by
        have := congrArg Fin.val hc
        simpa using this.symm
      omega
  · rw [frameOf_succ]
    rcases hsplit j with hj | ⟨j', rfl⟩
    · have hjz : j = ⟨0, by omega⟩ := Fin.ext (by simpa using hj)
      rw [hjz, frameOf_zero k m e f hk, real_inner_comm, hef, if_neg]
      intro hc
      have hval : (i' : ℕ) + 1 = 0 := by
        have := congrArg Fin.val hc
        simpa using this.symm
      omega
    · have h1 := (orthonormal_iff_ite.mp hf) i' j'
      rw [frameOf_succ, h1]
      by_cases hij : i' = j'
      · rw [if_pos hij, if_pos (by rw [hij])]
      · rw [if_neg hij, if_neg (fun hc => hij (Fin.ext (by
          have hval : (i' : ℕ) + 1 = (j' : ℕ) + 1 := by
            simpa using congrArg Fin.val hc
          omega)))]

/-! ## The `(k-1)`-frames in the orthogonal complement of `baseVec` -/

theorem insE_apply (k m : ℕ) (x : EuclideanSpace ℝ (Fin ((k-1)+m))) :
    insE k m x = insFun k m x := rfl

theorem insE_apply_castLE (k m : ℕ) (x : EuclideanSpace ℝ (Fin ((k-1)+m)))
    (i : Fin ((k-1)+m)) :
    (insE k m x).ofLp (Fin.castLE (show (k-1)+m ≤ k+m by omega) i) = x.ofLp i :=
  insFun_apply_castLE k m x i

theorem insE_apply_last (k m : ℕ) (hk : 1 ≤ k) (x : EuclideanSpace ℝ (Fin ((k-1)+m))) :
    (insE k m x).ofLp ⟨k+m-1, by omega⟩ = 0 :=
  insFun_apply_last k m hk x

/-- **`insE` lands in the orthogonal complement of `baseVec`.** -/
theorem inner_insE_baseVec (k m : ℕ) (hk : 1 ≤ k) (x : EuclideanSpace ℝ (Fin ((k-1)+m))) :
    inner ℝ (baseVec k m) (insE k m x) = 0 := by
  have hne : k + m ≠ 0 := by omega
  rw [baseVec, dif_neg hne, EuclideanSpace.inner_single_left]
  rw [insE_apply_last k m hk x]
  simp

/-- **The image under `insE` of an orthonormal frame is orthonormal.** -/
theorem orthonormal_insE_comp (k m : ℕ) {f : Fin (k-1) → EuclideanSpace ℝ (Fin ((k-1)+m))}
    (hf : Orthonormal ℝ f) :
    Orthonormal ℝ (fun j => insE k m (f j)) := by
  rw [orthonormal_iff_ite] at hf ⊢
  intro i j
  rw [LinearIsometry.inner_map_map (insE k m) (f i) (f j), hf i j]

/-- **The `k`-frame of a `(k-1)`-frame in the orthogonal complement of `baseVec`.** -/
def planeFrame (k m : ℕ) (q : Fin (k-1) → EuclideanSpace ℝ (Fin ((k-1)+m))) :
    Fin k → Amb (k+m) :=
  frameOf k m (baseVec k m) (fun j => insE k m (q j))

theorem orthonormal_planeFrame (k m : ℕ) (hk : 1 ≤ k)
    {q : Fin (k-1) → EuclideanSpace ℝ (Fin ((k-1)+m))} (hq : Orthonormal ℝ q) :
    Orthonormal ℝ (planeFrame k m q) :=
  orthonormal_frameOf k m hk (baseVec k m) (fun j => insE k m (q j))
    (norm_baseVec (by omega)) (orthonormal_insE_comp k m hq)
    (fun j => inner_insE_baseVec k m hk (q j))

/-! ## The two remaining geometric inputs of the incidence proof

`Work.ThomBordism.Grassmann.IncidenceReduce.incidenceFibreCohomology_of_geometry` reduces the
target to (a) the bijectivity of the two restrictions to the band and (b) the cohomology of the
upper half.  These are the two statements below.

* `IncidenceRestrictionsIso`: the band `upSet ∩ downSet` is trivialised
  (`IncidenceBandTriv.bandTrivHomeo`, as `fibreVec × Band`) and the annulus computation
  (`IncidenceAnnulus.annulusPuncturedCohomology`) gives the range `i ≤ k+m-3`.
* `upSetCohomologyIso`: `upSet ≃ₕ fibreVec` (`UpSetRetract`), `fibreVec ≃ₜ ℝ_{>0} × planeBaseSet`
  (`FibreModel.fibreModelHomeomorph`, needs `1 ≤ m`) and `planeBaseSet ≃ₜ OG (k-1) m`
  (`fibreBaseHomeomorph`, whose missing half is `OmegaFunSurjectiveOn`).

The `k = 1` and `m = 0` edge cases are separate: for `k = 1` the fibre over `baseVec` is two points
and `OG 0 m` is a point, so both sides of `upSetCohomologyIso` vanish in degrees `≥ 1` (they must be
handled by `H^j`-vanishing rather than by the homeomorphism).
-/

/-! ## The fibre over `baseVec` as `(0,∞) × planeBaseSet`, for `m = 0`

`FibreModel.fibreModelHomeomorph` proves `fibreVec k m ≃ₜ (0,∞) × planeBaseSet k m` under the
hypothesis `1 ≤ m`; the only use of that hypothesis is that it implies `baseVec k m ≠ 0`, which also
holds when `m = 0` and `1 ≤ k`.  The same proof therefore gives the model as soon as `k + m ≠ 0`,
which is what the `m = 0` edge case of the incidence statement needs.
-/

theorem baseVec_ne_zero' {k m : ℕ} (h : k + m ≠ 0) : baseVec k m ≠ 0 := by
  intro h0
  have := norm_baseVec h
  rw [h0, norm_zero] at this
  exact one_ne_zero this.symm

theorem smul_baseVec_ne_zero' {k m : ℕ} (h : k + m ≠ 0) {c : ℝ} (hc : 0 < c) :
    c • baseVec k m ≠ 0 :=
  smul_ne_zero (ne_of_gt hc) (baseVec_ne_zero' h)

/-- `baseVec` lies in the plane of a point of the fibre. -/
theorem memPlane_baseVec_of_mem_fibreVec' {k m : ℕ} (h : k + m ≠ 0) {x : ↥(incZero k m)}
    (hx : x ∈ fibreVec k m) : memPlane x.1.1 (baseVec k m) := by
  obtain ⟨f, hf, hw⟩ := evalVec_memPlane x.1
  refine ⟨f, hf, ?_⟩
  have hn : 0 < ‖evalVec x.1‖ :=
    norm_pos_iff.mpr (evalVec_ne_zero_of_mem_zeroComplement _ x.2)
  have hsm : evalVec x.1 = ‖evalVec x.1‖ • baseVec k m := evalVec_eq_smul_baseVec hx
  have hpos : (‖evalVec x.1‖)⁻¹ • evalVec x.1 = baseVec k m := by
    rw [hsm, norm_smul, Real.norm_eq_abs, abs_of_pos hn, norm_baseVec h, mul_one]
    rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hn), one_smul]
  rw [← hpos]
  exact Submodule.smul_mem _ _ hw



/-- **The fibre over `baseVec` is `(0,∞) × {planes containing baseVec}`.** -/
def fibreModelMap' (h : k + m ≠ 0) (x : ↥(fibreVec k m)) :
    {c : ℝ // 0 < c} × ↥(planeBaseSet k m) :=
  (fibreNormMap x, ⟨x.1.1.1, memPlane_baseVec_of_mem_fibreVec' h x.2⟩)

/-- The inverse of `fibreModelMap'`: put the plane `P` together with the vector `c • baseVec`. -/
def fibreModelInv' (h : k + m ≠ 0) (q : {c : ℝ // 0 < c} × ↥(planeBaseSet k m)) : ↥(fibreVec k m) :=
  ⟨toE q.2.1 (q.1.1 • baseVec k m) (smul_baseVec_ne_zero' h q.1.2)
      (memPlane_smul_baseVec_of_mem_planeBaseSet q.2.2), by
    show dirVec (toE q.2.1 (q.1.1 • baseVec k m) _ _) = baseVec k m
    rw [dirVec, evalVec_toE, norm_smul, Real.norm_eq_abs, abs_of_pos q.1.2,
      norm_baseVec h, mul_one, smul_smul, inv_mul_cancel₀ (ne_of_gt q.1.2), one_smul]⟩

theorem fibreModelInvMap' (h : k + m ≠ 0) (x : ↥(fibreVec k m)) :
    fibreModelInv' h (fibreModelMap' h x) = x := by
  refine Subtype.ext ?_
  show toE x.1.1.1 (‖evalVec x.1.1‖ • baseVec k m)
    (smul_baseVec_ne_zero' h (norm_pos_iff.mpr
      (evalVec_ne_zero_of_mem_zeroComplement _ x.1.2)))
    (memPlane_smul_baseVec_of_mem_planeBaseSet (memPlane_baseVec_of_mem_fibreVec' h x.2))
    = (x : ↥(incZero k m))
  exact (toE_congr rfl (evalVec_eq_smul_baseVec x.2).symm _ _
      (evalVec_ne_zero_of_mem_zeroComplement _ x.1.2) (evalVec_memPlane _)).trans
    (toE_self (x : ↥(incZero k m)))

theorem fibreModelMapInv' (h : k + m ≠ 0) (q : {c : ℝ // 0 < c} × ↥(planeBaseSet k m)) :
    fibreModelMap' h (fibreModelInv' h q) = q := by
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · show ‖evalVec (toE q.2.1 (q.1.1 • baseVec k m) (smul_baseVec_ne_zero' h q.1.2)
        (memPlane_smul_baseVec_of_mem_planeBaseSet q.2.2)).1‖ = q.1.1
    rw [evalVec_toE, norm_smul, Real.norm_eq_abs, abs_of_pos q.1.2,
      norm_baseVec h, mul_one]
  · rfl


theorem continuousFibreModelMap' (h : k + m ≠ 0) :
    Continuous fun x : ↥(fibreVec k m) => fibreModelMap' h x := by
  have h1 : Continuous fun x : ↥(fibreVec k m) => (x : ↥(incZero k m)) := continuous_subtype_val
  have h2 : Continuous fun z : ↥(incZero k m) => (z : (tautologicalBundle k m).TotalSpace) :=
    continuous_subtype_val
  have h3 : Continuous fun x : ↥(fibreVec k m) => x.1.1 := h2.comp h1
  have h4 : Continuous fun x : ↥(fibreVec k m) =>
      (⟨x.1.1.1, memPlane_baseVec_of_mem_fibreVec' h x.2⟩ : ↥(planeBaseSet k m)) :=
    Continuous.subtype_mk
      ((VectorBundleCore.continuous_proj (tautologicalBundle k m)).comp h3) _
  exact (continuous_fibreNormMap (k := k) (m := m)).prodMk h4

theorem continuousFibreModelInv' (h : k + m ≠ 0) :
    Continuous fun q : {c : ℝ // 0 < c} × ↥(planeBaseSet k m) => fibreModelInv' h q := by
  refine Continuous.subtype_mk ?_ _
  have hfst : Continuous fun q : {c : ℝ // 0 < c} × ↥(planeBaseSet k m) => q.1 := continuous_fst
  have hsnd : Continuous fun q : {c : ℝ // 0 < c} × ↥(planeBaseSet k m) => q.2 := continuous_snd
  have hproj : Continuous fun q : {c : ℝ // 0 < c} × ↥(planeBaseSet k m) => (q.2.1 : OG k m) :=
    continuous_subtype_val.comp hsnd
  have hval : Continuous fun q : {c : ℝ // 0 < c} × ↥(planeBaseSet k m) => q.1.1 :=
    continuous_subtype_val.comp hfst
  have hconst : Continuous fun _ : {c : ℝ // 0 < c} × ↥(planeBaseSet k m) => baseVec k m :=
    continuous_const
  have hbase : Continuous fun q : {c : ℝ // 0 < c} × ↥(planeBaseSet k m) =>
      ((q.2.1 : OG k m), q.1.1 • baseVec k m) := hproj.prodMk (hval.smul hconst)
  have hmem : ∀ q : {c : ℝ // 0 < c} × ↥(planeBaseSet k m),
      ((q.2.1 : OG k m), q.1.1 • baseVec k m) ∈
        {q : OG k m × Amb (k+m) | q.2 ≠ 0 ∧ memPlane q.1 q.2} :=
    fun q => ⟨smul_baseVec_ne_zero' h q.1.2, memPlane_smul_baseVec_of_mem_planeBaseSet q.2.2⟩
  have hcont : Continuous fun q : {c : ℝ // 0 < c} × ↥(planeBaseSet k m) =>
      mkTotal q.2.1 (toECoordAt ((tautologicalBundle k m).indexAt q.2.1) q.2.1
        (q.1.1 • baseVec k m)) :=
    continuousOn_toE_underlying.comp_continuous hbase hmem
  refine (hcont.subtype_mk fun q => ?_).congr fun q => ?_
  · show toECoordAt ((tautologicalBundle k m).indexAt q.2.1) q.2.1 (q.1.1 • baseVec k m) ≠ 0
    exact toECoordAt_ne_zero _ _ ((tautologicalBundle k m).mem_baseSet_at _) _
      (smul_baseVec_ne_zero' h q.1.2) (memPlane_smul_baseVec_of_mem_planeBaseSet q.2.2)
  · rfl

/-- **The homeomorphism `fibreVec k m ≃ (0,∞) × planeBaseSet k m`.** -/
noncomputable def fibreModelHomeomorphNeZero (h : k + m ≠ 0) :
    ↥(fibreVec k m) ≃ₜ {c : ℝ // 0 < c} × ↥(planeBaseSet k m) where
  toEquiv :=
    { toFun := fibreModelMap' h
      invFun := fibreModelInv' h
      left_inv := fibreModelInvMap' h
      right_inv := fibreModelMapInv' h }
  continuous_toFun := continuousFibreModelMap' h
  continuous_invFun := continuousFibreModelInv' h


/-! ## The cohomology of the upper half is that of the plane-base set

`upSet k m` is homotopy equivalent to `fibreVec k m` (`UpSetRetract`), the fibre is
`(0,∞) × planeBaseSet k m` (the fibre model, valid for `k + m ≠ 0`) and `(0,∞)` is contractible.
Hence `H^j(upSet k m) ≅ H^j(planeBaseSet k m)`.  For `k ≥ 2` the plane-base set is `≃ₜ OG (k-1) m`
(`OCPlaneHomeo`); for `k = 1` both `planeBaseSet 1 m` (two points) and `OG 0 m` (one point) have
vanishing cohomology in positive degrees.
-/

/-- **`(0,∞)` is contractible**: it is a nonempty convex subset of `ℝ`. -/
theorem contractibleSpace_posReal : ContractibleSpace {c : ℝ // 0 < c} :=
  (convex_Ioi (0 : ℝ)).contractibleSpace ⟨1, by norm_num⟩

/-- The fibre model with the hypothesis weakened to `k + m ≠ 0`. -/
theorem fibreModelHomeomorphNeZero' (k m : ℕ) (h : k + m ≠ 0) :
    Nonempty (↥(fibreVec k m) ≃ₜ {c : ℝ // 0 < c} × ↥(planeBaseSet k m)) :=
  ⟨fibreModelHomeomorphNeZero h⟩

/-- **`OG 0 m` is a point**: the only `0`-frame is the empty one, and `SO(0)` is trivial. -/
theorem subsingleton_OG_zero (m : ℕ) : Subsingleton (OG 0 m) := by
  refine ⟨fun P Q => ?_⟩
  obtain ⟨f, rfl⟩ := Quotient.exists_rep P
  obtain ⟨g, rfl⟩ := Quotient.exists_rep Q
  have hfg : f = g := Subtype.ext (funext fun i => i.elim0)
  rw [hfg]

/-- The positive-degree cohomology of `OG 0 m` vanishes (it is a point). -/
theorem isZero_cohomology_OG_zero (m j : ℕ) (hj : 1 ≤ j) :
    IsZero (Work.Cohomology.singularCohomology ℤ j (TopCat.of (OG 0 m))) := by
  haveI : Subsingleton (OG 0 m) := subsingleton_OG_zero m
  haveI : ContractibleSpace (OG 0 m) := inferInstance
  have h := Work.Cohomology.contractible ℤ (TopCat.of (OG 0 m)) (j - 1)
  rwa [Nat.sub_add_cancel hj] at h

/-- **`planeBaseSet 1 m` has at most two points.**  A `1`-frame is a unit vector `v`; if `baseVec`
lies in its span then `baseVec = c • v` with `|c| = 1`, so `v = ±baseVec`, and a frame of `Fin 1` is
determined by its single vector. -/
theorem finite_planeBaseSet_one (m : ℕ) : (planeBaseSet 1 m).Finite := by
  have hne : 1 + m ≠ 0 := by omega
  have hu : ‖baseVec 1 m‖ = 1 := norm_baseVec hne
  have horth1 : Orthonormal ℝ (fun _ : Fin 1 => baseVec 1 m) := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [show i = j from Fin.ext (by have := i.isLt; have := j.isLt; omega), if_pos rfl,
      real_inner_self_eq_norm_sq, hu]
    norm_num
  have horth2 : Orthonormal ℝ (fun _ : Fin 1 => (-1 : ℝ) • baseVec 1 m) := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [show i = j from Fin.ext (by have := i.isLt; have := j.isLt; omega), if_pos rfl,
      real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs, abs_of_neg (by norm_num), hu,
      mul_one]
    norm_num
  let f₁ : Stiefel 1 m := ⟨fun _ : Fin 1 => baseVec 1 m, horth1⟩
  let f₂ : Stiefel 1 m := ⟨fun _ : Fin 1 => (-1 : ℝ) • baseVec 1 m, horth2⟩
  have hsub : planeBaseSet 1 m ⊆ ({Quotient.mk'' f₁, Quotient.mk'' f₂} : Set (OG 1 m)) := by
    rintro P ⟨f, hf, hw⟩
    -- `baseVec` lies in the span of the single vector `f.1 0`
    have hrange : Set.range (f.1 : Fin 1 → Amb (1 + m)) = {f.1 0} := by
      ext v
      constructor
      · rintro ⟨i, rfl⟩
        rw [Subsingleton.elim i 0]; exact rfl
      · rintro rfl
        exact ⟨0, rfl⟩
    rw [hrange, Submodule.mem_span_singleton] at hw
    obtain ⟨c, hc⟩ := hw
    -- `|c| = 1`
    have hv : ‖f.1 0‖ = 1 := f.2.norm_eq_one 0
    have hcabs : |c| = 1 := by
      have h2 := congrArg norm hc
      rw [norm_smul, Real.norm_eq_abs, hv, mul_one, hu] at h2
      exact h2
    have hcases : c = 1 ∨ c = -1 := (abs_eq zero_le_one).mp hcabs
    have hf0 : f.1 0 = baseVec 1 m ∨ f.1 0 = (-1:ℝ) • baseVec 1 m := by
      rcases hcases with rfl | rfl
      · left; simpa using hc
      · right
        rw [neg_one_smul] at hc
        rw [neg_one_smul]
        exact neg_eq_iff_eq_neg.mp hc
    have hfeq : f = f₁ ∨ f = f₂ := by
      rcases hf0 with h0 | h0
      · left
        refine Subtype.ext (funext fun i => ?_)
        show f.1 i = baseVec 1 m
        rw [show i = 0 from Fin.ext (by have := i.isLt; omega), h0]
      · right
        refine Subtype.ext (funext fun i => ?_)
        show f.1 i = (-1 : ℝ) • baseVec 1 m
        rw [show i = 0 from Fin.ext (by have := i.isLt; omega), h0]
    rcases hfeq with hfeq | hfeq
    · rw [show P = Quotient.mk'' f₁ from by rw [← hf, hfeq]]
      exact Set.mem_insert _ _
    · rw [show P = Quotient.mk'' f₂ from by rw [← hf, hfeq]]
      exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  exact ((Set.finite_singleton (Quotient.mk'' f₂)).insert (Quotient.mk'' f₁)).subset hsub

/-- **`planeBaseSet 1 m` is discrete**: it is finite and `OG 1 m` is Hausdorff. -/
theorem discreteTopology_planeBaseSet_one (m : ℕ) :
    DiscreteTopology ↥(planeBaseSet 1 m) :=
  discreteTopology_of_noAccPts fun _ _ hacc => Set.Infinite.of_accPt hacc (finite_planeBaseSet_one m)

/-- The positive-degree cohomology of `planeBaseSet 1 m` vanishes (two-point discrete space). -/
theorem isZero_cohomology_planeBaseSet_one (m j : ℕ) (hj : 1 ≤ j) :
    IsZero (Work.Cohomology.singularCohomology ℤ j (TopCat.of ↥(planeBaseSet 1 m))) := by
  haveI : DiscreteTopology ↥(planeBaseSet 1 m) := discreteTopology_planeBaseSet_one m
  haveI : TotallyDisconnectedSpace ↥(planeBaseSet 1 m) := inferInstance
  have h := Work.Cohomology.totallyDisconnected ℤ (TopCat.of ↥(planeBaseSet 1 m)) (j - 1)
  rwa [Nat.sub_add_cancel hj] at h

/-- **`H^j(upSet k m) ≅ H^j(planeBaseSet k m)`**, given the fibre model. -/
theorem upSetPlaneBaseSetCohomologyIso (k m j : ℕ) (hk : 1 ≤ k)
    (hfib : Nonempty (↥(fibreVec k m) ≃ₜ {c : ℝ // 0 < c} × ↥(planeBaseSet k m))) :
    Nonempty (Work.Cohomology.singularCohomology ℤ j (TopCat.of ↥(upSet k m)) ≅
      Work.Cohomology.singularCohomology ℤ j (TopCat.of ↥(planeBaseSet k m))) := by
  haveI : ContractibleSpace {c : ℝ // 0 < c} := contractibleSpace_posReal
  obtain ⟨e₁⟩ := nonempty_homotopyEquiv_upSet_fibreVec (k := k) (m := m) hk
  obtain ⟨i₁⟩ := nonempty_singularCohomology_iso_of_homotopyEquiv
    (X := TopCat.of ↥(upSet k m)) (Y := TopCat.of ↥(fibreVec k m)) e₁ j
  obtain ⟨h⟩ := hfib
  obtain ⟨i₂⟩ := nonempty_singularCohomology_iso_of_homotopyEquiv
    (X := TopCat.of ↥(fibreVec k m))
    (Y := TopCat.of ({c : ℝ // 0 < c} × ↥(planeBaseSet k m))) h.toHomotopyEquiv j
  obtain ⟨i₃⟩ := Work.Cohomology.cohomology_prod_contractible ℤ
    (TopCat.of {c : ℝ // 0 < c}) (TopCat.of ↥(planeBaseSet k m)) j
  exact ⟨i₁ ≪≫ i₂ ≪≫ i₃⟩

/-- **The cohomology of the upper half is that of the fibre.** -/
theorem upSetCohomologyIso (k m j : ℕ) (hk : 1 ≤ k) (hj : 1 ≤ j) :
    Nonempty (Work.Cohomology.singularCohomology ℤ j (TopCat.of (upSet k m)) ≅
      Work.Cohomology.singularCohomology ℤ j (TopCat.of (OG (k - 1) m))) := by
  have hfib : Nonempty (↥(fibreVec k m) ≃ₜ {c : ℝ // 0 < c} × ↥(planeBaseSet k m)) := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      exact fibreModelHomeomorphNeZero' k 0 (by omega)
    · exact ⟨fibreModelHomeomorph hm⟩
  obtain ⟨e⟩ := upSetPlaneBaseSetCohomologyIso k m j hk hfib
  by_cases h2 : 2 ≤ k
  · obtain ⟨h⟩ := OCPlaneHomeo k m h2
    obtain ⟨e₂⟩ := nonempty_singularCohomology_iso_of_homotopyEquiv
      (X := TopCat.of ↥(planeBaseSet k m)) (Y := TopCat.of (OG (k - 1) m)) h.toHomotopyEquiv j
    exact ⟨e ≪≫ e₂⟩
  · have hk1 : k = 1 := by omega
    subst hk1
    exact ⟨e ≪≫ IsZero.iso (isZero_cohomology_planeBaseSet_one m j hj)
      (isZero_cohomology_OG_zero m j hj)⟩

/-- **The restrictions to the band are isomorphisms** (the two inputs `hU`, `hV` of
`incidenceFibreCohomology_of_geometry`): they are the two lemmas `restU_band_bijective` and
`restV_band_bijective` of `IncidenceBandRestrict`. -/
theorem IncidenceRestrictionsIso (k m : ℕ) (hk : 1 ≤ k) :
    (∀ i, i + 2 ≤ k + m - 1 →
      Function.Bijective (restU (X := TopCat.of (zeroComp k m)) (upSet k m) (downSet k m) i)) ∧
    (∀ i, i + 2 ≤ k + m - 1 →
      Function.Bijective (restV (X := TopCat.of (zeroComp k m)) (upSet k m) (downSet k m) i)) :=
  ⟨fun i hi => restU_band_bijective k m i hk hi,
    fun i hi => restV_band_bijective k m i hk hi⟩



/-- **The target.**  For `1 ≤ k`, `1 ≤ j` and `j ≤ k + m - 3` the rational cohomology of the
sphere bundle of the tautological oriented `k`-plane bundle over `G̃r_k(ℝ^{k+m})` agrees with that
of `G̃r_{k-1}(ℝ^{k+m-1}) = OG (k-1) m`.

The proof is the incidence fibration: `zeroComplement (tautologicalBundle k m)` retracts onto each
half of the two-hemisphere cover with common band, Mayer–Vietoris extracts
`H^j(zeroComplement) ≅ H^j(upSet)`, and `upSet` is cohomologically the fibre `OG (k-1) m`. -/
theorem incidenceFibreCohomologyRat (k m j : ℕ) (hk : 1 ≤ k) (hj1 : 1 ≤ j) (hj : j ≤ k + m - 3) :
    Nonempty (Work.SignatureBordism.ratCohomology j (Work.ThomBordism.Grassmann.sset (Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k m))) ≃ₗ[ℚ]
      Work.SignatureBordism.ratCohomology j (Work.ThomBordism.Grassmann.sset (Work.ThomBordism.Grassmann.OG (k - 1) m))) := by
  obtain ⟨hU, hV⟩ := IncidenceRestrictionsIso k m hk
  obtain ⟨e⟩ := incidenceFibreCohomology_of_geometry k m j hk hj1 hj hU hV
    (upSetCohomologyIso k m j hk hj1)
  exact ⟨LinearEquiv.baseChange ℤ ℚ _ _ e⟩

end

end Work.ThomBordism.Grassmann
