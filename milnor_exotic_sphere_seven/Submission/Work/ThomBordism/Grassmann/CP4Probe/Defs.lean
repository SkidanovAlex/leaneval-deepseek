import Mathlib
import Submission.Work.ThomBordism.Grassmann.probeCoords
import Submission.Work.ThomBordism.Grassmann.probeRot
import Submission.Work.ThomBordism.Grassmann.probeMap
import Submission.Work.Projective.Basic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

namespace Work.ThomBordism.Grassmann

open Work.TangentClasses Work.Projective

noncomputable section

/-! ## The two spaces -/

/-- The complex `5`-space `ℂ⁵`, as a real inner product space. -/
abbrev E5 : Type := EuclideanSpace ℂ (Fin 5)

/-- The complex `2`-space `ℂ²`, as a real inner product space. -/
abbrev E2 : Type := EuclideanSpace ℂ (Fin 2)

/-- The index of the `i`-th of the first three coordinates of `Fin 5`. -/
def idx3 (i : Fin 3) : Fin 5 := ⟨i.val, by have := i.isLt; omega⟩

/-- The index of the `i`-th of the last two coordinates of `Fin 5`. -/
def idx2 (i : Fin 2) : Fin 5 := ⟨3 + i.val, by have := i.isLt; omega⟩

/-- The first three coordinates of a representative of a point of `ℂP⁴`. -/
def pre3F (v : Fin 5 → ℂ) : Fin 3 → ℂ := fun i => v (idx3 i)

/-- The last two coordinates of a representative of a point of `ℂP⁴`. -/
def suf2F (v : Fin 5 → ℂ) : Fin 2 → ℂ := fun i => v (idx2 i)

/-- A representative of a point of `ℂP⁴`, as an element of `ℂ⁵`. -/
def cfOf (v : Fin 5 → ℂ) : E5 := WithLp.toLp 2 v

/-- The unit vector in the direction of a nonzero representative. -/
def cfUnit (v : Fin 5 → ℂ) : E5 := (‖cfOf v‖)⁻¹ • cfOf v

/-! ## Basic lemmas on the representatives -/

theorem cfOf_smul (c : ℂ) (v : Fin 5 → ℂ) : cfOf (c • v) = c • cfOf v :=
  WithLp.toLp_smul 2 c v

theorem cfOf_smul_real (a : ℝ) (v : Fin 5 → ℂ) : cfOf (a • v) = a • cfOf v :=
  WithLp.toLp_smul 2 a v

theorem cfOf_ofLp (v : Fin 5 → ℂ) : (cfOf v).ofLp = v := rfl

theorem cfOf_ne_zero {v : Fin 5 → ℂ} (hv : v ≠ 0) : cfOf v ≠ 0 := by
  intro h
  exact hv (by simpa [cfOf] using congrArg WithLp.ofLp h)

theorem cfUnit_norm {v : Fin 5 → ℂ} (hv : v ≠ 0) : ‖cfUnit v‖ = 1 := by
  have hne : ‖cfOf v‖ ≠ 0 := norm_ne_zero_iff.mpr (cfOf_ne_zero hv)
  rw [cfUnit, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
    inv_mul_cancel₀ hne]

theorem cfUnit_ne_zero {v : Fin 5 → ℂ} (hv : v ≠ 0) : cfUnit v ≠ 0 := by
  intro h
  have := cfUnit_norm hv
  rw [h, norm_zero] at this
  exact one_ne_zero this.symm

theorem cfUnit_smul_pos {v : Fin 5 → ℂ} (hv : v ≠ 0) {a : ℝ} (ha : 0 < a) :
    cfUnit (a • v) = cfUnit v := by
  have hne : ‖cfOf v‖ ≠ 0 := norm_ne_zero_iff.mpr (cfOf_ne_zero hv)
  have hcoe : cfOf (a • v) = a • cfOf v := cfOf_smul_real a v
  have hnorm : ‖a • cfOf v‖ = a * ‖cfOf v‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
  rw [cfUnit, cfUnit, hcoe, hnorm, smul_smul]
  have hscal : (a * ‖cfOf v‖)⁻¹ * a = ‖cfOf v‖⁻¹ := by
    rw [mul_inv, mul_assoc, mul_comm (‖cfOf v‖)⁻¹ a, ← mul_assoc,
      inv_mul_cancel₀ (ne_of_gt ha), one_mul]
  rw [hscal]

theorem cfUnit_smul_unit {v : Fin 5 → ℂ} (hv : v ≠ 0) {μ : ℂ} (hμ : ‖μ‖ = 1) :
    cfUnit (μ • v) = μ • cfUnit v := by
  have hne : ‖cfOf v‖ ≠ 0 := norm_ne_zero_iff.mpr (cfOf_ne_zero hv)
  have hcoe : cfOf (μ • v) = μ • cfOf v := cfOf_smul μ v
  have hnorm : ‖μ • cfOf v‖ = ‖cfOf v‖ := by rw [norm_smul, hμ, one_mul]
  rw [cfUnit, cfUnit, hcoe, hnorm, smul_comm]

theorem cfUnit_smul {v : Fin 5 → ℂ} (hv : v ≠ 0) {c : ℂ} (hc : c ≠ 0) :
    cfUnit (c • v) = (c / ((‖c‖ : ℝ) : ℂ)) • cfUnit v := by
  have hc0 : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  have hcn : (((‖c‖ : ℝ) : ℂ)) ≠ 0 := by simpa using hc0
  have hμ : ‖c / ((‖c‖ : ℝ) : ℂ)‖ = 1 := by
    rw [norm_div]
    have h2 : ‖((‖c‖ : ℝ) : ℂ)‖ = ‖c‖ := by simp
    rw [h2, div_self hc0]
  have hμ0 : c / ((‖c‖ : ℝ) : ℂ) ≠ 0 := by
    intro h; rw [h] at hμ; simp at hμ
  have hsplit : c • v = ((‖c‖ : ℝ)) • ((c / ((‖c‖ : ℝ) : ℂ)) • v) := by
    rw [← smul_assoc, Complex.real_smul]
    congr 1
    exact (mul_div_cancel₀ c hcn).symm
  rw [hsplit, cfUnit_smul_pos (v := (c / ((‖c‖ : ℝ) : ℂ)) • v) (smul_ne_zero hμ0 hv)
    (norm_pos_iff.mpr hc), cfUnit_smul_unit hv hμ]

/-! ## Sums of standard basis vectors -/

/-- A vector of `ℂⁿ` is the sum of its coordinates times the standard basis vectors. -/
theorem sum_single_eq_c (n : ℕ) (x : EuclideanSpace ℂ (Fin n)) :
    (∑ i : Fin n, EuclideanSpace.single (𝕜 := ℂ) i (x.ofLp i)) = x := by
  rw [WithLp.ext_iff]
  funext j
  rw [WithLp.ofLp_sum, Finset.sum_apply, Finset.sum_eq_single j]
  · rw [PiLp.single_apply, if_pos rfl]
  · intro i _ hi
    rw [PiLp.single_apply, if_neg (fun h : j = i => hi h.symm)]
  · intro h; exact absurd (Finset.mem_univ j) h

/-! ## The two projections of `ℂ⁵` -/

/-- The projection `ℂ⁵ → ℂ³` onto the first three coordinates, as a `ℂ`-linear map. -/
noncomputable def preC : E5 →L[ℂ] E3 :=
  ∑ i : Fin 3, (EuclideanSpace.proj (𝕜 := ℂ) (idx3 i)).smulRight
    (EuclideanSpace.single (𝕜 := ℂ) i 1)

/-- The projection `ℂ⁵ → ℂ²` onto the last two coordinates, as a `ℂ`-linear map. -/
noncomputable def sufC : E5 →L[ℂ] E2 :=
  ∑ i : Fin 2, (EuclideanSpace.proj (𝕜 := ℂ) (idx2 i)).smulRight
    (EuclideanSpace.single (𝕜 := ℂ) i 1)

/-- The complex scalar action on a standard basis vector. -/
theorem smul_single_eq {n : ℕ} (i : Fin n) (c : ℂ) :
    c • (EuclideanSpace.single (𝕜 := ℂ) i 1 : EuclideanSpace ℂ (Fin n))
      = EuclideanSpace.single (𝕜 := ℂ) i c := by
  ext j; simp [PiLp.single_apply]

theorem preC_single (x : E5) :
    preC x = ∑ i : Fin 3, EuclideanSpace.single (𝕜 := ℂ) i (x.ofLp (idx3 i)) := by
  rw [preC]
  simp only [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [ContinuousLinearMap.smulRight_apply]
  rw [show (EuclideanSpace.proj (𝕜 := ℂ) (idx3 i)) x = x.ofLp (idx3 i) from rfl,
    smul_single_eq]

theorem sufC_single (x : E5) :
    sufC x = ∑ i : Fin 2, EuclideanSpace.single (𝕜 := ℂ) i (x.ofLp (idx2 i)) := by
  rw [sufC]
  simp only [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [ContinuousLinearMap.smulRight_apply]
  rw [show (EuclideanSpace.proj (𝕜 := ℂ) (idx2 i)) x = x.ofLp (idx2 i) from rfl,
    smul_single_eq]

theorem preC_cfOf (v : Fin 5 → ℂ) : preC (cfOf v) = cxOf (pre3F v) := by
  rw [preC_single, ← sum_single_eq_c 3 (cxOf (pre3F v))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [cfOf_ofLp]
  rfl

theorem sufC_cfOf (v : Fin 5 → ℂ) :
    sufC (cfOf v) = WithLp.toLp 2 (suf2F v) := by
  rw [sufC_single, ← sum_single_eq_c 2 (WithLp.toLp 2 (suf2F v))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [cfOf_ofLp]
  rfl


/-! ## The embedding `ℂ⁵ → ℝ¹⁰` -/

/-- The index of the `a`-th real coordinate of the `i`-th of the last two complex coordinates. -/
def idxB (i a : Fin 2) : Fin 10 := ⟨6 + 2 * i.val + a.val, by have := i.isLt; have := a.isLt; omega⟩

/-- The first block of the embedding: the first three complex coordinates through the `ℂ³`-probe
embedding `probeEmb 2 8 ∘ cxE` into the first six coordinates of `ℝ¹⁰`. -/
noncomputable def embA : E3 →L[ℝ] Amb 10 :=
  (probeEmb 2 8 (by norm_num) (by norm_num)).comp (cxE.toContinuousLinearEquiv : E3 →L[ℝ] Amb 6)

theorem embA_apply (u : E3) :
    embA u = probeEmb 2 8 (by norm_num) (by norm_num) (cxE u) := rfl

/-- The second block of the embedding: the last two complex coordinates realified into the last four
coordinates of `ℝ¹⁰` (`re` into the even coordinate, `im` into the odd one). -/
noncomputable def embB : E2 →L[ℝ] Amb 10 :=
  (∑ i : Fin 2, (Complex.reCLM.comp ((EuclideanSpace.proj (𝕜 := ℂ) i).restrictScalars ℝ)).smulRight
      (EuclideanSpace.single (𝕜 := ℝ) (idxB i 0) 1))
  + (∑ i : Fin 2, (Complex.imCLM.comp ((EuclideanSpace.proj (𝕜 := ℂ) i).restrictScalars ℝ)).smulRight
      (EuclideanSpace.single (𝕜 := ℝ) (idxB i 1) 1))

theorem embB_coord (z : E2) (i : Fin 2) :
    (Complex.reCLM.comp ((EuclideanSpace.proj (𝕜 := ℂ) i).restrictScalars ℝ)) z = (z.ofLp i).re :=
  rfl

theorem embB_coord' (z : E2) (i : Fin 2) :
    (Complex.imCLM.comp ((EuclideanSpace.proj (𝕜 := ℂ) i).restrictScalars ℝ)) z = (z.ofLp i).im :=
  rfl

theorem embB_apply (z : E2) :
    embB z = (∑ i : Fin 2, (z.ofLp i).re •
        (EuclideanSpace.single (𝕜 := ℝ) (idxB i 0) 1 : Amb 10))
      + (∑ i : Fin 2, (z.ofLp i).im • EuclideanSpace.single (𝕜 := ℝ) (idxB i 1) 1) := by
  rw [embB]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply]
  rfl

/-- **The embedding `ℂ⁵ → ℝ¹⁰` of the probe**: the first three coordinates through the `ℂP²`-probe
embedding, the last two coordinates realified into the last four coordinates. -/
noncomputable def emb5 : E5 →L[ℝ] Amb 10 :=
  embA.comp (preC.restrictScalars ℝ) + embB.comp (sufC.restrictScalars ℝ)

theorem emb5_apply (x : E5) : emb5 x = embA (preC x) + embB (sufC x) := rfl

/-- The frame of the complex line of a nonzero representative: the realification of `u` and of
`i u`, where `u = ‖v‖⁻¹ • v`. -/
def lineFrame (v : Fin 5 → ℂ) : Fin 2 → Amb 10 :=
  ![emb5 (cfUnit v), -emb5 (Complex.I • cfUnit v)]

@[simp] theorem lineFrame_zero (v : Fin 5 → ℂ) : lineFrame v 0 = emb5 (cfUnit v) := rfl

@[simp] theorem lineFrame_one (v : Fin 5 → ℂ) :
    lineFrame v 1 = -emb5 (Complex.I • cfUnit v) := rfl

/-! ## The inclusion `ℂP² → ℂP⁴` -/

/-- The coordinate inclusion `ℂ³ → ℂ⁵`, as a `ℂ`-linear map. -/
def padF (v : Fin 3 → ℂ) : Fin 5 → ℂ := fun i => if h : i.val < 3 then v ⟨i.val, h⟩ else 0

theorem padF_smul (c : ℂ) (v : Fin 3 → ℂ) : padF (c • v) = c • padF v := by
  funext i
  by_cases h : i.val < 3 <;> simp [padF, h]

theorem padF_add (v w : Fin 3 → ℂ) : padF (v + w) = padF v + padF w := by
  funext i
  by_cases h : i.val < 3 <;> simp [padF, h]

/-- The coordinate inclusion `ℂ³ → ℂ⁵`, as a `ℂ`-linear map. -/
def padM : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 5 → ℂ) where
  toFun := padF
  map_add' := padF_add
  map_smul' := padF_smul

theorem padM_injective : Function.Injective padM := by
  intro v w h
  funext i
  have := congrFun h (idx3 i)
  simpa [padM, padF, idx3, i.isLt] using this

theorem padF_ne_zero {v : Fin 3 → ℂ} (hv : v ≠ 0) : padF v ≠ 0 := by
  intro h
  refine hv (funext fun i => ?_)
  have := congrFun h (idx3 i)
  simpa [padF, idx3, i.isLt] using this

theorem pre3F_padF (v : Fin 3 → ℂ) : pre3F (padF v) = v := by
  funext i; simp [pre3F, padF, idx3, i.isLt]

theorem suf2F_padF (v : Fin 3 → ℂ) : suf2F (padF v) = 0 := by
  funext i; simp [suf2F, padF, idx2]

/-- The underlying function of the inclusion `ℂP² → ℂP⁴`. -/
noncomputable def iotaFun (x : CP 2) : CP 4 :=
  Projectivization.map padM padM_injective x

theorem iotaFun_mk (v : {v : Fin 3 → ℂ // v ≠ 0}) :
    iotaFun (Projectivization.mk' ℂ v)
      = Projectivization.mk ℂ (padF v.1) (padF_ne_zero v.2) := by
  show Projectivization.map padM padM_injective (Projectivization.mk' ℂ v) = _
  rw [show Projectivization.mk' ℂ v = Projectivization.mk ℂ v.1 v.2 from rfl,
    Projectivization.map_mk]
  rfl

theorem continuous_iotaFun : Continuous iotaFun := by
  have hq : Topology.IsQuotientMap (Projectivization.mk' ℂ :
      {v : Fin 3 → ℂ // v ≠ 0} → CP 2) := isQuotientMap_quotient_mk'
  rw [hq.continuous_iff]
  have hcomp : iotaFun ∘ (Projectivization.mk' ℂ : {v : Fin 3 → ℂ // v ≠ 0} → CP 2)
      = fun v => Projectivization.mk ℂ (padF v.1) (padF_ne_zero v.2) :=
    funext (fun v => iotaFun_mk v)
  rw [hcomp]
  exact continuous_quotient_mk'.comp (Continuous.subtype_mk
    ((LinearMap.continuous_of_finiteDimensional (𝕜 := ℂ) padM).comp continuous_subtype_val)
    (fun v => padF_ne_zero v.2))

/-- **The inclusion `ℂP² → ℂP⁴`** of the coordinate `ℂP²` given by the first three coordinates. -/
noncomputable def iota : C(CP 2, CP 4) := ⟨iotaFun, continuous_iotaFun⟩

theorem iota_apply_mk (v : {v : Fin 3 → ℂ // v ≠ 0}) :
    iota (Projectivization.mk' ℂ v)
      = Projectivization.mk ℂ (padF v.1) (padF_ne_zero v.2) := iotaFun_mk v

end

end Work.ThomBordism.Grassmann
