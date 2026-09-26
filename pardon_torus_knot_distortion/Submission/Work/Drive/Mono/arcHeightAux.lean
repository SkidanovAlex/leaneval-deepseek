import Mathlib
import Submission.Work.Drive.Mono.gammaArcs_exist
import Submission.Work.Drive.Mono.BoxGenE

/-!
# Auxiliary lemmas for the arc height kernel
-/

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

noncomputable section

/-- The face pair map is `2πℤ²`-periodic. -/
theorem facePairMap_period (ψ : Submission.Diffeo) (σ : Equiv.Perm (Fin 3)) (i : Fin 3)
    (p : ℝ × ℝ) (k l : ℤ) :
    facePairMap ψ σ i (p.1 + (k : ℝ) * (2 * Real.pi), p.2 + (l : ℝ) * (2 * Real.pi)) =
      facePairMap ψ σ i p := by
  simp only [facePairMap, Work.BoxShrink.Pinch.par_period]

/-- The unit vector `shiftVσ σ 1` evaluates test vectors at the coordinate `σ 2`. -/
theorem inner_shiftVσ_one' (σ : Equiv.Perm (Fin 3)) (x : R3) :
    inner ℝ (Work.BoxShrink.shiftVσ σ 1) x = x (σ 2) := by
  rw [PiLp.inner_apply]
  simp [Work.BoxShrink.shiftVσ_apply]

theorem inner_shiftVσ_one_self (σ : Equiv.Perm (Fin 3)) :
    inner ℝ (Work.BoxShrink.shiftVσ σ 1) (Work.BoxShrink.shiftVσ σ 1) = 1 := by
  rw [inner_shiftVσ_one', Work.BoxShrink.shiftVσ_apply]; simp

/-- The coordinate function `y_{σ i} ∘ par`. -/
def coordFun (ψ : Submission.Diffeo) (σ : Equiv.Perm (Fin 3)) (i : Fin 3) : ℝ × ℝ → ℝ :=
  fun q => (Work.BoxShrink.Pinch.par ψ q) (σ i)

@[simp] theorem coordFun_apply (ψ : Submission.Diffeo) (σ : Equiv.Perm (Fin 3)) (i : Fin 3)
    (q : ℝ × ℝ) : coordFun ψ σ i q = (Work.BoxShrink.Pinch.par ψ q) (σ i) := rfl

theorem contDiff_coordFun (ψ : Submission.Diffeo) (σ : Equiv.Perm (Fin 3)) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (coordFun ψ σ i) := by
  have hpar : ContDiff ℝ (⊤ : ℕ∞) (Work.BoxShrink.Pinch.par ψ) := Work.BoxShrink.Pinch.par_contDiff ψ
  have hproj : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ =>
      (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) (σ i))
        (Work.BoxShrink.Pinch.par ψ q)) :=
    (ContinuousLinearMap.contDiff (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) (σ i))).comp hpar
  exact hproj

theorem contDiffAt_coordFun (ψ : Submission.Diffeo) (σ : Equiv.Perm (Fin 3)) (i : Fin 3)
    (q : ℝ × ℝ) : ContDiffAt ℝ (⊤ : ℕ∞) (coordFun ψ σ i) q :=
  (contDiff_coordFun ψ σ i).contDiffAt

/-- The coordinate functional `v ↦ v (σ i)` on `ℝ³` as a continuous linear map. -/
def coordCLM (σ : Equiv.Perm (Fin 3)) (i : Fin 3) : R3 →L[ℝ] ℝ where
  toFun := fun v => v (σ i)
  map_add' := by intro x y; rfl
  map_smul' := by intro c x; rfl

@[simp] theorem coordCLM_apply (σ : Equiv.Perm (Fin 3)) (i : Fin 3) (v : R3) :
    coordCLM σ i v = v (σ i) := rfl

/-- The unit coordinate vector in the direction `σ i`. -/
def evec (σ : Equiv.Perm (Fin 3)) (i : Fin 3) : R3 :=
  WithLp.toLp 2 (fun m : Fin 3 => if m = σ i then (1 : ℝ) else 0)

@[simp] theorem evec_apply (σ : Equiv.Perm (Fin 3)) (i m : Fin 3) :
    evec σ i m = if m = σ i then (1 : ℝ) else 0 := rfl

theorem norm_evec (σ : Equiv.Perm (Fin 3)) (i : Fin 3) : ‖evec σ i‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  rw [Finset.sum_eq_single (σ i)]
  · simp [evec]
  · intro b _ hb; simp [evec, hb]
  · intro h; exact absurd (Finset.mem_univ (σ i)) h

theorem inner_evec (σ : Equiv.Perm (Fin 3)) (i : Fin 3) (x : R3) :
    inner ℝ (evec σ i) x = x (σ i) := by
  rw [PiLp.inner_apply]
  simp [evec]

theorem norm_smul_evec (σ : Equiv.Perm (Fin 3)) (i : Fin 3) (a : ℝ) :
    ‖a • evec σ i‖ = |a| := by
  rw [norm_smul, norm_evec, mul_one, Real.norm_eq_abs]

/-- A nonzero linear functional on `ℝ × ℝ` has kernel spanned by its Hamiltonian field
`(-φ (0,1), φ (1,0))`. -/
theorem eq_smul_of_apply_eq_zero {φ : ℝ × ℝ →L[ℝ] ℝ} (hφ : φ ≠ 0) {u : ℝ × ℝ}
    (hu : φ u = 0) : ∃ c : ℝ, u = c • (-(φ ((0:ℝ), (1:ℝ))), φ ((1:ℝ), (0:ℝ))) := by
  have hvec : u = u.1 • (((1:ℝ), (0:ℝ)) : ℝ × ℝ) + u.2 • (((0:ℝ), (1:ℝ)) : ℝ × ℝ) := by
    ext <;> simp
  have h2 : u.1 * φ ((1:ℝ), (0:ℝ)) + u.2 * φ ((0:ℝ), (1:ℝ)) = 0 := by
    have h := hu
    rw [hvec, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h
    exact h
  rcases eq_or_ne (φ ((1:ℝ), (0:ℝ))) 0 with ha | ha
  · have hb : φ ((0:ℝ), (1:ℝ)) ≠ 0 := by
      intro hb
      exact hφ (by
        rw [ContinuousLinearMap.ext_iff]
        intro v
        show φ v = 0
        have hv : v = v.1 • (((1:ℝ), (0:ℝ)) : ℝ × ℝ) + v.2 • (((0:ℝ), (1:ℝ)) : ℝ × ℝ) := by
          ext <;> simp
        rw [hv, map_add, map_smul, map_smul, ha, hb]
        simp)
    have hu2 : u.2 = 0 := by
      have h := h2; rw [ha, mul_zero, zero_add] at h
      exact (mul_eq_zero.mp h).resolve_right hb
    refine ⟨-u.1 / φ ((0:ℝ), (1:ℝ)), ?_⟩
    rw [Prod.ext_iff]
    refine ⟨?_, ?_⟩
    · simp only [Prod.smul_fst, smul_eq_mul, Prod.snd_neg]
      field_simp
    · simp only [Prod.smul_snd, smul_eq_mul, Prod.snd_neg]
      rw [hu2, ha, mul_zero]
  · refine ⟨u.2 / φ ((1:ℝ), (0:ℝ)), ?_⟩
    rw [Prod.ext_iff]
    refine ⟨?_, ?_⟩
    · simp only [Prod.smul_fst, smul_eq_mul, Prod.fst_neg]
      have h1 : u.1 * φ ((1:ℝ), (0:ℝ)) = -(u.2 * φ ((0:ℝ), (1:ℝ))) := by linarith
      field_simp
      linarith
    · simp only [Prod.smul_snd, smul_eq_mul]
      field_simp

/-- `φ v = v.1 * φ (1,0) + v.2 * φ (0,1)`. -/
theorem linCoord_apply_pair (φ : ℝ × ℝ →L[ℝ] ℝ) (v : ℝ × ℝ) :
    φ v = v.1 * φ ((1:ℝ),(0:ℝ)) + v.2 * φ ((0:ℝ),(1:ℝ)) := by
  have hv : v = v.1 • (((1:ℝ),(0:ℝ)) : ℝ × ℝ) + v.2 • (((0:ℝ), (1:ℝ)) : ℝ × ℝ) := by
    ext <;> simp
  have h1 : φ (v.1 • (((1:ℝ),(0:ℝ)) : ℝ × ℝ) + v.2 • (((0:ℝ), (1:ℝ)) : ℝ × ℝ))
      = v.1 * φ ((1:ℝ),(0:ℝ)) + v.2 * φ ((0:ℝ),(1:ℝ)) := by
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  exact (congrArg φ hv).trans h1

/-- The derivative of the face pair map is the pair of the derivatives of its coordinates. -/
theorem fderiv_facePairMap (ψ : Submission.Diffeo) (σ : Equiv.Perm (Fin 3)) (i : Fin 3)
    (q : ℝ × ℝ) :
    fderiv ℝ (facePairMap ψ σ i) q =
      (fderiv ℝ (coordFun ψ σ i) q).prod (fderiv ℝ (coordFun ψ σ 2) q) := by
  have h1 : DifferentiableAt ℝ (coordFun ψ σ i) q :=
    (contDiffAt_coordFun ψ σ i q).differentiableAt (by simp)
  have h2 : DifferentiableAt ℝ (coordFun ψ σ 2) q :=
    (contDiffAt_coordFun ψ σ 2 q).differentiableAt (by simp)
  exact h1.fderiv_prodMk h2

/-- At a regular crossing point the `σ i`-coordinate functional is nonzero. -/
theorem fderiv_coordFun_ne_zero_of_invertible (ψ : Submission.Diffeo)
    (σ : Equiv.Perm (Fin 3)) (i : Fin 3) {p : ℝ × ℝ}
    (hinv : (fderiv ℝ (facePairMap ψ σ i) p).IsInvertible) :
    fderiv ℝ (coordFun ψ σ i) p ≠ 0 := by
  obtain ⟨A, hA⟩ := hinv
  intro hzero
  have hv : fderiv ℝ (facePairMap ψ σ i) p (A.symm ((1:ℝ),(0:ℝ))) = ((1:ℝ),(0:ℝ)) := by
    rw [← hA]; simp
  have h1 : (fderiv ℝ (coordFun ψ σ i) p) (A.symm ((1:ℝ),(0:ℝ))) = 1 := by
    have h := congrArg Prod.fst hv
    rwa [fderiv_facePairMap ψ σ i p, ContinuousLinearMap.prod_apply] at h
  rw [hzero] at h1
  simp at h1

/-- The Hamiltonian field of the `σ i`-coordinate is killed by its own derivative. -/
theorem fderiv_coordFun_self_faceTangent (ψ : Submission.Diffeo) (σ : Equiv.Perm (Fin 3))
    (i : Fin 3) (q : ℝ × ℝ) :
    fderiv ℝ (coordFun ψ σ i) q (faceTangent ψ σ i q) = 0 := by
  have h : faceTangent ψ σ i q = (-(fderiv ℝ (coordFun ψ σ i) q ((0:ℝ),(1:ℝ))),
      fderiv ℝ (coordFun ψ σ i) q ((1:ℝ),(0:ℝ))) := rfl
  rw [h, linCoord_apply_pair]
  ring

/-- The derivative of the `σ j`-coordinate along the Hamiltonian field of `σ i` is the vertical
tangent determinant. -/
theorem fderiv_coordFun_faceTangent (ψ : Submission.Diffeo) (σ : Equiv.Perm (Fin 3))
    (i j : Fin 3) (q : ℝ × ℝ) :
    fderiv ℝ (coordFun ψ σ j) q (faceTangent ψ σ i q) = faceVertDet ψ σ i j q := by
  have h : faceTangent ψ σ i q = (-(fderiv ℝ (coordFun ψ σ i) q ((0:ℝ),(1:ℝ))),
      fderiv ℝ (coordFun ψ σ i) q ((1:ℝ),(0:ℝ))) := rfl
  have hz : faceVertDet ψ σ i j q =
      (fderiv ℝ (coordFun ψ σ i) q ((1:ℝ),(0:ℝ))) *
        (fderiv ℝ (coordFun ψ σ j) q ((0:ℝ),(1:ℝ))) -
      (fderiv ℝ (coordFun ψ σ i) q ((0:ℝ),(1:ℝ))) *
        (fderiv ℝ (coordFun ψ σ j) q ((1:ℝ),(0:ℝ))) := rfl
  rw [h, linCoord_apply_pair, hz]
  ring

/-- The norm of a vector is bounded by the sum of the absolute values of its coordinates. -/
theorem norm_le_sum_abs_coord (σ : Equiv.Perm (Fin 3)) (v : R3) :
    ‖v‖ ≤ ∑ k : Fin 3, |v (σ k)| := by
  have h2 : ∑ m : Fin 3, |v m| ^ 2 ≤ (∑ m : Fin 3, |v m|) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg (fun m _ => abs_nonneg _)
  have h3 : (0:ℝ) ≤ ∑ m : Fin 3, |v m| := Finset.sum_nonneg (fun m _ => abs_nonneg _)
  calc ‖v‖ = Real.sqrt (∑ m : Fin 3, ‖v m‖ ^ 2) := EuclideanSpace.norm_eq v
    _ = Real.sqrt (∑ m : Fin 3, |v m| ^ 2) := by simp [Real.norm_eq_abs]
    _ ≤ Real.sqrt ((∑ m : Fin 3, |v m|) ^ 2) := Real.sqrt_le_sqrt h2
    _ = ∑ m : Fin 3, |v m| := Real.sqrt_sq h3
    _ = ∑ k : Fin 3, |v (σ k)| := (Equiv.sum_comp σ (fun m => |v m|)).symm

/-- The `v`-component of the derivative of the `σ k`-coordinate function is continuous. -/
theorem continuous_coordDeriv (ψ : Submission.Diffeo) (σ : Equiv.Perm (Fin 3)) (k : Fin 3)
    (v : ℝ × ℝ) :
    Continuous (fun q : ℝ × ℝ => fderiv ℝ (coordFun ψ σ k) q v) :=
  ((ContinuousLinearMap.apply ℝ ℝ v).continuous).comp
    ((contDiff_coordFun ψ σ k).continuous_fderiv (by simp))

/-- The vertical tangent determinant depends continuously on the parameter. -/
theorem continuous_faceVertDet (ψ : Submission.Diffeo) (σ : Equiv.Perm (Fin 3)) (i j : Fin 3) :
    Continuous (faceVertDet ψ σ i j) := by
  have h (k : Fin 3) (v : ℝ × ℝ) :
      Continuous (fun q : ℝ × ℝ => fderiv ℝ (coordFun ψ σ k) q v) :=
    continuous_coordDeriv ψ σ k v
  exact (((h i ((1:ℝ),(0:ℝ))).mul (h j ((0:ℝ),(1:ℝ)))).sub
    ((h i ((0:ℝ),(1:ℝ))).mul (h j ((1:ℝ),(0:ℝ)))))

/-- The derivative of the face pair map is `2πℤ²`-periodic in the parameter. -/
theorem fderiv_facePairMap_period (ψ : Submission.Diffeo) (σ : Equiv.Perm (Fin 3)) (i : Fin 3)
    (p : ℝ × ℝ) (k l : ℤ) :
    fderiv ℝ (facePairMap ψ σ i)
      (p.1 + (k : ℝ) * (2 * Real.pi), p.2 + (l : ℝ) * (2 * Real.pi)) =
    fderiv ℝ (facePairMap ψ σ i) p := by
  set c : ℝ × ℝ := ((k : ℝ) * (2 * Real.pi), (l : ℝ) * (2 * Real.pi)) with hc
  have hfun2 : ((facePairMap ψ σ i) ∘ (fun q : ℝ × ℝ => q + c)) = (facePairMap ψ σ i) := by
    funext q
    show facePairMap ψ σ i (q + c) = facePairMap ψ σ i q
    have hqc : (q + c : ℝ × ℝ) =
        (q.1 + (k : ℝ) * (2 * Real.pi), q.2 + (l : ℝ) * (2 * Real.pi)) := by
      rw [hc]; rfl
    rw [hqc]
    exact facePairMap_period ψ σ i q k l
  have hdiff : DifferentiableAt ℝ (facePairMap ψ σ i) (p + c) :=
    (facePairMap_contDiff ψ σ i).contDiffAt.differentiableAt (by norm_num)
  have hshift : HasFDerivAt (fun q : ℝ × ℝ => q + c) (ContinuousLinearMap.id ℝ (ℝ × ℝ)) p :=
    (hasFDerivAt_id p).add_const c
  have hcomp : HasFDerivAt ((facePairMap ψ σ i) ∘ (fun q : ℝ × ℝ => q + c))
      ((fderiv ℝ (facePairMap ψ σ i) (p + c)).comp (ContinuousLinearMap.id ℝ (ℝ × ℝ))) p :=
    hdiff.hasFDerivAt.comp p hshift
  rw [hfun2] at hcomp
  rw [hcomp.fderiv, ContinuousLinearMap.comp_id, hc]
  rfl


/-- Every parameter is the translate of a fundamental-domain parameter by a period lattice vector. -/
theorem exists_mem_arcFundBox_add_period (p : ℝ × ℝ) :
    ∃ q ∈ arcFundBox, ∃ k l : ℤ,
      q.1 + (k : ℝ) * (2 * Real.pi) = p.1 ∧ q.2 + (l : ℝ) * (2 * Real.pi) = p.2 := by
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  refine ⟨(p.1 - (⌊p.1 / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi),
      p.2 - (⌊p.2 / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi)), ?_,
    ⌊p.1 / (2 * Real.pi)⌋, ⌊p.2 / (2 * Real.pi)⌋, by ring, by ring⟩
  rw [mem_arcFundBox]
  constructor
  · have h1 : (⌊p.1 / (2 * Real.pi)⌋ : ℝ) ≤ p.1 / (2 * Real.pi) := Int.floor_le _
    have h2 := mul_le_mul_of_nonneg_right h1 (le_of_lt h2pi)
    rw [div_mul_cancel₀ _ (ne_of_gt h2pi)] at h2
    have h3 := mul_lt_mul_of_pos_right (Int.lt_floor_add_one (p.1 / (2 * Real.pi))) h2pi
    rw [div_mul_cancel₀ _ (ne_of_gt h2pi)] at h3
    constructor <;> linarith
  · have h1 : (⌊p.2 / (2 * Real.pi)⌋ : ℝ) ≤ p.2 / (2 * Real.pi) := Int.floor_le _
    have h2 := mul_le_mul_of_nonneg_right h1 (le_of_lt h2pi)
    rw [div_mul_cancel₀ _ (ne_of_gt h2pi)] at h2
    have h3 := mul_lt_mul_of_pos_right (Int.lt_floor_add_one (p.2 / (2 * Real.pi))) h2pi
    rw [div_mul_cancel₀ _ (ne_of_gt h2pi)] at h3
    constructor <;> linarith



theorem isInvertible_prod_of_det_ne_zero {φ ψ : ℝ × ℝ →L[ℝ] ℝ}
    (h : φ ((1:ℝ),(0:ℝ)) * ψ ((0:ℝ),(1:ℝ)) - φ ((0:ℝ),(1:ℝ)) * ψ ((1:ℝ),(0:ℝ)) ≠ 0) :
    (φ.prod ψ).IsInvertible := by
  set a : ℝ := φ ((1:ℝ),(0:ℝ)) with ha
  set b : ℝ := φ ((0:ℝ),(1:ℝ)) with hb
  set c' : ℝ := ψ ((1:ℝ),(0:ℝ)) with hc'
  set d : ℝ := ψ ((0:ℝ),(1:ℝ)) with hd
  have hΔ : a * d - b * c' ≠ 0 := by rw [ha, hb, hc', hd]; exact h
  set Δ : ℝ := a * d - b * c' with hΔdef
  have hΔne : Δ ≠ 0 := by rw [hΔdef]; exact hΔ
  let U : ℝ × ℝ →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
  let W : ℝ × ℝ →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ
  let g₁ : ℝ × ℝ →L[ℝ] ℝ := (d / Δ) • U - (b / Δ) • W
  let g₂ : ℝ × ℝ →L[ℝ] ℝ := (-(c' / Δ)) • U + (a / Δ) • W
  let g : ℝ × ℝ →L[ℝ] ℝ × ℝ := g₁.prod g₂
  have hg₁ : ∀ y : ℝ × ℝ, g₁ y = (d * y.1 - b * y.2) / Δ := by
    intro y
    show d / Δ * y.1 - b / Δ * y.2 = (d * y.1 - b * y.2) / Δ
    field_simp
  have hg₂ : ∀ y : ℝ × ℝ, g₂ y = (-(c' * y.1) + a * y.2) / Δ := by
    intro y
    show -(c' / Δ) * y.1 + a / Δ * y.2 = (-(c' * y.1) + a * y.2) / Δ
    field_simp
  have hφg : ∀ y : ℝ × ℝ, φ (g y) = g₁ y * a + g₂ y * b := by
    intro y
    rw [show g y = (g₁ y, g₂ y) from ContinuousLinearMap.prod_apply g₁ g₂ y]
    rw [linCoord_apply_pair, ← ha, ← hb]
  have hψg : ∀ y : ℝ × ℝ, ψ (g y) = g₁ y * c' + g₂ y * d := by
    intro y
    rw [show g y = (g₁ y, g₂ y) from ContinuousLinearMap.prod_apply g₁ g₂ y]
    rw [linCoord_apply_pair, ← hc', ← hd]
  refine ContinuousLinearMap.IsInvertible.of_inverse (f := φ.prod ψ) (g := g) ?_ ?_
  · rw [ContinuousLinearMap.ext_iff]
    intro y
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
    rw [show (φ.prod ψ) (g y) = (φ (g y), ψ (g y)) from ContinuousLinearMap.prod_apply φ ψ (g y)]
    rw [hφg y, hψg y, hg₁ y, hg₂ y]
    refine Prod.ext ?_ ?_
    · field_simp
      ring
    · field_simp
      ring
  · rw [ContinuousLinearMap.ext_iff]
    intro u
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
    rw [show (φ.prod ψ) u = (φ u, ψ u) from ContinuousLinearMap.prod_apply φ ψ u]
    rw [show g (φ u, ψ u) = (g₁ (φ u, ψ u), g₂ (φ u, ψ u)) from
      ContinuousLinearMap.prod_apply g₁ g₂ (φ u, ψ u)]
    rw [hg₁ (φ u, ψ u), hg₂ (φ u, ψ u)]
    rw [linCoord_apply_pair φ u, ← ha, ← hb, linCoord_apply_pair ψ u, ← hc', ← hd]
    refine Prod.ext ?_ ?_
    · field_simp
      ring
    · field_simp
      ring


/-- Nonvanishing of the vertical tangent determinant gives invertibility of the face pair derivative
(the determinant of the `2 × 2` system is exactly this function). -/
theorem isInvertible_facePairMap_of_faceVertDet_ne_zero (ψ : Submission.Diffeo)
    (σ : Equiv.Perm (Fin 3)) (i : Fin 3) (q : ℝ × ℝ)
    (h : faceVertDet ψ σ i 2 q ≠ 0) :
    (fderiv ℝ (facePairMap ψ σ i) q).IsInvertible := by
  rw [fderiv_facePairMap]
  exact isInvertible_prod_of_det_ne_zero h

end

end Work.Drive.Mono
