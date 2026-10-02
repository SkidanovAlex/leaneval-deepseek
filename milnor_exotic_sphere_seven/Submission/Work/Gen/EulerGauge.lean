import Mathlib
import Submission.Work.Gen.Basic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The Euler-sequence gauge over the standard charts of `ℂPⁿ`

This module sets up the pointwise identity behind the Euler sequence.  With `Λᵢ(u) = insertNth i 1 u`
the normalised homogeneous representative read in the chart `i`, the chart transition
`Φ = chartFun j ∘ chartInv i` satisfies, on the overlap of the two charts,
`Λᵢ(u) = (homCoord n i j (chartInv i u)) • insertNth j 1 (Φ u)` — the two representatives differ by
the `j`-th coordinate.  Differentiating this identity (chain rule + product rule) and projecting
orthogonally to `ℂ·Λᵢ(u)` is the whole content of the Euler sequence.
-/

namespace Work.Gen

open Work.Projective

noncomputable section

variable {n : ℕ}

/-- The linear map `u ↦ insertNth i 0 u`. -/
def insCLM (i : Fin (n + 1)) : (Fin n → ℂ) →L[ℂ] (Fin (n + 1) → ℂ) :=
  ContinuousLinearMap.pi (fun m : Fin (n + 1) =>
    if h : m = i then 0 else ContinuousLinearMap.proj (removeAbove i m h))

/-- The constant vector taking the value `c` at `i` and `0` elsewhere. -/
def insVec (i : Fin (n + 1)) (c : ℂ) : Fin (n + 1) → ℂ :=
  fun m => if h : m = i then c else 0

theorem insCLM_apply (i : Fin (n + 1)) (u : Fin n → ℂ) (m : Fin (n + 1)) :
    insCLM i u m = if h : m = i then 0 else u (removeAbove i m h) := by
  simp only [insCLM, ContinuousLinearMap.pi_apply]
  by_cases h : m = i
  · rw [dif_pos h, dif_pos h]
    rfl
  · rw [dif_neg h, dif_neg h]
    rfl

theorem insertNth_eq_ins (i : Fin (n + 1)) (c : ℂ) (u : Fin n → ℂ) :
    Fin.insertNth (α := fun _ => ℂ) i c u = insCLM i u + insVec i c := by
  funext m
  rw [Pi.add_apply, insCLM_apply]
  by_cases h : m = i
  · subst h
    rw [dif_pos rfl, Fin.insertNth_apply_same, insVec, dif_pos rfl]
    simp
  · rw [dif_neg h, insertNth_apply_of_ne i m h, insVec, dif_neg h]
    simp

/-- `insertNth i c` is affine with linear part `insCLM i`. -/
theorem hasFDerivAt_insertNth (i : Fin (n + 1)) (c : ℂ) (u : Fin n → ℂ) :
    HasFDerivAt (fun u : Fin n → ℂ => Fin.insertNth (α := fun _ => ℂ) i c u)
      (insCLM i) u := by
  have h : (fun u : Fin n → ℂ => Fin.insertNth (α := fun _ => ℂ) i c u)
      = fun u => insCLM i u + insVec i c := by
    funext u; exact insertNth_eq_ins i c u
  rw [h]
  exact (insCLM i).hasFDerivAt.add_const (insVec i c)

/-- The chart transition `chartFun j ∘ chartInv i` in the coordinates of the chart `i`. -/
def Phi (i j : Fin (n + 1)) : (Fin n → ℂ) → (Fin n → ℂ) :=
  fun u => chartFun j (chartInv i u)

/-- The `m`-th coordinate of `chartFun j (chartInv i u)` is, for `m = j.succAbove k`, the
quotient of the corresponding coordinates of `insertNth i 1 u`. -/
theorem chartFun_chartInv_apply {i j : Fin (n + 1)} {u : Fin n → ℂ}
    (hu : chartInv i u ∈ chartSet j) (k : Fin n) :
    Phi i j u k = (Fin.insertNth (α := fun _ => ℂ) i (1 : ℂ) u) (j.succAbove k) /
      (Fin.insertNth (α := fun _ => ℂ) i (1 : ℂ) u) j := by
  simp only [Phi, chartInv_apply, chartFun_cpMk, chartFunAux]

/-- `homCoord n i j` read in the chart `i` is the `j`-th coordinate of the normalised
representative. -/
theorem homCoord_chartInv_eq (i j : Fin (n + 1)) (u : Fin n → ℂ) :
    homCoord n i j (chartInv i u) = (Fin.insertNth (α := fun _ => ℂ) i (1 : ℂ) u) j := by
  simp only [homCoord, chartInv_apply, chartFun_cpMk, chartFunAux]
  by_cases h : j = i
  · subst h
    rw [dif_pos rfl, Fin.insertNth_apply_same]
  · rw [dif_neg h, Fin.insertNth_apply_same, succAbove_removeAbove, div_one]

/-- **The key pointwise identity**: the normalised representatives in the charts `i` and `j` differ
by the `j`-th homogeneous coordinate. -/
theorem insertNth_Phi {i j : Fin (n + 1)} {u : Fin n → ℂ} (hu : chartInv i u ∈ chartSet j) :
    Fin.insertNth (α := fun _ => ℂ) i (1 : ℂ) u
      = (homCoord n i j (chartInv i u)) •
        Fin.insertNth (α := fun _ => ℂ) j (1 : ℂ) (Phi i j u) := by
  have hne : (Fin.insertNth (α := fun _ => ℂ) i (1 : ℂ) u) j ≠ 0 := by
    have := (mem_chartSet_iff j ⟨Fin.insertNth (α := fun _ => ℂ) i (1 : ℂ) u,
      insertNth_one_ne_zero i u⟩).mp (by rwa [← chartInv_apply i u])
    exact this
  rw [homCoord_chartInv_eq i j u]
  funext m
  rw [Pi.smul_apply]
  by_cases hm : m = j
  · subst hm
    rw [Fin.insertNth_apply_same, smul_eq_mul, mul_one]
  · rw [insertNth_apply_of_ne j m hm]
    rw [chartFun_chartInv_apply hu (removeAbove j m hm)]
    rw [succAbove_removeAbove]
    rw [smul_eq_mul]
    field_simp

end

end Work.Gen


namespace Work.Gen

open Work.Projective

noncomputable section

variable {n : ℕ}

/-- The standard basis vector of `Fin k → ℂ`. -/
def stdBasis (k : ℕ) (m : Fin k) : Fin k → ℂ := Pi.single m 1

@[simp] theorem stdBasis_apply_same (k : ℕ) (m : Fin k) : stdBasis k m m = 1 := by
  simp [stdBasis]

theorem stdBasis_apply_of_ne {k : ℕ} {m m' : Fin k} (h : m' ≠ m) :
    stdBasis k m m' = 0 := by
  simp [stdBasis, h]

/-- The Hermitian form `∑ conj (v m) * x m`, as a continuous linear map in `x`. -/
def ipCLM {k : ℕ} (v : Fin k → ℂ) : (Fin k → ℂ) →L[ℂ] ℂ :=
  ∑ m, (star (v m)) • ContinuousLinearMap.proj m

theorem ipCLM_apply {k : ℕ} (v x : Fin k → ℂ) :
    ipCLM v x = ∑ m, star (v m) * x m := by
  rw [ipCLM, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]

theorem ipCLM_smul_left {k : ℕ} (v x : Fin k → ℂ) (c : ℂ) :
    ipCLM (c • v) x = star c * ipCLM v x := by
  rw [ipCLM_apply, ipCLM_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, star_mul]
  ring

theorem ipCLM_self_smul {k : ℕ} (v : Fin k → ℂ) (c : ℂ) :
    ipCLM (c • v) (c • v) = star c * c * ipCLM v v := by
  rw [ipCLM_smul_left, ContinuousLinearMap.map_smul, smul_eq_mul]
  ring

theorem ipCLM_self_ne_zero {k : ℕ} {v : Fin k → ℂ} (hv : v ≠ 0) : ipCLM v v ≠ 0 := by
  intro h
  have hsum : (∑ m, Complex.normSq (v m) : ℝ) = 0 := by
    have h' : ((∑ m, Complex.normSq (v m) : ℝ) : ℂ) = 0 := by
      rw [← h, ipCLM_apply]
      push_cast
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Complex.star_def, mul_comm, Complex.mul_conj]
    exact Complex.ofReal_injective (by rw [h']; simp)
  have hall := (Finset.sum_eq_zero_iff_of_nonneg
    (fun m _ => Complex.normSq_nonneg (v m))).mp hsum
  refine hv (funext fun m => ?_)
  exact Complex.normSq_eq_zero.mp (hall m (Finset.mem_univ m))

/-- **The orthogonal projection off the complex line `ℂ v`.** -/
def prCLM {k : ℕ} (v : Fin k → ℂ) : (Fin k → ℂ) →L[ℂ] (Fin k → ℂ) :=
  ContinuousLinearMap.id ℂ (Fin k → ℂ) -
    (ipCLM v).smulRight (((ipCLM v v)⁻¹ : ℂ) • v)

theorem prCLM_apply {k : ℕ} (v x : Fin k → ℂ) :
    prCLM v x = x - (ipCLM v x / ipCLM v v) • v := by
  rw [prCLM, sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, smul_smul, div_eq_mul_inv]

theorem prCLM_self {k : ℕ} (v : Fin k → ℂ) (h : ipCLM v v ≠ 0) : prCLM v v = 0 := by
  rw [prCLM_apply, div_self h, one_smul, sub_self]

/-- The projection only depends on the complex line spanned by `v`. -/
theorem prCLM_smul {k : ℕ} {v : Fin k → ℂ} (hv : v ≠ 0) {c : ℂ} (hc : c ≠ 0) :
    prCLM (c • v) = prCLM v := by
  have hv' : c • v ≠ 0 := smul_ne_zero hc hv
  ext x
  rw [prCLM_apply, prCLM_apply, ipCLM_smul_left, ipCLM_self_smul]
  have hB : ipCLM v v ≠ 0 := ipCLM_self_ne_zero hv
  have hsc : star c ≠ 0 := star_ne_zero.mpr hc
  congr 1
  rw [smul_smul, div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev, mul_inv_rev]
  field_simp

end

end Work.Gen


namespace Work.Gen

open Work.Projective Filter
open scoped Topology

noncomputable section

variable {n : ℕ}

theorem differentiableAt_insNth_proj (i m : Fin (n + 1)) (u : Fin n → ℂ) :
    DifferentiableAt ℂ (fun u : Fin n → ℂ => Fin.insertNth (α := fun _ => ℂ) i (1 : ℂ) u m) u := by
  rw [show (fun u : Fin n → ℂ => Fin.insertNth (α := fun _ => ℂ) i (1 : ℂ) u m)
      = fun u => insCLM i u m + insVec i 1 m from by
        funext w; rw [insertNth_eq_ins]; rfl]
  exact (((ContinuousLinearMap.proj m).comp (insCLM i)).differentiableAt).add_const _

/-- The chart transition `Φ = chartFun j ∘ chartInv i` is complex-differentiable on the overlap. -/
theorem differentiableAt_Phi {i j : Fin (n + 1)} {u : Fin n → ℂ} (hu : chartInv i u ∈ chartSet j) :
    DifferentiableAt ℂ (Phi i j) u := by
  have hmem : {w : Fin n → ℂ | chartInv i w ∈ chartSet j} ∈ 𝓝 u :=
    ((isOpen_chartSet j).preimage (continuous_chartInv i)).mem_nhds hu
  have hB : (Fin.insertNth (α := fun _ => ℂ) i (1 : ℂ) u) j ≠ 0 :=
    (mem_chartSet_iff j ⟨Fin.insertNth (α := fun _ => ℂ) i (1 : ℂ) u,
      insertNth_one_ne_zero i u⟩).mp (by rwa [← chartInv_apply i u])
  have hΨ : DifferentiableAt ℂ (fun w : Fin n → ℂ => fun k : Fin n =>
      (Fin.insertNth (α := fun _ => ℂ) i (1 : ℂ) w) (j.succAbove k) /
      (Fin.insertNth (α := fun _ => ℂ) i (1 : ℂ) w) j) u := by
    rw [differentiableAt_pi]
    intro k
    rw [show (fun w : Fin n → ℂ =>
        (Fin.insertNth (α := fun _ => ℂ) i (1 : ℂ) w) (j.succAbove k) /
        (Fin.insertNth (α := fun _ => ℂ) i (1 : ℂ) w) j)
        = fun w => (Fin.insertNth (α := fun _ => ℂ) i (1 : ℂ) w) (j.succAbove k) *
            ((Fin.insertNth (α := fun _ => ℂ) i (1 : ℂ) w) j)⁻¹ from by
          funext w; rw [div_eq_mul_inv]]
    exact (differentiableAt_insNth_proj i (j.succAbove k) u).mul
      ((differentiableAt_insNth_proj i j u).inv hB)
  refine hΨ.congr_of_eventuallyEq ?_
  filter_upwards [hmem] with w hw
  exact funext fun k => (chartFun_chartInv_apply hw k).symm

/-- **The derivative identity of the chart transition**, over `ℂ`. -/
theorem gauge_chainCLM {i j : Fin (n + 1)} {u : Fin n → ℂ} (hu : chartInv i u ∈ chartSet j) :
    insCLM i = ((Fin.insertNth (α := fun _ => ℂ) i (1 : ℂ) u) j) •
        ((insCLM j).comp (fderiv ℂ (Phi i j) u)) +
      (((ContinuousLinearMap.proj j).comp (insCLM i)).smulRight
        (Fin.insertNth (α := fun _ => ℂ) j 1 (Phi i j u))) := by
  have h1 := hasFDerivAt_insertNth i (1 : ℂ) u
  have hPhi := (differentiableAt_Phi hu).hasFDerivAt
  have hPsi : HasFDerivAt (fun w : Fin n → ℂ => Fin.insertNth (α := fun _ => ℂ) j 1 (Phi i j w))
      ((insCLM j).comp (fderiv ℂ (Phi i j) u)) u :=
    HasFDerivAt.comp (x := u) (f := Phi i j) (f' := fderiv ℂ (Phi i j) u)
      (hasFDerivAt_insertNth j (1 : ℂ) (Phi i j u)) hPhi
  have hl : HasFDerivAt (fun w : Fin n → ℂ => (Fin.insertNth (α := fun _ => ℂ) i (1 : ℂ) w) j)
      ((ContinuousLinearMap.proj j).comp (insCLM i)) u := by
    rw [show (fun w : Fin n → ℂ => (Fin.insertNth (α := fun _ => ℂ) i (1 : ℂ) w) j)
        = fun w => ((ContinuousLinearMap.proj j).comp (insCLM i)) w + (insVec i 1) j from by
          funext w; rw [insertNth_eq_ins]
          simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]]
    exact (((ContinuousLinearMap.proj j).comp (insCLM i)).hasFDerivAt).add_const _
  have hprod := hl.smul hPsi
  have heq : (fun w : Fin n → ℂ => ((Fin.insertNth (α := fun _ => ℂ) i (1 : ℂ) w) j) •
        (Fin.insertNth (α := fun _ => ℂ) j 1 (Phi i j w)))
      =ᶠ[𝓝 u] (fun w : Fin n → ℂ => Fin.insertNth (α := fun _ => ℂ) i (1 : ℂ) w) := by
    have hmem : {w : Fin n → ℂ | chartInv i w ∈ chartSet j} ∈ 𝓝 u :=
      ((isOpen_chartSet j).preimage (continuous_chartInv i)).mem_nhds hu
    filter_upwards [hmem] with w hw
    rw [← homCoord_chartInv_eq i j w]
    exact (insertNth_Phi hw).symm
  exact (h1.congr_of_eventuallyEq heq).unique hprod

/-- **The chain-rule identity of the Euler sequence**, evaluated at a vector. -/
theorem gauge_chain_apply {i j : Fin (n + 1)} {u : Fin n → ℂ} (hu : chartInv i u ∈ chartSet j)
    (x : Fin n → ℂ) :
    insCLM i x = ((Fin.insertNth (α := fun _ => ℂ) i (1 : ℂ) u) j) •
        (insCLM j ((fderiv ℂ (Phi i j) u) x)) +
      (((ContinuousLinearMap.proj j).comp (insCLM i)) x) •
        (Fin.insertNth (α := fun _ => ℂ) j 1 (Phi i j u)) := by
  have h := congrArg (fun (L : (Fin n → ℂ) →L[ℂ] (Fin (n + 1) → ℂ)) => L x)
    (gauge_chainCLM (n := n) hu)
  simpa [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply] using h

end

end Work.Gen

namespace Work.Gen

open Work.Projective Filter

noncomputable section

variable {n : ℕ}

/-- The normalised homogeneous representative read in the chart `i`. -/
def vVec (i : Fin (n + 1)) (u : Fin n → ℂ) : Fin (n + 1) → ℂ :=
  Fin.insertNth (α := fun _ => ℂ) i 1 u

theorem vVec_ne_zero (i : Fin (n + 1)) (u : Fin n → ℂ) : vVec i u ≠ 0 :=
  insertNth_one_ne_zero i u

/-- The squared norm of the normalised representative. -/
def Qfun (i : Fin (n + 1)) (u : Fin n → ℂ) : ℂ := ipCLM (vVec i u) (vVec i u)

theorem Qfun_ne_zero (i : Fin (n + 1)) (u : Fin n → ℂ) : Qfun i u ≠ 0 :=
  ipCLM_self_ne_zero (vVec_ne_zero i u)

/-- The orthogonal projection off the line `ℂ vVec i u`. -/
def prV (i : Fin (n + 1)) (u : Fin n → ℂ) : (Fin (n + 1) → ℂ) →L[ℂ] (Fin (n + 1) → ℂ) :=
  prCLM (vVec i u)


theorem star_insCLM (i : Fin (n + 1)) (x : Fin n → ℂ) :
    star (insCLM i x) = insCLM i (star x) := by
  funext m
  rw [Pi.star_apply, insCLM_apply, insCLM_apply]
  by_cases h : m = i
  · rw [dif_pos h, dif_pos h]; simp
  · rw [dif_neg h, dif_neg h]; simp

theorem star_ipCLM {k : ℕ} (v x : Fin k → ℂ) :
    ipCLM (star v) (star x) = star (ipCLM v x) := by
  rw [ipCLM_apply, ipCLM_apply, star_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Pi.star_apply, Pi.star_apply, star_mul, star_star, mul_comm]

theorem star_prCLM {k : ℕ} (v x : Fin k → ℂ) :
    star (prCLM v x) = prCLM (star v) (star x) := by
  rw [prCLM_apply, prCLM_apply, star_ipCLM, star_ipCLM]
  simp only [star_sub, star_smul, star_div₀]

/-- The `T^{1,0}` block of the Euler gauge, in the coordinates of the chart `i`. -/
def Gblock (i : Fin (n + 1)) (u : Fin n → ℂ) : (Fin n → ℂ) × ℂ → (Fin (n + 1) → ℂ) :=
  fun p => prV i u (insCLM i p.1) + p.2 • vVec i u

theorem Gblock_apply (i : Fin (n + 1)) (u : Fin n → ℂ) (p : (Fin n → ℂ) × ℂ) :
    Gblock i u p = prV i u (insCLM i p.1) + p.2 • vVec i u := rfl

/-- The `T^{0,1}` block of the Euler gauge: the conjugate of the `T^{1,0}` block, scaled by
`1/‖v‖²`. -/
def Hblock (i : Fin (n + 1)) (u : Fin n → ℂ) : (Fin n → ℂ) × ℂ → (Fin (n + 1) → ℂ) :=
  fun p => (Qfun i u)⁻¹ • star (Gblock i u (star p.1, star p.2))

theorem Hblock_apply (i : Fin (n + 1)) (u : Fin n → ℂ) (p : (Fin n → ℂ) × ℂ) :
    Hblock i u p = (Qfun i u)⁻¹ • star (Gblock i u (star p.1, star p.2)) := rfl

/-- The scalar relating the two normalised representatives: the `j`-th coordinate of `vVec i u`. -/
def lam (i j : Fin (n + 1)) (u : Fin n → ℂ) : ℂ := (vVec i u) j

theorem vVec_eq_lam_smul {i j : Fin (n + 1)} {u : Fin n → ℂ} (hu : chartInv i u ∈ chartSet j) :
    vVec i u = lam i j u • vVec j (Phi i j u) := by
  have h := insertNth_Phi hu
  rw [homCoord_chartInv_eq i j u] at h
  exact h

theorem lam_ne_zero {i j : Fin (n + 1)} {u : Fin n → ℂ} (hu : chartInv i u ∈ chartSet j) :
    lam i j u ≠ 0 := by
  have h := vVec_eq_lam_smul (n := n) hu
  intro h0
  rw [h0, zero_smul] at h
  exact vVec_ne_zero i u h

theorem prV_eq_of_charts {i j : Fin (n + 1)} {u : Fin n → ℂ} (hu : chartInv i u ∈ chartSet j) :
    prV j (Phi i j u) = prV i u := by
  have h := vVec_eq_lam_smul (n := n) hu
  rw [prV, prV, h, prCLM_smul (vVec_ne_zero j _) (lam_ne_zero hu)]

theorem Qfun_eq {i j : Fin (n + 1)} {u : Fin n → ℂ} (hu : chartInv i u ∈ chartSet j) :
    Qfun i u = star (lam i j u) * lam i j u * Qfun j (Phi i j u) := by
  have h := vVec_eq_lam_smul (n := n) hu
  rw [Qfun, Qfun, h, ipCLM_self_smul]



/-- **The `T^{1,0}` gauge identity**: the gauge intertwines the chart transition with the
`O(1)`-transition `(λ)⁻¹`. -/
theorem Gblock_comp {i j : Fin (n + 1)} {u : Fin n → ℂ} (hu : chartInv i u ∈ chartSet j)
    (x : Fin n → ℂ) (c : ℂ) :
    Gblock j (Phi i j u) ((fderiv ℂ (Phi i j) u) x, c) =
      (lam i j u)⁻¹ • Gblock i u (x, c) := by
  have hchain := gauge_chain_apply (n := n) hu x
  have hlam := lam_ne_zero (n := n) hu
  have hpr : prV i u (insCLM i x) = lam i j u • prV i u (insCLM j ((fderiv ℂ (Phi i j) u) x)) := by
    have h := congrArg (prV i u) hchain
    simp only [map_add, map_smul] at h
    have h2 : prV i u (Fin.insertNth (α := fun _ => ℂ) j 1 (Phi i j u)) = 0 := by
      have h0 : Fin.insertNth (α := fun _ => ℂ) j 1 (Phi i j u) = (lam i j u)⁻¹ • vVec i u := by
        rw [show Fin.insertNth (α := fun _ => ℂ) j 1 (Phi i j u) = vVec j (Phi i j u) from rfl,
          vVec_eq_lam_smul (n := n) hu, smul_smul, inv_mul_cancel₀ hlam, one_smul]
      rw [h0, map_smul, prV, prCLM_self _ (Qfun_ne_zero i u), smul_zero]
    rw [h2, smul_zero, add_zero] at h
    exact h
  show prV j (Phi i j u) (insCLM j ((fderiv ℂ (Phi i j) u) x)) + c • vVec j (Phi i j u)
      = (lam i j u)⁻¹ • (prV i u (insCLM i x) + c • vVec i u)
  rw [prV_eq_of_charts hu, hpr, vVec_eq_lam_smul (n := n) hu]
  simp only [smul_add, smul_smul]
  rw [inv_mul_cancel₀ hlam, one_smul]
  congr 1
  congr 1
  rw [mul_comm c (lam i j u), ← mul_assoc, inv_mul_cancel₀ hlam, one_mul]

/-- **The `T^{0,1}` gauge identity**: the conjugate gauge intertwines the conjugate transition with
the `O(-1)`-transition `λ`. -/
theorem Hblock_comp {i j : Fin (n + 1)} {u : Fin n → ℂ} (hu : chartInv i u ∈ chartSet j)
    (x : Fin n → ℂ) (c : ℂ) :
    Hblock j (Phi i j u) (star ((fderiv ℂ (Phi i j) u) (star x)), c) =
      lam i j u • Hblock i u (x, c) := by
  have hlam := lam_ne_zero (n := n) hu
  have hG := Gblock_comp (n := n) hu (star x) (star c)
  show (Qfun j (Phi i j u))⁻¹ • star (Gblock j (Phi i j u) (star (star ((fderiv ℂ (Phi i j) u) (star x))), star c))
      = lam i j u • Hblock i u (x, c)
  rw [star_star]
  rw [show Gblock j (Phi i j u) ((fderiv ℂ (Phi i j) u) (star x), star c)
      = (lam i j u)⁻¹ • Gblock i u (star x, star c) from hG]
  rw [Hblock_apply, star_smul, star_inv₀, Qfun_eq hu]
  rw [smul_smul, smul_smul]
  congr 1
  field_simp

end

end Work.Gen
