import Mathlib
import Submission.Work.ThomBordism.Grassmann.Model
import Submission.Work.ThomBordism.Grassmann.CP4Probe.Defs
import Submission.Work.ThomBordism.Grassmann.CP4Probe.Map
import Submission.Work.ThomBordism.Grassmann.CxModel
import Submission.Work.ThomBordism.Grassmann.CxFibre
import Submission.Work.Gen.ConjLine
import Submission.Work.Whitney.Basic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# The "two-block" `ℂP⁴`-probe into `G̃r₄(ℝ²⁰)`

Vocabulary of `Work.ThomBordism.Grassmann.probeCP4_twoBlock`: the two-block decomposition
`ℝ²⁰ = ℝ¹⁰ ⊕ ℝ¹⁰`, the explicit realification `ℂ⁵ → ℝ¹⁰`, the two-block frame of a nonzero
`v : ℂ⁵` (the real `4`-plane `L ⊕ L ⊂ ℂ⁵ ⊕ ℂ⁵`), and the induced map
`tbMap : ℂP⁴ → G̃r₄(ℝ²⁰)`.  Also the comparison bundle `tbW = tbZL ⊕ tbZL`.
-/

namespace Work.ThomBordism.Grassmann

open Work.TangentClasses Work.Projective

noncomputable section

/-- The coordinate projection of `EuclideanSpace` is evaluation of the underlying function. -/
theorem tbProj_apply {n : ℕ} (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace.proj (𝕜 := ℝ) i x = x.ofLp i := rfl

/-! ## 1. Index bookkeeping -/

/-- The `a`-th real coordinate of the `j`-th complex coordinate, inside `ℝ¹⁰`. -/
def tbIdx10 (j : Fin 5) (a : Fin 2) : Fin 10 := ⟨2 * j.val + a.val, by omega⟩

/-- The same index inside the first block of `ℝ²⁰`. -/
def tbIdx20L (j : Fin 5) (a : Fin 2) : Fin 20 := ⟨2 * j.val + a.val, by omega⟩

/-- The same index inside the second block of `ℝ²⁰`. -/
def tbIdx20R (j : Fin 5) (a : Fin 2) : Fin 20 := ⟨10 + 2 * j.val + a.val, by omega⟩

theorem tbIdx10_eq_iff {j j' : Fin 5} {a a' : Fin 2} :
    tbIdx10 j a = tbIdx10 j' a' ↔ j = j' ∧ a = a' := by
  constructor
  · intro h
    have hv : 2 * j.val + a.val = 2 * j'.val + a'.val := by
      simpa [tbIdx10] using congrArg Fin.val h
    exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem tbIdx10_ne_zero_one (j : Fin 5) : tbIdx10 j 0 ≠ tbIdx10 j 1 := by
  intro h
  have h2 := (tbIdx10_eq_iff.mp h).2
  exact (by decide : (0 : Fin 2) ≠ 1) h2
theorem tbIdx10_injective : Function.Injective (fun p : Fin 5 × Fin 2 => tbIdx10 p.1 p.2) := by
  intro p q h
  exact Prod.ext (tbIdx10_eq_iff.mp h).1 (tbIdx10_eq_iff.mp h).2
theorem tbIdx10_surjective : Function.Surjective (fun p : Fin 5 × Fin 2 => tbIdx10 p.1 p.2) := by
  intro k
  refine ⟨(⟨k.val / 2, by have := k.isLt; omega⟩, ⟨k.val % 2, by omega⟩), ?_⟩
  ext
  show 2 * (k.val / 2) + k.val % 2 = k.val
  have h := Nat.div_add_mod k.val 2
  omega
/-- The index equivalence `Fin 5 × Fin 2 ≃ Fin 10` underlying the realification. -/
noncomputable def tbE10 : Fin 5 × Fin 2 ≃ Fin 10 :=
  Equiv.ofBijective _ ⟨tbIdx10_injective, tbIdx10_surjective⟩

@[simp] theorem tbE10_apply (p : Fin 5 × Fin 2) : tbE10 p = tbIdx10 p.1 p.2 := rfl

/-! ## 2. The realification `ℂ⁵ → ℝ¹⁰` -/

/-- The underlying function of the realification `ℂ⁵ → ℝ¹⁰`: the `j`-th complex coordinate is sent
to the pair `(2j, 2j+1) = (Re, Im)`. -/
noncomputable def tbRealFun (z : E5) : Amb 10 :=
  ∑ j : Fin 5, ((z.ofLp j).re • (EuclideanSpace.single (𝕜 := ℝ) (tbIdx10 j 0) (1 : ℝ) : Amb 10)
    + (z.ofLp j).im • (EuclideanSpace.single (𝕜 := ℝ) (tbIdx10 j 1) (1 : ℝ) : Amb 10))

theorem tbRealFun_add (z w : E5) : tbRealFun (z + w) = tbRealFun z + tbRealFun w := by
  simp only [tbRealFun, WithLp.ofLp_add, Pi.add_apply, Complex.add_re, Complex.add_im]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [add_smul, add_smul]
  abel
theorem tbRealFun_smul (r : ℝ) (z : E5) : tbRealFun (r • z) = r • tbRealFun z := by
  simp only [tbRealFun, WithLp.ofLp_smul, Pi.smul_apply]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [Complex.smul_re, Complex.smul_im, smul_eq_mul, smul_add, smul_smul]
/-- **The realification `ℂ⁵ → ℝ¹⁰`**. -/
noncomputable def tbReal : E5 →L[ℝ] Amb 10 :=
  LinearMap.toContinuousLinearMap (𝕜 := ℝ)
    { toFun := tbRealFun, map_add' := tbRealFun_add, map_smul' := tbRealFun_smul }

theorem tbReal_apply (z : E5) : tbReal z = tbRealFun z := rfl

theorem tbReal_coord (z : E5) (j : Fin 5) (a : Fin 2) :
    (tbReal z).ofLp (tbIdx10 j a) = (if a = 0 then (z.ofLp j).re else (z.ofLp j).im) := by
  rw [tbReal_apply, tbRealFun]
  simp only [WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_add, Pi.add_apply,
    WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single j]
  · fin_cases a <;> simp [single_coord_self, single_coord_ne, tbIdx10_ne_zero_one j]
  · intro j' _ hj'
    have h0 : tbIdx10 j a ≠ tbIdx10 j' 0 := fun h => hj' (tbIdx10_eq_iff.mp h).1.symm
    have h1 : tbIdx10 j a ≠ tbIdx10 j' 1 := fun h => hj' (tbIdx10_eq_iff.mp h).1.symm
    rw [single_coord_ne h0, single_coord_ne h1]
    ring
  · intro h; exact absurd (Finset.mem_univ j) h

theorem tbReal_norm (z : E5) : ‖tbReal z‖ = ‖z‖ := by
  have h1 : ‖tbReal z‖ ^ 2 = ∑ j : Fin 5, ((z.ofLp j).re ^ 2 + (z.ofLp j).im ^ 2) := by
    rw [PiLp.norm_sq_eq_of_L2]
    rw [← Equiv.sum_comp tbE10 (fun k : Fin 10 => ‖(tbReal z).ofLp k‖ ^ 2)]
    simp only [tbE10_apply]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Fin.sum_univ_two, tbReal_coord, tbReal_coord]
    norm_num
  have h2 : ‖z‖ ^ 2 = ∑ j : Fin 5, ((z.ofLp j).re ^ 2 + (z.ofLp j).im ^ 2) := by
    rw [PiLp.norm_sq_eq_of_L2]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have h3 : ‖tbReal z‖ ^ 2 = ‖z‖ ^ 2 := by rw [h1, h2]
  nlinarith [norm_nonneg (tbReal z), norm_nonneg z]
theorem tbReal_inner (z w : E5) : inner ℝ (tbReal z) (tbReal w) = inner ℝ z w := by
  have h : tbReal z + tbReal w = tbReal (z + w) := (map_add tbReal z w).symm
  rw [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
    real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two, h,
    tbReal_norm, tbReal_norm, tbReal_norm]
/-! ## 3. Pair coordinates of `ℝ¹⁰` -/

/-- The `j`-th pair of real coordinates of `ℝ¹⁰`, as a vector of `ℝ²`. -/
noncomputable def tbPair (j : Fin 5) : Amb 10 →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (EuclideanSpace.proj (𝕜 := ℝ) (tbIdx10 j 0)).smulRight
      (EuclideanSpace.single (𝕜 := ℝ) (0 : Fin 2) (1 : ℝ))
    + (EuclideanSpace.proj (𝕜 := ℝ) (tbIdx10 j 1)).smulRight
      (EuclideanSpace.single (𝕜 := ℝ) (1 : Fin 2) (1 : ℝ))

theorem tbPair_apply (j : Fin 5) (w : Amb 10) :
    tbPair j w = WithLp.toLp 2 ![(w.ofLp (tbIdx10 j 0)), (w.ofLp (tbIdx10 j 1))] := by
  refine PiLp.ext (fun k => ?_)
  fin_cases k <;> simp [tbPair]

/-- The insertion of a pair of coordinates into the `j`-th slot of `ℝ¹⁰`. -/
noncomputable def tbPairInj (j : Fin 5) : EuclideanSpace ℝ (Fin 2) →L[ℝ] Amb 10 :=
  (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).smulRight
      (EuclideanSpace.single (𝕜 := ℝ) (tbIdx10 j 0) (1 : ℝ))
    + (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).smulRight
      (EuclideanSpace.single (𝕜 := ℝ) (tbIdx10 j 1) (1 : ℝ))

theorem tbPairInj_coord (j : Fin 5) (v : EuclideanSpace ℝ (Fin 2)) (a : Fin 2) :
    (tbPairInj j v).ofLp (tbIdx10 j a) = v.ofLp a := by
  fin_cases a <;> simp [tbPairInj, single_coord_self, single_coord_ne, tbIdx10_ne_zero_one j]

theorem tbPairInj_coord_ne (j : Fin 5) (v : EuclideanSpace ℝ (Fin 2)) {k : Fin 10}
    (h : ∀ a, k ≠ tbIdx10 j a) : (tbPairInj j v).ofLp k = 0 := by
  simp only [tbPairInj, ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
    WithLp.ofLp_add, Pi.add_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  rw [single_coord_ne (h 0), single_coord_ne (h 1)]
  simp

theorem tbPair_coord (j : Fin 5) (w : Amb 10) (a : Fin 2) :
    (tbPair j w).ofLp a = w.ofLp (tbIdx10 j a) := by
  rw [tbPair_apply, WithLp.ofLp_toLp]
  fin_cases a <;> simp

theorem tbPair_tbPairInj_coord (j j' : Fin 5) (v : EuclideanSpace ℝ (Fin 2)) (a : Fin 2) :
    (tbPair j (tbPairInj j' v)).ofLp a = (if j = j' then v else 0).ofLp a := by
  rw [tbPair_coord]
  by_cases h : j = j'
  · subst h
    rw [tbPairInj_coord, if_pos rfl]
  · rw [tbPairInj_coord_ne j' v (fun a' ha' => h (tbIdx10_eq_iff.mp ha').1), if_neg h]
    simp

theorem tbPair_tbPairInj (j j' : Fin 5) (v : EuclideanSpace ℝ (Fin 2)) :
    tbPair j (tbPairInj j' v) = if j = j' then v else 0 :=
  PiLp.ext (tbPair_tbPairInj_coord j j' v)

theorem tbPair_sum (w : Amb 10) : ∑ j : Fin 5, tbPairInj j (tbPair j w) = w := by
  refine PiLp.ext (fun k => ?_)
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  obtain ⟨⟨p1, p2⟩, hp⟩ := tbIdx10_surjective k
  rw [← hp, Finset.sum_eq_single p1]
  · rw [tbPairInj_coord, tbPair_apply]
    fin_cases p2 <;> simp
  · intro j _ hj
    rw [tbPairInj_coord_ne]
    intro a ha
    exact hj (tbIdx10_eq_iff.mp ha.symm).1
  · intro h; exact absurd (Finset.mem_univ p1) h
theorem tbPair_ext {w w' : Amb 10} (h : ∀ j, tbPair j w = tbPair j w') : w = w' := by
  rw [← tbPair_sum w, ← tbPair_sum w']
  exact Finset.sum_congr rfl (fun j _ => by rw [h j])
/-! ## 4. The multiplication operator `tbRot10` -/

/-- The `j`-th complex coordinate of `ℂ⁵`, as a `1`-dimensional vector. -/
noncomputable def tbE1 (j : Fin 5) : E5 →L[ℝ] EuclideanSpace ℂ (Fin 1) :=
  ((EuclideanSpace.proj (𝕜 := ℂ) j).restrictScalars ℝ).smulRight
    (EuclideanSpace.single (𝕜 := ℂ) (0 : Fin 1) (1 : ℂ))

theorem tbE1_apply (j : Fin 5) (z : E5) :
    tbE1 j z = z.ofLp j • (EuclideanSpace.single (𝕜 := ℂ) (0 : Fin 1) (1 : ℂ)) := rfl

theorem tbE1_smul (j : Fin 5) (μ : ℂ) (z : E5) : tbE1 j (μ • z) = μ • tbE1 j z := by
  rw [tbE1_apply, tbE1_apply, WithLp.ofLp_smul]
  simp only [Pi.smul_apply, smul_eq_mul, mul_smul]
theorem tbPair_tbReal (j : Fin 5) (z : E5) : tbPair j (tbReal z) = expC (tbE1 j z) := by
  refine PiLp.ext (fun k => ?_)
  fin_cases k <;> simp [tbPair, tbReal_coord, expC_apply, tbE1_apply]
/-- **Multiplication by `μ` on each realified complex coordinate of `ℝ¹⁰`.** -/
noncomputable def tbRot10 (μ : ℂ) : Amb 10 →L[ℝ] Amb 10 :=
  ∑ j : Fin 5, (tbPairInj j).comp ((expCMul μ).comp (tbPair j))

theorem tbPair_tbRot10 (j : Fin 5) (μ : ℂ) (w : Amb 10) :
    tbPair j (tbRot10 μ w) = expCMul μ (tbPair j w) := by
  rw [tbRot10]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply, map_sum]
  rw [Finset.sum_eq_single j]
  · rw [tbPair_tbPairInj, if_pos rfl]
  · intro j' _ hj'
    rw [tbPair_tbPairInj, if_neg (fun h => hj' h.symm)]
  · intro h; exact absurd (Finset.mem_univ j) h

theorem expCMul_I_I (x : EuclideanSpace ℝ (Fin 2)) : expCMul Complex.I (expCMul Complex.I x) = -x := by
  rw [expCMul_apply, expCMul_apply]
  refine PiLp.ext (fun k => ?_)
  fin_cases k <;> simp <;> ring
theorem expCMul_decomp (μ : ℂ) (x : EuclideanSpace ℝ (Fin 2)) :
    expCMul μ x = μ.re • x + μ.im • expCMul Complex.I x := by
  rw [expCMul_apply, expCMul_apply]
  refine PiLp.ext (fun k => ?_)
  fin_cases k <;> simp <;> ring

theorem tbRot10_decomp (μ : ℂ) (w : Amb 10) :
    tbRot10 μ w = μ.re • w + μ.im • tbRot10 Complex.I w := by
  refine tbPair_ext fun j => ?_
  rw [tbPair_tbRot10, map_add, map_smul, map_smul, tbPair_tbRot10]
  exact expCMul_decomp μ (tbPair j w)

theorem tbRot10_I_I (w : Amb 10) : tbRot10 Complex.I (tbRot10 Complex.I w) = -w := by
  refine tbPair_ext fun j => ?_
  rw [tbPair_tbRot10, tbPair_tbRot10, expCMul_I_I, map_neg]

theorem tbPair_tbReal_smul (j : Fin 5) (μ : ℂ) (z : E5) :
    tbPair j (tbReal (μ • z)) = expCMul μ (tbPair j (tbReal z)) := by
  rw [tbPair_tbReal, tbPair_tbReal, tbE1_smul]
  refine PiLp.ext (fun k => ?_)
  fin_cases k <;>
    simp [expCMul_apply, expC_apply, PiLp.toLp_apply, Complex.mul_re, Complex.mul_im,
      PiLp.single_apply] <;> ring
theorem tbReal_smul (μ : ℂ) (z : E5) : tbReal (μ • z) = tbRot10 μ (tbReal z) := by
  refine tbPair_ext fun j => ?_
  rw [tbPair_tbRot10, tbPair_tbReal_smul]
/-! ## 5. The two blocks of `ℝ²⁰` -/

/-- The first block embedding `ℝ¹⁰ → ℝ²⁰`. -/
noncomputable def tbBlkL : Amb 10 →L[ℝ] Amb 20 :=
  ∑ i : Fin 10, (EuclideanSpace.proj (𝕜 := ℝ) i).smulRight
    (EuclideanSpace.single (𝕜 := ℝ) (Fin.castAdd 10 i) (1 : ℝ) : Amb 20)

/-- The second block embedding `ℝ¹⁰ → ℝ²⁰`. -/
noncomputable def tbBlkR : Amb 10 →L[ℝ] Amb 20 :=
  ∑ i : Fin 10, (EuclideanSpace.proj (𝕜 := ℝ) i).smulRight
    (EuclideanSpace.single (𝕜 := ℝ) (Fin.natAdd 10 i) (1 : ℝ) : Amb 20)

/-- The projection onto the first block. -/
noncomputable def tbUnL : Amb 20 →L[ℝ] Amb 10 :=
  ∑ i : Fin 10, (EuclideanSpace.proj (𝕜 := ℝ) (Fin.castAdd 10 i)).smulRight
    (EuclideanSpace.single (𝕜 := ℝ) i (1 : ℝ) : Amb 10)

/-- The projection onto the second block. -/
noncomputable def tbUnR : Amb 20 →L[ℝ] Amb 10 :=
  ∑ i : Fin 10, (EuclideanSpace.proj (𝕜 := ℝ) (Fin.natAdd 10 i)).smulRight
    (EuclideanSpace.single (𝕜 := ℝ) i (1 : ℝ) : Amb 10)

theorem tbBlkL_apply (w : Amb 10) :
    tbBlkL w = ∑ i : Fin 10,
      w.ofLp i • (EuclideanSpace.single (𝕜 := ℝ) (Fin.castAdd 10 i) (1 : ℝ) : Amb 20) := by
  rw [tbBlkL]
  rw [sum_apply]
  simp only [ContinuousLinearMap.smulRight_apply, tbProj_apply]
theorem tbBlkR_apply (w : Amb 10) :
    tbBlkR w = ∑ i : Fin 10,
      w.ofLp i • (EuclideanSpace.single (𝕜 := ℝ) (Fin.natAdd 10 i) (1 : ℝ) : Amb 20) := by
  rw [tbBlkR]
  rw [sum_apply]
  simp only [ContinuousLinearMap.smulRight_apply, tbProj_apply]
theorem tbBlkL_coord (w : Amb 10) (i : Fin 10) :
    (tbBlkL w).ofLp (Fin.castAdd 10 i) = w.ofLp i := by
  rw [tbBlkL_apply]
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · simp
  · intro i' _ hi'
    rw [single_coord_ne (fun h => hi' (Fin.castAdd_inj.mp h).symm)]
    simp
  · intro h; exact absurd (Finset.mem_univ i) h
theorem tbBlkL_coordR (w : Amb 10) (i : Fin 10) : (tbBlkL w).ofLp (Fin.natAdd 10 i) = 0 := by
  rw [tbBlkL_apply]
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_eq_zero fun i' _ => ?_
  have hne : Fin.natAdd 10 i ≠ Fin.castAdd 10 i' := by
    intro h; have := congrArg Fin.val h; simp at this; have := i'.isLt; omega
  rw [single_coord_ne hne]
  simp
theorem tbBlkR_coordR (w : Amb 10) (i : Fin 10) :
    (tbBlkR w).ofLp (Fin.natAdd 10 i) = w.ofLp i := by
  rw [tbBlkR_apply]
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · simp
  · intro i' _ hi'
    rw [single_coord_ne (fun h => hi' (Fin.natAdd_inj 10 |>.mp h).symm)]
    simp
  · intro h; exact absurd (Finset.mem_univ i) h
theorem tbBlkR_coordL (w : Amb 10) (i : Fin 10) : (tbBlkR w).ofLp (Fin.castAdd 10 i) = 0 := by
  rw [tbBlkR_apply]
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_eq_zero fun i' _ => ?_
  have hne : Fin.castAdd 10 i ≠ Fin.natAdd 10 i' := by
    intro h; have := congrArg Fin.val h; simp at this; have := i.isLt; omega
  rw [single_coord_ne hne]
  simp
theorem tbUnL_coord (x : Amb 20) (i : Fin 10) :
    (tbUnL x).ofLp i = x.ofLp (Fin.castAdd 10 i) := by
  rw [tbUnL, sum_apply]
  simp only [ContinuousLinearMap.smulRight_apply, tbProj_apply, WithLp.ofLp_sum,
    Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · simp
  · intro i' _ hi'
    rw [single_coord_ne (fun h => hi' h.symm)]
    simp
  · intro h; exact absurd (Finset.mem_univ i) h

theorem tbUnR_coord (x : Amb 20) (i : Fin 10) :
    (tbUnR x).ofLp i = x.ofLp (Fin.natAdd 10 i) := by
  rw [tbUnR, sum_apply]
  simp only [ContinuousLinearMap.smulRight_apply, tbProj_apply, WithLp.ofLp_sum,
    Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · simp
  · intro i' _ hi'
    rw [single_coord_ne (fun h => hi' h.symm)]
    simp
  · intro h; exact absurd (Finset.mem_univ i) h

theorem tbUnL_tbBlkL (w : Amb 10) : tbUnL (tbBlkL w) = w := by
  refine PiLp.ext (fun i => ?_)
  rw [tbUnL_coord, tbBlkL_coord]
theorem tbUnL_tbBlkR (w : Amb 10) : tbUnL (tbBlkR w) = 0 := by
  refine PiLp.ext (fun i => ?_)
  rw [tbUnL_coord, tbBlkR_coordL]
  rfl
theorem tbUnR_tbBlkR (w : Amb 10) : tbUnR (tbBlkR w) = w := by
  refine PiLp.ext (fun i => ?_)
  rw [tbUnR_coord, tbBlkR_coordR]
theorem tbBlkL_norm (w : Amb 10) : ‖tbBlkL w‖ = ‖w‖ := by
  have h1 : ‖tbBlkL w‖ ^ 2 = ∑ i : Fin 10, ‖w.ofLp i‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_add (a := 10) (b := 10)]
    rw [show (∑ i : Fin 10, ‖(tbBlkL w).ofLp (Fin.castAdd 10 i)‖ ^ 2)
        = ∑ i : Fin 10, ‖w.ofLp i‖ ^ 2 from
      Finset.sum_congr rfl (fun i _ => by rw [tbBlkL_coord])]
    rw [show (∑ i : Fin 10, ‖(tbBlkL w).ofLp (Fin.natAdd 10 i)‖ ^ 2) = 0 from
      Finset.sum_eq_zero (fun i _ => by rw [tbBlkL_coordR]; simp)]
    rw [add_zero]
  have h2 : ‖w‖ ^ 2 = ∑ i : Fin 10, ‖w.ofLp i‖ ^ 2 := PiLp.norm_sq_eq_of_L2 _ w
  nlinarith [norm_nonneg (tbBlkL w), norm_nonneg w]
theorem tbBlkR_norm (w : Amb 10) : ‖tbBlkR w‖ = ‖w‖ := by
  have h1 : ‖tbBlkR w‖ ^ 2 = ∑ i : Fin 10, ‖w.ofLp i‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_add (a := 10) (b := 10)]
    rw [show (∑ i : Fin 10, ‖(tbBlkR w).ofLp (Fin.castAdd 10 i)‖ ^ 2) = 0 from
      Finset.sum_eq_zero (fun i _ => by rw [tbBlkR_coordL]; simp)]
    rw [show (∑ i : Fin 10, ‖(tbBlkR w).ofLp (Fin.natAdd 10 i)‖ ^ 2)
        = ∑ i : Fin 10, ‖w.ofLp i‖ ^ 2 from
      Finset.sum_congr rfl (fun i _ => by rw [tbBlkR_coordR])]
    rw [zero_add]
  have h2 : ‖w‖ ^ 2 = ∑ i : Fin 10, ‖w.ofLp i‖ ^ 2 := PiLp.norm_sq_eq_of_L2 _ w
  nlinarith [norm_nonneg (tbBlkR w), norm_nonneg w]
theorem tbBlkL_inner (w w' : Amb 10) : inner ℝ (tbBlkL w) (tbBlkL w') = inner ℝ w w' := by
  have h : tbBlkL w + tbBlkL w' = tbBlkL (w + w') := (map_add tbBlkL w w').symm
  rw [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
    real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two, h,
    tbBlkL_norm, tbBlkL_norm, tbBlkL_norm]
theorem tbBlkR_inner (w w' : Amb 10) : inner ℝ (tbBlkR w) (tbBlkR w') = inner ℝ w w' := by
  have h : tbBlkR w + tbBlkR w' = tbBlkR (w + w') := (map_add tbBlkR w w').symm
  rw [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
    real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two, h,
    tbBlkR_norm, tbBlkR_norm, tbBlkR_norm]
theorem tbBlk_add_norm (w w' : Amb 10) :
    ‖tbBlkL w + tbBlkR w'‖ ^ 2 = ‖w‖ ^ 2 + ‖w'‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_add (a := 10) (b := 10),
    PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  congr 1
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [WithLp.ofLp_add, Pi.add_apply, tbBlkL_coord, tbBlkR_coordL, add_zero]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [WithLp.ofLp_add, Pi.add_apply, tbBlkL_coordR, tbBlkR_coordR, zero_add]
theorem tbBlkL_tbBlkR_inner (w w' : Amb 10) : inner ℝ (tbBlkL w) (tbBlkR w') = 0 := by
  have h1 := tbBlk_add_norm w w'
  have h2 := tbBlkL_norm w
  have h3 := tbBlkR_norm w'
  rw [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
    ← sq, ← sq, ← sq, h1, h2, h3]
  ring
/-! ## 6. The two-block frame -/

/-- The frame of the complex line of a nonzero representative, as a frame of `ℝ¹⁰`. -/
def tbLine (v : Fin 5 → ℂ) : Fin 2 → E5 := ![cfUnit v, -(Complex.I • cfUnit v)]

@[simp] theorem tbLine_zero (v : Fin 5 → ℂ) : tbLine v 0 = cfUnit v := rfl
@[simp] theorem tbLine_one (v : Fin 5 → ℂ) :
    tbLine v 1 = -(Complex.I • cfUnit v) := rfl

theorem tbLine_smul (v : Fin 5 → ℂ) (hv : v ≠ 0) {μ : ℂ} (hμ : ‖μ‖ = 1) :
    tbLine (μ • v) = μ • tbLine v := by
  funext a
  have h01 : a = 0 ∨ a = 1 := by fin_cases a <;> simp
  rcases h01 with h | h
  · rw [h, Pi.smul_apply, tbLine_zero, tbLine_zero, cfUnit_smul_unit hv hμ]
  · rw [h, Pi.smul_apply, tbLine_one, tbLine_one, cfUnit_smul_unit hv hμ, smul_neg]
    congr 1
    rw [smul_comm]
theorem tbLine_orthonormal (v : Fin 5 → ℂ) (hv : v ≠ 0) : Orthonormal ℝ (tbLine v) := by
  constructor
  · intro a
    have h01 : a = 0 ∨ a = 1 := by fin_cases a <;> simp
    rcases h01 with h | h <;> rw [h]
    · rw [tbLine_zero, cfUnit_norm hv]
    · rw [tbLine_one, norm_neg, norm_smul, Complex.norm_I, one_mul, cfUnit_norm hv]
  · intro a a' h
    have h01 : a = 0 ∨ a = 1 := by fin_cases a <;> simp
    have h01' : a' = 0 ∨ a' = 1 := by fin_cases a' <;> simp
    rcases h01 with ha | ha <;> rcases h01' with ha' | ha'
    · exact absurd (by rw [ha, ha'] : a = a') h
    · rw [ha, ha', tbLine_zero, tbLine_one, inner_neg_right, neg_eq_zero]
      exact real_inner_I_smul_self ℂ (cfUnit v)
    · rw [ha, ha', tbLine_zero, tbLine_one, inner_neg_left, neg_eq_zero, real_inner_comm]
      exact real_inner_I_smul_self ℂ (cfUnit v)
    · exact absurd (by rw [ha, ha'] : a = a') h
/-- The realified line frame in `ℝ¹⁰`. -/
def tbRealF (v : Fin 5 → ℂ) : Fin 2 → Amb 10 := fun a => tbReal (tbLine v a)

theorem tbRealF_orthonormal (v : Fin 5 → ℂ) (hv : v ≠ 0) : Orthonormal ℝ (tbRealF v) := by
  constructor
  · intro a
    show ‖tbReal (tbLine v a)‖ = 1
    rw [tbReal_norm]
    exact (tbLine_orthonormal v hv).1 a
  · intro a a' h
    show inner ℝ (tbReal (tbLine v a)) (tbReal (tbLine v a')) = 0
    rw [tbReal_inner]
    exact (tbLine_orthonormal v hv).2 h
theorem tbRot10_I_tbReal_I (v : Fin 5 → ℂ) :
    tbRot10 Complex.I (tbReal (Complex.I • cfUnit v)) = -tbRealF v 0 := by
  have h : tbReal (Complex.I • cfUnit v) = tbRot10 Complex.I (tbRealF v 0) := by
    rw [tbReal_smul]
    rfl
  rw [h, tbRot10_I_I]

theorem tbRot10_neg_I (v : Fin 5 → ℂ) :
    tbRot10 Complex.I (tbReal (-(Complex.I • cfUnit v))) = tbRealF v 0 := by
  have h : tbReal (-(Complex.I • cfUnit v)) = -(tbRot10 Complex.I (tbRealF v 0)) := by
    rw [map_neg, tbReal_smul]
    rfl
  rw [h, map_neg, tbRot10_I_I, neg_neg]
theorem tbRealF_one (v : Fin 5 → ℂ) :
    tbRealF v 1 = -tbRot10 Complex.I (tbRealF v 0) := by
  show tbReal (tbLine v 1) = -tbRot10 Complex.I (tbReal (tbLine v 0))
  rw [tbLine_one, tbLine_zero, map_neg, tbReal_smul]

theorem tbRealF_smul (v : Fin 5 → ℂ) (hv : v ≠ 0) {μ : ℂ} (hμ : ‖μ‖ = 1) :
    tbRealF (μ • v) = soActFun (k := 2) (m := 8) (probeRotMat μ) (tbRealF v) := by
  funext a
  have h01 : a = 0 ∨ a = 1 := by fin_cases a <;> simp
  rcases h01 with h | h
  · rw [h]
    show tbReal (tbLine (μ • v) 0) = soActFun (k := 2) (m := 8) (probeRotMat μ) (tbRealF v) 0
    rw [tbLine_smul v hv hμ, Pi.smul_apply, tbReal_smul, tbRot10_decomp,
      show soActFun (k := 2) (m := 8) (probeRotMat μ) (tbRealF v) 0
        = probeRotMat μ 0 0 • tbRealF v 0 + probeRotMat μ 1 0 • tbRealF v 1 from by
        simp only [soActFun, Fin.sum_univ_two],
      probeRotMat_zero_zero, probeRotMat_one_zero, tbRealF_one]
    simp only [neg_smul, smul_neg, neg_neg]
    abel
  · rw [h]
    show tbReal (tbLine (μ • v) 1) = soActFun (k := 2) (m := 8) (probeRotMat μ) (tbRealF v) 1
    rw [tbLine_smul v hv hμ, Pi.smul_apply, tbLine_one, smul_neg, map_neg, tbReal_smul,
      tbRot10_decomp,
      show soActFun (k := 2) (m := 8) (probeRotMat μ) (tbRealF v) 1
        = probeRotMat μ 0 1 • tbRealF v 0 + probeRotMat μ 1 1 • tbRealF v 1 from by
        simp only [soActFun, Fin.sum_univ_two],
      probeRotMat_zero_one, probeRotMat_one_one, tbRealF_one]
    rw [tbRot10_I_tbReal_I,
      show tbReal (Complex.I • cfUnit v) = tbRot10 Complex.I (tbRealF v 0) from by
        rw [tbReal_smul]
        rfl]
    simp only [neg_smul, smul_neg, neg_add, neg_neg]
    abel
/-- The frame of the two-block plane, indexed by `Fin 2 ⊕ Fin 2` (block, index). -/
def tbFrameB (v : Fin 5 → ℂ) : Fin 2 ⊕ Fin 2 → Amb 20 :=
  Sum.elim (fun a => tbBlkL (tbRealF v a)) (fun a => tbBlkR (tbRealF v a))

theorem tbFrameB_orthonormal (v : Fin 5 → ℂ) (hv : v ≠ 0) : Orthonormal ℝ (tbFrameB v) := by
  constructor
  · rintro (a | a)
    · rw [show tbFrameB v (Sum.inl a) = tbBlkL (tbRealF v a) from rfl, tbBlkL_norm]
      exact (tbRealF_orthonormal v hv).1 a
    · rw [show tbFrameB v (Sum.inr a) = tbBlkR (tbRealF v a) from rfl, tbBlkR_norm]
      exact (tbRealF_orthonormal v hv).1 a
  · rintro (a | a) (a' | a') h
    · rw [show tbFrameB v (Sum.inl a) = tbBlkL (tbRealF v a) from rfl,
        show tbFrameB v (Sum.inl a') = tbBlkL (tbRealF v a') from rfl, tbBlkL_inner]
      exact (tbRealF_orthonormal v hv).2 (fun hh => h (by rw [hh]))
    · rw [show tbFrameB v (Sum.inl a) = tbBlkL (tbRealF v a) from rfl,
        show tbFrameB v (Sum.inr a') = tbBlkR (tbRealF v a') from rfl, tbBlkL_tbBlkR_inner]
    · rw [show tbFrameB v (Sum.inr a) = tbBlkR (tbRealF v a) from rfl,
        show tbFrameB v (Sum.inl a') = tbBlkL (tbRealF v a') from rfl, real_inner_comm,
        tbBlkL_tbBlkR_inner]
    · rw [show tbFrameB v (Sum.inr a) = tbBlkR (tbRealF v a) from rfl,
        show tbFrameB v (Sum.inr a') = tbBlkR (tbRealF v a') from rfl, tbBlkR_inner]
      exact (tbRealF_orthonormal v hv).2 (fun hh => h (by rw [hh]))
/-- The index equivalence `Fin 2 ⊕ Fin 2 ≃ Fin 4`. -/
def tbS4 : Fin 2 ⊕ Fin 2 ≃ Fin 4 := finSumFinEquiv

/-- **The two-block frame** of a nonzero `v : ℂ⁵`: the real `4`-plane `L ⊕ L ⊂ ℂ⁵ ⊕ ℂ⁵`. -/
def tbFrame (v : Fin 5 → ℂ) : Fin 4 → Amb 20 := fun i => tbFrameB v (tbS4.symm i)

theorem tbFrame_orthonormal (v : Fin 5 → ℂ) (hv : v ≠ 0) : Orthonormal ℝ (tbFrame v) := by
  constructor
  · intro i
    exact (tbFrameB_orthonormal v hv).1 (tbS4.symm i)
  · intro i i' h
    exact (tbFrameB_orthonormal v hv).2 (fun hh => h (tbS4.symm.injective hh))
/-! ## 7. Continuity -/

theorem continuous_tbLine_subtype :
    Continuous (fun a : {v : Fin 5 → ℂ // v ≠ 0} => tbLine a.1) := by
  refine continuous_pi (fun i => ?_)
  fin_cases i
  · exact continuousOn_iff_continuous_domRestrict.mp continuousOn_cfUnit
  · exact ((continuousOn_iff_continuous_domRestrict.mp continuousOn_cfUnit).const_smul
      Complex.I).neg
theorem continuous_tbRealF_subtype :
    Continuous (fun a : {v : Fin 5 → ℂ // v ≠ 0} => tbRealF a.1) := by
  refine continuous_pi (fun i => ?_)
  exact (tbReal.continuous.comp ((continuous_apply i).comp continuous_tbLine_subtype)).congr
    (fun a => rfl)

theorem continuous_tbFrameB_subtype :
    Continuous (fun a : {v : Fin 5 → ℂ // v ≠ 0} => tbFrameB a.1) := by
  refine continuous_pi (fun i => ?_)
  rcases i with a | a
  · show Continuous fun a' : {v : Fin 5 → ℂ // v ≠ 0} => tbBlkL (tbRealF a'.1 a)
    exact tbBlkL.continuous.comp ((continuous_apply a).comp continuous_tbRealF_subtype)
  · show Continuous fun a' : {v : Fin 5 → ℂ // v ≠ 0} => tbBlkR (tbRealF a'.1 a)
    exact tbBlkR.continuous.comp ((continuous_apply a).comp continuous_tbRealF_subtype)
theorem continuous_tbFrame_subtype :
    Continuous (fun a : {v : Fin 5 → ℂ // v ≠ 0} => tbFrame a.1) := by
  refine continuous_pi (fun i => ?_)
  show Continuous fun a : {v : Fin 5 → ℂ // v ≠ 0} => tbFrameB a.1 (tbS4.symm i)
  exact ((continuous_apply (tbS4.symm i)).comp continuous_tbFrameB_subtype)

def tbFrameW (v : {v : Fin 5 → ℂ // v ≠ 0}) : Stiefel 4 16 :=
  ⟨tbFrame v.1, tbFrame_orthonormal v.1 v.2⟩

/-! ## 8. The `SO(4)`-equivariance and the map `ℂP⁴ → G̃r₄(ℝ²⁰)` -/

/-- The `SO(4)`-matrix `diag(ρ(μ), ρ(μ))` acting on the two-block frame. -/
noncomputable def tbRotMat (μ : ℂ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.reindex tbS4 tbS4 (Matrix.fromBlocks (probeRotMat μ) 0 0 (probeRotMat μ))

theorem tbRotMat_transpose_mul {μ : ℂ} (hμ : ‖μ‖ = 1) :
    (tbRotMat μ).transpose * tbRotMat μ = 1 := by
  have h : (Matrix.fromBlocks (probeRotMat μ) 0 0 (probeRotMat μ)).transpose
        * (Matrix.fromBlocks (probeRotMat μ) 0 0 (probeRotMat μ)) = 1 := by
    rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
      probeRotMat_transpose_mul hμ]
    simp only [Matrix.transpose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
    exact Matrix.fromBlocks_one
  rw [tbRotMat, Matrix.reindex_apply, Matrix.transpose_submatrix,
    Matrix.submatrix_mul_equiv _ _ tbS4.symm tbS4.symm tbS4.symm, h,
    Matrix.submatrix_one_equiv]
theorem tbRotMat_det {μ : ℂ} (hμ : ‖μ‖ = 1) : (tbRotMat μ).det = 1 := by
  rw [tbRotMat, Matrix.reindex_apply, Matrix.det_submatrix_equiv_self,
    Matrix.det_fromBlocks_zero₁₂, probeRotMat_det hμ, one_mul]
def tbSO (μ : ℂ) (hμ : ‖μ‖ = 1) : SOk 4 :=
  ⟨tbRotMat μ, tbRotMat_transpose_mul hμ, tbRotMat_det hμ⟩

theorem tbFrameB_smul (v : Fin 5 → ℂ) (hv : v ≠ 0) {μ : ℂ} (hμ : ‖μ‖ = 1) :
    tbFrameB (μ • v) = fun i => ∑ j : Fin 2 ⊕ Fin 2,
      (Matrix.fromBlocks (probeRotMat μ) 0 0 (probeRotMat μ)) j i • tbFrameB v j := by
  funext i
  rcases i with a | a
  · rw [show tbFrameB (μ • v) (Sum.inl a) = tbBlkL (tbRealF (μ • v) a) from rfl,
      tbRealF_smul v hv hμ]
    simp only [soActFun, map_sum, map_smul]
    rw [show (∑ j : Fin 2 ⊕ Fin 2, (Matrix.fromBlocks (probeRotMat μ) 0 0 (probeRotMat μ)) j
          (Sum.inl a) • tbFrameB v j)
        = ∑ b : Fin 2, probeRotMat μ b a • tbBlkL (tbRealF v b) from by
      rw [Fintype.sum_sum_type]
      simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply,
        zero_smul, Finset.sum_const_zero, add_zero]
      exact Finset.sum_congr rfl (fun b _ => rfl)]
  · rw [show tbFrameB (μ • v) (Sum.inr a) = tbBlkR (tbRealF (μ • v) a) from rfl,
      tbRealF_smul v hv hμ]
    simp only [soActFun, map_sum, map_smul]
    rw [show (∑ j : Fin 2 ⊕ Fin 2, (Matrix.fromBlocks (probeRotMat μ) 0 0 (probeRotMat μ)) j
          (Sum.inr a) • tbFrameB v j)
        = ∑ b : Fin 2, probeRotMat μ b a • tbBlkR (tbRealF v b) from by
      rw [Fintype.sum_sum_type]
      simp only [Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply,
        zero_smul, Finset.sum_const_zero, zero_add]
      exact Finset.sum_congr rfl (fun b _ => rfl)]
theorem tbFrame_smul_reindex (v : Fin 5 → ℂ) (hv : v ≠ 0) {μ : ℂ} (hμ : ‖μ‖ = 1) :
    tbFrame (μ • v) = soActFun (k := 4) (m := 16) (tbRotMat μ) (tbFrame v) := by
  funext i
  rw [show tbFrame (μ • v) i = tbFrameB (μ • v) (tbS4.symm i) from rfl,
    tbFrameB_smul v hv hμ]
  rw [show soActFun (k := 4) (m := 16) (tbRotMat μ) (tbFrame v) i
      = ∑ j : Fin 2 ⊕ Fin 2, (Matrix.fromBlocks (probeRotMat μ) 0 0 (probeRotMat μ)) j
          (tbS4.symm i) • tbFrameB v j from ?_]
  · simp only [soActFun, tbRotMat, Matrix.reindex_apply, Matrix.submatrix_apply, tbFrame]
    rw [← Equiv.sum_comp tbS4 (fun j : Fin 4 =>
      (Matrix.fromBlocks (probeRotMat μ) 0 0 (probeRotMat μ)) (tbS4.symm j)
        (tbS4.symm i) • tbFrameB v (tbS4.symm j))]
    exact Finset.sum_congr rfl (fun j _ => by simp)
theorem tbMap_wd :
    ∀ (a b : {v : Fin 5 → ℂ // v ≠ 0}) (t : ℂ), (a : Fin 5 → ℂ) = t • (b : Fin 5 → ℂ) →
      ogMk 4 16 (tbFrameW a) = ogMk 4 16 (tbFrameW b) := by
  intro a b t h
  by_cases ht : t = 0
  · rw [ht, zero_smul] at h
    exact absurd h a.2
  · have hμ : ‖t / ((‖t‖ : ℝ) : ℂ)‖ = 1 := norm_div_norm_eq_one ht
    have hline : tbLine (t • b.1) = tbLine ((t / ((‖t‖ : ℝ) : ℂ)) • b.1) := by
      funext a'
      have h01 : a' = 0 ∨ a' = 1 := by fin_cases a' <;> simp
      rcases h01 with h' | h'
      · rw [h', tbLine_zero, tbLine_zero, cfUnit_smul b.2 ht, cfUnit_smul_unit b.2 hμ]
      · rw [h', tbLine_one, tbLine_one, cfUnit_smul b.2 ht, cfUnit_smul_unit b.2 hμ]
    have hframe : tbFrame (t • b.1) = tbFrame ((t / ((‖t‖ : ℝ) : ℂ)) • b.1) := by
      unfold tbFrame tbFrameB tbRealF
      rw [hline]
    have hA : tbFrame a.1
        = soActFun (k := 4) (m := 16) (tbRotMat (t / ((‖t‖ : ℝ) : ℂ))) (tbFrame b.1) := by
      rw [h, hframe, tbFrame_smul_reindex b.1 b.2 hμ]
    have heq : tbFrameW a = (tbSO (t / ((‖t‖ : ℝ) : ℂ)) hμ).act (tbFrameW b) := by
      apply Subtype.ext
      exact hA
    rw [heq]
    exact Quotient.sound ⟨(tbSO (t / ((‖t‖ : ℝ) : ℂ)) hμ).transpose,
      (SOk.act_transpose_act _ (tbFrameW b)).symm⟩
/-- The underlying function of the two-block map. -/
noncomputable def tbMapFun (x : CP 4) : OG 4 16 :=
  Projectivization.lift (fun v : {v : Fin 5 → ℂ // v ≠ 0} => ogMk 4 16 (tbFrameW v))
    tbMap_wd x

theorem tbMapFun_mk (v : {v : Fin 5 → ℂ // v ≠ 0}) :
    tbMapFun (Projectivization.mk' ℂ v) = ogMk 4 16 (tbFrameW v) :=
  Projectivization.lift_mk _ _ v.1 v.2

theorem continuous_tbMapFun : Continuous tbMapFun := by
  have hq : Topology.IsQuotientMap (Projectivization.mk' ℂ :
      {v : Fin 5 → ℂ // v ≠ 0} → CP 4) := isQuotientMap_quotient_mk'
  have hφ : Continuous (fun v : {v : Fin 5 → ℂ // v ≠ 0} => ogMk 4 16 (tbFrameW v)) :=
    (ogMk 4 16).continuous.comp (Continuous.subtype_mk continuous_tbFrame_subtype
      (fun v => tbFrame_orthonormal v.1 v.2))
  have hcomp : tbMapFun ∘ (Projectivization.mk' ℂ :
        {v : Fin 5 → ℂ // v ≠ 0} → CP 4)
      = fun v => ogMk 4 16 (tbFrameW v) := funext (fun v => tbMapFun_mk v)
  rw [hq.continuous_iff, hcomp]
  exact hφ
/-- **The two-block map** `ℂP⁴ → G̃r₄(ℝ²⁰)`. -/
noncomputable def tbMap : C(CP 4, OG 4 16) := ⟨tbMapFun, continuous_tbMapFun⟩

theorem tbMap_apply (v : {v : Fin 5 → ℂ // v ≠ 0}) :
    tbMap (Projectivization.mk' ℂ v) = ogMk 4 16 (tbFrameW v) := tbMapFun_mk v

theorem tbMap_apply_uVec (i : Fin 5) (x : CP 4) (hx : x ∈ Work.Projective.chartSet i) :
    tbMap x = ogMk 4 16 (tbFrameW ⟨Work.Gen.uVec i x, Work.Gen.uVec_ne_zero i x⟩) := by
  have h2 := tbMap_apply ⟨Work.Gen.uVec i x, Work.Gen.uVec_ne_zero i x⟩
  rw [show Projectivization.mk' ℂ ⟨Work.Gen.uVec i x, Work.Gen.uVec_ne_zero i x⟩ = x
    from Work.Gen.cpMk_uVec i x hx] at h2
  exact h2
/-! ## 9. The comparison bundles -/

/-- The realification of the tautological line bundle of `ℂP⁴`, in the standard fibre `ℝ²`. -/
abbrev tbZL : RealBundle (CP 4) (Amb 2) (Fin 5) :=
  RealBundle.mapFibre expC (Work.Thom.realification (Work.Gen.tautLine 4))

/-- The rank-`4` real bundle `tbZL ⊕ tbZL` compared with `tbMap ^* γ`. -/
abbrev tbW : RealBundle (CP 4) (Amb 4) (Fin 5 × Fin 5) := Work.Whitney.whitneySumR tbZL tbZL

/-- The pullback of the tautological oriented `4`-plane bundle along `tbMap`. -/
abbrev tbZ : RealBundle (CP 4) (Amb 4) (ChartIdx 4 16) :=
  Work.Thom.bundleComap (tautologicalBundle 4 16) tbMap

end

end Work.ThomBordism.Grassmann
