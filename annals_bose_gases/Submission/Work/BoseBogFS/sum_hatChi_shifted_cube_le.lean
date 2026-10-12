import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB6.Defs
import Submission.Work.BoseK15.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.sum_hatChi_shifted_cube_le`

**The shifted-cube Parseval row of the honest `hZP` slot** (`FINDING_honestZP_design.md`
§1(iv)): for the corpus localisation function `χ` (`Work.BoseK15.corpusBox`),

    Σ_{k : Fin 3 → Fin (gridD n)} χ̂(π·(2k − gridD n))² ≤ 1 ,

i.e. the sum of the *squared* `χ̂`-values over the shifted, truncated cube of the dual
lattice is at most one.

## The mathematics

`χ` is supported in the unit cell `[-1/2,1/2]³` (`BoxData.chi_supp`) and satisfies
`∫ χ² = 1`.  Write `p k = π(2k − M)`, `M = gridD n`.  The whole content is a single
application of **Bessel's inequality** on the unit cell:

* the momenta `p k` are pairwise congruent modulo `2πℤ³`
  (`p k − p k' = 2π·(k − k')`, `Work.BoseB4.vec`), so the complex exponentials
  `e^{i⟪p k,·⟫}` are *orthonormal* in `L²(unitCell)`:

      ∫_{unitCell} e^{i⟪p k − p k', x⟫} dx = δ_{k,k'} ,

  which is the real part statement `Work.BoseB4.integral_unitCell_cos_lattice`
  (the imaginary part is odd on the symmetric cell and hence vanishes — this is
  absorbed below by working with the real inner product of `ℂ` as an `ℝ`-Hilbert
  space);

* `χ` itself is the test vector, and

      χ̂(p k) = ∫_{unitCell} χ(x)·cos⟪p k, x⟫ dx = ⟪e^{i⟪p k,·⟫}, χ⟫_ℝ ,
      ‖χ‖²   = ∫_{unitCell} χ² = 1 .

Bessel then gives `Σ_k χ̂(p k)² ≤ ‖χ‖² = 1`.  No Poisson summation and no decay
estimate is used: the truncation is free because every summand is a square
(equivalently, the truncated cube is a *subsystem* of the orthonormal family).

## Implementation

The Hilbert space is `Lp ℂ 2 (volume.restrict unitCell)` regarded as a **real** inner
product space (`L2.inner_def` with `𝕜 = ℝ` gives
`⟪f, g⟫_ℝ = ∫ ⟪f x, g x⟫_ℝ`), so that the pointwise identities needed are the real
parts of elementary complex ones.  `Work.BoseB4.vec` is an `abbrev`-free `def`, hence
the small computational lemma `shiftedCubeMom_sub` before applying the lattice
orthogonality `Work.BoseB4.integral_unitCell_cos_lattice`.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBogFS

open scoped BigOperators Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The shifted-cube momentum -/

/-- The index set of the truncated, shifted cube: `Fin 3 → Fin (gridD n)`. -/
abbrev shiftedCubeIdx (n : ℕ) : Type := Fin 3 → Fin (Work.BoseB6.gridD n)

/-- The shifted-cube momentum `p k = π·(2kᵢ − gridD n)`, in the exact form in which it
appears in the target (half of `vec (2k − gridD n)`). -/
abbrev shiftedCubeMom (n : ℕ) (k : shiftedCubeIdx n) : ℝ³ :=
  (1 / 2 : ℝ) • Work.BoseB4.vec (fun i : Fin 3 => 2 * (k i : ℤ) - (Work.BoseB6.gridD n : ℤ))

/-- The measure of the unit cell. -/
abbrev cellLpMeasure : Measure ℝ³ := (volume : Measure ℝ³).restrict Work.BoseB4.unitCell

/-- The unit cell has finite measure, so every bounded measurable function is `L²` there. -/
lemma isFiniteMeasure_cellLpMeasure : IsFiniteMeasure cellLpMeasure :=
  (MeasureTheory.isFiniteMeasure_restrict).2
    (by rw [Work.BoseB4.volume_unitCell]; exact ENNReal.one_ne_top)

/-- **The difference of two shifted-cube momenta is a dual-lattice vector**:
`p k − p k' = 2π·(k − k') = vec (k − k')`. -/
lemma shiftedCubeMom_sub (n : ℕ) (k k' : shiftedCubeIdx n) :
    shiftedCubeMom n k - shiftedCubeMom n k' =
      Work.BoseB4.vec (fun i => (k i : ℤ) - (k' i : ℤ)) := by
  apply WithLp.ofLp_injective
  funext i
  simp only [shiftedCubeMom, Work.BoseB4.vec, WithLp.ofLp_sub, WithLp.ofLp_smul,
    WithLp.ofLp_toLp, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

/-- **Lattice orthogonality of the shifted-cube momenta on the unit cell**:
`∫_{unitCell} cos⟪p k − p k', x⟫ dx = δ_{k,k'}`. -/
lemma shiftedCube_integral_cos_sub (n : ℕ) (k k' : shiftedCubeIdx n) :
    ∫ x in Work.BoseB4.unitCell, Real.cos (inner ℝ (shiftedCubeMom n k - shiftedCubeMom n k') x)
      = if k = k' then 1 else 0 := by
  classical
  rw [shiftedCubeMom_sub n k k']
  simp only [Work.BoseB4.vec]
  rw [Work.BoseB4.integral_unitCell_cos_lattice]
  by_cases h : k = k'
  · subst h
    rw [if_pos (by funext i; simp), if_pos rfl]
  · have hz : ¬ ((fun i => (k i : ℤ) - (k' i : ℤ)) = 0) := by
      intro hz
      exact h (funext fun i => by
        have hi : (k i : ℤ) - (k' i : ℤ) = 0 := by simpa using congrFun hz i
        have : (k i : ℤ) = (k' i : ℤ) := by omega
        exact Fin.ext (by omega))
    rw [if_neg hz, if_neg h]

/-! ## 2. `χ̂` as an integral over the unit cell -/

/-- `χ` vanishes off the unit cell, so `χ̂` is the integral over the unit cell only. -/
lemma corpusBox_hatChi_eq_setIntegral (p : ℝ³) :
    Work.BoseK15.corpusBox.hatChi p
      = ∫ x in Work.BoseB4.unitCell, Work.BoseK15.corpusBox.chi x * Real.cos (inner ℝ p x) := by
  rw [Work.BoseB4.BoxData.hatChi]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    have h0 : Work.BoseK15.corpusBox.chi x = 0 := by
      by_contra h
      exact hx (Work.BoseK15.corpusBox.chi_supp (Function.mem_support.mpr h))
    rw [h0, zero_mul])).symm

/-! ## 3. The `L²(unitCell)` vectors -/

/-- The exponential `e^{i⟪p k, x⟫}` is in `L²` (it has modulus one). -/
lemma memLp_exp (n : ℕ) (k : shiftedCubeIdx n) :
    MemLp (fun x : ℝ³ => Complex.exp (((inner ℝ (shiftedCubeMom n k) x : ℝ) : ℂ) * Complex.I))
      2 cellLpMeasure := by
  haveI := isFiniteMeasure_cellLpMeasure
  refine MemLp.of_bound ?_ 1 ?_
  · exact (by fun_prop : Continuous fun x : ℝ³ =>
      Complex.exp (((inner ℝ (shiftedCubeMom n k) x : ℝ) : ℂ) * Complex.I)).aestronglyMeasurable
  · filter_upwards with x
    exact le_of_eq (Complex.norm_exp_ofReal_mul_I (inner ℝ (shiftedCubeMom n k) x))

/-- The corpus `χ`, as a complex-valued function, is in `L²(unitCell)`: it is continuous
on the compact unit cell (so bounded there) and vanishes outside it. -/
lemma memLp_chi :
    MemLp (fun x : ℝ³ => ((Work.BoseK15.corpusBox.chi x : ℝ) : ℂ)) 2 cellLpMeasure := by
  haveI := isFiniteMeasure_cellLpMeasure
  obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn (Work.BoseB4.isCompact_unitCell)
    (f := fun x : ℝ³ => ((Work.BoseK15.corpusBox.chi x : ℝ) : ℂ))
    ((Complex.continuous_ofReal.comp
      (Work.BoseB4.BoxData.chi_cont Work.BoseK15.corpusBox)).continuousOn)
  refine MemLp.of_bound ?_ C ?_
  · exact (Complex.continuous_ofReal.comp
      (Work.BoseB4.BoxData.chi_cont Work.BoseK15.corpusBox)).aestronglyMeasurable
  · filter_upwards with x
    by_cases hx : x ∈ Work.BoseB4.unitCell
    · exact hC x hx
    · have h0 : Work.BoseK15.corpusBox.chi x = 0 := by
        by_contra h
        exact hx (Work.BoseK15.corpusBox.chi_supp (Function.mem_support.mpr h))
      rw [h0]
      simp only [Complex.ofReal_zero, norm_zero]
      exact le_trans (norm_nonneg _) (hC 0 (by intro i; simp [Work.BoseB4.unitCell]))

/-- The `L²(unitCell)` vector `e^{i⟪p k,·⟫}`. -/
abbrev expVec (n : ℕ) (k : shiftedCubeIdx n) : Lp ℂ 2 cellLpMeasure :=
  MemLp.toLp _ (memLp_exp n k)

/-- The `L²(unitCell)` vector `χ`. -/
abbrev chiVec : Lp ℂ 2 cellLpMeasure := MemLp.toLp _ memLp_chi

/-! ## 4. The pointwise complex identities -/

/-- `⟪e^{iθ}, e^{iθ'}⟫_ℝ = cos (θ − θ')`. -/
lemma inner_exp_exp_pt (θ θ' : ℝ) :
    inner ℝ (Complex.exp ((θ : ℂ) * Complex.I)) (Complex.exp ((θ' : ℂ) * Complex.I))
      = Real.cos (θ - θ') := by
  rw [Complex.inner]
  have hconj : (starRingEnd ℂ) (Complex.exp ((θ : ℂ) * Complex.I))
      = Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_conj]
    congr 1
    rw [Complex.ext_iff]
    exact ⟨by simp [Complex.conj_ofReal, Complex.conj_I],
      by simp [Complex.conj_ofReal, Complex.conj_I]⟩
  rw [hconj, ← Complex.exp_add]
  rw [show (θ' : ℂ) * Complex.I + ((-θ : ℝ) : ℂ) * Complex.I
        = ((θ' - θ : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [Complex.exp_ofReal_mul_I_re]
  rw [show θ' - θ = -(θ - θ') by ring, Real.cos_neg]

/-- `⟪e^{iθ}, r⟫_ℝ = r·cos θ` for real `r`. -/
lemma inner_exp_chi_pt (θ r : ℝ) :
    inner ℝ (Complex.exp ((θ : ℂ) * Complex.I)) ((r : ℝ) : ℂ) = r * Real.cos θ := by
  rw [Complex.inner]
  have hconj : (starRingEnd ℂ) (Complex.exp ((θ : ℂ) * Complex.I))
      = Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_conj]
    congr 1
    rw [Complex.ext_iff]
    exact ⟨by simp [Complex.conj_ofReal, Complex.conj_I],
      by simp [Complex.conj_ofReal, Complex.conj_I]⟩
  rw [hconj, Complex.exp_ofReal_mul_I]
  simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
    sub_zero, add_zero, mul_one]

/-- `⟪r, r⟫_ℝ = r·r` for real `r`. -/
lemma inner_chi_chi_pt (r : ℝ) : inner ℝ ((r : ℝ) : ℂ) ((r : ℝ) : ℂ) = r * r := by
  rw [Complex.inner]
  simp [Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re]

/-! ## 5. The `L²` inner products -/

/-- **Orthonormality of the exponentials in `L²(unitCell)`**:
`⟪e^{i⟪p k,·⟫}, e^{i⟪p k',·⟫}⟫ = δ_{k,k'}`. -/
lemma inner_expVec_expVec (n : ℕ) (k k' : shiftedCubeIdx n) :
    inner ℝ (expVec n k) (expVec n k') = if k = k' then 1 else 0 := by
  rw [L2.inner_def]
  have h1 : (fun x => inner ℝ (((expVec n k : Lp ℂ 2 cellLpMeasure) : ℝ³ → ℂ) x)
      (((expVec n k' : Lp ℂ 2 cellLpMeasure) : ℝ³ → ℂ) x)) =ᵐ[cellLpMeasure]
      (fun x => Real.cos (inner ℝ (shiftedCubeMom n k - shiftedCubeMom n k') x)) := by
    filter_upwards [MemLp.coeFn_toLp (memLp_exp n k), MemLp.coeFn_toLp (memLp_exp n k')]
      with x hx hx'
    rw [hx, hx', inner_exp_exp_pt, inner_sub_left]
  rw [integral_congr_ae h1]
  exact shiftedCube_integral_cos_sub n k k'

/-- **The coefficient of `χ` against the exponential is `χ̂`**:
`⟪e^{i⟪p k,·⟫}, χ⟫_ℝ = χ̂(p k)`. -/
lemma inner_expVec_chiVec (n : ℕ) (k : shiftedCubeIdx n) :
    inner ℝ (expVec n k) chiVec = Work.BoseK15.corpusBox.hatChi (shiftedCubeMom n k) := by
  rw [L2.inner_def]
  have h1 : (fun x => inner ℝ (((expVec n k : Lp ℂ 2 cellLpMeasure) : ℝ³ → ℂ) x)
      (((chiVec : Lp ℂ 2 cellLpMeasure) : ℝ³ → ℂ) x)) =ᵐ[cellLpMeasure]
      (fun x => Work.BoseK15.corpusBox.chi x * Real.cos (inner ℝ (shiftedCubeMom n k) x)) := by
    filter_upwards [MemLp.coeFn_toLp (memLp_exp n k), MemLp.coeFn_toLp memLp_chi]
      with x hx hx'
    rw [hx, hx', inner_exp_chi_pt]
  rw [integral_congr_ae h1]
  exact (corpusBox_hatChi_eq_setIntegral (shiftedCubeMom n k)).symm

/-- **The norm of `χ` in `L²(unitCell)` is one**: `⟪χ, χ⟫ = ∫χ² = 1`. -/
lemma inner_chiVec_chiVec : inner ℝ chiVec chiVec = 1 := by
  rw [L2.inner_def]
  have h1 : (fun x => inner ℝ (((chiVec : Lp ℂ 2 cellLpMeasure) : ℝ³ → ℂ) x)
      (((chiVec : Lp ℂ 2 cellLpMeasure) : ℝ³ → ℂ) x)) =ᵐ[cellLpMeasure]
      (fun x => (Work.BoseK15.corpusBox.chi x) ^ 2) := by
    filter_upwards [MemLp.coeFn_toLp memLp_chi] with x hx
    rw [hx, inner_chi_chi_pt, sq]
  rw [integral_congr_ae h1]
  show (∫ x in Work.BoseB4.unitCell, (Work.BoseK15.corpusBox.chi x) ^ 2 ∂(volume : Measure ℝ³)) = 1
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    have h0 : Work.BoseK15.corpusBox.chi x = 0 := by
      by_contra h
      exact hx (Work.BoseK15.corpusBox.chi_supp (Function.mem_support.mpr h))
    rw [h0]
    ring)]
  exact Work.BoseK15.corpusBox.chi_int

/-! ## 6. Bessel and the target -/

/-- The exponentials form an orthonormal family of `L²(unitCell)`. -/
lemma orthonormal_expVec (n : ℕ) : Orthonormal ℝ (expVec n) := by
  constructor
  · intro k
    have h : inner ℝ (expVec n k) (expVec n k) = 1 := by
      rw [inner_expVec_expVec n k k, if_pos rfl]
    have h2 : ‖expVec n k‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq, h]
    rcases sq_eq_one_iff.mp h2 with h3 | h3
    · exact h3
    · linarith [norm_nonneg (expVec n k)]
  · intro k k' hne
    rw [inner_expVec_expVec n k k', if_neg hne]

/-- **The shifted-cube Parseval bound**, in the form of the momentum abbreviation. -/
theorem sum_hatChi_shiftedCubeMom_le (n : ℕ) :
    ∑ k : shiftedCubeIdx n, (Work.BoseK15.corpusBox.hatChi (shiftedCubeMom n k)) ^ 2 ≤ 1 := by
  have hb := Orthonormal.sum_inner_products_le (𝕜 := ℝ) chiVec (v := expVec n) (s := Finset.univ)
    (orthonormal_expVec n)
  have hnorm : ‖chiVec‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq, inner_chiVec_chiVec]
  calc ∑ k : shiftedCubeIdx n, (Work.BoseK15.corpusBox.hatChi (shiftedCubeMom n k)) ^ 2
      = ∑ k : shiftedCubeIdx n, ‖inner ℝ (expVec n k) chiVec‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro k _
        rw [inner_expVec_chiVec, Real.norm_eq_abs, sq_abs]
    _ ≤ ‖chiVec‖ ^ 2 := hb
    _ = 1 := hnorm

/-- **The shifted-cube Parseval row of the honest `hZP` slot** (FS's mode-lattice
truncation of `χ̂²`): the sum of `χ̂²` over the shifted cube `π(2k − gridD n)`,
`k : Fin 3 → Fin (gridD n)`, is at most one. -/
theorem sum_hatChi_shifted_cube_le (n : ℕ) :
    (∑ k : Fin 3 → Fin (Work.BoseB6.gridD n),
      (Work.BoseK15.corpusBox.hatChi
        ((1 / 2 : ℝ) • Work.BoseB4.vec
          (fun i : Fin 3 => 2 * (k i : ℤ) - (Work.BoseB6.gridD n : ℤ)))) ^ 2) ≤ 1 :=
  sum_hatChi_shiftedCubeMom_le n

end Work.BoseBogFS
