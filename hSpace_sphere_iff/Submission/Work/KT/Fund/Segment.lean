import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Fund.Laurent
import Submission.Work.KT.isUnit_one_sub_of_matNorm_lt_one

/-!
# `Work.KT.Fund.Segment` — elementary matrix-norm and homotopy scaffolding

Definitions used by `Work.KT.Fund.laurent_approx`:

* `mNorm n A` — the `ℓ∞` operator norm `sup_i ∑_j ‖A i j‖` of a square matrix, as an `NNReal`.
  This is the matrix norm appearing in the hypothesis of
  `Work.KT.isUnit_one_sub_of_matNorm_lt_one`, so every Neumann-series estimate is phrased in it.
* `tC Y` — the parameter `t ∈ [0,1]` as a continuous `ℂ`-valued function on `Y × [0,1]`.
* `seg u V` — the linear segment `(1-t) • u + t • V` inside the ring of matrices over
  `C(Y × [0,1], ℂ)`.
-/

namespace Work.KT.Fund

open Matrix

noncomputable section

set_option linter.style.haveILetI false

/-- The `ℓ∞` operator norm of a square matrix, as an `NNReal`: `sup_i ∑_j ‖A i j‖`.
This is exactly the norm for which `Work.KT.isUnit_one_sub_of_matNorm_lt_one` is stated. -/
def mNorm {R : Type*} [NormedRing R] (n : ℕ) (A : Matrix (Fin n) (Fin n) R) : NNReal :=
  Finset.univ.sup fun i => ∑ j, ‖A i j‖₊

/-- Submultiplicativity of the `ℓ∞` operator norm, in the `Finset.sup` form used by
`Work.KT.isUnit_one_sub_of_matNorm_lt_one`. -/
lemma mNorm_mul_le {R : Type*} [NormedRing R] (n : ℕ) (A B : Matrix (Fin n) (Fin n) R) :
    mNorm n (A * B) ≤ mNorm n A * mNorm n B := by
  letI : NormedRing (Matrix (Fin n) (Fin n) R) := Matrix.linftyOpNormedRing
  have hA : ‖A‖₊ = mNorm n A := Matrix.linfty_opNNNorm_def A
  have hB : ‖B‖₊ = mNorm n B := Matrix.linfty_opNNNorm_def B
  have hAB : ‖A * B‖₊ = mNorm n (A * B) := Matrix.linfty_opNNNorm_def (A * B)
  rw [← hAB, ← hA, ← hB]
  exact nnnorm_mul_le A B

/-- Mapping a matrix through a ring homomorphism whose norms are non-increasing does not increase
the `ℓ∞` operator norm. -/
lemma mNorm_map_le {R S : Type*} [NormedRing R] [NormedRing S] (n : ℕ) (φ : R →+* S)
    (hφ : ∀ a, ‖φ a‖ ≤ ‖a‖) (A : Matrix (Fin n) (Fin n) R) :
    mNorm n (A.map φ) ≤ mNorm n A := by
  unfold mNorm
  refine Finset.sup_le fun i _ => ?_
  calc ∑ j, ‖(A.map φ) i j‖₊ = ∑ j, ‖φ (A i j)‖₊ := by simp [Matrix.map_apply]
    _ ≤ ∑ j, ‖A i j‖₊ := Finset.sum_le_sum fun j _ => by
        rw [← NNReal.coe_le_coe]
        simpa using hφ (A i j)
    _ ≤ Finset.univ.sup (fun i => ∑ j, ‖A i j‖₊) := Finset.le_sup (f := fun i => ∑ j, ‖A i j‖₊) (Finset.mem_univ i)

/-- Scalar multiplication of matrices does not increase the `ℓ∞` operator norm by more than
the norm of the scalar. -/
lemma mNorm_smul_le {R : Type*} [NormedRing R] (n : ℕ) (c : R)
    (A : Matrix (Fin n) (Fin n) R) : mNorm n (c • A) ≤ ‖c‖₊ * mNorm n A := by
  unfold mNorm
  refine Finset.sup_le fun i _ => ?_
  have h1 : ∀ j : Fin n, ‖(c • A) i j‖₊ ≤ ‖c‖₊ * ‖A i j‖₊ := by
    intro j
    simpa [Matrix.smul_apply] using nnnorm_mul_le c (A i j)
  calc ∑ j, ‖(c • A) i j‖₊ ≤ ∑ j, ‖c‖₊ * ‖A i j‖₊ := Finset.sum_le_sum fun j _ => h1 j
    _ = ‖c‖₊ * ∑ j, ‖A i j‖₊ := by rw [Finset.mul_sum]
    _ ≤ ‖c‖₊ * Finset.univ.sup (fun i => ∑ j, ‖A i j‖₊) :=
        mul_le_mul_of_nonneg_left (Finset.le_sup (f := fun i => ∑ j, ‖A i j‖₊) (Finset.mem_univ i)) (by positivity)

/-- A continuous `ℂ`-valued function on a topological space is a unit of `C(Z, ℂ)` exactly when it
vanishes nowhere. -/
lemma isUnit_iff_forall_ne_zero (Z : Type) [TopologicalSpace Z] (f : C(Z, ℂ)) :
    IsUnit f ↔ ∀ z, f z ≠ 0 := by
  constructor
  · rintro ⟨u, rfl⟩ z h
    have h1 : ((↑u : C(Z, ℂ)) * (↑u⁻¹ : C(Z, ℂ))) z = (1 : C(Z, ℂ)) z := by rw [u.mul_inv]
    rw [ContinuousMap.mul_apply, h, zero_mul] at h1
    simp at h1
  · intro hf
    have hcont : Continuous fun z => (f z)⁻¹ := f.continuous.inv₀ hf
    refine ⟨⟨f, ⟨fun z => (f z)⁻¹, hcont⟩, ?_, ?_⟩, rfl⟩
    · ext z; exact mul_inv_cancel₀ (hf z)
    · ext z; exact inv_mul_cancel₀ (hf z)

/-- The parameter `t ∈ [0,1]`, as a continuous `ℂ`-valued function on `Y × [0,1]`. -/
def tC (Y : Type) [TopologicalSpace Y] : C(Y × unitInterval, ℂ) :=
  ⟨fun p => ((p.2 : ℝ) : ℂ), by fun_prop⟩

@[simp] lemma tC_apply (Y : Type) [TopologicalSpace Y] (p : Y × unitInterval) :
    tC Y p = ((p.2 : ℝ) : ℂ) := rfl

@[simp] lemma tC_zero (Y : Type) [TopologicalSpace Y] (y : Y) :
    tC Y (y, 0) = 0 := rfl

@[simp] lemma tC_one (Y : Type) [TopologicalSpace Y] (y : Y) :
    tC Y (y, 1) = 1 := rfl

/-- The linear segment joining two matrices over `C(Y, ℂ)`, as a matrix over
`C(Y × [0,1], ℂ)`: entry `(i,j)` is the function `(y,t) ↦ (1-t) * u i j y + t * V i j y`. -/
def seg {Y : Type} [TopologicalSpace Y] {n : ℕ}
    (u V : Matrix (Fin n) (Fin n) C(Y, ℂ)) :
    Matrix (Fin n) (Fin n) C(Y × unitInterval, ℂ) :=
  fun i j => ⟨fun p => (1 - tC Y p) * u i j p.1 + tC Y p * V i j p.1, by
    have h1 : Continuous fun p : Y × unitInterval => u i j p.1 :=
      (u i j).continuous.comp continuous_fst
    have h2 : Continuous fun p : Y × unitInterval => V i j p.1 :=
      (V i j).continuous.comp continuous_fst
    have h3 : Continuous fun p : Y × unitInterval => tC Y p := (tC Y).continuous
    exact ((continuous_const.sub h3).mul h1).add (h3.mul h2)⟩

@[simp] lemma seg_apply_zero {Y : Type} [TopologicalSpace Y] {n : ℕ}
    (u V : Matrix (Fin n) (Fin n) C(Y, ℂ)) (i j : Fin n) (y : Y) :
    seg u V i j (y, 0) = u i j y := by simp [seg]

@[simp] lemma seg_apply_one {Y : Type} [TopologicalSpace Y] {n : ℕ}
    (u V : Matrix (Fin n) (Fin n) C(Y, ℂ)) (i j : Fin n) (y : Y) :
    seg u V i j (y, 1) = V i j y := by simp [seg]


/-- If `u` is an invertible matrix over a complete normed ring `R` and `V` is within `1/‖u⁻¹‖` of
`u` in the `ℓ∞` operator norm, then `V` is invertible (Neumann series:
`V = u * (1 - u⁻¹ (u - V))`). -/
lemma isUnit_of_mNorm_sub_lt_one {R : Type*} [NormedRing R] [CompleteSpace R] {n : ℕ}
    {u V : Matrix (Fin n) (Fin n) R} (hu : IsUnit u)
    (h : mNorm n (u - V) * mNorm n (hu.unit⁻¹).val < 1) : IsUnit V := by
  have huw : u * (hu.unit⁻¹).val = 1 := by
    have h1 : (↑hu.unit : Matrix (Fin n) (Fin n) R) * (hu.unit⁻¹).val = 1 := Units.mul_inv hu.unit
    rwa [hu.unit_spec] at h1
  have h' : mNorm n ((hu.unit⁻¹).val * (u - V)) < 1 := by
    calc mNorm n ((hu.unit⁻¹).val * (u - V))
        ≤ mNorm n (hu.unit⁻¹).val * mNorm n (u - V) := mNorm_mul_le n _ _
      _ = mNorm n (u - V) * mNorm n (hu.unit⁻¹).val := mul_comm _ _
      _ < 1 := h
  have h1 : IsUnit (1 - (hu.unit⁻¹).val * (u - V)) :=
    isUnit_one_sub_of_matNorm_lt_one _ h'
  have h2 : IsUnit (u * (1 - (hu.unit⁻¹).val * (u - V))) := hu.mul h1
  have heq : u * (1 - (hu.unit⁻¹).val * (u - V)) = V := by
    rw [mul_sub, mul_one, ← mul_assoc, huw, one_mul, sub_sub_cancel]
  rwa [heq] at h2

/-- The linear segment `(1-t) u + t V` joining an invertible matrix `u` over `C(Y, ℂ)` (`Y` compact)
to a matrix `V` within `1/‖u⁻¹‖` of it is a unit of the matrix ring over `C(Y × [0,1], ℂ)`. -/
lemma isUnit_seg {Y : Type} [TopologicalSpace Y] [CompactSpace Y] {n : ℕ}
    (u V : Matrix (Fin n) (Fin n) C(Y, ℂ)) (hu : IsUnit u)
    (h : mNorm n (u - V) * mNorm n (hu.unit⁻¹).val < 1) : IsUnit (seg u V) := by
  set w : Matrix (Fin n) (Fin n) C(Y, ℂ) := (hu.unit⁻¹).val with hwdef
  have huw : u * w = 1 := by
    have h1 : (↑hu.unit : Matrix (Fin n) (Fin n) C(Y, ℂ)) * w = 1 := by
      rw [hwdef]; exact Units.mul_inv hu.unit
    rwa [hu.unit_spec] at h1
  have hw' : mNorm n w = mNorm n (hu.unit⁻¹).val := by rw [hwdef]
  rw [Matrix.isUnit_iff_isUnit_det (seg u V),
    isUnit_iff_forall_ne_zero (Y × unitInterval) (seg u V).det]
  intro p
  have hdet : (seg u V).det p = ((seg u V).map (evalC p)).det := by
    have h1 : (evalC p) ((seg u V).det) = (seg u V).det p :=
      ContinuousMap.evalAlgHom_apply ℂ ℂ p (seg u V).det
    rw [← h1]
    show ((evalC p).toRingHom) ((seg u V).det)
        = ((seg u V).map (evalC p)).det
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
    rfl
  rw [hdet]
  refine IsUnit.ne_zero ((Matrix.isUnit_iff_isUnit_det _).mp ?_)
  have huwY : u.map (evalC p.1) * w.map (evalC p.1) = 1 := by
    rw [← Matrix.map_mul (f := evalC p.1), huw]
    exact Matrix.map_one (evalC p.1) (map_zero _) (map_one _)
  have step1 : (seg u V).map (evalC p) =
      (1 - tC Y p) • u.map (evalC p.1) + (tC Y p) • V.map (evalC p.1) := by
    ext i j
    simp only [seg, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
      ContinuousMap.evalAlgHom_apply, ContinuousMap.coe_mk, smul_eq_mul, tC]
  have step2 : (1 - tC Y p) • u.map (evalC p.1) + (tC Y p) • V.map (evalC p.1)
      = u.map (evalC p.1) - (tC Y p) • (u.map (evalC p.1) - V.map (evalC p.1)) := by
    rw [sub_smul, one_smul, smul_sub]
    abel
  have step3 : u.map (evalC p.1) *
        (1 - (tC Y p) • (w.map (evalC p.1) * (u.map (evalC p.1) - V.map (evalC p.1))))
      = u.map (evalC p.1) - (tC Y p) • (u.map (evalC p.1) - V.map (evalC p.1)) := by
    rw [mul_sub, mul_one, Matrix.mul_smul, ← mul_assoc, huwY, one_mul]
  have hZ : (seg u V).map (evalC p) = u.map (evalC p.1) *
      (1 - (tC Y p) • (w.map (evalC p.1) * (u.map (evalC p.1) - V.map (evalC p.1)))) :=
    step1.trans (step2.trans step3.symm)
  have hWV : mNorm n (w.map (evalC p.1)) ≤ mNorm n w := by
    refine mNorm_map_le n (evalC p.1).toRingHom ?_ w
    intro a
    simpa [evalC] using ContinuousMap.norm_coe_le_norm a p.1
  have hUV : mNorm n (u.map (evalC p.1) - V.map (evalC p.1)) ≤ mNorm n (u - V) := by
    rw [← Matrix.map_sub (evalC p.1) (fun a b => map_sub (evalC p.1) a b) u V]
    refine mNorm_map_le n (evalC p.1).toRingHom ?_ (u - V)
    intro a
    simpa [evalC] using ContinuousMap.norm_coe_le_norm a p.1
  have ht : ‖tC Y p‖ ≤ 1 := by
    have h1 : ‖tC Y p‖ = |(p.2 : ℝ)| := by
      rw [tC_apply]; exact RCLike.norm_ofReal _
    rw [h1, abs_of_nonneg p.2.2.1]
    exact p.2.2.2
  have ht' : ‖tC Y p‖₊ ≤ 1 := by
    rw [← NNReal.coe_le_coe]; simpa [coe_nnnorm] using ht
  have hZlt : mNorm n ((tC Y p) •
      (w.map (evalC p.1) * (u.map (evalC p.1) - V.map (evalC p.1)))) < 1 := by
    have hZ2 : mNorm n (w.map (evalC p.1)) * mNorm n (u.map (evalC p.1) - V.map (evalC p.1))
        ≤ mNorm n w * mNorm n (u - V) :=
      mul_le_mul hWV hUV (by positivity) (by positivity)
    calc mNorm n ((tC Y p) • (w.map (evalC p.1) *
            (u.map (evalC p.1) - V.map (evalC p.1))))
        ≤ ‖tC Y p‖₊ * mNorm n (w.map (evalC p.1) *
            (u.map (evalC p.1) - V.map (evalC p.1))) := mNorm_smul_le n _ _
      _ ≤ 1 * (mNorm n w * mNorm n (u - V)) :=
          mul_le_mul ht' ((mNorm_mul_le n _ _).trans hZ2) (by positivity) (by norm_num)
      _ = mNorm n (u - V) * mNorm n w := by ring
      _ = mNorm n (u - V) * mNorm n (hu.unit⁻¹).val := by rw [hw']
      _ < 1 := h
  rw [hZ]
  have h1 : IsUnit (u.map (evalC p.1)) := by
    have := IsUnit.map (RingHom.mapMatrix (evalC p.1).toRingHom) hu
    rwa [RingHom.mapMatrix_apply] at this
  exact h1.mul (isUnit_one_sub_of_matNorm_lt_one _ hZlt)

end

end Work.KT.Fund
