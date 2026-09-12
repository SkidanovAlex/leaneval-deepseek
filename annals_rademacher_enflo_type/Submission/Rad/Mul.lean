import Submission.Rad.Symm
set_option autoImplicit false
open Function MeasureTheory ProbabilityTheory Measure
open scoped ENNReal

noncomputable section

namespace RadType
open RademacherEnfloType

/-- The two-point set is finite. -/
instance instFintypeC : Fintype C := by
  classical
  unfold C
  have hf : ({-1, 1} : Set ℤ).Finite := by simp
  exact hf.fintype

/-- Multiplication on `{-1,1} ⊆ ℤ`. -/
instance : Mul C where
  mul x y := ⟨(x : ℤ) * (y : ℤ), by
    rcases val_eq x with hx | hx <;> rcases val_eq y with hy | hy <;> simp [hx, hy]⟩

@[simp] lemma mul_val_int (x y : C) : (((x * y : C) : ℤ)) = (x : ℤ) * (y : ℤ) := rfl

lemma mul_val_real (x y : C) : (((x * y : C) : ℤ) : ℝ) = ((x : C) : ℝ) * ((y : C) : ℝ) := by
  norm_num

@[simp] lemma one_mulC (x : C) : (⟨1, by simp⟩ : C) * x = x := by
  apply Subtype.ext
  rcases val_eq x with hx | hx <;> simp [hx]

@[simp] lemma mulC_one (x : C) : x * (⟨1, by simp⟩ : C) = x := by
  apply Subtype.ext
  rcases val_eq x with hx | hx <;> simp [hx]

@[simp] lemma neg_one_mulC (x : C) : (⟨-1, by simp⟩ : C) * x = -x := by
  apply Subtype.ext
  rcases val_eq x with hx | hx <;> simp [hx, neg_coe_int]

@[simp] lemma mulC_neg_one (x : C) : x * (⟨-1, by simp⟩ : C) = -x := by
  apply Subtype.ext
  rcases val_eq x with hx | hx <;> simp [hx, neg_coe_int]

@[simp] lemma mulC_mulC (x y : C) : x * (x * y) = y := by
  apply Subtype.ext
  rcases val_eq x with hx | hx <;> rcases val_eq y with hy | hy <;> simp [hx, hy]

@[simp] lemma mulC_comm (x y : C) : x * y = y * x := by
  apply Subtype.ext
  rcases val_eq x with hx | hx <;> rcases val_eq y with hy | hy <;> simp [hx, hy]

@[simp] lemma mulC_sq (x : C) : x * x = ⟨1, by simp⟩ := by
  apply Subtype.ext
  rcases val_eq x with hx | hx <;> simp [hx, neg_coe_int]

@[simp] lemma mulC_neg (x : C) : x * (-x : C) = ⟨-1, by simp⟩ := by
  apply Subtype.ext
  rcases val_eq x with hx | hx <;> simp [hx, neg_coe_int]

@[simp] lemma mulC_flip (x y : C) : -x * y = -(x * y) := by
  apply Subtype.ext
  rcases val_eq x with hx | hx <;> rcases val_eq y with hy | hy <;> simp [hx, hy, neg_coe_int]

@[simp] lemma mulC_neg_right (x y : C) : x * (-y : C) = -(x * y) := by
  apply Subtype.ext
  rcases val_eq x with hx | hx <;> rcases val_eq y with hy | hy <;> simp [hx, hy, neg_coe_int]

/-- Coordinatewise multiplication of two cube points. -/
def mulΩ {n : ℕ} (x ξ : Ω n) : Ω n := fun j => x j * ξ j

@[simp] lemma mulΩ_apply {n : ℕ} (x ξ : Ω n) (j : Fin n) : (mulΩ x ξ) j = x j * ξ j := rfl

/-- Multiplying by a cube point is an involution. -/
@[simp] lemma mulΩ_mulΩ {n : ℕ} (x ξ : Ω n) : mulΩ x (mulΩ x ξ) = ξ := by
  ext j
  simp

@[simp] lemma mulΩ_comm {n : ℕ} (x ξ : Ω n) : mulΩ x ξ = mulΩ ξ x := by
  ext j
  simp

/-- Multiplying by `x` is injective. -/
lemma mulΩ_injective {n : ℕ} (x : Ω n) : Function.Injective (fun ξ : Ω n => mulΩ x ξ) := by
  intro a b h
  have h' := congrArg (fun z : Ω n => mulΩ x z) h
  simpa using h'

/-- Multiplying by `x` is surjective. -/
lemma mulΩ_surjective {n : ℕ} (x : Ω n) : Function.Surjective (fun ξ : Ω n => mulΩ x ξ) := by
  intro y
  refine ⟨mulΩ x y, ?_⟩
  simp

/-- The coordinate maps `z ↦ x*z` are measurable. -/
lemma measurable_mul_left {n : ℕ} (x : Ω n) : Measurable (fun ξ : Ω n => mulΩ x ξ) := by
  fun_prop

/-- Flipping a coordinate commutes with multiplication: `flip_j (x·ξ) = x·flip_j ξ`. -/
lemma flip_mulΩ {n : ℕ} (x ξ : Ω n) (j : Fin n) :
    flip j (mulΩ x ξ) = mulΩ x (flip j ξ) := by
  ext i
  by_cases h : i = j
  · subst i
    simp [flip]
  · simp [flip, h]

/-- Negation commutes with multiplication by `x`: `negΩ (x·ξ) = x·negΩ ξ`. -/
lemma neg_mulΩ {n : ℕ} (x ξ : Ω n) :
    negΩ (mulΩ x ξ) = mulΩ x (negΩ ξ) := by
  ext i
  simp

/-- The uniform cube measure is invariant under left multiplication by any cube point. -/
lemma map_mul_cube {n : ℕ} (x : Ω n) :
    (rademacherProductDistribution (Fin n)).map (fun ξ : Ω n => mulΩ x ξ)
      = rademacherProductDistribution (Fin n) := by
  unfold rademacherProductDistribution
  rw [show (fun ξ : Ω n => mulΩ x ξ) = (fun (ξ : Fin n → C) (i : Fin n) => x i * ξ i) by rfl]
  rw [MeasureTheory.Measure.infinitePi_map_pi
    (μ := fun _ : Fin n => rademacherDistribution) (f := fun i (z : C) => x i * z)]
  · have hfam : (fun i : Fin n => (rademacherDistribution).map (fun z : C => x i * z)) =
        (fun _ : Fin n => rademacherDistribution) := by
      funext i
      rcases val_eq (x i) with hx | hx
      · have hf : (fun z : C => z * x i) = id := by
          funext z
          apply Subtype.ext
          rw [mul_val_int]
          simp [hx]
        simp [hf]
      · have hf : (fun z : C => z * x i) = fun z : C => -z := by
          funext z
          apply Subtype.ext
          rw [mul_val_int, neg_coe_int]
          simp [hx]
        simp [hf, map_neg_rademacher]
    rw [hfam]
  · intro i
    fun_prop

/-- `x ↦ x·ξ` preserves the uniform cube measure (fixed ξ). -/
lemma map_mul_cube_right {n : ℕ} (ξ : Ω n) :
    (rademacherProductDistribution (Fin n)).map (fun x : Ω n => mulΩ x ξ)
      = rademacherProductDistribution (Fin n) := by
  have : (fun x : Ω n => mulΩ x ξ) = fun x : Ω n => mulΩ ξ x := by
    apply funext; intro x; exact mulΩ_comm x ξ
  rw [this]
  exact map_mul_cube ξ

lemma measurePreserving_mul_cube_right {n : ℕ} (ξ : Ω n) :
    MeasurePreserving (fun x : Ω n => mulΩ x ξ)
      (rademacherProductDistribution (Fin n)) (rademacherProductDistribution (Fin n)) where
  measurable := by
    rw [show (fun x : Ω n => mulΩ x ξ) = fun x : Ω n => mulΩ ξ x by
      apply funext; intro x; exact mulΩ_comm x ξ]
    exact measurable_mul_left ξ
  map_eq := map_mul_cube_right ξ

lemma measurePreserving_mul_cube_left {n : ℕ} (x : Ω n) :
    MeasurePreserving (fun ξ : Ω n => mulΩ x ξ)
      (rademacherProductDistribution (Fin n)) (rademacherProductDistribution (Fin n)) where
  measurable := measurable_mul_left x
  map_eq := map_mul_cube x

/-- The point `1` of the cube. -/
def cOne : C := ⟨(1 : ℤ), by norm_num⟩

/-- The point `-1` of the cube. -/
def cNegOne : C := ⟨(-1 : ℤ), by norm_num⟩

lemma mem_two (x : C) : x = cOne ∨ x = cNegOne := by
  rcases val_eq x with hx | hx
  · left; apply Subtype.ext; simpa [cOne] using hx
  · right; apply Subtype.ext; simpa [cNegOne] using hx

lemma cOne_ne_cNegOne : cOne ≠ cNegOne := by
  intro h
  have h' := congrArg (fun z : C => (z : ℤ)) h
  norm_num [cOne, cNegOne] at h'

lemma cNegOne_ne_cOne : cNegOne ≠ cOne := by
  exact fun h => cOne_ne_cNegOne h.symm

lemma one_subtype_eq_cOne : (⟨(1 : ℤ), by decide⟩ : C) = cOne := by
  apply Subtype.ext
  rfl

@[simp] lemma cOne_int : (cOne : ℤ) = 1 := rfl

@[simp] lemma cNegOne_int : (cNegOne : ℤ) = -1 := rfl

@[simp] lemma cOne_real : ((cOne : C) : ℝ) = 1 := by norm_num [cOne]

@[simp] lemma cNegOne_real : ((cNegOne : C) : ℝ) = -1 := by norm_num [cNegOne]

lemma negOne_subtype_eq_cNegOne : (⟨(-1 : ℤ), by decide⟩ : C) = cNegOne := by
  apply Subtype.ext
  rfl

lemma univ_C_eq : (Finset.univ : Finset C) = {cOne, cNegOne} := by
  classical
  ext x
  constructor
  · intro hx
    rcases mem_two x with hx' | hx' <;> simp [hx']
  · intro hx
    exact Finset.mem_univ x

/-- A sum over the two-point set is the sum of its two values. -/
lemma sum_univ_two {R : Type*} [AddCommMonoid R] (f : C → R) :
    (Finset.univ : Finset C).sum f = f cOne + f cNegOne := by
  classical
  rw [univ_C_eq]
  simp [cOne_ne_cNegOne]


end RadType

end
