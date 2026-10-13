/-
  Work.WilCrux.C1AsmDefs — the coordinate vocabulary of the `C¹` assembly (map node N4e).

  The space `ℝ^{a+b}` is the product of the *parameter block* `ℝ^a` and the *fibre block* `ℝ^b`
  glued along `Fin.append`.  This file provides:

  * `parIncl a b`, `fibIncl a b` — the two inclusions `h ↦ Fin.append h 0`,
    `k ↦ Fin.append 0 k`, as continuous linear maps;
  * `parProj a b`, `fibProj a b` — the two projections;
  * `pairCLM a b φ ψ` — the continuous linear functional `v ↦ φ (parProj v) + ψ (fibProj v)`
    on `ℝ^{a+b}` obtained by pairing a functional on each block, together with its norm bound
    `‖pairCLM φ ψ‖ ≤ ‖φ‖ + ‖ψ‖` (which is what makes continuity statements transfer);

  and their coordinate calculus.
-/
import Mathlib
import Submission.Work.WilG4c.StepCleanDefs

set_option autoImplicit false
noncomputable section
open Classical
open scoped Topology

namespace Work.WilCrux

/-! ## 1. The two blocks of `ℝ^{a+b}` -/

/-- The inclusion of the parameter block: `h ↦ Fin.append h 0`. -/
def parIncl (a b : ℕ) : (Fin a → ℝ) →L[ℝ] (Fin (a + b) → ℝ) :=
  ContinuousLinearMap.pi (fun k : Fin (a + b) =>
    Fin.addCases (motive := fun _ : Fin (a + b) => (Fin a → ℝ) →L[ℝ] ℝ)
      (fun i => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin a => ℝ) i)
      (fun _ => 0) k)

/-- The inclusion of the fibre block: `k ↦ Fin.append 0 k`. -/
def fibIncl (a b : ℕ) : (Fin b → ℝ) →L[ℝ] (Fin (a + b) → ℝ) :=
  ContinuousLinearMap.pi (fun k : Fin (a + b) =>
    Fin.addCases (motive := fun _ : Fin (a + b) => (Fin b → ℝ) →L[ℝ] ℝ)
      (fun _ => 0)
      (fun j => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin b => ℝ) j) k)

/-- The projection onto the parameter block. -/
def parProj (a b : ℕ) : (Fin (a + b) → ℝ) →L[ℝ] (Fin a → ℝ) :=
  ContinuousLinearMap.pi (fun i : Fin a =>
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (a + b) => ℝ) (Fin.castAdd b i))

/-- The projection onto the fibre block. -/
def fibProj (a b : ℕ) : (Fin (a + b) → ℝ) →L[ℝ] (Fin b → ℝ) :=
  ContinuousLinearMap.pi (fun j : Fin b =>
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (a + b) => ℝ) (Fin.natAdd a j))

/-! ## 2. Coordinate calculus -/

@[simp] theorem parIncl_apply (a b : ℕ) (h : Fin a → ℝ) (k : Fin (a + b)) :
    parIncl a b h k = Fin.append h 0 k := by
  rw [parIncl, ContinuousLinearMap.pi_apply]
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;> simp

@[simp] theorem fibIncl_apply (a b : ℕ) (h : Fin b → ℝ) (k : Fin (a + b)) :
    fibIncl a b h k = Fin.append 0 h k := by
  rw [fibIncl, ContinuousLinearMap.pi_apply]
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;> simp

@[simp] theorem parProj_apply (a b : ℕ) (v : Fin (a + b) → ℝ) (i : Fin a) :
    parProj a b v i = v (Fin.castAdd b i) := by
  rw [parProj, ContinuousLinearMap.pi_apply]
  rfl

@[simp] theorem fibProj_apply (a b : ℕ) (v : Fin (a + b) → ℝ) (j : Fin b) :
    fibProj a b v j = v (Fin.natAdd a j) := by
  rw [fibProj, ContinuousLinearMap.pi_apply]
  rfl

theorem parIncl_eq (a b : ℕ) (h : Fin a → ℝ) : parIncl a b h = Fin.append h 0 :=
  funext (parIncl_apply a b h)

theorem fibIncl_eq (a b : ℕ) (h : Fin b → ℝ) : fibIncl a b h = Fin.append 0 h :=
  funext (fibIncl_apply a b h)

/-- The block decomposition of a vector of `ℝ^{a+b}`. -/
theorem append_eq_parIncl_add_fibIncl (a b : ℕ) (w : Fin a → ℝ) (z : Fin b → ℝ) :
    Fin.append w z = parIncl a b w + fibIncl a b z := by
  funext k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;>
    simp [parIncl_apply, fibIncl_apply, Fin.append_left, Fin.append_right]

theorem parProj_append (a b : ℕ) (w : Fin a → ℝ) (z : Fin b → ℝ) :
    parProj a b (Fin.append w z) = w := by
  funext i; simp

theorem fibProj_append (a b : ℕ) (w : Fin a → ℝ) (z : Fin b → ℝ) :
    fibProj a b (Fin.append w z) = z := by
  funext j; simp

theorem parProj_parIncl (a b : ℕ) (h : Fin a → ℝ) : parProj a b (parIncl a b h) = h := by
  funext i; simp [parIncl_eq]

theorem fibProj_parIncl (a b : ℕ) (h : Fin a → ℝ) : fibProj a b (parIncl a b h) = 0 := by
  funext j; simp [parIncl_eq]

theorem parProj_fibIncl (a b : ℕ) (h : Fin b → ℝ) : parProj a b (fibIncl a b h) = 0 := by
  funext i; simp [fibIncl_eq]

theorem fibProj_fibIncl (a b : ℕ) (h : Fin b → ℝ) : fibProj a b (fibIncl a b h) = h := by
  funext j; simp [fibIncl_eq]

/-- Recomposition: `parIncl ∘ parProj + fibIncl ∘ fibProj = id`. -/
theorem parIncl_parProj_add_fibIncl_fibProj (a b : ℕ) (v : Fin (a + b) → ℝ) :
    parIncl a b (parProj a b v) + fibIncl a b (fibProj a b v) = v := by
  funext k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;> simp

theorem norm_parProj_le (a b : ℕ) (v : Fin (a + b) → ℝ) : ‖parProj a b v‖ ≤ ‖v‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg v)]
  intro i
  rw [parProj_apply]
  exact norm_le_pi_norm v _

theorem norm_fibProj_le (a b : ℕ) (v : Fin (a + b) → ℝ) : ‖fibProj a b v‖ ≤ ‖v‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg v)]
  intro j
  rw [fibProj_apply]
  exact norm_le_pi_norm v _

theorem norm_parIncl_le (a b : ℕ) (h : Fin a → ℝ) : ‖parIncl a b h‖ = ‖h‖ := by
  apply le_antisymm
  · rw [parIncl_eq, pi_norm_le_iff_of_nonneg (norm_nonneg h)]
    intro k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · rw [Fin.append_left]; exact norm_le_pi_norm h i
    · rw [Fin.append_right]; simp
  · have key : ‖h‖ = ‖parProj a b (parIncl a b h)‖ := by rw [parProj_parIncl]
    rw [key]
    exact norm_parProj_le a b (parIncl a b h)

/-! ## 3. The pairing of two functionals -/

/-- The continuous linear functional on `ℝ^{a+b}` obtained from a functional `φ` on the
parameter block and a functional `ψ` on the fibre block: `v ↦ φ (parProj v) + ψ (fibProj v)`. -/
def pairCLM (a b : ℕ) (φ : (Fin a → ℝ) →L[ℝ] ℝ) (ψ : (Fin b → ℝ) →L[ℝ] ℝ) :
    (Fin (a + b) → ℝ) →L[ℝ] ℝ :=
  φ.comp (parProj a b) + ψ.comp (fibProj a b)

@[simp] theorem pairCLM_apply (a b : ℕ) (φ : (Fin a → ℝ) →L[ℝ] ℝ)
    (ψ : (Fin b → ℝ) →L[ℝ] ℝ) (v : Fin (a + b) → ℝ) :
    pairCLM a b φ ψ v = φ (parProj a b v) + ψ (fibProj a b v) := rfl

@[simp] theorem pairCLM_parIncl (a b : ℕ) (φ : (Fin a → ℝ) →L[ℝ] ℝ)
    (ψ : (Fin b → ℝ) →L[ℝ] ℝ) (h : Fin a → ℝ) :
    pairCLM a b φ ψ (parIncl a b h) = φ h := by
  simp [pairCLM, parProj_parIncl, fibProj_parIncl]

@[simp] theorem pairCLM_fibIncl (a b : ℕ) (φ : (Fin a → ℝ) →L[ℝ] ℝ)
    (ψ : (Fin b → ℝ) →L[ℝ] ℝ) (h : Fin b → ℝ) :
    pairCLM a b φ ψ (fibIncl a b h) = ψ h := by
  simp [pairCLM, parProj_fibIncl, fibProj_fibIncl]

theorem pairCLM_sub (a b : ℕ) (φ φ' : (Fin a → ℝ) →L[ℝ] ℝ) (ψ ψ' : (Fin b → ℝ) →L[ℝ] ℝ) :
    pairCLM a b φ ψ - pairCLM a b φ' ψ' = pairCLM a b (φ - φ') (ψ - ψ') := by
  ext v
  simp only [pairCLM_apply, sub_apply, add_apply]
  ring

theorem pairCLM_smul (a b : ℕ) (c : ℝ) (φ : (Fin a → ℝ) →L[ℝ] ℝ) (ψ : (Fin b → ℝ) →L[ℝ] ℝ) :
    c • pairCLM a b φ ψ = pairCLM a b (c • φ) (c • ψ) := by
  ext v; simp [pairCLM]

/-- The operator-norm bound that transfers continuity statements to the paired functional. -/
theorem norm_pairCLM_le (a b : ℕ) (φ : (Fin a → ℝ) →L[ℝ] ℝ) (ψ : (Fin b → ℝ) →L[ℝ] ℝ) :
    ‖pairCLM a b φ ψ‖ ≤ ‖φ‖ + ‖ψ‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (add_nonneg (norm_nonneg φ) (norm_nonneg ψ))
    fun v => ?_
  rw [pairCLM_apply]
  calc ‖φ (parProj a b v) + ψ (fibProj a b v)‖
      ≤ ‖φ (parProj a b v)‖ + ‖ψ (fibProj a b v)‖ := norm_add_le _ _
    _ ≤ ‖φ‖ * ‖parProj a b v‖ + ‖ψ‖ * ‖fibProj a b v‖ :=
        add_le_add (φ.le_opNorm _) (ψ.le_opNorm _)
    _ ≤ ‖φ‖ * ‖v‖ + ‖ψ‖ * ‖v‖ :=
        add_le_add (mul_le_mul_of_nonneg_left (norm_parProj_le a b v) (norm_nonneg φ))
          (mul_le_mul_of_nonneg_left (norm_fibProj_le a b v) (norm_nonneg ψ))
    _ = (‖φ‖ + ‖ψ‖) * ‖v‖ := by rw [add_mul]

end Work.WilCrux
