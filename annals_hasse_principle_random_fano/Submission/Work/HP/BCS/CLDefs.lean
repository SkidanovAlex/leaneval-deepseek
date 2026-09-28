import Mathlib
import Submission.Work.HP.BCS.Defs

/-!
# Support definitions for `Work.HP.BCS.count_from_layer`

The half-open fundamental domain `fund Ψ = Ψ '' [0,1)^k` of the lattice `Λ = Ψ '' ℤ^k`, together
with elementary lemmas about the lattice embedding `toEk : (Fin k → ℤ) → ℝ^k`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped Pointwise

namespace Work.HP.BCS

variable {k : ℕ}

/-- The half-open fundamental domain `Ψ '' [0,1)^k` of the lattice `Ψ '' ℤ^k`, for `Ψ` a linear
endomorphism of `ℝ^k`. -/
def fund (Ψ : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)) :
    Set (EuclideanSpace ℝ (Fin k)) :=
  Ψ '' unitCube k

lemma mem_fund_iff {Ψ : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)}
    {x : EuclideanSpace ℝ (Fin k)} : x ∈ fund Ψ ↔ ∃ t ∈ unitCube k, Ψ t = x := Iff.rfl

lemma mem_unitCube_iff {x : EuclideanSpace ℝ (Fin k)} :
    x ∈ unitCube k ↔ ∀ i, x.ofLp i ∈ Set.Ico (0 : ℝ) 1 := Iff.rfl

/-! ### The lattice embedding `toEk` -/

@[simp] lemma toEk_add (c c' : Fin k → ℤ) : toEk (c + c') = toEk c + toEk c' := by
  have h1 : (fun i => ((c + c') i : ℝ)) = (fun i => (c i : ℝ)) + fun i => (c' i : ℝ) := by
    ext i; simp [Pi.add_apply, Int.cast_add]
  rw [toEk, h1, WithLp.toLp_add]
  rfl

@[simp] lemma toEk_zero : toEk (0 : Fin k → ℤ) = 0 := by
  rw [toEk, ← WithLp.toLp_zero]
  congr
  ext i; simp

@[simp] lemma toEk_neg (c : Fin k → ℤ) : toEk (-c) = -toEk c := by
  have h1 : (fun i => ((-c) i : ℝ)) = -(fun i => (c i : ℝ)) := by
    ext i; simp [Pi.neg_apply]
  rw [toEk, h1, WithLp.toLp_neg]
  rfl

@[simp] lemma toEk_sub (c c' : Fin k → ℤ) : toEk (c - c') = toEk c - toEk c' := by
  rw [sub_eq_add_neg, toEk_add, toEk_neg, sub_eq_add_neg]

lemma toEk_injective : Function.Injective (toEk (k := k)) := by
  intro c c' h
  funext i
  have h' : ((c i : ℝ)) = ((c' i : ℝ)) := by
    have := congrFun (congrArg WithLp.ofLp h) i
    simpa [toEk] using this
  exact_mod_cast h'

lemma toEk_eq_zero_iff {c : Fin k → ℤ} : toEk c = 0 ↔ c = 0 := by
  refine ⟨fun h => toEk_injective (by rw [h, toEk_zero]), fun h => by simp [h]⟩

lemma toEk_ne_zero_iff {c : Fin k → ℤ} : toEk c ≠ 0 ↔ c ≠ 0 := by
  simp only [ne_eq, toEk_eq_zero_iff]

/-- Decomposition of a vector in the frame `toEk (Pi.single i 1)` carried by `Ψ`. -/
lemma sum_smul_toEk_single_eq {k : ℕ} (y : EuclideanSpace ℝ (Fin k)) :
    (∑ i, (y.ofLp i) • toEk (Pi.single i (1 : ℤ))) = y := by
  ext i
  simp [toEk, Pi.single_apply, Finset.sum_apply]

@[simp] lemma toEk_zsmul (c : ℤ) (s : Fin k → ℤ) : toEk (c • s) = (c : ℝ) • toEk s := by
  have h1 : (fun i => ((c • s) i : ℝ)) = (c : ℝ) • (fun i => (s i : ℝ)) := by
    ext i; simp [smul_eq_mul, Int.cast_mul]
  rw [toEk, h1, WithLp.toLp_smul]
  rfl

end Work.HP.BCS
