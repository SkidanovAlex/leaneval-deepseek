import Mathlib
import Submission.CDTPlan.InterfacesC
import Submission.Work.CDcl.setup

/-! helper lemmas for the assembly of `Work.CDcl.c_dclosed` -/

noncomputable section

namespace Work.CDcl

open Polynomial PowerSeries

/-- coercion to power series commutes with finite sums -/
theorem coe_sum_finset {ι : Type*} (s : Finset ι) (g : ι → Polynomial ℚ) :
    ((∑ i ∈ s, g i : Polynomial ℚ) : PowerSeries ℚ) = ∑ i ∈ s, (g i : PowerSeries ℚ) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Polynomial.coe_add, ih]

/-- the `j`-index `5 + k` of `seventeen` -/
def idx (k : Fin 4) : Fin 17 := ⟨5 + (k : ℕ), by omega⟩

@[simp] theorem idx_val (k : Fin 4) : (idx k : ℕ) = 5 + (k : ℕ) := rfl

/-- the row of the `d/dy`-matrix attached to the order-4 ODE: `c` on `B₁ = 1` and `A k` on
`G^{(k)}`. -/
def odeRow (c : Polynomial ℚ) (A : Fin 4 → Polynomial ℚ) : Fin 17 → Polynomial ℚ := fun j =>
  (if (j : ℕ) = 0 then c else 0)
    + (∑ k : Fin 4, if (j : ℕ) = 5 + (k : ℕ) then A k else 0)

/-- the sum identity attached to `odeRow`. -/
theorem sum_odeRow (f : Fin 17 → PowerSeries ℚ) (c : Polynomial ℚ) (A : Fin 4 → Polynomial ℚ) :
    (∑ j : Fin 17, ((odeRow c A j : Polynomial ℚ) : PowerSeries ℚ) * f j)
      = (c : PowerSeries ℚ) * f 0
        + ∑ k : Fin 4, (A k : PowerSeries ℚ) * f (idx k) := by
  classical
  have hrow : ∀ j : Fin 17, ((odeRow c A j : Polynomial ℚ) : PowerSeries ℚ)
      = ((if (j : ℕ) = 0 then c else 0 : Polynomial ℚ) : PowerSeries ℚ)
        + ∑ k : Fin 4, ((if (j : ℕ) = 5 + (k : ℕ) then A k else 0 : Polynomial ℚ) :
            PowerSeries ℚ) := by
    intro j
    unfold odeRow
    rw [Polynomial.coe_add, coe_sum_finset]
  simp only [hrow]
  have hsplit : ∀ j : Fin 17,
      ((((if (j : ℕ) = 0 then c else 0 : Polynomial ℚ) : PowerSeries ℚ)
        + ∑ k : Fin 4, ((if (j : ℕ) = 5 + (k : ℕ) then A k else 0 : Polynomial ℚ)
            : PowerSeries ℚ)) * f j)
      = ((if (j : ℕ) = 0 then c else 0 : Polynomial ℚ) : PowerSeries ℚ) * f j
        + (∑ k : Fin 4, ((if (j : ℕ) = 5 + (k : ℕ) then A k else 0 : Polynomial ℚ)
            : PowerSeries ℚ)) * f j := by
    intro j; rw [add_mul]
  simp only [hsplit, Finset.sum_mul]
  rw [Finset.sum_add_distrib]
  congr 1
  · -- the constant part
    rw [Finset.sum_eq_single (0 : Fin 17)]
    · simp
    · intro b _ hb
      simp [hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [Finset.sum_eq_single (idx k)]
    · simp
    · intro b _ hb
      have hne : ¬ ((b : ℕ) = 5 + (k : ℕ)) := by
        intro hcon
        exact hb (Fin.ext (by rw [idx_val]; exact hcon))
      simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h

end Work.CDcl
