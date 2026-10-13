/-
Area DSCOH (curric-46) — shifts of the coordinate ring of `ℙⁿ` (the graded modules `S(-d)`).

The free graded modules over `A[x₀,…,x_{n-1}]` that occur in resolutions are finite direct sums
of shifts `S(-d)` of the structure sheaf's coordinate ring.  This file only records the grading
of `S(-d)`; that it is a decomposition, and that the multiplication is graded, are the lemmas
`Work.DSCOH.shift_decomposition` and `Work.DSCOH.shift_gradedSMul`.
-/
import Submission.Work.DSCOH.Basic

open MvPolynomial

namespace Work.DSCOH

variable {A : Type*} [CommRing A] {n : ℕ}

/-- The grading of the `d`-fold shift `S(-d)` of the polynomial ring `S = A[X₀,…,X_{n-1}]`:
its `e`-th piece is the `(e-d)`-th homogeneous piece of `S` for `e ≥ d`, and zero otherwise. -/
noncomputable def shift (d : ℕ) (e : ℕ) : Submodule A (Poly A n) :=
  if d ≤ e then homSub A n (e - d) else ⊥

@[simp]
lemma shift_of_le {d e : ℕ} (h : d ≤ e) : shift (A := A) (n := n) d e = homSub A n (e - d) := by
  simp [shift, h]

@[simp]
lemma shift_of_not_le {d e : ℕ} (h : ¬ d ≤ e) : shift (A := A) (n := n) d e = ⊥ := by
  simp [shift, h]

/-- The grading of a finite direct sum `⨁_{i : Fin k} S(-dᵢ)` of shifts: the `e`-th piece is the
product, over `i`, of the `(e - dᵢ)`-th piece of `S(-dᵢ)`. -/
noncomputable def shiftSum {k : ℕ} (d : Fin k → ℕ) (e : ℕ) :
    Submodule A (Fin k → Poly A n) :=
  ⨅ i, Submodule.comap (LinearMap.proj i) (shift (A := A) (n := n) (d i) e)

@[simp]
lemma mem_shiftSum {k : ℕ} {d : Fin k → ℕ} {e : ℕ} {x : Fin k → Poly A n} :
    x ∈ shiftSum (A := A) (n := n) d e ↔ ∀ i, x i ∈ shift (A := A) (n := n) (d i) e := by
  simp [shiftSum, Submodule.mem_iInf, Submodule.mem_comap]

end Work.DSCOH
