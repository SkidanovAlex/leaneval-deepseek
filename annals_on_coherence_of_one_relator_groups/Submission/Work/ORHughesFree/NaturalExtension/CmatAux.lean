/-
# Auxiliary definitions for `Cmat_degPart_compare`

This file collects the small objects used in comparing the row span of `Cmat p n` with the degree
filtration `degPart R (genIdeal p) n`.

* `Tpow k` : the monomial `t^k` of `S = R[t^{±1};τ]`;
* `Vvec p n k` : the row vector `s ↦ t^k • p_{s-k}` of `R^{n+1}` (this is the `k`-th row of
  `Cmat p n` when `0 ≤ k ≤ n`);
* `Emat p n` / `Esub p n` : the extra generators `t^{-(j+1)} * p` (`j < upDeg p`) and their span;
* `Crows p n` : the span of the rows of `Cmat p n`;
* `Msub p n = Crows p n ⊔ Esub p n`.
-/
import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.DualityDefs
import Submission.Work.ORHughesFree.NaturalExtension.DualityAPI
import Submission.Work.ORHughesFree.NaturalExtension.coeffElt_mul
import Submission.Work.ORHughesFree.NaturalExtension.EltDeg

set_option autoImplicit false

universe u

namespace Work.ORHughesFree.NaturalExtension

open Matrix Work.ORHughesFree

variable {R : Type u} [Ring R] [MulSemiringAction (Multiplicative ℤ) R]

/-- The monomial `t^k` of the skew Laurent polynomial ring `R[t^{±1};τ]`. -/
noncomputable def Tpow (k : ℤ) : SkewL R :=
  SkewMonoidAlgebra.single (Multiplicative.ofAdd k) (1 : R)

/-- The row vector `s ↦ t^k • p_{s-k}` of `R^{n+1}`.  For `0 ≤ k ≤ n` this is the `k`-th row of
`Cmat p n`. -/
noncomputable def Vvec (p : SkewL R) (n : ℕ) (k : ℤ) : Fin (n + 1) → R :=
  fun s => (Multiplicative.ofAdd k) • coeffElt p (((s : ℕ) : ℤ) - k)

/-- The `j`-th extra generator `cvec R n (t^{-(j+1)} * p)`, for `j < upDeg p`. -/
noncomputable def extra (p : SkewL R) (n : ℕ) (j : Fin (upDeg p)) : Fin (n + 1) → R :=
  cvec R n (Tpow (-(((j : ℕ) : ℤ) + 1)) * p)

/-- The matrix whose rows are the extra generators `t^{-(j+1)} * p`, `j < upDeg p`. -/
noncomputable def Emat (p : SkewL R) (n : ℕ) : Matrix (Fin (upDeg p)) (Fin (n + 1)) R :=
  fun j s => extra p n j s

/-- The span of the extra generators. -/
noncomputable def Esub (p : SkewL R) (n : ℕ) : Submodule R (Fin (n + 1) → R) :=
  Submodule.span R (Set.range (fun j : Fin (upDeg p) => (fun s : Fin (n + 1) => Emat p n j s)))

/-- The span of the rows of `Cmat p n`. -/
noncomputable def Crows (p : SkewL R) (n : ℕ) : Submodule R (Fin (n + 1) → R) :=
  Submodule.span R (Set.range (fun r : Fin (n + 1) => (fun s : Fin (n + 1) => Cmat p n r s)))

/-- The span of the rows of `Cmat p n` together with the extra generators. -/
noncomputable def Msub (p : SkewL R) (n : ℕ) : Submodule R (Fin (n + 1) → R) :=
  Crows p n ⊔ Esub p n

/-- Coefficient of `t^k * f`. -/
theorem coeffElt_Tpow_mul (k : ℤ) (f : SkewL R) (w : ℤ) :
    coeffElt (Tpow k * f) w = (Multiplicative.ofAdd k) • coeffElt f (w - k) := by
  rw [Tpow, coeffElt, SkewMonoidAlgebra.coeff_single_mul]
  have h : (Multiplicative.ofAdd k)⁻¹ * Multiplicative.ofAdd w
      = Multiplicative.ofAdd (w - k) := by
    rw [← ofAdd_neg, ← ofAdd_add]
    congr 1
    ring
  rw [one_mul, coeffElt, h]

section Rank

variable [VonNeumannRegularRing R]

/-- The dimension of the row span of a `d × n` matrix is at most `d`. -/
theorem rdim_span_rows_le (rk : SylvesterRank R) {d n : ℕ} (A : Matrix (Fin d) (Fin n) R) :
    rdim rk (Submodule.span R (Set.range (fun i : Fin d => (fun j : Fin n => A i j))))
      ≤ (d : ℝ) := by
  rw [rdim_eq_rk_rows rk A]
  exact RankAPI.rk_le_left rk A

/-- `rdim (Esub p n) ≤ upDeg p`: the extra generators are `upDeg p` in number. -/
theorem rdim_Esub_le (rk : SylvesterRank R) (p : SkewL R) (n : ℕ) :
    rdim rk (Esub p n) ≤ (upDeg p : ℝ) :=
  rdim_span_rows_le rk (Emat p n)

end Rank

/-- Every row of `Cmat p n` lies in the degree filtration `degPart R (genIdeal p) n`: it is the
coefficient vector of the polynomial element `t^r * p ∈ genIdeal p`. -/
theorem row_mem_degPart (p : SkewL R) (hp : ∀ k : ℤ, k < 0 → coeffElt p k = 0) (n : ℕ)
    (r : Fin (n + 1)) :
    (fun s : Fin (n + 1) => Cmat p n r s) ∈ degPart R (genIdeal p) n := by
  refine Submodule.subset_span ⟨Tpow (((r : ℕ) : ℤ)) * p, ⟨Tpow _, rfl⟩, ?_, ?_⟩
  · intro k hk
    rw [coeffElt_Tpow_mul]
    have h1 : k - (((r : ℕ) : ℤ)) < 0 := by
      have : (0 : ℤ) ≤ (((r : ℕ) : ℤ)) := Int.natCast_nonneg _
      omega
    rw [hp _ h1, smul_zero]
  · funext s
    rw [cvec, coeffElt_Tpow_mul]
    rfl

/-- The row span of `Cmat p n` is contained in `degPart R (genIdeal p) n`. -/
theorem Crows_le_degPart (p : SkewL R) (hp : ∀ k : ℤ, k < 0 → coeffElt p k = 0) (n : ℕ) :
    Crows p n ≤ degPart R (genIdeal p) n := by
  refine Submodule.span_le.mpr ?_
  rintro v ⟨r, rfl⟩
  exact row_mem_degPart p hp n r

end Work.ORHughesFree.NaturalExtension
