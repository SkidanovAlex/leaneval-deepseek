/-
  annals_wilkies_conjecture, AREA E3K (`Submission.Work.WilE3K`): the *arctan-elimination*
  framework for exp/tan chains.

  Route (design `sources/wilkiesE3E9/wilkies_E3E9_gaps.md` §GAP 1, nodes K1–K3).  The corrected
  Khovanskii bound `SepKhovanskiiET` is proved from the frozen `E2_khovanskii` by

  * **K1**: lift every `tan` chain function of a `SepChainLocal` system to a new coordinate `t_j`
    with the globally defined graph equation `arctan t_j - ℓ_j(x) + k_j π = 0` (the branch constant
    `k_j` exists because a convex domain meets only one branch of `tan`; FIX-1 of the review, see
    `Lift.lean`);
  * **K2**: one Khovanskii–Rolle elimination step per `tan` coordinate — Rolle along the level
    curve of the remaining system, the Rolle determinant multiplied by `∏ (1 + t_j²)` being an
    EA polynomial (`Elim.lean`, `Step.lean`);
  * **K3**: induction on the number of `tan` coordinates, with the frozen `E2_khovanskii` as base
    case (`rt = 0`: an exp-affine system in the `N` coordinates); `Reduction.lean`.

  This file fixes the vocabulary of the lifted (K2/K3) side.

  ## Conventions

  An `ETData N rt n re` is a *square* system on `ℝ^{N+1}` (coordinates `Fin (N+1)`):
  * the first `rt` coordinates are the **lifted `tan` coordinates** (an initial segment), the last
    `n` are the **free coordinates**: `E.freeCoord i = ⟨rt + i, _⟩`.  The proof field
    `E.h : rt + n = N + 1` records the decomposition;
  * `n` exp-affine equations `G i = 0`, whose chain functions
    `exp (∑ i, ca j i * x_i + cb j)` involve the free coordinates only;
  * `rt` **arctan graph equations** `Real.arctan (t_j) = ∑ i, lam j i * x_i + mu j`.

  The convention "tan coordinates *first*, free coordinates *last*" is what makes the elimination
  step of K2 cast-free (`Elim.lean`): eliminating the **last** `tan` coordinate turns it into the
  **first free** coordinate, so the ambient type `Fin (N + 1)` is unchanged, the remaining coordinates
  keep their indices and the remaining `tan` coordinates stay an initial segment.

  Two structural facts are used everywhere below.

  * The solutions of the `j`-th arctan equation are automatically confined to the slab
    `{z | -(π/2) < ∑ lam j i * x_i + mu j < π/2}` because `arctan` takes values in
    `(-(π/2), π/2)`: `lin_mem_Ioo_of_tanFun_eq_zero`.  This replaces, on the lifted side, the
    convexity hypothesis of `SepKhovanskiiET`.
  * Consequently `t_j = tan (∑ lam j i * x_i + mu j)` at every solution:
    `tan_eq_of_tanFun_eq_zero`.
-/
import Submission.Work.WilE3K.Defs
import Mathlib

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
namespace Work.WilE3K
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

variable {N rt n re : ℕ}

/-- **The lifted system.**  See the module docstring for the conventions. -/
structure ETData (N rt n re : ℕ) where
  /-- `rt + n = N + 1`: the ambient space is `Fin (N+1)`, whose first `rt` coordinates are the
  `tan` coordinates and whose last `n` are the free coordinates -/
  h : rt + n = N + 1
  /-- the chain coefficients, on the free coordinates only -/
  ca : Fin re → Fin n → ℝ
  cb : Fin re → ℝ
  /-- the exp-affine equations -/
  G : Fin n → EAPoly (N + 1) re
  /-- the linear parts of the arctan equations (on the free coordinates) -/
  lam : Fin rt → Fin n → ℝ
  /-- the constants of the arctan equations (they absorb the branch shift `-k_j π`) -/
  mu : Fin rt → ℝ

namespace ETData

variable (E : ETData N rt n re)

/-- The coordinate index of the `j`-th lifted `tan` coordinate. -/
def tanCoord (j : Fin rt) : Fin (N + 1) := ⟨j, by have := E.h; omega⟩

/-- The coordinate index of the `i`-th free coordinate. -/
def freeCoord (i : Fin n) : Fin (N + 1) := ⟨rt + i, by have := E.h; omega⟩

@[simp] theorem tanCoord_val (j : Fin rt) : ((E.tanCoord j : Fin (N + 1)) : ℕ) = j := rfl

@[simp] theorem freeCoord_val (i : Fin n) : ((E.freeCoord i : Fin (N + 1)) : ℕ) = rt + i := rfl

theorem tanCoord_injective : Function.Injective E.tanCoord := by
  intro j j' h
  have h' : ((E.tanCoord j : Fin (N + 1)) : ℕ) = ((E.tanCoord j' : Fin (N + 1)) : ℕ) := congrArg Fin.val h
  rw [tanCoord_val, tanCoord_val] at h'
  exact Fin.ext h'

theorem freeCoord_injective : Function.Injective E.freeCoord := by
  intro i i' h
  have h' : rt + (i : ℕ) = rt + (i' : ℕ) := congrArg Fin.val h
  exact Fin.ext (by omega)

/-- The `Fin rt` index of a coordinate which is smaller than `rt`. -/
def tanIndex (k : Fin (N + 1)) (hk : (k : ℕ) < rt) : Fin rt :=
  ⟨k, by have h1 : rt + n = N + 1 := E.h; omega⟩

/-- The free index of a coordinate which is at least `rt`. -/
def freeIndex (k : Fin (N + 1)) (hk : rt ≤ (k : ℕ)) : Fin n :=
  ⟨(k : ℕ) - rt, by
    have h1 : rt + n = N + 1 := E.h
    have h2 : (k : ℕ) < N + 1 := k.isLt
    omega⟩

@[simp] theorem tanCoord_tanIndex (k : Fin (N + 1)) (hk : (k : ℕ) < rt) :
    E.tanCoord (E.tanIndex k hk) = k := by
  ext
  simp [tanCoord, tanIndex]

@[simp] theorem freeCoord_freeIndex (k : Fin (N + 1)) (hk : rt ≤ (k : ℕ)) :
    E.freeCoord (E.freeIndex k hk) = k := by
  ext
  simp only [freeCoord, freeIndex]
  omega

@[simp] theorem tanIndex_tanCoord (j : Fin rt) (h : ((E.tanCoord j : Fin (N + 1)) : ℕ) < rt) :
    E.tanIndex (E.tanCoord j) h = j := by
  ext
  simp [tanCoord, tanIndex]

@[simp] theorem freeIndex_freeCoord (i : Fin n) (h : rt ≤ ((E.freeCoord i : Fin (N + 1)) : ℕ)) :
    E.freeIndex (E.freeCoord i) h = i := by
  ext
  simp [freeCoord, freeIndex]

/-- Every coordinate is either a `tan` coordinate or a free coordinate. -/
theorem eq_tanCoord_or_eq_freeCoord (k : Fin (N + 1)) :
    (∃ j : Fin rt, k = E.tanCoord j) ∨ (∃ i : Fin n, k = E.freeCoord i) := by
  by_cases h : (k : ℕ) < rt
  · exact Or.inl ⟨E.tanIndex k h, (E.tanCoord_tanIndex k h).symm⟩
  · exact Or.inr ⟨E.freeIndex k (not_lt.mp h), (E.freeCoord_freeIndex k (not_lt.mp h)).symm⟩

/-- The affine exponent of the `j`-th chain function. -/
def ellChain (j : Fin re) (z : Fin (N + 1) → ℝ) : ℝ :=
  (∑ i : Fin n, E.ca j i * z (E.freeCoord i)) + E.cb j

/-- Evaluation of an EA polynomial along the chain of the lifted system. -/
def evalPoly (P : EAPoly (N + 1) re) (z : Fin (N + 1) → ℝ) : ℝ :=
  MvPolynomial.eval (Sum.elim z fun j => Real.exp (E.ellChain j z)) P

theorem evalPoly_C (c : ℝ) (z : Fin (N + 1) → ℝ) : E.evalPoly (MvPolynomial.C c) z = c := by
  simp [evalPoly]

theorem evalPoly_add (P Q : EAPoly (N + 1) re) (z : Fin (N + 1) → ℝ) :
    E.evalPoly (P + Q) z = E.evalPoly P z + E.evalPoly Q z := by
  simp [evalPoly]

theorem evalPoly_mul (P Q : EAPoly (N + 1) re) (z : Fin (N + 1) → ℝ) :
    E.evalPoly (P * Q) z = E.evalPoly P z * E.evalPoly Q z := by
  simp [evalPoly]

theorem evalPoly_X_tan (k : Fin (N + 1)) (z : Fin (N + 1) → ℝ) : E.evalPoly (MvPolynomial.X (Sum.inl k)) z = z k := by
  simp [evalPoly]

theorem evalPoly_X_chain (j : Fin re) (z : Fin (N + 1) → ℝ) :
    E.evalPoly (MvPolynomial.X (Sum.inr j)) z = Real.exp (E.ellChain j z) := by
  simp [evalPoly]

/-- The coefficient of the `j`-th chain function in the symbolic derivative `∂/∂xᵢ`. -/
def dcoef (i : Fin (N + 1)) (j : Fin re) : ℝ :=
  if h : rt ≤ (i : ℕ) then E.ca j (E.freeIndex i h) else 0

@[simp] theorem dcoef_tan (j : Fin rt) (k : Fin re) : E.dcoef (E.tanCoord j) k = 0 := by
  simp only [dcoef]
  rw [dif_neg (by simp [tanCoord] : ¬ rt ≤ ((E.tanCoord j : Fin (N + 1)) : ℕ))]

@[simp] theorem dcoef_free (i : Fin n) (k : Fin re) : E.dcoef (E.freeCoord i) k = E.ca k i := by
  simp only [dcoef]
  rw [dif_pos (by simp [freeCoord] : rt ≤ ((E.freeCoord i : Fin (N + 1)) : ℕ))]
  exact congrArg (E.ca k) (E.freeIndex_freeCoord i _)

/-- The symbolic derivative `∂/∂xᵢ` along the chain of the lifted system. -/
def dPoly (i : Fin (N + 1)) (P : EAPoly (N + 1) re) : EAPoly (N + 1) re :=
  MvPolynomial.pderiv (Sum.inl i) P +
    ∑ j : Fin re, MvPolynomial.C (E.dcoef i j) * MvPolynomial.X (Sum.inr j) *
      MvPolynomial.pderiv (Sum.inr j) P

/-- The `i`-th exp-affine equation, evaluated. -/
def evP (i : Fin n) : (Fin (N + 1) → ℝ) → ℝ :=
  fun z => E.evalPoly (E.G i) z

/-- The linear part of the `j`-th arctan equation. -/
def lin (j : Fin rt) (z : Fin (N + 1) → ℝ) : ℝ :=
  (∑ i : Fin n, E.lam j i * z (E.freeCoord i)) + E.mu j

/-- The `j`-th arctan equation, as a function of the point. -/
def tanFun (j : Fin rt) : (Fin (N + 1) → ℝ) → ℝ :=
  fun z => Real.arctan (z (E.tanCoord j)) - E.lin j z

/-- The gradient of the `j`-th arctan equation, as a row: the entries are `1/(1 + t_j²)` on the
`j`-th `tan` coordinate and `- lam j i` on the free coordinates. -/
def dTanFun (j : Fin rt) (z : Fin (N + 1) → ℝ) (k : Fin (N + 1)) : ℝ :=
  if hk : (k : ℕ) < rt then (if k = E.tanCoord j then 1 / (1 + z k ^ 2) else 0)
    else -E.lam j (E.freeIndex k (not_lt.mp hk))

@[simp] theorem dTanFun_tan (j j' : Fin rt) (z : Fin (N + 1) → ℝ) :
    E.dTanFun j z (E.tanCoord j') =
      if j' = j then 1 / (1 + z (E.tanCoord j') ^ 2) else 0 := by
  simp only [dTanFun]
  rw [dif_pos (by simp [tanCoord] : ((E.tanCoord j' : Fin (N + 1)) : ℕ) < rt)]
  by_cases h : j' = j
  · subst h
    simp
  · rw [if_neg (fun hh => h (E.tanCoord_injective hh)), if_neg h]

@[simp] theorem dTanFun_free (j : Fin rt) (z : Fin (N + 1) → ℝ) (i : Fin n) :
    E.dTanFun j z (E.freeCoord i) = -E.lam j i := by
  simp only [dTanFun]
  rw [dif_neg (by simp [freeCoord] : ¬ ((E.freeCoord i : Fin (N + 1)) : ℕ) < rt)]
  exact congrArg (fun x => -E.lam j x) (E.freeIndex_freeCoord i _)

/-- The Jacobian matrix of the lifted system: rows are indexed by the equations (the first `rt`
are the arctan equations, the last `n` the exp-affine ones), columns by the coordinates. -/
def jac (z : Fin (N + 1) → ℝ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  Matrix.of fun r c => if hr : (r : ℕ) < rt then E.dTanFun (E.tanIndex r hr) z c
    else E.evalPoly (E.dPoly c (E.G (E.freeIndex r (not_lt.mp hr)))) z

@[simp] theorem jac_tan (z : Fin (N + 1) → ℝ) (j : Fin rt) (c : Fin (N + 1)) :
    E.jac z (E.tanCoord j) c = E.dTanFun j z c := by
  simp only [jac, Matrix.of_apply]
  rw [dif_pos (by simp [tanCoord] : ((E.tanCoord j : Fin (N + 1)) : ℕ) < rt)]
  exact congrArg (fun j' => E.dTanFun j' z c) (E.tanIndex_tanCoord j _)

@[simp] theorem jac_free (z : Fin (N + 1) → ℝ) (i : Fin n) (c : Fin (N + 1)) :
    E.jac z (E.freeCoord i) c = E.evalPoly (E.dPoly c (E.G i)) z := by
  simp only [jac, Matrix.of_apply]
  rw [dif_neg (by simp [freeCoord] : ¬ ((E.freeCoord i : Fin (N + 1)) : ℕ) < rt)]
  exact congrArg (fun i' => E.evalPoly (E.dPoly c (E.G i')) z) (E.freeIndex_freeCoord i _)

/-- The system map of the lifted system. -/
def map (z : Fin (N + 1) → ℝ) : Fin (N + 1) → ℝ :=
  fun r => if hr : (r : ℕ) < rt then E.tanFun (E.tanIndex r hr) z
    else E.evP (E.freeIndex r (not_lt.mp hr)) z

@[simp] theorem map_tan (z : Fin (N + 1) → ℝ) (j : Fin rt) :
    E.map z (E.tanCoord j) = E.tanFun j z := by
  simp only [map]
  rw [dif_pos (by simp [tanCoord] : ((E.tanCoord j : Fin (N + 1)) : ℕ) < rt)]
  exact congrArg (fun j' => E.tanFun j' z) (E.tanIndex_tanCoord j _)

@[simp] theorem map_free (z : Fin (N + 1) → ℝ) (i : Fin n) :
    E.map z (E.freeCoord i) = E.evP i z := by
  simp only [map]
  rw [dif_neg (by simp [freeCoord] : ¬ ((E.freeCoord i : Fin (N + 1)) : ℕ) < rt)]
  exact congrArg (fun i' => E.evP i' z) (E.freeIndex_freeCoord i _)

/-- **Nondegenerate zero of the lifted system**: all equations vanish and the Jacobian is
invertible. -/
def Nondegen (z : Fin (N + 1) → ℝ) : Prop :=
  (∀ i, E.evP i z = 0) ∧ (∀ j, E.tanFun j z = 0) ∧ (E.jac z).det ≠ 0

theorem Nondegen.evP {z : Fin (N + 1) → ℝ} (h : E.Nondegen z) (i : Fin n) : E.evP i z = 0 := h.1 i

theorem Nondegen.tanFun {z : Fin (N + 1) → ℝ} (h : E.Nondegen z) (j : Fin rt) : E.tanFun j z = 0 :=
  h.2.1 j

theorem Nondegen.det {z : Fin (N + 1) → ℝ} (h : E.Nondegen z) : (E.jac z).det ≠ 0 := h.2.2

theorem tanFun_eq (j : Fin rt) (z : Fin (N + 1) → ℝ) :
    E.tanFun j z = Real.arctan (z (E.tanCoord j)) - E.lin j z := rfl

/-- **The `tan` coordinate is recovered from the graph.**  A solution of the `j`-th arctan
equation has `t_j = tan (∑ lam j i * x_i + mu j)`. -/
theorem tan_eq_of_tanFun_eq_zero {j : Fin rt} {z : Fin (N + 1) → ℝ} (h : E.tanFun j z = 0) :
    z (E.tanCoord j) = Real.tan (E.lin j z) := by
  have h1 : Real.arctan (z (E.tanCoord j)) = E.lin j z := sub_eq_zero.mp h
  rw [← h1, Real.tan_arctan]

/-- **The branch confinement.**  A solution of the `j`-th arctan equation lies in the fundamental
slab of `tan`, where the graph is single-valued. -/
theorem lin_mem_Ioo_of_tanFun_eq_zero {j : Fin rt} {z : Fin (N + 1) → ℝ} (h : E.tanFun j z = 0) :
    -(Real.pi / 2) < E.lin j z ∧ E.lin j z < Real.pi / 2 := by
  have h1 : Real.arctan (z (E.tanCoord j)) = E.lin j z := sub_eq_zero.mp h
  exact ⟨by rw [← h1]; exact Real.neg_pi_div_two_lt_arctan _,
    by rw [← h1]; exact Real.arctan_lt_pi_div_two _⟩

theorem cos_lin_pos_of_tanFun_eq_zero {j : Fin rt} {z : Fin (N + 1) → ℝ} (h : E.tanFun j z = 0) :
    0 < Real.cos (E.lin j z) :=
  Real.cos_pos_of_mem_Ioo (E.lin_mem_Ioo_of_tanFun_eq_zero h)

/-- A solution of the `j`-th arctan equation determines the `tan` coordinate by a *function of the
free coordinates only*: the graph is single-valued. -/
theorem tanCoord_eq_of_tanFun_eq_zero {j : Fin rt} {z z' : Fin (N + 1) → ℝ}
    (h : E.tanFun j z = 0) (h' : E.tanFun j z' = 0)
    (hfree : ∀ i, z (E.freeCoord i) = z' (E.freeCoord i)) :
    z (E.tanCoord j) = z' (E.tanCoord j) := by
  rw [E.tan_eq_of_tanFun_eq_zero h, E.tan_eq_of_tanFun_eq_zero h']
  congr 1
  rw [lin, lin]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [hfree i]

/-! ## §2. The last `tan` coordinate is `1 + t² > 0` -/

theorem one_add_sq_pos (z : Fin (N + 1) → ℝ) (k : Fin (N + 1)) : 0 < 1 + z k ^ 2 := by positivity

end ETData

end Work.WilE3K
