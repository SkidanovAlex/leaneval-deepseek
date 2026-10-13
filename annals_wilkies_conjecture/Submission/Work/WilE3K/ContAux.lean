/-
  annals_wilkies_conjecture, AREA E3K: support for the smoothness / Jacobian lemma
  `Work.WilE3K.contDiff_map_and_det`.

  An `ETData N rt n re` is a square system on `ℝ^{N+1}` whose `rt` "arctan" equations live on
  the first coordinates and whose `n` exp-affine equations `G i` live on the last coordinates.
  Its chain functions are `exp (E.ellChain j z) = exp (∑ i : Fin n, ca j i * z (freeCoord i) + cb j)`.

  This file collects the *vocabulary bridge* to the EA-chain machinery of
  `Submission.Work.WilE9.EaD`:

  * `ETData.toChain` — the EA chain on the ambient `Fin (N+1)` coordinates whose chain function
    `j` is `exp (E.ellChain j ·)`.  Its coefficient `toChain.a j i = E.dcoef i j` is exactly the
    coefficient of `∂/∂z_i` in `exp (E.ellChain j ·)` (zero on `tan` coordinates, `ca j i` on free
    ones).
  * `ETData.evalPoly_eq_eaEval`, `ETData.dPoly_eq_eaD` — `E.evalPoly P = eaEval E.toChain P` and
    `E.dPoly i P = eaD E.toChain i P`, so the derivative lemmas `eaD_hasFDerivAt` /
    `eaEval_contDiff` of E9 apply verbatim.
  * `ETData.filter_not_lt_eq_image_freeCoord`, `ETData.sum_dcoef` — the coordinate bookkeeping
    (the free coordinates are exactly the coordinates `≥ rt`, and `E.dcoef` sums to `E.ca`).
-/
import Mathlib
import Submission.Work.WilE3K.ET

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
namespace Work.WilE3K
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

variable {N rt n re : ℕ}

namespace ETData

variable (E : ETData N rt n re)

/-! ## §1. Coordinate bookkeeping -/

/-- The coordinates that are *not* `tan` coordinates (i.e. `¬ c < rt`) are exactly the free
coordinates. -/
theorem filter_not_lt_eq_image_freeCoord (E : ETData N rt n re) :
    (Finset.univ : Finset (Fin (N + 1))).filter (fun c : Fin (N + 1) => ¬ (c : ℕ) < rt)
      = Finset.univ.image E.freeCoord := by
  ext c
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro h
    have hle : rt ≤ (c : ℕ) := by omega
    exact ⟨E.freeIndex c hle, E.freeCoord_freeIndex c hle⟩
  · rintro ⟨a, ha⟩
    have hc : (c : ℕ) = rt + (a : ℕ) := by rw [← ha, ETData.freeCoord_val]
    omega

/-- The symbolic derivative coefficients `E.dcoef · j` sum to the chain coefficient `E.ca j`. -/
theorem sum_dcoef (E : ETData N rt n re) (j : Fin re) (z : Fin (N + 1) → ℝ) :
    (∑ i : Fin (N + 1), E.dcoef i j * z i) = ∑ i : Fin n, E.ca j i * z (E.freeCoord i) := by
  rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
      (p := fun c : Fin (N + 1) => (c : ℕ) < rt) (f := fun c => E.dcoef c j * z c)]
  have hzero : ∑ c ∈ Finset.univ.filter (fun c : Fin (N + 1) => (c : ℕ) < rt),
      E.dcoef c j * z c = 0 := by
    apply Finset.sum_eq_zero
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    have h' : ¬ rt ≤ (c : ℕ) := by omega
    rw [ETData.dcoef, dif_neg h', zero_mul]
  have himg : ∑ c ∈ Finset.univ.filter (fun c : Fin (N + 1) => ¬ (c : ℕ) < rt),
      E.dcoef c j * z c = ∑ i : Fin n, E.ca j i * z (E.freeCoord i) := by
    rw [E.filter_not_lt_eq_image_freeCoord]
    rw [Finset.sum_image (E.freeCoord_injective.injOn)]
    exact Finset.sum_congr rfl fun i _ => by rw [E.dcoef_free]
  rw [hzero, himg, zero_add]

/-! ## §2. The ambient EA chain -/

/-- The EA chain on the ambient coordinates `Fin (N+1)` whose `j`-th chain function is
`exp (E.ellChain j ·)`: its coefficient `a j i = E.dcoef i j` is the derivative of `E.ellChain j`
in the `i`-th coordinate (zero on `tan` coordinates, `ca j i` on the free ones). -/
def toChain (E : ETData N rt n re) : EAChain (N + 1) re where
  a j i := E.dcoef i j
  b j := E.cb j

theorem ell_toChain (E : ETData N rt n re) (j : Fin re) (z : Fin (N + 1) → ℝ) :
    E.ellChain j z = E.toChain.ell j z := by
  simp only [ETData.ellChain, EAChain.ell, ETData.toChain]
  rw [E.sum_dcoef j z]

/-- `E.evalPoly` is the EA-chain evaluation of `E.toChain`. -/
theorem evalPoly_eq_eaEval (E : ETData N rt n re) (P : EAPoly (N + 1) re)
    (z : Fin (N + 1) → ℝ) :
    E.evalPoly P z = eaEval E.toChain P z := by
  have h : (Sum.elim z (fun j => Real.exp (E.ellChain j z)))
      = (Sum.elim z (fun j => Real.exp (E.toChain.ell j z))) := by
    funext s
    rcases s with i | j
    · rfl
    · simp only [Sum.elim_inr, ETData.ell_toChain]
  simp only [ETData.evalPoly, eaEval, h]

/-- `E.dPoly` is the symbolic EA derivative of `E.toChain`. -/
theorem dPoly_eq_eaD (E : ETData N rt n re) (i : Fin (N + 1)) (P : EAPoly (N + 1) re) :
    E.dPoly i P = eaD E.toChain i P := by
  simp only [ETData.dPoly, eaD, ETData.toChain]

end ETData

end Work.WilE3K
