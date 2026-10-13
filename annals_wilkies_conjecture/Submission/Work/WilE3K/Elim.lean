/-
  annals_wilkies_conjecture, AREA E3K (`Submission.Work.WilE3K`): the *elimination vocabulary*.

  This file fixes the objects of the Khovanskii–Rolle elimination step of K2 (design §GAP 1) for the
  lifted systems of `ET.lean`, plus the recursion bound `ETB` and the induction statement `SepET`
  of K3.

  ## The elimination step

  An `E : ETData N (rt+1) n re` is a system with `rt+1` arctan graph equations on `ℝ^{N+1}`.  The
  step eliminates the **last** arctan equation (the one attached to the `tan` coordinate of index
  `rt`, `E.lastRow`):

  * `E.psiMap` is the *remaining* system (`N` equations in `N+1` unknowns): the full system map
    with the eliminated row deleted (`Fin.succAbove`), i.e. its level sets are curves;
  * `E.gLast` is the eliminated arctan equation;
  * `E.rolleDetP` is the determinant of the *scaled Rolle matrix*: the arctan rows are multiplied by
    their own `1 + t_j²` (which clears the denominators `1/(1+t_j²)` in `∇(arctan t_j)`) and the
    polynomial rows are the symbolic derivatives `dPoly`.  Every entry is an EA polynomial, and
    `E.prodPoly = ∏_j (1 + t_j²)` is the product of the scaling factors.
  * `E.rolleDetFun` is the analytic Rolle determinant `d(gLast)` along the cross-product field of
    `psiMap`, divided by the scaling factors; `E.rolleMap` is `(psiMap, rolleDetFun)`.
  * `E.newData y δ` is the new system: the first `rt` arctan equations and the `n+1` polynomial
    equations obtained from the old ones by subtracting the value `y` plus the new equation
    `rolleDetP - δ · prodPoly = 0`.  The eliminated `tan` coordinate becomes the first free
    coordinate (convention "tan coordinates first"), so the ambient `Fin (N+1)` is unchanged.

  ## The bound

  `ETB q rt N D` is the recursion bound for the induction on the number of `tan` coordinates: the
  base case (`rt = 0`, an exp-affine system in the `N+1` coordinates) is the frozen Khovanskii
  bound `q`, the step is one sphere step plus one Rolle step, which multiplies the running total
  degree by `N + 8` and increases `N` by one.
-/
import Submission.Work.WilE3K.ET

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
namespace Work.WilE3K
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

namespace ETData

variable {N rt n re : ℕ}

/-! ## §1. The remaining system and the eliminated equation -/

/-- The row of the eliminated arctan equation: the last `tan` coordinate. -/
def lastRow (E : ETData N (rt + 1) n re) : Fin (N + 1) :=
  ⟨rt, by have h := E.h; omega⟩

/-- The eliminated arctan equation. -/
def gLast (E : ETData N (rt + 1) n re) : (Fin (N + 1) → ℝ) → ℝ := E.tanFun (Fin.last rt)

/-- The *remaining* system: the full system map with the eliminated row deleted. -/
def psiMap (E : ETData N (rt + 1) n re) : (Fin (N + 1) → ℝ) → (Fin N → ℝ) :=
  fun z i => E.map z (Fin.succAbove E.lastRow i)

@[simp] theorem psiMap_apply (E : ETData N (rt + 1) n re) (z : Fin (N + 1) → ℝ) (i : Fin N) :
    E.psiMap z i = E.map z (Fin.succAbove E.lastRow i) := rfl

/-- The value of the remaining system at a point. -/
def psiVal (E : ETData N (rt + 1) n re) (z : Fin (N + 1) → ℝ) : Fin N → ℝ := E.psiMap z


/-- The value of the *full* system (all `N+1` equations): `y` on the remaining equations and `0`
on the eliminated one.  It is the unique solution of `psiMap w = y`, `gLast w = 0`. -/
noncomputable def psiLift (E : ETData N (rt + 1) n re) (y : Fin N → ℝ) : Fin (N + 1) → ℝ :=
  fun r => if h : ∃ i : Fin N, Fin.succAbove E.lastRow i = r then y (Classical.choose h) else 0

theorem psiLift_succAbove (E : ETData N (rt + 1) n re) (y : Fin N → ℝ) (i : Fin N) :
    E.psiLift y (Fin.succAbove E.lastRow i) = y i := by
  classical
  have hex : ∃ j : Fin N, Fin.succAbove E.lastRow j = Fin.succAbove E.lastRow i := ⟨i, rfl⟩
  simp only [psiLift]
  rw [dif_pos hex]
  congr 1
  exact Fin.succAbove_right_injective (Classical.choose_spec hex)

theorem psiLift_lastRow (E : ETData N (rt + 1) n re) (y : Fin N → ℝ) :
    E.psiLift y E.lastRow = 0 := by
  simp only [psiLift]
  rw [dif_neg]
  rintro ⟨i, hi⟩
  exact Fin.succAbove_ne E.lastRow i hi



/-! ## §2. The scaled Rolle matrix -/

/-- The product `∏_j (1 + t_j²)` of the scaling factors of the arctan rows. -/
def prodPoly (E : ETData N (rt + 1) n re) : EAPoly (N + 1) re :=
  ∏ j : Fin (rt + 1), (1 + MvPolynomial.X (Sum.inl (E.tanCoord j)) ^ 2)

/-- The value of `prodPoly`. -/
def prodEval (E : ETData N (rt + 1) n re) (z : Fin (N + 1) → ℝ) : ℝ :=
  ∏ j : Fin (rt + 1), (1 + z (E.tanCoord j) ^ 2)

/-- The `j`-th arctan row scaled by `1 + t_j²`: the entries are `1` on the `j`-th `tan` coordinate,
`0` on the other `tan` coordinates and `-(1 + t_j²) · lam j i` on the free coordinates. -/
def dTanPoly (E : ETData N (rt + 1) n re) (j : Fin (rt + 1)) (k : Fin (N + 1)) :
    EAPoly (N + 1) re :=
  if hk : (k : ℕ) < rt + 1 then (if k = E.tanCoord j then 1 else 0)
    else -(MvPolynomial.C (E.lam j (E.freeIndex k (not_lt.mp hk))) *
      (1 + MvPolynomial.X (Sum.inl (E.tanCoord j)) ^ 2))

/-- The matrix whose rows are the scaled arctan rows (the first `rt+1` rows) and the symbolic
derivatives of the polynomial equations.  Its determinant is `∏_j (1+t_j²)` times the Jacobian
determinant. -/
def rolleMatP (E : ETData N (rt + 1) n re) : Matrix (Fin (N + 1)) (Fin (N + 1)) (EAPoly (N + 1) re) :=
  Matrix.of fun r c => if hr : (r : ℕ) < rt + 1 then E.dTanPoly (E.tanIndex r hr) c
    else E.dPoly c (E.G (E.freeIndex r (not_lt.mp hr)))

/-- The Rolle determinant, as an EA polynomial. -/
def rolleDetP (E : ETData N (rt + 1) n re) : EAPoly (N + 1) re := (E.rolleMatP).det

/-- The analytic Rolle determinant: the derivative of the eliminated equation along the
cross-product field of the remaining system, divided by the scaling factors. -/
def rolleDetFun (E : ETData N (rt + 1) n re) (z : Fin (N + 1) → ℝ) : ℝ :=
  E.evalPoly E.rolleDetP z / E.prodEval z

/-- The remaining system together with the Rolle determinant, as a map with values in `ℝ^{N+1}`:
this is the map whose critical values above a slice are null (`ETSliceNull`). -/
def rolleMap (E : ETData N (rt + 1) n re) (z : Fin (N + 1) → ℝ) : Fin (N + 1) → ℝ :=
  fun r => if h : (r : ℕ) < N then E.psiMap z ⟨(r : ℕ), h⟩ else E.rolleDetFun z

theorem rolleMap_apply_castSucc (E : ETData N (rt + 1) n re) (z : Fin (N + 1) → ℝ)
    (i : Fin N) : E.rolleMap z (Fin.castSucc i) = E.psiMap z i := by
  simp only [rolleMap, Fin.val_castSucc]
  rw [dif_pos i.isLt]

theorem rolleMap_apply_last (E : ETData N (rt + 1) n re) (z : Fin (N + 1) → ℝ) :
    E.rolleMap z (Fin.last N) = E.rolleDetFun z := by
  simp only [rolleMap]
  rw [dif_neg (by simp)]

@[simp] theorem rolleMap_castSucc (E : ETData N (rt + 1) n re) (z : Fin (N + 1) → ℝ)
    (i : Fin N) : E.rolleMap z (Fin.castSucc i) = E.psiMap z i :=
  E.rolleMap_apply_castSucc z i

@[simp] theorem rolleMap_last (E : ETData N (rt + 1) n re) (z : Fin (N + 1) → ℝ) :
    E.rolleMap z (Fin.last N) = E.rolleDetFun z := E.rolleMap_apply_last z

/-! ## §3. The new system -/

/-- The chain of the new system: the eliminated coordinate is free but does not occur in the
chain. -/
def newCa (E : ETData N (rt + 1) n re) : Fin re → Fin (n + 1) → ℝ :=
  fun j i' => if h : (i' : ℕ) = 0 then 0
    else E.ca j ⟨(i' : ℕ) - 1, by have h1 := i'.isLt; omega⟩

/-- The arctan coefficients of the new system. -/
def newLam (E : ETData N (rt + 1) n re) : Fin rt → Fin (n + 1) → ℝ :=
  fun j i' => if h : (i' : ℕ) = 0 then 0
    else E.lam (Fin.castSucc j) ⟨(i' : ℕ) - 1, by have h1 := i'.isLt; omega⟩

/-- The constants of the arctan equations of the new system: the old constants, shifted by the
value `y` of the remaining system (the Rolle step is carried out on the level set
`psiMap = y`, and the new arctan equations must vanish there). -/
def newMu (E : ETData N (rt + 1) n re) (y : Fin N → ℝ) : Fin rt → ℝ :=
  fun j => E.mu (Fin.castSucc j) + y ⟨j, by have h1 := E.h; omega⟩

/-- The equations of the new system: the Rolle equation at index `0`, and the old polynomial
equations (shifted by the value `y`) at the other indices. -/
def newG (E : ETData N (rt + 1) n re) (y : Fin N → ℝ) (δ : ℝ) : Fin (n + 1) → EAPoly (N + 1) re :=
  fun i' => if h : (i' : ℕ) = 0 then E.rolleDetP - MvPolynomial.C δ * E.prodPoly
    else E.G ⟨(i' : ℕ) - 1, by have h1 := i'.isLt; omega⟩ -
      MvPolynomial.C (y ⟨rt + ((i' : ℕ) - 1), by
        have h1 := i'.isLt; have h2 := h; have h3 := E.h; omega⟩)

variable (E : ETData N (rt + 1) n re)

/-- **The new system produced by one elimination step.** -/
def newData (y : Fin N → ℝ) (δ : ℝ) : ETData N rt (n + 1) re where
  h := by have h := E.h; omega
  ca := E.newCa
  cb := E.cb
  G := E.newG y δ
  lam := E.newLam
  mu := E.newMu y

@[simp] theorem newData_h (y : Fin N → ℝ) (δ : ℝ) :
    (E.newData y δ).h = (by have h := E.h; omega) := rfl

/-! ## §4. The sphere step -/

/-- The sphere equation `∑_k z_k² = c` in the ambient dimension `N + 2`. -/
def spherePoly (c : ℝ) : EAPoly (N + 2) re :=
  (∑ k : Fin (N + 2), MvPolynomial.X (Sum.inl k) ^ 2) - MvPolynomial.C c

/-- The embedding of the polynomials of `ℝ^{N+1}` into those of `ℝ^{N+2}` (new last coordinate). -/
def embedP (P : EAPoly (N + 1) re) : EAPoly (N + 2) re :=
  MvPolynomial.rename (Sum.map (Fin.castAdd 1) id) P

variable (E : ETData N rt n re)

/-- **The sphere step**: add one free coordinate (the last one) and the sphere equation, keeping
the other equations (which do not involve the new coordinate). -/
def sphereData (c : ℝ) : ETData (N + 1) rt (n + 1) re where
  h := by have h := E.h; omega
  ca := fun j i' => if h : (i' : ℕ) < n then E.ca j ⟨(i' : ℕ), h⟩ else 0
  cb := E.cb
  G := fun i' => if h : (i' : ℕ) < n then embedP (E.G ⟨(i' : ℕ), h⟩) else spherePoly c
  lam := fun j i' => if h : (i' : ℕ) < n then E.lam j ⟨(i' : ℕ), h⟩ else 0
  mu := E.mu

end ETData

/-! ## §5. The genericity bundle of the elimination step -/

namespace ETData

variable {N rt n re : ℕ}

/-- `y` is a regular value of the remaining system: the level set `{psiMap = y}` is a smooth
curve. -/
def ETSubmersion (E : ETData N (rt + 1) n re) (y : Fin N → ℝ) : Prop :=
  ∀ z, E.psiMap z = y →
    LinearIndependent ℝ (fun a => fderiv ℝ (fun w => E.psiMap w a) z)

/-- Every crossing of the level set `{psiMap = y}` with the eliminated equation is a
nondegenerate zero of the lifted system. -/
def ETRegValue (E : ETData N (rt + 1) n re) (y : Fin N → ℝ) : Prop :=
  ∀ z, E.psiMap z = y → E.gLast z = 0 → (E.jac z).det ≠ 0

/-- Above `y`, the critical values of the Rolle determinant form a null set, so that a regular
level `δ` of the Rolle determinant can be chosen below any prescribed bound. -/
def ETSliceNull (E : ETData N (rt + 1) n re) (y : Fin N → ℝ) : Prop :=
  MeasureTheory.volume {t : ℝ | Fin.snoc y t ∈
    E.rolleMap '' {z | (fderiv ℝ E.rolleMap z).det = 0}} = 0

/-- The genericity bundle of the elimination step (the analogue of `Work.WilE2.KhoGood`). -/
def ETGood (E : ETData N (rt + 1) n re) (y : Fin N → ℝ) : Prop :=
  E.ETSubmersion y ∧ E.ETRegValue y ∧ E.ETSliceNull y

end ETData

/-! ## §6. The recursion bound and the induction statement -/

/-- **The recursion bound of the ET induction.**  `ETB q rt N D` bounds the number of
nondegenerate zeros of a lifted system with `rt` arctan equations on `ℝ^{N+1}` whose degree sum
is `D`; the base case `rt = 0` is the exp-affine Khovanskii bound `q`, and one elimination step
(one sphere step and one Rolle step) multiplies the running degree sum by `N + 9` and increases
`N` by one. -/
def ETB (q : Polynomial ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, D => q.eval D
  | (rt + 1), N, D => ETB q rt (N + 1) ((N + 9) * (D + 11))

/-- **The induction statement (K3).**  For every bound `F` on the format there is a polynomial
bounding the number of nondegenerate zeros of every lifted system of format `N + 1 + re ≤ F`. -/
def SepET (F : ℕ) : Prop :=
  ∃ p : Polynomial ℕ, ∀ (N rt n re : ℕ) (E : ETData N rt n re) (s : Finset (Fin (N + 1) → ℝ)),
    N + 1 + re ≤ F → (∀ z ∈ s, E.Nondegen z) →
      s.card ≤ p.eval (∑ i, atomDeg (E.G i) + rt)

end Work.WilE3K
