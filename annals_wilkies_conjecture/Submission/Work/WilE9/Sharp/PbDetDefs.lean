/-
  WilE9 / Sharp — vocabulary for the fibre Jacobian of the pulled-back system.

  This module only records the *indices* and the two matrices involved in
  `Work.WilE9.Sharp.pb_det_ne_zero`, so that the auxiliary lemmas about it can be stated
  uniformly.

  * `Mmat n m r c h z` is the fibre Jacobian `∂(pbF j)/∂(fibre l)` of the pulled-back system,
    evaluated at the ambient point `z`.  Its rows and columns are the *fibre indices*
    `Fin (qpb n m)` (`fS`, `fY`, `fW`, `fT`, `fU`, `fA`), so that the ambient coordinate of
    column `l` is `Fin.natAdd n l`.
  * `Hmat n m r c h z` is the Jacobian of the stratum equations `h` in the `(τ, aux)` directions,
    again evaluated at `z` (reading `z` in the stratum coordinates `pbStrat z`).  This is the
    matrix whose invertibility is the hypothesis `hP` of `pb_det_ne_zero`.
  * `hRow n m a` is the row of `Mmat` carrying the stratum equation `h a`, and `hColIdx n m l`
    is the column of `Mmat` carrying the fibre coordinate `(τ, aux) l`
    (`l = 0 ↦ τ`, `l = b + 1 ↦ aux b`).  `wVec v` is `v` restricted to these columns.
-/
import Submission.Work.WilE9.Sharp.PbSystem

set_option autoImplicit false
noncomputable section
namespace Work.WilE9.Sharp
open WilkiesDesign WilkiesDesign.E

/-- The row of the pulled-back system carrying the stratum equation `h a`.  The equations of the
pulled-back system are, in order, `τ - s u` (index `0`), `y i - x i * w i`, `y i ^ 2 + w i ^ 2 - 1`,
`τ ^ 2 + u ^ 2 - 1`, and then `h 0, …, h m`, so `h a` sits at index `2 * n + 2 + a`. -/
def hRow (n m : ℕ) (a : Fin (1 + m)) : Fin (qpb n m) :=
  ⟨2 * n + 2 + a.val, by have := a.isLt; simp [qpb]; omega⟩

/-- The fibre coordinate of column `natAdd n ·` corresponding to the stratum coordinate
`(τ, aux) l`: `l = 0` gives `τ` (the fibre index `fT`), `l = b + 1` gives `aux b` (`fA b`). -/
def hColIdx (n m : ℕ) (l : Fin (1 + m)) : Fin (qpb n m) :=
  if h : (l : ℕ) = 0 then fT n m else fA n m ⟨(l : ℕ) - 1, by have := l.isLt; omega⟩

/-- The fibre Jacobian of the pulled-back system `pbF`, evaluated at `z`. -/
def Mmat (n m r : ℕ) (c : EAChain (n + (1 + m)) r)
    (h : Fin (1 + m) → EAPoly (n + (1 + m)) r) (z : Fin (Npb n m) → ℝ) :
    Matrix (Fin (qpb n m)) (Fin (qpb n m)) ℝ :=
  Matrix.of fun j l => eaEval (pbChain c) (eaD (pbChain c) (Fin.natAdd n l) (pbF n m r h j)) z

/-- The Jacobian of the stratum equations `h` in the `(τ, aux)` directions, evaluated at `z`. -/
def Hmat (n m r : ℕ) (c : EAChain (n + (1 + m)) r)
    (h : Fin (1 + m) → EAPoly (n + (1 + m)) r) (z : Fin (Npb n m) → ℝ) :
    Matrix (Fin (1 + m)) (Fin (1 + m)) ℝ :=
  Matrix.of fun a l => eaEval c (eaD c (Fin.natAdd n l) (h a)) (pbStrat z)

/-- The `(τ, aux)`-coordinates of a vector, as a vector indexed by `Fin (1 + m)`. -/
def wVec {n m : ℕ} (v : Fin (qpb n m) → ℝ) : Fin (1 + m) → ℝ := fun l => v (hColIdx n m l)

/-- The ambient coordinate of the fibre index `l`, recorded at the ambient type `Fin (Npb n m)`.
It is definitionally `Fin.natAdd n l`, but stating it at the ambient type avoids the
`Fin (n + qpb n m)`-vs-`Fin (Npb n m)` mismatch in `if`-conditions. -/
def ambIdx (n m : ℕ) (l : Fin (qpb n m)) : Fin (Npb n m) := Fin.natAdd n l

/-- The fibre index of the pulled-back column carrying the stratum coordinate `i`: `i < n` gives
the coordinate `y i`, `i = n` the coordinate `τ`, and `i = n + 1 + b` the coordinate `aux b`. -/
def kap (n m : ℕ) : Fin (n + (1 + m)) → Fin (qpb n m) := fun i =>
  if h : (i : ℕ) < n then fY n m ⟨i, h⟩
  else if _ : (i : ℕ) = n then fT n m
  else fA n m ⟨(i : ℕ) - (n + 1), by have := i.isLt; omega⟩

@[simp] theorem hRow_val {n m : ℕ} (a : Fin (1 + m)) : (hRow n m a : ℕ) = 2 * n + 2 + a.val := rfl

@[simp] theorem hColIdx_zero {n m : ℕ} : hColIdx n m 0 = fT n m := by
  simp [hColIdx]

theorem hColIdx_of_ne_zero {n m : ℕ} {l : Fin (1 + m)} (hl : (l : ℕ) ≠ 0) :
    hColIdx n m l = fA n m ⟨(l : ℕ) - 1, by have := l.isLt; omega⟩ := by
  simp only [hColIdx, dif_neg hl]

theorem hColIdx_ne_zero {n m : ℕ} {l : Fin (1 + m)} (hl : (l : ℕ) ≠ 0) :
    (hColIdx n m l : ℕ) = 2 * n + 2 + (l : ℕ) := by
  rw [hColIdx_of_ne_zero hl]
  simp only [fA]
  omega

theorem hColIdx_zero_val {n m : ℕ} : (hColIdx n m 0 : ℕ) = 2 * n + 1 := by
  simp [hColIdx, fT]

theorem Mmat_apply {n m r : ℕ} (c : EAChain (n + (1 + m)) r)
    (h : Fin (1 + m) → EAPoly (n + (1 + m)) r) (z : Fin (Npb n m) → ℝ)
    (j l : Fin (qpb n m)) :
    Mmat n m r c h z j l =
      eaEval (pbChain c) (eaD (pbChain c) (Fin.natAdd n l) (pbF n m r h j)) z := rfl

theorem Hmat_apply {n m r : ℕ} (c : EAChain (n + (1 + m)) r)
    (h : Fin (1 + m) → EAPoly (n + (1 + m)) r) (z : Fin (Npb n m) → ℝ)
    (a l : Fin (1 + m)) :
    Hmat n m r c h z a l = eaEval c (eaD c (Fin.natAdd n l) (h a)) (pbStrat z) := rfl

theorem wVec_apply {n m : ℕ} (v : Fin (qpb n m) → ℝ) (l : Fin (1 + m)) :
    wVec v l = v (hColIdx n m l) := rfl

end Work.WilE9.Sharp
