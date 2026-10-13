/-
  WilG4c / FibDiscMain / FibDiscAux — vocabulary for the proof that the *fibre-wise*
  discontinuity locus of an `Ω`-definable function is `Ω`-definable with format and degree
  uniform in the degree parameter `D`.

  Reading `H : ℝ^{p+N} → ℝ` as a family `H(l, z)` (`l : Fin p → ℝ` the parameters, `z` the
  fibre coordinates), the *fibre-wise* discontinuity (see `Work.WilG4c.fibDisc`) is the set of
  `w = (w_l, w_z)` at which the fibre function `z ↦ H(w_l, z)` is discontinuous at `w_z`.

  Its `ε`-`δ` description (the `∃ε>0 ∀δ>0 ∃z'` chain, where the parameter part of the witness is
  *not* quantified — that is exactly what distinguishes `fibDisc` from the ordinary
  discontinuity locus `disc (famFun H)`) is realised in the ambient space

    `ℝ^{bigA} = ℝ^{p+N+2} × ℝ^{N+2}`,   coordinates `(w, ε, δ | z', s, t)`,

  where the point `w` appears **once**: the "near point" `(w_l, z')` shares its parameter
  coordinates `w_l` with `w`.  The pieces of the (quantifier-free) matrix are

  * `gxSet H` — `s = H(w_l ⌢ z')`, a reindexed copy of `graphOf H` (`coordPre` along `gxMap`),
  * `gySet H` — `t = H(w)`, likewise (along `gyMap`),
  * `ballSet` — `Σ_j (z'_j - w_z_j)² < δ²`, the positivity set of `δ² - Σ_j (z'_j - w_z_j)²`,
  * `ineqSet` — `ε² ≤ (s - t)²`, the complement of the positivity set of `ε² - (s-t)²`,

  and `innerA H` is their intersection.  The quantifier chain is

    `bodyA H`    = `projN (N+2) (innerA H)`            — `∃ z' s t`
    `existDA H`  = `projN 1 (posDSet ∩ (bodyA H)ᶜ)`     — `∃ δ > 0, ¬ ·`
    `forallDA H` = `(existDA H)ᶜ`                       — `∀ δ > 0`
    `resBA H`    = `posESet ∩ forallDA H`               — `ε > 0 ∧ ·`
    `resA H`     = `projN 1 (resBA H)`                  — `∃ ε > 0`

  so that `resA H = fibDisc H` (`resA_eq_fibDisc` in the main module) and `mem_bodyA` /
  `mem_resA` are the unfoldings.
-/
import Mathlib
import Submission.Work.WilG4c.FibreCoreDefs
import Submission.Work.WilG1.Cell.Junk.DiscDefs
import Submission.Work.WilG5.Basic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000
noncomputable section
open Classical
open scoped BigOperators

namespace Work.WilG4c.FibDiscMain

open WilkiesDesign

/-! ## 1. The ambient spaces and the coordinate index maps

Throughout `p` is the number of *parameter* coordinates and `N` the number of *fibre*
coordinates; the dimension of the outer space is `p + N`.
-/

/-- Dimension of the `(w, ε, δ)`-space. -/
abbrev midA (p N : ℕ) : ℕ := p + N + 2

/-- Dimension of the `(w, ε)`-space. -/
abbrev smallA (p N : ℕ) : ℕ := (p + N) + 1

/-- Dimension of the big space `(w, ε, δ | z', s, t)`. -/
abbrev bigA (p N : ℕ) : ℕ := (p + N + 2) + (N + 2)

/-- The `i`-th parameter coordinate `w_l i`, inside the `(w, ε, δ)`-space. -/
def bPar (p N : ℕ) (i : Fin p) : Fin (midA p N) :=
  Fin.castAdd 1 (Fin.castAdd 1 (Fin.castAdd N i))

/-- The `j`-th fibre coordinate `w_z j`, inside the `(w, ε, δ)`-space. -/
def bFib (p N : ℕ) (j : Fin N) : Fin (midA p N) :=
  Fin.castAdd 1 (Fin.castAdd 1 (Fin.natAdd p j))

/-- The radius coordinate `ε`, inside the `(w, ε, δ)`-space. -/
def bEps (p N : ℕ) : Fin (midA p N) := Fin.castAdd 1 (Fin.natAdd (p + N) (0 : Fin 1))

/-- The tolerance coordinate `δ`, inside the `(w, ε, δ)`-space. -/
def bDel (p N : ℕ) : Fin (midA p N) := Fin.natAdd (p + N + 1) (0 : Fin 1)

/-- The `j`-th coordinate of `w = (w_l, w_z)`, inside the `(w, ε, δ)`-space. -/
def bAll (p N : ℕ) (j : Fin (p + N)) : Fin (midA p N) :=
  Fin.addCases (fun i : Fin p => bPar p N i) (fun j' : Fin N => bFib p N j') j

/-- The `i`-th parameter coordinate `w_l i`, inside the big space (the point `w` itself). -/
def par (p N : ℕ) (i : Fin p) : Fin (bigA p N) := Fin.castAdd (N + 2) (bPar p N i)

/-- The `j`-th fibre coordinate `w_z j`, inside the big space. -/
def fib (p N : ℕ) (j : Fin N) : Fin (bigA p N) := Fin.castAdd (N + 2) (bFib p N j)

/-- The radius coordinate `ε` in the big space. -/
def epsIx (p N : ℕ) : Fin (bigA p N) := Fin.castAdd (N + 2) (bEps p N)

/-- The tolerance coordinate `δ` in the big space. -/
def delIx (p N : ℕ) : Fin (bigA p N) := Fin.castAdd (N + 2) (bDel p N)

/-- The `j`-th coordinate of `w` in the big space. -/
def allIx (p N : ℕ) (j : Fin (p + N)) : Fin (bigA p N) := Fin.castAdd (N + 2) (bAll p N j)

/-- The `j`-th witness coordinate `z' j`, in the big space. -/
def zp (p N : ℕ) (j : Fin N) : Fin (bigA p N) :=
  Fin.natAdd (p + N + 2) (Fin.castAdd 1 (Fin.castAdd 1 j))

/-- The coordinate `s = H(w_l ⌢ z')`, in the big space. -/
def sIx (p N : ℕ) : Fin (bigA p N) :=
  Fin.natAdd (p + N + 2) (Fin.castAdd 1 (Fin.natAdd N (0 : Fin 1)))

/-- The coordinate `t = H(w)`, in the big space. -/
def tIx (p N : ℕ) : Fin (bigA p N) :=
  Fin.natAdd (p + N + 2) (Fin.natAdd (N + 1) (0 : Fin 1))

/-- The near point `(w_l, z')` read inside the big space: the `j`-th coordinate of the point at
which `H` is evaluated to define `s`. -/
def icombX (p N : ℕ) : Fin (p + N) → Fin (bigA p N) :=
  Fin.addCases (fun i : Fin p => par p N i) (fun j : Fin N => zp p N j)

/-- The index map underlying `gxSet`: the point `(w_l, z', s)` of `ℝ^{p+N+1}` read in the big
space. -/
def gxMap (p N : ℕ) : Fin (p + N + 1) → Fin (bigA p N) :=
  Fin.lastCases (motive := fun _ => Fin (bigA p N)) (sIx p N) (icombX p N)

/-- The index map underlying `gySet`: the point `(w, t)` of `ℝ^{p+N+1}` read in the big space. -/
def gyMap (p N : ℕ) : Fin (p + N + 1) → Fin (bigA p N) :=
  Fin.lastCases (motive := fun _ => Fin (bigA p N)) (tIx p N) (fun j => allIx p N j)

/-! ## 2. Reading `Fin.append`-points in these coordinates -/

/-- A point of the `(w, ε, δ)`-space of the form `(w, ε, δ)` read at a big-space index. -/
@[simp] theorem app_sIx (p N : ℕ) (u : Fin (midA p N) → ℝ) (w : Fin (N + 2) → ℝ) :
    Fin.append u w (sIx p N) = w (Fin.castAdd 1 (Fin.natAdd N (0 : Fin 1))) := by
  simp [sIx, Fin.append_right]

@[simp] theorem app_tIx (p N : ℕ) (u : Fin (midA p N) → ℝ) (w : Fin (N + 2) → ℝ) :
    Fin.append u w (tIx p N) = w (Fin.natAdd (N + 1) (0 : Fin 1)) := by
  simp [tIx, Fin.append_right]

@[simp] theorem app_par (p N : ℕ) (u : Fin (midA p N) → ℝ) (w : Fin (N + 2) → ℝ)
    (i : Fin p) : Fin.append u w (par p N i) = u (bPar p N i) := by
  simp [par, Fin.append_left]

@[simp] theorem app_zp (p N : ℕ) (u : Fin (midA p N) → ℝ) (w : Fin (N + 2) → ℝ)
    (j : Fin N) : Fin.append u w (zp p N j) = w (Fin.castAdd 1 (Fin.castAdd 1 j)) := by
  simp [zp, Fin.append_right]

@[simp] theorem app_fib (p N : ℕ) (u : Fin (midA p N) → ℝ) (w : Fin (N + 2) → ℝ)
    (j : Fin N) : Fin.append u w (fib p N j) = u (bFib p N j) := by
  simp [fib, Fin.append_left]

@[simp] theorem app_allIx (p N : ℕ) (u : Fin (midA p N) → ℝ) (w : Fin (N + 2) → ℝ)
    (j : Fin (p + N)) : Fin.append u w (allIx p N j) = u (bAll p N j) := by
  simp [allIx, Fin.append_left]

@[simp] theorem app_epsIx (p N : ℕ) (u : Fin (midA p N) → ℝ) (w : Fin (N + 2) → ℝ) :
    Fin.append u w (epsIx p N) = u (bEps p N) := by
  simp [epsIx, Fin.append_left]

@[simp] theorem app_delIx (p N : ℕ) (u : Fin (midA p N) → ℝ) (w : Fin (N + 2) → ℝ) :
    Fin.append u w (delIx p N) = u (bDel p N) := by
  simp [delIx, Fin.append_left]

/-! ## 3. The witness point `(z', s, t)` of `ℝ^{N+2}` and the point `(w, ε, δ)` -/

/-- The point `(z', s, t)` of `ℝ^{N+2}`. -/
def mkPt (N : ℕ) (z' : Fin N → ℝ) (s t : ℝ) : Fin (N + 2) → ℝ :=
  @Fin.append (N + 1) 1 ℝ (Fin.append z' (fun _ : Fin 1 => s)) (fun _ : Fin 1 => t)

/-- The point `(w, ε, δ)` of the `(w, ε, δ)`-space. -/
abbrev mkMid (p N : ℕ) (w : Fin (p + N) → ℝ) (ε δ : ℝ) : Fin (midA p N) → ℝ :=
  @Fin.append (p + N + 1) 1 ℝ (Fin.append w (fun _ : Fin 1 => ε)) (fun _ : Fin 1 => δ)

@[simp] theorem mkPt_castAdd {N : ℕ} (z' : Fin N → ℝ) (s t : ℝ) (j : Fin N) :
    mkPt N z' s t (Fin.castAdd 1 (Fin.castAdd 1 j)) = z' j := by
  simp [mkPt, Fin.append_left]

@[simp] theorem mkPt_eps {N : ℕ} (z' : Fin N → ℝ) (s t : ℝ) :
    mkPt N z' s t (Fin.castAdd 1 (Fin.natAdd N (0 : Fin 1))) = s := by
  simp [mkPt, Fin.append_left]

@[simp] theorem mkPt_del {N : ℕ} (z' : Fin N → ℝ) (s t : ℝ) :
    mkPt N z' s t (Fin.natAdd (N + 1) (0 : Fin 1)) = t := by
  simp [mkPt, Fin.append_right]

/-! ## 4. The pieces of the matrix -/

/-- `s = H(w_l ⌢ z')`: a reindexed copy of `graphOf H`. -/
def gxSet (p N : ℕ) (H : (Fin (p + N) → ℝ) → ℝ) : Set (Fin (bigA p N) → ℝ) :=
  Work.WilG5.coordPre (gxMap p N) (graphOf H)

/-- `t = H(w)`: a reindexed copy of `graphOf H`. -/
def gySet (p N : ℕ) (H : (Fin (p + N) → ℝ) → ℝ) : Set (Fin (bigA p N) → ℝ) :=
  Work.WilG5.coordPre (gyMap p N) (graphOf H)

/-- The polynomial `δ² - Σ_j (z'_j - w_z_j)²`. -/
def ballPoly (p N : ℕ) : MvPolynomial (Fin (bigA p N)) ℝ :=
  MvPolynomial.X (delIx p N) ^ 2 -
    ∑ j : Fin N, (MvPolynomial.X (zp p N j) - MvPolynomial.X (fib p N j)) ^ 2

/-- The polynomial `ε² - (s - t)²`. -/
def ineqPoly (p N : ℕ) : MvPolynomial (Fin (bigA p N)) ℝ :=
  MvPolynomial.X (epsIx p N) ^ 2 - (MvPolynomial.X (sIx p N) - MvPolynomial.X (tIx p N)) ^ 2

/-- The condition `Σ_j (z'_j - w_z_j)² < δ²`. -/
def ballSet (p N : ℕ) : Set (Fin (bigA p N) → ℝ) :=
  {Z | 0 < MvPolynomial.eval Z (ballPoly p N)}

/-- The condition `ε² ≤ (s - t)²`. -/
def ineqSet (p N : ℕ) : Set (Fin (bigA p N) → ℝ) :=
  {Z | 0 < MvPolynomial.eval Z (ineqPoly p N)}ᶜ

/-- The quantifier-free matrix of the fibre-discontinuity condition. -/
def innerA (p N : ℕ) (H : (Fin (p + N) → ℝ) → ℝ) : Set (Fin (bigA p N) → ℝ) :=
  ((gxSet p N H ∩ gySet p N H) ∩ ballSet p N) ∩ ineqSet p N

/-- `∃ z' s t`: the `(w, ε, δ)`-parameters admitting a witness, i.e. the "body" of the `ε`-`δ`
formulation. -/
def bodyA (p N : ℕ) (H : (Fin (p + N) → ℝ) → ℝ) : Set (Fin (midA p N) → ℝ) :=
  Work.WilG5.projN (N + 2) (innerA p N H)

/-- `∃ δ > 0` with the body failing. -/
def existDA (p N : ℕ) (H : (Fin (p + N) → ℝ) → ℝ) : Set (Fin (smallA p N) → ℝ) :=
  Work.WilG5.projN 1 (Work.WilG1.Cell.Junk.posDSet (p + N) ∩ (bodyA p N H)ᶜ)

/-- `∀ δ > 0`, the body holding. -/
def forallDA (p N : ℕ) (H : (Fin (p + N) → ℝ) → ℝ) : Set (Fin (smallA p N) → ℝ) :=
  (existDA p N H)ᶜ

/-- `ε > 0` and the `∀ δ > 0` condition. -/
def resBA (p N : ℕ) (H : (Fin (p + N) → ℝ) → ℝ) : Set (Fin (smallA p N) → ℝ) :=
  Work.WilG1.Cell.Junk.posESet (p + N) ∩ forallDA p N H

/-- `∃ ε > 0`: the `ε`-`δ` description of the fibre-wise discontinuity locus. -/
def resA (p N : ℕ) (H : (Fin (p + N) → ℝ) → ℝ) : Set (Fin (p + N) → ℝ) :=
  Work.WilG5.projN 1 (resBA p N H)

/-! ## 5. Unfolding the pieces -/

theorem mem_gxSet {p N : ℕ} {H : (Fin (p + N) → ℝ) → ℝ} {Z : Fin (bigA p N) → ℝ} :
    Z ∈ gxSet p N H ↔
      Z (sIx p N) =
        H (Fin.append (fun i : Fin p => Z (par p N i)) (fun j : Fin N => Z (zp p N j))) := by
  have harg : (fun j : Fin (p + N) => Z (icombX p N j))
      = Fin.append (fun i : Fin p => Z (par p N i)) (fun j : Fin N => Z (zp p N j)) := by
    funext j
    cases j using Fin.addCases with
    | left i => simp only [icombX, Fin.addCases_left, par, Fin.append_left]
    | right j' => simp only [icombX, Fin.addCases_right, zp, Fin.append_right]
  simp only [gxSet, Work.WilG5.coordPre, Set.mem_ofPred_eq, graphOf, Function.comp_def]
  have hlast : gxMap p N (Fin.last (p + N)) = sIx p N := Fin.lastCases_last
  have hcast : ∀ j : Fin (p + N), gxMap p N (Fin.castSucc j) = icombX p N j :=
    fun j => Fin.lastCases_castSucc j
  have hinit : Fin.init (fun j => Z (gxMap p N j)) = fun j => Z (icombX p N j) := by
    funext j
    show Z (gxMap p N (Fin.castSucc j)) = Z (icombX p N j)
    rw [hcast j]
  rw [hlast, hinit, harg]

theorem mem_gySet {p N : ℕ} {H : (Fin (p + N) → ℝ) → ℝ} {Z : Fin (bigA p N) → ℝ} :
    Z ∈ gySet p N H ↔ Z (tIx p N) = H (fun j : Fin (p + N) => Z (allIx p N j)) := by
  simp only [gySet, Work.WilG5.coordPre, Set.mem_ofPred_eq, graphOf, Function.comp_def]
  have hlast : gyMap p N (Fin.last (p + N)) = tIx p N := Fin.lastCases_last
  have hcast : ∀ j : Fin (p + N), gyMap p N (Fin.castSucc j) = allIx p N j :=
    fun j => Fin.lastCases_castSucc j
  have hinit : Fin.init (fun j => Z (gyMap p N j)) = fun j : Fin (p + N) => Z (allIx p N j) := by
    funext j
    show Z (gyMap p N (Fin.castSucc j)) = Z (allIx p N j)
    rw [hcast j]
  rw [hlast, hinit]

theorem mem_ballSet {p N : ℕ} {Z : Fin (bigA p N) → ℝ} :
    Z ∈ ballSet p N ↔
      (∑ j : Fin N, (Z (zp p N j) - Z (fib p N j)) ^ 2) < Z (delIx p N) ^ 2 := by
  rw [ballSet, Set.mem_ofPred_eq]
  simp only [ballPoly, MvPolynomial.eval_sub, MvPolynomial.eval_pow, MvPolynomial.eval_sum,
    MvPolynomial.eval_X]
  constructor <;> intro h <;> linarith

theorem mem_ineqSet {p N : ℕ} {Z : Fin (bigA p N) → ℝ} :
    Z ∈ ineqSet p N ↔ Z (epsIx p N) ^ 2 ≤ (Z (sIx p N) - Z (tIx p N)) ^ 2 := by
  show ¬ (0 < MvPolynomial.eval Z (ineqPoly p N)) ↔ _
  rw [ineqPoly]
  simp only [MvPolynomial.eval_sub, MvPolynomial.eval_pow, MvPolynomial.eval_X]
  constructor <;> intro h <;> linarith

theorem mem_innerA {p N : ℕ} {H : (Fin (p + N) → ℝ) → ℝ} {Z : Fin (bigA p N) → ℝ} :
    Z ∈ innerA p N H ↔
      Z (sIx p N) =
        H (Fin.append (fun i : Fin p => Z (par p N i)) (fun j : Fin N => Z (zp p N j))) ∧
      Z (tIx p N) = H (fun j : Fin (p + N) => Z (allIx p N j)) ∧
      (∑ j : Fin N, (Z (zp p N j) - Z (fib p N j)) ^ 2) < Z (delIx p N) ^ 2 ∧
      Z (epsIx p N) ^ 2 ≤ (Z (sIx p N) - Z (tIx p N)) ^ 2 := by
  show ((Z ∈ gxSet p N H ∧ Z ∈ gySet p N H) ∧ Z ∈ ballSet p N) ∧ Z ∈ ineqSet p N ↔ _
  simp only [mem_gxSet, mem_gySet, mem_ballSet, mem_ineqSet]
  tauto

/-- Unfolding the body: the `(w, ε, δ)`-parameters admitting a witness `z'` with
`Σ_j (z'_j - w_z_j)² < δ²` and `ε² ≤ (H(w_l ⌢ z') - H(w))²`. -/
theorem mem_bodyA {p N : ℕ} {H : (Fin (p + N) → ℝ) → ℝ} {u : Fin (midA p N) → ℝ} :
    u ∈ bodyA p N H ↔ ∃ z' : Fin N → ℝ,
      (∑ j : Fin N, (z' j - u (bFib p N j)) ^ 2) < (u (bDel p N)) ^ 2 ∧
      (u (bEps p N)) ^ 2 ≤ (H (Fin.append (fun i : Fin p => u (bPar p N i)) z')
        - H (fun j : Fin (p + N) => u (bAll p N j))) ^ 2 := by
  rw [bodyA, Work.WilG5.projN, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨w, hw⟩
    rw [mem_innerA] at hw
    simp only [app_sIx, app_tIx, app_par, app_zp, app_fib, app_allIx, app_epsIx, app_delIx] at hw
    obtain ⟨h1, h2, h3, h4⟩ := hw
    refine ⟨fun j => w (Fin.castAdd 1 (Fin.castAdd 1 j)), h3, ?_⟩
    rw [h1, h2] at h4
    exact h4
  · rintro ⟨z', h3, h4⟩
    refine ⟨mkPt N z' (H (Fin.append (fun i : Fin p => u (bPar p N i)) z'))
      (H (fun j : Fin (p + N) => u (bAll p N j))), ?_⟩
    rw [mem_innerA]
    simp only [app_sIx, app_tIx, app_par, app_zp, app_fib, app_allIx, app_epsIx, app_delIx,
      mkPt_castAdd, mkPt_eps, mkPt_del]
    exact ⟨trivial, trivial, h3, h4⟩

/-! ## 6. Reading a point of the form `(w, ε, δ)` in the block-local coordinates -/

@[simp] theorem appAA_bPar (p N : ℕ) (w : Fin (p + N) → ℝ) (e d : Fin 1 → ℝ) (i : Fin p) :
    Fin.append (Fin.append w e) d (bPar p N i) = w (Fin.castAdd N i) := by
  simp [bPar, Fin.append_left]

@[simp] theorem appAA_bFib (p N : ℕ) (w : Fin (p + N) → ℝ) (e d : Fin 1 → ℝ) (j : Fin N) :
    Fin.append (Fin.append w e) d (bFib p N j) = w (Fin.natAdd p j) := by
  simp [bFib, Fin.append_left]

@[simp] theorem appAA_bEps (p N : ℕ) (w : Fin (p + N) → ℝ) (e d : Fin 1 → ℝ) :
    Fin.append (Fin.append w e) d (bEps p N) = e 0 := by
  simp [bEps, Fin.append_left, Fin.append_right]

@[simp] theorem appAA_bDel (p N : ℕ) (w : Fin (p + N) → ℝ) (e d : Fin 1 → ℝ) :
    Fin.append (Fin.append w e) d (bDel p N) = d 0 := by
  simp [bDel, Fin.append_right]

@[simp] theorem appAA_bAll (p N : ℕ) (w : Fin (p + N) → ℝ) (e d : Fin 1 → ℝ)
    (j : Fin (p + N)) : Fin.append (Fin.append w e) d (bAll p N j) = w j := by
  cases j using Fin.addCases with
  | left i => simp only [bAll, Fin.addCases_left, appAA_bPar]
  | right j' => simp only [bAll, Fin.addCases_right, appAA_bFib]

/-- The `w`-point, read through `bAll` at the point `(w, ε, δ)`. -/
theorem bAll_appendAA (p N : ℕ) (w : Fin (p + N) → ℝ) (e d : Fin 1 → ℝ) :
    (fun j : Fin (p + N) => Fin.append (Fin.append w e) d (bAll p N j)) = w :=
  funext fun j => appAA_bAll p N w e d j

/-- Splitting a point `w : ℝ^{p+N}` into its parameter and its fibre part and reassembling
it gives `w` back. -/
theorem append_split (p N : ℕ) (w : Fin (p + N) → ℝ) :
    Fin.append (fun i : Fin p => w (Fin.castAdd N i)) (fun j : Fin N => w (Fin.natAdd p j))
      = w := by
  funext j
  cases j using Fin.addCases with
  | left i => simp only [Fin.append_left]
  | right j' => simp only [Fin.append_right]

/-! ## 7. `Ω`-membership uniform in the degree parameter

The sets of §4 are built from `graphOf H` (a fixed format `F`, arbitrary degree parameter `D`)
by intersections, complements, coordinate reindexings, positivity sets and projections.  None of
these operations lets the format or the degree *polynomial* depend on `D` or on `H`: the format
is always a numeral and the degree is always a polynomial in the variable that is evaluated at
`D`.  `UOA` packages this: a family `X D H` is `UOA` if it is `Ω`-definable with a format and a
degree polynomial independent of `D` and `H`. -/

/-- Families of `Ω`-sets, indexed by the degree parameter `D` and by a defining function `H`,
that are `Ω`-definable with format and degree polynomial independent of `D` and `H`. -/
def UOA (S : WilkiesDesign.SOMin) (m F n : ℕ)
    (X : ℕ → ((Fin m → ℝ) → ℝ) → Set (Fin n → ℝ)) : Prop :=
  ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (D : ℕ) (H : (Fin m → ℝ) → ℝ),
    graphOf H ∈ S.Ω F D (m + 1) → X D H ∈ S.Ω a (b.eval D) n

namespace UOA

variable {S : WilkiesDesign.SOMin} {m F n : ℕ}
  {X Y : ℕ → ((Fin m → ℝ) → ℝ) → Set (Fin n → ℝ)}

theorem of_hyp : UOA S m F (m + 1) (fun _ H => graphOf H) :=
  ⟨F, Polynomial.X, fun D H hH => by simpa using hH⟩

theorem compl (h : UOA S m F n X) : UOA S m F n (fun D H => (X D H)ᶜ) := by
  obtain ⟨a, b, hb⟩ := h
  exact ⟨a + 1, b, fun D H hH => S.compl (hb D H hH)⟩

theorem inter (hX : UOA S m F n X) (hY : UOA S m F n Y) :
    UOA S m F n (fun D H => X D H ∩ Y D H) := by
  obtain ⟨a₁, b₁, h₁⟩ := hX
  obtain ⟨a₂, b₂, h₂⟩ := hY
  refine ⟨max a₁ a₂ + 1, b₁ + b₂, fun D H hH => ?_⟩
  simpa only [Polynomial.eval_add] using Work.WilG1.Omega.inter₂ (h₁ D H hH) (h₂ D H hH)

theorem projN (k : ℕ) {X : ℕ → ((Fin m → ℝ) → ℝ) → Set (Fin (n + k) → ℝ)}
    (h : UOA S m F (n + k) X) :
    UOA S m F n (fun D H => Work.WilG5.projN k (X D H)) := by
  obtain ⟨a, b, hb⟩ := h
  exact ⟨a + k, b, fun D H hH =>
    Work.WilG5.projN_mem (S := S) (n := n) k a (b.eval D) (hb D H hH)⟩

theorem coordPre {n' : ℕ} (ι : Fin n → Fin n') (h : UOA S m F n X) :
    UOA S m F n' (fun D H => Work.WilG5.coordPre ι (X D H)) := by
  obtain ⟨a, b, hb⟩ := h
  refine ⟨a + 64 * (n' + n) + 64, b + Polynomial.C (32 * (n' + n) + 32), fun D H hH => ?_⟩
  rw [Polynomial.eval_add, Polynomial.eval_C]
  exact Work.WilG5.coordPre_mem (S := S) (ι := ι) (hb D H hH)

theorem pos (P : MvPolynomial (Fin n) ℝ) :
    UOA S m F n (fun _ _ => {z | 0 < MvPolynomial.eval z P}) :=
  ⟨n + 2, Polynomial.C (P.totalDegree + 2), fun D _ _ =>
    Work.WilG1.Calc.pos_mem (S := S) (m := n) D P⟩

end UOA

end Work.WilG4c.FibDiscMain
