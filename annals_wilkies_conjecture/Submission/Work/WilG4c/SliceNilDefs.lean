/-
  WilG4c / `SliceNilDefs` — the `Ω`-shape encoding of the *pointwise* fibre continuity of a
  family, used by `AlDgListSliceNil`.

  ## What is being encoded

  For `f : (Fin p → ℝ) → (Fin (n+1) → ℝ) → ℝ` the *pointwise* fibre continuity condition at a
  point `z = (l, u, v)` of `ℝ^{p+(n+1)+1}` (the last coordinate being the graph value) is

    `v = f l u ∧ ∀ ε > 0, ∃ δ > 0, ∀ y', (Σ_j (y'_j - u_j)² < δ²) → |f l y' - v| < ε`.

  The shape `ZpShape p n` realises exactly this set, in terms of the graph `famGraph f` (two
  `mem`-atoms: the free point itself, and the point `(l, y', v')`).

  The coordinates of the auxiliary space are laid out as

  * `0 … p-1`           : `l` (the parameter),
  * `p … p+n`           : `u` (the cube point),
  * `Nc`                : `v` (the graph value; `Nc = p + (n+1)`),
  * `Nc+1`              : `ε`,
  * `Nc+2`              : `tε`  (witness for `ε > 0`),
  * `Nc+3`              : `δ`,
  * `Nc+4`              : `tδ`  (witness for `δ > 0`),
  * `Nc+5+j`            : `y'_j`,
  * `Kz`                : `tΣ`  (witness for `Σ (y'_j-u_j)² < δ²`),
  * `Kz+1`              : `v'`  (the value of the family at `(l,y')`),
  * `Kz+2`              : `tD`  (witness for `(v'-v)² < ε²`),

  where `Kz = (Nc+5) + (n+1)`.

  Every strict inequality is coded by the standard *positivity gadget*: `Q > 0` is the same as
  `∃t, t²·Q - 1 = 0` (`posAtom`/`posGadget`).
-/
import Mathlib
import Submission.Work.WilG0.Main
import Submission.Work.WilG4c.SlicedDerivDefs
import Submission.Work.WilG4c.inflated_mem_m

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-! ## 1. The positivity gadget -/

/-- The atom `X_last ^ 2 * Q - 1` on `Fin (m+1)`: its zero set is non-empty in the last
coordinate exactly when `Q > 0`. -/
def posAtom {m : ℕ} (Q : MvPolynomial (Fin m) ℝ) : MvPolynomial (Fin (m + 1)) ℝ :=
  MvPolynomial.X (Fin.last m) ^ 2 * MvPolynomial.rename (Fin.castAdd 1) Q - 1

theorem eval_rename_castAdd {m : ℕ} (Q : MvPolynomial (Fin m) ℝ) (v : Fin (m + 1) → ℝ) :
    MvPolynomial.eval v (MvPolynomial.rename (Fin.castAdd 1) Q) =
      MvPolynomial.eval (Fin.init v) Q := by
  rw [MvPolynomial.eval_rename]
  rfl

theorem eval_posAtom {m : ℕ} (Q : MvPolynomial (Fin m) ℝ) (v : Fin (m + 1) → ℝ) :
    MvPolynomial.eval v (posAtom Q) =
      (v (Fin.last m)) ^ 2 * MvPolynomial.eval (Fin.init v) Q - 1 := by
  rw [posAtom, MvPolynomial.eval_sub, MvPolynomial.eval_mul, MvPolynomial.eval_pow,
    MvPolynomial.eval_X, map_one, eval_rename_castAdd]

/-- The positivity gadget: the set `{u | 0 < eval u Q}`, as the realisation of a shape that
exists in the last coordinate. -/
theorem posEx_realize {m : ℕ} (Q : MvPolynomial (Fin m) ℝ) :
    (OShape.ex (OShape.poly (m + 1))).realize (posAtom Q) =
      {u : Fin m → ℝ | 0 < MvPolynomial.eval u Q} := by
  ext u
  simp only [OShape.realize, WilkiesDesign.projLast, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨t, ht⟩
    rw [eval_posAtom, Fin.init_snoc, Fin.snoc_last] at ht
    have h : MvPolynomial.eval u Q * t ^ 2 = 1 := by linarith
    nlinarith [sq_nonneg t, sq_nonneg (MvPolynomial.eval u Q)]
  · intro h
    refine ⟨(Real.sqrt (MvPolynomial.eval u Q))⁻¹, ?_⟩
    rw [eval_posAtom, Fin.init_snoc, Fin.snoc_last]
    have hs : Real.sqrt (MvPolynomial.eval u Q) ^ 2 = MvPolynomial.eval u Q :=
      Real.sq_sqrt (le_of_lt h)
    have hne : MvPolynomial.eval u Q ≠ 0 := ne_of_gt h
    rw [inv_pow, hs, inv_mul_cancel₀ hne]
    ring

/-- The degree of the positivity atom. -/
theorem totalDegree_posAtom_le {m : ℕ} (Q : MvPolynomial (Fin m) ℝ) :
    (posAtom Q).totalDegree ≤ 2 + Q.totalDegree := by
  have hmul : (MvPolynomial.X (Fin.last m) ^ 2 * MvPolynomial.rename (Fin.castAdd 1) Q :
      MvPolynomial (Fin (m + 1)) ℝ).totalDegree ≤ 2 + Q.totalDegree := by
    refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
    have ha : (MvPolynomial.X (Fin.last m) ^ 2 : MvPolynomial (Fin (m + 1)) ℝ).totalDegree
        ≤ 2 := by
      rw [MvPolynomial.totalDegree_X_pow]
    have hb : (MvPolynomial.rename (Fin.castAdd 1) Q).totalDegree ≤ Q.totalDegree :=
      MvPolynomial.totalDegree_rename_le _ _
    omega
  rw [posAtom]
  refine le_trans (MvPolynomial.totalDegree_sub _ _) (max_le hmul ?_)
  simp

/-! ## 2. Universal quantification over a block of coordinates -/

/-- `forallIter m k σ` universally quantifies the last `k` coordinates of `σ`.  Each universal
quantifier is `¬∃¬`, and the coordinate stripped first is the largest one, so the block of `k`
coordinates is quantified in decreasing coordinate order. -/
def forallIter (m : ℕ) : (k : ℕ) → OShape (m + k) → OShape m
  | 0, σ => σ
  | k + 1, σ => forallIter m k (OShape.neg (OShape.ex (OShape.neg σ)))

/-- The data of `forallIter m k σ`: the data type does not change. -/
def forallIterData (m : ℕ) :
    (k : ℕ) → (σ : OShape (m + k)) → σ.Data → (forallIter m k σ).Data
  | 0, σ, d => d
  | k + 1, σ, d => forallIterData m k (OShape.neg (OShape.ex (OShape.neg σ))) d

theorem forallIter_zero (m : ℕ) (σ : OShape (m + 0)) : forallIter m 0 σ = σ := rfl

theorem forallIter_succ (m k : ℕ) (σ : OShape (m + (k + 1))) :
    forallIter m (k + 1) σ = forallIter m k (OShape.neg (OShape.ex (OShape.neg σ))) := rfl

theorem forallIterData_zero (m : ℕ) (σ : OShape (m + 0)) (d : σ.Data) :
    forallIterData m 0 σ d = d := rfl

theorem forallIterData_succ (m k : ℕ) (σ : OShape (m + (k + 1))) (d : σ.Data) :
    forallIterData m (k + 1) σ d
      = forallIterData m k (OShape.neg (OShape.ex (OShape.neg σ))) d := rfl

/-- The recursion of `Work.WilG0.snocIt` in its second argument. -/
theorem snocIt_succ (n m : ℕ) (x : Fin n → ℝ) (w : Fin (m + 1) → ℝ) :
    Work.WilG0.snocIt n (m + 1) x w
      = Fin.snoc (Work.WilG0.snocIt n m x (Fin.init w)) (w (Fin.last m)) := rfl

/-- **The realisation of `forallIter`.**  Universally quantifying the last `k` coordinates of a
shape gives `{x | ∀ w : Fin k → ℝ, snocIt m k x w ∈ σ.realize d}`. -/
theorem forallIter_realize (m : ℕ) :
    ∀ (k : ℕ) (σ : OShape (m + k)) (d : σ.Data),
      (forallIter m k σ).realize (forallIterData m k σ d) =
        {x : Fin m → ℝ | ∀ w : Fin k → ℝ, Work.WilG0.snocIt m k x w ∈ σ.realize d} := by
  intro k
  induction k with
  | zero =>
      intro σ d
      change (σ.realize d) = {x : Fin m → ℝ | ∀ w : Fin 0 → ℝ, x ∈ σ.realize d}
      ext x
      constructor
      · intro hx w
        exact hx
      · intro hx
        exact hx Fin.elim0
  | succ k ih =>
      intro σ d
      let τ : OShape (m + k) := OShape.neg (OShape.ex (OShape.neg σ))
      have ih' : (forallIter m k τ).realize (forallIterData m k τ d)
          = {x : Fin m → ℝ | ∀ w : Fin k → ℝ, Work.WilG0.snocIt m k x w ∈ τ.realize d} :=
        ih τ d
      have hconn : (forallIter m (k + 1) σ).realize (forallIterData m (k + 1) σ d)
          = (forallIter m k τ).realize (forallIterData m k τ d) := rfl
      rw [hconn, ih']
      simp only [τ, OShape.realize, WilkiesDesign.projLast, Set.mem_compl_iff, Set.mem_ofPred_eq]
      ext x
      constructor
      · intro h w'
        by_contra hc
        exact h (Fin.init w') ⟨w' (Fin.last k), hc⟩
      · intro h w
        rintro ⟨t, ht⟩
        exact ht (by simpa [snocIt_succ, Fin.init_snoc, Fin.snoc_last] using h (Fin.snoc w t))

/-- **`Good` is preserved by `forallIter`.** -/
theorem forallIter_good {S : WilkiesDesign.SOMin} {F : ℕ} (m : ℕ) :
    ∀ (k : ℕ) (σ : OShape (m + k)) (d : σ.Data),
      (forallIter m k σ).Good S F (forallIterData m k σ d) ↔ σ.Good S F d := by
  intro k
  induction k with
  | zero => intro σ d; rfl
  | succ k ih =>
      intro σ d
      let τ : OShape (m + k) := OShape.neg (OShape.ex (OShape.neg σ))
      have ih' : (forallIter m k τ).Good S F (forallIterData m k τ d) ↔ τ.Good S F d := ih τ d
      have hconn : (forallIter m (k + 1) σ).Good S F (forallIterData m (k + 1) σ d)
          = ((forallIter m k τ).Good S F (forallIterData m k τ d)) := rfl
      rw [hconn, ih']
      rfl

/-- **The degree is preserved by `forallIter`.** -/
theorem forallIter_deg (m : ℕ) :
    ∀ (k : ℕ) (σ : OShape (m + k)) (d : σ.Data),
      (forallIter m k σ).deg (forallIterData m k σ d) = σ.deg d := by
  intro k
  induction k with
  | zero => intro σ d; rfl
  | succ k ih =>
      intro σ d
      let τ : OShape (m + k) := OShape.neg (OShape.ex (OShape.neg σ))
      have ih' : (forallIter m k τ).deg (forallIterData m k τ d) = τ.deg d := ih τ d
      have hconn : (forallIter m (k + 1) σ).deg (forallIterData m (k + 1) σ d)
          = (forallIter m k τ).deg (forallIterData m k τ d) := rfl
      rw [hconn, ih']
      rfl

/-! ## 3. Coordinates -/

/-- The dimension `p + (n+1)` of the space of pairs `(l, z)`. -/
abbrev Nc (p n : ℕ) : ℕ := p + (n + 1)

/-- The ambient dimension of `famGraph f`. -/
abbrev Ng (p n : ℕ) : ℕ := Nc p n + 1

/-- The top level of the pointwise-continuity shape. -/
abbrev Kz (p n : ℕ) : ℕ := (Nc p n + 5) + (n + 1)

/-! ### Polynomials -/

/-- The polynomial `ε` in the coordinates of level `Nc+2`. -/
def Peps (p n : ℕ) : MvPolynomial (Fin (Nc p n + 2)) ℝ :=
  MvPolynomial.X ⟨Nc p n + 1, by omega⟩

/-- The polynomial `δ` in the coordinates of level `Nc+4`. -/
def Pdel (p n : ℕ) : MvPolynomial (Fin (Nc p n + 4)) ℝ :=
  MvPolynomial.X ⟨Nc p n + 3, by omega⟩

/-- The polynomial `δ² - Σ_j (y'_j - y_j)²` in the coordinates of level `Kz`. -/
def Pball (p n : ℕ) : MvPolynomial (Fin (Kz p n)) ℝ :=
  MvPolynomial.X ⟨Nc p n + 3, by simp only [Kz, Nc]; omega⟩ ^ 2 -
    ∑ j : Fin (n + 1),
      (MvPolynomial.X ⟨Nc p n + 5 + (j : ℕ), by simp only [Kz, Nc]; omega⟩ -
        MvPolynomial.X ⟨p + (j : ℕ), by simp only [Kz, Nc]; omega⟩) ^ 2

/-- The polynomial `ε² - (v' - v)²` in the coordinates of level `Kz+2`. -/
def PD (p n : ℕ) : MvPolynomial (Fin (Kz p n + 2)) ℝ :=
  MvPolynomial.X ⟨Nc p n + 1, by simp only [Kz, Nc]; omega⟩ ^ 2 -
    (MvPolynomial.X ⟨Kz p n + 1, by simp only [Kz, Nc]; omega⟩ -
      MvPolynomial.X ⟨Nc p n, by simp only [Kz, Nc]; omega⟩) ^ 2

/-! ### The index maps for the two graph atoms -/

/-- The index map picking `(l, y, v)` out of the auxiliary space: the free coordinates
`0 … p-1` (`l`), the free coordinates `p … p+n` (`y`), and the free coordinate `Nc` (`v`).
This is just the inclusion of the free block `Fin (Nc+1)` into the auxiliary space. -/
def iotaV (p n : ℕ) : Fin (Ng p n) → Fin (Kz p n + 2) :=
  fun i => ⟨(i : ℕ), by simp only [Kz, Nc, Ng] at *; omega⟩

/-- The index map picking `(l, y', v')` out of the auxiliary space: the free coordinates
`0 … p-1` (`l`), the witness coordinates `Nc+5+j` (`y'`), and the witness coordinate `Kz+1`
(`v'`). -/
def iotaVp (p n : ℕ) : Fin (Ng p n) → Fin (Kz p n + 2) :=
  Fin.append (m := p) (n := (n + 1) + 1)
    (fun i : Fin p => ⟨(i : ℕ), by simp only [Kz, Nc, Ng] at *; omega⟩)
    (Fin.append (m := n + 1) (n := 1)
      (fun j : Fin (n + 1) =>
        ⟨Nc p n + 5 + (j : ℕ), by simp only [Kz, Nc, Ng] at *; omega⟩)
      (fun _ : Fin 1 => ⟨Kz p n + 1, by simp only [Kz, Nc, Ng] at *; omega⟩))

/-! ### The named coordinates of the auxiliary space (all at level `Kz+2`) -/

/-- The index of the parameter coordinate `l i`. -/
abbrev lPos (p n : ℕ) (i : Fin p) : Fin (Kz p n + 2) :=
  ⟨(i : ℕ), by simp only [Kz, Nc]; omega⟩

/-- The index of the free cube coordinate `u j`. -/
abbrev uPos (p n : ℕ) (j : Fin (n + 1)) : Fin (Kz p n + 2) :=
  ⟨p + (j : ℕ), by simp only [Kz, Nc]; omega⟩

/-- The index of the witness cube coordinate `y' j`. -/
abbrev ypPos (p n : ℕ) (j : Fin (n + 1)) : Fin (Kz p n + 2) :=
  ⟨Nc p n + 5 + (j : ℕ), by simp only [Kz, Nc]; omega⟩

/-- The index of the free value coordinate `v` (= `Nc`). -/
abbrev vPos (p n : ℕ) : Fin (Kz p n + 2) :=
  ⟨Nc p n, by simp only [Kz, Nc]; omega⟩

/-- The index of the witness value coordinate `v'` (= `Kz+1`). -/
abbrev vpPos (p n : ℕ) : Fin (Kz p n + 2) := ⟨Kz p n + 1, by omega⟩

/-! ## 4. The shape -/

/-- The body with `v'` still free: `(l,y',v') ∈ famGraph f` together with `(v'-v)² < ε²`. -/
def zpInner (p n : ℕ) : OShape (Kz p n + 2) :=
  OShape.and (OShape.mem (Kz p n + 2) (Ng p n) (iotaVp p n))
    (OShape.ex (OShape.poly (Kz p n + 3)))

/-- `∃ v'`, the value of the family at `(l,y')`. -/
def zpVexists (p n : ℕ) : OShape (Kz p n + 1) := OShape.ex (zpInner p n)

/-- The ball implication: `(Σ_j (y'_j-y_j)² < δ²) → ∃ v' (…)`. -/
def zpBallImp (p n : ℕ) : OShape (Kz p n) :=
  OShape.neg (OShape.ex (OShape.and (OShape.poly (Kz p n + 1)) (OShape.neg (zpVexists p n))))

/-- `∀ y'`, universally quantified over the cube point. -/
def zpYBlock (p n : ℕ) : OShape (Nc p n + 5) := forallIter (Nc p n + 5) (n + 1) (zpBallImp p n)

/-- `δ > 0 ∧ ∀ y' (…)`. -/
def zpDelta (p n : ℕ) : OShape (Nc p n + 5) :=
  OShape.and (OShape.poly (Nc p n + 5)) (zpYBlock p n)

/-- `∃ δ, δ > 0 ∧ ∀ y' (…)`. -/
def zpDeltaEx (p n : ℕ) : OShape (Nc p n + 3) := OShape.ex (OShape.ex (zpDelta p n))

/-- `ε > 0 ∧ ∃ δ (…)`. -/
def zpEps (p n : ℕ) : OShape (Nc p n + 3) :=
  OShape.and (OShape.poly (Nc p n + 3)) (OShape.neg (zpDeltaEx p n))

/-- `∃ ε, ε > 0 ∧ ¬ ∃ δ (…)`, i.e. `∀ ε > 0, ∃ δ (…)`. -/
def zpEpsEx (p n : ℕ) : OShape (Nc p n + 2) := OShape.ex (zpEps p n)

/-- The continuity body: `∀ ε > 0, ∃ δ > 0, ∀ y' (…)`.  It is `¬∃ε (ε > 0 ∧ ¬ Δ)`, i.e. the
negation is taken *outside* the existential quantifier — `zpEpsEx` already exists in `ε`. -/
def zpCont (p n : ℕ) : OShape (Nc p n + 1) := OShape.neg (OShape.ex (zpEpsEx p n))

/-- **The pointwise fibre continuity shape.**  `ZpShape p n` is the shape in
`ℝ^{p+(n+1)+1}` (coordinates `(l,u,v)`) whose data are the two copies of `famGraph f` and the
four gadget polynomials. -/
def ZpShape (p n : ℕ) : OShape (Nc p n + 1) :=
  OShape.and (OShape.mem (Nc p n + 1) (Ng p n) id) (zpCont p n)

/-! ## 5. The data -/

/-- The data of `zpInner`. -/
def zpInnerData (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (D : ℕ) :
    (zpInner p n).Data :=
  ((famGraph f, D), (posAtom (PD p n) : MvPolynomial (Fin (Kz p n + 3)) ℝ))

/-- The data of `zpVexists`. -/
def zpVexistsData (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (D : ℕ) :
    (zpVexists p n).Data := zpInnerData p n f D

/-- The data of `zpBallImp`. -/
def zpBallImpData (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (D : ℕ) :
    (zpBallImp p n).Data :=
  ((posAtom (Pball p n) : MvPolynomial (Fin (Kz p n + 1)) ℝ), zpVexistsData p n f D)

/-- The data of `zpYBlock`. -/
def zpYBlockData (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (D : ℕ) :
    (zpYBlock p n).Data :=
  forallIterData (Nc p n + 5) (n + 1) (zpBallImp p n) (zpBallImpData p n f D)

/-- The data of `zpDelta`. -/
def zpDeltaData (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (D : ℕ) :
    (zpDelta p n).Data :=
  ((posAtom (Pdel p n) : MvPolynomial (Fin (Nc p n + 5)) ℝ), zpYBlockData p n f D)

/-- The data of `zpDeltaEx`. -/
def zpDeltaExData (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (D : ℕ) :
    (zpDeltaEx p n).Data := zpDeltaData p n f D

/-- The data of `zpEps`. -/
def zpEpsData (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (D : ℕ) :
    (zpEps p n).Data :=
  ((posAtom (Peps p n) : MvPolynomial (Fin (Nc p n + 3)) ℝ), zpDeltaExData p n f D)

/-- The data of `zpEpsEx`. -/
def zpEpsExData (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (D : ℕ) :
    (zpEpsEx p n).Data := zpEpsData p n f D

/-- The data of `zpCont`. -/
def zpContData (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (D : ℕ) :
    (zpCont p n).Data := zpEpsData p n f D

/-- The data of `ZpShape p n`: the graph of `f` (used twice) at declared degree `D`, and the
four gadget atoms. -/
def ZpData (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (D : ℕ) : (ZpShape p n).Data :=
  ((famGraph f, D), zpContData p n f D)

/-- The set realised by `ZpShape p n`: the graph of `f` over the *pointwise* fibre continuity
locus. -/
def ZpSet (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) : Set (Fin (Nc p n + 1) → ℝ) :=
  {z | z ∈ famGraph f ∧
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ y' : Fin (n + 1) → ℝ,
      (∑ j : Fin (n + 1), (y' j - cubePt (Fin.init z) j) ^ 2) < δ ^ 2 →
      (f (parPt (Fin.init z)) y' - z (Fin.last (Nc p n))) ^ 2 < ε ^ 2}

end Work.WilkG4c
