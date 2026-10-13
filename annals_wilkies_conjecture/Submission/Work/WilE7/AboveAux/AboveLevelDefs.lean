/-
  Area E7, `Work.WilE7.AboveAux.aboveLevel_subPf` — vocabulary.

  The target lemma `aboveLevel_subPf` presents the set of levels `t = y (Fin.last p)` lying
  strictly above the `j`-th level of `k` *distinct, increasing* points of the fibre of a
  restricted semi-Pfaffian set `X ⊆ ℝ^{p+q}` over the base `Fin.init y`, with the base also
  constrained by an independent semi-Pfaffian set `XC ⊆ ℝ^{p+M}`:

      Y = {y : Fin (p+1) → ℝ | y ∈ cubeC (p+1) ∧ (∃ w : Fin M → ℝ, Fin.append (Fin.init y) w ∈ XC.set) ∧
             y (Fin.last p) < 1 ∧
             ∃ z : Fin k → (Fin (p+q) → ℝ),
               (∀ l, z l ∈ X.set) ∧ (∀ l, projFirst p q (z l) = Fin.init y) ∧
               (∀ l l', l < l' → (z l) (Fin.natAdd p j) < (z l') (Fin.natAdd p j)) ∧
               (∀ l, (z l) (Fin.natAdd p j) < y (Fin.last p))}

  Since `SubPf` is (by definition) closed under projection of a `SemiPf` set, it suffices to
  build one `SemiPf` set in a bigger space whose projection to the coordinates
  `(Fin.init y, y (Fin.last p))` is `Y`.  This file fixes the layout, the atoms and the
  presentation; the set identity itself is proved in `Submission.Work.WilE7.AboveAux.aboveLevel_subPf`.

  ## The layout

  The ambient space of the presentation is

      ℝ^D,     D = levDim p q M k = (p + 1) + (M + (p + q) * k),

  laid out as `(t, w, z 0, …, z (k-1))` with `y = Fin.append (Fin.init y) t`, i.e.

  * coordinates `0 … p-1`  : the base `x = Fin.init y`            (part of the `XC`-block),
  * coordinate  `p`        : the level `t = y (Fin.last p)`,
  * coordinates `p+1 … p+M`: the witness `w` of the projection of `XC`,
  * then `k` blocks of `p + q` coordinates: the points `z l` of `X`.

  ## The presentation

  * `W := SemiPf.prod XC (fibBlocks X k)` in `ℝ^{blkDim}`, `blkDim p q M k = (p+M) + (p+q)*k`:
    its coordinates are `(x, w, z 0, …, z (k-1))` with `x` the first `p` coordinates
    (`prodSet`, `fibBlocks_set`);
  * `SemiPf.extend (gapInj p q M k) W`: `gapInj` reads `(x, w, z 0, …)` off a point of the
    large space — it inserts the level `t` at coordinate `p` and *drops* the coordinate `p` of
    the source (the source's coordinate `p` is the last coordinate of `x`, and the source's
    coordinates `p … p+M-1` are `w`; see `gapInj_projFirst` / `gapInj_projSnd`);
  * the atoms (`addAtoms`): `eqAtom`s force the base of each `z l` to be `x`, `lvlAtom`s force
    `z l`'s level below `t`, `ordAtom`s force the levels to increase with `l`, and
    `1 - X (tIdx)` forces `t < 1`.
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.Defs
import Submission.Work.WilE7.ProdDefs
import Submission.Work.WilE7.LevelFibre.withAtoms
import Submission.Work.WilE8.Extend

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7.AboveAux
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-! ## The `k`-fold self-product of a semi-Pfaffian set -/

/-- The `m`-fold product of `X` with itself, in `ℝ^{N*m}`.  Its point set is
`{Z | ∀ l : Fin m, fibBlk Z l ∈ X.set}` (`Work.WilE7.AboveAux.fibBlocks_set`). -/
def fibBlocks {N : ℕ} (X : SemiPf N) : (m : ℕ) → SemiPf (N * m)
  | 0 => ⟨0, EAChain.nil 0, [⟨[], []⟩]⟩
  | (m + 1) => SemiPf.prod (fibBlocks X m) X

theorem fibBlocks_zero {N : ℕ} (X : SemiPf N) :
    fibBlocks X 0 = (⟨0, EAChain.nil 0, [⟨[], []⟩]⟩ : SemiPf 0) := rfl

theorem fibBlocks_succ {N : ℕ} (X : SemiPf N) (m : ℕ) :
    fibBlocks X (m + 1) = SemiPf.prod (fibBlocks X m) X := rfl

/-- The index, in `ℝ^{N*m}`, of the `i`-th coordinate of the `l`-th block. -/
def fibBlkIdx (N m : ℕ) (l : Fin m) (i : Fin N) : Fin (N * m) :=
  ⟨l.val * N + i.val, by
    have h1 : l.val * N + i.val < l.val * N + N := Nat.add_lt_add_left i.isLt _
    have h2 : l.val * N + N = (l.val + 1) * N := by ring
    have h3 : (l.val + 1) * N ≤ m * N := Nat.mul_le_mul_right N (Nat.succ_le_of_lt l.isLt)
    have h4 : m * N = N * m := Nat.mul_comm m N
    omega⟩

@[simp] theorem fibBlkIdx_val (N m : ℕ) (l : Fin m) (i : Fin N) :
    (fibBlkIdx N m l i).val = l.val * N + i.val := rfl

/-- The `l`-th block of a point of `ℝ^{N*m}`. -/
def fibBlk {N m : ℕ} (Z : Fin (N * m) → ℝ) (l : Fin m) : Fin N → ℝ :=
  fun i => Z (fibBlkIdx N m l i)

@[simp] theorem fibBlk_apply {N m : ℕ} (Z : Fin (N * m) → ℝ) (l : Fin m) (i : Fin N) :
    fibBlk Z l i = Z (fibBlkIdx N m l i) := rfl

/-- Glue `k` points of `ℝ^N` into a point of `ℝ^{N*k}` (the opposite of `fibBlk`):
`blocksOf z (fibBlkIdx N k l i) = z l i` (`Work.WilE7.AboveAux.blocksOf_fibBlkIdx`). -/
def blocksOf {N : ℕ} : (k : ℕ) → (Fin k → Fin N → ℝ) → Fin (N * k) → ℝ
  | 0, _ => fun i => i.elim0
  | k + 1, z => Fin.append (blocksOf k fun l => z (Fin.castSucc l)) (z (Fin.last k))

/-! ## The dimensions and the coordinate layout -/

/-- The dimension of the `SemiPf.prod` presentation: `(x, w, z 0, …, z (k-1))`. -/
abbrev blkDim (p q M k : ℕ) : ℕ := (p + M) + (p + q) * k

/-- The dimension of the ambient space of the presentation `aboveLevelZ`:
`(t, w, z 0, …, z (k-1))` with the base `x` read off the first `p` coordinates of `t`. -/
abbrev levDim (p q M k : ℕ) : ℕ := (p + 1) + (M + (p + q) * k)

/-- `gapInj p q M k` reads a point `(x, w, z 0, …, z (k-1))` of `ℝ^{blkDim}` off a point
`(y, w, z 0, …)` of `ℝ^{levDim}`: the coordinate `p` of the target (the level `y (Fin.last p)`)
is skipped, so the first `p` coordinates are the base and the rest is shifted up by one. -/
def gapInj (p q M k : ℕ) : Fin (blkDim p q M k) → Fin (levDim p q M k) :=
  fun i =>
    if h : (i : ℕ) < p then
      ⟨i, by
        have hi : (i : ℕ) < (p + M) + (p + q) * k := i.isLt
        show (i : ℕ) < (p + 1) + (M + (p + q) * k)
        omega⟩
    else
      ⟨(i : ℕ) + 1, by
        have hi : (i : ℕ) < (p + M) + (p + q) * k := i.isLt
        show (i : ℕ) + 1 < (p + 1) + (M + (p + q) * k)
        omega⟩

/-- The level coordinate `t = y (Fin.last p)`. -/
def tIdx (p q M k : ℕ) : Fin (levDim p q M k) :=
  ⟨p, by show p < (p + 1) + (M + (p + q) * k); omega⟩

/-- The `a`-th coordinate of the base `x = Fin.init y`. -/
def xIdx (p q M k : ℕ) (a : Fin p) : Fin (levDim p q M k) :=
  ⟨a, by
    have ha : (a : ℕ) < p := a.isLt
    show (a : ℕ) < (p + 1) + (M + (p + q) * k)
    omega⟩

/-- The `s`-th coordinate of the witness `w`. -/
def wIdx (p q M k : ℕ) (s : Fin M) : Fin (levDim p q M k) :=
  ⟨p + 1 + s, by
    have hs : (s : ℕ) < M := s.isLt
    show p + 1 + (s : ℕ) < (p + 1) + (M + (p + q) * k)
    omega⟩

/-- The index, in `ℝ^{levDim}`, of the `i`-th coordinate of the block `z l`. -/
def blkD (p q M k : ℕ) (l : Fin k) (i : Fin (p + q)) : Fin (levDim p q M k) :=
  ⟨p + M + 1 + l.val * (p + q) + i.val, by
    have hle : l.val * (p + q) + i.val < (p + q) * k := by
      calc l.val * (p + q) + i.val < l.val * (p + q) + (p + q) :=
            Nat.add_lt_add_left i.isLt _
        _ = (l.val + 1) * (p + q) := by ring
        _ ≤ k * (p + q) := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt l.isLt)
        _ = (p + q) * k := Nat.mul_comm _ _
    show p + M + 1 + l.val * (p + q) + i.val < (p + 1) + (M + (p + q) * k)
    omega⟩

/-- The projected variable `y = (Fin.init y, y (Fin.last p))` read off the large space. -/
def rdY (p q M k : ℕ) (V : Fin (levDim p q M k) → ℝ) : Fin (p + 1) → ℝ :=
  projFirst (p + 1) (M + (p + q) * k) V

/-- The witness `w` read off the large space. -/
def rdW (p q M k : ℕ) (V : Fin (levDim p q M k) → ℝ) : Fin M → ℝ :=
  projFirst M ((p + q) * k) (projSnd (p + 1) (M + (p + q) * k) V)

/-- The block point `(z 0, …, z (k-1))` read off the large space. -/
def rdBlkPt (p q M k : ℕ) (V : Fin (levDim p q M k) → ℝ) : Fin ((p + q) * k) → ℝ :=
  projSnd M ((p + q) * k) (projSnd (p + 1) (M + (p + q) * k) V)

/-- The `l`-th block `z l` read off the large space. -/
def rdBlk (p q M k : ℕ) (V : Fin (levDim p q M k) → ℝ) (l : Fin k) : Fin (p + q) → ℝ :=
  fun i => V (blkD p q M k l i)

/-! ## The atoms -/

/-- The equation `z l`'s `a`-th base coordinate `= x a`. -/
def eqAtom (p q M k : ℕ) (l : Fin k) (a : Fin p) : MvPolynomial (Fin (levDim p q M k)) ℝ :=
  MvPolynomial.X (blkD p q M k l (Fin.castAdd q a)) - MvPolynomial.X (xIdx p q M k a)

/-- The list of base equations for all `l` and `a`. -/
def eqAtoms (p q M k : ℕ) : List (MvPolynomial (Fin (levDim p q M k)) ℝ) :=
  (List.finRange k).flatMap fun l => (List.finRange p).map fun a => eqAtom p q M k l a

/-- The inequality `z l`'s level `< t`. -/
def lvlAtom (p q M k : ℕ) (j : Fin q) (l : Fin k) :
    MvPolynomial (Fin (levDim p q M k)) ℝ :=
  MvPolynomial.X (tIdx p q M k) - MvPolynomial.X (blkD p q M k l (Fin.natAdd p j))

/-- The list of level inequalities `z l`'s level `< t`. -/
def lvlAtoms (p q M k : ℕ) (j : Fin q) : List (MvPolynomial (Fin (levDim p q M k)) ℝ) :=
  (List.finRange k).map fun l => lvlAtom p q M k j l

/-- The inequality `z l`'s level `< z l'`'s level. -/
def ordAtom (p q M k : ℕ) (j : Fin q) (l l' : Fin k) :
    MvPolynomial (Fin (levDim p q M k)) ℝ :=
  MvPolynomial.X (blkD p q M k l' (Fin.natAdd p j)) -
    MvPolynomial.X (blkD p q M k l (Fin.natAdd p j))

/-- The list of level inequalities `z l`'s level `< z l'`'s level` for `l < l'`. -/
def ordAtoms (p q M k : ℕ) (j : Fin q) : List (MvPolynomial (Fin (levDim p q M k)) ℝ) :=
  (((List.finRange k).product (List.finRange k)).filter
      (fun pr : Fin k × Fin k => pr.1 < pr.2)).map
    fun pr => ordAtom p q M k j pr.1 pr.2

/-- All the positive atoms: `t < 1`, the level inequalities and the order inequalities. -/
def posAtoms (p q M k : ℕ) (j : Fin q) : List (MvPolynomial (Fin (levDim p q M k)) ℝ) :=
  (1 - MvPolynomial.X (tIdx p q M k)) :: (lvlAtoms p q M k j ++ ordAtoms p q M k j)

/-! ## The presentation -/

/-- The `SemiPf.prod` presentation of the coordinates `(x, w, z 0, …, z (k-1))` of a point of
the large space, pulled back along `gapInj`. -/
def Z0 (p q M k : ℕ) (X : SemiPf (p + q)) (XC : SemiPf (p + M)) : SemiPf (levDim p q M k) :=
  Work.WilE8.SemiPf.extend (gapInj p q M k) (SemiPf.prod XC (fibBlocks X k))

/-- The semi-Pfaffian set presenting `Y` in `ℝ^{levDim}`. -/
def aboveLevelZ (p q M k : ℕ) (j : Fin q) (X : SemiPf (p + q)) (XC : SemiPf (p + M)) :
    SemiPf (levDim p q M k) :=
  Work.WilE7.LevelFibre.addAtoms (Z0 p q M k X XC)
    ((eqAtoms p q M k).map fun Q => Work.WilE7.LevelFibre.eaEmbed Q)
    ((posAtoms p q M k j).map fun Q => Work.WilE7.LevelFibre.eaEmbed Q)

end Work.WilE7.AboveAux
