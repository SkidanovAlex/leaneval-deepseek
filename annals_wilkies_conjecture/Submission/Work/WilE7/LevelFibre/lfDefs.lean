/-
  Area E7: the layout and the ambient semi-Pfaffian set used by
  `Work.WilE7.LevelFibre.levelFibre_subPf`.

  The set

  ```
  Y = {y : Fin (p+1) → ℝ |
        (∃ w : Fin M → ℝ, Fin.append (Fin.init y) w ∈ XC.set) ∧
        ∃ z : Fin k → (Fin (p + q) → ℝ), (∀ l, z l ∈ X.set) ∧
          (∀ l, projFirst p q (z l) = Fin.init y) ∧
          (∀ l l', l < l' → (z l) (Fin.natAdd p j) < (z l') (Fin.natAdd p j)) ∧
          (z i) (Fin.natAdd p j) = y (Fin.last p)}
  ```

  is the projection onto the first `p+1` coordinates `(x, t)` of the semi-Pfaffian set built in
  the ambient `ℝ^{lfD p q M k}`, `lfD p q M k = (p+M) + (p+q)*k`, laid out as

  * positions `0 … p-1`   : the base coordinates `x` (shared with `XC`),
  * positions `p … p+M-1` : the `XC`-witness coordinates `w`,
  * positions `p+M …`     : `k` blocks of `p+q` coordinates (the points `z l`).

  The set `lfW2` is the product `SemiPf.prod XC (SemiPf.blocks X k)`, cut by the atoms

  * `z l (castAdd q a) = x a` (`a : Fin p`, `l : Fin k`),
  * `z l (natAdd p j) < z l' (natAdd p j)` (`l < l'`);

  the coordinate `t = y (Fin.last p)` is the level coordinate `z i (natAdd p j)` of the `i`-th
  block, which is brought to position `p` by the transposition `lfE`.

  Main statements (delegated, in separate modules):

  * `lf_mem_W2`  — the point set of `lfW2`;
  * `lfE_xIdx`, `lfE_lvIdx` — the two coordinate facts about `lfE`.
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.LevelFibre.Defs
import Submission.Work.WilE7.LevelFibre.withAtoms

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7.LevelFibre
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-! ## §1. The ambient layout -/

/-- The ambient dimension: the base coordinates `p`, the `XC`-witness coordinates `M` and the `k`
blocks of `p+q` coordinates. -/
def lfD (p q M k : ℕ) : ℕ := (p + M) + (p + q) * k

/-- The number of coordinates that the projection `projFirst (p+1) (lfM …)` removes. -/
def lfM (p q M k : ℕ) : ℕ := lfD p q M k - (p + 1)

/-- The position of the base coordinate `a`. -/
def lfXIdx {p q M k : ℕ} (a : Fin p) : Fin (lfD p q M k) :=
  Fin.castAdd ((p + q) * k) (Fin.castAdd M a)

/-- The position of the `XC`-witness coordinate `t`. -/
def lfWIdx {p q M k : ℕ} (t : Fin M) : Fin (lfD p q M k) :=
  Fin.castAdd ((p + q) * k) (Fin.natAdd p t)

/-- The position of the coordinate `c` of the `l`-th block. -/
def lfBIdx {p q M k : ℕ} (l : Fin k) (c : Fin (p + q)) : Fin (lfD p q M k) :=
  Fin.natAdd (p + M) (blkIdx (p + q) k l c)

/-- The position of the *level* coordinate `j` of the `i`-th block. -/
def lfLvIdx {p q M k : ℕ} (j : Fin q) (i : Fin k) : Fin (lfD p q M k) :=
  lfBIdx i (Fin.natAdd p j)

@[simp] theorem lfXIdx_val {p q M k : ℕ} (a : Fin p) :
    (lfXIdx (q := q) (M := M) (k := k) a).val = a.val := rfl

@[simp] theorem lfWIdx_val {p q M k : ℕ} (t : Fin M) :
    (lfWIdx (p := p) (q := q) (k := k) t).val = p + t.val := rfl

@[simp] theorem lfBIdx_val {p q M k : ℕ} (l : Fin k) (c : Fin (p + q)) :
    (lfBIdx (p := p) (q := q) (M := M) l c).val = p + M + (l.val * (p + q) + c.val) := by
  show p + M + (blkIdx (p + q) k l c).val = p + M + (l.val * (p + q) + c.val)
  rw [blkIdx_val]

@[simp] theorem lfLvIdx_val {p q M k : ℕ} (j : Fin q) (i : Fin k) :
    (lfLvIdx (p := p) (M := M) j i).val = p + M + (i.val * (p + q) + (p + j.val)) := by
  rw [lfLvIdx, lfBIdx_val]
  simp

theorem lt_lfD (p q M k : ℕ) (h : 1 ≤ (p + q) * k) : p < lfD p q M k := by
  show p < (p + M) + (p + q) * k
  omega

/-- `lfD` is `(p+1) + lfM`, as soon as `(p+q)*k ≥ 1`. -/
theorem lfD_eq_add (p q M k : ℕ) (h : 1 ≤ (p + q) * k) :
    lfD p q M k = (p + 1) + lfM p q M k := by
  have hle : p + 1 ≤ lfD p q M k := by
    show p + 1 ≤ (p + M) + (p + q) * k
    omega
  simp only [lfM]
  show (p + M) + (p + q) * k = (p + 1) + ((p + M) + (p + q) * k - (p + 1))
  omega

/-! ## §2. The semi-Pfaffian set -/

/-- The product `XC × X^k`, in the layout `(x, w, blocks)`. -/
noncomputable def lfW1 {p q M k : ℕ} (X : SemiPf (p + q)) (XC : SemiPf (p + M)) :
    SemiPf (lfD p q M k) :=
  SemiPf.prod XC (SemiPf.blocks X k)

/-- The equation atoms `z_l (castAdd q a) = x_a` (polynomials in the plain coordinates). -/
def lfEqs {p q M k : ℕ} : List (MvPolynomial (Fin (lfD p q M k)) ℝ) :=
  ((List.finRange k).product (List.finRange p)).map fun la =>
    MvPolynomial.X (lfBIdx (p := p) (q := q) (M := M) la.1 (Fin.castAdd q la.2)) -
      MvPolynomial.X (lfXIdx (q := q) (M := M) (k := k) la.2)

/-- The inequality atoms `z_l (level) < z_l' (level)`, one for each pair `l < l'`. -/
def lfPoss {p q M k : ℕ} (j : Fin q) : List (MvPolynomial (Fin (lfD p q M k)) ℝ) :=
  (((List.finRange k).product (List.finRange k)).filterMap fun ll =>
    if ll.1 < ll.2 then
      some (MvPolynomial.X (lfLvIdx (p := p) (M := M) j ll.2) -
        MvPolynomial.X (lfLvIdx (p := p) (M := M) j ll.1)) else none)

/-- The semi-Pfaffian set of the construction: the product cut by the atoms. -/
noncomputable def lfW2 {p q M k : ℕ} (j : Fin q) (X : SemiPf (p + q)) (XC : SemiPf (p + M)) :
    SemiPf (lfD p q M k) :=
  addAtoms (lfW1 X XC)
    ((lfEqs (p := p) (q := q) (M := M) (k := k)).map
      (@eaEmbed (lfD p q M k) (lfW1 X XC).r))
    ((lfPoss (p := p) (q := q) (M := M) (k := k) j).map
      (@eaEmbed (lfD p q M k) (lfW1 X XC).r))

/-- The coordinate transposition `p ↔ (level coordinate of block i)`. -/
def lfSwap {p q M k : ℕ} (h : 1 ≤ (p + q) * k) (j : Fin q) (i : Fin k) :
    Equiv.Perm (Fin (lfD p q M k)) :=
  Equiv.swap ⟨p, lt_lfD p q M k h⟩ (lfLvIdx j i)

/-- The coordinate equivalence bringing the level coordinate of block `i` to position `p`. -/
def lfE {p q M k : ℕ} (h : 1 ≤ (p + q) * k) (j : Fin q) (i : Fin k)
    (hdim : lfD p q M k = (p + 1) + lfM p q M k) :
    Fin (lfD p q M k) ≃ Fin ((p + 1) + lfM p q M k) :=
  (lfSwap h j i).trans (finEquiv hdim)

/-- `lfE` with the dimension proof supplied by `lfD_eq_add`. -/
noncomputable def lfEv {p q M k : ℕ} (h : 1 ≤ (p + q) * k) (j : Fin q) (i : Fin k) :
    Fin (lfD p q M k) ≃ Fin ((p + 1) + lfM p q M k) :=
  lfE h j i (lfD_eq_add p q M k h)

/-- The final semi-Pfaffian set in `ℝ^{(p+1) + lfM}`. -/
noncomputable def lfFinal {p q M k : ℕ} (h : 1 ≤ (p + q) * k) (j : Fin q) (i : Fin k)
    (X : SemiPf (p + q)) (XC : SemiPf (p + M)) : SemiPf ((p + 1) + lfM p q M k) :=
  SemiPf.reindex (lfEv h j i) (lfW2 j X XC)

/-- The set presented by the construction: the target set of `levelFibre_subPf`. -/
def lfY {p q M k : ℕ} (j : Fin q) (i : Fin k) (X : SemiPf (p + q)) (XC : SemiPf (p + M)) :
    Set (Fin (p + 1) → ℝ) :=
  {y : Fin (p + 1) → ℝ |
    (∃ w : Fin M → ℝ, Fin.append (Fin.init y) w ∈ XC.set) ∧
    ∃ z : Fin k → (Fin (p + q) → ℝ),
      (∀ l : Fin k, z l ∈ X.set) ∧
      (∀ l : Fin k, projFirst p q (z l) = Fin.init y) ∧
      (∀ l l' : Fin k, l < l' → (z l) (Fin.natAdd p j) < (z l') (Fin.natAdd p j)) ∧
      (z i) (Fin.natAdd p j) = y (Fin.last p)}

/-! ## §3. Flattening the `k` blocks -/

/-- The `k` blocks `z l : Fin (p+q) → ℝ` flattened into a single function on `Fin ((p+q)*k)`,
`l`-th block first. -/
def lfFlat {p q k : ℕ} (hN : 0 < p + q) (z : Fin k → (Fin (p + q) → ℝ)) :
    Fin ((p + q) * k) → ℝ :=
  fun b => z ⟨b.val / (p + q), (Nat.div_lt_iff_lt_mul hN).mpr
      (Nat.lt_of_lt_of_eq b.isLt (Nat.mul_comm (p + q) k))⟩
    ⟨b.val % (p + q), Nat.mod_lt _ hN⟩

/-- Flattening undoes `blkIdx`. -/
theorem lfFlat_blkIdx {p q k : ℕ} (hN : 0 < p + q) (z : Fin k → (Fin (p + q) → ℝ))
    (l : Fin k) (c : Fin (p + q)) : lfFlat hN z (blkIdx (p + q) k l c) = z l c := by
  have hne : 0 < p + q := hN
  have h1 : (blkIdx (p + q) k l c).val / (p + q) = l.val := by
    rw [blkIdx_val, Nat.mul_comm l.val (p + q), Nat.mul_add_div hne,
      Nat.div_eq_of_lt c.isLt, Nat.add_zero]
  have h2 : (blkIdx (p + q) k l c).val % (p + q) = c.val := by
    rw [blkIdx_val, Nat.mul_comm l.val (p + q), Nat.mul_add_mod, Nat.mod_eq_of_lt c.isLt]
  unfold lfFlat
  apply congrArg₂ z
  · exact Fin.ext h1
  · exact Fin.ext h2

end Work.WilE7.LevelFibre
