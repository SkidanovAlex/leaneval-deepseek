/-
  Area E7, `Work.WilE7.graphCell_subPf` (item 2 of `E7main_DESIGN.md`, the graph cells of a
  sheet over a `SubPf` base cell, stated with the fibre-cardinality/level-order data only).

  ## Where this is going (the whole plan, so the helper lemmas make sense)

  Target:

  ```
  theorem graphCell_subPf {p m : ℕ} (S : WilkiesDesign.E.Stratum p (m + 1))
      (C : Set (Fin p → ℝ)) (hCpf : SubPf p C)
      (k : ℕ) (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
      (hinj : ∀ x ∈ C, Injective fun j => s j x)
      (hsub : ∀ j x ∈ C, Fin.append x (s j x) ∈ S.X.set)
      (hcov : ∀ z ∈ S.X.set, π_p z ∈ C → ∃ j, s j (π_p z) = π_{m+1} z)
      (hcard : ∀ x ∈ C, (fiber S.X.set x).ncard = k)
      (hlvl : ∀ x ∈ C, StrictMono fun j => (s j x) (Fin.last m))
      (i : Fin k) : SubPf (p + 1) {y | Fin.init y ∈ C ∧ y (Fin.last p) = (s i (Fin.init y)) (Fin.last m)}
  ```

  ### The mathematics

  `hsub`+`hcov` say that for `x ∈ C` the fibre of `X := S.X` over `x` is exactly the `k`-element
  set `{s j x}`; `hlvl` orders it by the *level* `φ z := z (Fin.natAdd p (Fin.last m))`.  So
  `l j x := (s j x) (Fin.last m)` is the strictly increasing enumeration of the `k` levels of the
  fibre over `x`, and the graph cell is

  ```
  G_i = {(x,t) | x ∈ C, t is the i-th smallest level of the fibre of X over x}.
  ```

  "i-th smallest" is *existential* given that the fibre has exactly `k` elements (`hcard`): `t` is
  the `i`-th smallest level iff there are `k` fibre points `z 0, …, z (k-1)`, of strictly
  increasing level, with `t = φ (z i)`.  (`≥ i` levels below `t` and `≥ k-1-i` above force the
  count to be exactly `i`.)  Undoing the existential over the `k` fibre points is a *projection*
  of a semi-Pfaffian set, hence `SubPf`.

  ### The formal route (which is what the helper lemmas supply)

  * `SemiPf.blocks X k` (this file): the `k`-fold product of `X` with itself, in `ℝ^{N*k}`,
    with `blk` the `l`-th block; `blocks_set` (delegated) computes its point set.
  * `withAtoms` (delegated): a semi-Pfaffian set can be cut by *semialgebraic* atoms
    (polynomial equations/inequalities in the plain coordinates).
  * `levelFibre_subPf` (delegated, the main construction): for arbitrary `X : SemiPf (p+q)` and
    `XC : SemiPf (p+M)`,

    ```
    SubPf (p + 1) {y : Fin (p+1) → ℝ |
        (∃ w : Fin M → ℝ, Fin.append (Fin.init y) w ∈ XC.set) ∧
        ∃ z : Fin k → (Fin (p+q) → ℝ),
          (∀ l, z l ∈ X.set) ∧ (∀ l, projFirst p q (z l) = Fin.init y) ∧
          (∀ l l', l < l' → (z l) (Fin.natAdd p j) < (z l') (Fin.natAdd p j)) ∧
          (z i) (Fin.natAdd p j) = y (Fin.last p)}
    ```

  * the assembly (my file): apply the construction with `X := S.X`, `XC` a semi-Pfaffian set
    whose projection is `C`, `j := Fin.last m`; then identify the two sets using
    `hsub`/`hcov`/`hinj` (fibre `= {s l x}`) and `hcard` (the fibre has exactly `k` points),
    `hlvl` (the level enumeration is increasing).

  ## Layout conventions used by the helper lemmas

  For `N` coordinates per block, the block space `ℝ^{N*m}` has its `l`-th block (`l : Fin m`) at
  the coordinates `blkIdx N m l i = l * N + i`; `blk Z l` is that block.

  The construction of `levelFibre_subPf` is meant to take place in `ℝ^D`,
  `D := (p + M) + (p + q) * k`, laid out as

  * `0 … p-1` : the base coordinates `x` (shared with the `XC`-block),
  * `p … p+M-1` : the `XC`-witness coordinates `w`,
  * `p+M … D-1` : `k` blocks of `p + q` coordinates each (`k` points of `X.set`),

  i.e. `projFirst (p+M) ((p+q)*k) Z ∈ XC.set` and
  `∀ l, blk (projSnd (p+M) ((p+q)*k) Z) l ∈ X.set`, cut by the atoms

  * `blk (projSnd …) l (Fin.castAdd q a) = projFirst (p+M) ((p+q)*k) Z (Fin.castAdd M a)`
    for `l : Fin k`, `a : Fin p` (the block bases equal `x`),
  * `blk (projSnd …) l (Fin.natAdd p j) < blk (projSnd …) l' (Fin.natAdd p j)` for `l < l'`,

  and finally projected to the coordinates `(x, φ (z i))`: those are two coordinates of the
  ambient, so reindex the semi-Pfaffian set along the transposition `Equiv.swap p lvIdx`
  (`lvIdx := (p+M) + i*(p+q) + (p + j)`, the position of block `i`'s level coordinate) and then
  take `projFirst (p+1) (D - (p+1))`.
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.prod_semiPf

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7.LevelFibre
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-! ## Blocks -/

/-- The index of the `i`-th coordinate of the `l`-th block in the block space `Fin (N * m)`. -/
def blkIdx (N m : ℕ) (l : Fin m) (i : Fin N) : Fin (N * m) :=
  ⟨l.val * N + i.val, by
    have h1 : l.val * N + i.val < l.val * N + N := by omega
    have h2 : (l.val + 1) * N ≤ m * N := Nat.mul_le_mul_right N (Nat.succ_le_of_lt l.isLt)
    have h3 : (l.val + 1) * N = l.val * N + N := by ring
    have h4 : m * N = N * m := Nat.mul_comm m N
    omega⟩

@[simp] theorem blkIdx_val (N m : ℕ) (l : Fin m) (i : Fin N) :
    (blkIdx N m l i).val = l.val * N + i.val := rfl

/-- The `l`-th block of a point of `ℝ^{N*m}`. -/
def blk {N m : ℕ} (Z : Fin (N * m) → ℝ) (l : Fin m) : Fin N → ℝ := fun i => Z (blkIdx N m l i)

@[simp] theorem blk_apply {N m : ℕ} (Z : Fin (N * m) → ℝ) (l : Fin m) (i : Fin N) :
    blk Z l i = Z (blkIdx N m l i) := rfl

/-- The `m`-fold product of `X` with itself, in `ℝ^{N*m}`: the coordinates are split into `m`
blocks of `N` coordinates, each block a point of `X.set`. -/
noncomputable def SemiPf.blocks {N : ℕ} (X : SemiPf N) : (m : ℕ) → SemiPf (N * m)
  | 0 => ⟨0, EAChain.nil 0, [⟨[], []⟩]⟩
  | (m+1) => SemiPf.prod (SemiPf.blocks X m) X

@[simp] theorem SemiPf.blocks_zero {N : ℕ} (X : SemiPf N) :
    SemiPf.blocks X 0 = ⟨0, EAChain.nil 0, [⟨[], []⟩]⟩ := rfl

theorem SemiPf.blocks_succ {N : ℕ} (X : SemiPf N) (m : ℕ) :
    SemiPf.blocks X (m+1) = SemiPf.prod (SemiPf.blocks X m) X := rfl

end Work.WilE7.LevelFibre
