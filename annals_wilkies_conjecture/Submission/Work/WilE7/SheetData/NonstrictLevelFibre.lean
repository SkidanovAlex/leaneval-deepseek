/-
  A **non-strict** variant of `Work.WilE7.LevelFibre.levelFibre_subPf`.

  `LevelFibre.lfW2` cuts the product `XC × X^k` by the *strict* level ordering
  `level(z_l) < level(z_l')` (`l < l'`).  The graph-cell lemma for a `Monotone` level map needs
  instead the *non-strict* ordering: the fibre points may share their level.

  Here we build the ambient set in `ℝ^{lfD p (q+1) M k}` (so that the sheet blocks have one extra
  coordinate, a slack `ε_l ∈ [-1,1]`), and cut by

  * the base atoms       `z_l (castAdd (q+1) a) = x_a`              (`lf3Eqs`),
  * the slack atoms      `level(z_{l+1}) - level(z_l) - 1 - ε_l = 0` (`lf3SlackEqs`),
  * the distinctness atom `∏_{l<l'} Σ_c (z_l c - z_{l'} c)² > 0`     (`lf3DistAtom`).

  The slack atom encodes `level(z_l) ≤ level(z_{l+1})` exactly: it is solvable in `ε_l ∈ [-1,1]`
  iff the difference lies in `[0,2]`, and each level lies in `[-1,1]` (it is a coordinate of a
  point of `X.set ⊆ cubeC`).

  The point set of the construction is characterised in `lf3_mem_W3`; the final theorem
  `nonstrictLevel_subPf` says that the set

  ```
  {y | (∃ w, Fin.append (Fin.init y) w ∈ XC.set) ∧
       ∃ z : Fin k → ℝ^{p+q}, (∀ l, z l ∈ X.set) ∧ (∀ l, projFirst p q (z l) = Fin.init y) ∧
         (∀ l < l', level (z l) ≤ level (z l')) ∧ (∀ l ≠ l', z l ≠ z l') ∧
         level (z i) = y (Fin.last p)}
  ```

  is `SubPf (p+1)`.

  All the index arithmetic and the coordinate transposition `lfE` are those of
  `Work.WilE7.LevelFibre.lfDefs`, used with `q := q+1`.
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.LevelFibre.lfDefs
import Submission.Work.WilE7.LevelFibre.lf_mem_W2
import Submission.Work.WilE7.LevelFibre.withAtoms
import Submission.Work.WilE7.LevelFibre.blocks_set
import Submission.Work.WilE7.prodSet

set_option autoImplicit false
noncomputable section
open Classical
open scoped BigOperators

namespace Work.WilE7.SheetData

open WilkiesConjecture WilkiesDesign WilkiesDesign.E
open Work.WilE7.LevelFibre

/-! ## §1. The block set `X × [-1,1]` -/

/-- The full cube `[-1,1]^n`, as a restricted semi-Pfaffian set. -/
def cubeSemiPf (n : ℕ) : SemiPf n := ⟨0, EAChain.nil n, [⟨[], []⟩]⟩

@[simp] theorem cubeSemiPf_set (n : ℕ) : (cubeSemiPf n).set = cubeC n := by
  ext x
  simp only [SemiPf.set, Set.mem_setOf_eq, cubeSemiPf]
  constructor
  · rintro ⟨hx, -⟩; exact hx
  · intro hx
    refine ⟨hx, ⟨[], []⟩, List.mem_singleton.mpr rfl, ?_⟩
    simp [Basic.holds]

/-- The block set `X × [-1,1]` in `ℝ^{p+(q+1)}`: a point of `X.set` together with a slack
coordinate in `[-1,1]`. -/
def lfBlk (p q : ℕ) (X : SemiPf (p + q)) : SemiPf (p + (q + 1)) :=
  SemiPf.prod (k := p + q) (k' := 1) X (cubeSemiPf 1)

/-- The point set of `lfBlk`. -/
theorem lfBlk_set {p q : ℕ} (X : SemiPf (p + q)) :
    (lfBlk p q X).set = {w : Fin (p + (q + 1)) → ℝ |
      projFirst (p + q) 1 w ∈ X.set ∧ projSnd (p + q) 1 w ∈ cubeC 1} := by
  rw [lfBlk, Work.WilE7.prodSet, cubeSemiPf_set]
  rfl

/-! ## §2. The layout of `ℝ^{lfD p (q+1) M k}` -/

/-- The block coordinate of `c : Fin (p+q)` (`X`-point part of a block of size `p+(q+1)`). -/
def lfXc {p q : ℕ} (c : Fin (p + q)) : Fin (p + (q + 1)) := Fin.castAdd 1 c

/-- The slack coordinate: the last coordinate of a block of size `p+(q+1)`. -/
def lfSlkc {p q : ℕ} : Fin (p + (q + 1)) := Fin.natAdd p (Fin.last q)

/-- The level coordinate `j` of a block of size `p+(q+1)`. -/
def lfLvc {p q : ℕ} (j : Fin q) : Fin (p + (q + 1)) := Fin.natAdd p (Fin.castSucc j)

/-- The base coordinate `a` in the ambient space. -/
def lf3XIdx {p q M k : ℕ} (a : Fin p) : Fin (lfD p (q + 1) M k) := lfXIdx (q := q + 1) a

/-- The `XC`-witness coordinate `t` in the ambient space. -/
def lf3WIdx {p q M k : ℕ} (t : Fin M) : Fin (lfD p (q + 1) M k) :=
  lfWIdx (q := q + 1) t

/-- The coordinate `c` of the `l`-th block. -/
def lf3BIdx {p q M k : ℕ} (l : Fin k) (c : Fin (p + (q + 1))) :
    Fin (lfD p (q + 1) M k) := lfBIdx (q := q + 1) l c

/-- The level coordinate `j` of the `l`-th block. -/
def lf3LvIdx {p q M k : ℕ} (j : Fin q) (l : Fin k) : Fin (lfD p (q + 1) M k) :=
  lfBIdx (q := q + 1) l (lfLvc j)

/-- The slack coordinate of the `l`-th block. -/
def lf3SlkIdx {p q M k : ℕ} (l : Fin k) : Fin (lfD p (q + 1) M k) :=
  lfBIdx (q := q + 1) l (lfSlkc (p := p) (q := q))

/-- The coordinate `c : Fin (p+q)` of the `X`-point part of the `l`-th block. -/
def lf3XpIdx {p q M k : ℕ} (l : Fin k) (c : Fin (p + q)) : Fin (lfD p (q + 1) M k) :=
  lfBIdx (q := q + 1) l (lfXc c)

/-! ## §3. The atoms -/

/-- The base atoms `z_l (castAdd (q+1) a) = x_a`. -/
def lf3Eqs {p q M k : ℕ} : List (MvPolynomial (Fin (lfD p (q + 1) M k)) ℝ) :=
  ((List.finRange k).product (List.finRange p)).map fun la =>
    MvPolynomial.X (lf3BIdx (p := p) (q := q) (M := M) la.1 (Fin.castAdd (q + 1) la.2)) -
      MvPolynomial.X (lf3XIdx (q := q) (M := M) (k := k) la.2)

/-- The slack atoms `level(z_{l+1}) - level(z_l) - 1 - ε_l = 0`. -/
def lf3SlackEqs {p q M k : ℕ} (j : Fin q) :
    List (MvPolynomial (Fin (lfD p (q + 1) M k)) ℝ) :=
  (List.finRange (k - 1)).map fun l =>
    MvPolynomial.X (lf3LvIdx (p := p) (q := q) (M := M) j ⟨l.val + 1, by omega⟩) -
      MvPolynomial.X (lf3LvIdx (p := p) (q := q) (M := M) j ⟨l.val, by omega⟩) -
      MvPolynomial.C 1 - MvPolynomial.X (lf3SlkIdx (p := p) (q := q) (M := M) ⟨l.val, by omega⟩)

/-- The pairwise-distinctness atom `∏_{l<l'} Σ_c (z_l c - z_{l'} c)² > 0`. -/
def lf3DistAtom {p q M k : ℕ} : MvPolynomial (Fin (lfD p (q + 1) M k)) ℝ :=
  ((Finset.univ : Finset (Fin k × Fin k)).filter (fun ll => ll.1 < ll.2)).prod fun ll =>
    ∑ c : Fin (p + q),
      (MvPolynomial.X (lf3XpIdx (p := p) (q := q) (M := M) ll.1 c) -
        MvPolynomial.X (lf3XpIdx (p := p) (q := q) (M := M) ll.2 c)) ^ 2

/-- The ambient semi-Pfaffian set of the non-strict level-fibre construction. -/
def lfW3 {p q M k : ℕ} (j : Fin q) (X : SemiPf (p + q)) (XC : SemiPf (p + M)) :
    SemiPf (lfD p (q + 1) M k) :=
  addAtoms (lfW1 (q := q + 1) (lfBlk p q X) XC)
    (((lf3Eqs (p := p) (q := q) (M := M) (k := k)) ++
        (lf3SlackEqs (p := p) (q := q) (M := M) (k := k) j)).map
      (@eaEmbed (lfD p (q + 1) M k) _))
    [(@eaEmbed (lfD p (q + 1) M k) _)
      (lf3DistAtom (p := p) (q := q) (M := M) (k := k))]

/-- The reindexed final semi-Pfaffian set in `ℝ^{(p+1) + lfM p (q+1) M k}`. -/
noncomputable def lf3Final {p q M k : ℕ} (hpq : 1 ≤ (p + (q + 1)) * k) (j : Fin q) (i : Fin k)
    (X : SemiPf (p + q)) (XC : SemiPf (p + M)) :
    SemiPf ((p + 1) + lfM p (q + 1) M k) :=
  SemiPf.reindex (lfEv hpq (Fin.castSucc j) i) (lfW3 j X XC)

/-- The set presented by the non-strict construction. -/
def lfY3 {p q M k : ℕ} (j : Fin q) (i : Fin k) (X : SemiPf (p + q)) (XC : SemiPf (p + M)) :
    Set (Fin (p + 1) → ℝ) :=
  {y : Fin (p + 1) → ℝ |
    (∃ w : Fin M → ℝ, Fin.append (Fin.init y) w ∈ XC.set) ∧
    ∃ z : Fin k → (Fin (p + q) → ℝ),
      (∀ l : Fin k, z l ∈ X.set) ∧
      (∀ l : Fin k, projFirst p q (z l) = Fin.init y) ∧
      (∀ l l' : Fin k, l < l' → (z l) (Fin.natAdd p j) ≤ (z l') (Fin.natAdd p j)) ∧
      (∀ l l' : Fin k, l ≠ l' → z l ≠ z l') ∧
      (z i) (Fin.natAdd p j) = y (Fin.last p)}

end Work.WilE7.SheetData
