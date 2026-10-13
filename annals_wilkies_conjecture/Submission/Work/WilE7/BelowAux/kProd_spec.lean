import Mathlib
import Submission.Work.WilE7.BelowAux.kProd
import Submission.Work.WilE7.prodSet
import Submission.Work.WilE8.Basic

namespace Work.WilE7.BelowAux

open WilkiesDesign WilkiesDesign.E

/-! ## `projFirst` / `projSnd` of an appended pair

`Fin.append x y` is the point of `ℝ^{p+q}` whose first `p` coordinates are `x` and whose last
`q` coordinates are `y`; these two lemmas identify its projections. -/

theorem projFirst_append {p q : ℕ} (x : Fin p → ℝ) (y : Fin q → ℝ) :
    WilkiesDesign.E.projFirst p q (Fin.append x y) = x := by
  funext i
  simp [WilkiesDesign.E.projFirst, Fin.append_left]

theorem projSnd_append {p q : ℕ} (x : Fin p → ℝ) (y : Fin q → ℝ) :
    WilkiesDesign.E.projSnd p q (Fin.append x y) = y := by
  funext i
  simp [WilkiesDesign.E.projSnd, Fin.append_right]

/-! ## The point set of the `k`-fold product

This is the first (point-set) half of `kProd_spec` at level `k`: the coordinates of `ℝ^{n*k}` split
into `k` blocks, and a point lies in `iterProd X k` exactly when every block lies in `X.set`.

The induction is the recursive construction `iterProd X (k+1) = prod (iterProd X k) X`: the point
set of `SemiPf.prod` (`Work.WilE7.prodSet`) is the product of the point sets, the new (last) block
is read off by `blk_last` and the old blocks by `blk_castSucc`. -/

theorem iterProd_set {n : ℕ} (X : WilkiesDesign.E.SemiPf n) (k : ℕ) :
    (Work.WilE7.iterProd X k).set =
      {z : Fin (n * k) → ℝ | ∀ i : Fin k, Work.WilE7.blk i z ∈ X.set} := by
  induction k with
  | zero =>
    show (Work.WilE8.cubeSemiPf 0).set =
      {z : Fin (n * 0) → ℝ | ∀ i : Fin 0, Work.WilE7.blk i z ∈ X.set}
    rw [Work.WilE8.cubeSemiPf_set]
    ext z
    constructor
    · intro _ i
      exact i.elim0
    · intro _ i
      exact i.elim0
  | succ k ih =>
    show (Work.WilE7.SemiPf.prod (Work.WilE7.iterProd X k) X).set =
      {z : Fin (n * (k + 1)) → ℝ | ∀ i : Fin (k + 1), Work.WilE7.blk i z ∈ X.set}
    rw [Work.WilE7.prodSet]
    apply Set.ext
    intro z
    show (WilkiesDesign.E.projFirst (n * k) n z ∈ (Work.WilE7.iterProd X k).set ∧
        WilkiesDesign.E.projSnd (n * k) n z ∈ X.set) ↔
      ∀ i : Fin (k + 1), Work.WilE7.blk i z ∈ X.set
    rw [Fin.forall_iff_castSucc]
    constructor
    · rintro ⟨h1, h2⟩
      have h1'' : WilkiesDesign.E.projFirst (n * k) n z ∈
          {w : Fin (n * k) → ℝ | ∀ i : Fin k, Work.WilE7.blk i w ∈ X.set} := by
        rw [← ih]
        exact h1
      refine ⟨?_, fun i => ?_⟩
      · rw [Work.WilE7.blk_last]
        exact h2
      · rw [Work.WilE7.blk_castSucc]
        exact h1'' i
    · rintro ⟨h2, h1⟩
      refine ⟨?_, ?_⟩
      · rw [ih]
        intro i
        rw [← Work.WilE7.blk_castSucc]
        exact h1 i
      · rw [← Work.WilE7.blk_last]
        exact h2

/-! ## Surjectivity of the block map

The second half of `kProd_spec` at level `k`: every `k`-tuple of points of `X.set` is the tuple of
blocks of some point of `(iterProd X k).set`.  Induction again: given the blocks `Z (castSucc i)` of
the first `k` coordinates and the last block `Z (last k)`, append the two witnesses with
`Fin.append` (`projFirst_append` / `projSnd_append`). -/

theorem iterProd_surj {n : ℕ} (X : WilkiesDesign.E.SemiPf n) (k : ℕ) :
    ∀ Z : Fin k → Fin n → ℝ, (∀ i, Z i ∈ X.set) →
      ∃ z ∈ (Work.WilE7.iterProd X k).set, ∀ i, Work.WilE7.blk i z = Z i := by
  induction k with
  | zero =>
    intro Z hZ
    refine ⟨0, ?_, fun i => i.elim0⟩
    show (0 : Fin (n * 0) → ℝ) ∈ (Work.WilE8.cubeSemiPf 0).set
    rw [Work.WilE8.cubeSemiPf_set]
    intro i
    exact i.elim0
  | succ k ih =>
    intro Z hZ
    obtain ⟨z₁, hz₁, hblk₁⟩ := ih (fun i => Z (Fin.castSucc i)) (fun i => hZ _)
    refine ⟨Fin.append z₁ (Z (Fin.last k)), ?_, ?_⟩
    · show Fin.append z₁ (Z (Fin.last k)) ∈
        (Work.WilE7.SemiPf.prod (Work.WilE7.iterProd X k) X).set
      rw [Work.WilE7.prodSet]
      exact ⟨by rw [projFirst_append]; exact hz₁, by rw [projSnd_append]; exact hZ _⟩
    · intro i
      refine Fin.lastCases (motive := fun i => Work.WilE7.blk i
        (Fin.append z₁ (Z (Fin.last k))) = Z i) ?_ ?_ i
      · rw [Work.WilE7.blk_last, projSnd_append]
      · intro j
        rw [Work.WilE7.blk_castSucc, projFirst_append]
        exact hblk₁ j

theorem kProd_spec {n : ℕ} (X : WilkiesDesign.E.SemiPf n) (k : ℕ) :
    (Work.WilE7.iterProd X k).set =
      {z : Fin (n * k) → ℝ | ∀ i : Fin k, Work.WilE7.blk i z ∈ X.set} ∧
    (∀ Z : Fin k → Fin n → ℝ, (∀ i, Z i ∈ X.set) →
      ∃ z ∈ (Work.WilE7.iterProd X k).set, ∀ i, Work.WilE7.blk i z = Z i) :=
  ⟨iterProd_set X k, iterProd_surj X k⟩

end Work.WilE7.BelowAux
