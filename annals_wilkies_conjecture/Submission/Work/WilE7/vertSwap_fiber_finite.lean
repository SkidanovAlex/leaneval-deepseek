import Mathlib
import Submission.Work.WilE7.VertSwap

namespace Work.WilE7

/-!
  `Work.WilE7.vertSwap_fiber_finite`.

  `vertSwap n M` exchanges the first and the last fibre coordinate of `ℝ^{n+(M+1)}`, keeping the
  base coordinates `0, …, n-1` fixed.  Consequently it acts on the fibre over a base point `x`
  simply by swapping the first and the last coordinate of the fibre: this is a bijection of
  `Fin (M+1) → ℝ`, hence it preserves finiteness of fibres.

  The proof of the target is therefore:
  * `vertSwap_apply_natAdd` : the index computation, `vertSwap n M (Fin.natAdd n j)` is the
    tail index `Fin.natAdd n (tailSwap M j)`;
  * `append_vertSwap`       : `Fin.append x y ∘ vertSwap n M = Fin.append x (tailSwapFun M y)`;
  * `fiber_reindex_vertSwap`: the fibre of the reindexed piece is the image of the fibre of the
    original piece under `tailSwapFun M`.
-/

/-- The swap of the first and the last fibre coordinate in `Fin (M+1)`: this is the permutation
induced by `vertSwap n M` on the fibre coordinates. -/
def tailSwap (M : ℕ) : Equiv.Perm (Fin (M + 1)) :=
  Equiv.swap 0 ⟨M, Nat.lt_succ_self M⟩

/-- Precomposition with `tailSwap M`, as a self-map of the fibre `Fin (M+1) → ℝ`. -/
def tailSwapFun (M : ℕ) : (Fin (M + 1) → ℝ) → (Fin (M + 1) → ℝ) :=
  fun y j => y (tailSwap M j)

/-- `tailSwapFun M` is an involution. -/
theorem tailSwapFun_invol (M : ℕ) (y : Fin (M + 1) → ℝ) :
    tailSwapFun M (tailSwapFun M y) = y := by
  funext j
  simp only [tailSwapFun, tailSwap, Equiv.swap_apply_self]

/-- The index computation: on the last fibre coordinate, `vertSwap n M` acts as `tailSwap M`. -/
theorem vertSwap_apply_natAdd (n M : ℕ) (j : Fin (M + 1)) :
    Work.WilE7.vertSwap n M (Fin.natAdd n j) = Fin.natAdd n (tailSwap M j) := by
  have hf : Function.Injective (Fin.natAdd n : Fin (M + 1) → Fin (n + (M+1))) :=
    Fin.natAdd_injective (M+1) n
  have hswap : (Equiv.swap (Fin.natAdd n (0 : Fin (M+1)))
        (Fin.natAdd n ⟨M, Nat.lt_succ_self M⟩) : Equiv.Perm (Fin (n + (M+1))))
      = Work.WilE7.vertSwap n M := rfl
  rw [← hswap]
  exact hf.swap_apply 0 ⟨M, Nat.lt_succ_self M⟩ j

/-- The key computation: composing `Fin.append x y` with `vertSwap n M` amounts to swapping the
first and the last coordinate of the fibre part `y`. -/
theorem append_vertSwap (n M : ℕ) (x : Fin n → ℝ) (y : Fin (M + 1) → ℝ) :
    (fun i => Fin.append x y (Work.WilE7.vertSwap n M i))
      = Fin.append x (tailSwapFun M y) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro i0
    simp only [Work.WilE7.vertSwap_apply_castAdd, Fin.append_left]
  · intro j
    rw [vertSwap_apply_natAdd]
    simp only [Fin.append_right, tailSwapFun]

/-- Reindexing a piece along `vertSwap n M` acts on the fibre over `x` by `tailSwapFun M`. -/
theorem fiber_reindex_vertSwap {n M : ℕ} (P : WilkiesDesign.E.SemiPf (n + (M + 1)))
    (x : Fin n → ℝ) :
    WilkiesDesign.E.fiber ((Work.WilE7.SemiPf.reindex (Work.WilE7.vertSwap n M) P).set) x
      = tailSwapFun M '' WilkiesDesign.E.fiber P.set x := by
  ext y
  rw [Set.mem_image]
  have key : y ∈ WilkiesDesign.E.fiber ((Work.WilE7.SemiPf.reindex (Work.WilE7.vertSwap n M) P).set) x
      ↔ tailSwapFun M y ∈ WilkiesDesign.E.fiber P.set x := by
    simp only [WilkiesDesign.E.fiber, Set.mem_ofPred_eq]
    rw [show Fin.append x y ∈ (Work.WilE7.SemiPf.reindex (Work.WilE7.vertSwap n M) P).set
        ↔ (fun i => Fin.append x y (Work.WilE7.vertSwap n M i)) ∈ P.set from
        Work.WilE7.sp_reindex_mem (Work.WilE7.vertSwap n M) P (Fin.append x y)]
    rw [append_vertSwap]
  constructor
  · intro hy
    exact ⟨tailSwapFun M y, key.mp hy, tailSwapFun_invol M y⟩
  · rintro ⟨z, hz, hzy⟩
    rw [key, ← hzy, tailSwapFun_invol M z]
    exact hz

theorem vertSwap_fiber_finite {n M : ℕ} (P : WilkiesDesign.E.SemiPf (n + (M + 1)))
    (hfin : ∀ x : Fin n → ℝ, (WilkiesDesign.E.fiber P.set x).Finite) :
    ∀ x : Fin n → ℝ,
      (WilkiesDesign.E.fiber (Work.WilE7.SemiPf.reindex (Work.WilE7.vertSwap n M) P).set x).Finite := by
  intro x
  rw [fiber_reindex_vertSwap P x]
  exact Set.Finite.image (tailSwapFun M) (hfin x)

end Work.WilE7
