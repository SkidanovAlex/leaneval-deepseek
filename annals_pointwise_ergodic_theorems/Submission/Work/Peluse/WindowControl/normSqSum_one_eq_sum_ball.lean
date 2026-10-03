import Mathlib
import Submission.Work.Peluse.BoxNorm.boxSumPow_eq_boxNormPow

open scoped BigOperators

namespace Work.Peluse.WindowControl

/-- At level `t = 1` the "sum of squares" form `normSqSum` of the box sum collapses to the
elementary sum of squares of the windowed averages `∑_{a ∈ Q₀} g (x + a)`: the two sums over the
tail tuples are sums over a `Fin 0`-indexed product (a subsingleton), and the reduced cube term
`redCube` of dimension `0` is just `g` itself. -/
theorem normSqSum_one_eq_sum_ball {N : ℕ} (Q0 : Finset ℤ) (g : ℤ → ℂ) :
    Work.Peluse.BoxNorm.normSqSum (fun _ : Fin 1 => Q0) g N
      = ∑ x ∈ Work.Peluse.BoxNorm.ball 1 (fun _ : Fin 1 => Q0) N,
          ‖∑ a ∈ Q0, g (x + a)‖ ^ 2 := by
  -- the 0-dimensional reduced cube term is the function itself
  have hred : ∀ (hs hs' : (i : Fin 0) → {x : ℤ // x ∈ (fun _ : Fin 1 => Q0) i.succ})
      (u : ℤ), Work.Peluse.BoxNorm.redCube (fun _ : Fin 1 => Q0) hs hs' g u = g u := by
    intro hs hs' u
    simp [Work.Peluse.BoxNorm.redCube, Work.Peluse.weight, Work.Peluse.cornerShift]
  -- so the inner window sum does not depend on the tail tuples
  have hinner : ∀ (hs hs' : (i : Fin 0) → {x : ℤ // x ∈ (fun _ : Fin 1 => Q0) i.succ}),
      (∑ x ∈ Work.Peluse.BoxNorm.ball 1 (fun _ : Fin 1 => Q0) N,
        ‖∑ a : {y : ℤ // y ∈ (fun _ : Fin 1 => Q0) 0},
            Work.Peluse.BoxNorm.redCube (fun _ : Fin 1 => Q0) hs hs' g (x + (a : ℤ))‖ ^ 2)
        = ∑ x ∈ Work.Peluse.BoxNorm.ball 1 (fun _ : Fin 1 => Q0) N,
            ‖∑ a ∈ Q0, g (x + a)‖ ^ 2 := by
    intro hs hs'
    refine Finset.sum_congr rfl (fun x _ => ?_)
    have h : (∑ a : {y : ℤ // y ∈ (fun _ : Fin 1 => Q0) 0},
          Work.Peluse.BoxNorm.redCube (fun _ : Fin 1 => Q0) hs hs' g (x + (a : ℤ)))
        = ∑ a ∈ Q0, g (x + a) := by
      rw [Finset.univ_eq_attach Q0, ← Finset.sum_attach Q0 (fun a => g (x + a))]
      exact Finset.sum_congr rfl (fun a _ => hred hs hs' (x + (a : ℤ)))
    rw [h]
  rw [Work.Peluse.BoxNorm.normSqSum]
  refine (Finset.sum_congr rfl (fun hs _ =>
    Finset.sum_congr rfl (fun hs' _ => hinner hs hs'))).trans ?_
  -- the two sums over the (subsingleton) tail-tuple types collapse
  rw [Fintype.sum_subsingleton _ (fun i : Fin 0 => i.elim0)]
  rw [Fintype.sum_subsingleton _ (fun i : Fin 0 => i.elim0)]

end Work.Peluse.WindowControl
