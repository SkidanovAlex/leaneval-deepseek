import Mathlib
import Submission.Work.OROneRel.MagnusGenDefs
import Submission.Work.OROneRel.decor_pow_flatMap

namespace Work.OROneRel

universe u

/-- **The walk telescoping identity.**

`decor c i L` records the traversals of the walk of the word `L` in the
`ℤ`-cover: the letter `(x, true)` read at running level `j` yields the symbol
`((x, j), true)` (the edge from level `j` to level `j + c x`, read forwards),
while the letter `(x, false)` read at running level `j` yields
`((x, j - c x), false)` (that edge, read backwards).

Suppose that for every traversed edge `p` the "edge relation"
`Y (source of p) * X (letter of p) = E p * Y (target of p)` holds, where `Y`
is attached to levels, `X` to letters and `E` to edges.  Then walking along `L`
starts at `Y i`, collects the `X`-traversals of the letters on the left and the
`E`-traversals of the edges on the right, and ends at the level `i + lsig c L`:

`Y i * ∏ (X^{ε_p}) = ∏ (E^{ε_p}) * Y (i + lsig c L)`.

The proof is the chain
`Y i_k * X_k^{ε_k} = E_k^{ε_k} * Y i_{k+1}` for the successive running levels
`i = i_1, i_2, …, i_{n+1} = i + lsig c L` of the walk, multiplied together. -/
theorem walking_telescope {α : Type u} {K : Type*} [Group K] (c : α → ℤ) (X : α → K) (Y : ℤ → K)
    (E : α × ℤ → K) (L : List (α × Bool)) (i : ℤ)
    (hstep : ∀ p ∈ Work.OROneRel.decor c i L,
      Y p.1.2 * X p.1.1 = E p.1 * Y (p.1.2 + c p.1.1)) :
    Y i * ((Work.OROneRel.decor c i L).map
        (fun p => if p.2 then X p.1.1 else (X p.1.1)⁻¹)).prod
      = ((Work.OROneRel.decor c i L).map
          (fun p => if p.2 then E p.1 else (E p.1)⁻¹)).prod * Y (i + Work.OROneRel.lsig c L) := by
  classical
  induction L generalizing i with
  | nil =>
    simp only [decor, List.map_nil, List.prod_nil, lsig, List.map_nil, List.sum_nil,
      add_zero, mul_one, one_mul]
  | cons q L ih =>
    obtain ⟨a, b⟩ := q
    cases b
    · -- the letter `(a, false)`: the traversal is the edge `(a, i - c a)`, read backwards
      have hm : ((a, i - c a), false) ∈ decor c i ((a, false) :: L) := by
        rw [show decor c i ((a, false) :: L)
              = ((a, i - c a), false) :: decor c (i - c a) L from rfl]
        exact List.mem_cons_self ..
      have hstep₀ : Y (i - c a) * X a = E (a, i - c a) * Y i := by
        have h := hstep ((a, i - c a), false) hm
        simpa using h
      have ih' : Y (i - c a) *
            ((decor c (i - c a) L).map
              (fun p => if p.2 then X p.1.1 else (X p.1.1)⁻¹)).prod
          = ((decor c (i - c a) L).map
              (fun p => if p.2 then E p.1 else (E p.1)⁻¹)).prod
            * Y (i - c a + lsig c L) :=
        ih (i - c a) (fun p hp => hstep p (by
          rw [show decor c i ((a, false) :: L)
                = ((a, i - c a), false) :: decor c (i - c a) L from rfl]
          exact List.mem_cons_of_mem _ hp))
      -- the level `i` can be read backwards through the edge
      have hY : Y i * (X a)⁻¹ = (E (a, i - c a))⁻¹ * Y (i - c a) := by
        have h2 : Y i = (E (a, i - c a))⁻¹ * (Y (i - c a) * X a) := by
          rw [hstep₀]; group
        rw [h2]; group
      rw [show decor c i ((a, false) :: L)
            = ((a, i - c a), false) :: decor c (i - c a) L from rfl]
      rw [decor_lsig_cons_false]
      simp only [List.map_cons, List.prod_cons, Bool.false_eq_true, ↓reduceIte]
      rw [show (i : ℤ) + (-c a + lsig c L) = i - c a + lsig c L from by ring]
      calc Y i * ((X a)⁻¹ *
              ((decor c (i - c a) L).map
                (fun p => if p.2 then X p.1.1 else (X p.1.1)⁻¹)).prod)
          = (Y i * (X a)⁻¹) *
              ((decor c (i - c a) L).map
                (fun p => if p.2 then X p.1.1 else (X p.1.1)⁻¹)).prod := by group
        _ = ((E (a, i - c a))⁻¹ * Y (i - c a)) *
              ((decor c (i - c a) L).map
                (fun p => if p.2 then X p.1.1 else (X p.1.1)⁻¹)).prod := by rw [hY]
        _ = (E (a, i - c a))⁻¹ * (Y (i - c a) *
              ((decor c (i - c a) L).map
                (fun p => if p.2 then X p.1.1 else (X p.1.1)⁻¹)).prod) := by group
        _ = (E (a, i - c a))⁻¹ * (((decor c (i - c a) L).map
                (fun p => if p.2 then E p.1 else (E p.1)⁻¹)).prod
              * Y (i - c a + lsig c L)) := by rw [ih']
        _ = ((E (a, i - c a))⁻¹ * ((decor c (i - c a) L).map
                (fun p => if p.2 then E p.1 else (E p.1)⁻¹)).prod)
              * Y (i - c a + lsig c L) := by group
    · -- the letter `(a, true)`: the traversal is the edge `(a, i)`, read forwards
      have hm : ((a, i), true) ∈ decor c i ((a, true) :: L) := by
        rw [show decor c i ((a, true) :: L)
              = ((a, i), true) :: decor c (i + c a) L from rfl]
        exact List.mem_cons_self ..
      have hstep₀ : Y i * X a = E (a, i) * Y (i + c a) := by
        have h := hstep ((a, i), true) hm
        simpa using h
      have ih' : Y (i + c a) *
            ((decor c (i + c a) L).map
              (fun p => if p.2 then X p.1.1 else (X p.1.1)⁻¹)).prod
          = ((decor c (i + c a) L).map
              (fun p => if p.2 then E p.1 else (E p.1)⁻¹)).prod
            * Y (i + c a + lsig c L) :=
        ih (i + c a) (fun p hp => hstep p (by
          rw [show decor c i ((a, true) :: L)
                = ((a, i), true) :: decor c (i + c a) L from rfl]
          exact List.mem_cons_of_mem _ hp))
      rw [show decor c i ((a, true) :: L)
            = ((a, i), true) :: decor c (i + c a) L from rfl]
      rw [decor_lsig_cons_true]
      simp only [List.map_cons, List.prod_cons, if_true]
      rw [show (i : ℤ) + (c a + lsig c L) = i + c a + lsig c L from by ring]
      calc Y i * (X a *
              ((decor c (i + c a) L).map
                (fun p => if p.2 then X p.1.1 else (X p.1.1)⁻¹)).prod)
          = Y i * X a *
              ((decor c (i + c a) L).map
                (fun p => if p.2 then X p.1.1 else (X p.1.1)⁻¹)).prod := by group
        _ = E (a, i) * Y (i + c a) *
              ((decor c (i + c a) L).map
                (fun p => if p.2 then X p.1.1 else (X p.1.1)⁻¹)).prod := by rw [hstep₀]
        _ = E (a, i) * (Y (i + c a) *
              ((decor c (i + c a) L).map
                (fun p => if p.2 then X p.1.1 else (X p.1.1)⁻¹)).prod) := by group
        _ = E (a, i) * (((decor c (i + c a) L).map
                (fun p => if p.2 then E p.1 else (E p.1)⁻¹)).prod
              * Y (i + c a + lsig c L)) := by rw [ih']
        _ = E (a, i) * ((decor c (i + c a) L).map
                (fun p => if p.2 then E p.1 else (E p.1)⁻¹)).prod
              * Y (i + c a + lsig c L) := by group

end Work.OROneRel
