import Mathlib
import Submission.Work.Peluse.SwapC.cStPerm

namespace Work.Peluse.SwapC

noncomputable section

open Work.Peluse
open Work.Peluse.LadderP.Swap
open CC

/-! ## The average of a function of one coordinate of a function space

The one analytic input of `cStZeroIdent`: the average over the whole function space `α → I` of a
function which only sees the value at one point `a` is the average over `I`.  (A copy of the private
lemma of the same name in `concatAll.lean`, kept here because `cStZeroIdent` is used by
`concatAll` itself and hence cannot import it.) -/

/-- Splitting off a single coordinate of a function space. -/
private def piSingleEquiv {α I : Type} [DecidableEq α] (a : α) :
    (α → I) ≃ I × ({x : α // x ≠ a} → I) where
  toFun f := (f a, fun x => f x.1)
  invFun p := fun x => if h : x = a then p.1 else p.2 ⟨x, h⟩
  left_inv f := by
    funext x
    by_cases h : x = a
    · subst h; simp
    · simp [h]
  right_inv p := by
    refine Prod.ext ?_ ?_
    · simp
    · funext x; simp [x.2]

/-- **The average over a function space of a function of one coordinate is the average over that
coordinate** (`α` finite). -/
private lemma avg_pi_single {α I : Type} [Fintype α] [DecidableEq α] [Fintype I] [Nonempty I]
    (a : α) (F : I → ℝ) : Work.Peluse.LadderP.Swap.avg (fun f : α → I => F (f a))
      = Work.Peluse.LadderP.Swap.avg F := by
  classical
  have h1 : (∑ f : α → I, F (f a))
      = ∑ p : I × ({x : α // x ≠ a} → I), F p.1 := by
    refine Fintype.sum_equiv (piSingleEquiv a) _ _ ?_
    intro f; rfl
  have hcard : Fintype.card (α → I)
      = Fintype.card I * Fintype.card ({x : α // x ≠ a} → I) := by
    rw [Fintype.card_congr (piSingleEquiv a), Fintype.card_prod]
  have h2 : (∑ i : I, ∑ _r : ({x : α // x ≠ a} → I), F i)
      = ((Fintype.card ({x : α // x ≠ a} → I) : ℝ)) * ∑ i : I, F i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Work.Peluse.LadderP.Swap.avg, Work.Peluse.LadderP.Swap.avg, h1, Fintype.sum_prod_type, h2,
    hcard]
  push_cast
  field_simp

/-! ## The state at the canonical initial slot list -/

/-- **The state at the start of the process, for the canonical list of raw slots.**  Reading the
coefficients of a raw slot (`cA q ι (CC.raw j a) = q (ι a) j`, `cB q ι (CC.raw j (czero s)) = 0`)
and the entries of `(List.finRange s).map g` turns the inner box norm at `ι` into
`pbox s (q (ι (czero s))) (fun _ => 0) M (symIcc N) f`, and the outer average over
`ι : (Fin s → Bool) → I` of a function of the single value `ι (czero s)` into the average over `I`.

The index types of the two `pbox`es differ (`Fin ((List.finRange s).map g).length` vs `Fin s`), so
the bridge is `pbox_compEquiv` along `finCongr hlen`, `hlen : ((List.finRange s).map g).length = s`. -/
theorem cSt_finRange_raw (I : Type) [Fintype I] [Nonempty I] (s : ℕ) (q : I → Fin s → ℤ)
    (M N : ℕ) (f : ℤ → ℂ) :
    cSt I q M N f ((List.finRange s).map (fun j : Fin s => CC.raw j (czero s)))
      = Work.Peluse.LadderP.Swap.avg (fun i : I =>
          Work.Peluse.LadderP.Swap.pbox s (q i) (fun _ => 0) M (Work.Peluse.symIcc N) f) := by
  rw [cSt_def]
  have hlen : ((List.finRange s).map (fun j : Fin s => CC.raw j (czero s))).length = s := by
    rw [List.length_map, List.length_finRange]
  -- the entry of the canonical list at the slot `k`
  have hget : ∀ k : Fin s,
      ((List.finRange s).map (fun j : Fin s => CC.raw j (czero s))).get ((finCongr hlen).symm k)
        = CC.raw k (czero s) := by
    intro k
    rw [List.get_eq_getElem, List.getElem_map, List.getElem_finRange]
    simp [finCongr_symm, Fin.val_cast]
  -- the inner box norm at `ι` only sees `ι (czero s)`
  have key : ∀ ι : (Fin s → Bool) → I,
      pbox ((List.finRange s).map (fun j : Fin s => CC.raw j (czero s))).length
          (fun k => cA q ι (((List.finRange s).map (fun j : Fin s => CC.raw j (czero s))).get k))
          (fun k => cB q ι (((List.finRange s).map (fun j : Fin s => CC.raw j (czero s))).get k))
          M (symIcc N) f
        = pbox s (q (ι (czero s))) (fun _ => 0) M (symIcc N) f := by
    intro ι
    rw [pbox_compEquiv (finCongr hlen)
      (fun k => cA q ι (((List.finRange s).map (fun j : Fin s => CC.raw j (czero s))).get k))
      (fun k => cB q ι (((List.finRange s).map (fun j : Fin s => CC.raw j (czero s))).get k))
      M (symIcc N) f]
    have h₁ : (fun k : Fin s => cA q ι
        (((List.finRange s).map (fun j : Fin s => CC.raw j (czero s))).get ((finCongr hlen).symm k)))
        = q (ι (czero s)) := by
      funext k; rw [hget k]; rfl
    have h₂ : (fun k : Fin s => cB q ι
        (((List.finRange s).map (fun j : Fin s => CC.raw j (czero s))).get ((finCongr hlen).symm k)))
        = (fun _ => 0) := by
      funext k; rw [hget k]; rfl
    rw [h₁, h₂]
  simp only [key]
  exact avg_pi_single (czero s)
    (fun i : I => pbox s (q i) (fun _ => 0) M (symIcc N) f)

/-- **The state at the start of the process is the hypothesis of `concatAll`.**  `cSt I q M N f L`
is the average, over all `ι : (Fin s → Bool) → I`, of the box norm of `f` with the slot list `L`;
`genuineSlots (cproc s 0)` is the slot list of the initial subdivision (the single leaf `czero s`),
which by `cgenSlotsEndpoints` is the list of the `s` raw slots at the empty string.

The content is the computation of the coefficients `cA q ι (CC.raw j (czero s)) = q (ι (czero s)) j`,
`cB q ι (CC.raw j (czero s)) = 0`, of `((List.finRange s).map g).get k = g ((List.finRange s).get k)`
(`List.getElem_map`, `List.getElem_finRange`, `List.get_finRange`), and the fact that the average
over the whole function space `(Fin s → Bool) → I` of a function of the single value `ι (czero s)`
is the average over `I`.

Careful with the index types: the left `pbox` has index type
`Fin ((List.finRange s).map (fun j => CC.raw j (czero s))).length`, the right one `Fin s`; these are
*not* definitionally equal (`(List.finRange s).length` does not reduce to `s`), so the bridge is
`pbox_compEquiv` (`Submission/Work/Peluse/SwapC/cStPerm.lean`) applied to
`finCongr (by rw [List.length_map, List.length_finRange])`, or an explicit `Fin.cast`. -/
theorem cStZeroIdent (I : Type) [Fintype I] [Nonempty I] (s : ℕ) (q : I → Fin s → ℤ) (M N : ℕ)
    (f : ℤ → ℂ)
    (h : (genuineSlots (cproc s 0)).Perm
      ((List.finRange s).map (fun j : Fin s => CC.raw j (czero s)))) :
    cSt I q M N f (genuineSlots (cproc s 0))
      = Work.Peluse.LadderP.Swap.avg (fun i : I =>
          Work.Peluse.LadderP.Swap.pbox s (q i) (fun _ => 0) M (Work.Peluse.symIcc N) f) := by
  rw [cStPerm I q M N f h]
  exact cSt_finRange_raw I s q M N f

end

end Work.Peluse.SwapC
