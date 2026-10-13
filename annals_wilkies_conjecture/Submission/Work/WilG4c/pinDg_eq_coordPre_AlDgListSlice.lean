import Mathlib
import Submission.Work.WilG4c.SlicePinnedDefs
import Submission.Work.WilG4c.iterDir_eq_iteratedFDeriv
import Submission.Work.WilG4c.contDiffAt_init_iff
import Submission.Work.WilG4c.iterDir_init_transport

set_option autoImplicit false
noncomputable section

open Classical
open Work.WilkG4c

namespace Work.WilG4c

/-!
  ## The index bookkeeping

  The pullback along `delDummy` of the padded graph is compared pointwise with `pinDg`.  A point
  `z` of the pinned layout `ℝ^{p + (n+1) + 1}` is sent to the padded point `z ∘ delDummy`, whose
  coordinates are `(l, x, y, dummy, s)` with `l = pinL p n (Fin.init z)`,
  `x = pinX p n (Fin.init z)`, `y = pinY p n (Fin.init z)` and
  `s = z (Fin.last (p + (n+1)))`.  The lemmas below record that the padded family at that point is
  the slice `y' ↦ slice (f l) x (Fin.init y')`, that the padded cube point reduces to
  `pinY p n (Fin.init z)` with `Fin.init`, and that the padded value coordinate is the pinned one.
  All three are computations with `delDummy`, whose branches are decided by `omega` on the index
  values.
-/

/-- `delDummy` sends an index of the padded layout to the index of the pinned layout with the
same value (for the indices `0, …, p + n`). -/
private theorem delDummy_apply_eq {p n : ℕ} (z : Fin (p + (n + 1) + 1) → ℝ)
    (i : Fin ((p + 1) + (n + 1) + 1)) (j : Fin (p + (n + 1) + 1)) (h : i.val = j.val) :
    z (delDummy p n i) = z j := by
  rw [delDummy]
  split_ifs with hlt
  · congr 1
    exact Fin.ext (by simp [h])
  · congr 1
    exact Fin.ext (by simp [show j.val = p + n + 1 by omega])

/-- `delDummy` collapses the dummy coordinate and the value coordinate both onto the value
coordinate. -/
private theorem delDummy_last (p n : ℕ) :
    delDummy p n (Fin.last ((p + 1) + (n + 1))) = Fin.last (p + (n + 1)) := by
  rw [delDummy, dif_neg (by rw [Fin.val_last]; omega)]
  rfl

/-- The parameter block of the padded point is the pair `(l, x)` of the pinned point, so the
padded family there reads `Fin.init` of the cube point through the slice `slice (f l) x`. -/
private theorem padFam_parPt_delDummy_apply (p n : ℕ)
    (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (z : Fin (p + (n + 1) + 1) → ℝ)
    (w : Fin (n + 1) → ℝ) :
    padFam p n f (parPt (Fin.init (z ∘ delDummy p n))) w =
      slice (f (pinL p n (Fin.init z))) (pinX p n (Fin.init z)) (Fin.init w) := by
  have ha : (fun i : Fin p => parPt (Fin.init (z ∘ delDummy p n)) (Fin.castSucc i)) =
      pinL p n (Fin.init z) := by
    funext i
    simp only [parPt, pinL, Fin.init, Function.comp_apply]
    exact delDummy_apply_eq z ((Fin.castAdd (n + 1) (Fin.castSucc i)).castSucc)
      ((Fin.castAdd (n + 1) i).castSucc)
      (by simp only [Fin.val_castSucc, Fin.val_castAdd] <;> try omega)
  have hb : parPt (Fin.init (z ∘ delDummy p n)) (Fin.last p) = pinX p n (Fin.init z) := by
    simp only [parPt, pinX, Fin.init, Function.comp_apply]
    exact delDummy_apply_eq z ((Fin.castAdd (n + 1) (Fin.last p)).castSucc)
      ((Fin.natAdd p 0).castSucc)
      (by simp only [Fin.val_castSucc, Fin.val_castAdd, Fin.val_last, Fin.val_natAdd,
        Fin.val_zero] <;> try omega)
  show f (fun i : Fin p => parPt (Fin.init (z ∘ delDummy p n)) (Fin.castSucc i))
      (Fin.cons (parPt (Fin.init (z ∘ delDummy p n)) (Fin.last p)) (Fin.init w)) =
    f (pinL p n (Fin.init z)) (Fin.cons (pinX p n (Fin.init z)) (Fin.init w))
  rw [ha, hb]

/-- The cube block of the padded point, read in the first `n` coordinates, is the cube point of
the pinned point. -/
private theorem init_cubePt_init_delDummy (p n : ℕ) (z : Fin (p + (n + 1) + 1) → ℝ) :
    Fin.init (cubePt (Fin.init (z ∘ delDummy p n))) = pinY p n (Fin.init z) := by
  funext j
  simp only [cubePt, pinY, Fin.init, Function.comp_apply]
  exact delDummy_apply_eq z ((Fin.natAdd (p + 1) (Fin.castSucc j)).castSucc)
    ((Fin.natAdd p j.succ).castSucc)
    (by simp only [Fin.val_castSucc, Fin.val_natAdd, Fin.val_succ] <;> try omega)

/-- The value coordinate of the padded point is the value coordinate of the pinned point. -/
private theorem comp_delDummy_last (p n : ℕ) (z : Fin (p + (n + 1) + 1) → ℝ) :
    z (delDummy p n (Fin.last ((p + 1) + (n + 1)))) = z (Fin.last (p + (n + 1))) := by
  rw [delDummy_last]

/-!
  ## The derivative in `iteratedFDeriv` form

  The two transport lemmas `Work.WilG4c.contDiffAt_init_iff` and
  `Work.WilG4c.iterDir_init_transport` concern `Fin.init`; they are assembled (through
  `Work.WilG4c.iterDir_eq_iteratedFDeriv`) into the `iteratedFDeriv` statement the graph
  comparison needs.
-/

/-- The `|M|`-th directional derivative of the padded function in the directions
`M.map Fin.castSucc` is the `|M|`-th directional derivative of `g` at `Fin.init y` in the
directions `M`. -/
private theorem iteratedFDeriv_init_castSucc {n : ℕ} (g : (Fin n → ℝ) → ℝ) (M : List (Fin n))
    (y : Fin (n + 1) → ℝ) (h : ContDiffAt ℝ M.length g (Fin.init y)) :
    iteratedFDeriv ℝ M.length g (Fin.init y) (fun j => Pi.single (M.get j) 1) =
      iteratedFDeriv ℝ (M.map Fin.castSucc).length
        (fun w : Fin (n + 1) → ℝ => g (Fin.init w)) y
        (fun j => Pi.single ((M.map Fin.castSucc).get j) 1) := by
  have hpad : ContDiffAt ℝ (M.map Fin.castSucc).length
      (fun w : Fin (n + 1) → ℝ => g (Fin.init w)) y :=
    (Work.WilG4c.contDiffAt_init_iff g (M.map Fin.castSucc).length y).mpr
      (by simpa [List.length_map] using h)
  rw [← Work.WilG4c.iterDir_eq_iteratedFDeriv M g (Fin.init y) h,
    ← Work.WilG4c.iterDir_init_transport g M y hpad,
    Work.WilG4c.iterDir_eq_iteratedFDeriv (M.map Fin.castSucc)
      (fun w : Fin (n + 1) → ℝ => g (Fin.init w)) y hpad]

/-- The pinned slice derivative graph `pinDg p n f M` (in the ambient layout `(l, x, y, s)`) is
the pullback of the fibre derivative graph of the *padded* pinned family `padFam p n f` along the
index map `delDummy p n` that deletes the dummy cube coordinate.  The dummy coordinate is never
read, and the derivative directions `M` sit in the first `n` cube coordinates of `padFam`
(embedded by `Fin.castSucc`). -/
theorem pinDg_eq_coordPre_AlDgListSlice (p n : ℕ)
    (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (M : List (Fin n)) :
    Work.WilkG4c.pinDg p n f M =
      Work.WilG5.coordPre (Work.WilkG4c.delDummy p n)
        (Work.WilkG4c.AlDgListSlice (p + 1) n (Work.WilkG4c.padFam p n f)
          (M.map Fin.castSucc)) := by
  ext z
  simp only [Work.WilG5.coordPre, Set.mem_ofPred_eq]
  rw [mem_pinDg, mem_AlDgListSlice]
  have hfun : padFam p n f (parPt (Fin.init (z ∘ delDummy p n))) =
      fun w : Fin (n + 1) → ℝ =>
        slice (f (pinL p n (Fin.init z))) (pinX p n (Fin.init z)) (Fin.init w) := by
    funext w
    exact padFam_parPt_delDummy_apply p n f z w
  simp only [hfun, Function.comp_apply]
  have hiff : ContDiffAt ℝ (M.map Fin.castSucc).length
        (fun w : Fin (n + 1) → ℝ =>
          slice (f (pinL p n (Fin.init z))) (pinX p n (Fin.init z)) (Fin.init w))
        (cubePt (Fin.init (z ∘ delDummy p n))) ↔
      ContDiffAt ℝ M.length (slice (f (pinL p n (Fin.init z))) (pinX p n (Fin.init z)))
        (pinY p n (Fin.init z)) := by
    rw [Work.WilG4c.contDiffAt_init_iff (slice (f (pinL p n (Fin.init z))) (pinX p n (Fin.init z)))
      (M.map Fin.castSucc).length (cubePt (Fin.init (z ∘ delDummy p n)))]
    rw [init_cubePt_init_delDummy p n z, List.length_map]
  have key : ∀ (hpad : ContDiffAt ℝ (M.map Fin.castSucc).length
        (fun w : Fin (n + 1) → ℝ =>
          slice (f (pinL p n (Fin.init z))) (pinX p n (Fin.init z)) (Fin.init w))
        (cubePt (Fin.init (z ∘ delDummy p n)))),
      ContDiffAt ℝ M.length (slice (f (pinL p n (Fin.init z))) (pinX p n (Fin.init z)))
        (pinY p n (Fin.init z)) →
      iteratedFDeriv ℝ M.length (slice (f (pinL p n (Fin.init z))) (pinX p n (Fin.init z)))
          (pinY p n (Fin.init z)) (fun j => Pi.single (M.get j) 1) =
        iteratedFDeriv ℝ (M.map Fin.castSucc).length
          (fun w : Fin (n + 1) → ℝ =>
            slice (f (pinL p n (Fin.init z))) (pinX p n (Fin.init z)) (Fin.init w))
          (cubePt (Fin.init (z ∘ delDummy p n)))
          (fun j => Pi.single ((M.map Fin.castSucc).get j) 1) := by
    intro hpad hL
    have hL' : ContDiffAt ℝ M.length (slice (f (pinL p n (Fin.init z))) (pinX p n (Fin.init z)))
        (Fin.init (cubePt (Fin.init (z ∘ delDummy p n)))) := by
      rw [init_cubePt_init_delDummy p n z]
      exact hL
    rw [← init_cubePt_init_delDummy p n z,
      iteratedFDeriv_init_castSucc (slice (f (pinL p n (Fin.init z))) (pinX p n (Fin.init z)))
        M (cubePt (Fin.init (z ∘ delDummy p n))) hL']
  constructor
  · rintro ⟨hL, hE⟩
    have hpad := hiff.mpr hL
    refine ⟨hpad, ?_⟩
    rw [comp_delDummy_last p n z, hE, key hpad hL]
  · rintro ⟨hpad, hE⟩
    have hL := hiff.mp hpad
    refine ⟨hL, ?_⟩
    rw [← comp_delDummy_last p n z, hE, ← key hpad hL]

end Work.WilG4c
