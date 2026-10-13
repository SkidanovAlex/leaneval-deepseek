import Mathlib
import Submission.Work.WilG4a.CD.fibDerivDefs

namespace Work.WilG4a.CD

/-! ## Coordinate computations for `cutIdx`

`cutIdx p k e : Fin (k+2) → Fin (p+2)` sends the `k` parameter coordinates to the coordinates
selected by `e`, and the two remaining coordinates to the `x`-coordinate (`p`) and the value
coordinate (`p+1`).  The three lemmas below record its values at exactly the three kinds of
indices that `Fin.init (Fin.init ·)` and `Fin.init · (Fin.last ·)` produce. -/

/-- `cutIdx` at a parameter index. -/
lemma cutIdx_castSucc_castSucc {p k : ℕ} (e : Fin k ↪ Fin p) (i : Fin k) :
    cutIdx p k e (Fin.castSucc (Fin.castSucc i)) = Fin.castSucc (Fin.castSucc (e i)) := by
  simp only [cutIdx, Fin.addCases]
  rw [dite_eq_left (by simp)]
  rfl

/-- `cutIdx` at the `x`-coordinate. -/
lemma cutIdx_castSucc_last {p k : ℕ} (e : Fin k ↪ Fin p) :
    cutIdx p k e (Fin.castSucc (Fin.last k)) = Fin.castSucc (Fin.last p) := by
  apply Fin.ext
  simp only [cutIdx, Fin.addCases, Fin.val_castSucc, Fin.val_last]
  rw [dite_eq_right (by simp)]
  simp

/-- `cutIdx` at the value coordinate. -/
lemma cutIdx_last {p k : ℕ} (e : Fin k ↪ Fin p) :
    cutIdx p k e (Fin.last (k+1)) = Fin.last (p+1) := by
  apply Fin.ext
  simp only [cutIdx, Fin.addCases, Fin.val_last]
  rw [dite_eq_right (by simp)]
  simp

/-! ## Reading off the components of `w ∘ cutIdx`

These are the three components of the `(k+2)`-tuple `w ∘ cutIdx p k e` that the unfoldings of
`fibDerivSet` and of the pulled-back family refer to: the parameter tuple, the base point and the
value. -/

/-- The parameter tuple of `w ∘ cutIdx` is the parameter tuple of `w` restricted along `e`. -/
lemma init_init_comp_cutIdx {p k : ℕ} (e : Fin k ↪ Fin p) (w : Fin (p + 2) → ℝ) :
    Fin.init (Fin.init (w ∘ cutIdx p k e)) = (Fin.init (Fin.init w)) ∘ e := by
  ext i
  simp only [Fin.init, Function.comp_apply]
  rw [cutIdx_castSucc_castSucc]

/-- The base point of `w ∘ cutIdx` is the base point of `w`. -/
lemma init_comp_cutIdx_last {p k : ℕ} (e : Fin k ↪ Fin p) (w : Fin (p + 2) → ℝ) :
    (Fin.init (w ∘ cutIdx p k e)) (Fin.last k) = (Fin.init w) (Fin.last p) := by
  simp only [Fin.init, Function.comp_apply]
  rw [cutIdx_castSucc_last]

/-- The value coordinate of `w ∘ cutIdx` is the value coordinate of `w`. -/
lemma comp_cutIdx_last {p k : ℕ} (e : Fin k ↪ Fin p) (w : Fin (p + 2) → ℝ) :
    (w ∘ cutIdx p k e) (Fin.last (k+1)) = w (Fin.last (p+1)) := by
  simp only [Function.comp_apply]
  rw [cutIdx_last]

/-- Transport of the target set along a parametrisation. If `Ψ : ℝ^k → ℝ^p` satisfies `Ψ (l ∘ e) = l` for all `l ∈ C` (`e : Fin k ↪ Fin p`), then for `w : Fin (p+2) → ℝ` with `Fin.init (Fin.init w) ∈ C` the point `w = (l, x, y)` belongs to `T_j(f) = fibDerivSet f j` if and only if the `(k+2)`-tuple `(l ∘ e, x, y) = w ∘ cutIdx p k e` belongs to `T_j` of the pulled-back family `(u,x) ↦ f (Ψ u) x`. This is a pure set identity: on the fibre over `l ∈ C` the two families have the same slice, because `Ψ (l ∘ e) = l`. -/
theorem fibDerivSet_lift {p k : ℕ} (e : Fin k ↪ Fin p) (C : Set (Fin p → ℝ))
    (Ψ : (Fin k → ℝ) → (Fin p → ℝ)) (hsec : ∀ l ∈ C, Ψ (l ∘ e) = l)
    (f : (Fin p → ℝ) → ℝ → ℝ) (j : ℕ) (w : Fin (p + 2) → ℝ)
    (hw : Fin.init (Fin.init w) ∈ C) :
    (w ∈ Work.WilG4a.CD.fibDerivSet f j ↔
      (w ∘ Work.WilG4a.CD.cutIdx p k e) ∈
        Work.WilG4a.CD.fibDerivSet (fun (u : Fin k → ℝ) (x : ℝ) => f (Ψ u) x) j) := by
  -- The two families have the same slice over `w`: the parametrisation is a section over `C`.
  have hΨ : Ψ ((Fin.init (Fin.init w)) ∘ e) = Fin.init (Fin.init w) := hsec _ hw
  have hfun : (fun x : ℝ => f (Ψ (Fin.init (Fin.init (w ∘ cutIdx p k e)))) x)
      = fun x : ℝ => f (Fin.init (Fin.init w)) x := by
    rw [init_init_comp_cutIdx, hΨ]
  rw [mem_fibDerivSet, mem_fibDerivSet, hfun, init_comp_cutIdx_last, comp_cutIdx_last]

end Work.WilG4a.CD
