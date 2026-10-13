import Mathlib
import Submission.Work.WilG4c.CellMonoDeriv

namespace Work.WilkG4c

/-- **Strict monotonicity along the last coordinate.** If `κ ⊆ ℝ^{p+1}` is closed under vertical
segments (for `w, w' ∈ κ` with equal initial segment, the whole segment joining them is in `κ`), and
`g` is `C¹` at every point of `κ` with last-coordinate derivative at least `c > 0` on `κ`, then `g`
is strictly increasing along vertical segments of `κ`. -/
theorem slice_strictMono {p : ℕ} {g : (Fin (p + 1) → ℝ) → ℝ} {κ : Set (Fin (p + 1) → ℝ)}
    (c : ℝ) (hc : 0 < c)
    (hfib : ∀ w ∈ κ, ∀ w' ∈ κ, Fin.init w = Fin.init w' → ∀ t : ℝ, w (Fin.last p) ≤ t →
      t ≤ w' (Fin.last p) → Fin.snoc (Fin.init w) t ∈ κ)
    (hC1 : ∀ z ∈ κ, ContDiffAt ℝ 1 g z)
    (hder : ∀ z ∈ κ, c ≤ fderiv ℝ g z (Pi.single (Fin.last p) (1 : ℝ))) :
    ∀ w ∈ κ, ∀ w' ∈ κ, Fin.init w = Fin.init w' → w (Fin.last p) < w' (Fin.last p) → g w < g w' := by
  intro w hw w' hw' hinit hlt
  -- The vertical segment over the common base point lies in `κ`.
  have hmem : ∀ t ∈ Set.Icc (w (Fin.last p)) (w' (Fin.last p)),
      Fin.snoc (Fin.init w) t ∈ κ := by
    intro t ht
    rw [Set.mem_Icc] at ht
    exact hfib w hw w' hw' hinit t ht.1 ht.2
  -- The one-variable slice has the expected derivative at every point of the segment.
  have hderiv : ∀ x ∈ Set.Icc (w (Fin.last p)) (w' (Fin.last p)),
      HasDerivAt (fun t : ℝ => g (Fin.snoc (Fin.init w) t))
        (fderiv ℝ g (Fin.snoc (Fin.init w) x) (Pi.single (Fin.last p) (1 : ℝ))) x := by
    intro x hx
    have hxk : Fin.snoc (Fin.init w) x ∈ κ := hmem x hx
    have hd : DifferentiableAt ℝ g (Fin.snoc (Fin.init w) x) :=
      (hC1 _ hxk).differentiableAt (by norm_num)
    exact hd.hasFDerivAt.comp_hasDerivAt x
      (_root_.Work.WilG4c.hasDerivAt_fin_snoc (Fin.init w) x)
  -- Strict monotonicity of the slice on the interval, with derivative strictly positive there.
  have hstrict : StrictMonoOn (fun t : ℝ => g (Fin.snoc (Fin.init w) t))
      (Set.Icc (w (Fin.last p)) (w' (Fin.last p))) := by
    refine strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _)
      (f' := fun x => fderiv ℝ g (Fin.snoc (Fin.init w) x)
        (Pi.single (Fin.last p) (1 : ℝ))) ?_ ?_ ?_
    · -- continuity on the interval
      intro x hx
      exact (((hC1 _ (hmem x hx)).continuousAt).comp
        (_root_.Work.WilG4c.hasDerivAt_fin_snoc (Fin.init w) x).continuousAt).continuousWithinAt
    · -- differentiability on the interior
      intro x hx
      have hxI : x ∈ Set.Icc (w (Fin.last p)) (w' (Fin.last p)) := by
        rw [interior_Icc] at hx
        exact Set.Ioo_subset_Icc_self hx
      exact (hderiv x hxI).hasDerivWithinAt
    · -- strictly positive derivative on the interior
      intro x hx
      have hxI : x ∈ Set.Icc (w (Fin.last p)) (w' (Fin.last p)) := by
        rw [interior_Icc] at hx
        exact Set.Ioo_subset_Icc_self hx
      exact lt_of_lt_of_le hc (hder _ (hmem x hxI))
  have ha : w (Fin.last p) ∈ Set.Icc (w (Fin.last p)) (w' (Fin.last p)) := ⟨le_refl _, hlt.le⟩
  have hb : w' (Fin.last p) ∈ Set.Icc (w (Fin.last p)) (w' (Fin.last p)) := ⟨hlt.le, le_refl _⟩
  calc g w = g (Fin.snoc (Fin.init w) (w (Fin.last p))) :=
        (congrArg g (Fin.snoc_init_self w)).symm
    _ < g (Fin.snoc (Fin.init w) (w' (Fin.last p))) := hstrict ha hb hlt
    _ = g w' := by rw [hinit]; exact congrArg g (Fin.snoc_init_self w')

end Work.WilkG4c
