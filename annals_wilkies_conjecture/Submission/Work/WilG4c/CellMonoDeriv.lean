import Mathlib

namespace Work.WilG4c

/-! ## Monotonicity of a function along the last coordinate of a fibre-convex set

If `κ ⊆ ℝ^{m+1}` has the property that the fibre over every base point (i.e. every non-last
coordinate tuple) is an interval — equivalently, that for `w, w' ∈ κ` with the same initial
segment the whole vertical segment joining them lies in `κ` — and if `f` is `C^1` on `κ` with
non-negative derivative in the last coordinate direction everywhere on `κ`, then `f` is monotone
in the last coordinate along `κ`.

The proof parametrises the vertical segment by `φ t = Fin.snoc (Fin.init w) t`, which is an
affine map of `ℝ` with derivative the constant vector `Pi.single (Fin.last m) 1`, and applies
the monotonicity criterion `monotoneOn_of_hasDerivWithinAt_nonneg` to `f ∘ φ` on the interval
`[w (last m), w' (last m)]`. -/

/-- The affine parametrisation of the fibre coordinate: appending `t` in the last coordinate is
the same as appending `0` and then translating by `t` in the direction `Pi.single (Fin.last m) 1`.
-/
lemma fin_snoc_eq_add_smul {m : ℕ} (u : Fin m → ℝ) (t : ℝ) :
    Fin.snoc u t = Fin.snoc u 0 + t • (Pi.single (Fin.last m) (1 : ℝ) : Fin (m + 1) → ℝ) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simp

/-- `t ↦ Fin.snoc u t` is differentiable with constant derivative `Pi.single (Fin.last m) 1`. -/
lemma hasDerivAt_fin_snoc {m : ℕ} (u : Fin m → ℝ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => Fin.snoc u t)
      (Pi.single (Fin.last m) (1 : ℝ) : Fin (m + 1) → ℝ) x := by
  have h : HasDerivAt
      (fun t : ℝ => Fin.snoc u 0 + t • (Pi.single (Fin.last m) (1 : ℝ) : Fin (m + 1) → ℝ))
      (Pi.single (Fin.last m) (1 : ℝ) : Fin (m + 1) → ℝ) x := by
    have hh := (hasDerivAt_id x).smul_const (Pi.single (Fin.last m) (1 : ℝ) : Fin (m + 1) → ℝ)
    simp only [one_smul] at hh
    exact hh.const_add (Fin.snoc u 0)
  refine h.congr_of_eventuallyEq ?_
  filter_upwards with t
  exact fin_snoc_eq_add_smul u t

theorem CellMonoDeriv {m : ℕ} {κ : Set (Fin (m + 1) → ℝ)} {f : (Fin (m + 1) → ℝ) → ℝ}
    (hfib : ∀ w ∈ κ, ∀ w' ∈ κ, Fin.init w = Fin.init w' → ∀ t : ℝ,
      w (Fin.last m) ≤ t → t ≤ w' (Fin.last m) → Fin.snoc (Fin.init w) t ∈ κ)
    (hC1 : ∀ z ∈ κ, ContDiffAt ℝ 1 f z)
    (hder : ∀ z ∈ κ, 0 ≤ fderiv ℝ f z (Pi.single (Fin.last m) 1)) :
    ∀ w ∈ κ, ∀ w' ∈ κ, Fin.init w = Fin.init w' → w (Fin.last m) ≤ w' (Fin.last m) →
      f w ≤ f w' := by
  intro w hw w' hw' hinit hle
  -- the vertical segment over the common base point lies in `κ`
  have hmem : ∀ t ∈ Set.Icc (w (Fin.last m)) (w' (Fin.last m)),
      Fin.snoc (Fin.init w) t ∈ κ := by
    intro t ht
    rw [Set.mem_Icc] at ht
    exact hfib w hw w' hw' hinit t ht.1 ht.2
  -- derivative of the parametrised function
  have hderiv : ∀ x ∈ Set.Icc (w (Fin.last m)) (w' (Fin.last m)),
      HasDerivAt (fun t : ℝ => f (Fin.snoc (Fin.init w) t))
        (fderiv ℝ f (Fin.snoc (Fin.init w) x)
          (Pi.single (Fin.last m) (1 : ℝ) : Fin (m + 1) → ℝ)) x := by
    intro x hx
    have hxk : Fin.snoc (Fin.init w) x ∈ κ := hmem x hx
    have hd : DifferentiableAt ℝ f (Fin.snoc (Fin.init w) x) :=
      (hC1 _ hxk).differentiableAt (by norm_num)
    exact hd.hasFDerivAt.comp_hasDerivAt x (hasDerivAt_fin_snoc (Fin.init w) x)
  -- monotonicity on the interval by the mean value theorem
  have hmono : MonotoneOn (fun t : ℝ => f (Fin.snoc (Fin.init w) t))
      (Set.Icc (w (Fin.last m)) (w' (Fin.last m))) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (f' := fun x => fderiv ℝ f (Fin.snoc (Fin.init w) x)
        (Pi.single (Fin.last m) (1 : ℝ) : Fin (m + 1) → ℝ)) ?_ ?_ ?_
    · -- continuity on the interval
      intro x hx
      exact (((hC1 _ (hmem x hx)).continuousAt).comp
        (hasDerivAt_fin_snoc (Fin.init w) x).continuousAt).continuousWithinAt
    · -- differentiability on the interior
      intro x hx
      have hxI : x ∈ Set.Icc (w (Fin.last m)) (w' (Fin.last m)) := by
        rw [interior_Icc] at hx
        exact Set.Ioo_subset_Icc_self hx
      exact (hderiv x hxI).hasDerivWithinAt
    · -- non-negative derivative on the interior
      intro x hx
      have hxI : x ∈ Set.Icc (w (Fin.last m)) (w' (Fin.last m)) := by
        rw [interior_Icc] at hx
        exact Set.Ioo_subset_Icc_self hx
      exact hder _ (hmem x hxI)
  have ha : w (Fin.last m) ∈ Set.Icc (w (Fin.last m)) (w' (Fin.last m)) :=
    ⟨le_refl _, hle⟩
  have hb : w' (Fin.last m) ∈ Set.Icc (w (Fin.last m)) (w' (Fin.last m)) :=
    ⟨hle, le_refl _⟩
  have e1 : f (Fin.snoc (Fin.init w) (w (Fin.last m))) = f w :=
    congrArg f (Fin.snoc_init_self w)
  have e2 : f (Fin.snoc (Fin.init w) (w' (Fin.last m))) = f w' := by
    rw [hinit]
    exact congrArg f (Fin.snoc_init_self w')
  calc f w = f (Fin.snoc (Fin.init w) (w (Fin.last m))) := e1.symm
    _ ≤ f (Fin.snoc (Fin.init w) (w' (Fin.last m))) := hmono ha hb hle
    _ = f w' := e2

end Work.WilG4c
