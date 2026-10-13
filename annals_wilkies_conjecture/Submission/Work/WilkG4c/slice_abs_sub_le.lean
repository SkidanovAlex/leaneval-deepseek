import Mathlib
import Submission.Work.WilG4c.CellMonoDeriv
import Submission.Work.WilkG4c.mvt_abs_sub_lower_bound

namespace Work.WilkG4c

/-! ## Quantitative injectivity along the last coordinate

If `κ ⊆ ℝ^{p+1}` is closed under vertical segments and `g` is `C¹` on `κ` with
`|∂_{last} g| ≥ c > 0` on `κ`, then `g` is `c`-expanding along vertical segments.

The proof parametrises the vertical segment joining `w` and `w'` (which have the same initial
segment) by `φ t = Fin.snoc (Fin.init w) t`.  The fibre-convexity hypothesis puts the whole
segment in `κ`, hence the one-variable function `t ↦ g (φ t)` has, at every interior point `t`,
derivative `fderiv ℝ g (φ t) (Pi.single (Fin.last p) 1)` of absolute value at least `c`.  The mean
value theorem then produces an interior point `ξ` with
`|g w' - g w| = |deriv (g ∘ φ) ξ| * |w' (last) - w (last)| ≥ c * |w' (last) - w (last)|`. -/

/-- **Directional form.** If `w (last p) ≤ w' (last p)` then the difference of the values is at
least `c` times the (unsigned) difference of the last coordinates. -/
theorem slice_abs_sub_le_of_le {p : ℕ} {g : (Fin (p + 1) → ℝ) → ℝ}
    {κ : Set (Fin (p + 1) → ℝ)}
    (c : ℝ)
    (hfib : ∀ w ∈ κ, ∀ w' ∈ κ, Fin.init w = Fin.init w' → ∀ t : ℝ, w (Fin.last p) ≤ t →
      t ≤ w' (Fin.last p) → Fin.snoc (Fin.init w) t ∈ κ)
    (hC1 : ∀ z ∈ κ, ContDiffAt ℝ 1 g z)
    (hder : ∀ z ∈ κ, c ≤ |fderiv ℝ g z (Pi.single (Fin.last p) (1 : ℝ))|) :
    ∀ w ∈ κ, ∀ w' ∈ κ, Fin.init w = Fin.init w' → w (Fin.last p) ≤ w' (Fin.last p) →
      c * (w' (Fin.last p) - w (Fin.last p)) ≤ |g w' - g w| := by
  intro w hw w' hw' hinit hle
  rcases eq_or_lt_of_le hle with heq | hlt
  · rw [← heq, sub_self, mul_zero]
    exact abs_nonneg _
  · -- the vertical segment over the common base point lies in `κ`
    have hmem : ∀ t ∈ Set.Icc (w (Fin.last p)) (w' (Fin.last p)),
        Fin.snoc (Fin.init w) t ∈ κ := by
      intro t ht
      rw [Set.mem_Icc] at ht
      exact hfib w hw w' hw' hinit t ht.1 ht.2
    -- the one-variable slice is differentiable on the segment, with the expected derivative
    have hderiv : ∀ x ∈ Set.Icc (w (Fin.last p)) (w' (Fin.last p)),
        HasDerivAt (fun t : ℝ => g (Fin.snoc (Fin.init w) t))
          (fderiv ℝ g (Fin.snoc (Fin.init w) x) (Pi.single (Fin.last p) (1 : ℝ))) x := by
      intro x hx
      exact (((hC1 _ (hmem x hx)).differentiableAt (by norm_num)).hasFDerivAt).comp_hasDerivAt x
        (_root_.Work.WilG4c.hasDerivAt_fin_snoc (Fin.init w) x)
    have hcont : ContinuousOn (fun t : ℝ => g (Fin.snoc (Fin.init w) t))
        (Set.Icc (w (Fin.last p)) (w' (Fin.last p))) := by
      intro x hx
      exact (hderiv x hx).continuousAt.continuousWithinAt
    have hdiff : ∀ x ∈ Set.Ioo (w (Fin.last p)) (w' (Fin.last p)),
        DifferentiableAt ℝ (fun t : ℝ => g (Fin.snoc (Fin.init w) t)) x := by
      intro x hx
      exact (hderiv x (Set.Ioo_subset_Icc_self hx)).differentiableAt
    have hder' : ∀ x ∈ Set.Ioo (w (Fin.last p)) (w' (Fin.last p)),
        c ≤ |deriv (fun t : ℝ => g (Fin.snoc (Fin.init w) t)) x| := by
      intro x hx
      rw [(hderiv x (Set.Ioo_subset_Icc_self hx)).deriv]
      exact hder _ (hmem _ (Set.Ioo_subset_Icc_self hx))
    -- mean value theorem on the segment
    have hbound := mvt_abs_sub_lower_bound hlt hcont hdiff hder'
    have e1 : g (Fin.snoc (Fin.init w) (w (Fin.last p))) = g w :=
      congrArg g (Fin.snoc_init_self w)
    have e2 : g (Fin.snoc (Fin.init w) (w' (Fin.last p))) = g w' := by
      rw [hinit]
      exact congrArg g (Fin.snoc_init_self w')
    rw [e1, e2] at hbound
    exact hbound

/-- **Quantitative injectivity along the last coordinate.** If `κ ⊆ ℝ^{p+1}` is closed under
vertical segments and `g` is `C¹` at every point of `κ` with `|∂_{last} g| ≥ c > 0` on `κ`, then
`g` is `c`-expanding along vertical segments: for `w, w' ∈ κ` with equal initial segment,
`c * |w (Fin.last p) - w' (Fin.last p)| ≤ |g w - g w'|`. -/
theorem slice_abs_sub_le {p : ℕ} {g : (Fin (p + 1) → ℝ) → ℝ} {κ : Set (Fin (p + 1) → ℝ)}
    (c : ℝ) (hc : 0 < c)
    (hfib : ∀ w ∈ κ, ∀ w' ∈ κ, Fin.init w = Fin.init w' → ∀ t : ℝ, w (Fin.last p) ≤ t →
      t ≤ w' (Fin.last p) → Fin.snoc (Fin.init w) t ∈ κ)
    (hC1 : ∀ z ∈ κ, ContDiffAt ℝ 1 g z)
    (hder : ∀ z ∈ κ, c ≤ |fderiv ℝ g z (Pi.single (Fin.last p) (1 : ℝ))|) :
    ∀ w ∈ κ, ∀ w' ∈ κ, Fin.init w = Fin.init w' →
      c * |w (Fin.last p) - w' (Fin.last p)| ≤ |g w - g w'| := by
  intro w hw w' hw' hinit
  rcases le_total (w (Fin.last p)) (w' (Fin.last p)) with hle | hle
  · have h := slice_abs_sub_le_of_le (p := p) (g := g) (κ := κ) c hfib hC1 hder
      w hw w' hw' hinit hle
    rw [abs_of_nonpos (sub_nonpos.mpr hle), neg_sub, abs_sub_comm]
    exact h
  · have h := slice_abs_sub_le_of_le (p := p) (g := g) (κ := κ) c hfib hC1 hder
      w' hw' w hw hinit.symm hle
    rw [abs_of_nonneg (sub_nonneg.mpr hle)]
    exact h

end Work.WilkG4c
