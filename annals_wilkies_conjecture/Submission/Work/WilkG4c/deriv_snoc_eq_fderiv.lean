import Mathlib
import Submission.Work.WilG4c.CellMonoDeriv

namespace Work.WilkG4c

/-- **`deriv` in the last coordinate is `fderiv` on the last basis vector.** For `g : ℝ^{p+1} → ℝ`
and `l : ℝ^p`, the derivative of the one-variable slice `s ↦ g (Fin.snoc l s)` equals the `fderiv`
of `g` at `Fin.snoc l s` applied to `Pi.single (Fin.last p) 1`. -/
theorem deriv_snoc_eq_fderiv {p : ℕ} (g : (Fin (p + 1) → ℝ) → ℝ) (l : Fin p → ℝ) (s : ℝ)
    (hg : DifferentiableAt ℝ g (Fin.snoc l s)) :
    deriv (fun s' : ℝ => g (Fin.snoc l s')) s
      = fderiv ℝ g (Fin.snoc l s) (Pi.single (Fin.last p) (1 : ℝ)) := by
  -- The slice `s' ↦ Fin.snoc l s'` is affine in `s'`, with derivative the last basis vector `e`.
  have hφ : HasDerivAt (fun s' : ℝ => Fin.snoc l s')
      (Pi.single (Fin.last p) (1 : ℝ) : Fin (p + 1) → ℝ) s := by
    set e : Fin (p + 1) → ℝ := Pi.single (Fin.last p) 1 with he
    -- `s' ↦ Fin.snoc l s + (s' - s) • e` and `s' ↦ Fin.snoc l s'` agree, so it suffices to
    -- differentiate the manifestly affine map.
    have hfun : (fun s' : ℝ => Fin.snoc l s + (s' - s) • e) = fun s' : ℝ => Fin.snoc l s' := by
      funext s'
      ext i
      obtain ⟨j, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last i
      · simp [Fin.snoc_castSucc, he]
      · simp [Fin.snoc_last, he, Pi.single_eq_same]
    have hsub : HasDerivAt (fun s' : ℝ => s' - s) (1 : ℝ) s := (hasDerivAt_id s).sub_const s
    have hsmul : HasDerivAt (fun s' : ℝ => (s' - s) • e) ((1 : ℝ) • e) s := hsub.smul_const e
    have h1 : HasDerivAt (fun s' : ℝ => Fin.snoc l s + (s' - s) • e) e s := by
      have := hsmul.const_add (Fin.snoc l s)
      simpa using this
    rw [hfun] at h1
    exact h1
  -- Chain rule: `g` has Fréchet derivative `fderiv ℝ g (Fin.snoc l s)` there.
  have hcomp : HasDerivAt (fun s' : ℝ => g (Fin.snoc l s'))
      (fderiv ℝ g (Fin.snoc l s) (Pi.single (Fin.last p) (1 : ℝ))) s :=
    hg.hasFDerivAt.comp_hasDerivAt s hφ
  exact hcomp.deriv

end Work.WilkG4c
