import Mathlib
import Submission.Work.WilG4a.Defs
import Submission.Work.WilG4a.Cells
import Submission.Work.WilG4a.f1affine1_defs

set_option linter.unusedVariables false
set_option autoImplicit false
noncomputable section

namespace Work.WilG4a

/-- **A nondegenerate fibre arbitrarily near every point of `I`.**

The family `κ` of finitely many subsets of `ℝ^{p+1}` covers `{l} × I` over the parameter
`l` (`hcover`): for every `x ∈ I` there is a member `κ σ` containing `Fin.snoc l x`.  Then
for every `x ∈ I` and every `ε > 0` there is a member `σ` whose fibre over `l` contains a
point `y` with `|y - x| < ε`, and which is not a subsingleton.

In fact no hypothesis on the shape of the fibres is needed beyond *finiteness of
subsingleton fibres*: the interval `I ∩ (x - ε, x + ε)` is infinite and is covered by the
finitely many fibres `fibre (κ σ) l`; a finite union of subsingletons is finite, so one of
the fibres meets this interval in infinitely many points, hence is not a subsingleton.
(The hypothesis `hsub`, which records that each fibre is either a subsingleton or an open
interval, is therefore not used; it is kept because it is part of the requested
statement.) -/
theorem exists_near_nondegen_fibre {p m : ℕ} (κ : Fin m → Set (Fin (p + 1) → ℝ)) (hcover : ∀ l : Fin p → ℝ, ∀ x ∈ Work.WilG4a.I, ∃ σ, Fin.snoc l x ∈ κ σ) (hsub : ∀ (σ : Fin m) (l : Fin p → ℝ), (Work.WilG4a.fibre (κ σ) l).Subsingleton ∨ ∃ a b : ℝ, a < b ∧ Work.WilG4a.fibre (κ σ) l = Set.Ioo a b) (l : Fin p → ℝ) (x : ℝ) (hx : x ∈ Work.WilG4a.I) (ε : ℝ) (hε : 0 < ε) : ∃ σ, ∃ y ∈ Work.WilG4a.fibre (κ σ) l, |y - x| < ε ∧ ¬ (Work.WilG4a.fibre (κ σ) l).Subsingleton := by
  obtain ⟨hx0, hx1⟩ := hx
  -- a small radius around `x` which still lies inside `I ∩ (x-ε, x+ε)`
  set δ : ℝ := min ε (min x (1 - x)) / 2 with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    linarith [lt_min hε (lt_min hx0 (by linarith : (0 : ℝ) < 1 - x))]
  have hδε : δ < ε := by
    have h := min_le_left ε (min x (1 - x)); rw [hδdef]; linarith
  have hδx : δ < x := by
    have h1 := min_le_right ε (min x (1 - x))
    have h2 := min_le_left x (1 - x); rw [hδdef]; linarith
  have hδ1 : δ < 1 - x := by
    have h1 := min_le_right ε (min x (1 - x))
    have h2 := min_le_right x (1 - x); rw [hδdef]; linarith
  have hsubIoo : Set.Ioo (x - δ) (x + δ) ⊆ Work.WilG4a.I ∩ Set.Ioo (x - ε) (x + ε) := by
    intro y hy
    obtain ⟨hy1, hy2⟩ := hy
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  have hSinf : (Work.WilG4a.I ∩ Set.Ioo (x - ε) (x + ε)).Infinite :=
    Set.Infinite.mono hsubIoo (Set.Ioo_infinite (by linarith))
  have hcoverS : Work.WilG4a.I ∩ Set.Ioo (x - ε) (x + ε) ⊆
      ⋃ σ : Fin m, Work.WilG4a.fibre (κ σ) l := by
    intro y hy
    obtain ⟨σ, hσ⟩ := hcover l y hy.1
    exact Set.mem_iUnion.mpr ⟨σ, hσ⟩
  -- some fibre meets `I ∩ (x-ε, x+ε)` in infinitely many points
  obtain ⟨σ, hσinf⟩ : ∃ σ : Fin m,
      (Work.WilG4a.fibre (κ σ) l ∩ (Work.WilG4a.I ∩ Set.Ioo (x - ε) (x + ε))).Infinite := by
    by_contra hcon
    have hfin : ∀ σ : Fin m,
        (Work.WilG4a.fibre (κ σ) l ∩ (Work.WilG4a.I ∩ Set.Ioo (x - ε) (x + ε))).Finite := by
      intro σ
      by_contra hf
      exact hcon ⟨σ, hf⟩
    have hunionfin : (⋃ σ : Fin m,
        Work.WilG4a.fibre (κ σ) l ∩ (Work.WilG4a.I ∩ Set.Ioo (x - ε) (x + ε))).Finite :=
      Set.finite_iUnion hfin
    have hsub' : Work.WilG4a.I ∩ Set.Ioo (x - ε) (x + ε) ⊆
        ⋃ σ : Fin m, Work.WilG4a.fibre (κ σ) l ∩
          (Work.WilG4a.I ∩ Set.Ioo (x - ε) (x + ε)) := by
      intro y hy
      obtain ⟨σ, hσ⟩ := Set.mem_iUnion.mp (hcoverS hy)
      exact Set.mem_iUnion.mpr ⟨σ, hσ, hy⟩
    exact hSinf (hunionfin.subset hsub')
  have hnondeg : ¬ (Work.WilG4a.fibre (κ σ) l).Subsingleton := by
    intro h
    exact hσinf (h.finite.inter_of_left _)
  obtain ⟨y, hy⟩ := hσinf.nonempty
  refine ⟨σ, y, hy.1, ?_, hnondeg⟩
  rw [abs_lt]
  exact ⟨by linarith [hy.2.2.1], by linarith [hy.2.2.2]⟩

end Work.WilG4a
