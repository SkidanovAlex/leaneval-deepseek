import Mathlib

/-!
# B5: small analytic helpers for the `κ`-collar

* `uniqueDiffOn_Icc_univ_Ioo` — `UniqueDiffOn` for a box that is closed in the first coordinate
  and open in the remaining ones (`Icc a b ×ˢ univ ×ˢ Ioo c d`).
* `fderivWithin_slice_deriv` — the `fderivWithin` in the last-coordinate direction `(0,0,1)` is
  the ordinary one-variable derivative of the slice `r ↦ f (τ, (t, r))`.
* `continuousOn_slice_deriv` — for a `C¹` function on such a box, the slice derivative is
  continuous on the box.  This is the ingredient that makes the "flatness of the level
  inversion at `ρ = 0`" uniform in `(τ, t)`.
-/

open Set Filter
open scoped Topology

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

/-- `UniqueDiffOn` for `Icc a b ×ˢ univ ×ˢ Ioo c d`, a box closed in the first coordinate. -/
theorem uniqueDiffOn_Icc_univ_Ioo (a b c d : ℝ) (hab : a < b) :
    UniqueDiffOn ℝ (Set.Icc a b ×ˢ (Set.univ : Set ℝ) ×ˢ Set.Ioo c d) :=
  (uniqueDiffOn_Icc hab).prod (uniqueDiffOn_univ.prod isOpen_Ioo.uniqueDiffOn)

/-- The `fderivWithin` of `f : ℝ × (ℝ × ℝ) → F` at a point of `A ×ˢ B` in the direction
`(0, (0, 1))` is the ordinary derivative of the slice `r ↦ f (τ, (t, r))` at `ρ`. -/
theorem fderivWithin_slice_deriv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × (ℝ × ℝ) → F} {A : Set ℝ} {B : Set (ℝ × ℝ)} {τ t ρ : ℝ}
    (hA : τ ∈ A) (hBnhds : B ∈ 𝓝 (t, ρ))
    (hd : DifferentiableWithinAt ℝ f (A ×ˢ B) (τ, (t, ρ))) :
    (fderivWithin ℝ f (A ×ˢ B) (τ, (t, ρ))) ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))
      = deriv (fun r : ℝ => f (τ, (t, r))) ρ := by
  have hfd := hd.hasFDerivWithinAt
  have hgd : HasDerivAt (fun r : ℝ => (τ, (t, r))) ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) ρ :=
    (hasDerivAt_const ρ τ).prodMk ((hasDerivAt_const ρ t).prodMk (hasDerivAt_id ρ))
  have hmem : ∀ᶠ r in 𝓝 ρ, (τ, (t, r)) ∈ A ×ˢ B := by
    filter_upwards [ContinuousAt.preimage_mem_nhds
      ((continuous_const.prodMk continuous_id).continuousAt) hBnhds] with r hr
    exact ⟨hA, hr⟩
  have hderiv : HasDerivAt (fun r : ℝ => f (τ, (t, r)))
      ((fderivWithin ℝ f (A ×ˢ B) (τ, (t, ρ))) ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))) ρ := by
    have hcomp := HasFDerivWithinAt.comp_hasFDerivAt ρ hfd
      ((hasDerivAt_iff_hasFDerivAt).mp hgd) hmem
    have := hcomp.hasDerivAt
    simpa [Function.comp_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply] using this
  exact hderiv.deriv.symm

/-- On a box `Icc a b ×ˢ univ ×ˢ Ioo c d` a `C¹` function has a continuous slice derivative in
the last coordinate. -/
theorem continuousOn_slice_deriv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × (ℝ × ℝ) → F} {a b c d : ℝ} (hab : a < b) {n : WithTop ℕ∞} (hn : 1 ≤ n)
    (hf : ContDiffOn ℝ n f (Set.Icc a b ×ˢ (Set.univ : Set ℝ) ×ˢ Set.Ioo c d)) :
    ContinuousOn (fun p : ℝ × (ℝ × ℝ) =>
        deriv (fun r : ℝ => f (p.1, (p.2.1, r))) p.2.2)
      (Set.Icc a b ×ˢ (Set.univ : Set ℝ) ×ˢ Set.Ioo c d) := by
  have hSdiff : UniqueDiffOn ℝ (Set.Icc a b ×ˢ (Set.univ : Set ℝ) ×ˢ Set.Ioo c d) :=
    uniqueDiffOn_Icc_univ_Ioo a b c d hab
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have hcont := hf.continuousOn_fderivWithin_apply hSdiff hn
  have hv : ContinuousOn (fun p : ℝ × (ℝ × ℝ) =>
      (p, ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))))
      (Set.Icc a b ×ˢ (Set.univ : Set ℝ) ×ˢ Set.Ioo c d) :=
    (continuous_id.prodMk continuous_const).continuousOn
  have hmap : Set.MapsTo (fun p : ℝ × (ℝ × ℝ) => (p, ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))))
      (Set.Icc a b ×ˢ (Set.univ : Set ℝ) ×ˢ Set.Ioo c d)
      ((Set.Icc a b ×ˢ (Set.univ : Set ℝ) ×ˢ Set.Ioo c d) ×ˢ Set.univ) :=
    fun p hp => ⟨hp, Set.mem_univ _⟩
  have h2 : ContinuousOn (fun p : ℝ × (ℝ × ℝ) =>
      (fderivWithin ℝ f (Set.Icc a b ×ˢ (Set.univ : Set ℝ) ×ˢ Set.Ioo c d) p)
        ((0 : ℝ), ((0 : ℝ), (1 : ℝ))))
      (Set.Icc a b ×ˢ (Set.univ : Set ℝ) ×ˢ Set.Ioo c d) := by
    have := ContinuousOn.comp
      (f := fun p : ℝ × (ℝ × ℝ) => (p, ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))))
      (s := Set.Icc a b ×ˢ (Set.univ : Set ℝ) ×ˢ Set.Ioo c d) hcont hv hmap
    simpa [Function.comp_def] using this
  refine h2.congr ?_
  intro p hp
  have hBnhds : (Set.univ : Set ℝ) ×ˢ Set.Ioo c d ∈ 𝓝 (p.2.1, p.2.2) :=
    (isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨Set.mem_univ _, hp.2.2⟩
  exact (fderivWithin_slice_deriv (A := Set.Icc a b)
    (B := (Set.univ : Set ℝ) ×ˢ Set.Ioo c d) (τ := p.1) (t := p.2.1) (ρ := p.2.2)
    hp.1 hBnhds ((hf.differentiableOn hn0) p hp)).symm

end Work.RPB.B5
