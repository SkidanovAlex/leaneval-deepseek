import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1B.boxMarginDefs
import Submission.Work.BoseFixB1B.volume_iUnion_collar_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.volume_boxMargin_lt_support`

The **linear collar bound (F2)** of `Submission/Work/BoseFixB1B/boxMarginDefs.lean`: the Lebesgue
volume of the set of points of the support of the sliding window `χ_{B(u)}` whose box margin
`boxMargin ℓ d u` is `< δ` is `O(δ)`.

Together with the companion (F1) fact `Work.BoseFixB1B.chiB_abs_le_boxMargin` this is what makes
the `L²`/`H¹` distance between the windowed sharp fibre `1_{B(u)^{|S|}}·ψ` on the one hand and its
smooth approximation `γ_δ^{|S|}·ψ` (with `γ_δ` a cutoff equal to `1` on `{boxMargin ≥ δ}` and
supported in `dlBox`) on the other hand vanish as `δ → 0`: the gradient of `γ_δ` contributes
`∫ χ²|∇γ_δ|² ≤ (C'/δ²)·C²δ²·(Cδ) = O(δ)`.

## The argument

`boxMargin ℓ d u x` is the minimum of the six coordinate margins
`ℓ/2 - |x_m|` (`m : Fin 3`) and `ℓd/2 - |(x - (ℓd)•u)_m|`.  Hence

* `boxMargin ℓ d u x < δ` implies that one of the six margins is `< δ`
  (`min_lt_iff` + `Finset.inf'_lt_iff`, `cover_step` below), and
* `Function.support (chiB ℓ d u) ⊆ dlBox ℓ d u`
  (`Submission.BoseGases.chiB_support_mem`), i.e. `x ∈ acube ℓ` and
  `x - (ℓd)•u ∈ acube (ℓd)`.

So the set of interest is contained in the union, over `i : Fin 3`, of the two collars
`{x | ∀ m, |x_m| ≤ ℓ/2} ∩ {ℓ/2 - |x_i| < δ}` and
`{x | ∀ m, |(x - (ℓd)•u)_m| ≤ ℓd/2} ∩ {ℓd/2 - |(x - (ℓd)•u)_i| < δ}`,

each of which has volume `≤ ENNReal.ofReal (8 c² δ)` (`c` the half-side of the enclosing cube):
the union over the three coordinates is bounded by
`Work.BoseFixB1B.volume_iUnion_collar_le`, giving `24 c² δ` for the cube of half-side `c`.
Summing the two cubes (`c = ℓ/2` and `c = ℓd/2`) gives
`24 (ℓ/2)² δ + 24 (ℓd/2)² δ = 6 ℓ²(1 + d²) δ`, so `C = 6 ℓ²(1 + d²)` works.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

namespace Work.BoseFixB1B

set_option autoImplicit false

/-- **Geometry.**  A point of the support of `chiB` whose box margin is `< δ` lies within
distance `δ` of one of the faces of one of the two cubes defining the sliding box: either some
coordinate margin `ℓ/2 - |x i|` is `< δ`, or some translated coordinate margin
`ℓd/2 - |(x - (ℓd)•u) i|` is. -/
private lemma cover_step {ℓ d δ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (u x : ℝ³)
    (hx : x ∈ Function.support (Submission.BoseGases.chiB ℓ d u))
    (hm : boxMargin ℓ d u x < δ) :
    (∃ i : Fin 3, (∀ m : Fin 3, |x m| ≤ ℓ / 2) ∧ ℓ / 2 - |x i| < δ)
      ∨ (∃ i : Fin 3, (∀ m : Fin 3, |(x - (ℓ * d) • u) m| ≤ ℓ * d / 2)
          ∧ ℓ * d / 2 - |(x - (ℓ * d) • u) i| < δ) := by
  have hneq : Submission.BoseGases.chiB ℓ d u x ≠ 0 := Function.mem_support.mp hx
  have hbox : x ∈ Submission.BoseGases.dlBox ℓ d u :=
    Submission.BoseGases.chiB_support_mem hℓ hd u x hneq
  have hbox' : x ∈ Submission.BoseGases.acube ℓ
      ∧ x - (ℓ * d) • u ∈ Submission.BoseGases.acube (ℓ * d) := hbox
  obtain ⟨h1, h2⟩ := hbox'
  rw [Submission.BoseGases.mem_acube_iff] at h1 h2
  rw [boxMargin] at hm
  rcases min_lt_iff.mp hm with hA | hB
  · rcases (Finset.inf'_lt_iff Finset.univ_nonempty).mp hA with ⟨i, -, hi⟩
    exact Or.inl ⟨i, fun m => abs_le.mpr ⟨by linarith [(h1 m).1], by linarith [(h1 m).2]⟩, hi⟩
  · rcases (Finset.inf'_lt_iff Finset.univ_nonempty).mp hB with ⟨i, -, hi⟩
    exact Or.inr ⟨i, fun m => abs_le.mpr ⟨by linarith [(h2 m).1], by linarith [(h2 m).2]⟩, hi⟩

/-- **The linear collar bound (F2).**  For `ℓ, d > 0` and every `u` the volume of the part of the
support of the sliding window `χ_{B(u)}` on which the box margin is `< δ` is at most
`C·δ` with `C = 6 ℓ² (1 + d²)`. -/
theorem volume_boxMargin_lt_support {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ →
      MeasureTheory.volume ({x : EuclideanSpace ℝ (Fin 3) | Work.BoseFixB1B.boxMargin ℓ d u x < δ}
          ∩ Function.support (Submission.BoseGases.chiB ℓ d u))
        ≤ ENNReal.ofReal (C * δ) := by
  refine ⟨6 * ℓ ^ 2 * (1 + d ^ 2), by positivity, ?_⟩
  intro δ hδ
  set S1 : Set ℝ³ := ⋃ i : Fin 3,
    {x : ℝ³ | (∀ m : Fin 3, |x m| ≤ ℓ / 2) ∧ ℓ / 2 - |x i| < δ} with hS1
  set S2 : Set ℝ³ := ⋃ i : Fin 3,
    {x : ℝ³ | (∀ m : Fin 3, |(x - (ℓ * d) • u) m| ≤ ℓ * d / 2)
      ∧ ℓ * d / 2 - |(x - (ℓ * d) • u) i| < δ} with hS2
  have hcover : {x : ℝ³ | boxMargin ℓ d u x < δ}
      ∩ Function.support (Submission.BoseGases.chiB ℓ d u) ⊆ S1 ∪ S2 := by
    intro x hx
    obtain ⟨hm, hs⟩ := hx
    rcases cover_step hℓ hd u x hs hm with ⟨i, h1, h2⟩ | ⟨i, h1, h2⟩
    · exact Or.inl (Set.mem_iUnion.mpr ⟨i, h1, h2⟩)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨i, h1, h2⟩)
  calc MeasureTheory.volume ({x : ℝ³ | boxMargin ℓ d u x < δ}
        ∩ Function.support (Submission.BoseGases.chiB ℓ d u))
      ≤ MeasureTheory.volume (S1 ∪ S2) := measure_mono hcover
    _ ≤ MeasureTheory.volume S1 + MeasureTheory.volume S2 := measure_union_le _ _
    _ ≤ ENNReal.ofReal (24 * (ℓ / 2) ^ 2 * δ)
          + ENNReal.ofReal (24 * (ℓ * d / 2) ^ 2 * δ) := by
        refine add_le_add ?_ ?_
        · rw [hS1]
          simpa using volume_iUnion_collar_le (c := ℓ / 2) (δ := δ) (by positivity) hδ (0 : ℝ³)
        · rw [hS2]
          simpa using volume_iUnion_collar_le (c := ℓ * d / 2) (δ := δ) (by positivity) hδ
            ((ℓ * d) • u)
    _ = ENNReal.ofReal (6 * ℓ ^ 2 * (1 + d ^ 2) * δ) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

end Work.BoseFixB1B
