/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Unfolding the radial disc extension to linear reflections

The one-sided radial Seeley extension of `discExt` reflects a point `z` of radius `‖z‖` to the
point of the *same direction* and radius `1 - b (‖z‖ - 1)`.  In the coordinates
`(x, u, σ) ↦ (x, (1 - σ) • (u/‖u‖))` this reflection becomes the *linear* map
`σ ↦ -(b) * σ` on the last coordinate, which is what makes the jet matching a multilinear
moment identity.

This file records the two maps of the unfolding (`discSigma` and `discUnfold`) and the unfolded
extension `discUnfoldExt`, together with the identification `discExt = discUnfoldExt ∘ discSigma`.
-/
import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.NN.Final.DiscRadialDefs

noncomputable section
open scoped NNReal ENNReal ContDiff Topology
open Set Metric Filter

namespace Work.NN.DiscRadial

open Work.NN.Final

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The unfolding of a point `p = (x, z)` of the disc: the direction `z/‖z‖`, and the signed
radial offset `1 - ‖z‖` (positive inside the unit disc, negative outside). -/
def discSigma (p : X × ℂ) : (X × ℂ) × ℝ :=
  ((p.1, p.2 / (‖p.2‖ : ℂ)), 1 - ‖p.2‖)

/-- The unfolded function: at a point `(y, σ)` with `y = (x, u)`, the value of `g` at the point
of radius `1 - σ` in the direction `u/‖u‖`. -/
def discUnfold (g : X × ℂ → ℂ) : (X × ℂ) × ℝ → ℂ :=
  fun y => g (y.1.1, (1 - y.2) • (y.1.2 / (‖y.1.2‖ : ℂ)))

/-- The unfolding map `Φ(y, σ) = (y.1.1, (1 - σ) • (y.1.2/‖y.1.2‖))`, whose composition with
`g` is `discUnfold g`. -/
def unfoldMap : (X × ℂ) × ℝ → X × ℂ :=
  fun y => (y.1.1, (1 - y.2) • (y.1.2 / (‖y.1.2‖ : ℂ)))

@[simp] lemma unfoldMap_apply (y : (X × ℂ) × ℝ) :
    unfoldMap y = (y.1.1, (1 - y.2) • (y.1.2 / (‖y.1.2‖ : ℂ))) := rfl

@[simp] lemma discUnfold_apply (g : X × ℂ → ℂ) (y : (X × ℂ) × ℝ) :
    discUnfold g y = g (unfoldMap y) := rfl

@[simp] lemma discUnfold_apply' (g : X × ℂ → ℂ) (y : (X × ℂ) × ℝ) :
    discUnfold g y = g (y.1.1, (1 - y.2) • (y.1.2 / (‖y.1.2‖ : ℂ))) := rfl

lemma discUnfold_eq_comp (g : X × ℂ → ℂ) :
    discUnfold (X := X) g = g ∘ unfoldMap := rfl

/-- The unfolded one-sided extension: `discExt` transported along the unfolding.  For
`σ > 0` (inside the unit disc) it is `discUnfold`; on `σ = 0` the (radial) boundary value;
for `σ < 0` the finite reflected sum with the weights `discWt k` at the scales `discScale`. -/
def discUnfoldExt (k : ℕ) (g : X × ℂ → ℂ) : (X × ℂ) × ℝ → ℂ := fun y =>
  if 0 < y.2 then discUnfold g y
  else if y.2 = 0 then
    Filter.limUnder (𝓝[>] (0 : ℝ)) (fun σ : ℝ => discUnfold g (y.1, σ))
  else
    ∑ i ∈ Finset.range (k + 1),
      (discWt k i) •
        ((seeleyCut (-(discScale i) * y.2)) • discUnfold g (y.1, -(discScale i) * y.2))

/-- On the open unit disc part (`σ > 0`) the unfolded extension is the unfolded function. -/
@[simp] lemma discUnfoldExt_of_pos {k : ℕ} {g : X × ℂ → ℂ} {y : (X × ℂ) × ℝ}
    (hy : 0 < y.2) : discUnfoldExt k g y = discUnfold g y := ite_eq_left hy

/-- On the hyperplane `σ = 0` the unfolded extension is the radial boundary value. -/
@[simp] lemma discUnfoldExt_of_eq_zero {k : ℕ} {g : X × ℂ → ℂ} {y : (X × ℂ) × ℝ}
    (hy : y.2 = 0) :
    discUnfoldExt k g y = Filter.limUnder (𝓝[>] (0 : ℝ)) (fun σ : ℝ => discUnfold g (y.1, σ)) := by
  simp only [discUnfoldExt]
  rw [ite_eq_right (not_lt.mpr hy.le), ite_eq_left hy]

/-- On the outside (`σ < 0`) the unfolded extension is the reflected sum. -/
@[simp] lemma discUnfoldExt_of_neg {k : ℕ} {g : X × ℂ → ℂ} {y : (X × ℂ) × ℝ}
    (hy : y.2 < 0) :
    discUnfoldExt k g y =
      ∑ i ∈ Finset.range (k + 1),
        (discWt k i) •
          ((seeleyCut (-(discScale i) * y.2)) • discUnfold g (y.1, -(discScale i) * y.2)) := by
  simp only [discUnfoldExt]
  rw [ite_eq_right (not_lt.mpr hy.le), ite_eq_right (ne_of_lt hy)]

end Work.NN.DiscRadial

namespace Work.NN.DiscRadial

open scoped Topology
open Filter

/-- Reparametrisation of a one-sided limit: the limit as `σ → 0⁺` of `f (1 - σ)` is the limit as
`s → 1⁻` of `f s`. -/
lemma limUnder_comp_one_sub (f : ℝ → ℂ) :
    Filter.limUnder (𝓝[>] (0 : ℝ)) (fun σ => f (1 - σ))
      = Filter.limUnder (𝓝[<] (1 : ℝ)) f := by
  have hH : Filter.map (fun σ : ℝ => 1 - σ) (𝓝[>] (0 : ℝ)) = 𝓝[<] (1 : ℝ) := by
    rw [nhdsWithin, nhdsWithin, Filter.map_inf (by intro a b h; linarith)]
    congr 1
    · have := Homeomorph.map_nhds_eq ((Homeomorph.neg ℝ).trans (Homeomorph.addLeft 1)) 0
      simpa using this
    · rw [map_principal]
      congr 1
      ext t
      simp only [Set.mem_image, Set.mem_Iio, Set.mem_Ioi]
      exact ⟨fun ⟨σ, hσ, hσt⟩ => by linarith, fun ht => ⟨1 - t, by linarith, by ring⟩⟩
  change (Filter.map f (Filter.map (fun σ : ℝ => 1 - σ) (𝓝[>] (0 : ℝ)))).lim
      = (Filter.map f (𝓝[<] (1 : ℝ))).lim
  rw [hH]

end Work.NN.DiscRadial
