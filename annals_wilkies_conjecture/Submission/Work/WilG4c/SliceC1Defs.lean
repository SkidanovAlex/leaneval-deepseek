/-
  WilG4c / `SliceC1Defs` — the (multi-variable) fibre `C¹` predicate of a family.

  ## Why this file exists

  `SliceLocus p n f 1` is the set of `w : ℝ^{p+(n+1)}` such that the *slice*
  `y ↦ f (parPt w) y` of the family `f` is `C¹` (Fréchet, in all `n+1` cube variables) at
  the cube point `cubePt w`.  The point of the vocabulary here is that this condition is a
  **first-order formula over the graph of the family**: `C¹` at `u` means "on a ball around
  `u` the function has Fréchet derivatives and they depend continuously on the point", and
  the Fréchet derivative itself is characterised by the `ε`-`δ` estimate

    `‖g y' - g y - φ (y' - y)‖ ≤ ε ‖y' - y‖`,

  a first-order condition whose only non-logical symbols are the graph relation of `f` and
  the field operations of `ℝ`.  The quantifiers over the linear maps `φ` are eliminated by
  representing `φ` by its coefficient vector `c j = φ (Pi.single j 1)` (then
  `φ = linMap c`), and the *norms* are replaced by the equivalent (over `∀ε > 0 ∃δ > 0`)
  `ℓ²`-conditions `∑ j (…)² < δ²`, which are *polynomial* inequalities of degree `2`.

  The two predicates below are exactly the formula that the `Ω`-encoding in
  `SliceC1Shape` realises, and the equivalence with Mathlib's `ContDiffAt ℝ 1` is
  `c1Pred_iff_contDiffAt` (in the sibling module `SliceC1Real`).

  Everything in this file is a definition or a trivial unfolding; it is `sorry`-free.
-/
import Mathlib

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

/-! ## 1. Linear functionals as coefficient vectors -/

/-- The linear functional `v ↦ ∑ j, c j * v j` encoded by the coefficient vector `c`.
(Every element of `(Fin M → ℝ) →L[ℝ] ℝ` is of this form, with `c j = φ (Pi.single j 1)`.) -/
def linMap {M : ℕ} (c : Fin M → ℝ) : (Fin M → ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun v => ∑ j, c j * v j
      map_add' := by
        intro v w
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro a v
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring }
    (∑ j, |c j|)
    (by
      intro v
      rw [Real.norm_eq_abs]
      calc |∑ j, c j * v j| ≤ ∑ j, |c j * v j| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ j, |c j| * |v j| := by
            exact Finset.sum_congr rfl fun j _ => by rw [abs_mul]
        _ ≤ ∑ j, |c j| * ‖v‖ := by
            refine Finset.sum_le_sum fun j _ => ?_
            exact mul_le_mul_of_nonneg_left (by
              simpa only [Real.norm_eq_abs] using norm_le_pi_norm v j) (abs_nonneg _)
        _ = (∑ j, |c j|) * ‖v‖ := by rw [Finset.sum_mul])

@[simp] theorem linMap_apply {M : ℕ} (c v : Fin M → ℝ) :
    linMap c v = ∑ j, c j * v j := rfl

/-- The coefficient vector of a linear functional. -/
def linCoeff {M : ℕ} (φ : (Fin M → ℝ) →L[ℝ] ℝ) : Fin M → ℝ := fun j => φ (Pi.single j 1)

/-- A linear functional is recovered from its coefficient vector. -/
theorem linMap_linCoeff {M : ℕ} (φ : (Fin M → ℝ) →L[ℝ] ℝ) : linMap (linCoeff φ) = φ := by
  ext v
  have hv : (∑ j, v j • (Pi.single j (1 : ℝ))) = v := by
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne, hb]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  calc linMap (linCoeff φ) v = ∑ j, φ (Pi.single j 1) * v j := by
        simp only [linMap_apply, linCoeff]
    _ = ∑ j, v j * φ (Pi.single j 1) :=
        Finset.sum_congr rfl fun j _ => by ring
    _ = ∑ j, v j • φ (Pi.single j 1) := by simp
    _ = ∑ j, φ (v j • Pi.single j (1 : ℝ)) := by simp
    _ = φ (∑ j, v j • Pi.single j (1 : ℝ)) := by rw [map_sum]
    _ = φ v := by rw [hv]

/-! ## 2. The pointwise `ε`-`δ` Fréchet-derivative predicate -/

/-- **The `ε`-`δ` characterisation of `HasFDerivAt g (linMap c) y`, with `ℓ²` balls.**

For `ε > 0` the conditions `‖y' - y‖ < δ` and `(∑ j, (y' j - y j)²) < δ²` (with Mathlib's
sup norm on `Fin M → ℝ`) and `|A| ≤ ε ‖y' - y‖` and `A² ≤ ε² ∑ j, (y' j - y j)²` define the
same filters in `δ` and `ε`, so this is equivalent to `HasFDerivAt g (linMap c) y`
(`hasFDerivEps_iff_hasFDerivAt` in `SliceC1Real`). -/
def HasFDerivEps {M : ℕ} (g : (Fin M → ℝ) → ℝ) (y c : Fin M → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ y' : Fin M → ℝ, (∑ j, (y' j - y j) ^ 2) < δ ^ 2 →
      (g y' - g y - ∑ j, c j * (y' j - y j)) ^ 2 ≤
        ε ^ 2 * ∑ j, (y' j - y j) ^ 2

/-! ## 3. The localised `C¹` predicate -/

/-- **The fibre `C¹` predicate.**  On a ball around `u` every point carries a Fréchet
derivative (`HasFDerivEps`), and the derivative depends continuously on the point (the
final `∃ c'` clause).  This is equivalent to Mathlib's `ContDiffAt ℝ 1 g u`
(`c1Pred_iff_contDiffAt` in `SliceC1Real`). -/
def C1Pred {M : ℕ} (g : (Fin M → ℝ) → ℝ) (u : Fin M → ℝ) : Prop :=
  ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ y : Fin M → ℝ, (∑ j, (y j - u j) ^ 2) < δ₀ ^ 2 →
    ∃ c : Fin M → ℝ, HasFDerivEps g y c ∧
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ y' : Fin M → ℝ, (∑ j, (y' j - y j) ^ 2) < δ ^ 2 →
          ∃ c' : Fin M → ℝ, HasFDerivEps g y' c' ∧ (∑ j, (c' j - c j) ^ 2) < ε ^ 2

end Work.WilG4c
