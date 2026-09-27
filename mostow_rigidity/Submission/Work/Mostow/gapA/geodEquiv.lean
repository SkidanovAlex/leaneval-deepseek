import Mathlib
import Submission.Work.Mostow.gapA.defs
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.bdInnerMul

/-!
# Equivariance of the geodesic data under an isometry

For `a, b ∈ Sph n` and `g : PO n 1`, both the distance to the geodesic `geodSet a b` and the
geodesic itself are transported by `g`:

* `distGeod (bd g a) (bd g b) (g • u) = distGeod a b u`;
* `u ∈ geodSet a b ↔ g • u ∈ geodSet (bd g a) (bd g b)`.

Both are immediate consequences of the Busemann cocycle

  `β_{bd g a} (g • u) = β_a u + bCocy g a`

and of the conformal factor identity `bdInnerMul`

  `1 - ⟪bd g a, bd g b⟫ = (1 - ⟪a,b⟫) * exp (bCocy g a + bCocy g b)`:

the exponential of the level `exp (β_a u + β_b u)` and the normalising constant `1 - ⟪a,b⟫`
are scaled by the *same* factor, so all the ratios defining `geodSet` and `distGeod` are
unchanged.
-/

namespace Work.Mostow.gapA

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

/-- Multiplying numerator and denominator by the same non-zero constant does not change a
ratio of the form `2 X / D`. -/
private lemma two_mul_mul_div_mul (X D K : ℝ) (hK : K ≠ 0) :
    2 * (X * K) / (D * K) = 2 * X / D := by
  rw [mul_comm D K, ← div_div, mul_div_assoc, mul_div_cancel_right₀ X hK]

/-- Multiplying numerator and denominator of an equation `X = c/2` by the same non-zero
constant does not change it. -/
private lemma mul_div_two_iff (X c K : ℝ) (hK : K ≠ 0) :
    (X = c / 2) ↔ (X * K = c * K / 2) := by
  have h2 : c * K / 2 = (c / 2) * K := by ring
  rw [h2]
  exact ⟨fun h => by rw [h], fun h => mul_right_cancel₀ hK h⟩

theorem geodEquiv (n : ℕ) (hn : 2 ≤ n) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n)
    (a b : Submission.Mostow.E n) (ha : a ∈ Submission.Mostow.Sph n)
    (hb : b ∈ Submission.Mostow.Sph n) (g : LeanEval.Geometry.MostowRigidity.PO n 1) :
    (∀ u : Submission.Mostow.E n,
      Work.Mostow.distGeod (Submission.Mostow.bd g a) (Submission.Mostow.bd g b) (g • u)
        = Work.Mostow.distGeod a b u) ∧
    (∀ u : Submission.Mostow.E n,
      u ∈ Work.Mostow.geodSet a b
        ↔ g • u ∈ Work.Mostow.geodSet (Submission.Mostow.bd g a) (Submission.Mostow.bd g b)) := by
  have hQ : HypIsoData n := HypIsoData.ofProp hI
  -- the conformal factor `exp (bCocy g a + bCocy g b)`, non-zero
  have hKne : Real.exp (Work.Mostow.bCocy g a + Work.Mostow.bCocy g b) ≠ 0 :=
    ne_of_gt (Real.exp_pos _)
  -- the level `exp (β_{bd g a} (g•u) + β_{bd g b} (g•u))` is the level at `u` times the factor
  have hExp_sum : ∀ u : E n,
      Real.exp (busemann (bd g a) (g • u) + busemann (bd g b) (g • u))
        = Real.exp (busemann a u + busemann b u)
            * Real.exp (Work.Mostow.bCocy g a + Work.Mostow.bCocy g b) := by
    intro u
    simp only [Work.Mostow.bCocy]
    rw [hQ.busemann_cocycle g a u ha, hQ.busemann_cocycle g b u hb,
      show (busemann a u + busemann (bd g a) (g • 0)) + (busemann b u + busemann (bd g b) (g • 0))
          = (busemann a u + busemann b u)
              + (busemann (bd g a) (g • 0) + busemann (bd g b) (g • 0)) from by ring,
      Real.exp_add]
  -- the normalising constant scales by the same factor
  have hD : 1 - inner ℝ (bd g a) (bd g b)
      = (1 - inner ℝ a b) * Real.exp (Work.Mostow.bCocy g a + Work.Mostow.bCocy g b) :=
    Work.Mostow.bdInnerMul n hA hI g ha hb
  constructor
  · intro u
    have harg : 2 * Real.exp (busemann (bd g a) (g • u) + busemann (bd g b) (g • u))
          / (1 - inner ℝ (bd g a) (bd g b))
        = 2 * Real.exp (busemann a u + busemann b u) / (1 - inner ℝ a b) := by
      rw [hExp_sum u, hD]
      exact two_mul_mul_div_mul _ _ _ hKne
    simp only [Work.Mostow.distGeod]
    exact congrArg (fun t : ℝ => Real.arcosh (Real.sqrt t)) harg
  · intro u
    simp only [Work.Mostow.geodSet, Set.mem_setOf_eq]
    rw [hExp_sum u, hD]
    exact mul_div_two_iff _ _ _ hKne

end

end Work.Mostow.gapA
