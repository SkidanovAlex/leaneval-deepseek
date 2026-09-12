import Submission.PaperBand.RadicalBounds

open Real
open scoped BigOperators
set_option autoImplicit false

/-!
# Lemma G: the trapezoid length relations (abstract, parameterized)

Lemma G of the paper reduces to pure real arithmetic once the geometry of
the cut-open band is in place.  This module states that reduction over the
three parameters `H, D, t` (lengths of the two boundary arcs of the
cut-open trapezoid and the horizontal displacement of the cut):

    H + D = 2a          (the two boundary arcs make up the whole boundary)
    D − 2t = H          (the parallel sides of the trapezoid)
    √(1+t²) ≤ H         (the straight cut T fits inside the arc H)
    √(5+t²) < D         (Lemma A1 via the shaded triangle of height ≥ 1)

Imply the Lemma G inequality

    2a > max (δ(t), ν(t))        with δ = √(1+t²)+√(5+t²),
                                       ν = 2√(5+t²) − 2t

whose `t` is then the witness of `lemmaG_inequality` (via
`RadicalBounds.aspect_bound`).

The side-identification of Figure 2 (which of `u,v,w,x` are the two copies
of the cut pre-bend `T` versus the arcs `H1,H2,D1,D2`) is deliberately NOT
fixed here: this theorem is parameterized over `H,D,t`, so the visual pass
only has to supply one instance of the four relations, not re-prove the
algebra.
-/

noncomputable section
namespace Submission

open Submission.PaperBand

/-- **Lemma G algebra**: any planar cut-open trapezoid configuration whose
two boundary-arc lengths `H`, `D` and cut displacement `t` satisfy the four
length relations produces the Lemma G witness `t`:
`2a > max (δ(t)) (ν(t))`. -/
theorem lemmaG_of_length_relations {a H D t : ℝ}
    (hHD : H + D = 2 * a) (hDH : D - 2 * t = H)
    (hT : Real.sqrt (1 + t ^ 2) ≤ H)
    (hB : Real.sqrt (5 + t ^ 2) < D) :
    2 * a > max (aspectDelta t) (aspectNu t) := by
  have hDsub : D - t = a := by nlinarith
  -- δ(t) = √(1+t²) + √(5+t²) < H + D = 2a
  have hδ : aspectDelta t < 2 * a := by
    unfold aspectDelta
    have hadd : Real.sqrt (1 + t ^ 2) + Real.sqrt (5 + t ^ 2) < H + D :=
      add_lt_add_of_le_of_lt hT hB
    nlinarith
  -- ν(t) = 2√(5+t²) − 2t < 2D − 2t = 2a
  have hν : aspectNu t < 2 * a := by
    unfold aspectNu
    have hB2 : 2 * Real.sqrt (5 + t ^ 2) < 2 * D :=
      mul_lt_mul_of_pos_left hB (by norm_num : (0 : ℝ) < 2)
    nlinarith
  have hmax : max (aspectDelta t) (aspectNu t) < 2 * a :=
    max_lt hδ hν
  linarith

/-- The corresponding witness form: if such `H,D,t` exist then
`lemmaG_inequality`-style conclusion holds (the `t` is explicit). -/
theorem exists_t_of_length_relations {a : ℝ} (H D t : ℝ)
    (hHD : H + D = 2 * a) (hDH : D - 2 * t = H)
    (hT : Real.sqrt (1 + t ^ 2) ≤ H)
    (hB : Real.sqrt (5 + t ^ 2) < D) :
    ∃ t : ℝ, 2 * a > max (aspectDelta t) (aspectNu t) := by
  exact ⟨t, lemmaG_of_length_relations hHD hDH hT hB⟩

/-- **Bridge for a T-bend with aspect inequalities**: if a pre-bend `T`
whose horizontal displacement is `t` (with `0 ≤ t ≤ a`) satisfies
`√(1+t²) ≤ a−t` and `√(5+t²) < a+t`, then its `t` is a witness:
`2a > max(δ(t), ν(t))`.  This is exactly the call site that Lemma T (the
T-pattern construction) must feed: take `H = a−t`, `D = a+t` (the two
boundary-arc lengths of the band between the endpoints of `T`) — the
identities `H+D=2a` and `D−2t=H` are automatic. -/
theorem lemmaG_of_aspect_inequalities {a t : ℝ} (ht0 : 0 ≤ t) (hta : t ≤ a)
    (h3 : Real.sqrt (1 + t ^ 2) ≤ a - t)
    (h4 : Real.sqrt (5 + t ^ 2) < a + t) :
    ∃ t : ℝ, 2 * a > max (aspectDelta t) (aspectNu t) := by
  have hHD : (a - t) + (a + t) = 2 * a := by ring
  have hDH : (a + t) - 2 * t = a - t := by ring
  exact ⟨t, lemmaG_of_length_relations (a := a) (H := a - t) (D := a + t)
    hHD hDH h3 h4⟩

end Submission
