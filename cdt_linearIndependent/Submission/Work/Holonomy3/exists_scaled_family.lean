import Mathlib
import Submission.Work.Holonomy3.comp_defs
import Submission.Work.Holonomy3.scale_hasDenomType
import Submission.Work.Holonomy3.scale_polyIndependent
import Submission.Work.Holonomy3.scale_dClosed
import Submission.Work.Holonomy3.scale_pullbackMero
import Submission.Work.Holonomy3.scale_coeff_bound

/-!
# Scaling a denominator-typed, `D`-closed, independent family to normalised growth

The fine holonomy bound of `Submission.CDTPlan.HolonomyBound` is applied to a family `f₁, …, f_m`
whose Taylor coefficients obey a bound `‖coeff n (f i)‖ ≤ A ^ n` with the *constant* `A ^ 0 = 1`,
i.e. with the growth constant already normalised to `1`.  The data coming from the paper's
templates only gives `‖coeff n (f i)‖ ≤ C · A ^ n`.

Since a common scaling of the family by a nonzero rational preserves every structural property
used by the holonomy bound — the denominator type (the fixed factor `K` absorbs the scaling), the
`ℚ(x)`-independence, the `d/dx`-closedness of the span, and the meromorphy of the pullbacks — one
may simply divide the family by an integer `q ≥ C`: the constant `C` is absorbed and the growth
bound becomes `A ^ n`.

This file proves exactly that normalisation; the five preservation lemmas are proved separately
(`scale_hasDenomType`, `scale_polyIndependent`, `scale_dClosed`, `scale_pullbackMero`,
`scale_coeff_bound`).
-/

namespace Work.Holonomy3

open Submission.CDTPlan
open scoped BigOperators

/-- **Growth normalisation.**  Given a family `f` of power series over `ℚ` which is `ℚ(x)`-linearly
independent, whose span is `d/dx`-closed, all of whose members have a denominator type and whose
pullbacks by every `φ k` are meromorphic, and whose coefficients obey
`‖coeff n (f i)‖ ≤ C · A ^ n` with `A ≥ 1`, `C > 0`, there is a positive integer `q` such that the
scaled family `(q⁻¹ • f i)` enjoys all the same properties and, in addition, the normalised growth
bound `‖coeff n ((q⁻¹ • f i))‖ ≤ A ^ n`.

The scaling preserves the denominator type because the fixed integral factor `K` may absorb `q`;
it preserves independence and `d/dx`-closedness because `q⁻¹ ≠ 0`; it preserves the meromorphy of
the pullbacks because the numerator of the pullback germ is simply multiplied by the constant
`q⁻¹`.  Taking `q = ⌈C⌉₊` makes the coefficient bound hold. -/
theorem exists_scaled_family {m r' : ℕ} (b : Fin m → Fin r' → ℕ) (e : Fin m → ℕ)
    (f : Fin m → PowerSeries ℚ) {l : ℕ} (φ : Fin (l + 1) → ℂ → ℂ)
    (hden : ∀ i, Submission.CDTPlan.HasDenomType (e i) (b i) (f i))
    (hpi : Submission.CDTPlan.PolyIndependent f) (hdc : Submission.CDTPlan.DClosed f)
    (hpm : ∀ i k, Submission.CDTPlan.PullbackMero (f i) (φ k))
    (A C : ℝ) (hA : 1 ≤ A) (hC : 0 < C)
    (hgr : ∀ i n, ‖((PowerSeries.coeff n (f i) : ℚ) : ℝ)‖ ≤ C * A ^ n) :
    ∃ q : ℕ, 0 < q ∧
      (∀ i, Submission.CDTPlan.HasDenomType (e i) (b i) ((q : ℚ)⁻¹ • f i)) ∧
      Submission.CDTPlan.PolyIndependent (fun i => (q : ℚ)⁻¹ • f i) ∧
      Submission.CDTPlan.DClosed (fun i => (q : ℚ)⁻¹ • f i) ∧
      (∀ i k, Submission.CDTPlan.PullbackMero ((q : ℚ)⁻¹ • f i) (φ k)) ∧
      (∀ i n, ‖((PowerSeries.coeff n ((q : ℚ)⁻¹ • f i) : ℚ) : ℝ)‖ ≤ A ^ n) := by
  refine ⟨Nat.ceil C, Nat.ceil_pos.mpr hC, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact scale_hasDenomType (Nat.ceil C) (Nat.ceil_pos.mpr hC) (e i) (b i) (f i) (hden i)
  · exact scale_polyIndependent (Nat.ceil C) (Nat.ceil_pos.mpr hC) f hpi
  · exact scale_dClosed (Nat.ceil C) (Nat.ceil_pos.mpr hC) f hdc
  · intro i k
    exact scale_pullbackMero (Nat.ceil C) (Nat.ceil_pos.mpr hC) (f i) (φ k) (hpm i k)
  · intro i n
    exact scale_coeff_bound (Nat.ceil C) (Nat.ceil_pos.mpr hC) C A hA hC (Nat.le_ceil C)
      (f i) (hgr i) n

end Work.Holonomy3
