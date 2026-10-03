import Mathlib
import Submission.Work.KMTAreas.A7.LargeInterface

namespace Work.KMTAreas.A7Hi

open MeasureTheory
open scoped ENNReal NNReal BigOperators

/-! ## The two definitional pieces of the variational norm -/

/-- The values supremum `⨆ n, ‖a n‖ₑ` of the variational norm. -/
noncomputable def supPart (r : NNReal) (a : ℕ → ℂ) : ℝ≥0∞ := ⨆ n : ℕ, ‖a n‖ₑ

/-- The chain term of the variational norm (supremum over monotone chains of the `ℓ^r`-norm of the
jumps). -/
noncomputable def chainPart (r : NNReal) (a : ℕ → ℂ) : ℝ≥0∞ :=
  ⨆ (J : ℕ) (N : ℕ → ℕ) (_ : Monotone N),
    ENNReal.ofReal ‖(WithLp.toLp r (fun (i : Fin J) ↦ a (N (i + 1)) - a (N i)))‖

lemma variationalNorm_eq_parts (r : NNReal) (a : ℕ → ℂ) :
    PointwiseErgodicTheorems.variationalNorm r a = supPart r a + chainPart r a := rfl

/-- The low-pass family of the estimate: `T_m = kmtProj ρ l₁ (-(m₀ + m))`. -/
noncomputable def lpf (ρ : ℝ) (l₁ m₀ m : ℕ) (f : ℤ → ℂ) : ℤ → ℂ :=
  Work.KMTContract.kmtProj ρ l₁ (-((m₀ : ℤ) + (m : ℤ))) f

/-- The family of *increments* `T_{m+1} - T_m` at the point `x`. -/
noncomputable def incFam (ρ : ℝ) (l₁ m₀ : ℕ) (f : ℤ → ℂ) (x : ℤ) : ℕ → ℂ :=
  fun m => lpf ρ l₁ m₀ (m + 1) f x - lpf ρ l₁ m₀ m f x

/-- The band-pass **square function** of the increments of the low-pass family at the point `x`:
`(∑'_m ‖Δ_m f x‖²)^{1/2}`, `Δ_m f = T_{m+1} f - T_m f`.  This is the real-variable quantity
that controls the chain term of the variational norm (`LowpassChainLe`); it is *not* replaceable by
the variational norm of the increments (see `NOTES_LowpassVarDyadic_chain_inequality_FALSE.md`). -/
noncomputable def sqFun (ρ : ℝ) (l₁ m₀ : ℕ) (f : ℤ → ℂ) (x : ℤ) : ℝ≥0∞ :=
  (∑' m : ℕ, ‖lpf ρ l₁ m₀ (m + 1) f x - lpf ρ l₁ m₀ m f x‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)

/-! ## Elementary helpers -/

/-- The good-major-arcs predicate is *monotone decreasing* in the constant `Cρ`:
`C₁ ≤ C₂` makes the hypothesis `GoodMajorArcs ρ C₂ l k` stronger. -/
lemma goodMajorArcs_mono {ρ C₁ C₂ : ℝ} {l : ℕ} {k : ℤ} (h : C₁ ≤ C₂)
    (hk : Work.Analysis.IonescuWainger.GoodMajorArcs ρ C₂ l k) :
    Work.Analysis.IonescuWainger.GoodMajorArcs ρ C₁ l k := by
  unfold Work.Analysis.IonescuWainger.GoodMajorArcs at *
  have h2 : (0:ℝ) < (2:ℝ) ^ (ρ * (l:ℝ)) := by positivity
  nlinarith [hk, h, h2]

/-- `ofReal a * A + ofReal b * A = ofReal (a + b) * A`. -/
lemma ofReal_mul_add_eq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (A : ℝ≥0∞) :
    ENNReal.ofReal a * A + ENNReal.ofReal b * A = ENNReal.ofReal (a + b) * A := by
  rw [← add_mul, ← ENNReal.ofReal_add ha hb]

/-- `ofReal a * (ofReal b * A) = ofReal (a * b) * A`. -/
lemma ofReal_mul_mul_eq {a b : ℝ} (ha : 0 ≤ a) (_hb : 0 ≤ b) (A : ℝ≥0∞) :
    ENNReal.ofReal a * (ENNReal.ofReal b * A) = ENNReal.ofReal (a * b) * A := by
  rw [← mul_assoc, ← ENNReal.ofReal_mul ha]

end Work.KMTAreas.A7Hi
