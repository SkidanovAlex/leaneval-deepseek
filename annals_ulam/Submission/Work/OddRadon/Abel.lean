import Submission.Work.OddRadon.Core

/-!
# The Abel-type transforms of the odd-dimensional Radon inversion (`Work.OddRadon`, part 3)

For odd `d = 2n+1` (`n ≥ 1`) the one-variable Radon transform of an even profile `γ` is, up to
an explicit power of `c` and a constant,

  `T_α γ (c) = ∫_0^c γ s (c² - s²)^α ds`,  `α = (d-4)/2 = n - 3/2`,

and the inversion is: reduce the exponent down to `α = -1/2` (the classical Abel transform) by
the recursion `T_α' = 2α c T_{α-1}`, then apply the classical Abel inversion.

## Main definitions

* `abelTrans α G c = ∫_0^c G s (c² - s²)^α ds` — the forward transform;
* `abelReduce α F c = deriv F c / (2 α c)` — one exponent-reduction step `F_α ↦ F_{α-1}`;
* `abelReduceIter α k F` — `k` iterated reductions (exponents `α, α-1, …, α-k+1`);
* `abelInvert Φ u = (2/π) d/du ∫_0^u c Φ c / √(u²-c²) dc` — the classical Abel inversion;
* `abelInverseData n Ψ = abelInvert (abelReduceIter (n-3/2) (n-1) Ψ)` — the full inversion;
* `radonInverse n F u` — the inverse of `radonProfile (2n+1)` at the data level.
-/

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace Pointwise Interval Topology

namespace Work.OddRadon

/-- **The forward Abel-type transform** `T_α G c = ∫_0^c G s (c² - s²)^α ds`. -/
def abelTrans (α : ℝ) (G : ℝ → ℝ) (c : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..c, G s * (c ^ 2 - s ^ 2) ^ α

/-- **One exponent-reduction step**: if `F = T_α G` then `abelReduce α F = T_{α-1} G`
(the recursion `T_α' = 2 α c T_{α-1}`). -/
def abelReduce (α : ℝ) (F : ℝ → ℝ) : ℝ → ℝ := fun c => deriv F c / (2 * α * c)

/-- **`k` iterated exponent-reduction steps**, using the exponents `α, α-1, …, α-k+1`
(the result is at exponent `α - k`). -/
def abelReduceIter (α : ℝ) : ℕ → (ℝ → ℝ) → (ℝ → ℝ)
  | 0, F => F
  | (k + 1), F => abelReduceIter (α - 1) k (abelReduce α F)

/-- **The classical Abel inversion** `Φ ↦ (2/π) d/du ∫_0^u c Φ c / √(u² - c²) dc`, the inverse
of `abelTrans (-1/2)`. -/
def abelInvert (Φ : ℝ → ℝ) (u : ℝ) : ℝ :=
  (2 / Real.pi) * deriv (fun u : ℝ => ∫ c in (0 : ℝ)..u, c * Φ c / Real.sqrt (u ^ 2 - c ^ 2)) u

/-- **The inverse of the odd-dimensional Abel datum**: from `Ψ = T_{n-3/2} γ` recover `γ`. -/
def abelInverseData (n : ℕ) (Ψ : ℝ → ℝ) (u : ℝ) : ℝ :=
  abelInvert (abelReduceIter ((n : ℝ) - 3 / 2) (n - 1) Ψ) u

/-- **The inverse of the `(2n+1)`-dimensional spherical Radon profile transform**, at the level
of the data function `F = radonProfile (2n+1) γ`:
`radonInverse n F u = γ u` (`radonProfile_inv`).

It first multiplies the data by `(2 |S^{2n-2}|)⁻¹ c^{2n-2}`, which is exactly the Abel datum
`T_{n-3/2} γ` (`radonProfile_eq_abelTrans`), and then runs the inversion of `abelInverseData`. -/
def radonInverse (n : ℕ) (F : ℝ → ℝ) (u : ℝ) : ℝ :=
  abelInvert (abelReduceIter ((n : ℝ) - 3 / 2) (n - 1)
    (fun c => (2 * sphereArea (2 * n - 2))⁻¹ * c ^ (2 * n - 2) * F c)) u

@[simp] lemma abelTrans_zero (α : ℝ) (G : ℝ → ℝ) : abelTrans α G 0 = 0 := by
  simp [abelTrans]

@[simp] lemma abelReduceIter_zero (α : ℝ) (F : ℝ → ℝ) : abelReduceIter α 0 F = F := rfl

lemma abelReduceIter_succ (α : ℝ) (k : ℕ) (F : ℝ → ℝ) :
    abelReduceIter α (k + 1) F = abelReduceIter (α - 1) k (abelReduce α F) := rfl

lemma abelReduce_const_mul (α C : ℝ) (F : ℝ → ℝ) :
    abelReduce α (fun c => C * F c) = fun c => C * abelReduce α F c := by
  funext c
  simp only [abelReduce, deriv_const_mul_field]
  ring

end Work.OddRadon
