import Mathlib
import Submission.Work.Drive.Generic.angVelNum_pos_of_chordConcave

/-!
# The angular-velocity numerator of the needle's chart: the zone lemmas

Lane H2 (`Work.Drive.unknotted_of_avoidingArc`), the per-loop margin pin
(`Work.Drive.ChartLoopMargin`).

The chart of the needle fixes a unit "chord" direction `v` and a unit "up" direction `e` (the
normalised `Work.Drive.chartUp`, perpendicular to `v`).  For a curve `p` of `Space`, a centre `c` and
a tangent vector `T`, the *angular-velocity numerator in the chart frame* is

    E(p, T) := ⟪p - c, e⟫ * ⟪T, v⟫ - ⟪p - c, v⟫ * ⟪T, e⟫ .

The loop is a straight *chord*, a straight *leg* (chamfer) and the *arc*; the three zones give three
independent lemmas.

* **`Work.Drive.H2.angNum_segment`** — on a straight piece `p s = A + s • (B - A)` travelled with the
  constant velocity `λ • (B - A)`, the numerator is *constant* in `s`: the `s`-term cancels because
  the position increment and the velocity are parallel.  This covers both the chord zone and the two
  chamfer zones, and reduces their positivity to the *sign of the signed area* of the triangle
  `(c, A, B)`.
* **`Work.Drive.H2.angNum_arc_zero`** — on the arc zone, in the chart `(X, H)` **measured from the
  centre** (`X := ⟪p - c, v⟫`, `H := ⟪p - c, e⟫`), the numerator is `H X' - X H'`, and it is positive
  as soon as the arc's chart profile is concave in the chart coordinate, the chart coordinate is
  strictly increasing, and the centre lies strictly below the arc's chart graph at the chart
  coordinate of the centre (this is `Work.Drive.Generic.angVelNum_pos_of_chordConcave` with the
  centre at the origin).
* **`Work.Drive.H2.angNum_eq_chart`** — the bridge: if `X` and `H` are the chart coordinates of a
  curve and `T` is its velocity, then `E(p, T) = H * X' - X * H'`.
-/

noncomputable section
namespace Work.Drive.H2

open scoped Real Topology
open Work.Drive.Generic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## 1. The numerator on a straight piece -/

/-- **The angular-velocity numerator is constant on a straight piece.**  For a segment
`p s = A + s • (B - A)` travelled with the velocity `λ • (B - A)`, the numerator
`⟪p - c, e⟫ * ⟪T, v⟫ - ⟪p - c, v⟫ * ⟪T, e⟫` does not depend on `s` and equals `λ` times the
"oriented area" `⟪A - c, e⟫ * ⟪B - A, v⟫ - ⟪A - c, v⟫ * ⟪B - A, e⟫`. -/
theorem angNum_segment {v e A B c : E} {c₀ s : ℝ} :
    inner ℝ (A + s • (B - A) - c) e * inner ℝ (c₀ • (B - A)) v
      - inner ℝ (A + s • (B - A) - c) v * inner ℝ (c₀ • (B - A)) e
    = c₀ * (inner ℝ (A - c) e * inner ℝ (B - A) v
        - inner ℝ (A - c) v * inner ℝ (B - A) e) := by
  have h1 : A + s • (B - A) - c = (A - c) + s • (B - A) := by abel
  rw [h1]
  simp only [inner_add_left, real_inner_smul_left, real_inner_smul_right]
  ring

/-- **The numerator on a straight piece, with a nonnegative factor.**  In the applications the
velocity of the chord/leg zone is `λ • (B - A)` with `λ > 0`, so the sign of the numerator is the
sign of the oriented area. -/
theorem angNum_segment_pos {v e A B c : E} {c₀ s : ℝ} (hc₀ : 0 < c₀)
    (harea : 0 < inner ℝ (A - c) e * inner ℝ (B - A) v
      - inner ℝ (A - c) v * inner ℝ (B - A) e) :
    0 < inner ℝ (A + s • (B - A) - c) e * inner ℝ (c₀ • (B - A)) v
      - inner ℝ (A + s • (B - A) - c) v * inner ℝ (c₀ • (B - A)) e := by
  rw [angNum_segment]
  exact mul_pos hc₀ harea

/-! ## 2. The numerator of a chord-concave chart graph -/

/-- **The arc zone: the angular-velocity numerator of a chart graph about a centre at the origin is
positive** when the chart coordinate is strictly increasing with positive derivative, the profile is
concave in the chart coordinate, and the profile at the chart coordinate of the centre is positive.
This is `Work.Drive.Generic.angVelNum_pos_of_chordConcave` at `xc = yc = 0`. -/
theorem angNum_arc_zero {H X : ℝ → ℝ} {a b ξ₀ : ℝ} (hab : a < b)
    (hXmono : StrictMonoOn X (Set.Icc a b))
    (hxpos : ∀ ξ ∈ Set.Ioo a b, 0 < deriv X ξ)
    (hHdiff : ∀ ξ ∈ Set.Ioo a b, DifferentiableAt ℝ H ξ)
    (hchord : ∀ ξ₁ ∈ Set.Icc a b, ∀ ξ₂ ∈ Set.Icc a b, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ ξ ∈ Set.Icc a b, X ξ = t * X ξ₁ + (1 - t) * X ξ₂ →
        t * H ξ₁ + (1 - t) * H ξ₂ ≤ H ξ)
    (hξ₀ : ξ₀ ∈ Set.Ioo a b) (hx₀ : X ξ₀ = 0) (hy₀ : 0 < H ξ₀) :
    ∀ ξ ∈ Set.Ioo a b, 0 < H ξ * deriv X ξ - X ξ * deriv H ξ := by
  intro ξ hξ
  have h := angVelNum_pos_of_chordConcave (H := H) (X := X) (a := a) (b := b) (xc := 0) (yc := 0)
    (ξ₀ := ξ₀) hab hXmono hxpos hHdiff hchord hξ₀ hy₀ hx₀.symm ξ hξ
  simpa using h

/-! ## 3. The bridge to the chart coordinates of a curve -/

/-- **The chart coordinates of a curve.**  For a curve `p` with velocity `T`, the chart coordinates
`X := ⟪p - c, v⟫` and `H := ⟪p - c, e⟫` have the derivatives `⟪T, v⟫` and `⟪T, e⟫`. -/
theorem hasDerivAt_chartCoords {p T : ℝ → E} {c v e : E} {s : ℝ}
    (h : HasDerivAt p (T s) s) :
    HasDerivAt (fun u : ℝ => inner ℝ (p u - c) v) (inner ℝ (T s) v) s ∧
      HasDerivAt (fun u : ℝ => inner ℝ (p u - c) e) (inner ℝ (T s) e) s := by
  have h1 : HasDerivAt (fun u : ℝ => p u - c) (T s) s := h.sub_const c
  have hv : HasDerivAt (fun _ : ℝ => v) 0 s := hasDerivAt_const s v
  have he : HasDerivAt (fun _ : ℝ => e) 0 s := hasDerivAt_const s e
  exact ⟨by simpa using h1.inner (𝕜 := ℝ) hv, by simpa using h1.inner (𝕜 := ℝ) he⟩

/-- **The bridge identity.**  If `X` and `H` are the chart coordinates of the curve `p` (with
respect to the centre `c` and the frame `(v, e)`) and the derivative of `X` at `s` is `⟪T s, v⟫` and
that of `H` is `⟪T s, e⟫`, then the angular-velocity numerator is `H s * X' s - X s * H' s`. -/
theorem angNum_eq_chart {p T : ℝ → E} {c v e : E} {s : ℝ}
    (hX : HasDerivAt (fun u : ℝ => inner ℝ (p u - c) v) (inner ℝ (T s) v) s)
    (hH : HasDerivAt (fun u : ℝ => inner ℝ (p u - c) e) (inner ℝ (T s) e) s) :
    inner ℝ (p s - c) e * inner ℝ (T s) v - inner ℝ (p s - c) v * inner ℝ (T s) e
      = inner ℝ (p s - c) e * deriv (fun u : ℝ => inner ℝ (p u - c) v) s
        - inner ℝ (p s - c) v * deriv (fun u : ℝ => inner ℝ (p u - c) e) s := by
  rw [hX.deriv, hH.deriv]


end Work.Drive.H2
