import Submission.Work.BendImage
import Submission.PaperBand.PeriodicFacts

open OptimalMoebius Topology ContDiff
open scoped BigOperators Matrix Topology Metric
open InnerProductGeometry
open Filter

set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# Pre-bend boundary-arc facts: the FREE part of Lemma G (GREEN)

For ANY straight pre-bend chord `[A, B]` of the band — `A = (0, y0)` on the
left boundary line, `B = (1, y1)` on the right, image chord isometric
(`‖f B − f A‖ = ‖B − A‖`) — the two boundary arcs of the band between the
images of `A` and `B` have preimage lengths `a + t` and `a − t` where
`t = |y1 − y0|`, and the 1-Lipschitz edge chains give the universal bound

    √(1 + t²) = ‖f B − f A‖ ≤ a − t          (relation (3) of Lemma G)

which also forces `t ≤ (a²−1)/(2a)` (in particular `t < a`).  Together
with the trivial identities `(a−t) + (a+t) = 2a` and `(a+t) − 2t = a−t`
(relations (1),(2) of Lemma G, `ring`), this is exactly the free part of
Lemma G's four length relations — everything except relation (4)
`√(5+t²) < a+t`, which is the content of the T-pattern construction.

The chains used (both from `embedding_lipschitz` + periodicity, NO
arc-length library):

* `f !₂[1, y0 + a] = f !₂[0, y0]`  (period image of the left-edge point),
  so ‖f B − f A‖ = ‖f(1,y1) − f(1,y0+a)‖ ≤ |y1−y0−a|  (right-edge chain);
* `f !₂[1, y0 − a] = f !₂[0, y0]`,  giving ‖f B − f A‖ ≤ |y1−y0+a|
  (the mirror chain).

Everything is stated abstractly over the endpoint heights `y0, y1` and the
isometric-image hypothesis `himg`, then instantiated for the canonical
U-bends (`uBendA`, `uBendB`) of `Main0U`/`BendImage`.
-/

noncomputable section
namespace Submission.PaperBand

/-! ## 1. Boundary edge points and periodicity -/

/-- The left-edge point `(0,y)` is in the unit strip. -/
lemma leftEdge_mem_unitStrip (y : ℝ) : (!₂[0, y] : ℝ²) ∈ unitStrip := by
  unfold unitStrip
  constructor <;> norm_num

/-- The right-edge point `(1,y)` is in the unit strip. -/
lemma rightEdge_mem_unitStrip (y : ℝ) : (!₂[1, y] : ℝ²) ∈ unitStrip := by
  unfold unitStrip
  constructor <;> norm_num

/-- `period` sends the left-edge point `(0,y)` to `(1, y+a)`. -/
lemma period_leftEdge (a : ℝ) (y : ℝ) :
    period a (!₂[0, y] : ℝ²) = !₂[1, y + a] := by
  ext i <;> fin_cases i <;> simp [period]

/-- **Left-edge to right-edge**: `f (1, y + a) = f (0, y)` — the images of
the left-edge point `(0,y)` and the right-edge point at height `y+a`
coincide (they are in the same orbit under the deck map). -/
lemma f_leftEdge_eq_rightEdge_plus {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (y : ℝ) :
    f !₂[1, y + a] = f !₂[0, y] := by
  have h := hf.periodic (!₂[0, y] : ℝ²) (leftEdge_mem_unitStrip y)
  simpa [period_leftEdge] using h

/-- **Mirror identity**: `f (1, y − a) = f (0, y)` — the right-edge point
at height `y−a` is the period image of `(0, y−2a)`, whose image equals
`f (0,y)` by `2a`-periodicity along the left edge. -/
lemma f_leftEdge_eq_rightEdge_minus {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (y : ℝ) :
    f !₂[1, y - a] = f !₂[0, y] := by
  have hper : f (period a (!₂[0, y - 2 * a] : ℝ²)) = f !₂[0, y - 2 * a] :=
    hf.periodic (!₂[0, y - 2 * a] : ℝ²) (leftEdge_mem_unitStrip (y - 2 * a))
  have hperEq : period a (!₂[0, y - 2 * a] : ℝ²) = !₂[1, y - a] := by
    ext i <;> fin_cases i <;> simp [period] <;> ring
  have htw : f !₂[0, y - 2 * a] = f !₂[0, y] := by
    have hz := boundary_period_twice (a := a) hf (y - 2 * a)
    have harg : (y - 2 * a) + 2 * a = y := by ring
    simpa [harg] using hz.symm
  have hper' : f !₂[1, y - a] = f !₂[0, y - 2 * a] := by simpa [hperEq] using hper
  exact hper'.trans htw

/-! ## 2. Norm facts -/

lemma norm_single_second (t : ℝ) : ‖(!₂[0, t] : ℝ²)‖ = |t| := by
  have hsq : ‖(!₂[0, t] : ℝ²)‖ ^ 2 = t ^ 2 := by
    rw [norm_sq_coord_sum]
    simp
  have hnn : 0 ≤ ‖(!₂[0, t] : ℝ²)‖ := norm_nonneg _
  apply le_antisymm
  · have h' : ‖(!₂[0, t] : ℝ²)‖ ^ 2 ≤ |t| ^ 2 := by simpa [sq_abs] using hsq.le
    exact (sq_le_sq₀ hnn (abs_nonneg t)).mp h'
  · have h' : |t| ^ 2 ≤ ‖(!₂[0, t] : ℝ²)‖ ^ 2 := by simpa [sq_abs] using hsq.ge
    exact (sq_le_sq₀ (abs_nonneg t) hnn).mp h'

/-- Distance between two right-edge points equals the height difference. -/
lemma dist_rightEdge (y1 y2 : ℝ) :
    ‖(!₂[1, y1] : ℝ²) - !₂[1, y2]‖ = |y1 - y2| := by
  have hvec : (!₂[1, y1] : ℝ²) - !₂[1, y2] = !₂[0, y1 - y2] := by
    ext i <;> fin_cases i <;> simp <;> ring
  rw [hvec]
  exact norm_single_second (y1 - y2)

/-! ## 3. The edge chains (1-Lipschitz) -/

/-- **Right-edge chain**: the image distance between the boundary points
`(0,y0)` and `(1,y1)` is at most `|y1 − y0 − a|` (follow `f(1, ·)` from
`y1` to the period copy `y0 + a` of `(0,y0)`). -/
lemma boundary_dist_le_delta_sub_a {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (y0 y1 : ℝ) :
    ‖f !₂[1, y1] - f !₂[0, y0]‖ ≤ |y1 - y0 - a| := by
  have hfa : f !₂[1, y0 + a] = f !₂[0, y0] := f_leftEdge_eq_rightEdge_plus hf y0
  have hL := embedding_lipschitz hf (rightEdge_mem_unitStrip y1)
    (rightEdge_mem_unitStrip (y0 + a))
  calc
    ‖f !₂[1, y1] - f !₂[0, y0]‖ = ‖f !₂[1, y1] - f !₂[1, y0 + a]‖ := by rw [hfa]
    _ ≤ ‖(!₂[1, y0 + a] : ℝ²) - !₂[1, y1]‖ := by simpa [norm_sub_rev] using hL
    _ = |(y0 + a) - y1| := dist_rightEdge (y0 + a) y1
    _ = |y1 - y0 - a| := by
      have hneg : (y0 + a) - y1 = -(y1 - y0 - a) := by ring
      rw [hneg, abs_neg]

/-- **Mirror edge chain**: the image distance between `(0,y0)` and `(1,y1)`
is at most `|y1 − y0 + a|` (follow `f(1, ·)` down to the period copy
`y0 − a` of `(0,y0)`). -/
lemma boundary_dist_le_delta_add_a {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (y0 y1 : ℝ) :
    ‖f !₂[1, y1] - f !₂[0, y0]‖ ≤ |y1 - y0 + a| := by
  have hfa : f !₂[1, y0 - a] = f !₂[0, y0] := f_leftEdge_eq_rightEdge_minus hf y0
  have hL := embedding_lipschitz hf (rightEdge_mem_unitStrip y1)
    (rightEdge_mem_unitStrip (y0 - a))
  calc
    ‖f !₂[1, y1] - f !₂[0, y0]‖ = ‖f !₂[1, y1] - f !₂[1, y0 - a]‖ := by rw [hfa]
    _ ≤ ‖(!₂[1, y0 - a] : ℝ²) - !₂[1, y1]‖ := by simpa [norm_sub_rev] using hL
    _ = |(y0 - a) - y1| := dist_rightEdge (y0 - a) y1
    _ = |y1 - y0 + a| := by
      have hneg : (y0 - a) - y1 = -(y1 - y0 + a) := by ring
      rw [hneg, abs_neg]

/-! ## 4. Preimage chord length -/

/-- The preimage chord between `(0,y0)` and `(1,y1)` has length
`√(1 + (y1−y0)²)`. -/
lemma preimage_chord_length (y0 y1 : ℝ) :
    ‖(!₂[1, y1] : ℝ²) - !₂[0, y0]‖ = Real.sqrt (1 + (y1 - y0) ^ 2) := by
  let Δ : ℝ := y1 - y0
  have hnn : 0 ≤ ‖(!₂[1, y1] : ℝ²) - !₂[0, y0]‖ := norm_nonneg _
  calc
    ‖(!₂[1, y1] : ℝ²) - !₂[0, y0]‖ = Real.sqrt (‖(!₂[1, y1] : ℝ²) - !₂[0, y0]‖ ^ 2) := by
      rw [Real.sqrt_sq hnn]
    _ = Real.sqrt (1 + Δ ^ 2) := by
      congr 1
      rw [norm_sq_coord_sum]
      simp [Δ]

/-! ## 5. The chord-vs-boundary-arc root inequalities -/

/-- **Chord ≤ arc**: an isometrically-imaged chord from `(0,y0)` to
`(1,y1)` has image length at most the (signed) odd-period-copy distance
`|Δ − a|`; since the image chord has length `√(1+Δ²)` we get
`√(1+Δ²) ≤ |Δ − a|`. -/
lemma chord_sqrt_le_abs_sub {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (y0 y1 : ℝ) (himg : ‖f !₂[1, y1] - f !₂[0, y0]‖ = ‖(!₂[1, y1] : ℝ²) - !₂[0, y0]‖) :
    Real.sqrt (1 + (y1 - y0) ^ 2) ≤ |y1 - y0 - a| := by
  calc
    Real.sqrt (1 + (y1 - y0) ^ 2) = ‖(!₂[1, y1] : ℝ²) - !₂[0, y0]‖ :=
      (preimage_chord_length y0 y1).symm
    _ = ‖f !₂[1, y1] - f !₂[0, y0]‖ := himg.symm
    _ ≤ |y1 - y0 - a| := boundary_dist_le_delta_sub_a hf y0 y1

/-- The mirror bound: `√(1+Δ²) ≤ |Δ + a|`. -/
lemma chord_sqrt_le_abs_add {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (y0 y1 : ℝ) (himg : ‖f !₂[1, y1] - f !₂[0, y0]‖ = ‖(!₂[1, y1] : ℝ²) - !₂[0, y0]‖) :
    Real.sqrt (1 + (y1 - y0) ^ 2) ≤ |y1 - y0 + a| := by
  calc
    Real.sqrt (1 + (y1 - y0) ^ 2) = ‖(!₂[1, y1] : ℝ²) - !₂[0, y0]‖ :=
      (preimage_chord_length y0 y1).symm
    _ = ‖f !₂[1, y1] - f !₂[0, y0]‖ := himg.symm
    _ ≤ |y1 - y0 + a| := boundary_dist_le_delta_add_a hf y0 y1

/-- Squared form of the positive chain: `1 + Δ² ≤ (Δ − a)²`. -/
lemma sq_one_add_delta_sq_le_sub_sq {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (y0 y1 : ℝ)
    (himg : ‖f !₂[1, y1] - f !₂[0, y0]‖ = ‖(!₂[1, y1] : ℝ²) - !₂[0, y0]‖) :
    1 + (y1 - y0) ^ 2 ≤ ((y1 - y0) - a) ^ 2 := by
  let Δ : ℝ := y1 - y0
  have hroot : Real.sqrt (1 + Δ ^ 2) ≤ |Δ - a| := by
    simpa [Δ] using chord_sqrt_le_abs_sub hf y0 y1 himg
  have hnonnegL : 0 ≤ Real.sqrt (1 + Δ ^ 2) := Real.sqrt_nonneg _
  have hnonnegR : 0 ≤ |Δ - a| := abs_nonneg _
  have hsq := (sq_le_sq₀ hnonnegL hnonnegR).mpr hroot
  have hroot2 : (Real.sqrt (1 + Δ ^ 2)) ^ 2 = 1 + Δ ^ 2 :=
    Real.sq_sqrt (by nlinarith [sq_nonneg Δ])
  have habs : |Δ - a| ^ 2 = (Δ - a) ^ 2 := by rw [sq_abs]
  have hfinal : 1 + Δ ^ 2 ≤ (Δ - a) ^ 2 := by simpa [hroot2, habs] using hsq
  simpa [Δ] using hfinal

/-- Squared form of the mirror chain: `1 + Δ² ≤ (Δ + a)²`. -/
lemma sq_one_add_delta_sq_le_add_sq {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (y0 y1 : ℝ)
    (himg : ‖f !₂[1, y1] - f !₂[0, y0]‖ = ‖(!₂[1, y1] : ℝ²) - !₂[0, y0]‖) :
    1 + (y1 - y0) ^ 2 ≤ ((y1 - y0) + a) ^ 2 := by
  let Δ : ℝ := y1 - y0
  have hroot : Real.sqrt (1 + Δ ^ 2) ≤ |Δ + a| := by
    simpa [Δ] using chord_sqrt_le_abs_add hf y0 y1 himg
  have hnonnegL : 0 ≤ Real.sqrt (1 + Δ ^ 2) := Real.sqrt_nonneg _
  have hnonnegR : 0 ≤ |Δ + a| := abs_nonneg _
  have hsq := (sq_le_sq₀ hnonnegL hnonnegR).mpr hroot
  have hroot2 : (Real.sqrt (1 + Δ ^ 2)) ^ 2 = 1 + Δ ^ 2 :=
    Real.sq_sqrt (by nlinarith [sq_nonneg Δ])
  have habs : |Δ + a| ^ 2 = (Δ + a) ^ 2 := by rw [sq_abs]
  have hfinal : 1 + Δ ^ 2 ≤ (Δ + a) ^ 2 := by simpa [hroot2, habs] using hsq
  simpa [Δ] using hfinal

/-! ## 6. The displacement bound `|Δ| ≤ (a²−1)/(2a)` -/

/-- Upper bound on the displacement from the positive chain. -/
lemma delta_le_div_of_chord {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (y0 y1 : ℝ)
    (himg : ‖f !₂[1, y1] - f !₂[0, y0]‖ = ‖(!₂[1, y1] : ℝ²) - !₂[0, y0]‖) :
    y1 - y0 ≤ (a ^ 2 - 1) / (2 * a) := by
  let Δ : ℝ := y1 - y0
  have hsq : 1 + Δ ^ 2 ≤ (Δ - a) ^ 2 := by
    simpa [Δ] using sq_one_add_delta_sq_le_sub_sq hf y0 y1 himg
  have hlin : 2 * a * Δ ≤ a ^ 2 - 1 := by nlinarith
  have hpos : 0 < 2 * a := by nlinarith [ha]
  have h : Δ ≤ (a ^ 2 - 1) / (2 * a) := by
    rw [le_div_iff₀ hpos]
    nlinarith
  simpa [Δ] using h

/-- Lower bound on the displacement from the mirror chain:
`−(a²−1)/(2a) ≤ Δ`, equivalently `(1−a²)/(2a) ≤ Δ`. -/
lemma neg_div_le_delta_of_chord {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (y0 y1 : ℝ)
    (himg : ‖f !₂[1, y1] - f !₂[0, y0]‖ = ‖(!₂[1, y1] : ℝ²) - !₂[0, y0]‖) :
    (1 - a ^ 2) / (2 * a) ≤ y1 - y0 := by
  let Δ : ℝ := y1 - y0
  have hsq : 1 + Δ ^ 2 ≤ (Δ + a) ^ 2 := by
    simpa [Δ] using sq_one_add_delta_sq_le_add_sq hf y0 y1 himg
  have hlin : 1 - a ^ 2 ≤ 2 * a * Δ := by nlinarith
  have hpos : 0 < 2 * a := by nlinarith [ha]
  have h : (1 - a ^ 2) / (2 * a) ≤ Δ := by
    rw [div_le_iff₀ hpos]
    nlinarith
  simpa [Δ] using h

/-- **Displacement bound**: the displacement `Δ = y1 − y0` of an
isometrically-imaged chord satisfies `|Δ| ≤ (a²−1)/(2a)` — automatically
`|Δ| < a` and in fact `|Δ| ≤ a/2 − 1/(2a) < a/2`. -/
lemma abs_delta_le_div_of_chord {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (y0 y1 : ℝ)
    (himg : ‖f !₂[1, y1] - f !₂[0, y0]‖ = ‖(!₂[1, y1] : ℝ²) - !₂[0, y0]‖) :
    |y1 - y0| ≤ (a ^ 2 - 1) / (2 * a) := by
  have hU := delta_le_div_of_chord hf ha y0 y1 himg
  have hL := neg_div_le_delta_of_chord hf ha y0 y1 himg
  rw [abs_le]
  constructor
  · have hfrac : -((a ^ 2 - 1) / (2 * a)) = (1 - a ^ 2) / (2 * a) := by
      rw [← neg_div]
      congr 1
      ring
    rw [hfrac]
    exact hL
  · exact hU

/-! ## 7. The chord bound `√(1+Δ²) ≤ a − |Δ|` (relation (3)) -/

/-- For an isometrically-imaged chord, the preimage length `√(1+Δ²)` is at
most `a − |Δ|` — relation (3) of Lemma G in the free part. -/
lemma chord_length_le_sub_abs_delta {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (y0 y1 : ℝ)
    (himg : ‖f !₂[1, y1] - f !₂[0, y0]‖ = ‖(!₂[1, y1] : ℝ²) - !₂[0, y0]‖) :
    Real.sqrt (1 + (y1 - y0) ^ 2) ≤ a - |y1 - y0| := by
  let t : ℝ := |y1 - y0|
  have hb := abs_delta_le_div_of_chord hf ha y0 y1 himg
  have ht0 : 0 ≤ t := abs_nonneg _
  have htdiv : t ≤ (a ^ 2 - 1) / (2 * a) := by simpa [t] using hb
  have h2at : 2 * a * t ≤ a ^ 2 - 1 := by
    have hpos : 0 < 2 * a := by nlinarith [ha]
    have h := (le_div_iff₀ hpos).1 htdiv
    nlinarith
  have htsq : 1 + t ^ 2 ≤ (a - t) ^ 2 := by nlinarith
  have hta : t ≤ a := by
    have hle : t ≤ (a ^ 2 - 1) / (2 * a) := htdiv
    have hfrac : (a ^ 2 - 1) / (2 * a) ≤ a := by
      have hpos : 0 < 2 * a := by nlinarith [ha]
      exact (div_le_iff₀ hpos).2 (by nlinarith)
    linarith
  have hnonnegR : 0 ≤ a - t := sub_nonneg.mpr hta
  have hnonnegL : 0 ≤ Real.sqrt (1 + t ^ 2) := Real.sqrt_nonneg _
  have hsqroot : (Real.sqrt (1 + t ^ 2)) ^ 2 = 1 + t ^ 2 :=
    Real.sq_sqrt (by nlinarith)
  have hs : Real.sqrt (1 + t ^ 2) ≤ a - t :=
    (sq_le_sq₀ hnonnegL hnonnegR).mp (by simpa [hsqroot] using htsq)
  -- target has √(1 + (y1−y0)²) with (y1−y0)² = t²
  simpa [t, sq_abs] using hs

/-- The image chord of an isometrically-imaged chord has length at most
`a − |Δ|` (same content, norm form). -/
lemma chord_norm_le_sub_abs_delta {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (y0 y1 : ℝ)
    (himg : ‖f !₂[1, y1] - f !₂[0, y0]‖ = ‖(!₂[1, y1] : ℝ²) - !₂[0, y0]‖) :
    ‖f !₂[1, y1] - f !₂[0, y0]‖ ≤ a - |y1 - y0| := by
  rw [himg]
  have h := chord_length_le_sub_abs_delta hf ha y0 y1 himg
  have hpre : ‖(!₂[1, y1] : ℝ²) - !₂[0, y0]‖ = Real.sqrt (1 + (y1 - y0) ^ 2) :=
    preimage_chord_length y0 y1
  simpa [hpre] using h

/-! ## 8. Free relations (1) and (2) of Lemma G -/

/-- Relations (1),(2): with `H = a−t`, `D = a+t` we have `H + D = 2a` and
`D − 2t = H`. -/
lemma arc_length_relations (a t : ℝ) :
    (a - t) + (a + t) = 2 * a ∧ (a + t) - 2 * t = a - t := by
  constructor <;> ring

/-! ## 9. Instantiation for canonical U-bends -/

/-- A point with `x0 = 0` equals the left-edge point at its own height. -/
lemma leftEdge_eq_vec {A : ℝ²} (hA0 : A 0 = 0) : A = !₂[0, A 1] := by
  ext i <;> fin_cases i <;> simp [hA0]

/-- A point with `x0 = 1` equals the right-edge point at its own height. -/
lemma rightEdge_eq_vec {B : ℝ²} (hB0 : B 0 = 1) : B = !₂[1, B 1] := by
  ext i <;> fin_cases i <;> simp [hB0]

/-- The canonical U-bend endpoints give an isometric image chord (this is
`BendImage.bend_length_eq` re-expressed with the coordinate endpoints). -/
lemma uBend_image_chord {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0) :
    ‖f !₂[1, (uBendB hf ha hx hdN) 1] - f !₂[0, (uBendA hf ha hx hdN) 1]‖ =
    ‖(!₂[1, (uBendB hf ha hx hdN) 1] : ℝ²) - !₂[0, (uBendA hf ha hx hdN) 1]‖ := by
  have hA0 : (uBendA hf ha hx hdN) 0 = 0 := by
    have h := uBendA_leftEdge hf ha hx hdN
    unfold leftEdge at h
    simpa using h
  have hB0 : (uBendB hf ha hx hdN) 0 = 1 := by
    have h := uBendB_rightEdge hf ha hx hdN
    unfold rightEdge at h
    simpa using h
  have hAeq : uBendA hf ha hx hdN = !₂[0, (uBendA hf ha hx hdN) 1] :=
    leftEdge_eq_vec hA0
  have hBeq : uBendB hf ha hx hdN = !₂[1, (uBendB hf ha hx hdN) 1] :=
    rightEdge_eq_vec hB0
  have hb := bend_length_eq hf ha hx hdN
  rw [← hBeq, ← hAeq]
  exact hb

/-- **Canonical U-bend displacement bound**: `|Δ| ≤ (a²−1)/(2a)` where
`Δ = B1 − A1` is the horizontal displacement of the canonical U-leaf. -/
theorem uBend_abs_disp_bound {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0) :
    |(uBendB hf ha hx hdN) 1 - (uBendA hf ha hx hdN) 1| ≤
      (a ^ 2 - 1) / (2 * a) := by
  have himg := uBend_image_chord hf ha hx hdN
  exact abs_delta_le_div_of_chord hf ha ((uBendA hf ha hx hdN) 1) ((uBendB hf ha hx hdN) 1) himg

/-- **Canonical U-bend relation (3)**: with `t = |Δ|` the displacement of
the canonical U-leaf, `√(1+t²) ≤ a − t`. -/
theorem uBend_h3 {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0) :
    Real.sqrt (1 + |(uBendB hf ha hx hdN) 1 - (uBendA hf ha hx hdN) 1| ^ 2) ≤
      a - |(uBendB hf ha hx hdN) 1 - (uBendA hf ha hx hdN) 1| := by
  have himg := uBend_image_chord hf ha hx hdN
  have h := chord_length_le_sub_abs_delta hf ha
    ((uBendA hf ha hx hdN) 1) ((uBendB hf ha hx hdN) 1) himg
  simpa [sq_abs] using h

/-- **Canonical U-bend displacement is below the aspect**: for the canonical
U-leaf, `t = |Δ| ≤ a` (from relation (3), `0 ≤ √(1+t²) ≤ a−t`). -/
theorem uBend_disp_le_a {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0) :
    |(uBendB hf ha hx hdN) 1 - (uBendA hf ha hx hdN) 1| ≤ a := by
  have h3 := uBend_h3 hf ha hx hdN
  have hnonneg : 0 ≤ Real.sqrt (1 + |(uBendB hf ha hx hdN) 1 - (uBendA hf ha hx hdN) 1| ^ 2) :=
    Real.sqrt_nonneg _
  linarith

/-- **Canonical U-bend image-chord length**: the image of the closed U-leaf
has length at most `a − t` with `t = |Δ|`. -/
theorem uBend_image_length_le_sub_abs {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior)
    (hdN : dN f x ≠ 0) :
    ‖f (uBendB hf ha hx hdN) - f (uBendA hf ha hx hdN)‖ ≤
      a - |(uBendB hf ha hx hdN) 1 - (uBendA hf ha hx hdN) 1| := by
  have hA0 : (uBendA hf ha hx hdN) 0 = 0 := by
    have h := uBendA_leftEdge hf ha hx hdN
    unfold leftEdge at h
    simpa using h
  have hB0 : (uBendB hf ha hx hdN) 0 = 1 := by
    have h := uBendB_rightEdge hf ha hx hdN
    unfold rightEdge at h
    simpa using h
  have hAeq : uBendA hf ha hx hdN = !₂[0, (uBendA hf ha hx hdN) 1] :=
    leftEdge_eq_vec hA0
  have hBeq : uBendB hf ha hx hdN = !₂[1, (uBendB hf ha hx hdN) 1] :=
    rightEdge_eq_vec hB0
  have himg := uBend_image_chord hf ha hx hdN
  have h := chord_norm_le_sub_abs_delta hf ha
    ((uBendA hf ha hx hdN) 1) ((uBendB hf ha hx hdN) 1) himg
  rw [← hBeq, ← hAeq] at h
  exact h

/-- **Every canonical pre-bend has image length at most the aspect**:
`‖f(B) − f(A)‖ ≤ a` (image length ≤ a − t ≤ a with `t = |Δ| ≥ 0`).  This is
the paper's "ℓ(u') ≤ ℓ(∂Ω)/2 = λ" bound at the level of a single pre-bend,
needed for Lemma T's centreline-intersection argument. -/
theorem uBend_length_le_a {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0) :
    ‖f (uBendB hf ha hx hdN) - f (uBendA hf ha hx hdN)‖ ≤ a := by
  have h := uBend_image_length_le_sub_abs hf ha hx hdN
  have ht0 : 0 ≤ |(uBendB hf ha hx hdN) 1 - (uBendA hf ha hx hdN) 1| := abs_nonneg _
  linarith


end Submission.PaperBand
end
