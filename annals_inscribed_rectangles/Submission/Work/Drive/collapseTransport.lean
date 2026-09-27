import Mathlib
import Submission.Work.Drive.planeChain
import Submission.Work.Drive.clampedSweep
import Submission.Work.Drive.sideCountDefs
import Submission.Work.Drive.cutTranslate
import Submission.Work.Drive.cutBaseBox

/-!
# The radial-collapse transport of Hugelmeyer's Lemma 2 (the lead's design, 2026-09-25 11:00)

`Work.Drive.chainFunctional_topClauses` — the old form of the transport `n_P ≡ ε_Q · ε_R` — is
**retired**: its hypothesis ("the cut of the plane by a sweep is one arc or empty") is false for the
honest chart (`CLASSIMAGE_NONPLANAR.md`: the class image of a plane chart spans `ℝP³`).  The lead's
replacement is the **radial collapse**, whose only geometric inputs are disjointness statements (no
level inequalities, no chord systems, no `1`-manifold classification).

## The collapse

With `σ s = sin² (π s / 2)` and a smooth collar function `β > 0` with `β ≥ √·` and `β = √·` on
`[δ², ∞)`:

> `ρ(s, z) = z / (1 + σ s (β (‖z‖²) - 1))`.

Then `ρ(0, ·) = id`, `ρ` preserves the boundary circle, is odd, never increases the radius on the
closed disk, and `ρ(1, ·) = z / ‖z‖` on the collar `‖z‖ ≥ δ`.  The **collapse family** of block `0` is

> `colPlane β Q s u = Q (ρ(s, sqDisk (foldBox u))) = diskPlane (Q ∘ ρ(s, ·)) u`,

so `colPlane β Q 0 = diskPlane Q` (the plane) and `colPlane β Q 1` is the *radially collapsed* plane:
its outer part (the collar) is the core loop, and its inner part stays in a small disk.

## The count, and the shape of the transport

For the two radial sweeps `V = clampedSweep c ψ P₁`, `W = clampedSweep c ψ P₂` the collapsed count is

> `colCount β Q V W s = #{(u, y, z) ∈ □ × □ × □ | colPlane β Q s u = V y ∧ diskPlane Q u = W z}`

(the second condition is *independent of `s`*, so the `(u, z)` part is pinned to the cut of the plane
by `W` throughout the deformation).  The transport is then

* `Even (colCount β Q V W 0 + colCount β Q V W 1)` (box parity / the `(2,2)`-meet engine with the two
  charts `ρ(s,·) ∘ Q` and `Q` split apart, `ParityProp` at `m = 8`);
* `colCount β Q V W 0 = n_P` (`colPlane β Q 0 = diskPlane Q`, and the dictionary
  `ncard_topBdryMeet_zero_eq_ncard_cutTriples` of `cutTranslate.lean`);
* `colCount β Q V W 1 = Σ_{(t,y) ∈ coreMeet Q c P₁} #(diamMeet Q t W)` (the fibre sum: at `s = 1` the
  outer part of the collapsed plane is the core loop, and the radial fibre at a core point is a
  diameter);
* `Odd (#(diamMeet Q t W)) ↔ Odd (coreSideCount Q c P₂)` for every `t` (two applications of the loop
  deformation invariance `Work.Drive.odd_ncard_loopFamMeet_iff`: the diameter `σ ↦ (1-2σ)e^{iπt}` is
  deformed first into the half-circle through `±e^{iπt}` and then rotated to the core loop);

whence `Odd n_P ↔ Odd (coreSideCount Q c P₁) ∧ Odd (coreSideCount Q c P₂)` — Hugelmeyer's Lemma 2 in
the form the design's count `Work.Drive.designCount` consumes (its `hdense`, and with the
reference-plane triple also `hn2`).

The file is organised as: the calculus of `ρ` (§1, proved), the collar function (§2, delegated), the
family and the count (§3, proved bookkeeping), and the four analytic obligations as named statements
(§4) to be proved in the indicated order.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology

noncomputable section

/-! ## 1. The calculus of the radial collapse -/

/-- The interpolation profile `σ s = sin² (π s / 2)`. -/
def colSigma (s : ℝ) : ℝ := Real.sin (Real.pi * s / 2) ^ 2

lemma colSigma_zero : colSigma 0 = 0 := by simp [colSigma]

lemma colSigma_one : colSigma 1 = 1 := by
  rw [colSigma, show Real.pi * 1 / 2 = Real.pi / 2 by ring, Real.sin_pi_div_two]; norm_num

lemma colSigma_mem (s : ℝ) : colSigma s ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨sq_nonneg _, ?_⟩
  rw [colSigma]
  exact Real.sin_sq_le_one _

lemma contDiff_colSigma : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) colSigma := by
  unfold colSigma
  fun_prop

/-- The denominator `1 + σ s (β (‖z‖²) - 1)` of the radial collapse. -/
def colDenom (β : ℝ → ℝ) (s : ℝ) (z : ℂ) : ℝ := 1 + colSigma s * (β (‖z‖ ^ 2) - 1)

/-- The radial collapse `z ↦ z / (1 + σ s (β (‖z‖²) - 1))`. -/
def colMap (β : ℝ → ℝ) (s : ℝ) (z : ℂ) : ℂ := ((colDenom β s z)⁻¹ : ℝ) • z

lemma colDenom_pos {β : ℝ → ℝ} (hβpos : ∀ t : ℝ, 0 < β t) (s : ℝ) (z : ℂ) :
    0 < colDenom β s z := by
  have hσ := colSigma_mem s
  simp only [Set.mem_Icc] at hσ
  have hb := hβpos (‖z‖ ^ 2)
  have he : colDenom β s z = (1 - colSigma s) + colSigma s * β (‖z‖ ^ 2) := by rw [colDenom]; ring
  rw [he]
  nlinarith [hσ.1, hσ.2, hb, mul_nonneg hσ.1 hb.le]

lemma colMap_zero (β : ℝ → ℝ) (z : ℂ) : colMap β 0 z = z := by
  simp [colMap, colDenom, colSigma_zero]

lemma colMap_neg (β : ℝ → ℝ) (s : ℝ) (z : ℂ) : colMap β s (-z) = -colMap β s z := by
  simp [colMap, colDenom, norm_neg]

lemma norm_colMap {β : ℝ → ℝ} (hβpos : ∀ t : ℝ, 0 < β t) (s : ℝ) (z : ℂ) :
    ‖colMap β s z‖ = (colDenom β s z)⁻¹ * ‖z‖ := by
  rw [colMap, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (colDenom_pos hβpos s z))]

/-- **The denominator dominates the radius**: for a collar function `β ≥ √·` and `‖z‖ ≤ 1`, the
collapse never increases the radius. -/
lemma norm_le_colDenom {β : ℝ → ℝ} (hβ : ∀ t : ℝ, Real.sqrt t ≤ β t)
    (s : ℝ) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖z‖ ≤ colDenom β s z := by
  have hσ := colSigma_mem s
  simp only [Set.mem_Icc] at hσ
  have hβz : ‖z‖ ≤ β (‖z‖ ^ 2) := by
    have := hβ (‖z‖ ^ 2)
    rwa [Real.sqrt_sq (norm_nonneg z)] at this
  have h2 : (1 - colSigma s) * ‖z‖ ≤ 1 - colSigma s := by
    have h1 : (0 : ℝ) ≤ 1 - colSigma s := by linarith [hσ.2]
    nlinarith [norm_nonneg z, hz, h1]
  have h3 : colSigma s * ‖z‖ ≤ colSigma s * β (‖z‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hβz hσ.1
  have he : colDenom β s z = (1 - colSigma s) + colSigma s * β (‖z‖ ^ 2) := by rw [colDenom]; ring
  have h4 : (1 - colSigma s) * ‖z‖ + colSigma s * ‖z‖ = ‖z‖ := by ring
  rw [he]
  linarith

lemma norm_colMap_le_one {β : ℝ → ℝ} (hβpos : ∀ t : ℝ, 0 < β t)
    (hβ : ∀ t : ℝ, Real.sqrt t ≤ β t) (s : ℝ) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖colMap β s z‖ ≤ 1 := by
  rw [norm_colMap hβpos, inv_mul_le_iff₀ (colDenom_pos hβpos s z)]
  simpa using norm_le_colDenom hβ s z hz

/-- The collapse at `s = 1` in the outer collar is the radial projection. -/
lemma colMap_one_of_collar {β : ℝ → ℝ}
    {δ : ℝ} (hδ : 0 ≤ δ) (hβδ : ∀ t : ℝ, δ ^ 2 ≤ t → β t = Real.sqrt t)
    (z : ℂ) (hz : δ ≤ ‖z‖) :
    colMap β 1 z = ((‖z‖)⁻¹ : ℝ) • z := by
  have hsq : δ ^ 2 ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ hδ hz 2
  have h1 : colDenom β 1 z = ‖z‖ := by
    rw [colDenom, colSigma_one, one_mul, hβδ (‖z‖ ^ 2) hsq, Real.sqrt_sq (norm_nonneg z)]
    ring
  rw [colMap, h1]

/-- The collapse fixes the boundary circle. -/
lemma colMap_of_norm_one {β : ℝ → ℝ}
    (hβ1 : β 1 = 1) (s : ℝ) (z : ℂ) (hz : ‖z‖ = 1) : colMap β s z = z := by
  have h1 : colDenom β s z = 1 := by
    rw [colDenom, hz, one_pow, hβ1]; ring
  rw [colMap, h1]; simp

/-! ## 2. The collar function (delegated as `Work.Drive.colCollar_exists`)

**The collar function of the radial collapse.**  For every `0 < δ` there is a smooth `β : ℝ → ℝ` which
is positive, dominates `√·` on `[0, ∞)` and coincides with `√·` on the collar `[δ², ∞)`.  (The
construction is the convex combination `β t = (1 - η t) · 1 + η t · √t` where `η` is a smooth
`Real.smoothTransition`-cutoff which is `0` below `δ²/2` and `1` above `δ²`; the product `η · √t` is
`C^∞` because it vanishes near the positive half-line's singular point `0`.) -/

/-! ## 3. The collapse family, the count, and its two ends -/

/-! ### Smoothness of the collapse -/

lemma contDiff_normSq_fun :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℂ => ‖p.2‖ ^ 2) := by
  have he : (fun p : ℝ × ℂ => ‖p.2‖ ^ 2) = fun p => (p.2).re ^ 2 + (p.2).im ^ 2 := by
    funext p
    rw [Complex.sq_norm, Complex.normSq_apply]
    push_cast
    ring
  rw [he]
  refine ContDiff.add ?_ ?_
  · exact (Complex.reCLM.contDiff.comp contDiff_snd).pow 2
  · exact (Complex.imCLM.contDiff.comp contDiff_snd).pow 2

lemma contDiff_colDenom {β : ℝ → ℝ} (hβ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℂ => colDenom β p.1 p.2) := by
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℂ => β (‖p.2‖ ^ 2)) :=
    hβ.comp contDiff_normSq_fun
  have h3 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℂ => colSigma p.1) :=
    contDiff_colSigma.comp contDiff_fst
  unfold colDenom
  exact contDiff_const.add (h3.mul (h2.sub contDiff_const))

lemma contDiff_colMap {β : ℝ → ℝ} (hβ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β)
    (hβpos : ∀ t : ℝ, 0 < β t) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℂ => colMap β p.1 p.2) := by
  have hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℂ => (colDenom β p.1 p.2)⁻¹) :=
    (contDiff_colDenom hβ).inv (fun p => ne_of_gt (colDenom_pos hβpos p.1 p.2))
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℂ => (colDenom β p.1 p.2)⁻¹ • p.2) :=
    hd.smul (contDiff_snd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℂ => p.2))
  simpa only [colMap] using h2

/-- The collapsed chart: the chart `Q` composed with the collapse at parameter `s`. -/
def colChart (β : ℝ → ℝ) (Q : ℂ → CappingSpace) (s : ℝ) : ℂ → CappingSpace :=
  fun z => Q (colMap β s z)

/-- **Block `0` of the collapse family**: the disk plane presented by the collapsed chart. -/
def colPlane (β : ℝ → ℝ) (Q : ℂ → CappingSpace) (s : ℝ) :
    EuclideanSpace ℝ (Fin 2) → CappingSpace :=
  diskPlane (colChart β Q s)

lemma colPlane_zero (β : ℝ → ℝ) (Q : ℂ → CappingSpace) : colPlane β Q 0 = diskPlane Q := by
  funext u
  simp [colPlane, colChart, diskPlane, colMap_zero]

/-- **The collapsed plane inherits the seam invariance of the chart.** -/
lemma colPlane_seamInv2 {β : ℝ → ℝ} (hβ1 : β 1 = 1) {Q : ℂ → CappingSpace} (s : ℝ)
    (hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z) {y : EuclideanSpace ℝ (Fin 2)}
    (hy : onSeam2 y) : colPlane β Q s (seamInv2 y) = colPlane β Q s y := by
  refine diskPlane_seamInv2 ?_ hy
  intro z hz
  show colChart β Q s (-z) = colChart β Q s z
  have hz' : ‖colMap β s z‖ = 1 := by rw [colMap_of_norm_one hβ1 s z hz]; exact hz
  simp only [colChart, colMap_neg, hQseam (colMap β s z) hz']

/-- **The collapsed plane on the seam is the plane itself** (the collapse fixes the circle). -/
lemma colPlane_of_norm_one {β : ℝ → ℝ} (hβ1 : β 1 = 1) {Q : ℂ → CappingSpace} (s : ℝ)
    {y : EuclideanSpace ℝ (Fin 2)} (hy : onSeam2 y) :
    colPlane β Q s y = diskPlane Q y := by
  have hbox : foldBox y ∈ Submission.Drive.unitBox 1 := foldBox_mem_unitBox y
  have hnorm : ‖sqDisk (foldBox y)‖ = 1 := (norm_sqDisk_eq_one_iff _ hbox).mpr (onSeam2_foldBox hy)
  simp only [colPlane, colChart, diskPlane, colMap_of_norm_one hβ1 s _ hnorm]

/-- **Block `0` at `s = 1` on the collar** is the *normalised* disk plane: outside the collar radius `δ`
the collapse is the radial projection.  This is the form in which the outer part of the collapsed plane
is identified with the core loop. -/
theorem colPlane_one_of_collar {β : ℝ → ℝ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hβδ : ∀ t : ℝ, δ ^ 2 ≤ t → β t = Real.sqrt t) (Q : ℂ → CappingSpace)
    (u : EuclideanSpace ℝ (Fin 2)) (hu : δ ≤ ‖sqDisk (foldBox u)‖) :
    colPlane β Q 1 u
      = Q (((‖sqDisk (foldBox u)‖)⁻¹ : ℝ) • sqDisk (foldBox u)) := by
  show Q (colMap β 1 (sqDisk (foldBox u))) = _
  rw [colMap_one_of_collar hδ hβδ _ hu]

/-- **The image of the inner disk under the collapse at `s = 1` stays in a disk of radius
`δ₁/β₀`** whenever `β ≥ β₀ > 0` on `[0, δ₁²]`.  This is what makes the inner part of the collapsed
plane miss the cut. -/
theorem norm_colMap_one_le {β : ℝ → ℝ} {δ₁ β₀ : ℝ} (hβ₀ : 0 < β₀)
    (hβ : ∀ t : ℝ, 0 ≤ t → t ≤ δ₁ ^ 2 → β₀ ≤ β t) (z : ℂ) (hz : ‖z‖ ≤ δ₁) :
    ‖colMap β 1 z‖ ≤ ‖z‖ / β₀ := by
  have hsq : (0 : ℝ) ≤ ‖z‖ ^ 2 := sq_nonneg _
  have hle : ‖z‖ ^ 2 ≤ δ₁ ^ 2 := pow_le_pow_left₀ (norm_nonneg z) hz 2
  have hd : colDenom β 1 z = β (‖z‖ ^ 2) := by rw [colDenom, colSigma_one]; ring
  have hpos : 0 < β (‖z‖ ^ 2) := lt_of_lt_of_le hβ₀ (hβ _ hsq hle)
  rw [colMap, hd, norm_smul, Real.norm_eq_abs ((β (‖z‖ ^ 2))⁻¹),
    abs_of_pos (inv_pos.mpr hpos), inv_mul_eq_div]
  exact div_le_div_of_nonneg_left (norm_nonneg z) hβ₀ (hβ _ hsq hle)

/-- **The `8`-parameter meet set of the collapse**: `(u,y,z)` with the collapsed plane meeting `V` at
the point `y` of the parameter cube and the *uncollapsed* plane meeting `W` at `z`.  This is the set
whose cardinality the radial collapse computes (the lead's `K(s)`). -/
def colMeet (β : ℝ → ℝ) (Q : ℂ → CappingSpace)
    (V W : EuclideanSpace ℝ (Fin 3) → CappingSpace) (s : ℝ) :
    Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :=
  {p | p.1 ∈ Submission.Drive.unitBox 1 ∧ p.2.1 ∈ Submission.Drive.unitBox 2 ∧
       p.2.2 ∈ Submission.Drive.unitBox 2 ∧
       colPlane β Q s p.1 = V p.2.1 ∧ diskPlane Q p.1 = W p.2.2}

/-- The collapsed meet count `K(s)`. -/
def colCount (β : ℝ → ℝ) (Q : ℂ → CappingSpace)
    (V W : EuclideanSpace ℝ (Fin 3) → CappingSpace) (s : ℝ) : ℕ :=
  (colMeet β Q V W s).ncard

/-- **`K(0)` is the plane/sweep triple count**: at `s = 0` the collapse is the identity, so the
collapsed meet set is exactly `cutTriples (diskPlane Q) V W`. -/
theorem colMeet_zero_eq_cutTriples (β : ℝ → ℝ) (Q : ℂ → CappingSpace)
    (V W : EuclideanSpace ℝ (Fin 3) → CappingSpace) :
    colMeet β Q V W 0 = cutTriples (diskPlane Q) V W := by
  ext p
  simp only [colMeet, cutTriples, cutRel, Set.mem_ofPred_eq, colPlane_zero]

/-- **`K(0) = n_P`** — the `0`-th collapsed count is the engine's top count for the block `0` of the
radial-sweep triple `(diskPlane Q, V, W)`. -/
theorem colCount_zero_eq_topBdryMeet (β : ℝ → ℝ) (Q : ℂ → CappingSpace)
    (c₀ c : ℝ) (ψ : ℝ → ℝ) (hψ : ψ 1 = 0)
    (P₁ P₂ : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hfibV : ∀ u ∈ cutBaseBox (diskPlane Q) (clampedSweep c ψ P₁) (clampedSweep c ψ P₂),
      (cutFibreBox (diskPlane Q) (clampedSweep c ψ P₁) u).ncard = 1)
    (hfibW : ∀ u ∈ cutBaseBox (diskPlane Q) (clampedSweep c ψ P₁) (clampedSweep c ψ P₂),
      (cutFibreBox (diskPlane Q) (clampedSweep c ψ P₂) u).ncard = 1) :
    colCount β Q (clampedSweep c ψ P₁) (clampedSweep c ψ P₂) 0
      = (topBdryMeet CappingSpace
          (fun k => clampedSweep (![c₀, c, c] k) ψ (![diskPlane Q, P₁, P₂] k)) 0).ncard := by
  have h := Work.Drive.Capping.ncard_topBdryMeet_zero_eq_ncard_cutBaseBox
    (fun k => ![diskPlane Q, P₁, P₂] k) (fun k => ![c₀, c, c] k) ψ hψ hfibV hfibW
  rw [colCount, colMeet_zero_eq_cutTriples, h]
  have hcb : cutBaseBox (![diskPlane Q, P₁, P₂] 0)
      (clampedSweep (![c₀, c, c] 1) ψ (![diskPlane Q, P₁, P₂] 1))
      (clampedSweep (![c₀, c, c] 2) ψ (![diskPlane Q, P₁, P₂] 2))
      = cutBaseBox (diskPlane Q) (clampedSweep c ψ P₁) (clampedSweep c ψ P₂) := by simp
  rw [hcb]
  exact ncard_cutTriples_eq_ncard_cutBaseBox _ _ _ hfibV hfibW

/-! ### The two-parameter loops of the second half

At `s = 1` the outer part of the collapsed plane is the core loop, and the radial fibre over a core
point `e^{iπt}` is the *diameter* `σ ↦ (1 - 2σ) e^{iπt}`.  The parity of the number of meets of a loop
with a fixed chain is invariant under deformation of the loop (`Work.Drive.odd_ncard_loopFamMeet_iff`),
so the diameter meet count has the parity of the core meet count (first deform the diameter segment
into the half-circle through `±e^{iπt}`, then rotate `e^{iπt}` to `1`). -/

/-- **The diameter loop of the chart at angle `t`**: `σ ↦ Q ((1 - 2σ) · exp (i π t))`. -/
def diamLoop (Q : ℂ → CappingSpace) (t : ℝ) (σ : ℝ) : CappingSpace :=
  Q ((1 - 2 * σ) * Complex.exp (Real.pi * (t : ℂ) * Complex.I))

/-- **The half-circle loop of the chart at angle `t`**: `σ ↦ Q (exp (i π (t + σ)))`; it has the same
endpoints `± exp (i π t)` as the diameter loop, and the two are homotopic through loops with fixed
endpoints kept in the disk. -/
def arcLoop (Q : ℂ → CappingSpace) (t : ℝ) (σ : ℝ) : CappingSpace :=
  Q (Complex.exp (Real.pi * ((t + σ : ℝ) : ℂ) * Complex.I))

/-- **The diameter meet**: the meets of the diameter loop at angle `t` with the chain `W`, kept as
`(σ, z)` pairs. -/
def diamMeet (Q : ℂ → CappingSpace) (t : ℝ) (W : EuclideanSpace ℝ (Fin 3) → CappingSpace) :
    Set (ℝ × EuclideanSpace ℝ (Fin 3)) :=
  {p | p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ p.2 ∈ Submission.Drive.unitBox 2 ∧ diamLoop Q t p.1 = W p.2}

/-- **The half-circle meet** at angle `t` with the chain `W`. -/
def arcMeet (Q : ℂ → CappingSpace) (t : ℝ) (W : EuclideanSpace ℝ (Fin 3) → CappingSpace) :
    Set (ℝ × EuclideanSpace ℝ (Fin 3)) :=
  {p | p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ p.2 ∈ Submission.Drive.unitBox 2 ∧ arcLoop Q t p.1 = W p.2}

/-- **The half-circle meet at angle `0` is the core meet** (`arcLoop Q 0 σ = Q (e^{iπσ}) = coreLoop Q σ`),
so the `s = 1` half of T5 lands exactly on the design's side value. -/
theorem arcMeet_zero_eq_coreMeet (Q : ℂ → CappingSpace) (c : ℝ)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) :
    arcMeet Q 0 (clampedSweep c (fun t => 1 - t) P) = coreMeet Q c P := by
  have harg : ∀ σ : ℝ, Complex.exp (Real.pi * (((0 : ℝ) + σ : ℝ) : ℂ) * Complex.I)
      = Complex.exp (Real.pi * (σ : ℂ) * Complex.I) := by
    intro σ; rw [zero_add]
  ext p
  simp only [arcMeet, coreMeet, Set.mem_ofPred_eq, arcLoop, coreLoop]
  rw [harg p.1]

/-! ### The two deformations of T5, as explicit families of loops

`odd_ncard_loopFamMeet_iff` deforms a *family* `L : ℝ² → M` of loops (the first box coordinate is the
family parameter, the second the loop parameter) at fixed second chain `W`, and needs `L (t, 0) = L (t, 1)`
for the *closedness* of every member.  For the chart's loops this closedness is exactly the **seam clause
`Q (-z) = Q z` on the unit circle**.  Two families:

* `diamInterp` — the straight segment interpolation from the diameter `σ ↦ (1 - 2σ) e^{iπt}` to the
  half-circle `σ ↦ e^{iπ(t+σ)}` (both run from `e^{iπt}` to `-e^{iπt}`);
* `arcRot` — the rotation `e^{iπt} → 1` of the half-circle. -/

/-- The point of `ℂ` of angle parameter `t`. -/
def colCirclePt (t : ℝ) : ℂ := Complex.exp (Real.pi * (t : ℂ) * Complex.I)

@[simp] lemma norm_colCirclePt (t : ℝ) : ‖colCirclePt t‖ = 1 := by
  rw [colCirclePt, Complex.norm_exp]
  simp

lemma colCirclePt_add_one (t : ℝ) : colCirclePt (t + 1) = -colCirclePt t := by
  rw [colCirclePt, colCirclePt]
  have h : (Real.pi * ((t + 1 : ℝ) : ℂ) * Complex.I) = Real.pi * (t : ℂ) * Complex.I
      + (Real.pi * Complex.I) := by push_cast; ring
  rw [h, Complex.exp_add, Complex.exp_pi_mul_I]
  ring

/-- **The interpolation between the diameter loop and the half-circle loop**, as a family of loops with
parameter `λ`: `λ = 0` is the diameter, `λ = 1` the half-circle, and every member runs from
`e^{iπt}` (at `σ = 0`) to `-e^{iπt}` (at `σ = 1`). -/
def diamInterp (Q : ℂ → CappingSpace) (t a σ : ℝ) : CappingSpace :=
  Q ((((1 - a) * (1 - 2 * σ) : ℝ) : ℂ) * colCirclePt t
      + ((a : ℂ) * colCirclePt (t + σ)))

@[simp] lemma diamInterp_zero (Q : ℂ → CappingSpace) (t σ : ℝ) :
    diamInterp Q t 0 σ = diamLoop Q t σ := by
  simp [diamInterp, diamLoop, colCirclePt]

@[simp] lemma diamInterp_one (Q : ℂ → CappingSpace) (t σ : ℝ) :
    diamInterp Q t 1 σ = arcLoop Q t σ := by
  simp [diamInterp, arcLoop, colCirclePt]

lemma diamInterp_sigma_zero (Q : ℂ → CappingSpace) (t a : ℝ) :
    diamInterp Q t a 0 = Q (colCirclePt t) := by
  have h : (((1 - a) * (1 - 2 * 0) : ℝ) : ℂ) * colCirclePt t + ((a : ℂ) * colCirclePt (t + 0))
      = colCirclePt t := by
    rw [show (t + 0 : ℝ) = t from by ring]
    push_cast
    ring
  rw [diamInterp, h]

lemma diamInterp_sigma_one (Q : ℂ → CappingSpace) (t a : ℝ) :
    diamInterp Q t a 1 = Q (-colCirclePt t) := by
  have h : (((1 - a) * (1 - 2 * 1) : ℝ) : ℂ) * colCirclePt t + ((a : ℂ) * colCirclePt (t + 1))
      = -colCirclePt t := by
    rw [colCirclePt_add_one]
    push_cast
    ring
  rw [diamInterp, h]

/-- **Every member of the interpolation is a closed loop**, by the seam clause of the chart. -/
lemma diamInterp_loop {Q : ℂ → CappingSpace} (hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z)
    (t a : ℝ) : diamInterp Q t a 1 = diamInterp Q t a 0 := by
  rw [diamInterp_sigma_one, diamInterp_sigma_zero, hQseam _ (by simp)]

/-- **The rotation of the half-circle loop**: `τ = 0` is the half-circle at angle `t`, `τ = 1` the one
at angle `0`, and every member runs from `e^{iπ((1-τ)t)}` to `-e^{iπ((1-τ)t)}`. -/
def arcRot (Q : ℂ → CappingSpace) (t τ σ : ℝ) : CappingSpace :=
  Q (colCirclePt ((1 - τ) * t + σ))

@[simp] lemma arcRot_zero (Q : ℂ → CappingSpace) (t σ : ℝ) :
    arcRot Q t 0 σ = arcLoop Q t σ := by
  simp [arcRot, arcLoop, colCirclePt]

@[simp] lemma arcRot_one (Q : ℂ → CappingSpace) (t σ : ℝ) :
    arcRot Q t 1 σ = arcLoop Q 0 σ := by
  simp [arcRot, arcLoop, colCirclePt]

lemma arcRot_sigma_zero (Q : ℂ → CappingSpace) (t τ : ℝ) :
    arcRot Q t τ 0 = Q (colCirclePt ((1 - τ) * t)) := by
  simp [arcRot]

lemma arcRot_sigma_one (Q : ℂ → CappingSpace) (t τ : ℝ) :
    arcRot Q t τ 1 = Q (-colCirclePt ((1 - τ) * t)) := by
  have h : ((1 - τ) * t + 1 : ℝ) = ((1 - τ) * t) + 1 := by ring
  rw [arcRot, h, colCirclePt_add_one]

/-- **Every member of the rotation family is a closed loop**, by the seam clause of the chart. -/
lemma arcRot_loop {Q : ℂ → CappingSpace} (hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z)
    (t τ : ℝ) : arcRot Q t τ 1 = arcRot Q t τ 0 := by
  rw [arcRot_sigma_one, arcRot_sigma_zero, hQseam _ (by simp)]

/-! ### Note on the family smoothness of block `0`

The pure `ContDiff` statement `ContDiff ℝ ⊤ (fun p : ℝ³ => colMap β (p 2) (sqDisk (foldBox (mk2 (p 0) (p 1)))))`
— the analytic input of the family smoothness of block `0` — is mathematically immediate from
`contDiff_colMap` (`smooth` ∘ `sqDisk ∘ foldBox ∘ mk2`), but its *elaboration* in this file blows the
`whnf` heartbeat budget (a known phenomenon of this workspace around `CappingSpace`/`sqDisk`; the same
happened for the `ContMDiff (𝓡 3) (𝓡 4)` form).  It is therefore left as a (trivial) obligation for the
consumer of the collapse family, together with the `ContMDiff` statement
`ContMDiff (𝓡 3) (𝓡 4) (fun p : ℝ³ => colPlane β Q (p 2) (mk2 (p 0) (p 1)))` obtained by composing it with
`hQ`. -/

end

end Work.Drive
