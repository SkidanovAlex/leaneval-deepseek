import Mathlib
import Submission.Work.Drive.orderTripleParity
import Submission.Work.Drive.blockFactorIdentification
import Submission.Work.Drive.tripleProductIdentity
import Submission.Work.Drive.germLevelBridge

/-!
# The design's identity in the germ's own counts (the `CntAt` form of route (B))

`TRIPLE_IDENTITY_STATUS.md` §8 records the two routes to the identity at a valid pair `(a, c')`.
Route (B) runs the triple machinery at a *perturbed* parameter `τ : Fin 3 → 𝔼^m` (the chart
perturbation applied to the three blocks of the design's triple) instead of at the honest one; then
`Work.Drive.coreSideCount_block_eq_CntAt_chartPert` identifies each T6 factor with the germ's own count
`CntAt Ξ Q (cblk j) (u j − u k) (τ k, τ j)`, i.e. with the very quantity that `sideGerm` is the germ of.

This file performs that assembly at the level of the *counts*: from

* the engine plus the ends clause at the perturbed triple (`hmeet`, `hdisj`, `hbot` — the inputs of
  `Work.Drive.odd_sum_topBdryMeet_of_ends`),
* the per-block multiplicativity T6 of the transport (`hblock`), and
* the commutation of the chart perturbation with the rotations (`hcomm`; automatic for the concrete
  `Work.Drive.chartPert` by `Work.Drive.chartPert_rotCapping_comm`),

it produces the identity **in `CntAt` form**

> `C(0,1)·C(0,2) + C(1,2)·C(1,0) + C(2,0)·C(2,1) = 1`   in `ZMod 2`,

where `C(k,j)` is the `ZMod 2` value of `CntAt Ξ Q (cblk j) (u j − u k) (τ k, τ j)`.

The remaining step — converting each `CntAt` into a `sideGerm` value, which needs the six pair
goodnesses, the parity locality at the levels and the germ's level independence — is
`Work.Drive.CntAt_cast_eq_sideGerm` and `Work.Drive.sideGerm_eq_of_level_lt`, applied by the consumer.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-- **The chart of the block `k` of the perturbed design's triple**: the perturbed rotated chart
`Ξ (τ k) ∘ rotCapping (u k) ∘ Q`. -/
def blockChart {m : ℕ} (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (u : Fin 3 → UnitAddCircle) (τ : Fin 3 → EuclideanSpace ℝ (Fin m))
    (k : Fin 3) : ℂ → CappingSpace :=
  fun z => Ξ (τ k) (rotCapping (u k) (Q z))

/-- **The plane presentation of the block `k` of the perturbed design's triple**: the perturbed rotated
plane `Ξ (τ k) ∘ rotPresentation Q (u k)`. -/
def blockPlane {m : ℕ} (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (u : Fin 3 → UnitAddCircle) (τ : Fin 3 → EuclideanSpace ℝ (Fin m))
    (k : Fin 3) : EuclideanSpace ℝ (Fin 2) → CappingSpace :=
  fun y => Ξ (τ k) (rotPresentation Q (u k) y)

/-- **The `k`-th chain of the perturbed design's triple**: the radial sweep of the perturbed rotated
plane, truncated at the level `cblk k`. -/
def designSweep {m : ℕ} (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (u : Fin 3 → UnitAddCircle) (τ : Fin 3 → EuclideanSpace ℝ (Fin m))
    (cblk : Fin 3 → ℝ) (k : Fin 3) : EuclideanSpace ℝ (Fin 3) → CappingSpace :=
  clampedSweep (cblk k) (fun s => 1 - s) (blockPlane Ξ Q u τ k)

/-- **The design's identity in the germ's own counts, from the perturbed triple machinery.**  The six
`CntAt` values at the six ordered pairs `(k,j)` satisfy the functional identity of Hugelmeyer's
Lemma 4 at the angles `u`:

> `Σ_k (the two factors of the block k, read as germ counts at the angles u (k+1) − u k and
> u (k+2) − u k) = 1`.

The hypotheses are exactly the inputs of `Work.Drive.odd_sum_topBdryMeet_of_ends` at the perturbed
triple together with the transport's per-block T6 (`hblock`, in the block's own chart) and the
commutation of `Ξ` with the rotations. -/
theorem sum_CntAt_products_eq_one_of_blockT6 {m : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) CappingSpace]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) CappingSpace]
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace) (Q : ℂ → CappingSpace)
    (u : Fin 3 → UnitAddCircle) (τ : Fin 3 → EuclideanSpace ℝ (Fin m)) (cblk : Fin 3 → ℝ)
    (hmeet : Meet3Hyp CappingSpace (designSweep Ξ Q u τ cblk))
    (hdisj : ∀ (k : Fin 3) (x : Fin 3 → EuclideanSpace ℝ (Fin 3)),
      x ∈ tripleBdryMeet CappingSpace (designSweep Ξ Q u τ cblk) k →
      ¬ (onSeam (x k) ∧ (x k 2 = 0 ∨ x k 2 = 1)))
    (hbot : Odd ((bottomBdryMeet CappingSpace (designSweep Ξ Q u τ cblk) 0).ncard
      + (bottomBdryMeet CappingSpace (designSweep Ξ Q u τ cblk) 1).ncard
      + (bottomBdryMeet CappingSpace (designSweep Ξ Q u τ cblk) 2).ncard))
    (hblock : ∀ k : Fin 3,
      Odd ((topBdryMeet CappingSpace (designSweep Ξ Q u τ cblk) k).ncard) ↔
        (Odd (coreSideCount (blockChart Ξ Q u τ k) (cblk (k + 1))
              (blockPlane Ξ Q u τ (k + 1)))
          ∧ Odd (coreSideCount (blockChart Ξ Q u τ k) (cblk (k + 2))
              (blockPlane Ξ Q u τ (k + 2)))))
    (hcomm : ∀ (s : EuclideanSpace ℝ (Fin m)) (w : UnitAddCircle) (p : CappingSpace),
      Ξ s (rotCapping w p) = rotCapping w (Ξ s p)) :
    ((CntAt Ξ Q (cblk (0 + 1)) (u (0 + 1) - u 0) (τ 0, τ 1) : ℕ) : ZMod 2)
        * ((CntAt Ξ Q (cblk (0 + 2)) (u (0 + 2) - u 0) (τ 0, τ 2) : ℕ) : ZMod 2)
      + ((CntAt Ξ Q (cblk (1 + 1)) (u (1 + 1) - u 1) (τ 1, τ 2) : ℕ) : ZMod 2)
        * ((CntAt Ξ Q (cblk (1 + 2)) (u (1 + 2) - u 1) (τ 1, τ 0) : ℕ) : ZMod 2)
      + ((CntAt Ξ Q (cblk (2 + 1)) (u (2 + 1) - u 2) (τ 2, τ 0) : ℕ) : ZMod 2)
        * ((CntAt Ξ Q (cblk (2 + 2)) (u (2 + 2) - u 2) (τ 2, τ 1) : ℕ) : ZMod 2) = 1 := by
  have htop := odd_sum_topBdryMeet_of_ends (designSweep Ξ Q u τ cblk) hmeet hdisj hbot
  have hsum := zmod2_sum_three_eq_one_of_odd
    (fun k : Fin 3 => (topBdryMeet CappingSpace (designSweep Ξ Q u τ cblk) k).ncard)
    (by simpa using htop)
  -- the three block multiplicativities, in `ZMod 2` form
  have hk : ∀ k : Fin 3,
      (((topBdryMeet CappingSpace (designSweep Ξ Q u τ cblk) k).ncard : ℕ) : ZMod 2)
        = ((coreSideCount (blockChart Ξ Q u τ k) (cblk (k + 1))
              (blockPlane Ξ Q u τ (k + 1)) : ℕ) : ZMod 2)
          * ((coreSideCount (blockChart Ξ Q u τ k) (cblk (k + 2))
              (blockPlane Ξ Q u τ (k + 2)) : ℕ) : ZMod 2) :=
    fun k => zmod2_natCast_eq_mul_of_odd_iff (hblock k)
  -- the identification of the factors with the germ's own counts
  have hid : ∀ k j : Fin 3,
      ((coreSideCount (blockChart Ξ Q u τ k) (cblk j) (blockPlane Ξ Q u τ j) : ℕ) : ZMod 2)
        = ((CntAt Ξ Q (cblk j) (u j - u k) (τ k, τ j) : ℕ) : ZMod 2) := by
    intro k j
    have h := coreSideCount_block_eq_CntAt Ξ hcomm Q u τ cblk k j
    change (((coreSideCount (fun z => Ξ (τ k) (rotCapping (u k) (Q z))) (cblk j)
        (fun y => Ξ (τ j) (rotPresentation Q (u j) y)) : ℕ)) : ZMod 2)
      = ((CntAt Ξ Q (cblk j) (u j - u k) (τ k, τ j) : ℕ) : ZMod 2)
    rw [h]
  rw [hk 0, hk 1, hk 2] at hsum
  simp only [hid] at hsum
  rw [show (0 : Fin 3) + 1 = 1 from by decide, show (0 : Fin 3) + 2 = 2 from by decide,
    show (1 : Fin 3) + 1 = 2 from by decide, show (1 : Fin 3) + 2 = 0 from by decide,
    show (2 : Fin 3) + 1 = 0 from by decide, show (2 : Fin 3) + 2 = 1 from by decide] at hsum
  exact hsum

/-! ## The form for the concrete chart perturbation -/

/-- **The `CntAt` form of the design's identity for the concrete perturbation `Work.Drive.chartPert`**
(`m = 4`), with the commutation discharged by the proved `Work.Drive.chartPert_rotCapping_comm`. -/
theorem sum_CntAt_products_eq_one_of_blockT6_chartPert
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) CappingSpace]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) CappingSpace]
    (Q : ℂ → CappingSpace) (u : Fin 3 → UnitAddCircle)
    (τ : Fin 3 → EuclideanSpace ℝ (Fin 4)) (cblk : Fin 3 → ℝ)
    (hmeet : Meet3Hyp CappingSpace
      (designSweep (fun s p => chartPert s p) Q u τ cblk))
    (hdisj : ∀ (k : Fin 3) (x : Fin 3 → EuclideanSpace ℝ (Fin 3)),
      x ∈ tripleBdryMeet CappingSpace
        (designSweep (fun s p => chartPert s p) Q u τ cblk) k →
      ¬ (onSeam (x k) ∧ (x k 2 = 0 ∨ x k 2 = 1)))
    (hbot : Odd ((bottomBdryMeet CappingSpace
          (designSweep (fun s p => chartPert s p) Q u τ cblk) 0).ncard
      + (bottomBdryMeet CappingSpace
          (designSweep (fun s p => chartPert s p) Q u τ cblk) 1).ncard
      + (bottomBdryMeet CappingSpace
          (designSweep (fun s p => chartPert s p) Q u τ cblk) 2).ncard))
    (hblock : ∀ k : Fin 3,
      Odd ((topBdryMeet CappingSpace
          (designSweep (fun s p => chartPert s p) Q u τ cblk) k).ncard) ↔
        (Odd (coreSideCount (blockChart (fun s p => chartPert s p) Q u τ k) (cblk (k + 1))
              (blockPlane (fun s p => chartPert s p) Q u τ (k + 1)))
          ∧ Odd (coreSideCount (blockChart (fun s p => chartPert s p) Q u τ k) (cblk (k + 2))
              (blockPlane (fun s p => chartPert s p) Q u τ (k + 2))))) :
    ((CntAt (fun s p => chartPert s p) Q (cblk (0 + 1)) (u (0 + 1) - u 0) (τ 0, τ 1) : ℕ) : ZMod 2)
        * ((CntAt (fun s p => chartPert s p) Q (cblk (0 + 2)) (u (0 + 2) - u 0)
            (τ 0, τ 2) : ℕ) : ZMod 2)
      + ((CntAt (fun s p => chartPert s p) Q (cblk (1 + 1)) (u (1 + 1) - u 1)
            (τ 1, τ 2) : ℕ) : ZMod 2)
        * ((CntAt (fun s p => chartPert s p) Q (cblk (1 + 2)) (u (1 + 2) - u 1)
            (τ 1, τ 0) : ℕ) : ZMod 2)
      + ((CntAt (fun s p => chartPert s p) Q (cblk (2 + 1)) (u (2 + 1) - u 2)
            (τ 2, τ 0) : ℕ) : ZMod 2)
        * ((CntAt (fun s p => chartPert s p) Q (cblk (2 + 2)) (u (2 + 2) - u 2)
            (τ 2, τ 1) : ℕ) : ZMod 2) = 1 := by
  refine sum_CntAt_products_eq_one_of_blockT6 (fun s p => chartPert s p) Q u τ cblk
    hmeet hdisj hbot hblock ?_
  intro s w p
  obtain ⟨x, hx⟩ : ∃ x : ℝ, ((x : ℝ) : UnitAddCircle) = w := ⟨Quotient.out w, Quotient.out_eq w⟩
  rw [← hx]
  exact chartPert_rotCapping_comm x s p

/-! ## The germ identity from the `CntAt` identity

The last step of route (B) of `TRIPLE_IDENTITY_STATUS.md` §8: the six `CntAt` values are the six germ
values, by the dictionary `Work.Drive.CntAt_cast_eq_sideGerm` (a good configuration at the level
`cblk j`, the locality ball) followed by the germ's level independence
`Work.Drive.sideGerm_eq_of_level_lt` (the levels `cblk j` and the design's level `c`).  The wrapper
below takes exactly those six conversions as a single hypothesis, so that the consumer's only remaining
obligation is to produce them. -/

/-- **The germ identity at the pair `(a, c')` from the `CntAt`-form identity.**  The hypothesis `hconv`
is the six-fold conversion of counts into germ values; everything else is the angle bookkeeping of the
design's triple `u 0 = 0`, `u 1 = a`, `u 2 = a + c'`. -/
theorem sideGerm_identity_of_CntAt_products {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace) (Q : ℂ → CappingSpace)
    (c : ℝ) (a c' : UnitAddCircle) (u : Fin 3 → UnitAddCircle)
    (hu0 : u 0 = 0) (hu1 : u 1 = a) (hu2 : u 2 = a + c')
    (τ : Fin 3 → EuclideanSpace ℝ (Fin m)) (cblk : Fin 3 → ℝ)
    (hcnt : ((CntAt Ξ Q (cblk (0 + 1)) (u (0 + 1) - u 0) (τ 0, τ 1) : ℕ) : ZMod 2)
        * ((CntAt Ξ Q (cblk (0 + 2)) (u (0 + 2) - u 0) (τ 0, τ 2) : ℕ) : ZMod 2)
      + ((CntAt Ξ Q (cblk (1 + 1)) (u (1 + 1) - u 1) (τ 1, τ 2) : ℕ) : ZMod 2)
        * ((CntAt Ξ Q (cblk (1 + 2)) (u (1 + 2) - u 1) (τ 1, τ 0) : ℕ) : ZMod 2)
      + ((CntAt Ξ Q (cblk (2 + 1)) (u (2 + 1) - u 2) (τ 2, τ 0) : ℕ) : ZMod 2)
        * ((CntAt Ξ Q (cblk (2 + 2)) (u (2 + 2) - u 2) (τ 2, τ 1) : ℕ) : ZMod 2) = 1)
    (hconv : ∀ k j : Fin 3, k ≠ j →
      ((CntAt Ξ Q (cblk j) (u j - u k) (τ k, τ j) : ℕ) : ZMod 2)
        = sideGerm Ξ Q c (u j - u k)) :
    sideGerm Ξ Q c a * sideGerm Ξ Q c (a + c')
      + sideGerm Ξ Q c (-a) * sideGerm Ξ Q c c'
      + sideGerm Ξ Q c (-(a + c')) * sideGerm Ξ Q c (-c') = 1 := by
  simp only [show (0 : Fin 3) + 1 = 1 from by decide, show (0 : Fin 3) + 2 = 2 from by decide,
    show (1 : Fin 3) + 1 = 2 from by decide, show (1 : Fin 3) + 2 = 0 from by decide,
    show (2 : Fin 3) + 1 = 0 from by decide, show (2 : Fin 3) + 2 = 1 from by decide] at hcnt
  rw [hconv 0 1 (by decide), hconv 0 2 (by decide), hconv 1 2 (by decide),
    hconv 2 0 (by decide), hconv 1 0 (by decide), hconv 2 1 (by decide)] at hcnt
  have e01 : u 1 - u 0 = a := by rw [hu1, hu0]; abel
  have e02 : u 2 - u 0 = a + c' := by rw [hu2, hu0]; abel
  have e12 : u 2 - u 1 = c' := by rw [hu2, hu1]; abel
  have e10 : u 0 - u 1 = -a := by rw [hu0, hu1]; abel
  have e20 : u 0 - u 2 = -(a + c') := by rw [hu0, hu2]; abel
  have e21 : u 1 - u 2 = -c' := by rw [hu1, hu2]; abel
  rw [e01, e02, e12, e10, e20, e21] at hcnt
  rw [← mul_comm (sideGerm Ξ Q c (-a)) (sideGerm Ξ Q c c')] at hcnt
  exact hcnt

end

end Work.Drive
