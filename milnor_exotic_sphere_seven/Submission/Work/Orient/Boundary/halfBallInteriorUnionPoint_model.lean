import Mathlib
import Submission.Work.Orient.Boundary
import Submission.Work.Orient.Boundary.localHomology_corner

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The half-space model with the puncture at a boundary point

For the half-space `H = EuclideanHalfSpace (n+1)`, a point `c` of the hyperplane (`c.1 0 = 0`) and
`ρ > 0`, the pair consisting of the punctured half-space `{y | y ≠ c}` and the complement of the
half-ball `{y | dist y c ≤ ρ ∧ 0 < y 0}` has vanishing `n`-th homology.

The proof is the **deformation retraction** pushing every point of the punctured half-space radially
*away* from `c` until its distance from `c` is at least `2ρ`: this lands in the complement of the
half-ball, the homotopy never meets `c` (which is removed), and since `c` lies on the hyperplane the
push is a positive scaling of the vector from `c`, so it automatically stays in the half-space.  The
inclusion `Z ↪ Y` is therefore a homotopy equivalence and
`Work.Orient.Boundary.isZero_relChains_of_homotopyEquiv_incl` gives the vanishing.

This is the boundary-point analogue of `Work.Orient.Boundary.halfBallPuncturedCore` (which punctures
at an *interior* point and pushes away from it, needing a clamp back into the half-space).

The half-space is modelled here on the ambient space `ℝ^{n+1}` (the condition `0 ≤ y 0` being part of
the subtype), which keeps the subtype structure flat; the transfer to a chart of a manifold with
boundary uses `halfIncl`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Manifold

namespace Work.Orient.Boundary

noncomputable section

/-! ## The spaces and the push -/

/-- The punctured half-space, modelled on the ambient space (`0 ≤ y 0` is the half-space
condition). -/
abbrev pSpace (n : ℕ) (c : EuclideanSpace ℝ (Fin (n + 1))) : Type :=
  {y : EuclideanSpace ℝ (Fin (n + 1)) | 0 ≤ y 0 ∧ y ≠ c}

/-- The complement of the half-ball (together with its centre) inside the punctured half-space. -/
abbrev pSet (n : ℕ) (c : EuclideanSpace ℝ (Fin (n + 1))) (ρ : ℝ) : Set (pSpace n c) :=
  {y : pSpace n c | ¬ (dist y.1 c ≤ ρ ∧ 0 < y.1 0)}

/-- The `0`-th coordinate of a point of the form `c + s • (x - c)`, for `c` on the hyperplane. -/
lemma coord_add_smul (n : ℕ) {c : EuclideanSpace ℝ (Fin (n + 1))} (hc : c 0 = 0) (s : ℝ)
    (x : EuclideanSpace ℝ (Fin (n + 1))) :
    (c + s • (x - c)) 0 = s * x 0 := by
  have h : (c + s • (x - c)) 0 = c 0 + s * (x 0 - c 0) := by
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  rw [h, hc, sub_zero, zero_add]

/-- The scale factor pushing a point away from `c` so that its distance from `c` is at least
`2ρ`. -/
def pScale (n : ℕ) (ρ : ℝ) (c : EuclideanSpace ℝ (Fin (n + 1))) (y : pSpace n c) : ℝ :=
  max 1 (2 * ρ / dist y.1 c)

lemma pScale_one_le {n : ℕ} {ρ : ℝ} {c : EuclideanSpace ℝ (Fin (n + 1))} {y : pSpace n c} :
    1 ≤ pScale n ρ c y := le_max_left _ _
lemma pScale_pos {n : ℕ} {ρ : ℝ} {c : EuclideanSpace ℝ (Fin (n + 1))} {y : pSpace n c} :
    0 < pScale n ρ c y := lt_of_lt_of_le zero_lt_one pScale_one_le

lemma pSpace_dist_pos {n : ℕ} {c : EuclideanSpace ℝ (Fin (n + 1))} (y : pSpace n c) :
    0 < dist y.1 c := dist_pos.mpr y.2.2

lemma pScale_mul {n : ℕ} {ρ : ℝ} {c : EuclideanSpace ℝ (Fin (n + 1))} {y : pSpace n c}
    (hd : 0 < dist y.1 c) : pScale n ρ c y * dist y.1 c = max (dist y.1 c) (2 * ρ) := by
  unfold pScale
  rw [max_mul_of_nonneg _ _ (le_of_lt hd), one_mul, div_mul_cancel₀ _ (ne_of_gt hd)]

/-- The scale factor at time `t` of the homotopy. -/
def pScaleT (n : ℕ) (ρ t : ℝ) (c : EuclideanSpace ℝ (Fin (n + 1))) (y : pSpace n c) : ℝ :=
  max 1 (1 + t * (pScale n ρ c y - 1))

lemma pScaleT_one_le {n : ℕ} {ρ t : ℝ} {c : EuclideanSpace ℝ (Fin (n + 1))} {y : pSpace n c} :
    1 ≤ pScaleT n ρ t c y := le_max_left _ _
lemma pScaleT_pos {n : ℕ} {ρ t : ℝ} {c : EuclideanSpace ℝ (Fin (n + 1))} {y : pSpace n c} :
    0 < pScaleT n ρ t c y := lt_of_lt_of_le zero_lt_one pScaleT_one_le
lemma pScaleT_zero {n : ℕ} {ρ : ℝ} {c : EuclideanSpace ℝ (Fin (n + 1))} {y : pSpace n c} :
    pScaleT n ρ 0 c y = 1 := by
  unfold pScaleT
  rw [zero_mul, add_zero, max_self]
lemma pScaleT_one {n : ℕ} {ρ : ℝ} {c : EuclideanSpace ℝ (Fin (n + 1))} {y : pSpace n c} :
    pScaleT n ρ 1 c y = pScale n ρ c y := by
  have h1 : 1 ≤ 1 + (pScale n ρ c y - 1) := by
    linarith [pScale_one_le (n := n) (ρ := ρ) (c := c) (y := y)]
  unfold pScaleT
  rw [one_mul, max_eq_right h1]
  ring

/-- The ambient point at time `t` of the homotopy. -/
def pPathA (n : ℕ) (ρ t : ℝ) (c : EuclideanSpace ℝ (Fin (n + 1))) (y : pSpace n c) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  c + pScaleT n ρ t c y • (y.1 - c)

lemma pPathA_sub {n : ℕ} {ρ t : ℝ} {c : EuclideanSpace ℝ (Fin (n + 1))} {y : pSpace n c} :
    pPathA n ρ t c y - c = pScaleT n ρ t c y • (y.1 - c) := by
  unfold pPathA; abel

lemma dist_pPathA {n : ℕ} {ρ t : ℝ} {c : EuclideanSpace ℝ (Fin (n + 1))} {y : pSpace n c} :
    dist (pPathA n ρ t c y) c = pScaleT n ρ t c y * dist y.1 c := by
  rw [dist_eq_norm, pPathA_sub, norm_smul, Real.norm_of_nonneg (le_of_lt pScaleT_pos),
    ← dist_eq_norm]

lemma pPathA_ne {n : ℕ} {ρ t : ℝ} {c : EuclideanSpace ℝ (Fin (n + 1))} {y : pSpace n c}
    (hd : 0 < dist y.1 c) : pPathA n ρ t c y ≠ c := by
  intro h
  have h0 : dist (pPathA n ρ t c y) c = 0 := by rw [h, dist_self]
  rw [dist_pPathA] at h0
  have h4 : 0 < pScaleT n ρ t c y := pScaleT_pos
  nlinarith [h0]

/-- The point at time `t` of the homotopy, as a point of the punctured half-space. -/
def pPath (n : ℕ) (ρ t : ℝ) (c : EuclideanSpace ℝ (Fin (n + 1))) (hc : c 0 = 0) (y : pSpace n c) :
    pSpace n c :=
  ⟨pPathA n ρ t c y,
    by
      rw [pPathA, coord_add_smul n hc]
      exact mul_nonneg (le_of_lt pScaleT_pos) y.2.1,
    fun h => pPathA_ne (pSpace_dist_pos y) h⟩

lemma pPath_coe {n : ℕ} {ρ t : ℝ} {c : EuclideanSpace ℝ (Fin (n + 1))} {hc : c 0 = 0}
    {y : pSpace n c} : (pPath n ρ t c hc y).1 = pPathA n ρ t c y := rfl

/-- The homotopy stays in the complement of the half-ball when started there. -/
lemma pPath_mem (n : ℕ) {ρ : ℝ} {c : EuclideanSpace ℝ (Fin (n + 1))} (hc : c 0 = 0)
    {t : ℝ} (ht : 0 ≤ t) (z : pSet n c ρ) :
    pPath n ρ t c hc z.1 ∈ pSet n c ρ := by
  have hd : 0 < dist z.1.1 c := pSpace_dist_pos z.1
  rintro ⟨h1, h2⟩
  rw [pPath_coe] at h1 h2
  refine z.2 ⟨?_, ?_⟩
  · have hd1 := dist_pPathA (n := n) (ρ := ρ) (t := t) (c := c) (y := z.1)
    have hle : 1 ≤ pScaleT n ρ t c z.1 := pScaleT_one_le
    nlinarith [hd1, h1, hd]
  · have hcoord : (pPathA n ρ t c z.1) 0 = pScaleT n ρ t c z.1 * z.1.1 0 := by
      unfold pPathA
      rw [coord_add_smul n hc]
    rw [hcoord] at h2
    have hle : 1 ≤ pScaleT n ρ t c z.1 := pScaleT_one_le
    nlinarith [h2, hle]

/-- The endpoint of the homotopy lies in the complement of the half-ball. -/
lemma pPath_one_mem (n : ℕ) {ρ : ℝ} {c : EuclideanSpace ℝ (Fin (n + 1))} (hc : c 0 = 0)
    (hρ : 0 < ρ) (y : pSpace n c) : pPath n ρ 1 c hc y ∈ pSet n c ρ := by
  rintro ⟨h1, h2⟩
  rw [pPath_coe] at h1
  have hd : 0 < dist y.1 c := pSpace_dist_pos y
  have h2' : dist (pPathA n ρ 1 c y) c = max (dist y.1 c) (2 * ρ) := by
    rw [dist_pPathA, pScaleT_one, pScale_mul hd]
  have h3 : 2 * ρ ≤ ρ := le_trans (le_max_right _ _) (by rw [← h2']; exact h1)
  linarith

/-! ## Continuity -/

lemma continuous_pScale (n : ℕ) (ρ : ℝ) (c : EuclideanSpace ℝ (Fin (n + 1))) :
    Continuous (pScale n ρ c) := by
  have h1 : Continuous fun y : pSpace n c => dist y.1 c := by fun_prop
  have h2 : Continuous fun y : pSpace n c => (2 * ρ) * (dist y.1 c)⁻¹ :=
    continuous_const.mul (h1.inv₀ (fun y => ne_of_gt (pSpace_dist_pos y)))
  unfold pScale
  exact continuous_const.max (by simpa only [div_eq_mul_inv] using h2)

lemma continuous_pPathA (n : ℕ) (ρ : ℝ) (c : EuclideanSpace ℝ (Fin (n + 1))) :
    Continuous fun q : ℝ × pSpace n c => pPathA n ρ q.1 c q.2 := by
  have h1 : Continuous fun q : ℝ × pSpace n c => pScale n ρ c q.2 :=
    (continuous_pScale n ρ c).comp (by fun_prop)
  have ht : Continuous fun q : ℝ × pSpace n c => q.1 := continuous_fst
  have h3 : Continuous fun q : ℝ × pSpace n c => pScaleT n ρ q.1 c q.2 := by
    unfold pScaleT
    exact continuous_const.max (continuous_const.add (ht.mul (h1.sub continuous_const)))
  have h4 : Continuous fun q : ℝ × pSpace n c => q.2.1 - c := by fun_prop
  unfold pPathA
  exact continuous_const.add (h3.smul h4)

/-- **The model vanishing, punctured at the boundary point.** -/
theorem isZero_relChains_punctured_boundary_halfBall (n : ℕ) (c : EuclideanSpace ℝ (Fin (n + 1)))
    (hc : c 0 = 0) (ρ : ℝ) (hρ : 0 < ρ) :
    IsZero ((Work.Cohomology.relChains (TopCat.of (pSpace n c)) (pSet n c ρ)).homology n) := by
  classical
  -- the retraction, at the endpoint of the homotopy
  have hpathY : Continuous fun y : pSpace n c => pPath n ρ 1 c hc y := by
    have hb : Continuous fun y : pSpace n c => pPathA n ρ 1 c y :=
      (continuous_pPathA n ρ c).comp (continuous_const.prodMk continuous_id)
    unfold pPath
    exact Continuous.subtype_mk hb (fun y => ⟨by
        unfold pPathA
        rw [coord_add_smul n hc]
        exact mul_nonneg (le_of_lt pScaleT_pos) y.2.1,
      pPathA_ne (pSpace_dist_pos y)⟩)
  let g : TopCat.of (pSpace n c) ⟶ TopCat.of (pSet n c ρ) := TopCat.ofHom
    ⟨fun y => ⟨pPath n ρ 1 c hc y, pPath_one_mem n hc hρ y⟩,
      Continuous.subtype_mk hpathY (fun y => pPath_one_mem n hc hρ y)⟩
  let Hmap : C(↑unitInterval × pSpace n c, pSpace n c) :=
    ⟨fun q => pPath n ρ (q.1 : ℝ) c hc q.2, by
      have h2 : Continuous fun q : ↑unitInterval × pSpace n c => ((q.1 : ℝ), q.2) := by fun_prop
      have h1 : Continuous fun q : ↑unitInterval × pSpace n c => pPathA n ρ (q.1 : ℝ) c q.2 :=
        (continuous_pPathA n ρ c).comp h2
      unfold pPath
      exact Continuous.subtype_mk h1 (fun q => ⟨by
          unfold pPathA
          rw [coord_add_smul n hc]
          exact mul_nonneg (le_of_lt pScaleT_pos) q.2.2.1,
        pPathA_ne (pSpace_dist_pos q.2)⟩)⟩
  have hY : TopCat.Homotopy (𝟙 (TopCat.of (pSpace n c)))
      (g ≫ Work.Cohomology.subtypeIncl (TopCat.of (pSpace n c)) (pSet n c ρ)) :=
    ContinuousMap.Homotopy.mk Hmap
      (fun y => by
        apply Subtype.ext
        show pPathA n ρ 0 c y = y.1
        unfold pPathA
        rw [pScaleT_zero, one_smul]
        abel)
      (fun y => rfl)
  have hpathZm : Continuous fun q : ↑unitInterval × (TopCat.of (pSet n c ρ)) =>
      pPath n ρ (q.1 : ℝ) c hc q.2.1 := by
    have h3 : Continuous fun q : ↑unitInterval × (TopCat.of (pSet n c ρ)) =>
        ((q.1 : ℝ), q.2.1) := by fun_prop
    have h2 : Continuous fun q : ↑unitInterval × (TopCat.of (pSet n c ρ)) =>
        pPathA n ρ (q.1 : ℝ) c q.2.1 := (continuous_pPathA n ρ c).comp h3
    unfold pPath
    exact Continuous.subtype_mk h2 (fun q => ⟨by
        unfold pPathA
        rw [coord_add_smul n hc]
        exact mul_nonneg (le_of_lt pScaleT_pos) q.2.1.2.1,
      pPathA_ne (pSpace_dist_pos q.2.1)⟩)
  let hZm : C(↑unitInterval × (TopCat.of (pSet n c ρ)), TopCat.of (pSet n c ρ)) :=
    ⟨fun q => ⟨pPath n ρ (q.1 : ℝ) c hc q.2.1, pPath_mem n hc q.1.2.1 q.2⟩,
      Continuous.subtype_mk hpathZm (fun q => pPath_mem n hc q.1.2.1 q.2)⟩
  have hZhom : TopCat.Homotopy (𝟙 (TopCat.of (pSet n c ρ)))
      (Work.Cohomology.subtypeIncl (TopCat.of (pSpace n c)) (pSet n c ρ) ≫ g) :=
    ContinuousMap.Homotopy.mk hZm
      (fun z => by
        unfold hZm
        apply Subtype.ext
        apply Subtype.ext
        show pPathA n ρ 0 c z.1 = z.1.1
        unfold pPathA
        rw [pScaleT_zero, one_smul]
        abel)
      (fun z => rfl)
  exact isZero_relChains_of_homotopyEquiv_incl g hZhom.symm hY.symm n

end

end Work.Orient.Boundary
