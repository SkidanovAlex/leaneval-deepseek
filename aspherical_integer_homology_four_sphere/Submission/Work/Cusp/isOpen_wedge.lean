/-
# The four wedges of the perimeter parameter are open

The filling disk of the Dehn filling is the square `Sq = [-1,1]²` of `Work.Cusp.Basic`, with the
layer parameter `nrm p = ‖p‖∞ = max(|p 0|, |p 1|)` and the perimeter parameter
`u p = uPerim (bnd p)`, the arclength coordinate (normalised to total length `1`) of the ray
through `p` along the boundary of the square, starting at the corner `(1,1)`.

`wedge k` (`Work.Cusp.Charts`) is the set of points whose direction has perimeter parameter in the
`k`-th quarter interval `(k/4, (k+1)/4)`.  Each `wedge k` is the open cone of directions between
two consecutive corners of the square:

* `wedge 0 = {p | |p 1| < p 0}`   (between the corners `(1,-1)` and `(1,1)`),
* `wedge 1 = {p | |p 0| < -p 1}`  (between `(1,-1)` and `(-1,-1)`),
* `wedge 2 = {p | |p 1| < -p 0}`  (between `(-1,-1)` and `(-1,1)`),
* `wedge 3 = {p | |p 0| < p 1}`   (between `(-1,1)` and `(1,1)`).

Each is cut out by the *strict* inequalities `±p 0 ± p 1 > 0` (the four points `p 0 ± p 1 = 0`,
i.e. the four corner rays, are exactly the directions with `u p ∈ {0, 1/4, 1/2, 3/4}`, which the
open quarter intervals exclude), hence open; the four equalities are this file's content, and
`isOpen_wedge` is the immediate consequence.

The two ingredients of the identification are:

* **forward** (`wedge k ⊆ cone`): for `p ≠ 0` the radial projection `bnd p` lies on `∂Sq`
  (`nrm_bnd`), so `bnd p = bndOfU (u p)` (`nrmu_bndOfU_uPerim`); the quarter interval containing
  `u p` selects the branch of `bndOfU`, which reads the direction of `p` off `u p` explicitly.
  Since `p = nrm p • bnd p` (`smul_bnd`) with `nrm p > 0`, one coordinate of `p` is `±nrm p` and
  the other is `nrm p` times a number of absolute value `< 1`.
* **backward** (`cone ⊆ wedge k`): in the cone `k` the maximum `nrm p` is the coordinate with the
  fixed sign, so `nrm p` and `bnd p` are known in closed form, the relevant branch of `uPerim`
  applies, and the resulting affine expression in `p` lies in the `k`-th quarter interval.
-/
import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.Charts
import Submission.Work.Cusp.nrm_bnd
import Submission.Work.Cusp.smul_bnd
import Submission.Work.Cusp.uPerim_mem
import Submission.Work.Cusp.nrm_u_injOn

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open scoped Real InnerProductSpace

namespace Work.Cusp

/-! ### Coordinate helpers -/

/-- Coordinates of `bnd p = (nrm p)⁻¹ • p`. -/
private lemma bnd_apply (p : E2) (i : Fin 2) : bnd p i = (nrm p)⁻¹ * p i := by
  simp [bnd]

/-- The identity `p = nrm p • bnd p` (`smul_bnd`) in coordinates. -/
private lemma apply_smul_bnd (p : E2) (i : Fin 2) : p i = nrm p * bnd p i := by
  have h := congrArg (fun x : E2 => x i) (smul_bnd p).symm
  simpa using h

/-- The coordinate functions on `E2` are continuous. -/
private lemma continuous_coord (i : Fin 2) : Continuous (fun p : E2 => p i) :=
  PiLp.continuous_apply 2 _ i

/-! ### The four branches of `bndOfU` on the quarter intervals -/

/-- `bndOfU` on the first quarter interval `[0, 1/4)`: the right edge of the square. -/
private lemma bndOfU_lt_quarter {v : ℝ} (h0 : 0 ≤ v) (h1 : v < 1 / 4) :
    bndOfU v = !₂[1, 1 - 8 * v] := by
  unfold bndOfU
  rw [(Int.fract_eq_self).mpr ⟨h0, by linarith⟩]
  rw [ite_eq_left h1]

/-- `bndOfU` on `[1/4, 1/2)`: the bottom edge of the square. -/
private lemma bndOfU_lt_half {v : ℝ} (h0 : 1 / 4 ≤ v) (h1 : v < 1 / 2) :
    bndOfU v = !₂[3 - 8 * v, -1] := by
  unfold bndOfU
  rw [(Int.fract_eq_self).mpr ⟨by linarith, by linarith⟩]
  rw [ite_eq_right (not_lt.mpr h0), ite_eq_left h1]

/-- `bndOfU` on `[1/2, 3/4)`: the left edge of the square. -/
private lemma bndOfU_lt_threequarter {v : ℝ} (h0 : 1 / 2 ≤ v) (h1 : v < 3 / 4) :
    bndOfU v = !₂[-1, 8 * v - 5] := by
  unfold bndOfU
  rw [(Int.fract_eq_self).mpr ⟨by linarith, by linarith⟩]
  rw [ite_eq_right (not_lt.mpr (by linarith : (1:ℝ) / 4 ≤ v)), ite_eq_right (not_lt.mpr h0),
    ite_eq_left h1]

/-- `bndOfU` on `[3/4, 1)`: the top edge of the square. -/
private lemma bndOfU_le_one {v : ℝ} (h0 : 3 / 4 ≤ v) (h1 : v < 1) :
    bndOfU v = !₂[8 * v - 7, 1] := by
  unfold bndOfU
  rw [(Int.fract_eq_self).mpr ⟨by linarith, h1⟩]
  rw [ite_eq_right (not_lt.mpr (by linarith : (1:ℝ) / 4 ≤ v)),
    ite_eq_right (not_lt.mpr (by linarith : (1:ℝ) / 2 ≤ v)), ite_eq_right (not_lt.mpr h0)]

/-! ### The four branches of `uPerim` on the edges of the square -/

/-- `uPerim` on the right edge `q 0 = 1`. -/
private lemma uPerim_of_eq_one {q : E2} (h : q 0 = 1) : uPerim q = (1 - q 1) / 8 := by
  rw [uPerim, ite_eq_left h]

/-- `uPerim` on the bottom edge `q 1 = -1`, off the corner `(1,-1)`. -/
private lemma uPerim_of_eq_neg_one_x {q : E2} (h0 : q 0 ≠ 1) (h1 : q 1 = -1) :
    uPerim q = (3 - q 0) / 8 := by
  rw [uPerim, ite_eq_right h0, ite_eq_left h1]

/-- `uPerim` on the left edge `q 0 = -1`, off the corners `(1,-1)` and `(-1,-1)`. -/
private lemma uPerim_of_eq_neg_one_y {q : E2} (h0 : q 0 ≠ 1) (h1 : q 1 ≠ -1) (h2 : q 0 = -1) :
    uPerim q = (5 + q 1) / 8 := by
  rw [uPerim, ite_eq_right h0, ite_eq_right h1, ite_eq_left h2]

/-- `uPerim` on the top edge `q 1 = 1`, off the three other corners. -/
private lemma uPerim_of_last {q : E2} (h0 : q 0 ≠ 1) (h1 : q 1 ≠ -1) (h2 : q 0 ≠ -1) :
    uPerim q = (7 + q 0) / 8 := by
  rw [uPerim, ite_eq_right h0, ite_eq_right h1, ite_eq_right h2]

/-! ### The four wedges are the four open cones -/

/-- **`wedge 0` is the cone over the right edge of the square.** -/
private lemma wedge_zero_of_mem (p : E2) (hp : p ∈ wedge (0 : Fin 4)) : |p 1| < p 0 := by
  rw [wedge] at hp
  simp only [Set.mem_ofPred_eq, Set.mem_Ioo] at hp
  norm_num at hp
  obtain ⟨hn, hm1, hm2⟩ := hp
  have hpne : p ≠ 0 := by
    intro h
    rw [h] at hn
    simp [nrm] at hn
  have hbnd : bnd p = bndOfU (u p) := (nrmu_bndOfU_uPerim (nrm_bnd hpne)).symm
  have hv : bndOfU (u p) = !₂[1, 1 - 8 * u p] := bndOfU_lt_quarter (le_of_lt hm1) hm2
  have hb0 : bnd p 0 = 1 := by rw [hbnd, hv]; simp
  have hb1 : bnd p 1 = 1 - 8 * u p := by rw [hbnd, hv]; simp
  have habs : |1 - 8 * u p| < 1 := by
    rw [abs_lt]
    constructor <;> linarith
  have hp0 : p 0 = nrm p := by rw [apply_smul_bnd p 0, hb0, mul_one]
  have hp1 : p 1 = nrm p * (1 - 8 * u p) := by rw [apply_smul_bnd p 1, hb1]
  rw [hp0, hp1, abs_mul, abs_of_pos hn]
  calc nrm p * |1 - 8 * u p| < nrm p * 1 := mul_lt_mul_of_pos_left habs hn
    _ = nrm p := mul_one _

/-- **The cone over the right edge is `wedge 0`.** -/
private lemma mem_wedge_zero (p : E2) (hp : |p 1| < p 0) : p ∈ wedge (0 : Fin 4) := by
  have hg0 : 0 < p 0 := lt_of_le_of_lt (abs_nonneg _) hp
  have habs : |p 1| < |p 0| := by rwa [abs_of_nonneg (le_of_lt hg0)]
  have hnrm : nrm p = p 0 := by
    rw [nrm, max_eq_left (le_of_lt habs), abs_of_nonneg (le_of_lt hg0)]
  have hb0 : bnd p 0 = (nrm p)⁻¹ * p 0 := bnd_apply p 0
  have hb1 : bnd p 1 = (nrm p)⁻¹ * p 1 := bnd_apply p 1
  have hb0' : bnd p 0 = 1 := by rw [hb0, hnrm, inv_mul_cancel₀ (ne_of_gt hg0)]
  have hb1' : bnd p 1 = p 1 / p 0 := by rw [hb1, hnrm, div_eq_inv_mul]
  have hu : u p = (1 - p 1 / p 0) / 8 := by rw [u, uPerim_of_eq_one hb0', hb1']
  rw [wedge]
  simp only [Set.mem_ofPred_eq, Set.mem_Ioo]
  norm_num
  refine ⟨by rw [hnrm]; exact hg0, ?_⟩
  rw [hu]
  have hq0 : (-1:ℝ) < p 1 / p 0 := by
    rw [lt_div_iff₀ hg0]
    linarith [(abs_lt.mp hp).1]
  have hq1 : p 1 / p 0 < 1 := by
    rw [div_lt_iff₀ hg0]
    linarith [le_abs_self (p 1), hp]
  constructor <;> linarith

/-- **`wedge 1` is the cone over the bottom edge of the square.** -/
private lemma wedge_one_of_mem (p : E2) (hp : p ∈ wedge (1 : Fin 4)) : |p 0| < -p 1 := by
  rw [wedge] at hp
  simp only [Set.mem_ofPred_eq, Set.mem_Ioo] at hp
  norm_num at hp
  obtain ⟨hn, hm1, hm2⟩ := hp
  have hpne : p ≠ 0 := by
    intro h
    rw [h] at hn
    simp [nrm] at hn
  have hbnd : bnd p = bndOfU (u p) := (nrmu_bndOfU_uPerim (nrm_bnd hpne)).symm
  have hv : bndOfU (u p) = !₂[3 - 8 * u p, -1] := bndOfU_lt_half (le_of_lt hm1) hm2
  have hb0 : bnd p 0 = 3 - 8 * u p := by rw [hbnd, hv]; simp
  have hb1 : bnd p 1 = -1 := by rw [hbnd, hv]; simp
  have habs : |3 - 8 * u p| < 1 := by
    rw [abs_lt]
    constructor <;> linarith
  have hp0 : p 0 = nrm p * (3 - 8 * u p) := by rw [apply_smul_bnd p 0, hb0]
  have hp1 : p 1 = -nrm p := by rw [apply_smul_bnd p 1, hb1]; ring
  rw [hp0, hp1, neg_neg, abs_mul, abs_of_pos hn]
  calc nrm p * |3 - 8 * u p| < nrm p * 1 := mul_lt_mul_of_pos_left habs hn
    _ = nrm p := mul_one _

/-- **The cone over the bottom edge is `wedge 1`.** -/
private lemma mem_wedge_one (p : E2) (hp : |p 0| < -p 1) : p ∈ wedge (1 : Fin 4) := by
  have hg1 : 0 < -p 1 := lt_of_le_of_lt (abs_nonneg _) hp
  have hp1neg : p 1 < 0 := by linarith
  have habs : |p 0| < |p 1| := by rw [abs_of_neg hp1neg]; exact hp
  have hnrm : nrm p = -p 1 := by
    rw [nrm, max_eq_right (le_of_lt habs), abs_of_neg hp1neg]
  have hb0 : bnd p 0 = (nrm p)⁻¹ * p 0 := bnd_apply p 0
  have hb1 : bnd p 1 = (nrm p)⁻¹ * p 1 := bnd_apply p 1
  have hb1' : bnd p 1 = -1 := by
    rw [hb1, hnrm, inv_neg, neg_mul, inv_mul_cancel₀ (ne_of_lt hp1neg)]
  have hb0' : bnd p 0 = p 0 / (-p 1) := by rw [hb0, hnrm, div_eq_inv_mul]
  have hq : p 0 / (-p 1) ∈ Set.Ioo (-1) 1 := by
    constructor
    · rw [lt_div_iff₀ hg1]; linarith [(abs_lt.mp hp).1]
    · rw [div_lt_iff₀ hg1]; linarith [(abs_lt.mp hp).2]
  have hb0ne : bnd p 0 ≠ 1 := by
    rw [hb0']; intro h; linarith [hq.2, h]
  have hu : u p = (3 - p 0 / (-p 1)) / 8 := by
    rw [u, uPerim_of_eq_neg_one_x hb0ne hb1', hb0']
  rw [wedge]
  simp only [Set.mem_ofPred_eq, Set.mem_Ioo]
  norm_num
  refine ⟨by rw [hnrm]; exact hg1, ?_⟩
  rw [hu]
  constructor <;> linarith [hq.1, hq.2]

/-- **`wedge 2` is the cone over the left edge of the square.** -/
private lemma wedge_two_of_mem (p : E2) (hp : p ∈ wedge (2 : Fin 4)) : |p 1| < -p 0 := by
  rw [wedge] at hp
  simp only [Set.mem_ofPred_eq, Set.mem_Ioo] at hp
  norm_num at hp
  obtain ⟨hn, hm1, hm2⟩ := hp
  have hpne : p ≠ 0 := by
    intro h
    rw [h] at hn
    simp [nrm] at hn
  have hbnd : bnd p = bndOfU (u p) := (nrmu_bndOfU_uPerim (nrm_bnd hpne)).symm
  have hv : bndOfU (u p) = !₂[-1, 8 * u p - 5] := bndOfU_lt_threequarter (le_of_lt hm1) hm2
  have hb0 : bnd p 0 = -1 := by rw [hbnd, hv]; simp
  have hb1 : bnd p 1 = 8 * u p - 5 := by rw [hbnd, hv]; simp
  have habs : |8 * u p - 5| < 1 := by
    rw [abs_lt]
    constructor <;> linarith
  have hp0 : p 0 = -nrm p := by rw [apply_smul_bnd p 0, hb0]; ring
  have hp1 : p 1 = nrm p * (8 * u p - 5) := by rw [apply_smul_bnd p 1, hb1]
  rw [hp0, hp1, neg_neg, abs_mul, abs_of_pos hn]
  calc nrm p * |8 * u p - 5| < nrm p * 1 := mul_lt_mul_of_pos_left habs hn
    _ = nrm p := mul_one _

/-- **The cone over the left edge is `wedge 2`.** -/
private lemma mem_wedge_two (p : E2) (hp : |p 1| < -p 0) : p ∈ wedge (2 : Fin 4) := by
  have hg0 : 0 < -p 0 := lt_of_le_of_lt (abs_nonneg _) hp
  have hp0neg : p 0 < 0 := by linarith
  have habs : |p 1| < |p 0| := by rw [abs_of_neg hp0neg]; exact hp
  have hnrm : nrm p = -p 0 := by
    rw [nrm, max_eq_left (le_of_lt habs), abs_of_neg hp0neg]
  have hb0 : bnd p 0 = (nrm p)⁻¹ * p 0 := bnd_apply p 0
  have hb1 : bnd p 1 = (nrm p)⁻¹ * p 1 := bnd_apply p 1
  have hb0' : bnd p 0 = -1 := by
    rw [hb0, hnrm, inv_neg, neg_mul, inv_mul_cancel₀ (ne_of_lt hp0neg)]
  have hb1' : bnd p 1 = p 1 / (-p 0) := by rw [hb1, hnrm, div_eq_inv_mul]
  have hq : p 1 / (-p 0) ∈ Set.Ioo (-1) 1 := by
    constructor
    · rw [lt_div_iff₀ hg0]; linarith [(abs_lt.mp hp).1]
    · rw [div_lt_iff₀ hg0]; linarith [(abs_lt.mp hp).2]
  have hb1ne : bnd p 1 ≠ -1 := by
    rw [hb1']; intro h; linarith [hq.1, h]
  have hb0ne : bnd p 0 ≠ 1 := by rw [hb0']; norm_num
  have hu : u p = (5 + p 1 / (-p 0)) / 8 := by
    rw [u, uPerim_of_eq_neg_one_y hb0ne hb1ne hb0', hb1']
  rw [wedge]
  simp only [Set.mem_ofPred_eq, Set.mem_Ioo]
  norm_num
  refine ⟨by rw [hnrm]; exact hg0, ?_⟩
  rw [hu]
  constructor <;> linarith [hq.1, hq.2]

/-- **`wedge 3` is the cone over the top edge of the square.** -/
private lemma wedge_three_of_mem (p : E2) (hp : p ∈ wedge (3 : Fin 4)) : |p 0| < p 1 := by
  rw [wedge] at hp
  simp only [Set.mem_ofPred_eq, Set.mem_Ioo] at hp
  norm_num at hp
  obtain ⟨hn, hm1, hm2⟩ := hp
  have hpne : p ≠ 0 := by
    intro h
    rw [h] at hn
    simp [nrm] at hn
  have hbnd : bnd p = bndOfU (u p) := (nrmu_bndOfU_uPerim (nrm_bnd hpne)).symm
  have hv : bndOfU (u p) = !₂[8 * u p - 7, 1] := bndOfU_le_one (le_of_lt hm1) hm2
  have hb0 : bnd p 0 = 8 * u p - 7 := by rw [hbnd, hv]; simp
  have hb1 : bnd p 1 = 1 := by rw [hbnd, hv]; simp
  have habs : |8 * u p - 7| < 1 := by
    rw [abs_lt]
    constructor <;> linarith
  have hp0 : p 0 = nrm p * (8 * u p - 7) := by rw [apply_smul_bnd p 0, hb0]
  have hp1 : p 1 = nrm p := by rw [apply_smul_bnd p 1, hb1, mul_one]
  rw [hp0, hp1, abs_mul, abs_of_pos hn]
  calc nrm p * |8 * u p - 7| < nrm p * 1 := mul_lt_mul_of_pos_left habs hn
    _ = nrm p := mul_one _

/-- **The cone over the top edge is `wedge 3`.** -/
private lemma mem_wedge_three (p : E2) (hp : |p 0| < p 1) : p ∈ wedge (3 : Fin 4) := by
  have hg1 : 0 < p 1 := lt_of_le_of_lt (abs_nonneg _) hp
  have habs : |p 0| < |p 1| := by rw [abs_of_pos hg1]; exact hp
  have hnrm : nrm p = p 1 := by
    rw [nrm, max_eq_right (le_of_lt habs), abs_of_pos hg1]
  have hb0 : bnd p 0 = (nrm p)⁻¹ * p 0 := bnd_apply p 0
  have hb1 : bnd p 1 = (nrm p)⁻¹ * p 1 := bnd_apply p 1
  have hb1' : bnd p 1 = 1 := by rw [hb1, hnrm, inv_mul_cancel₀ (ne_of_gt hg1)]
  have hb0' : bnd p 0 = p 0 / p 1 := by rw [hb0, hnrm, div_eq_inv_mul]
  have hq : p 0 / p 1 ∈ Set.Ioo (-1) 1 := by
    constructor
    · rw [lt_div_iff₀ hg1]; linarith [(abs_lt.mp hp).1]
    · rw [div_lt_iff₀ hg1]; linarith [(abs_lt.mp hp).2]
  have hb0ne1 : bnd p 0 ≠ 1 := by rw [hb0']; intro h; linarith [hq.2, h]
  have hb0ne2 : bnd p 0 ≠ -1 := by rw [hb0']; intro h; linarith [hq.1, h]
  have hb1ne : bnd p 1 ≠ -1 := by rw [hb1']; norm_num
  have hu : u p = (7 + p 0 / p 1) / 8 := by
    rw [u, uPerim_of_last hb0ne1 hb1ne hb0ne2, hb0']
  rw [wedge]
  simp only [Set.mem_ofPred_eq, Set.mem_Ioo]
  norm_num
  refine ⟨by rw [hnrm]; exact hg1, ?_⟩
  rw [hu]
  constructor <;> linarith [hq.1, hq.2]

/-- **The four wedges are the four open cones of the square.** -/
theorem wedge_zero_eq : wedge (0 : Fin 4) = {p : E2 | |p 1| < p 0} :=
  Set.Subset.antisymm (fun _ hp => wedge_zero_of_mem _ hp) fun _ hp => mem_wedge_zero _ hp

theorem wedge_one_eq : wedge (1 : Fin 4) = {p : E2 | |p 0| < -p 1} :=
  Set.Subset.antisymm (fun _ hp => wedge_one_of_mem _ hp) fun _ hp => mem_wedge_one _ hp

theorem wedge_two_eq : wedge (2 : Fin 4) = {p : E2 | |p 1| < -p 0} :=
  Set.Subset.antisymm (fun _ hp => wedge_two_of_mem _ hp) fun _ hp => mem_wedge_two _ hp

theorem wedge_three_eq : wedge (3 : Fin 4) = {p : E2 | |p 0| < p 1} :=
  Set.Subset.antisymm (fun _ hp => wedge_three_of_mem _ hp) fun _ hp => mem_wedge_three _ hp

/-! ### The cones are open -/

/-- `{p | |p 1| < p 0}` is the intersection of the two open half planes `p 1 < p 0` and
`-p 1 < p 0`. -/
private lemma isOpen_cone_zero : IsOpen {p : E2 | |p 1| < p 0} := by
  rw [show ({p : E2 | |p 1| < p 0} : Set E2) = {p | p 1 < p 0} ∩ {p | -p 1 < p 0} from by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, abs_lt]
    constructor
    · intro h; exact ⟨h.2, by linarith [h.1]⟩
    · intro h; exact ⟨by linarith [h.2], h.1⟩]
  exact (isOpen_lt (continuous_coord 1) (continuous_coord 0)).inter
    (isOpen_lt (continuous_coord 1).neg (continuous_coord 0))

private lemma isOpen_cone_one : IsOpen {p : E2 | |p 0| < -p 1} := by
  rw [show ({p : E2 | |p 0| < -p 1} : Set E2) = {p | p 0 < -p 1} ∩ {p | -p 0 < -p 1} from by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, abs_lt]
    constructor
    · intro h; exact ⟨h.2, by linarith [h.1]⟩
    · intro h; exact ⟨by linarith [h.2], h.1⟩]
  exact (isOpen_lt (continuous_coord 0) (continuous_coord 1).neg).inter
    (isOpen_lt (continuous_coord 0).neg (continuous_coord 1).neg)

private lemma isOpen_cone_two : IsOpen {p : E2 | |p 1| < -p 0} := by
  rw [show ({p : E2 | |p 1| < -p 0} : Set E2) = {p | p 1 < -p 0} ∩ {p | -p 1 < -p 0} from by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, abs_lt]
    constructor
    · intro h; exact ⟨h.2, by linarith [h.1]⟩
    · intro h; exact ⟨by linarith [h.2], h.1⟩]
  exact (isOpen_lt (continuous_coord 1) (continuous_coord 0).neg).inter
    (isOpen_lt (continuous_coord 1).neg (continuous_coord 0).neg)

private lemma isOpen_cone_three : IsOpen {p : E2 | |p 0| < p 1} := by
  rw [show ({p : E2 | |p 0| < p 1} : Set E2) = {p | p 0 < p 1} ∩ {p | -p 0 < p 1} from by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, abs_lt]
    constructor
    · intro h; exact ⟨h.2, by linarith [h.1]⟩
    · intro h; exact ⟨by linarith [h.2], h.1⟩]
  exact (isOpen_lt (continuous_coord 0) (continuous_coord 1)).inter
    (isOpen_lt (continuous_coord 0).neg (continuous_coord 1))

private lemma isOpen_wedge_zero : IsOpen (wedge (0 : Fin 4)) := by
  rw [wedge_zero_eq]; exact isOpen_cone_zero

private lemma isOpen_wedge_one : IsOpen (wedge (1 : Fin 4)) := by
  rw [wedge_one_eq]; exact isOpen_cone_one

private lemma isOpen_wedge_two : IsOpen (wedge (2 : Fin 4)) := by
  rw [wedge_two_eq]; exact isOpen_cone_two

private lemma isOpen_wedge_three : IsOpen (wedge (3 : Fin 4)) := by
  rw [wedge_three_eq]; exact isOpen_cone_three

/-- **The requested statement: each wedge of the perimeter parameter is open.** -/
theorem isOpen_wedge (k : Fin 4) : IsOpen (wedge k) := by
  fin_cases k
  · exact isOpen_wedge_zero
  · exact isOpen_wedge_one
  · exact isOpen_wedge_two
  · exact isOpen_wedge_three

end Work.Cusp
