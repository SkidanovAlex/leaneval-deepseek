import Mathlib
import Submission.E2cGeom
import Submission.DirCycle
import Submission.DirSet
import Submission.E2bAssembly
import Submission.E2bParam
import Submission.SpineGaps

/-!
# E2c parameters: B, δ, u, A for the DStar deformation + FatStar geometry

`Submission.E2c` (the Pólya/Hankel wiring) instantiates
`Submission.DStar.deformation_star` with parameters `A B δ u` chosen so that
*the whole deformed contour lies inside `FatStar S ε`* (the set where the
`HedgehogBound` polynomials are small) and the big circle `C(0, e^B)` is
large enough for the circle-moment identity
(`Submission.PolyMoment.cMomentMatrix_eq_circleIntegral`).

This module produces those parameters (per DESIGN NOTE 64):

    S    the finite conjugate set (`S = conjugateValues α` in the engine);
    ε    > 0, the fattening radius from `HedgehogBound S`;
    R0   > 0, the Taylor-radius reciprocal (circle radius must exceed `R0`).

with the choices

    ℓ_j      := dirSpikeLen S (dirX S hlen0 j)      (length of spike j)
    rad_j    := ℓ_j + ε/2
    u j      := Real.log (rad_j)        (so exp (u j) = rad_j; hug: exp(u j)−ℓ_j = ε/2)
    B        := Real.log (L0 + ε/2 + max 1 R0),   L0 := maxEndNorm S
    A        := Real.log (ε/2)          (so exp A = ε/2 ≤ ε; A ≤ u j ∀j)
    δ        := from `E2bParam.exists_delta_lt` shrunk below
                1, (x_0+π)/2 and ε/(4·(L0+ε/2)), so that
                hsep/hwrap/hδx0 hold and 2·(L0+ε/2)·δ ≤ ε/2 (⟹ huδ for all j).

The statements below are exactly the hypotheses consumed by
`DStar.deformation_star` and by `E2cGeom.fatStar_of_rot_point` /
`fatStar_gap_point`, keyed to the caller-supplied `hlen0 : 0 < (dirList S).length`.
-/

noncomputable section

open scoped Real Polynomial Topology BigOperators

namespace Submission.E2cParam

open Submission.E2cGeom
open Submission.DirSet
open Submission.DirCycle
open Submission.E2bAssembly
open Submission.E2bParam
open Submission.SpineGaps

/-- The maximal norm of a spike endpoint of `star S`. -/
def maxEndNorm (S : Finset ℂ) : ℝ :=
  sSup {r : ℝ | ∃ w ∈ spikeEndpoints S, r = ‖w‖}

/-- The radius of the cap in direction `x_j`: spike length plus `ε/2`. -/
def radius (S : Finset ℂ) (hlen0 : 0 < (dirList S).length) (ε : ℝ) (j : ℕ) : ℝ :=
  dirSpikeLen S (dirX S hlen0 j) + ε / 2

/-- The `u` parameter: `Real.log (radius)`, so `Real.exp (u j) = radius j`. -/
def uOf (S : Finset ℂ) (hlen0 : 0 < (dirList S).length) (ε : ℝ) (j : ℕ) : ℝ :=
  Real.log (radius S hlen0 ε j)

/-- The `B` parameter: `log` of a quantity above every spike radius and `R0`. -/
def BOf (S : Finset ℂ) (ε R0 : ℝ) : ℝ :=
  Real.log (maxEndNorm S + ε / 2 + max 1 R0)

/-- The `A` parameter: `log (ε/2)`. -/
def AOf (ε : ℝ) : ℝ := Real.log (ε / 2)

/-- The global bound `L0 + ε/2` for all spike radii. -/
def radBound (S : Finset ℂ) (ε : ℝ) : ℝ := maxEndNorm S + ε / 2

/-- `wrapGap` of the direction list equals `2π + x_0 − x_{s−1}` in `get`-form. -/
lemma wrapGap_dirList_eq (S : Finset ℂ) (hlen0 : 0 < (dirList S).length) :
    wrapGap (dirList S) =
      2 * Real.pi + (dirList S).get ⟨0, hlen0⟩ -
        (dirList S).get ⟨(dirList S).length - 1, by omega⟩ := by
  classical
  unfold wrapGap
  have hneL : dirList S ≠ [] := by
    intro h
    have : (dirList S).length = 0 := by simp [h]
    omega
  have hhead_gen : ∀ (l : List ℝ), l ≠ [] → ∀ (h0 : 0 < l.length),
      l.head! = l.get ⟨0, h0⟩ := by
    intro l hne h0
    rcases List.exists_cons_of_ne_nil hne with ⟨a, t, rfl⟩
    simp
  have hlast_gen : ∀ (l : List ℝ), l ≠ [] → ∀ (h0 : 0 < l.length),
      l.getLast! = l.get ⟨l.length - 1, Nat.sub_lt h0 (by norm_num : (1 : ℕ) > 0)⟩ := by
    intro l hne h0
    rw [List.getLast!_eq_getLast?_getD]
    rw [List.getLast?_eq_some_getLast hne]
    simp
    rw [List.getLast_eq_getElem]
  rw [hhead_gen (dirList S) hneL hlen0]
  rw [hlast_gen (dirList S) hneL hlen0]

/-- All members of the direction list lie in `(−π, π]`. -/
lemma dirList_mem_Ioc_all (S : Finset ℂ) : ∀ x ∈ dirList S, x ∈ Set.Ioc (-Real.pi) Real.pi := by
  intro x hx
  rcases List.mem_iff_get.mp hx with ⟨i, rfl⟩
  exact dirList_get_mem_Ioc S i

/-- The wrap gap of the direction list is positive. -/
lemma wrapGap_dirList_pos (S : Finset ℂ) (hne : (dirSet S).Nonempty) :
    0 < wrapGap (dirList S) := by
  classical
  have hlen0 : 0 < (dirList S).length := by
    rw [dirList_length]
    exact Finset.card_pos.mpr hne
  rw [wrapGap_dirList_eq S hlen0]
  have hx0 : (dirList S).get ⟨0, hlen0⟩ ∈ Set.Ioc (-Real.pi) Real.pi :=
    dirList_get_mem_Ioc S ⟨0, hlen0⟩
  have hlast : (dirList S).get ⟨(dirList S).length - 1, by omega⟩ ∈
      Set.Ioc (-Real.pi) Real.pi :=
    dirList_get_mem_Ioc S ⟨(dirList S).length - 1, by omega⟩
  linarith [hx0.1, hlast.2]

/-- `dirX S hlen0 j` is a direction of the hedgehog (an argument of some
spike endpoint). -/
lemma dirX_mem_dirSet (S : Finset ℂ) (hlen0 : 0 < (dirList S).length) {j : ℕ}
    (hj : j < (dirList S).length) : dirX S hlen0 j ∈ dirSet S := by
  rw [dirX_of_lt S hlen0 hj]
  exact (dirList_mem_iff S ((dirList S).get ⟨j, hj⟩)).mp (List.get_mem (dirList S) ⟨j, hj⟩)

/-- The spike length in a direction is nonnegative. -/
lemma dirSpikeLen_nonneg (S : Finset ℂ) (x : ℝ) : 0 ≤ dirSpikeLen S x := by
  classical
  by_cases hx : x ∈ dirSet S
  · rcases dirSpikeLen_mem S hx with ⟨w, hw, hnorm⟩
    rw [← hnorm]
    exact norm_nonneg w
  · have hne : ¬ (dirEndpoints S x).Nonempty := by
      intro hn
      exact hx ((mem_dirSet_iff_endpoint S x).mpr hn)
    unfold dirSpikeLen
    have hset : ({r : ℝ | ∃ w ∈ dirEndpoints S x, r = ‖w‖} : Set ℝ) = ∅ := by
      ext r
      constructor
      · rintro ⟨w, hw, hr⟩
        exfalso
        exact hne ⟨w, hw⟩
      · intro hr
        simpa using hr
    rw [hset]
    rw [Real.sSup_empty]

/-- Every spike endpoint has norm at most `maxEndNorm S`. -/
lemma norm_le_maxEndNorm (S : Finset ℂ) {w : ℂ} (hw : w ∈ spikeEndpoints S) :
    ‖w‖ ≤ maxEndNorm S := by
  classical
  let E : Finset ℝ := (spikeEndpoints S).image (fun z : ℂ => ‖z‖)
  have hEq : ({r : ℝ | ∃ z ∈ spikeEndpoints S, r = ‖z‖} : Set ℝ) = (E : Set ℝ) := by
    ext r
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨z, hz, rfl⟩)
    · intro hr
      rcases Finset.mem_image.mp (Finset.mem_coe.mp hr) with ⟨z, hz, rfl⟩
      exact ⟨z, hz, rfl⟩
  unfold maxEndNorm
  rw [hEq]
  exact le_csSup E.bddAbove (Finset.mem_image.mpr ⟨w, hw, rfl⟩)

/-- Every direction-`x` spike is at most as long as the maximal endpoint
norm. -/
lemma dirSpikeLen_le_maxEndNorm (S : Finset ℂ) {x : ℝ} (hx : x ∈ dirSet S) :
    dirSpikeLen S x ≤ maxEndNorm S := by
  classical
  rcases dirSpikeLen_mem S hx with ⟨w, hw, hnorm⟩
  rw [← hnorm]
  exact norm_le_maxEndNorm S ((mem_dirEndpoints_iff S x w).mp hw).1

/-- `maxEndNorm S` is nonnegative. -/
lemma maxEndNorm_nonneg (S : Finset ℂ) : 0 ≤ maxEndNorm S := by
  classical
  let E : Finset ℝ := (spikeEndpoints S).image (fun w : ℂ => ‖w‖)
  have hEq : ({r : ℝ | ∃ w ∈ spikeEndpoints S, r = ‖w‖} : Set ℝ) = (E : Set ℝ) := by
    ext r
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨w, hw, rfl⟩)
    · intro hr
      rcases Finset.mem_image.mp (Finset.mem_coe.mp hr) with ⟨w, hw, rfl⟩
      exact ⟨w, hw, rfl⟩
  unfold maxEndNorm
  rw [hEq]
  by_cases hE : E.Nonempty
  · rcases hE with ⟨e, he⟩
    have hnonneg : 0 ≤ e := by
      rcases Finset.mem_image.mp he with ⟨w, hw, rfl⟩
      exact norm_nonneg w
    exact le_trans hnonneg (le_csSup E.bddAbove (Finset.mem_coe.mpr he))
  · have hEempty : (E : Set ℝ) = ∅ := by
      ext r
      constructor
      · intro hr
        exfalso
        exact hE ⟨r, Finset.mem_coe.mp hr⟩
      · intro hr
        simpa using hr
    rw [hEempty]
    rw [Real.sSup_empty]

/-- The per-direction radius is positive. -/
lemma radius_pos (S : Finset ℂ) (hlen0 : 0 < (dirList S).length) {ε : ℝ} (hε : 0 < ε)
    (j : ℕ) : 0 < radius S hlen0 ε j := by
  unfold radius
  have hℓ : 0 ≤ dirSpikeLen S (dirX S hlen0 j) := dirSpikeLen_nonneg S (dirX S hlen0 j)
  linarith

/-- `Real.exp (u j) = radius j`. -/
lemma exp_uOf (S : Finset ℂ) (hlen0 : 0 < (dirList S).length) {ε : ℝ} (hε : 0 < ε)
    (j : ℕ) : Real.exp (uOf S hlen0 ε j) = radius S hlen0 ε j := by
  unfold uOf
  exact Real.exp_log (radius_pos S hlen0 hε j)

/-- **hug**: `exp (u j) − dirSpikeLen S (dirX j) ≤ ε/2`. -/
lemma exp_uOf_sub_spikeLen_le_half (S : Finset ℂ) (hlen0 : 0 < (dirList S).length)
    {ε : ℝ} (hε : 0 < ε) (j : ℕ) :
    Real.exp (uOf S hlen0 ε j) - dirSpikeLen S (dirX S hlen0 j) ≤ ε / 2 := by
  rw [exp_uOf S hlen0 hε j]
  unfold radius
  linarith

/-- **hshort (per direction)**: every endpoint on the ray of `x_j` is shorter
than the cap radius. -/
lemma short_of_uOf (S : Finset ℂ) (hlen0 : 0 < (dirList S).length) {ε : ℝ} (hε : 0 < ε)
    {j : ℕ} (hj : j < (dirList S).length) {w : ℂ} (hw : w ∈ spikeEndpoints S)
    (hwarg : Complex.arg w = dirX S hlen0 j) :
    ‖w‖ < Real.exp (uOf S hlen0 ε j) := by
  rw [exp_uOf S hlen0 hε j]
  unfold radius
  have hwdir : w ∈ dirEndpoints S (dirX S hlen0 j) := by
    rw [mem_dirEndpoints_iff]
    exact ⟨hw, hwarg⟩
  have hle : ‖w‖ ≤ dirSpikeLen S (dirX S hlen0 j) := norm_le_dirSpikeLen S hwdir
  linarith

/-- `A ≤ u j` for every `j < s`. -/
lemma AOf_le_uOf (S : Finset ℂ) (hlen0 : 0 < (dirList S).length) {ε : ℝ} (hε : 0 < ε)
    {j : ℕ} (hj : j < (dirList S).length) : AOf ε ≤ uOf S hlen0 ε j := by
  unfold AOf uOf radius
  apply Real.log_le_log (x := ε / 2)
    (y := dirSpikeLen S (dirX S hlen0 j) + ε / 2)
  · positivity
  · have hℓ : 0 ≤ dirSpikeLen S (dirX S hlen0 j) := dirSpikeLen_nonneg S (dirX S hlen0 j)
    linarith

/-- `exp A = ε/2`. -/
lemma exp_AOf {ε : ℝ} (hε : 0 < ε) : Real.exp (AOf ε) = ε / 2 := by
  unfold AOf
  exact Real.exp_log (half_pos hε)

/-- **gap-arc smallness**: `exp A ≤ ε`. -/
lemma exp_AOf_le_eps {ε : ℝ} (hε : 0 < ε) : Real.exp (AOf ε) ≤ ε := by
  rw [exp_AOf hε]
  linarith

/-- `exp B = L0 + ε/2 + max 1 R0`. -/
lemma exp_BOf (S : Finset ℂ) {ε R0 : ℝ} (hε : 0 < ε) (hR0 : 0 < R0) :
    Real.exp (BOf S ε R0) = maxEndNorm S + ε / 2 + max 1 R0 := by
  unfold BOf
  apply Real.exp_log
  have hmn : 0 ≤ maxEndNorm S := maxEndNorm_nonneg S
  have hmax : 0 < max 1 R0 := lt_of_lt_of_le zero_lt_one (le_max_left 1 R0)
  linarith

/-- **hBigB**: every spike endpoint is strictly inside the big circle. -/
lemma hBigB_of_BOf (S : Finset ℂ) {ε R0 : ℝ} (hε : 0 < ε) (hR0 : 0 < R0) :
    ∀ w ∈ spikeEndpoints S, ‖w‖ < Real.exp (BOf S ε R0) := by
  intro w hw
  rw [exp_BOf S hε hR0]
  have hmn : 0 ≤ maxEndNorm S := maxEndNorm_nonneg S
  have hmax : 0 < max 1 R0 := lt_of_lt_of_le zero_lt_one (le_max_left 1 R0)
  have hle : ‖w‖ ≤ maxEndNorm S := norm_le_maxEndNorm S hw
  linarith

/-- **hub**: `u j ≤ B` for every `j < s`. -/
lemma uOf_le_BOf (S : Finset ℂ) (hlen0 : 0 < (dirList S).length) {ε R0 : ℝ}
    (hε : 0 < ε) (hR0 : 0 < R0) {j : ℕ} (hj : j < (dirList S).length) :
    uOf S hlen0 ε j ≤ BOf S ε R0 := by
  unfold uOf BOf radius
  apply Real.log_le_log (x := dirSpikeLen S (dirX S hlen0 j) + ε / 2)
    (y := maxEndNorm S + ε / 2 + max 1 R0)
  · have hℓ : 0 ≤ dirSpikeLen S (dirX S hlen0 j) := dirSpikeLen_nonneg S (dirX S hlen0 j)
    linarith
  · have hx : dirX S hlen0 j ∈ dirSet S := dirX_mem_dirSet S hlen0 hj
    have hℓ : dirSpikeLen S (dirX S hlen0 j) ≤ maxEndNorm S :=
      dirSpikeLen_le_maxEndNorm S hx
    have hmax : 0 ≤ max 1 R0 := le_trans zero_le_one (le_max_left 1 R0)
    linarith

/-- The big-circle radius exceeds `R0`. -/
lemma R0_lt_exp_BOf (S : Finset ℂ) {ε R0 : ℝ} (hε : 0 < ε) (hR0 : 0 < R0) :
    R0 < Real.exp (BOf S ε R0) := by
  rw [exp_BOf S hε hR0]
  have hmn : 0 ≤ maxEndNorm S := maxEndNorm_nonneg S
  have hε2 : 0 < ε / 2 := half_pos hε
  have hR0le : R0 ≤ max 1 R0 := le_max_right 1 R0
  linarith

/-- If `π` is a direction, it is the last one. -/
lemma last_dir_eq_pi_of_mem (S : Finset ℂ) (hlen0 : 0 < (dirList S).length)
    (hπ : Real.pi ∈ dirSet S) :
    (dirList S).get ⟨(dirList S).length - 1, by omega⟩ = Real.pi := by
  classical
  have hπlist : Real.pi ∈ dirList S := (dirList_mem_iff S Real.pi).mpr hπ
  rcases List.mem_iff_get.mp hπlist with ⟨i, hiπ⟩
  -- every entry is ≤ π, in particular the last one
  have hlast_le_pi : (dirList S).get ⟨(dirList S).length - 1, by omega⟩ ≤ Real.pi :=
    (dirList_get_mem_Ioc S ⟨(dirList S).length - 1, by omega⟩).2
  -- the last index is ≥ i, so `get i ≤ get last`
  have hi_last : i.val ≤ (dirList S).length - 1 := by
    have : i.val < (dirList S).length := i.isLt
    omega
  have hge : (dirList S).get ⟨(dirList S).length - 1, by omega⟩ ≤ (dirList S).get i := by
    rw [hiπ]
    exact hlast_le_pi
  have hle : (dirList S).get i ≤ (dirList S).get ⟨(dirList S).length - 1, by omega⟩ :=
    dirList_get_mono S (i := i) (j := ⟨(dirList S).length - 1, by omega⟩) hi_last
  rw [← hiπ]
  exact le_antisymm hge hle

/-- **hshortπ (last index)**: endpoints on the negative real axis are shorter
than the last cap radius. -/
lemma shortπ_last (S : Finset ℂ) (hlen0 : 0 < (dirList S).length) {ε : ℝ} (hε : 0 < ε)
    {w : ℂ} (hw : w ∈ spikeEndpoints S) (hwarg : Complex.arg w = Real.pi) :
    ‖w‖ < Real.exp (uOf S hlen0 ε ((dirList S).length - 1)) := by
  classical
  have hπdir : Real.pi ∈ dirSet S := by
    rw [dirSet]
    exact Finset.mem_image.mpr ⟨w, hw, hwarg⟩
  have hlast : (dirList S).get ⟨(dirList S).length - 1, by omega⟩ = Real.pi :=
    last_dir_eq_pi_of_mem S hlen0 hπdir
  have hlt : (dirList S).length - 1 < (dirList S).length := by omega
  have hwarg' : Complex.arg w = dirX S hlen0 ((dirList S).length - 1) := by
    calc
      Complex.arg w = Real.pi := hwarg
      _ = (dirList S).get ⟨(dirList S).length - 1, by omega⟩ := hlast.symm
      _ = (dirList S).get ⟨(dirList S).length - 1, hlt⟩ := by
        exact congrArg (fun e : Fin (dirList S).length => (dirList S).get e) (Fin.ext rfl)
      _ = dirX S hlen0 ((dirList S).length - 1) := (dirX_of_lt S hlen0 hlt).symm
  exact short_of_uOf S hlen0 hε (j := (dirList S).length - 1) hlt hw hwarg'

/-- **huδ for all directions** from the uniform bound
`2 · (L0 + ε/2) · δ ≤ ε/2`. -/
lemma huδ_of_radBound (S : Finset ℂ) (hlen0 : 0 < (dirList S).length) {ε δ : ℝ}
    (hε : 0 < ε) (hδ0 : 0 ≤ δ) (hbound : 2 * (radBound S ε) * δ ≤ ε / 2)
    {j : ℕ} (hj : j < (dirList S).length) :
    2 * Real.exp (uOf S hlen0 ε j) * δ ≤ ε / 2 := by
  rw [exp_uOf S hlen0 hε j]
  unfold radius
  change 2 * (maxEndNorm S + ε / 2) * δ ≤ ε / 2 at hbound
  have hx : dirX S hlen0 j ∈ dirSet S := dirX_mem_dirSet S hlen0 hj
  have hℓ : dirSpikeLen S (dirX S hlen0 j) ≤ maxEndNorm S := dirSpikeLen_le_maxEndNorm S hx
  have hle : 2 * (dirSpikeLen S (dirX S hlen0 j) + ε / 2) * δ ≤
      2 * (maxEndNorm S + ε / 2) * δ := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith : dirSpikeLen S (dirX S hlen0 j) + ε / 2 ≤
        maxEndNorm S + ε / 2) (by norm_num : (0 : ℝ) ≤ 2)) hδ0
  exact le_trans hle hbound

/-- **Existence of the angular half-width `δ`**: positive, `≤ 1`, below
`(x_0 + π)` (so `hδx0`), separating consecutive directions and the wrap gap,
and small enough that `2·(L0+ε/2)·δ ≤ ε/2` (so `huδ` holds in every
direction). -/
theorem exists_delta_geo (S : Finset ℂ) (hne : (dirSet S).Nonempty)
    {ε : ℝ} (hε : 0 < ε) {R0 : ℝ} (hR0 : 0 < R0) :
    let hlen0 : 0 < (dirList S).length := by
      rw [dirList_length]
      exact Finset.card_pos.mpr hne
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      δ < (dirList S).get ⟨0, hlen0⟩ + Real.pi ∧
      (∀ (j : ℕ) (hj : j + 1 < (dirList S).length),
        (dirList S).get ⟨j + 1, hj⟩ -
          (dirList S).get ⟨j, Nat.lt_trans (Nat.lt_succ_self j) hj⟩ > 2 * δ) ∧
      2 * Real.pi + (dirList S).get ⟨0, hlen0⟩ -
          (dirList S).get ⟨(dirList S).length - 1, by omega⟩ > 2 * δ ∧
      2 * (radBound S ε) * δ ≤ ε / 2 := by
  classical
  let hlen0 : 0 < (dirList S).length := by
    rw [dirList_length]
    exact Finset.card_pos.mpr hne
  have hneL : dirList S ≠ [] := by
    intro h
    have : (dirList S).length = 0 := by simp [h]
    omega
  have hIoc : ∀ x ∈ dirList S, x ∈ Set.Ioc (-Real.pi) Real.pi := dirList_mem_Ioc_all S
  have hwrap : 0 < wrapGap (dirList S) := wrapGap_dirList_pos S hne
  have hx0 : (dirList S).get ⟨0, hlen0⟩ + Real.pi > 0 := by
    have hI := dirList_get_mem_Ioc S ⟨0, hlen0⟩
    linarith [hI.1]
  let c0 : ℝ := min (min 1 (ε / (4 * (radBound S ε)))) (((dirList S).get ⟨0, hlen0⟩ + Real.pi) / 2)
  have hc0pos : 0 < c0 := by
    dsimp [c0]
    have hbpos : 0 < radBound S ε := by
      dsimp [radBound]
      exact add_pos_of_nonneg_of_pos (maxEndNorm_nonneg S) (half_pos hε)
    have h4 : 0 < 4 * radBound S ε := by positivity
    have hε4 : 0 < ε / (4 * radBound S ε) := div_pos hε h4
    have hx0h : 0 < ((dirList S).get ⟨0, hlen0⟩ + Real.pi) / 2 := by positivity
    exact lt_min (lt_min (by norm_num : (0 : ℝ) < 1) hε4) hx0h
  rcases exists_delta_lt (dirList S) hneL (dirList_strict S) hIoc hwrap (ε := c0) hc0pos
    with ⟨δ, hδpos, hδlt, hsep, hwrapδ⟩
  refine ⟨δ, hδpos, ?_, ?_, hsep, ?_, ?_⟩
  · -- δ ≤ 1
    have h1 : δ < c0 := hδlt
    have hle1 : c0 ≤ 1 := by
      dsimp [c0]
      exact le_trans (min_le_left _ _) (min_le_left _ _)
    linarith
  · -- δ < x_0 + π
    have h1 : δ < c0 := hδlt
    have hle : c0 ≤ ((dirList S).get ⟨0, hlen0⟩ + Real.pi) / 2 := by
      dsimp [c0]
      exact min_le_right _ _
    have hhalf : ((dirList S).get ⟨0, hlen0⟩ + Real.pi) / 2 < (dirList S).get ⟨0, hlen0⟩ + Real.pi := by
      linarith [hx0]
    linarith
  · -- wrap gap in get-form
    rw [← wrapGap_dirList_eq S hlen0]
    exact hwrapδ
  · -- huδ bound
    have h1 : δ < c0 := hδlt
    have hle : c0 ≤ ε / (4 * radBound S ε) := by
      dsimp [c0]
      exact le_trans (min_le_left _ _) (min_le_right _ _)
    have hδle : δ ≤ ε / (4 * radBound S ε) := le_of_lt (lt_of_lt_of_le h1 hle)
    have hb0 : 0 ≤ radBound S ε := by
      dsimp [radBound]
      exact add_nonneg (maxEndNorm_nonneg S) (le_of_lt (half_pos hε))
    have hbpos : 0 < radBound S ε := by
      dsimp [radBound]
      exact add_pos_of_nonneg_of_pos (maxEndNorm_nonneg S) (half_pos hε)
    have hmul : 2 * radBound S ε * δ ≤ ε / 2 := by
      have hq : δ ≤ ε / (4 * radBound S ε) := hδle
      have hconv : 2 * radBound S ε * (ε / (4 * radBound S ε)) = ε / 2 := by
        field_simp [hbpos.ne']
        ring
      calc
        2 * radBound S ε * δ ≤ 2 * radBound S ε * (ε / (4 * radBound S ε)) := by
              exact mul_le_mul_of_nonneg_left hq (mul_nonneg (by norm_num) hb0)
        _ = ε / 2 := hconv
    exact hmul

end Submission.E2cParam

end
