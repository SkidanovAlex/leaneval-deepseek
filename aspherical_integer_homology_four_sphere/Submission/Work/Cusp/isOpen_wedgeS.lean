/-
# The `c`-shifted wedges of the perimeter parameter are open

`wedgeS c k` (`Work.Cusp.Charts`) is the set of points of the filling disk `Sq = [-1,1]²` whose
direction has perimeter parameter, *measured from the shifted cut at `u = frac c`*, in the `k`-th
quarter `(k/4, (k+1)/4)`:

`wedgeS c k = {p | 0 < nrm p ∧ Int.fract (u p - c) ∈ Ioo (k/4) ((k+1)/4)}`.

Equivalently (`arcSet`, the arithmetic lemma `interval_nonempty_iff_fract`) it is the set of points
whose perimeter parameter lies in the *arc of length `1/4`*

`u p ∈ Ioo (θ + m) (θ + 1/4 + m)`  for some `m : ℤ`,  where `θ = c + k/4`.

The direction of a point is the radial projection `bnd p ∈ ∂Sq`, and the perimeter parameter is a
coordinate on `∂Sq` (`uPerim (bndOfU t) = frac t`, `bndOfU (uPerim q) = q`); the arc of *directions*
cut out by the arc of parameters is an arc of `∂Sq` of length `1/4`, i.e. one edge of the square or
part of two consecutive edges.  The cone over such an arc is the *open* cone spanned by its two
bounding directions, and this is what the file proves:

`wedgeS c k = wedgeCone (bndOfU θ) (bndOfU (θ + 1/4))`,  `θ = c + k/4`,

whence `isOpen_wedgeS`, since `wedgeCone A B` is an intersection of two open half-planes.

The proof is organised as follows.

* `arcSet θ` is the set of points with `u p` in the arc `(θ, θ+1/4)`;  `coneOf θ` is the cone
  spanned by the two bounding directions `bndOfU θ`, `bndOfU (θ + 1/4)`.
* `arcSet θ = coneOf θ` for `θ ∈ [0, 1/4)` is the geometric content (`geo_quarter` together with
  the two branch formulas of `bndOfU` on the right and bottom edges, and the positive homogeneity
  of the cone): both bounding directions then lie on the right and bottom edges of the square.
* The two sides are periodic in `θ` with period `1` (`bndOfU_add_int`), and both are transported by
  the quarter turn `rot90` (`bndOfU_add_quarter`, `u (rot90 p) = frac (u p + 1/4)`), so the
  identity for an arbitrary `θ` follows from the case `θ ∈ [0, 1/4)` by shifting `θ` by quarters
  into that window.
* The final step `wedgeS c k = arcSet (c + k/4)` is the arithmetic of `Int.fract`.
-/
import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.Charts
import Submission.Work.Cusp.WedgeSCone
import Submission.Work.Cusp.nrm_bnd
import Submission.Work.Cusp.smul_bnd
import Submission.Work.Cusp.uPerim_mem
import Submission.Work.Cusp.bndOfU_uPerim
import Submission.Work.Cusp.uPerim_bndOfU
import Submission.Work.Cusp.nrm_bndOfU
import Submission.Work.Cusp.bndOfU_add_int
import Submission.Work.Cusp.bndOfU_add_quarter
import Submission.Work.Cusp.geo_quarter

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

namespace Work.Cusp

open scoped Real InnerProductSpace

/-! ### The arc of directions cut out by the shifted perimeter parameter -/

/-- The set of points `p ≠ 0` whose direction has perimeter parameter in the arc `(θ, θ+1/4)` of
length `1/4`, lifted to the universal cover: `u p ∈ Ioo (θ + m) (θ + 1/4 + m)` for some `m : ℤ`.
The condition `0 < nrm p` is exactly `p ≠ 0`. -/
private def arcSet (θ : ℝ) : Set E2 :=
  {p : E2 | 0 < nrm p ∧ ∃ m : ℤ, u p ∈ Set.Ioo (θ + m) (θ + 1/4 + m)}

/-- The open cone spanned by the two directions that bound the arc `(θ, θ + 1/4)`:  the directions
`bndOfU θ` and `bndOfU (θ + 1/4)` of `∂Sq`. -/
private def coneOf (θ : ℝ) : Set E2 :=
  wedgeCone (bndOfU θ) (bndOfU (θ + 1/4))

/-! ### The arithmetic of `Int.fract` and the arc -/

/-- An interval of length `1/4` meets an integer translate of itself: the condition
`x ∈ Ioo (θ+m) (θ+1/4+m)` depends only on the class of `x` modulo `1`, so it may be tested on
`Int.fract x`. -/
private lemma interval_nonempty_iff_fract (x θ : ℝ) :
    (∃ m : ℤ, x ∈ Set.Ioo (θ + m) (θ + 1/4 + m)) ↔
      (∃ m : ℤ, Int.fract x ∈ Set.Ioo (θ + m) (θ + 1/4 + m)) := by
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m - ⌊x⌋, ?_⟩
    have hx : x - (⌊x⌋ : ℝ) = Int.fract x := Int.self_sub_floor x
    have hcast : (((m - ⌊x⌋ : ℤ)) : ℝ) = (m : ℝ) - (⌊x⌋ : ℝ) := by push_cast; ring
    rw [Set.mem_Ioo] at hm ⊢
    constructor
    · rw [hcast]; linarith
    · rw [hcast]; linarith
  · rintro ⟨m, hm⟩
    refine ⟨m + ⌊x⌋, ?_⟩
    have hx : x = Int.fract x + (⌊x⌋ : ℝ) := by rw [Int.fract_add_floor]
    have hcast : (((m + ⌊x⌋ : ℤ)) : ℝ) = (m : ℝ) + (⌊x⌋ : ℝ) := by push_cast; ring
    rw [Set.mem_Ioo] at hm ⊢
    constructor
    · rw [hcast]; linarith
    · rw [hcast]; linarith

/-- Shifting the argument of the fractional part by `-1/4` shifts the arc by `+1/4`: the
condition `frac (x - 1/4) ∈ Ioo (θ+m) (θ+1/4+m)` says that `x` lies in `Ioo (θ+1/4+m) (θ+1/2+m)`,
i.e. that (the direction with parameter) `x` is the *next* arc after `(θ, θ+1/4)`. -/
private lemma exists_fract_sub_quarter (x θ : ℝ) :
    (∃ m : ℤ, Int.fract (x - 1/4) ∈ Set.Ioo (θ + m) (θ + 1/4 + m)) ↔
      (∃ m : ℤ, x ∈ Set.Ioo ((θ + 1/4) + m) ((θ + 1/4) + 1/4 + m)) := by
  rw [← interval_nonempty_iff_fract (x - 1/4) θ]
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, by rw [Set.mem_Ioo] at hm ⊢; constructor <;> linarith⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, by rw [Set.mem_Ioo] at hm ⊢; constructor <;> linarith⟩

/-- For `0 ≤ x < 1` and `0 ≤ θ` with `θ + 1/4 ≤ 1` the lifted arc condition
`∃ m, x ∈ Ioo (θ+m) (θ+1/4+m)` is the plain condition `x ∈ Ioo θ (θ+1/4)`: only the translate
`m = 0` can meet `[0,1)`. -/
private lemma exists_interval_reduce {x θ : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hθ0 : 0 ≤ θ) (hθ1 : θ + 1/4 ≤ 1) :
    (∃ m : ℤ, x ∈ Set.Ioo (θ + m) (θ + 1/4 + m)) ↔ x ∈ Set.Ioo θ (θ + 1/4) := by
  constructor
  · rintro ⟨m, hm⟩
    rw [Set.mem_Ioo] at hm ⊢
    have hm0 : m = 0 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · exfalso
        have hmle : (m : ℝ) ≤ -1 := by
          have : m ≤ -1 := by omega
          exact_mod_cast this
        linarith
      · exfalso
        have hmge : (1 : ℝ) ≤ (m : ℝ) := by
          have : (1 : ℤ) ≤ m := by omega
          exact_mod_cast this
        linarith
    subst hm0
    simpa using hm
  · intro hx
    exact ⟨0, by simpa using hx⟩


/-! ### Periodicity in `θ` -/

/-- The arc set only depends on `θ` modulo `1`. -/
private lemma arcSet_add_int (θ : ℝ) (l : ℤ) : arcSet (θ + l) = arcSet θ := by
  ext p
  simp only [arcSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h0, m, hm⟩
    refine ⟨h0, l + m, ?_⟩
    have hcast : (((l + m : ℤ)) : ℝ) = (l : ℝ) + (m : ℝ) := by push_cast; ring
    rw [Set.mem_Ioo] at hm ⊢
    constructor
    · rw [hcast]; linarith [hm.1]
    · rw [hcast]; linarith [hm.2]
  · rintro ⟨h0, m, hm⟩
    refine ⟨h0, m - l, ?_⟩
    have hcast : (((m - l : ℤ)) : ℝ) = (m : ℝ) - (l : ℝ) := by push_cast; ring
    rw [Set.mem_Ioo] at hm ⊢
    constructor
    · rw [hcast]; linarith [hm.1]
    · rw [hcast]; linarith [hm.2]

/-- The cone spanned by the two bounding directions only depends on `θ` modulo `1`. -/
private lemma coneOf_add_int (θ : ℝ) (l : ℤ) : coneOf (θ + l) = coneOf θ := by
  simp only [coneOf]
  have h2 : bndOfU (θ + (l : ℝ) + 1/4) = bndOfU (θ + 1/4) := by
    rw [show θ + (l : ℝ) + 1/4 = (θ + 1/4) + (l : ℝ) by ring, bndOfU_add_int]
  rw [bndOfU_add_int, h2]

/-! ### The quarter turn -/

/-- The quarter turn of a square direction has perimeter parameter one quarter larger.  This is the
form in which the transport of the arc set uses it. -/
private lemma bndOfU_sub_quarter (x : ℝ) : bndOfU (x - 1/4) = rot90Inv (bndOfU x) := by
  have h := bndOfU_add_quarter (x - 1/4)
  rw [sub_add_cancel] at h
  rw [h, rot90Inv_rot90]

/-- The sup norm is invariant under the inverse quarter turn. -/
private lemma nrm_rot90Inv (p : E2) : nrm (rot90Inv p) = nrm p := by
  simp only [nrm, rot90Inv, Matrix.cons_val_zero, Matrix.cons_val_one, abs_neg, max_comm]

/-- The inverse quarter turn is homogeneous. -/
private lemma rot90Inv_smul (c : ℝ) (p : E2) : rot90Inv (c • p) = c • rot90Inv p := by
  ext i; fin_cases i <;> simp [rot90Inv, PiLp.smul_apply]

/-- The radial projection commutes with the quarter turn. -/
private lemma bnd_rot90 (p : E2) : bnd (rot90 p) = rot90 (bnd p) := by
  rw [bnd, bnd, nrm_rot90, rot90_smul]

/-- The radial projection commutes with the inverse quarter turn. -/
private lemma bnd_rot90Inv (p : E2) : bnd (rot90Inv p) = rot90Inv (bnd p) := by
  rw [bnd, bnd, nrm_rot90Inv, rot90Inv_smul]

/-- **The perimeter parameter of a quarter-turned point** is the shifted fractional part
`frac (u p + 1/4)`: with `bnd p = bndOfU (u p)` and `bndOfU (x + 1/4) = rot90 (bndOfU x)`, the
quarter turn of the direction shifts the parameter by one quarter. -/
private lemma u_rot90 {p : E2} (hp : p ≠ 0) : u (rot90 p) = Int.fract (u p + 1/4) := by
  have hbnd : bndOfU (u p) = bnd p := bndOfU_uPerim (nrm_bnd hp)
  calc u (rot90 p) = uPerim (bnd (rot90 p)) := rfl
    _ = uPerim (rot90 (bnd p)) := by rw [bnd_rot90]
    _ = uPerim (rot90 (bndOfU (u p))) := by rw [← hbnd]
    _ = uPerim (bndOfU (u p + 1/4)) := by rw [bndOfU_add_quarter]
    _ = Int.fract (u p + 1/4) := uPerim_bndOfU _

/-- The perimeter parameter of an inversely quarter-turned point is `frac (u p - 1/4)`. -/
private lemma u_rot90Inv {p : E2} (hp : p ≠ 0) : u (rot90Inv p) = Int.fract (u p - 1/4) := by
  have hbnd : bndOfU (u p) = bnd p := bndOfU_uPerim (nrm_bnd hp)
  calc u (rot90Inv p) = uPerim (bnd (rot90Inv p)) := rfl
    _ = uPerim (rot90Inv (bnd p)) := by rw [bnd_rot90Inv]
    _ = uPerim (rot90Inv (bndOfU (u p))) := by rw [← hbnd]
    _ = uPerim (bndOfU (u p - 1/4)) := by rw [bndOfU_sub_quarter]
    _ = Int.fract (u p - 1/4) := uPerim_bndOfU _

/-- Membership in the image of a set under the quarter turn, tested with the inverse. -/
private lemma mem_rot_image {s : Set E2} {p : E2} : p ∈ rot90 '' s ↔ rot90Inv p ∈ s := by
  constructor
  · rintro ⟨q, hq, hqp⟩
    have hq' : q = rot90Inv p := by rw [← hqp, rot90Inv_rot90]
    rwa [hq'] at hq
  · intro hp
    exact ⟨rot90Inv p, hp, rot90_rot90Inv p⟩

/-- **The arc set is transported by the quarter turn**: the points whose direction has parameter
one quarter above the arc `(θ, θ+1/4)` are the quarter turns of the points of that arc. -/
private lemma arcSet_add_quarter (θ : ℝ) : arcSet (θ + 1/4) = rot90 '' arcSet θ := by
  ext p
  rw [mem_rot_image]
  simp only [arcSet, Set.mem_ofPred_eq, nrm_rot90Inv]
  have hpne : ∀ h0 : 0 < nrm p, p ≠ 0 := by
    intro h0 h
    rw [h] at h0
    simp [nrm] at h0
  constructor
  · rintro ⟨h0, m, hm⟩
    obtain ⟨m', hmm⟩ := (exists_fract_sub_quarter (u p) θ).mpr ⟨m, hm⟩
    exact ⟨h0, m', by rw [u_rot90Inv (p := p) (hpne h0)]; exact hmm⟩
  · rintro ⟨h0, m, hm⟩
    rw [u_rot90Inv (p := p) (hpne h0)] at hm
    obtain ⟨m', hmm⟩ := (exists_fract_sub_quarter (u p) θ).mp ⟨m, hm⟩
    exact ⟨h0, m', hmm⟩

/-- **The cone of the shifted arc**: the quarter turn carries the open cone spanned by the two
bounding directions of the arc `(θ, θ+1/4)` to the open cone of the arc one quarter up. -/
private lemma coneOf_add_quarter (θ : ℝ) : coneOf (θ + 1/4) = rot90 '' coneOf θ := by
  have h1 : bndOfU (θ + 1/4) = rot90 (bndOfU θ) := bndOfU_add_quarter θ
  have h2 : bndOfU (θ + 1/2) = rot90 (bndOfU (θ + 1/4)) := by
    rw [show θ + 1/2 = (θ + 1/4) + 1/4 by ring]
    exact bndOfU_add_quarter (θ + 1/4)
  have h3 : coneOf (θ + 1/4) = wedgeCone (bndOfU (θ + 1/4)) (bndOfU (θ + 1/2)) := by
    rw [coneOf, show θ + 1/4 + 1/4 = θ + 1/2 by ring]
  have h4 : rot90 '' coneOf θ = rot90 '' wedgeCone (bndOfU θ) (bndOfU (θ + 1/4)) := by
    rw [coneOf]
  rw [h3, h1, h2, wedgeCone_rot, h4]

/-! ### `wedgeS` is the arc set at `θ = c + k/4` -/

/-- **`wedgeS c k` is the arc set at `θ = c + k/4`.**  `frac (u p - c) ∈ Ioo (k/4) ((k+1)/4)` says
that `u p - c` lies in the translate `(k/4 + m, k/4 + 1/4 + m)` of the `k`-th quarter, i.e. that
`u p ∈ Ioo ((c + k/4) + m) ((c + k/4) + 1/4 + m)`. -/
private lemma wedgeS_eq_arcSet (c : ℝ) (k : Fin 4) :
    wedgeS c k = arcSet (c + (k : ℝ) / 4) := by
  have hk : (((k : ℝ) + 1) / 4) = (k : ℝ) / 4 + 1 / 4 := by ring
  ext p
  simp only [wedgeS, arcSet, Set.mem_ofPred_eq, hk]
  constructor
  · rintro ⟨h0, h1⟩
    obtain ⟨m, hm⟩ :=
      (interval_nonempty_iff_fract (u p - c) ((k : ℝ) / 4)).mpr ⟨0, by simpa using h1⟩
    exact ⟨h0, m, by rw [Set.mem_Ioo] at hm ⊢; constructor <;> linarith⟩
  · rintro ⟨h0, m, hm⟩
    rw [Set.mem_Ioo] at hm ⊢
    have hk3 : (k : ℝ) ≤ 3 := by fin_cases k <;> norm_num
    have hsub : u p - c ∈ Set.Ioo ((k : ℝ) / 4 + m) ((k : ℝ) / 4 + 1 / 4 + m) :=
      ⟨by linarith [hm.1], by linarith [hm.2]⟩
    have hex : ∃ m' : ℤ, Int.fract (u p - c) ∈
        Set.Ioo ((k : ℝ) / 4 + m') ((k : ℝ) / 4 + 1 / 4 + m') :=
      (interval_nonempty_iff_fract (u p - c) ((k : ℝ) / 4)).mp ⟨m, hsub⟩
    have hred := (exists_interval_reduce (x := Int.fract (u p - c)) (θ := (k : ℝ) / 4)
      (Int.fract_nonneg _) (Int.fract_lt_one _) (by positivity) (by linarith)).mp hex
    exact ⟨h0, by simpa using hred⟩

/-! ### The arc set is the open cone over its two bounding directions -/

/-- `bndOfU` on the first quarter `[0, 1/4)` of the parameter: the right edge of the square,
traversed from the corner `(1,1)` down to `(1,-1)`. -/
private lemma bndOfU_of_lt_quarter {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1/4) :
    bndOfU θ = !₂[(1 : ℝ), 1 - 8 * θ] := by
  have hf : Int.fract θ = θ := Int.fract_eq_self.mpr ⟨h0, by linarith⟩
  unfold bndOfU
  rw [hf, ite_eq_left h1]

/-- `bndOfU` one quarter of the parameter up (the second quarter `[1/4, 1/2)`): the bottom edge of
the square, from `(1,-1)` to `(-1,-1)`. -/
private lemma bndOfU_of_quarter {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1/4) :
    bndOfU (θ + 1/4) = !₂[1 - 8 * θ, (-1 : ℝ)] := by
  have hf : Int.fract (θ + 1/4) = θ + 1/4 :=
    Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  unfold bndOfU
  rw [hf, ite_eq_right (by linarith : ¬ (θ + 1/4 < 1/4)),
    ite_eq_left (by linarith : θ + 1/4 < 1/2)]
  ext i
  fin_cases i <;> (simp; try ring)

/-- **The arc set is the cone over its bounding directions**, for `θ` in the first quarter of the
period.  There the two bounding directions are `bndOfU θ = (1, 1-8θ)` on the right edge and
`bndOfU (θ+1/4) = (1-8θ, -1)` on the bottom edge, and `geo_quarter` identifies the cone with the
set of boundary points whose perimeter parameter lies in the arc `(θ, θ+1/4)`.  Both sides are
cones (the conditions are on the direction `bnd p` and the cone is invariant under positive
scaling), so it suffices to compare directions. -/
private theorem arcSet_eq_coneOf_quarter (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1/4) :
    arcSet θ = coneOf θ := by
  have hA : bndOfU θ = !₂[(1 : ℝ), 1 - 8 * θ] := bndOfU_of_lt_quarter hθ0 hθ1
  have hB : bndOfU (θ + 1/4) = !₂[1 - 8 * θ, (-1 : ℝ)] := bndOfU_of_quarter hθ0 hθ1
  ext p
  constructor
  · rintro ⟨h0, m, hm⟩
    have hpne : p ≠ 0 := by intro h; rw [h] at h0; simp [nrm] at h0
    obtain ⟨hu0, hu1⟩ := uPerim_mem (nrm_bnd hpne)
    have hred : u p ∈ Set.Ioo θ (θ + 1/4) :=
      (exists_interval_reduce hu0 hu1 hθ0 (by linarith)).mp ⟨m, hm⟩
    have hgeo : bnd p ∈ coneOf θ := by
      rw [coneOf, hA, hB]
      exact (geo_quarter θ hθ0 hθ1 (nrm_bnd hpne)).mpr hred
    have hsc := (wedgeCone_smul h0 (bndOfU θ) (bndOfU (θ + 1/4)) (bnd p)).mpr hgeo
    rwa [smul_bnd] at hsc
  · rintro hp
    have hpne : p ≠ 0 := wedgeCone_ne_zero hp
    have h0 : 0 < nrm p := nrm_pos hpne
    have hbd : bnd p ∈ wedgeCone !₂[(1 : ℝ), 1 - 8 * θ] !₂[1 - 8 * θ, (-1 : ℝ)] := by
      have h := hp
      rw [coneOf] at h
      have h' : nrm p • bnd p ∈ wedgeCone (bndOfU θ) (bndOfU (θ + 1/4)) := by
        rwa [smul_bnd]
      have h'' := (wedgeCone_smul h0 (bndOfU θ) (bndOfU (θ + 1/4)) (bnd p)).mp h'
      rwa [hA, hB] at h''
    have hgeo : uPerim (bnd p) ∈ Set.Ioo θ (θ + 1/4) :=
      (geo_quarter θ hθ0 hθ1 (nrm_bnd hpne)).mp hbd
    exact ⟨h0, 0, by simpa [u] using hgeo⟩

/-- **The arc set is the cone over its two bounding directions**, for every real `θ`.  The two
sides are periodic in `θ` with period `1` (`arcSet_add_int`, `coneOf_add_int`) and are both
transported by the quarter turn (`arcSet_add_quarter`, `coneOf_add_quarter`), so shifting `θ` by
quarters into the window `[0, 1/4)` reduces the statement to `arcSet_eq_coneOf_quarter`. -/
private theorem arcSet_eq_coneOf (θ : ℝ) : arcSet θ = coneOf θ := by
  have hstep : ∀ x : ℝ, arcSet (x - 1/4) = coneOf (x - 1/4) → arcSet x = coneOf x := by
    intro x h
    calc arcSet x = arcSet ((x - 1/4) + 1/4) := by rw [sub_add_cancel]
      _ = rot90 '' arcSet (x - 1/4) := arcSet_add_quarter _
      _ = rot90 '' coneOf (x - 1/4) := by rw [h]
      _ = coneOf ((x - 1/4) + 1/4) := (coneOf_add_quarter _).symm
      _ = coneOf x := by rw [sub_add_cancel]
  have s2 : ∀ x : ℝ, arcSet (x - 1/2) = coneOf (x - 1/2) → arcSet x = coneOf x := by
    intro x h
    have h₁ : arcSet (x - 1/4) = coneOf (x - 1/4) :=
      hstep (x - 1/4) (by rwa [show x - 1/4 - 1/4 = x - 1/2 by ring])
    exact hstep x h₁
  have s3 : ∀ x : ℝ, arcSet (x - 3/4) = coneOf (x - 3/4) → arcSet x = coneOf x := by
    intro x h
    have h' : arcSet (x - 1/4 - 1/2) = coneOf (x - 1/4 - 1/2) := by
      rwa [show x - 1/4 - 1/2 = x - 3/4 by ring]
    exact hstep x (s2 (x - 1/4) h')
  have hwin : arcSet (Int.fract θ) = coneOf (Int.fract θ) := by
    set f := Int.fract θ with hf
    have hf0 : 0 ≤ f := by rw [hf]; exact Int.fract_nonneg θ
    have hf1 : f < 1 := by rw [hf]; exact Int.fract_lt_one θ
    rcases lt_or_ge f (1/4) with h | h
    · exact arcSet_eq_coneOf_quarter f hf0 h
    · rcases lt_or_ge f (1/2) with h2 | h2
      · have h0 : arcSet (f - 1/4) = coneOf (f - 1/4) :=
          arcSet_eq_coneOf_quarter (f - 1/4) (by linarith) (by linarith)
        rw [show f = (f - 1/4) + 1/4 by ring]
        exact hstep _ (by rw [show (f - 1/4) + 1/4 - 1/4 = f - 1/4 by ring]; exact h0)
      · rcases lt_or_ge f (3/4) with h3 | h3
        · have h0 : arcSet (f - 1/2) = coneOf (f - 1/2) :=
            arcSet_eq_coneOf_quarter (f - 1/2) (by linarith) (by linarith)
          rw [show f = (f - 1/2) + 1/2 by ring]
          exact s2 _ (by rw [show (f - 1/2) + 1/2 - 1/2 = f - 1/2 by ring]; exact h0)
        · have h0 : arcSet (f - 3/4) = coneOf (f - 3/4) :=
            arcSet_eq_coneOf_quarter (f - 3/4) (by linarith) (by linarith)
          rw [show f = (f - 3/4) + 3/4 by ring]
          exact s3 _ (by rw [show (f - 3/4) + 3/4 - 3/4 = f - 3/4 by ring]; exact h0)
  calc arcSet θ = arcSet (Int.fract θ + (⌊θ⌋ : ℝ)) := by rw [Int.fract_add_floor]
    _ = arcSet (Int.fract θ) := arcSet_add_int _ _
    _ = coneOf (Int.fract θ) := hwin
    _ = coneOf (Int.fract θ + (⌊θ⌋ : ℝ)) := (coneOf_add_int _ _).symm
    _ = coneOf θ := by rw [Int.fract_add_floor]

/-! ### The shifted wedges are open -/

/-- **The `c`-shifted wedges are open.**  `wedgeS c k` is the arc set at `θ = c + k/4`
(`wedgeS_eq_arcSet`), which is the open cone spanned by the two bounding directions
(`arcSet_eq_coneOf`), and a cone is an intersection of two open half-planes
(`isOpen_wedgeCone`). -/
theorem isOpen_wedgeS (c : ℝ) (k : Fin 4) : IsOpen (wedgeS c k) := by
  rw [wedgeS_eq_arcSet c k, arcSet_eq_coneOf, coneOf]
  exact isOpen_wedgeCone _ _

end Work.Cusp
