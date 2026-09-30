import Mathlib
import Submission.Work.RTOwed.cuspDev
import Submission.Work.RTOwed.cuspCertWalls
import Submission.Work.RTOwed.cuspCert.cube_quad
import Submission.Work.RTOwed.cuspCert.cusp_disjoint
import Submission.Work.RTOwed.cuspCert.cubeOfMod_corner_dvd

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function
open scoped BigOperators

namespace Work.RTOwed.cuspCert

/-! ## The cell decomposition of the cube coordinates by the cusp lattice

`lamK v k = diag (latMod v) · k` is the lattice offset vector, `lamV v k` the same vector of `E3`.
The *cell* of the cube `a` at the offset `k` is the translate `cubeBox a + lamV v k`; these cells
(for the cubes `a` of the cusp `v` and the offsets `k ∈ ℤ³` with `lamK v k ∈ Λ_v`) tile `E3`, and
`mbarPt v` restricts to a continuous map on each. -/

/-- The lattice offset of the coefficient vector `k`. -/
def lamK (v : Fin 5) (k : Fin 3 → ℤ) : Fin 3 → ℤ := fun i => (Work.Cusp.latMod v i : ℤ) * k i

/-- The lattice offset, as a vector of `E3`. -/
def lamV (v : Fin 5) (k : Fin 3 → ℤ) : Work.RTOwed.CuspE3 :=
  WithLp.toLp 2 fun i => (lamK v k i : ℝ)

/-- The coefficient vector of an offset with entries in `{-1,0,1}`. -/
def kfun (u : Fin 3 → Fin 3) : Fin 3 → ℤ := fun i => (u i : ℤ) - 1

/-- The lower corner of the overlap of `cubeBox a` and `cubeBox b + lamV v k`. -/
def loB (v : Fin 5) (a b : Fin 48) (k : Fin 3 → ℤ) : Fin 3 → ℤ :=
  fun i => max (Work.Cusp.cubeCorner a i) (Work.Cusp.cubeCorner b i + lamK v k i)

/-- The upper corner of the overlap of `cubeBox a` and `cubeBox b + lamV v k`. -/
def hiB (v : Fin 5) (a b : Fin 48) (k : Fin 3 → ℤ) : Fin 3 → ℤ :=
  fun i => min (Work.Cusp.cubeCorner a i + 1) (Work.Cusp.cubeCorner b i + lamK v k i + 1)

/-- The overlap of the two boxes is non-empty. -/
abbrev ovl (v : Fin 5) (a b : Fin 48) (k : Fin 3 → ℤ) : Prop :=
  ∀ i : Fin 3, Work.Cusp.cubeCorner b i + lamK v k i ≤ Work.Cusp.cubeCorner a i + 1 ∧
    Work.Cusp.cubeCorner a i ≤ Work.Cusp.cubeCorner b i + lamK v k i + 1

/-- The generator attached to the direction `i` of the overlap: the type of the wall of `a` that
is tight there, or `0` in a free direction. -/
def bindG (v : Fin 5) (a b : Fin 48) (k : Fin 3 → ℤ) (i : Fin 3) : Work.FoldInst.Gg :=
  if loB v a b k i = hiB v a b k i then
    (if loB v a b k i = Work.Cusp.cubeCorner a i then
      Work.FoldInst.typeGen (Work.FoldInst.sideTypeIdx (Work.RTOwed.wallLo a i))
    else if loB v a b k i = Work.Cusp.cubeCorner a i + 1 then
      Work.FoldInst.typeGen (Work.FoldInst.sideTypeIdx (Work.RTOwed.wallHi a i))
    else 0)
  else 0

/-- The group element of the gluing of the cell of `a` with the cell of `b` at offset `k`. -/
def glueGam (v : Fin 5) (a b : Fin 48) (k : Fin 3 → ℤ) : Work.FoldInst.Gg :=
  ∑ i : Fin 3, bindG v a b k i

/-- The `j`-th column of the difference of the affine maps of the gluing, scaled by `10`. -/
abbrev linG (v : Fin 5) (a b : Fin 48) (k : Fin 3 → ℤ) (r : Fin 4) (j : Fin 3) : ℤ :=
  Work.FoldInst.signVec (glueGam v a b k).1 r * A10 a r j - A10 b r j

/-- The constant term of the difference of the affine maps of the gluing, scaled by `10`. -/
abbrev conG (v : Fin 5) (a b : Fin 48) (k : Fin 3 → ℤ) (r : Fin 4) : ℤ :=
  Work.FoldInst.signVec (glueGam v a b k).1 r * b10 a r
    + (A10 b r 0 * lamK v k 0 + A10 b r 1 * lamK v k 1 + A10 b r 2 * lamK v k 2)
    - b10 b r

/-! ## The finite certificate of the gluing -/

/-- The certificate of the gluing for the first cube `a` (its cusp is `Work.Cusp.cubeCusp a`):
checked one cube at a time, each a small kernel `decide`. -/
abbrev glueRow (a : Fin 48) : Prop :=
  ∀ (b : Fin 48) (u : Fin 3 → Fin 3),
    Work.Cusp.cubeCusp b = (Work.Cusp.cubeCusp a) → ovl (Work.Cusp.cubeCusp a) a b (kfun u) →
    ((glueGam (Work.Cusp.cubeCusp a) a b (kfun u)).2 + cubeBit a = cubeBit b ∧
      (∀ j : Fin 3, loB (Work.Cusp.cubeCusp a) a b (kfun u) j ≠ hiB (Work.Cusp.cubeCusp a) a b (kfun u) j →
        ∀ r : Fin 4, linG (Work.Cusp.cubeCusp a) a b (kfun u) r j = 0) ∧
      (∀ r : Fin 4, linG (Work.Cusp.cubeCusp a) a b (kfun u) r 0 * loB (Work.Cusp.cubeCusp a) a b (kfun u) 0
        + linG (Work.Cusp.cubeCusp a) a b (kfun u) r 1 * loB (Work.Cusp.cubeCusp a) a b (kfun u) 1
        + linG (Work.Cusp.cubeCusp a) a b (kfun u) r 2 * loB (Work.Cusp.cubeCusp a) a b (kfun u) 2
        + conG (Work.Cusp.cubeCusp a) a b (kfun u) r = 0))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem glueRow_0 : glueRow 0 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem glueRow_1 : glueRow 1 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem glueRow_2 : glueRow 2 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem glueRow_3 : glueRow 3 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem glueRow_4 : glueRow 4 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem glueRow_5 : glueRow 5 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem glueRow_6 : glueRow 6 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem glueRow_7 : glueRow 7 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem glueRow_8 : glueRow 8 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem glueRow_9 : glueRow 9 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem glueRow_10 : glueRow 10 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem glueRow_11 : glueRow 11 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem glueRow_12 : glueRow 12 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem glueRow_13 : glueRow 13 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem glueRow_14 : glueRow 14 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem glueRow_15 : glueRow 15 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem glueRow_16 : glueRow 16 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem glueRow_17 : glueRow 17 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem glueRow_18 : glueRow 18 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem glueRow_19 : glueRow 19 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem glueRow_20 : glueRow 20 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem glueRow_21 : glueRow 21 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem glueRow_22 : glueRow 22 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem glueRow_23 : glueRow 23 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem glueRow_24 : glueRow 24 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem glueRow_25 : glueRow 25 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem glueRow_26 : glueRow 26 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem glueRow_27 : glueRow 27 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem glueRow_28 : glueRow 28 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem glueRow_29 : glueRow 29 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem glueRow_30 : glueRow 30 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem glueRow_31 : glueRow 31 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem glueRow_32 : glueRow 32 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem glueRow_33 : glueRow 33 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem glueRow_34 : glueRow 34 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem glueRow_35 : glueRow 35 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem glueRow_36 : glueRow 36 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem glueRow_37 : glueRow 37 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem glueRow_38 : glueRow 38 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem glueRow_39 : glueRow 39 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem glueRow_40 : glueRow 40 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem glueRow_41 : glueRow 41 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem glueRow_42 : glueRow 42 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem glueRow_43 : glueRow 43 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem glueRow_44 : glueRow 44 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem glueRow_45 : glueRow 45 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem glueRow_46 : glueRow 46 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem glueRow_47 : glueRow 47 := by decide +kernel

/-- **The finite certificate of the gluing.**  For every cusp `v`, every pair of cubes `a`, `b` of
that cusp and every offset with entries in `{-1,0,1}` whose cells overlap, the group element
`glueGam v a b k` matches the copy bits, the difference of the affine maps of the two facets
vanishes along the free directions of the overlap, and it vanishes at the lower corner. -/
theorem glue_cert : ∀ (v : Fin 5) (a b : Fin 48) (u : Fin 3 → Fin 3),
    Work.Cusp.cubeCusp a = v → Work.Cusp.cubeCusp b = v → ovl v a b (kfun u) →
    ((glueGam v a b (kfun u)).2 + cubeBit a = cubeBit b ∧
      (∀ j : Fin 3, loB v a b (kfun u) j ≠ hiB v a b (kfun u) j →
        ∀ r : Fin 4, linG v a b (kfun u) r j = 0) ∧
      (∀ r : Fin 4, linG v a b (kfun u) r 0 * loB v a b (kfun u) 0
        + linG v a b (kfun u) r 1 * loB v a b (kfun u) 1
        + linG v a b (kfun u) r 2 * loB v a b (kfun u) 2
        + conG v a b (kfun u) r = 0)) := by
  intro v a b u hca hcb hov
  subst hca
  have h : glueRow a := by
    fin_cases a
    exacts [glueRow_0, glueRow_1, glueRow_2, glueRow_3, glueRow_4, glueRow_5, glueRow_6, glueRow_7, glueRow_8, glueRow_9, glueRow_10, glueRow_11, glueRow_12, glueRow_13, glueRow_14, glueRow_15, glueRow_16, glueRow_17, glueRow_18, glueRow_19, glueRow_20, glueRow_21, glueRow_22, glueRow_23, glueRow_24, glueRow_25, glueRow_26, glueRow_27, glueRow_28, glueRow_29, glueRow_30, glueRow_31, glueRow_32, glueRow_33, glueRow_34, glueRow_35, glueRow_36, glueRow_37, glueRow_38, glueRow_39, glueRow_40, glueRow_41, glueRow_42, glueRow_43, glueRow_44, glueRow_45, glueRow_46, glueRow_47]
  exact h b u hcb hov


/-! ## Decoding an offset with entries in `{-1,0,1}` -/

/-- The index of an integer `-1 ≤ n ≤ 1` among `{-1,0,1}`. -/
def toF3 (n : ℤ) (h : n = -1 ∨ n = 0 ∨ n = 1) : Fin 3 :=
  if n = -1 then 0 else if n = 0 then 1 else 2

theorem toF3_spec (n : ℤ) (h : n = -1 ∨ n = 0 ∨ n = 1) :
    ((toF3 n h : Fin 3) : ℤ) - 1 = n := by
  rcases h with h | h | h <;> simp [toF3, h]

theorem exists_kfun (k : Fin 3 → ℤ) (h : ∀ i, k i = -1 ∨ k i = 0 ∨ k i = 1) :
    ∃ u : Fin 3 → Fin 3, kfun u = k := by
  refine ⟨fun i => toF3 (k i) (h i), ?_⟩
  funext i
  exact toF3_spec (k i) (h i)

/-! ## The bound on the offset of two overlapping cells -/

theorem latMod_pos : ∀ (v : Fin 5) (i : Fin 3), 0 < (Work.Cusp.latMod v i : ℤ) := by decide +kernel

/-- The signed gap of the corners along `i` is smaller than twice the lattice spacing. -/
theorem corner_bound_hi : ∀ (v : Fin 5) (a b : Fin 48) (i : Fin 3),
    Work.Cusp.cubeCusp a = v → Work.Cusp.cubeCusp b = v →
    Work.Cusp.cubeCorner a i + 1 - Work.Cusp.cubeCorner b i
      < 2 * (Work.Cusp.latMod v i : ℤ) := by
  decide +kernel

theorem corner_bound_lo : ∀ (v : Fin 5) (a b : Fin 48) (i : Fin 3),
    Work.Cusp.cubeCusp a = v → Work.Cusp.cubeCusp b = v →
    Work.Cusp.cubeCorner b i + 1 - Work.Cusp.cubeCorner a i
      < 2 * (Work.Cusp.latMod v i : ℤ) := by
  decide +kernel

/-- **The offset of two overlapping cells has entries in `{-1,0,1}`.** -/
theorem k_bound (v : Fin 5) (a b : Fin 48) (i : Fin 3)
    (hca : Work.Cusp.cubeCusp a = v) (hcb : Work.Cusp.cubeCusp b = v)
    (k : Fin 3 → ℤ) (y y' : Work.RTOwed.CuspE3)
    (hy : y ∈ cubeBox a) (hy' : y' ∈ cubeBox b)
    (hd : y i - y' i = (lamK v k i : ℝ)) : -1 ≤ k i ∧ k i ≤ 1 := by
  have hyi := hy i
  have hyi' := hy' i
  have hpos : (0 : ℝ) < (Work.Cusp.latMod v i : ℝ) := by
    exact_mod_cast (latMod_pos v i)
  have hk : (lamK v k i : ℝ) = (Work.Cusp.latMod v i : ℝ) * (k i : ℝ) := by
    simp [lamK]
  have hstep : (y i - y' i) < 2 * (Work.Cusp.latMod v i : ℝ) := by
    have hL := corner_bound_hi v a b i hca hcb
    have h1 : (y i - y' i) ≤ (Work.Cusp.cubeCorner a i : ℝ) + 1 - (Work.Cusp.cubeCorner b i : ℝ) := by
      linarith [hyi.1, hyi.2, hyi'.1, hyi'.2]
    have h2 : ((Work.Cusp.cubeCorner a i + 1 - Work.Cusp.cubeCorner b i : ℤ) : ℝ)
        < 2 * (Work.Cusp.latMod v i : ℝ) := by exact_mod_cast hL
    push_cast at h2
    linarith
  have hstep' : (y' i - y i) < 2 * (Work.Cusp.latMod v i : ℝ) := by
    have hR := corner_bound_lo v a b i hca hcb
    have h1 : (y' i - y i) ≤ (Work.Cusp.cubeCorner b i : ℝ) + 1 - (Work.Cusp.cubeCorner a i : ℝ) := by
      linarith [hyi.1, hyi.2, hyi'.1, hyi'.2]
    have h2 : ((Work.Cusp.cubeCorner b i + 1 - Work.Cusp.cubeCorner a i : ℤ) : ℝ)
        < 2 * (Work.Cusp.latMod v i : ℝ) := by exact_mod_cast hR
    push_cast at h2
    linarith
  have hA : (Work.Cusp.latMod v i : ℝ) * (k i : ℝ) < 2 * (Work.Cusp.latMod v i : ℝ) := by
    rw [← hk, ← hd]
    exact hstep
  have hB : -((Work.Cusp.latMod v i : ℝ) * (k i : ℝ)) < 2 * (Work.Cusp.latMod v i : ℝ) := by
    have hthis : y' i - y i = -((Work.Cusp.latMod v i : ℝ) * (k i : ℝ)) := by
      rw [show y' i - y i = -(y i - y' i) by ring, hd, hk]
    rw [hthis] at hstep'
    exact hstep'
  constructor
  · have h3 : -(k i : ℝ) < 2 := by nlinarith [hB]
    have h4 : ((-(k i) : ℤ) : ℝ) < 2 := by
      rw [show ((-(k i) : ℤ) : ℝ) = -(k i : ℝ) by push_cast; ring]; exact h3
    have h5 : (-(k i) : ℤ) < 2 := by exact_mod_cast h4
    omega
  · have h3 : (k i : ℝ) < 2 := by nlinarith [hA]
    have h4 : (k i : ℤ) < 2 := by exact_mod_cast h3
    omega

/-! ## The directions of the overlap that are degenerate on a wall of `a` -/

theorem loB_eq_hiB_cases (v : Fin 5) (a b : Fin 48) (k : Fin 3 → ℤ) (i : Fin 3)
    (h : loB v a b k i = hiB v a b k i) :
    loB v a b k i = Work.Cusp.cubeCorner a i ∨
      loB v a b k i = Work.Cusp.cubeCorner a i + 1 := by
  simp only [loB, hiB] at h ⊢
  omega




/-! ## The affine maps of the cube in the rescaled integer coordinates -/

/-- `10` times the `r`-th Klein coordinate of the point of the facet of the cube `a` with cube
coordinates `x`. -/
theorem ten_kleinPt (a : Fin 48) (x : Work.RTOwed.CuspE3) (r : Fin 4) :
    10 * Work.RTOwed.kleinPt a x r
      = (A10 a r 0 * x 0 + A10 a r 1 * x 1 + A10 a r 2 * x 2 + b10 a r : ℝ) := by
  simp only [Work.RTOwed.kleinPt, PiLp.toLp_apply]
  rw [Fin.sum_univ_three]
  rw [hA10 a r 0, hA10 a r 1, hA10 a r 2, hb10 a r]
  push_cast
  ring

/-- The coordinate form of the action of a sign change. -/
theorem act_apply_r (g : Fin 4 → ZMod 2) (y : Work.FoldInst.E4) (r : Fin 4) :
    (Work.FoldInst.act g y) r = ((Work.FoldInst.signVec g r : ℤ) : ℝ) * y r := by
  have h := congrFun (Work.FoldInst.act_apply g y) r
  simpa using h

/-- The difference of the two rescaled affine maps, expanded in the columns `linG` and the
constant `conG`. -/
theorem glue_lin (v : Fin 5) (a b : Fin 48) (k : Fin 3 → ℤ) (r : Fin 4) (y : Fin 3 → ℝ) :
    ((Work.FoldInst.signVec (glueGam v a b k).1 r : ℤ) : ℝ)
        * ((A10 a r 0 : ℤ) * y 0 + (A10 a r 1 : ℤ) * y 1 + (A10 a r 2 : ℤ) * y 2 + (b10 a r : ℤ))
      - ((A10 b r 0 : ℤ) * (y 0 - (lamK v k 0 : ℤ)) + (A10 b r 1 : ℤ) * (y 1 - (lamK v k 1 : ℤ))
          + (A10 b r 2 : ℤ) * (y 2 - (lamK v k 2 : ℤ)) + (b10 b r : ℤ))
    = ((linG v a b k r 0 : ℤ) : ℝ) * y 0 + ((linG v a b k r 1 : ℤ) : ℝ) * y 1
      + ((linG v a b k r 2 : ℤ) : ℝ) * y 2 + ((conG v a b k r : ℤ) : ℝ) := by
  simp only [linG, conG]
  push_cast
  ring

/-- The overlap box of the two cells contains every point of the first cell that is offset by
`lamK v k` from a point of the second. -/
theorem mem_loB_hiB (v : Fin 5) (a b : Fin 48) (k : Fin 3 → ℤ)
    (y y' : Work.RTOwed.CuspE3) (hy : y ∈ cubeBox a) (hy' : y' ∈ cubeBox b)
    (hd : ∀ i, y i - y' i = (lamK v k i : ℝ)) :
    ∀ j : Fin 3, (loB v a b k j : ℝ) ≤ y j ∧ y j ≤ (hiB v a b k j : ℝ) := by
  intro j
  obtain ⟨h1, h2⟩ := hy j
  obtain ⟨h3, h4⟩ := hy' j
  have h5 := hd j
  have hlo : (loB v a b k j : ℝ)
      = max ((Work.Cusp.cubeCorner a j : ℤ) : ℝ)
        (((Work.Cusp.cubeCorner b j : ℤ) : ℝ) + (lamK v k j : ℝ)) := by
    simp only [loB]; push_cast; rfl
  have hhi : (hiB v a b k j : ℝ)
      = min (((Work.Cusp.cubeCorner a j : ℤ) : ℝ) + 1)
        (((Work.Cusp.cubeCorner b j : ℤ) : ℝ) + (lamK v k j : ℝ) + 1) := by
    simp only [hiB]; push_cast; rfl
  rw [hlo, hhi]
  constructor
  · refine max_le h1 ?_
    linarith
  · refine le_min h2 ?_
    linarith

/-- The certificate turns the expanded difference into zero on the overlap box. -/
theorem lin_sum_eq_zero (v : Fin 5) (a b : Fin 48) (k : Fin 3 → ℤ) (r : Fin 4)
    (y y' : Work.RTOwed.CuspE3) (hy : y ∈ cubeBox a) (hy' : y' ∈ cubeBox b)
    (hd : ∀ i, y i - y' i = (lamK v k i : ℝ))
    (hcol : ∀ j : Fin 3, loB v a b k j ≠ hiB v a b k j → linG v a b k r j = 0)
    (hcon : linG v a b k r 0 * loB v a b k 0 + linG v a b k r 1 * loB v a b k 1
      + linG v a b k r 2 * loB v a b k 2 + conG v a b k r = 0) :
    ((linG v a b k r 0 : ℤ) : ℝ) * y 0 + ((linG v a b k r 1 : ℤ) : ℝ) * y 1
      + ((linG v a b k r 2 : ℤ) : ℝ) * y 2 + ((conG v a b k r : ℤ) : ℝ) = 0 := by
  have hb := mem_loB_hiB v a b k y y' hy hy' hd
  have key : ∀ j : Fin 3,
      ((linG v a b k r j : ℤ) : ℝ) * y j = ((linG v a b k r j : ℤ) : ℝ) * (loB v a b k j : ℝ) := by
    intro j
    by_cases h : loB v a b k j = hiB v a b k j
    · have h1 := hb j
      have h2 : y j = (loB v a b k j : ℝ) := le_antisymm (h ▸ h1.2) h1.1
      rw [h2]
    · rw [hcol j h]; push_cast; ring
  have h0 : ((linG v a b k r 0 : ℤ) : ℝ) * y 0
      = ((linG v a b k r 0 : ℤ) : ℝ) * (loB v a b k 0 : ℝ) := key 0
  have h1 : ((linG v a b k r 1 : ℤ) : ℝ) * y 1
      = ((linG v a b k r 1 : ℤ) : ℝ) * (loB v a b k 1 : ℝ) := key 1
  have h2 : ((linG v a b k r 2 : ℤ) : ℝ) * y 2
      = ((linG v a b k r 2 : ℤ) : ℝ) * (loB v a b k 2 : ℝ) := key 2
  rw [h0, h1, h2]
  exact_mod_cast hcon


/-! ## The gluing of two overlapping cells -/

/-- **The gluing of two overlapping cells.**  If `y` is a point of the cube `a`, `y'` a point of the
cube `b`, with `a`, `b` cubes of the same cusp `v` and `y - y' = lamK v k` for a vector `k` with
entries in `{-1,0,1}`, then the two facet points represent the same point of `M̄`. -/
theorem glue_rel (v : Fin 5) (a b : Fin 48) (hca : Work.Cusp.cubeCusp a = v)
    (hcb : Work.Cusp.cubeCusp b = v) (k : Fin 3 → ℤ)
    (hk : ∀ i, k i = -1 ∨ k i = 0 ∨ k i = 1)
    (y y' : Work.RTOwed.CuspE3) (hy : y ∈ cubeBox a) (hy' : y' ∈ cubeBox b)
    (hd : ∀ i, y i - y' i = (lamK v k i : ℝ)) :
    Work.FoldInst.mk (xbarOf a (Work.RTOwed.kleinPt a y) (cube_quad.1 a y hy))
      = Work.FoldInst.mk (xbarOf b (Work.RTOwed.kleinPt b y') (cube_quad.1 b y' hy')) := by
  obtain ⟨u, hu⟩ := exists_kfun k hk
  have hd' : ∀ i, y i - y' i = (lamK v (kfun u) i : ℝ) := by intro i; rw [hu]; exact hd i
  have hov : ovl v a b (kfun u) := by
    intro i
    obtain ⟨h1, h2⟩ := hy i
    obtain ⟨h3, h4⟩ := hy' i
    have h5 := hd' i
    have hR1 : ((Work.Cusp.cubeCorner b i : ℤ) : ℝ) + (lamK v (kfun u) i : ℝ)
        ≤ ((Work.Cusp.cubeCorner a i : ℤ) : ℝ) + 1 := by linarith
    have hR2 : ((Work.Cusp.cubeCorner a i : ℤ) : ℝ)
        ≤ ((Work.Cusp.cubeCorner b i : ℤ) : ℝ) + (lamK v (kfun u) i : ℝ) + 1 := by linarith
    exact ⟨by exact_mod_cast hR1, by exact_mod_cast hR2⟩
  have hcert := glue_cert v a b u hca hcb hov
  obtain ⟨hcp, hcol, hcon⟩ := hcert
  have haff : Work.FoldInst.act (glueGam v a b (kfun u)).1 (Work.RTOwed.kleinPt a y)
      = Work.RTOwed.kleinPt b y' := by
    apply PiLp.ext
    intro r
    have hA := ten_kleinPt a y r
    have hB := ten_kleinPt b y' r
    have hb0 : y' 0 = y 0 - (lamK v (kfun u) 0 : ℝ) := by have := hd' 0; linarith
    have hb1 : y' 1 = y 1 - (lamK v (kfun u) 1 : ℝ) := by have := hd' 1; linarith
    have hb2 : y' 2 = y 2 - (lamK v (kfun u) 2 : ℝ) := by have := hd' 2; linarith
    rw [hb0, hb1, hb2] at hB
    have hp := glue_lin v a b (kfun u) r (fun j => y j)
    have key : 10 * (((Work.FoldInst.signVec (glueGam v a b (kfun u)).1 r : ℤ) : ℝ)
          * Work.RTOwed.kleinPt a y r - Work.RTOwed.kleinPt b y' r) = 0 := by
      have e : 10 * (((Work.FoldInst.signVec (glueGam v a b (kfun u)).1 r : ℤ) : ℝ)
            * Work.RTOwed.kleinPt a y r - Work.RTOwed.kleinPt b y' r)
          = ((Work.FoldInst.signVec (glueGam v a b (kfun u)).1 r : ℤ) : ℝ)
              * (10 * Work.RTOwed.kleinPt a y r) - 10 * Work.RTOwed.kleinPt b y' r := by ring
      rw [e, hA, hB, hp]
      exact lin_sum_eq_zero v a b (kfun u) r y y' hy hy' hd' (fun j hj => hcol j hj r) (hcon r)
    have hz : ((Work.FoldInst.signVec (glueGam v a b (kfun u)).1 r : ℤ) : ℝ)
        * Work.RTOwed.kleinPt a y r - Work.RTOwed.kleinPt b y' r = 0 := by
      rcases mul_eq_zero.mp key with h | h
      · norm_num at h
      · exact h
    rw [act_apply_r]
    linarith
  have hK : glueGam v a b (kfun u) ∈ Work.FoldInst.Ksub (Work.RTOwed.kleinPt a y) := by
    rw [glueGam, Fin.sum_univ_three]
    refine AddSubgroup.add_mem _ (AddSubgroup.add_mem _ ?_ ?_) ?_
    · by_cases hdi : loB v a b (kfun u) 0 = hiB v a b (kfun u) 0
      · have hyi := mem_loB_hiB v a b (kfun u) y y' hy hy' hd' 0
        have hyeq : y 0 = (loB v a b (kfun u) 0 : ℝ) := le_antisymm (hdi ▸ hyi.2) hyi.1
        rw [bindG, if_pos hdi]
        by_cases h1 : loB v a b (kfun u) 0 = Work.Cusp.cubeCorner a 0
        · rw [if_pos h1]
          refine AddSubgroup.subset_closure ⟨Work.RTOwed.wallLo a 0, ?_, rfl⟩
          rw [Work.RTOwed.sideSlack_wallLo, hyeq, h1]
          push_cast
          ring
        · by_cases h2 : loB v a b (kfun u) 0 = Work.Cusp.cubeCorner a 0 + 1
          · rw [if_neg h1, if_pos h2]
            refine AddSubgroup.subset_closure ⟨Work.RTOwed.wallHi a 0, ?_, rfl⟩
            rw [Work.RTOwed.sideSlack_wallHi, hyeq, h2]
            push_cast
            ring
          · rw [if_neg h1, if_neg h2]
            exact (Work.FoldInst.Ksub _).zero_mem
      · rw [bindG, if_neg hdi]
        exact (Work.FoldInst.Ksub _).zero_mem
    · by_cases hdi : loB v a b (kfun u) 1 = hiB v a b (kfun u) 1
      · have hyi := mem_loB_hiB v a b (kfun u) y y' hy hy' hd' 1
        have hyeq : y 1 = (loB v a b (kfun u) 1 : ℝ) := le_antisymm (hdi ▸ hyi.2) hyi.1
        rw [bindG, if_pos hdi]
        by_cases h1 : loB v a b (kfun u) 1 = Work.Cusp.cubeCorner a 1
        · rw [if_pos h1]
          refine AddSubgroup.subset_closure ⟨Work.RTOwed.wallLo a 1, ?_, rfl⟩
          rw [Work.RTOwed.sideSlack_wallLo, hyeq, h1]
          push_cast
          ring
        · by_cases h2 : loB v a b (kfun u) 1 = Work.Cusp.cubeCorner a 1 + 1
          · rw [if_neg h1, if_pos h2]
            refine AddSubgroup.subset_closure ⟨Work.RTOwed.wallHi a 1, ?_, rfl⟩
            rw [Work.RTOwed.sideSlack_wallHi, hyeq, h2]
            push_cast
            ring
          · rw [if_neg h1, if_neg h2]
            exact (Work.FoldInst.Ksub _).zero_mem
      · rw [bindG, if_neg hdi]
        exact (Work.FoldInst.Ksub _).zero_mem
    · by_cases hdi : loB v a b (kfun u) 2 = hiB v a b (kfun u) 2
      · have hyi := mem_loB_hiB v a b (kfun u) y y' hy hy' hd' 2
        have hyeq : y 2 = (loB v a b (kfun u) 2 : ℝ) := le_antisymm (hdi ▸ hyi.2) hyi.1
        rw [bindG, if_pos hdi]
        by_cases h1 : loB v a b (kfun u) 2 = Work.Cusp.cubeCorner a 2
        · rw [if_pos h1]
          refine AddSubgroup.subset_closure ⟨Work.RTOwed.wallLo a 2, ?_, rfl⟩
          rw [Work.RTOwed.sideSlack_wallLo, hyeq, h1]
          push_cast
          ring
        · by_cases h2 : loB v a b (kfun u) 2 = Work.Cusp.cubeCorner a 2 + 1
          · rw [if_neg h1, if_pos h2]
            refine AddSubgroup.subset_closure ⟨Work.RTOwed.wallHi a 2, ?_, rfl⟩
            rw [Work.RTOwed.sideSlack_wallHi, hyeq, h2]
            push_cast
            ring
          · rw [if_neg h1, if_neg h2]
            exact (Work.FoldInst.Ksub _).zero_mem
      · rw [bindG, if_neg hdi]
        exact (Work.FoldInst.Ksub _).zero_mem
  refine Quotient.sound ?_
  refine ⟨glueGam v a b (kfun u), hK, ?_⟩
  refine Prod.ext ?_ ?_
  · simpa [Work.FoldInst.actX, Work.RTOwed.xbarOf, add_comm] using hcp
  · refine Subtype.ext ?_
    simpa [Work.FoldInst.actX, Work.RTOwed.xbarOf] using haff


/-! ## The cells, the branch, and its continuity -/

theorem isClosed_cubeBox (a : Fin 48) : IsClosed (Work.RTOwed.cubeBox a) := by
  have h : Work.RTOwed.cubeBox a = ⋂ i : Fin 3,
      ({x : Work.RTOwed.CuspE3 | (Work.Cusp.cubeCorner a i : ℝ) ≤ x i} ∩
       {x : Work.RTOwed.CuspE3 | x i ≤ (Work.Cusp.cubeCorner a i : ℝ) + 1}) := by
    ext x; simp only [Work.RTOwed.cubeBox, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_inter_iff]
  rw [h]
  exact isClosed_iInter fun i => IsClosed.inter
    (isClosed_le continuous_const (by fun_prop)) (isClosed_le (by fun_prop) continuous_const)

/-- The cell of the cube `a` at the offset `lamV v k`: the translate `cubeBox a + lamV v k`. -/
def cell (v : Fin 5) (a : Fin 48) (k : Fin 3 → ℤ) : Set Work.RTOwed.CuspE3 :=
  {x | x - lamV v k ∈ Work.RTOwed.cubeBox a}

theorem isClosed_cell (v : Fin 5) (a : Fin 48) (k : Fin 3 → ℤ) : IsClosed (cell v a k) := by
  have h : cell v a k = (fun x : Work.RTOwed.CuspE3 => x - lamV v k) ⁻¹' Work.RTOwed.cubeBox a := rfl
  rw [h]
  exact (isClosed_cubeBox a).preimage (continuous_id.sub continuous_const)

theorem continuous_kleinPt (a : Fin 48) : Continuous (Work.RTOwed.kleinPt a) := by
  unfold Work.RTOwed.kleinPt
  fun_prop

/-- The branch of `mbarPt v` on the cell of `a` at the offset `k`. -/
noncomputable def branch (v : Fin 5) (a : Fin 48) (k : Fin 3 → ℤ) (x : cell v a k) :
    Work.FoldInst.Mbar :=
  Work.FoldInst.mk (xbarOf a (Work.RTOwed.kleinPt a (x.1 - lamV v k))
    (Work.RTOwed.cuspCert.cube_quad.1 a (x.1 - lamV v k) x.2))

theorem continuous_branch (v : Fin 5) (a : Fin 48) (k : Fin 3 → ℤ) :
    Continuous (branch v a k) := by
  unfold branch
  refine (continuous_quotient_mk').comp ?_
  simp only [Work.RTOwed.xbarOf]
  have hk := continuous_kleinPt a
  fun_prop

/-! ## The floor cell and the branch of `mbarPt` -/

/-- `redV v x` is `x` shifted by the integer vector `⌊x⌋ - corner (cubeOf v x)`. -/
theorem redV_eq_sub (v : Fin 5) (x : Work.RTOwed.CuspE3) :
    redV v x = x - WithLp.toLp 2
      (fun i => ((Work.RTOwed.floorV x i - Work.Cusp.cubeCorner (Work.RTOwed.cubeOf v x) i : ℤ) : ℝ)) := by
  apply PiLp.ext; intro i
  simp only [redV, Work.RTOwed.floorV, PiLp.sub_apply, PiLp.toLp_apply, WithLp.ofLp_toLp]
  push_cast
  ring

/-- The lattice coefficient vector of the floor cell of `x`. -/
def floorK (v : Fin 5) (x : Work.RTOwed.CuspE3) : Fin 3 → ℤ :=
  fun i => (Work.RTOwed.floorV x i - Work.Cusp.cubeCorner (Work.RTOwed.cubeOf v x) i)
    / (Work.Cusp.latMod v i : ℤ)

theorem lamK_sub (v : Fin 5) (a b : Fin 3 → ℤ) :
    lamK v (fun i => a i - b i) = fun i => lamK v a i - lamK v b i := by
  funext i; simp only [lamK]; ring

theorem sub_lamV_floorK (v : Fin 5) (x : Work.RTOwed.CuspE3)
    (hdvd : ∀ i, (Work.Cusp.latMod v i : ℤ)
      ∣ (Work.RTOwed.floorV x i - Work.Cusp.cubeCorner (Work.RTOwed.cubeOf v x) i)) :
    x - lamV v (floorK v x) = redV v x := by
  rw [redV_eq_sub]
  congr 1
  apply PiLp.ext; intro i
  simp only [lamV, floorK, lamK, PiLp.toLp_apply]
  rw [Int.mul_ediv_cancel' (hdvd i)]

theorem pm_one_or (n : ℤ) (h : -1 ≤ n ∧ n ≤ 1) : n = -1 ∨ n = 0 ∨ n = 1 := by omega

theorem lam_mod_pos (v : Fin 5) (i : Fin 3) : (0 : ℝ) < (Work.Cusp.latMod v i : ℝ) := by
  exact_mod_cast latMod_pos v i

theorem lam_abs_le (v : Fin 5) (i : Fin 3) (k : Fin 3 → ℤ) :
    ((|k i| : ℤ) : ℝ) ≤ |((lamK v k i : ℤ) : ℝ)| := by
  rw [Int.cast_abs, show ((lamK v k i : ℤ) : ℝ) = (Work.Cusp.latMod v i : ℝ) * (k i : ℝ) by
    simp only [lamK]; push_cast; ring, abs_mul,
    abs_of_pos (lam_mod_pos v i)]
  have : (1 : ℝ) ≤ (Work.Cusp.latMod v i : ℝ) := by
    have := latMod_pos v i; exact_mod_cast this
  nlinarith [abs_nonneg (k i : ℝ)]

/-- **The point of `mbarPt v` on a cell is the branch of that cell.** -/
theorem mbarPt_eq_branch (v : Fin 5) (a : Fin 48) (hca : Work.Cusp.cubeCusp a = v) (k : Fin 3 → ℤ)
    (x : Work.RTOwed.CuspE3) (hx : x ∈ cell v a k)
    (hdvd : ∀ i, (Work.Cusp.latMod v i : ℤ)
      ∣ (Work.RTOwed.floorV x i - Work.Cusp.cubeCorner (Work.RTOwed.cubeOf v x) i)) :
    Work.RTOwed.mbarPt v x = branch v a k ⟨x, hx⟩ := by
  have hx' : x - lamV v k ∈ Work.RTOwed.cubeBox a := hx
  have hy' : redV v x ∈ Work.RTOwed.cubeBox (Work.RTOwed.cubeOf v x) := redV_mem_cubeBox v x
  have hca0 : Work.Cusp.cubeCusp (Work.RTOwed.cubeOf v x) = v := by
    rw [show Work.RTOwed.cubeOf v x = Work.Cusp.cubeOfMod v (Work.RTOwed.floorV x) from rfl]
    exact cubeCusp_cubeOfMod v (Work.RTOwed.floorV x)
  have hm : Work.RTOwed.mbarPt v x
      = Work.FoldInst.mk (xbarOf (Work.RTOwed.cubeOf v x)
          (Work.RTOwed.kleinPt (Work.RTOwed.cubeOf v x) (redV v x))
          (Work.RTOwed.cuspCert.cube_quad.1 (Work.RTOwed.cubeOf v x) (redV v x) hy')) := by
    rw [Work.RTOwed.mbarPt,
      Work.RTOwed.cuspPtX_of_mem v x (Work.RTOwed.cuspCert.cube_quad.1 (Work.RTOwed.cubeOf v x) (redV v x) hy')]
  rw [hm]
  refine (glue_rel v a (Work.RTOwed.cubeOf v x) hca hca0
    (fun i => floorK v x i - k i)
    (fun i => pm_one_or _ (k_bound v a (Work.RTOwed.cubeOf v x) i hca hca0
      (fun j => floorK v x j - k j) (x - lamV v k) (redV v x) hx' hy'
      (by
        have h1 : (x - lamV v k) i = x i - (lamK v k i : ℝ) := by
          simp only [lamV, PiLp.sub_apply, PiLp.toLp_apply, lamK]
        have h2 : (redV v x) i = x i - (lamK v (floorK v x) i : ℝ) := by
          rw [← sub_lamV_floorK v x hdvd]
          simp only [lamV, PiLp.sub_apply, PiLp.toLp_apply, lamK]
        rw [h1, h2, lamK_sub]
        push_cast
        ring)))
    (x - lamV v k) (redV v x) hx' hy'
    (fun i => by
      have h1 : (x - lamV v k) i = x i - (lamK v k i : ℝ) := by
        simp only [lamV, PiLp.sub_apply, PiLp.toLp_apply, lamK]
      have h2 : (redV v x) i = x i - (lamK v (floorK v x) i : ℝ) := by
        rw [← sub_lamV_floorK v x hdvd]
        simp only [lamV, PiLp.sub_apply, PiLp.toLp_apply, lamK]
      rw [h1, h2, lamK_sub]
      push_cast
      ring)).symm


/-! ## The cover of `E3` by the cells, and local finiteness -/

/-- **The residue of the floor vector is the corner of its cube.**  (The cube `cubeOfMod v p` is the
cube whose corner is congruent to `p` modulo the lattice divisors.) -/
theorem floorV_dvd (v : Fin 5) (x : Work.RTOwed.CuspE3) (i : Fin 3) :
    (Work.Cusp.latMod v i : ℤ)
      ∣ (Work.RTOwed.floorV x i - Work.Cusp.cubeCorner (Work.RTOwed.cubeOf v x) i) := by
  simpa only [Work.RTOwed.cubeOf] using cubeOfMod_corner_dvd v (Work.RTOwed.floorV x) i

theorem corner_abs_le : ∀ (a : Fin 48) (i : Fin 3), |Work.Cusp.cubeCorner a i| ≤ 3 := by
  decide +kernel

theorem exists_cell (v : Fin 5) (x : Work.RTOwed.CuspE3) :
    ∃ (a : Fin 48) (k : Fin 3 → ℤ), Work.Cusp.cubeCusp a = v ∧ x ∈ cell v a k := by
  refine ⟨Work.RTOwed.cubeOf v x, floorK v x, ?_, ?_⟩
  · rw [show Work.RTOwed.cubeOf v x = Work.Cusp.cubeOfMod v (Work.RTOwed.floorV x) from rfl]
    exact cubeCusp_cubeOfMod v (Work.RTOwed.floorV x)
  · have h := sub_lamV_floorK v x (fun i => floorV_dvd v x i)
    show x - lamV v (floorK v x) ∈ Work.RTOwed.cubeBox (Work.RTOwed.cubeOf v x)
    rw [h]
    exact redV_mem_cubeBox v x

/-- The index type of the cells of the cusp `v`. -/
abbrev CIdx (v : Fin 5) : Type := {a : Fin 48 // Work.Cusp.cubeCusp a = v} × (Fin 3 → ℤ)

/-- The cell family of the cusp `v`. -/
def CFam (v : Fin 5) : CIdx v → Set Work.RTOwed.CuspE3 := fun p => cell v p.1.1 p.2

theorem locallyFinite_cells (v : Fin 5) : LocallyFinite (CFam v) := by
  intro x
  refine ⟨{y : Work.RTOwed.CuspE3 | ∀ i, |y i - x i| < 1}, ?_, ?_⟩
  · refine IsOpen.mem_nhds ?_ ?_
    · have h : {y : Work.RTOwed.CuspE3 | ∀ i, |y i - x i| < 1}
          = ⋂ i : Fin 3, {y : Work.RTOwed.CuspE3 | |y i - x i| < 1} := by
        ext y; simp only [Set.mem_ofPred_eq, Set.mem_iInter]
      rw [h]
      exact isOpen_iInter_of_finite fun i => isOpen_lt (by fun_prop) continuous_const
    · intro i; simp
  · refine (Set.Finite.prod Set.finite_univ (Set.Finite.pi'
      (t := fun i : Fin 3 => Set.Icc (-(Int.ceil |x i| + 5)) (Int.ceil |x i| + 5))
      (fun i => Set.finite_Icc _ _))).subset ?_
    rintro ⟨⟨a, ha⟩, k⟩ ⟨y, hy1, hy2⟩
    simp only [Set.mem_prod, Set.mem_univ, Set.mem_ofPred_eq, Set.mem_setOf_eq, true_and]
    intro i
    rw [Set.mem_Icc]
    have hy1i := hy1 i
    have hy2i : |y i - x i| < 1 := hy2 i
    have hca : |((Work.Cusp.cubeCorner a i : ℤ) : ℝ)| ≤ 3 := by
      have := corner_abs_le a i
      exact_mod_cast this
    have hlam : |y i - (lamK v k i : ℝ) - (Work.Cusp.cubeCorner a i : ℝ)| ≤ 1 := by
      have h := hy1i
      simp only [PiLp.sub_apply, PiLp.toLp_apply, lamV, lamK] at h
      push_cast at h
      rw [abs_le]
      simp only [lamK]
      push_cast
      exact ⟨by linarith [h.1, h.2], by linarith [h.1, h.2]⟩
    have hyb : |y i| ≤ |x i| + 1 := by
      have h1 : |y i - x i| ≤ 1 := le_of_lt hy2i
      calc |y i| = |(y i - x i) + x i| := by ring_nf
        _ ≤ |y i - x i| + |x i| := abs_add_le _ _
        _ ≤ 1 + |x i| := by linarith
        _ = |x i| + 1 := by ring
    have habs : |((lamK v k i : ℤ) : ℝ)| ≤ |x i| + 5 := by
      have key : ((lamK v k i : ℤ) : ℝ) = (y i - (Work.Cusp.cubeCorner a i : ℝ))
          - (y i - (lamK v k i : ℝ) - (Work.Cusp.cubeCorner a i : ℝ)) := by ring
      rw [key]
      calc |(y i - (Work.Cusp.cubeCorner a i : ℝ))
            - (y i - (lamK v k i : ℝ) - (Work.Cusp.cubeCorner a i : ℝ))|
          ≤ |y i - (Work.Cusp.cubeCorner a i : ℝ)| + |y i - (lamK v k i : ℝ)
            - (Work.Cusp.cubeCorner a i : ℝ)| := abs_sub _ _
        _ ≤ (|y i| + 3) + 1 := by linarith [abs_sub (y i) ((Work.Cusp.cubeCorner a i : ℝ))]
        _ ≤ |x i| + 5 := by linarith
    have hkl : ((|k i| : ℤ) : ℝ) ≤ |((lamK v k i : ℤ) : ℝ)| := lam_abs_le v i k
    have hb : ((|k i| : ℤ) : ℝ) ≤ (Int.ceil |x i| : ℝ) + 5 := by
      have hc : |x i| ≤ ((Int.ceil |x i| : ℤ) : ℝ) := Int.le_ceil (|x i|)
      linarith
    have hb2 : (|k i| : ℤ) ≤ Int.ceil |x i| + 5 := by exact_mod_cast hb
    exact abs_le.mp hb2

/-! ## Continuity of `mbarPt` -/

theorem mbarPt_continuous : ∀ v : Fin 5, Continuous (Work.RTOwed.mbarPt v) := by
  intro v
  refine (locallyFinite_cells v).continuous ?_ ?_ ?_
  · ext x
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    obtain ⟨a, k, hca, hx⟩ := exists_cell v x
    exact Set.mem_iUnion.mpr ⟨(⟨a, hca⟩, k), hx⟩
  · intro p; exact isClosed_cell v p.1.1 p.2
  · intro p
    rw [continuousOn_iff_continuous_domRestrict]
    refine (continuous_branch v p.1.1 p.2).congr (fun x => ?_)
    exact (mbarPt_eq_branch v p.1.1 p.1.2 p.2 x.1 x.2 (fun i => floorV_dvd v x.1 i)).symm

end Work.RTOwed.cuspCert
