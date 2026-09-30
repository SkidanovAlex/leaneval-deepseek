/-
# The perimeter parametrisation `bndOfU` commutes with a quarter turn of the square

`bndOfU : ℝ → ∂Sq` traverses the boundary of the square `Sq = [-1,1]²` counterclockwise,
starting and ending at the corner `(1,1)`, one lap per unit of its argument `u`; `u` is the
normalised perimeter parameter (`Basic.uPerim`, `Basic.u`).  The quarter turn
`rot90 p = (p 1, -(p 0))` of `Work.Cusp.WedgeSCone` carries the `k`-th edge of `Sq` to the
`(k+1)`-st **in the direction in which the perimeter parameter grows** — e.g. it sends the right
edge, traversed from `(1,1)` down to `(1,-1)`, to the bottom edge, traversed from `(1,-1)` to
`(-1,-1)`.  Advancing the perimeter parameter by `1/4` (one edge, since each edge has length `1/4`
in the normalisation of `uPerim`) is therefore the same as applying `rot90`:

`bndOfU (x + 1/4) = rot90 (bndOfU x)`.

The proof is a direct computation.  `bndOfU` depends only on the fractional part
(`bndOfU_fract`), so it suffices to treat `0 ≤ t < 1` (`bndOfU_add_quarter_of_mem`); there the
four quarter intervals of `t` are analysed with the four explicit branch formulas of `bndOfU`
(`bndOfU_lt_quarter`, `bndOfU_lt_half`, `bndOfU_lt_threequarter`, `bndOfU_le_one`), and each
identity is an explicit manipulation of the two coordinates.  In the last interval the argument
`t + 1/4` exceeds `1`, and the periodicity `bndOfU (v + 1) = bndOfU v` (`bndOfU_add_one`) brings it
back to `bndOfU (t - 3/4)`, where `t - 3/4` lies in the first quarter interval.
-/
import Mathlib
import Submission.Work.Cusp.WedgeSCone
import Submission.Work.Cusp.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

/-! ### Two elementary identities about the vector notation `!₂[·,·]` -/

/-- The quarter turn of a vector of `E2` written in coordinates: `(a,b) ↦ (b,-a)`. -/
private lemma rot90_cons (a b : ℝ) : rot90 (!₂[a, b] : E2) = !₂[b, -a] := by
  simp [rot90]

/-- Equality of two explicit vectors `!₂[·,·]` from the two coordinate equalities. -/
private lemma cons2_eq {a b c d : ℝ} (h1 : a = c) (h2 : b = d) :
    (!₂[a, b] : E2) = !₂[c, d] := by
  ext i; fin_cases i <;> simp [h1, h2]

/-! ### The four branches of `bndOfU`

For `v ∈ [0,1)` the definition of `bndOfU` collapses to the branch selected by which quarter of
`[0,1)` contains `v`.  These are the four `rw`-friendly forms of the definition. -/

/-- `bndOfU` on the first quarter interval `[0, 1/4)`: the right edge, from `(1,1)` to `(1,-1)`. -/
private lemma bndOfU_lt_quarter {v : ℝ} (h0 : 0 ≤ v) (h1 : v < 1/4) :
    bndOfU v = !₂[1, 1 - 8 * v] := by
  have hfv : Int.fract v = v := Int.fract_eq_self.mpr ⟨h0, by linarith⟩
  simp only [bndOfU, hfv]
  rw [ite_eq_left h1]

/-- `bndOfU` on `[1/4, 1/2)`: the bottom edge, from `(1,-1)` to `(-1,-1)`. -/
private lemma bndOfU_lt_half {v : ℝ} (h0 : 1/4 ≤ v) (h1 : v < 1/2) :
    bndOfU v = !₂[3 - 8 * v, -1] := by
  have hfv : Int.fract v = v := Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  simp only [bndOfU, hfv]
  rw [ite_eq_right (not_lt.mpr h0), ite_eq_left h1]

/-- `bndOfU` on `[1/2, 3/4)`: the left edge, from `(-1,-1)` to `(-1,1)`. -/
private lemma bndOfU_lt_threequarter {v : ℝ} (h0 : 1/2 ≤ v) (h1 : v < 3/4) :
    bndOfU v = !₂[-1, 8 * v - 5] := by
  have hfv : Int.fract v = v := Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  simp only [bndOfU, hfv]
  rw [ite_eq_right (not_lt.mpr (by linarith : (1:ℝ)/4 ≤ v)),
      ite_eq_right (not_lt.mpr h0), ite_eq_left h1]

/-- `bndOfU` on `[3/4, 1)`: the top edge, from `(-1,1)` back to `(1,1)`. -/
private lemma bndOfU_le_one {v : ℝ} (h0 : 3/4 ≤ v) (h1 : v < 1) :
    bndOfU v = !₂[8 * v - 7, 1] := by
  have hfv : Int.fract v = v := Int.fract_eq_self.mpr ⟨by linarith, h1⟩
  simp only [bndOfU, hfv]
  rw [ite_eq_right (not_lt.mpr (by linarith : (1:ℝ)/4 ≤ v)),
      ite_eq_right (not_lt.mpr (by linarith : (1:ℝ)/2 ≤ v)), ite_eq_right (not_lt.mpr h0)]

/-! ### Periodicity and the reduction to `[0,1)` -/

/-- `bndOfU` is `1`-periodic: `v` and `v + 1` have the same fractional part. -/
private lemma bndOfU_add_one (v : ℝ) : bndOfU (v + 1) = bndOfU v := by
  have h : (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
  simp only [bndOfU]
  rw [h, Int.fract_add_intCast]

/-- `bndOfU` depends only on the fractional part of its argument. -/
private lemma bndOfU_fract (u : ℝ) : bndOfU u = bndOfU (Int.fract u) := by
  have hff : Int.fract (Int.fract u) = Int.fract u :=
    Int.fract_eq_self.mpr ⟨Int.fract_nonneg u, Int.fract_lt_one u⟩
  simp only [bndOfU, hff]

/-! ### The quarter shift on one period -/

/-- **The quarter shift of `bndOfU` on `[0,1)`.**  For `t ∈ [0,1)`, advancing the perimeter
parameter by one quarter, i.e. by one edge, is the quarter turn `rot90`.  The four cases are the
four edges of the square: `rot90` maps each edge onto the next one, preserving the affine
parametrisation of the perimeter. -/
private lemma bndOfU_add_quarter_of_mem {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) :
    bndOfU (t + 1/4) = rot90 (bndOfU t) := by
  rcases lt_or_ge t (1/4) with hA | hA
  · rw [bndOfU_lt_quarter h0 hA, bndOfU_lt_half (by linarith) (by linarith), rot90_cons]
    exact cons2_eq (by ring) (by ring)
  · rcases lt_or_ge t (1/2) with hB | hB
    · rw [bndOfU_lt_half hA hB, bndOfU_lt_threequarter (by linarith) (by linarith), rot90_cons]
      exact cons2_eq (by ring) (by ring)
    · rcases lt_or_ge t (3/4) with hC | hC
      · rw [bndOfU_lt_threequarter hB hC, bndOfU_le_one (by linarith) (by linarith), rot90_cons]
        exact cons2_eq (by ring) (by ring)
      · -- here `t + 1/4 ≥ 1`: bring it back into `[0,1)` with the periodicity of `bndOfU`
        rw [bndOfU_le_one hC h1, show t + 1/4 = (t - 3/4) + 1 by ring, bndOfU_add_one,
          bndOfU_lt_quarter (by linarith) (by linarith), rot90_cons]
        exact cons2_eq (by ring) (by ring)

/-! ### The statement -/

/-- **`bndOfU` commutes with the quarter turn.**  Advancing the perimeter parameter of a boundary
point of `Sq` by `1/4` — one edge of the square — is the same as rotating the point by the quarter
turn `rot90 p = (p 1, -(p 0))` that runs in the direction of increasing perimeter. -/
theorem bndOfU_add_quarter (x : ℝ) : bndOfU (x + 1/4) = rot90 (bndOfU x) := by
  -- `x` and `Int.fract x` differ by an integer, and so do `x + 1/4` and `Int.fract x + 1/4`
  have hfr : Int.fract (x + 1/4) = Int.fract (Int.fract x + 1/4) := by
    conv_lhs => rw [← Int.fract_add_floor x]
    rw [show Int.fract x + ((⌊x⌋ : ℤ) : ℝ) + 1/4
        = (Int.fract x + 1/4) + ((⌊x⌋ : ℤ) : ℝ) by ring]
    rw [Int.fract_add_intCast]
  calc bndOfU (x + 1/4)
      = bndOfU (Int.fract x + 1/4) := by
        rw [bndOfU_fract (x + 1/4), hfr]
        exact (bndOfU_fract (Int.fract x + 1/4)).symm
    _ = rot90 (bndOfU (Int.fract x)) :=
        bndOfU_add_quarter_of_mem (Int.fract_nonneg x) (Int.fract_lt_one x)
    _ = rot90 (bndOfU x) := by rw [bndOfU_fract x]

end Work.Cusp
