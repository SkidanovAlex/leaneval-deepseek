/-
# The pieces of the cusp chart cover are open in `X̄`

This file proves `Work.RTOwed.isOpen_piece`: for a cusp `v`, a cube `a`, a lattice offset `k` and an
open set `B ⊆ E4` of positive height, the *piece*

  `piece v a k B = {x : Z̄ × Q̄ | x.1 = cubeBit a ∧ ∃ q ∈ pieceSrc v a k B, x.2.1 = cellPt v a k q}`

of `Submission/Work/RTOwed/CuspPiece.lean` is open in `X̄ = ZMod 2 × Q̄`.

## The mathematics

`piece v a k B` is the set of points of `X̄` of copy bit `cubeBit a` whose underlying Klein point is
the value of the Möbius chart of the cube `a` at an *unfolded* cube coordinate
`u = uhsXj q - lamV v k ∈ [cubeCorner a - 1, cubeCorner a + 2]³` of a point `q ∈ B`.

The box of `pieceSrc` is closed, so the chart is not literally the image of an open set; the box is
however *one unit too wide*: the chart of the cube `a` meets the truncated 24-cell `Q̄` only over the
closed unit cube `cubeBox a` of the *cube coordinates*:

  `chartKlein a (mkE4 u s) ∈ Q̄ → u ∈ cubeBox a`   (`cubeBox_of_mem_Qbar`),

for every positive height `s`.  Hence the closed box in `pieceSrc` may be replaced by its interior,

  `piece v a k B = {x | x.1 = cubeBit a ∧ x.2.1 ∈ chartKlein a '' (wPt v k '' B ∩ boxOpen a)}`,

and both conditions on the right are open: the first because `ZMod 2` is discrete, the second
because the affine coordinate change `wPt v k` is a homeomorphism, the box `boxOpen a` is open, and
`chartKlein a` is an open map on the region of positive height (`chartKlein_image_open`).

The chamber fact `cubeBox_of_mem_Qbar` is proved from the *wall slacks*: the sides
`wallLo a i` and `wallHi a i` of `Q̄` have, at the chart point, the slacks

  `sideSlack (wallLo a i) (chartKlein a (mkE4 u s)) = L · (u i - cubeCorner a i) / chartVec a u s 4`,
  `sideSlack (wallHi a i) (chartKlein a (mkE4 u s)) = 2λ · (u i - cubeCorner a i - 1) / chartVec a u s 4`

with `L > 0` (`wallLo_Ls_pos_all`), `2λ < 0` (`lamWall_eq`) and `chartVec a u s 4 > 0`
(`chartVec4_pos_any`, positive for *every* `u` and `s`: the quadratic coefficient `Cq a 4` is
positive — `Cq4_pos` — and the vertex value is `cert4any a / (4 Cq a 4) > 0`, a finite check).
-/
import Mathlib
import Submission.Work.RTOwed.CuspPiece
import Submission.Work.RTOwed.chartKlein_image_open
import Submission.Work.RTOwed.wallLo_slack_sign
import Submission.Work.RTOwed.wallHi_slack_sign
import Submission.Work.RTOwed.chartKlein_mem
import Submission.Work.Cusp.Assembly

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function
open scoped BigOperators Matrix

namespace Work.RTOwed

open chartKleinMem

/-! ## The fourth chart coordinate is positive at every UHS point -/

/-- The integer certificate for the strict positivity of the fourth chart coordinate at *every*
UHS point: `4 Cq · Ck - Σ_j (Cl_j)²`, the numerator of the vertex value of the quadratic form
`chartVec a · 4`. -/
def cert4any (a : Fin 48) : ℤ :=
  4 * Cq a 4 * Ck a 4 - ∑ j : Fin 3, Cl a 4 j ^ 2

/-- The certificate is positive (finite check over the 48 cubes). -/
theorem cert4any_pos : ∀ a : Fin 48, 0 < cert4any a := by decide

/-- **The fourth chart coordinate is positive at every UHS point.**  `chartVec a x s 4` is the
quadratic form `Cq · q² + Σ_j Cl_j x_j + Ck` with `Cq > 0`; completing the square it equals
`Cq · (Σ_j (x_j + Cl_j/(2 Cq))² + s²) + cert4any/(4 Cq)`, and both terms are positive. -/
theorem chartVec4_pos_any (a : Fin 48) (x : CuspE3) (s : ℝ) :
    0 < chartVec a x s 4 := by
  rw [chartVec_eq]
  set c : ℝ := (Cq a 4 : ℝ) with hcdef
  set e : ℝ := (Ck a 4 : ℝ) with hedef
  set l : Fin 3 → ℝ := fun j => (Cl a 4 j : ℝ) with hldef
  have hc : 0 < c := by rw [hcdef]; exact_mod_cast Cq4_pos a
  have hcert : (0 : ℝ) < 4 * c * e - ∑ j : Fin 3, (l j) ^ 2 := by
    have h := cert4any_pos a
    have hcast : ((cert4any a : ℤ) : ℝ) = 4 * c * e - ∑ j : Fin 3, (l j) ^ 2 := by
      simp only [cert4any, hcdef, hedef, hldef]
      push_cast
      ring
    rw [← hcast]
    exact_mod_cast h
  have hkey : c * qsq x s + ∑ j : Fin 3, l j * x j + e
      = c * (∑ j : Fin 3, (x j + l j / (2 * c)) ^ 2 + s ^ 2)
        + (4 * c * e - ∑ j : Fin 3, (l j) ^ 2) / (4 * c) := by
    have hc0 : c ≠ 0 := ne_of_gt hc
    simp only [qsq, Fin.sum_univ_three]
    field_simp
    ring
  have hmin : 0 < (4 * c * e - ∑ j : Fin 3, (l j) ^ 2) / (4 * c) :=
    div_pos hcert (by linarith)
  have hnn : 0 ≤ c * (∑ j : Fin 3, (x j + l j / (2 * c)) ^ 2 + s ^ 2) :=
    mul_nonneg hc.le (by positivity)
  linarith [hkey, hmin, hnn]

/-! ## The chamber fact: the chart of a cube meets `Q̄` only over the cube -/

/-- **The chart of the cube `a` meets `Q̄` only over the closed unit cube.**  If the chart point
`chartKlein a (mkE4 x s)` of a point of positive height lies in the truncated 24-cell, then the cube
coordinate `x` lies in `cubeBox a`.

The two *walls* of the cube `a` in the `i`-th coordinate are sides of `Q̄`
(`wallLo a i`, `wallHi a i`), and at the chart point their slacks are

  `Ls a (wallLo a i) i · (x i - c) / chartVec a x s 4`,
  `2 λ · (x i - c - 1) / chartVec a x s 4`,

with `Ls a (wallLo a i) i > 0` and `λ < 0` (`wallLo_Nside`, `Nside_wallHi`, `wallLo_Ls_pos_all`,
`lamWall_eq`) and with the denominator `chartVec a x s 4 > 0` for *every* `(x, s)`
(`chartVec4_pos_any`).  Membership in `Q̄` makes both slacks nonnegative, which forces
`c ≤ x i ≤ c + 1`. -/
theorem cubeBox_of_mem_Qbar (a : Fin 48) {x : CuspE3} {s : ℝ} (hs : 0 < s)
    (hQ : chartKlein a (mkE4 x s) ∈ Work.FoldInst.Qbar) : x ∈ cubeBox a := by
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hV : 0 < chartVec a x s 4 := chartVec4_pos_any a x s
  have hVne : chartVec a x s 4 ≠ 0 := ne_of_gt hV
  intro j
  constructor
  · -- the lower wall `wallLo a j`
    have hsl : (0 : ℝ) ≤ Work.FoldInst.sideSlack (wallLo a j) (chartKlein a (mkE4 x s)) :=
      hQ.1 (wallLo a j)
    rw [chartKleinMem.sideSlack_eq a (wallLo a j) x s hs0 hVne, wallLo_Nside a j x s] at hsl
    have hq : 0 < (Ls a (wallLo a j) j : ℝ) / chartVec a x s 4 :=
      div_pos (by exact_mod_cast wallLo_Ls_pos_all a j) hV
    have hsl' : (0 : ℝ) ≤ ((Ls a (wallLo a j) j : ℝ) / chartVec a x s 4)
        * (x j - (Work.Cusp.cubeCorner a j : ℝ)) := by
      have hsplit : (Ls a (wallLo a j) j : ℝ) * (x j - (Work.Cusp.cubeCorner a j : ℝ))
          / chartVec a x s 4
          = ((Ls a (wallLo a j) j : ℝ) / chartVec a x s 4)
            * (x j - (Work.Cusp.cubeCorner a j : ℝ)) := by ring
      rwa [hsplit] at hsl
    have := nonneg_of_mul_nonneg_right hsl' hq
    linarith
  · -- the upper wall `wallHi a j`
    have hsl : (0 : ℝ) ≤ Work.FoldInst.sideSlack (wallHi a j) (chartKlein a (mkE4 x s)) :=
      hQ.1 (wallHi a j)
    rw [chartKleinMem.sideSlack_eq a (wallHi a j) x s hs0 hVne, Nside_wallHi a j x s] at hsl
    have hm : 2 * (lamWall a j : ℝ) / chartVec a x s 4 < 0 :=
      div_neg_of_neg_of_pos (by rcases lamWall_eq a j with h | h <;> rw [h] <;> norm_num) hV
    have hsl' : (0 : ℝ) ≤ (2 * (lamWall a j : ℝ) / chartVec a x s 4)
        * (x j - ((Work.Cusp.cubeCorner a j : ℝ) + 1)) := by
      have hsplit : 2 * (lamWall a j : ℝ) * (x j - ((Work.Cusp.cubeCorner a j : ℝ) + 1))
          / chartVec a x s 4
          = (2 * (lamWall a j : ℝ) / chartVec a x s 4)
            * (x j - ((Work.Cusp.cubeCorner a j : ℝ) + 1)) := by ring
      rwa [hsplit] at hsl
    have hz : x j - ((Work.Cusp.cubeCorner a j : ℝ) + 1) ≤ 0 :=
      nonpos_of_mul_nonneg_right hsl' hm
    linarith

/-! ## The affine coordinate change of the unfolded chart -/

/-- The coordinate change `q ↦ (uhsXj q - lamV v k, q 3)` of the unfolded chart: the argument of
`cellPt v a k`. -/
def wPt (v : Fin 5) (k : Fin 3 → ℤ) (q : CuspE4) : CuspE4 :=
  mkE4 (uhsXj q - cuspCert.lamV v k) (q 3)

/-- The inverse coordinate change (`wPt v k` is an affine bijection of `E4`). -/
def wPtInv (v : Fin 5) (k : Fin 3 → ℤ) (p : CuspE4) : CuspE4 :=
  mkE4 (xOf4 p + cuspCert.lamV v k - cuspH) (p 3)

/-- **The cell chart is the Möbius chart of the transformed point.** -/
theorem cellPt_eq_chartKlein (v : Fin 5) (a : Fin 48) (k : Fin 3 → ℤ) (q : CuspE4) :
    cellPt v a k q = chartKlein a (wPt v k q) := rfl

/-- The horizontal part of the transformed point. -/
theorem xOf4_wPt (v : Fin 5) (k : Fin 3 → ℤ) (q : CuspE4) :
    xOf4 (wPt v k q) = uhsXj q - cuspCert.lamV v k := by
  ext j
  fin_cases j <;> simp [xOf4, wPt, mkE4]

/-- The height of the transformed point. -/
theorem wPt_apply_three (v : Fin 5) (k : Fin 3 → ℤ) (q : CuspE4) : (wPt v k q) 3 = q 3 := by
  simp [wPt, mkE4]

theorem wPtInv_wPt (v : Fin 5) (k : Fin 3 → ℤ) (q : CuspE4) : wPtInv v k (wPt v k q) = q := by
  ext i
  fin_cases i <;>
    simp [wPtInv, wPt, mkE4, xOf4, uhsXj, cuspH, PiLp.toLp_apply, PiLp.add_apply, PiLp.sub_apply]

theorem wPt_wPtInv (v : Fin 5) (k : Fin 3 → ℤ) (p : CuspE4) : wPt v k (wPtInv v k p) = p := by
  ext i
  fin_cases i <;>
    simp [wPtInv, wPt, mkE4, xOf4, uhsXj, cuspH, PiLp.toLp_apply, PiLp.add_apply, PiLp.sub_apply]

theorem continuous_wPt (v : Fin 5) (k : Fin 3 → ℤ) : Continuous (wPt v k) := by
  unfold wPt mkE4 uhsXj xOf4 cuspH cuspCert.lamV cuspCert.lamK
  fun_prop

theorem continuous_wPtInv (v : Fin 5) (k : Fin 3 → ℤ) : Continuous (wPtInv v k) := by
  unfold wPtInv mkE4 xOf4 cuspH cuspCert.lamV cuspCert.lamK
  fun_prop

/-! ## The open box of the unfolded coordinates, and the piece -/

/-- The open box of the unfolded cube coordinates of the cube `a` (the *interior* of the box of
`pieceSrc`, which has half-width `1` and `2`). -/
def boxOpen (a : Fin 48) : Set CuspE4 :=
  {p | ∀ j : Fin 3, (Work.Cusp.cubeCorner a j : ℝ) - 1 < xOf4 p j
    ∧ xOf4 p j < (Work.Cusp.cubeCorner a j : ℝ) + 2}

/-- **The open source of the piece**: the image of `B` under the coordinate change, intersected
with the open box. -/
def pieceOpen (v : Fin 5) (a : Fin 48) (k : Fin 3 → ℤ) (B : Set CuspE4) : Set CuspE4 :=
  wPt v k '' B ∩ boxOpen a

theorem isOpen_boxOpen (a : Fin 48) : IsOpen (boxOpen a) := by
  have hcont : ∀ j : Fin 3, Continuous (fun p : CuspE4 => xOf4 p j) := by
    intro j
    unfold xOf4
    fun_prop
  rw [show boxOpen a = ⋂ j : Fin 3,
      ({p : CuspE4 | (Work.Cusp.cubeCorner a j : ℝ) - 1 < xOf4 p j}
        ∩ {p : CuspE4 | xOf4 p j < (Work.Cusp.cubeCorner a j : ℝ) + 2}) from by
    ext p
    simp [boxOpen]]
  exact isOpen_iInter_of_finite fun j =>
    (isOpen_lt continuous_const (hcont j)).inter (isOpen_lt (hcont j) continuous_const)

theorem isOpen_image_wPt (v : Fin 5) (k : Fin 3 → ℤ) {B : Set CuspE4} (hB : IsOpen B) :
    IsOpen (wPt v k '' B) := by
  rw [show wPt v k '' B = wPtInv v k ⁻¹' B from by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      change wPtInv v k (wPt v k q) ∈ B
      rw [wPtInv_wPt]
      exact hq
    · intro hp
      exact ⟨wPtInv v k p, hp, wPt_wPtInv v k p⟩]
  exact hB.preimage (continuous_wPtInv v k)

theorem isOpen_pieceOpen (v : Fin 5) (a : Fin 48) (k : Fin 3 → ℤ) {B : Set CuspE4}
    (hB : IsOpen B) : IsOpen (pieceOpen v a k B) :=
  (isOpen_image_wPt v k hB).inter (isOpen_boxOpen a)

/-! ## The piece as the image of the open box -/

/-- **The piece is the image of the open box.**  The closed box of `pieceSrc` is one unit wider on
each side than the cube, and by the chamber fact (`cubeBox_of_mem_Qbar`) the chart of the cube meets
`Q̄` only over the cube itself; hence a point of the piece is already obtained from a point of `B`
whose unfolded coordinate lies in the *open* box. -/
theorem piece_eq_pieceOpen (v : Fin 5) (a : Fin 48) (k : Fin 3 → ℤ) (B : Set CuspE4)
    (hBpos : ∀ q ∈ B, 0 < q 3) :
    piece v a k B
      = {x : CuspXbar | x.1 = cubeBit a ∧ x.2.1 ∈ chartKlein a '' pieceOpen v a k B} := by
  ext x
  constructor
  · rintro ⟨h1, q, hq, hqx⟩
    refine ⟨h1, wPt v k q, ⟨⟨q, hq.1, rfl⟩, ?_⟩, ?_⟩
    · have hQ : chartKlein a (wPt v k q) ∈ Work.FoldInst.Qbar := by
        rw [← cellPt_eq_chartKlein v a k q, ← hqx]
        exact x.2.2
      have hcube := cubeBox_of_mem_Qbar a (hBpos q hq.1) hQ
      intro j
      have hx : xOf4 (wPt v k q) j = (uhsXj q - cuspCert.lamV v k) j := by rw [xOf4_wPt]
      have hj := hcube j
      constructor
      · rw [hx]; linarith [hj.1]
      · rw [hx]; linarith [hj.2]
    · rw [← cellPt_eq_chartKlein v a k q]
      exact hqx.symm
  · rintro ⟨h1, p, hp, hpchart⟩
    obtain ⟨q, hqB, hqp⟩ := hp.1
    refine ⟨h1, q, ⟨hqB, ?_⟩, ?_⟩
    · intro j
      have hboxj := hp.2 j
      have hx : xOf4 p j = (uhsXj q - cuspCert.lamV v k) j := by
        rw [← hqp, xOf4_wPt]
      constructor <;> linarith [hboxj.1, hboxj.2, hx]
    · rw [cellPt_eq_chartKlein, hqp]
      exact hpchart.symm

/-! ## The target -/

theorem isOpen_piece (v : Fin 5) {B : Set CuspE4} (hB : IsOpen B)
    (hBpos : ∀ q ∈ B, 0 < q 3) (a : Fin 48) (k : Fin 3 → ℤ) : IsOpen (piece v a k B) := by
  rw [piece_eq_pieceOpen v a k B hBpos]
  have hU : IsOpen (chartKlein a '' pieceOpen v a k B) := by
    refine chartKlein_image_open a (isOpen_pieceOpen v a k hB) ?_
    intro p hp
    obtain ⟨q, hqB, hqp⟩ := hp.1
    rw [← hqp, wPt_apply_three]
    exact hBpos q hqB
  have h1 : IsOpen {x : CuspXbar | x.1 = cubeBit a} := by
    rw [show {x : CuspXbar | x.1 = cubeBit a}
        = Prod.fst ⁻¹' ({cubeBit a} : Set (ZMod 2)) from rfl]
    exact (isOpen_discrete _).preimage continuous_fst
  have h2 : IsOpen {x : CuspXbar | x.2.1 ∈ chartKlein a '' pieceOpen v a k B} := by
    rw [show {x : CuspXbar | x.2.1 ∈ chartKlein a '' pieceOpen v a k B}
        = (fun x : CuspXbar => ((x.2 : Work.FoldInst.Qbar) : CuspE4)) ⁻¹'
            (chartKlein a '' pieceOpen v a k B) from rfl]
    exact hU.preimage (continuous_subtype_val.comp continuous_snd)
  rw [show {x : CuspXbar | x.1 = cubeBit a ∧ x.2.1 ∈ chartKlein a '' pieceOpen v a k B}
      = {x : CuspXbar | x.1 = cubeBit a}
        ∩ {x : CuspXbar | x.2.1 ∈ chartKlein a '' pieceOpen v a k B} from rfl]
  exact h1.inter h2

end Work.RTOwed
