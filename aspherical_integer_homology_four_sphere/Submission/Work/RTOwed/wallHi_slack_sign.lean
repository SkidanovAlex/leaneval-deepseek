/-
# The sign of the side slack of the *upper* wall of a cusp cube

The Möbius chart `Work.RTOwed.chartKlein a (mkE4 u s)` of the cube `a` sends the UHS cube
coordinate `u` (and the height `s`) into the Klein model of `Q̄`.  For the *upper* wall
`S = wallHi a i` (the side of `Q̄` corresponding to the facet `{x i = cubeCorner a i + 1}` of the
cube) this file determines the sign of the side slack

  `sideSlack S y = 1 - ∑_{k<4} n_{S,k} y_k`

of the chart point, in terms of the single coordinate `u i`:

  `sideSlack (wallHi a i) (chartKlein a (mkE4 u s))` is `> 0`, `= 0`, `< 0` according to
  `u i < cubeCorner a i + 1`, `u i = cubeCorner a i + 1`, `u i > cubeCorner a i + 1`.

## The computation

Write `M = chartMat a` and `h = hypOfUHS (mkE4 u s)`, so that the chart point is
`chartKlein a (mkE4 u s) = kleinOfHyp (M *ᵥ h)`, i.e. its `k`-th coordinate is `P k / P 4` with
`P = M *ᵥ h`; hence

  `sideSlack S (chartKlein a (mkE4 u s)) = (P 4 - ∑ n_{S,k} P k) / P 4`.

The numerators `Nside a S x s = chartVec a x s 4 - ∑ n_{S,k} chartVec a x s k` and the chart vector
`chartVec a x s = 2s • P` are the objects of `Submission/Work/RTOwed/chartKlein_mem.lean`, where
`Nside` is expanded as the quadratic form `Qs · q² + ∑ Ls_j x_j + Ks` in the UHS coordinates.

The two integer facts that make the sign computation possible are *finite checks* over the
generated data (`chartMat`, `sideNormal`, `wallHi`, `cubeCorner`):

* `Qs a (wallHi a i) = 0`, `Ls a (wallHi a i) j = 2λ δ_{ij}` and
  `Ks a (wallHi a i) = -2λ (cubeCorner a i + 1)`, where `λ = lamWall a i` is the `i`-th component of
  `L u = M 4 u - ∑_t n_t (M t u)`.  Consequently the numerator is the *linear* function
  `Nside a (wallHi a i) u s = 2λ (u i - (cubeCorner a i + 1))` — the quadratic part cancels and only
  the coordinate `u i` survives (`Nside_wallHi`);
* `λ ∈ {-1, -2}` (`lamWall_eq`), so `2λ < 0`.

Moreover the fourth chart coordinate is positive for every `s ≥ 11/10` (the certificate
`cert4_pos` of `chartKlein_mem`, applied here without any restriction on `u`,
`chartVec4_pos_of_height`).  Dividing, the side slack is `2λ (u i - c) / chartVec a u s 4` with
`2λ < 0` and a positive denominator, and the three sign equivalences follow.

Note that no hypothesis on the height `s` beyond `s ≥ 11/10` and *no* hypothesis on `u` are needed;
the `hu` box hypothesis of the statement is therefore not used in the proof.
-/
import Mathlib
import Submission.Work.RTOwed.cuspChart
import Submission.Work.RTOwed.chartKlein_mem
import Submission.Work.RTOwed.cuspDev

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.unusedVariables false

noncomputable section

open scoped Matrix BigOperators
open Matrix

namespace Work.RTOwed

open chartKleinMem

/-! ## The integer pattern of the upper wall -/

/-- The column of `chartMat a` belonging to the cube coordinate `i : Fin 3`. -/
def col5 (i : Fin 3) : Fin 5 := Fin.castSucc (Fin.castSucc i)

/-- **The proportionality constant `λ` of the upper wall `i`**: the `i`-th component of the vector
`L u = (chartMat a 4 u) - ∑_t n_t (chartMat a t u)`, `n = sideNormal (wallHi a i)`. -/
def lamWall (a : Fin 48) (i : Fin 3) : ℤ :=
  chartMat a 4 (col5 i) -
    ∑ t : Fin 4, Work.FoldInst.sideNormal (wallHi a i) t * chartMat a (Fin.castSucc t) (col5 i)

/-- The constant `λ` of an upper wall is `-1` or `-2` (finite check over the 48 cubes). -/
theorem lamWall_eq : ∀ (a : Fin 48) (i : Fin 3), lamWall a i = -1 ∨ lamWall a i = -2 := by
  decide

/-- The quadratic coefficient of the numerator of the upper wall vanishes. -/
theorem Qs_wallHi : ∀ (a : Fin 48) (i : Fin 3), Qs a (wallHi a i) = 0 := by decide

/-- The linear coefficients of the numerator of the upper wall are `2λ e_i`. -/
theorem Ls_wallHi : ∀ (a : Fin 48) (i : Fin 3) (j : Fin 3),
    Ls a (wallHi a i) j = 2 * lamWall a i * (if j = i then 1 else 0) := by decide

/-- The constant of the numerator of the upper wall is `-2λ (cubeCorner a i + 1)`. -/
theorem Ks_wallHi : ∀ (a : Fin 48) (i : Fin 3),
    Ks a (wallHi a i) = -(2 * lamWall a i) * ((Work.Cusp.cubeCorner a i : ℤ) + 1) := by decide

/-! ## The fourth chart coordinate and the numerator -/

/-- The fourth chart coordinate is strictly positive for every UHS point of height `s ≥ 11/10`
(no restriction on the horizontal coordinate is needed; the certificate `cert4_pos` bounds the
quadratic form at its vertex). -/
theorem chartVec4_pos_of_height (a : Fin 48) (x : CuspE3) {s : ℝ} (hs1 : 11 / 10 ≤ s) :
    0 < chartVec a x s 4 := by
  rw [chartVec_eq]
  exact quad_pos_of_pos (by exact_mod_cast Cq4_pos a) (certPos_bound_pos (cert4_pos a)) x s hs1

/-- **The numerator of the side slack of an upper wall is linear in the single coordinate
`u i`**: `Nside a (wallHi a i) u s = 2λ (u i - (cubeCorner a i + 1))`. -/
theorem Nside_wallHi (a : Fin 48) (i : Fin 3) (x : CuspE3) (s : ℝ) :
    Nside a (wallHi a i) x s
      = 2 * (lamWall a i : ℝ) * (x i - ((Work.Cusp.cubeCorner a i : ℝ) + 1)) := by
  rw [Nside_eq]
  have hQ : ((Qs a (wallHi a i) : ℤ) : ℝ) = 0 := by rw [Qs_wallHi a i]; norm_num
  have hK : ((Ks a (wallHi a i) : ℤ) : ℝ)
      = -(2 * (lamWall a i : ℝ)) * ((Work.Cusp.cubeCorner a i : ℝ) + 1) := by
    rw [Ks_wallHi a i]; push_cast; ring
  have hsum : (∑ j : Fin 3, ((Ls a (wallHi a i) j : ℤ) : ℝ) * x j)
      = ∑ j : Fin 3, (2 * (lamWall a i : ℝ) * (if j = i then 1 else 0)) * x j := by
    apply Finset.sum_congr rfl
    intro j _
    rw [Ls_wallHi a i j]
    by_cases hji : j = i <;> simp [hji]
  have hsingle : (∑ j : Fin 3, (2 * (lamWall a i : ℝ) * (if j = i then 1 else 0)) * x j)
      = 2 * (lamWall a i : ℝ) * x i := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ i) h
  rw [hQ, zero_mul, zero_add, hsum, hsingle, hK]
  ring

/-! ## Elementary sign lemmas -/

private lemma div_neg_iff_of_pos_right' {a B : ℝ} (hB : 0 < B) : a / B < 0 ↔ a < 0 := by
  rw [div_neg_iff]
  constructor
  · rintro (⟨_, h⟩ | ⟨h, _⟩)
    · exact absurd h (not_lt.mpr hB.le)
    · exact h
  · intro h; exact Or.inr ⟨h, hB⟩

private lemma div_eq_zero_iff_of_pos_right' {a B : ℝ} (hB : 0 < B) : a / B = 0 ↔ a = 0 := by
  rw [div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · exact h
    · exact absurd h (ne_of_gt hB)
  · intro h; exact Or.inl h

private lemma neg_mul_pos_iff' {m z : ℝ} (hm : m < 0) : 0 < m * z ↔ z < 0 := by
  constructor
  · intro h
    by_contra hz
    have h1 : m * z ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hm.le (not_lt.mp hz)
    linarith
  · intro hz
    exact mul_pos_of_neg_of_neg hm hz

private lemma neg_mul_neg_iff' {m z : ℝ} (hm : m < 0) : m * z < 0 ↔ 0 < z := by
  constructor
  · intro h
    by_contra hz
    have h1 : 0 ≤ m * z := mul_nonneg_of_nonpos_of_nonpos hm.le (not_lt.mp hz)
    linarith
  · intro hz
    exact mul_neg_of_neg_of_pos hm hz

/-! ## The sign of the side slack -/

theorem wallHi_slack_sign (a : Fin 48) (i : Fin 3) {u : CuspE3} {s : ℝ} (hs : 11 / 10 ≤ s)
    (hu : ∀ j : Fin 3, (Work.Cusp.cubeCorner a j : ℝ) - 1 ≤ u j
      ∧ u j ≤ (Work.Cusp.cubeCorner a j : ℝ) + 2) :
    (0 < Work.FoldInst.sideSlack (wallHi a i) (chartKlein a (mkE4 u s))
        ↔ u i < (Work.Cusp.cubeCorner a i : ℝ) + 1) ∧
    (Work.FoldInst.sideSlack (wallHi a i) (chartKlein a (mkE4 u s)) = 0
        ↔ u i = (Work.Cusp.cubeCorner a i : ℝ) + 1) ∧
    (Work.FoldInst.sideSlack (wallHi a i) (chartKlein a (mkE4 u s)) < 0
        ↔ (Work.Cusp.cubeCorner a i : ℝ) + 1 < u i) := by
  have hs0 : s ≠ 0 := by linarith
  have hB : 0 < chartVec a u s 4 := chartVec4_pos_of_height a u hs
  have h4 : chartVec a u s 4 ≠ 0 := ne_of_gt hB
  have hslack : Work.FoldInst.sideSlack (wallHi a i) (chartKlein a (mkE4 u s))
      = Nside a (wallHi a i) u s / chartVec a u s 4 := sideSlack_eq a (wallHi a i) u s hs0 h4
  have hN : Nside a (wallHi a i) u s
      = 2 * (lamWall a i : ℝ) * (u i - ((Work.Cusp.cubeCorner a i : ℝ) + 1)) :=
    Nside_wallHi a i u s
  have hneg : (2 : ℝ) * (lamWall a i : ℝ) < 0 := by
    rcases lamWall_eq a i with h | h <;> rw [h] <;> norm_num
  rw [hslack, hN]
  refine ⟨?_, ?_, ?_⟩
  · rw [div_pos_iff_of_pos_right hB, neg_mul_pos_iff' hneg]
    constructor <;> intro h <;> linarith
  · rw [div_eq_zero_iff_of_pos_right' hB, mul_eq_zero]
    constructor
    · rintro (h | h)
      · exact absurd h (ne_of_lt hneg)
      · linarith
    · intro h; exact Or.inr (by linarith)
  · rw [div_neg_iff_of_pos_right' hB, neg_mul_neg_iff' hneg]
    constructor <;> intro h <;> linarith

end Work.RTOwed
