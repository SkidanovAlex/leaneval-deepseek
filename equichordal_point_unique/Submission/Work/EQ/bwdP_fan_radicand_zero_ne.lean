import Mathlib
import Submission.Work.EQ.bwdFanDefs
import Submission.Work.EQ.fan_estimates

/-!
# The labelled radicands of the backward fan iterates are nonzero

`bwdP a σ (fan a h ε 0)` is the `σ`-fold backward image of the centre of the fan word `ε`
(the point at index `-|σ|` of the chain whose index-`0` point is the fan centre).  This file
shows that the radicand `bsq (subO1 a ·) = (x + a/2)^2 + y^2` of *that* point never vanishes,
for every pair of words `σ`, `ε` and every stable germ with `0 < a < 1`.

The proof is essentially a sanity fact about the axis:

* `bwdP_fan_eq_fan_aux` says that a backward iterate of a fan value is a fan value again, with
  the same small argument `0`: `bwdP a σ (fan a h ε 0) = fan a h (σ.reverse ++ ε) 0`;
* `fan_centres` locates that centre on the axis, at a point `(-1/2 + 2k, 0)` of the coset
  `-1/2 + 2ℤ`;
* for `0 < a < 1` no such point coincides with `O₁ = (-a/2, 0)`, since `-1/2 + 2k + a/2 = 0`
  would force `k = (1-a)/4 ∈ (0, 1/4)`, impossible for an integer.
-/

namespace Work.EQ

open Complex Metric Filter _root_.Topology

noncomputable section

/-- For `0 < a < 1`, the abscissa `-1/2 + 2k` of a fan centre is never equal to `-a/2`: the
equation `-1/2 + 2k + a/2 = 0` forces `k = (1-a)/4`, which lies strictly between `0` and `1/4`
and is therefore not an integer. -/
theorem fan_centre_add_half_ne_zero {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (k : ℤ) :
    -1 / 2 + 2 * (k : ℝ) + a / 2 ≠ 0 := by
  intro h
  have hk4 : (k : ℝ) = (1 - a) / 4 := by linarith
  have hk_pos : (0 : ℝ) < (k : ℝ) := by rw [hk4]; linarith
  have hk_lt : (k : ℝ) < 1 / 4 := by rw [hk4]; nlinarith
  have hk1 : (1 : ℤ) ≤ k := by
    have : (0 : ℤ) < k := by exact_mod_cast hk_pos
    omega
  have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  linarith

/-- **The labelled radicand of a backward fan iterate is nonzero.**  For every sign list `σ` and
every branch word `ε`, the point `bwdP a σ (fan a h ε 0)` has `bsq (subO1 a ·) ≠ 0`, i.e. it is
off the isotropic lines through `O₁ = (-a/2, 0)`; equivalently the corresponding backward branch
`invBranch` is non-degenerate there. -/
theorem bwdP_fan_radicand_zero_ne {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) (ε σ : List Bool) :
    bsq (subO1 a (bwdP a σ (fan a h ε 0))) ≠ 0 := by
  have hlam : (0 : ℝ) < eqLam a := eqLam_pos' ha0 ha1
  have hlam0 : ((eqLam a : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hlam)
  -- a backward iterate of a fan value is a fan value again, at the same argument `0`
  have hid := bwdP_fan_eq_fan_aux (a := a) h hlam0 σ ε 0
  rw [zero_div] at hid
  rw [hid]
  -- the new centre lies on the axis at `-1/2 + 2ℤ`
  obtain ⟨hz, k, hk⟩ := fan_centres ha0 ha1 hh (σ.reverse ++ ε)
  have hpt : fan a h (σ.reverse ++ ε) 0 =
      ((((-1 / 2 + 2 * (k : ℝ)) : ℝ) : ℂ), (0 : ℂ)) := by
    rw [Prod.ext_iff]; exact ⟨hk, hz⟩
  rw [hpt]
  -- translating by `O₁` gives the axis point `-1/2 + 2k + a/2`
  have hsub : subO1 a ((((-1 / 2 + 2 * (k : ℝ)) : ℝ) : ℂ), (0 : ℂ)) =
      (((-1 / 2 + 2 * (k : ℝ) + a / 2 : ℝ) : ℂ), (0 : ℂ)) := by
    apply Prod.ext
    · simp only [subO1]
      push_cast
      ring
    · simp only [subO1]
  rw [hsub]
  have hx : (-1 / 2 + 2 * (k : ℝ) + a / 2) ≠ 0 := fan_centre_add_half_ne_zero ha0 ha1 k
  simp only [bsq]
  rw [show ((0 : ℂ) ^ 2) = 0 by ring, add_zero]
  exact pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hx)

end

end Work.EQ
