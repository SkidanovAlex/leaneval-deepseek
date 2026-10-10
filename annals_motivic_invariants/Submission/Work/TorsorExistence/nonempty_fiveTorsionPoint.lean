import Mathlib
import Submission.Work.TorsorExistence.Defs
import Submission.Work.TorsorExistence.Tate.Defs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# Over every infinite field there is an elliptic curve with `j ≠ 1728` and a point of order `5`

This file proves `Work.TorsorExistence.nonempty_fiveTorsionPoint` by exhibiting the Tate normal
form

`E(c) : y² + (1 - c)xy - cy = x³ - cx²`,  i.e. `(a₁, a₂, a₃, a₄, a₆) = (1 - c, -c, -c, 0, 0)`,

whose affine point `T = (0, 0)` satisfies `2T = (c, c²)`, `4T = (0, c) = -T` and hence
`5T = 0`.  Its discriminant and `c₄`-invariant are

`Δ(E(c)) = c⁵(c² - 11c - 1)`,  `c₄(E(c)) = c⁴ - 12c³ + 14c² + 12c + 1`,

so `E(c)` is elliptic iff `c⁵(c² - 11c - 1) ≠ 0`, and (using `j = c₄³/Δ`) its `j`-invariant is
`1728` iff `c₄³ = 1728·c⁵(c² - 11c - 1)`.  Both conditions are polynomial equations in `c`
whose solution set is finite (the associated polynomial has degree `15` and leading coefficient
`1` in *every* characteristic), so an infinite field contains a good `c`.

## Main results

* `Work.TorsorExistence.Tate.tateCurve_Δ`, `tateCurve_c₄` (`Tate/Defs.lean`): the invariants.
* `Work.TorsorExistence.Tate.exists_tate_param`: a good parameter exists over any infinite field.
* `Work.TorsorExistence.Tate.tate_five_smul`: for `c ≠ 0` the point `(0,0)` of `E(c)` satisfies
  `5 • (0,0) = 0`.
* `Work.TorsorExistence.nonempty_fiveTorsionPoint`: the conclusion.
-/

noncomputable section

namespace Work.TorsorExistence.Tate

open WeierstrassCurve WeierstrassCurve.Affine Polynomial

section Arithmetic

variable {𝕜 : Type} [Field 𝕜] [Infinite 𝕜]

/-- **A good Tate parameter exists over any infinite field.**

The two bad conditions `c⁵(c² - 11c - 1) = 0` (singularity of the Tate normal form) and
`c₄³ = 1728·c⁵(c² - 11c - 1)` (i.e. `j = 1728`) are the vanishing conditions of the two factors
of the polynomial

`R = X·(X² - 11X - 1)·((X⁴ - 12X³ + 14X² + 12X + 1)³ - 1728·X⁵·(X² - 11X - 1))`.

`R` is nonzero in every characteristic: all three of its factors are nonzero (the first is `X`,
the second takes the value `-1` at `0`, and for the third, `Q(0) = A(0)³ = 1`, so `Q = 0` would
force `1 = A(0)³ = 1728·0 = 0`, a contradiction — this works even in characteristic `2`, where
`Q` degenerates to `(X+1)¹²`).  Hence the root set of `R` is finite, and an infinite field has
an element outside a finite set. -/
theorem exists_tate_param :
    ∃ c : 𝕜, c ^ 5 * (c ^ 2 - 11 * c - 1) ≠ 0 ∧
      (c ^ 4 - 12 * c ^ 3 + 14 * c ^ 2 + 12 * c + 1) ^ 3 ≠
        1728 * (c ^ 5 * (c ^ 2 - 11 * c - 1)) := by
  classical
  set A : 𝕜[X] := X ^ 4 - C 12 * X ^ 3 + C 14 * X ^ 2 + C 12 * X + C 1 with hA
  set B : 𝕜[X] := X ^ 5 * (X ^ 2 - C 11 * X - C 1) with hB
  set Q : 𝕜[X] := A ^ 3 - C 1728 * B with hQ
  set R : 𝕜[X] := X * (X ^ 2 - C 11 * X - C 1) * Q with hR
  -- `A(0) = 1`, so `A ≠ 0`; `X² - 11X - 1` evaluated at `0` is `-1`, so it is nonzero too
  have hA0 : Polynomial.eval (0 : 𝕜) A = 1 := by simp [hA]
  have hquad : (X ^ 2 - C 11 * X - C 1 : 𝕜[X]) ≠ 0 := by
    intro hh
    have h1 := congrArg (Polynomial.eval (0 : 𝕜)) hh
    simp at h1
  -- if `Q` vanished, then evaluating `A ^ 3 = 1728·B` at `0` would give `1 = 0`
  have hQ0 : Q ≠ 0 := by
    intro hh
    have h3 : A ^ 3 = C 1728 * B := by
      have h4 : A ^ 3 - C 1728 * B = 0 := by rw [← hQ]; exact hh
      exact sub_eq_zero.mp h4
    have h5 := congrArg (Polynomial.eval (0 : 𝕜)) h3
    rw [Polynomial.eval_pow, hA0, Polynomial.eval_mul, Polynomial.eval_C] at h5
    simp [hB] at h5
  have hR0 : R ≠ 0 := by
    rw [hR]
    exact mul_ne_zero (mul_ne_zero X_ne_zero hquad) hQ0
  -- a nonzero polynomial over an infinite field has a non-root
  obtain ⟨c, hc⟩ : ∃ c : 𝕜, ¬ R.IsRoot c := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hR0 (Polynomial.eq_zero_of_infinite_isRoot R (by
      have hone : {x : 𝕜 | R.IsRoot x} = Set.univ := by
        ext x; exact ⟨fun _ => trivial, fun _ => h x⟩
      rw [hone]; exact Set.infinite_univ))
  have hcR : R.eval c ≠ 0 := by simpa [Polynomial.IsRoot.def] using hc
  rw [hR, hQ, hA, hB] at hcR
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C] at hcR
  rw [mul_ne_zero_iff] at hcR
  obtain ⟨hcl, hcq⟩ := hcR
  rw [mul_ne_zero_iff] at hcl
  obtain ⟨hc0, hcquad⟩ := hcl
  exact ⟨c, mul_ne_zero (pow_ne_zero 5 hc0) hcquad, sub_ne_zero.mp hcq⟩

end Arithmetic

section PointLaw

variable {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]

/-- **The Tate normal form has a rational point of order five.**

For `c ≠ 0` the point `T = (0,0)` of `E(c) : y² + (1-c)xy - cy = x³ - cx²` satisfies
`2T = (c, c²)`, `4T = (0, c) = -T`, hence `5T = 0`.  All denominators occurring in the
chord–tangent formulae are powers of `c`, so no hypothesis on the characteristic is needed. -/
theorem tate_five_smul (c : 𝕜) (hc : c ≠ 0) (h : Nonsingular (tateCurve c) 0 0) :
    (5 : ℕ) • Point.some 0 0 h = 0 := by
  -- `T` is not `2`-torsion, since `-T = (0, c) ≠ (0, 0)`
  have hy : (0 : 𝕜) ≠ negY (tateCurve c) 0 0 := by
    rw [tateCurve_negY_zero]
    exact fun hh => hc hh.symm
  have hxy : ¬((0 : 𝕜) = 0 ∧ (0 : 𝕜) = negY (tateCurve c) 0 0) := fun hh => hy hh.2
  -- `2T = (c, c²)`: the tangent at `(0,0)` is horizontal, and the third intersection
  -- point of `y = 0` with `E(c)` is `x = c`, `y = c²`
  have hsl1 : slope (tateCurve c) 0 0 0 0 = 0 := by
    rw [slope_of_Y_ne rfl hy]
    simp
  have hx2 : addX (tateCurve c) 0 0 (slope (tateCurve c) 0 0 0 0) = c := by
    rw [hsl1]; simp only [addX, tateCurve]; ring
  have hy2 : addY (tateCurve c) 0 0 0 (slope (tateCurve c) 0 0 0 0) = c ^ 2 := by
    rw [hsl1]
    simp only [addY, WeierstrassCurve.Affine.negY, negAddY, addX, tateCurve]
    first | refl_ring1 | ring
  have hns2 : Nonsingular (tateCurve c) c (c ^ 2) := by
    have h' := nonsingular_add h h hxy
    rwa [hx2, hy2] at h'
  have h2T : Point.some 0 0 h + Point.some 0 0 h = Point.some c (c ^ 2) hns2 := by
    rw [Point.add_some hxy, Point.some.injEq]
    exact ⟨hx2, hy2⟩
  -- `(c, c²)` is not `2`-torsion either: `-(c, c²) = (c, 0) ≠ (c, c²)`
  have hzero : negY (tateCurve c) c (c ^ 2) = 0 := by
    simp only [WeierstrassCurve.Affine.negY, tateCurve]; ring
  have hy' : c ^ 2 ≠ negY (tateCurve c) c (c ^ 2) := by
    rw [hzero]; exact pow_ne_zero 2 hc
  have hxy' : ¬(c = c ∧ c ^ 2 = negY (tateCurve c) c (c ^ 2)) := fun hh => hy' hh.2
  -- `2·(c, c²) = (0, c)`: the tangent at `(c, c²)` has slope `c`
  have hsl2 : slope (tateCurve c) c c (c ^ 2) (c ^ 2) = c := by
    rw [slope_of_Y_ne rfl hy']
    have hnum : (3 * c ^ 2 + 2 * (tateCurve c).a₂ * c + (tateCurve c).a₄
        - (tateCurve c).a₁ * c ^ 2) = c ^ 3 := by
      simp only [tateCurve]; ring
    have hden : (c ^ 2 - negY (tateCurve c) c (c ^ 2)) = c ^ 2 := by
      rw [hzero]; ring
    rw [hnum, hden, div_eq_iff (pow_ne_zero 2 hc)]
    first | refl_ring1 | ring
  have hx4 : addX (tateCurve c) c c (slope (tateCurve c) c c (c ^ 2) (c ^ 2)) = 0 := by
    rw [hsl2]; simp only [addX, tateCurve]; ring
  have hy4 : addY (tateCurve c) c c (c ^ 2) (slope (tateCurve c) c c (c ^ 2) (c ^ 2)) = c := by
    rw [hsl2]
    simp only [addY, WeierstrassCurve.Affine.negY, negAddY, addX, tateCurve]
    first | refl_ring1 | ring
  have hns4 : Nonsingular (tateCurve c) 0 c := by
    have h' := nonsingular_add hns2 hns2 hxy'
    rwa [hx4, hy4] at h'
  have h4T : Point.some c (c ^ 2) hns2 + Point.some c (c ^ 2) hns2 = Point.some 0 c hns4 := by
    rw [Point.add_some hxy', Point.some.injEq]
    exact ⟨hx4, hy4⟩
  -- `4T = (0, c) = -T`, so `5T = 4T + T = 0`
  have h5T : Point.some 0 c hns4 + Point.some 0 0 h = 0 :=
    Point.add_of_Y_eq rfl (by rw [tateCurve_negY_zero])
  have h_a : (2 : ℕ) • Point.some 0 0 h = Point.some c (c ^ 2) hns2 := by
    rw [two_nsmul]; exact h2T
  have h_b : Point.some c (c ^ 2) hns2 + Point.some c (c ^ 2) hns2 = Point.some 0 c hns4 := h4T
  have h_c : Point.some 0 c hns4 + Point.some 0 0 h = 0 := h5T
  rw [show (5 : ℕ) = 2 + 2 + 1 from rfl, add_nsmul, add_nsmul, one_nsmul, h_a, h_b, h_c]

end PointLaw

end Work.TorsorExistence.Tate

namespace Work.TorsorExistence

open WeierstrassCurve WeierstrassCurve.Affine

/-- Over every infinite field there is an elliptic curve with `j ≠ 1728` and a rational point
of exact order `5`.  (Route: the Tate normal form `E(c) : y² + (1-c)xy - cy = x³ - cx²`, whose
discriminant is `c⁵(c² - 11c - 1)` and whose point `T = (0,0)` satisfies `2T = (c, c²)`,
`4T = (0, c) = -T`, hence `5T = 0`.  The `j`-invariant of `E(c)` is `c₄³/(c⁵(c²-11c-1))` with
`c₄ = c⁴ - 12c³ + 14c² + 12c + 1`; the equation `j = 1728` is a nonzero polynomial equation of
degree `12` in `c` (the leading coefficient is `1` in every characteristic), so over an infinite
field there are only finitely many bad `c`, and a good `c` gives a curve with `j ≠ 1728`.) -/
theorem nonempty_fiveTorsionPoint {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] [Infinite 𝕜] :
    Nonempty (FiveTorsionPoint 𝕜) := by
  classical
  obtain ⟨c, hΔne, hjne⟩ := Tate.exists_tate_param (𝕜 := 𝕜)
  have hΔ : (Tate.tateCurve c).Δ ≠ 0 := by rw [Tate.tateCurve_Δ]; exact hΔne
  have hEll : (Tate.tateCurve c).IsElliptic := by
    rw [WeierstrassCurve.isElliptic_iff]
    exact isUnit_iff_ne_zero.mpr hΔ
  haveI := hEll
  have hc0 : c ≠ 0 := fun hc => hΔne (by rw [hc]; ring)
  have hns00 : Nonsingular (Tate.tateCurve c) 0 0 :=
    (equation_iff_nonsingular (W := Tate.tateCurve c)).mp (Tate.tateCurve_equation_zero c)
  let T : Point (Tate.tateCurve c) := Point.some 0 0 hns00
  have h5T : (5 : ℕ) • T = 0 := Tate.tate_five_smul c hc0 hns00
  have hPne : T ≠ 0 := Point.some_ne_zero hns00
  have hj : (Tate.tateCurve c).j ≠ 1728 := by
    intro h
    have hc4 : (Tate.tateCurve c).c₄ ^ 3 = 1728 * (Tate.tateCurve c).Δ := by
      have h2 := congrArg (fun t => (Tate.tateCurve c).Δ * t) h
      rw [WeierstrassCurve.j_eq] at h2
      rw [← mul_assoc, mul_inv_cancel₀ hΔ, one_mul,
        mul_comm ((Tate.tateCurve c).Δ) 1728] at h2
      exact h2
    rw [Tate.tateCurve_c₄, Tate.tateCurve_Δ] at hc4
    exact hjne hc4
  exact ⟨{ E := Tate.tateCurve c
           isElliptic := hEll
           j_ne := hj
           P := T
           P_ne_zero := hPne
           five_smul := h5T }⟩

end Work.TorsorExistence
