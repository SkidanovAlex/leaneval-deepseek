import Mathlib
import Submission.Work.Smooth.SphereJordan.argChangeLift

/-!
# The index (winding number) of a continuous closed plane curve

This file develops the elementary degree theory of continuous closed curves in `ℂ`, the ingredient
which the topological form of the Jordan separation theorem (for curves that are merely
continuous, as opposed to `C¹` and immersed) needs, and which the sibling chapter
`Submission.Work.Smooth.JordanSeparation` provides only in the smooth case.

For a continuous closed path `c : [0,1] → ℂ` avoiding `0`, the **index** `loopIndex c` is the net
number of times `c` winds around the origin; it is characterised by

`Λ 1 - Λ 0 = (loopIndex c : ℂ) * (2 * π * I)`

for every continuous lift `Λ` of `c` through the exponential map (the existence of such a lift and
the independence of `Λ 1 - Λ 0` of the choice of `Λ` is `argChangeLift`), and this unique
characterisation is the lemma `loopIndex_spec`.

The main results are

* `loopIndex_spec` — the defining property of the index;
* `loopIndex_eq_zero_of_lift` — a closed path whose lift is closed has index `0`;
* `loopIndex_eq_zero_of_slitPlane` — a closed path avoiding the slit `ℂ \ (-∞,0]` has index `0`
  (its lift is the continuous logarithm, which returns to its starting value);
* `loopIndex_congr` — pointwise equal closed paths have equal index;
* `loopIndex_mul` — additivity: `loopIndex (u * v) = loopIndex u + loopIndex v`.

The geometric consequences (independence of the base point along a segment avoiding the curve, and
the vanishing at infinity) are in `planeIndexGeom.lean`.
-/

noncomputable section

open Set
open Classical

namespace Work.Smooth.SphereJordan

/-- The complex number `2 * π * I` is nonzero. -/
theorem two_pi_I_ne_zero : (2 * ↑Real.pi * Complex.I : ℂ) ≠ 0 :=
  mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    Complex.I_ne_zero

/-- **Existence and uniqueness of the index of a nowhere vanishing closed path.**  There is an
integer `k` such that *every* continuous lift `Λ` of `c` through `exp` satisfies
`Λ 1 - Λ 0 = k * (2 * π * I)`. -/
theorem exists_index_int (c : C(unitInterval, ℂ)) (hc : ∀ t, c t ≠ 0) (hloop : c 0 = c 1) :
    ∃ k : ℤ, ∀ Λ : C(unitInterval, ℂ), (∀ t, Complex.exp (Λ t) = c t) →
      Λ 1 - Λ 0 = (k : ℂ) * (2 * ↑Real.pi * Complex.I) := by
  obtain ⟨Λ₀, hΛ₀, -, huniq⟩ := argChangeLift c hc
  have hexp : Complex.exp (Λ₀ 1 - Λ₀ 0) = 1 := by
    rw [Complex.exp_sub, hΛ₀ 1, hΛ₀ 0, hloop, div_self (hc 1)]
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp hexp
  exact ⟨k, fun Λ hΛ => by rw [huniq Λ hΛ, hk]⟩

/-- **The index (winding number) of a continuous closed path.**  For a path avoiding `0` this is
the net number of times it winds around the origin (see `loopIndex_spec`); for a path meeting `0`
the value is irrelevant and set to `0`. -/
noncomputable def loopIndex (c : C(unitInterval, ℂ)) : ℤ :=
  if h : (∀ t, c t ≠ 0) ∧ c 0 = c 1 then (exists_index_int c h.1 h.2).choose else 0

/-- **The defining property of the index**: for every continuous lift `Λ` of a nowhere vanishing
closed path `c`, the increment `Λ 1 - Λ 0` is `(loopIndex c) * (2 * π * I)`. -/
theorem loopIndex_spec (c : C(unitInterval, ℂ)) (hc : ∀ t, c t ≠ 0) (hloop : c 0 = c 1)
    (Λ : C(unitInterval, ℂ)) (hΛ : ∀ t, Complex.exp (Λ t) = c t) :
    Λ 1 - Λ 0 = (loopIndex c : ℂ) * (2 * ↑Real.pi * Complex.I) := by
  rw [loopIndex, dif_pos ⟨hc, hloop⟩]
  exact (exists_index_int c hc hloop).choose_spec Λ hΛ

/-- A closed path whose lift is closed has index `0`. -/
theorem loopIndex_eq_zero_of_lift (c : C(unitInterval, ℂ)) (hc : ∀ t, c t ≠ 0)
    (hloop : c 0 = c 1) (Λ : C(unitInterval, ℂ)) (hΛ : ∀ t, Complex.exp (Λ t) = c t)
    (hfix : Λ 1 = Λ 0) : loopIndex c = 0 := by
  have h := loopIndex_spec c hc hloop Λ hΛ
  rw [hfix, sub_self] at h
  have h2 : (loopIndex c : ℂ) = 0 := by
    rcases (mul_eq_zero.mp h.symm) with h3 | h3
    · exact h3
    · exact absurd h3 two_pi_I_ne_zero
  exact Int.cast_eq_zero.mp h2

/-- **A closed path avoiding the slit `ℂ \ (-∞,0]` has index `0`.**

Indeed `Complex.log` is continuous on the slit plane (`Complex.continuousAt_clog`), so
`t ↦ Complex.log (c t)` is a lift of `c`; being a function of the point it returns to its starting
value at the end of the loop. -/
theorem loopIndex_eq_zero_of_slitPlane (c : C(unitInterval, ℂ)) (hc : ∀ t, c t ≠ 0)
    (hloop : c 0 = c 1) (hslit : ∀ t, c t ∈ Complex.slitPlane) : loopIndex c = 0 := by
  refine loopIndex_eq_zero_of_lift c hc hloop
    ⟨fun t => Complex.log (c t), c.continuous.clog hslit⟩ (fun t => Complex.exp_log (hc t)) ?_
  show Complex.log (c (1 : unitInterval)) = Complex.log (c (0 : unitInterval))
  rw [hloop]

/-- Pointwise equal closed paths have the same index. -/
theorem loopIndex_congr {c d : C(unitInterval, ℂ)} (hcd : ∀ t, c t = d t)
    (hc : ∀ t, c t ≠ 0) (hd : ∀ t, d t ≠ 0) (hlc : c 0 = c 1) (hld : d 0 = d 1) :
    loopIndex c = loopIndex d := by
  obtain ⟨Λ, hΛ, -, -⟩ := argChangeLift c hc
  have hΛ' : ∀ t, Complex.exp (Λ t) = d t := fun t => by rw [hΛ t, hcd t]
  have h1 := loopIndex_spec c hc hlc Λ hΛ
  have h2 := loopIndex_spec d hd hld Λ hΛ'
  have h3 : (loopIndex c : ℂ) * (2 * ↑Real.pi * Complex.I) =
      (loopIndex d : ℂ) * (2 * ↑Real.pi * Complex.I) := by rw [← h1, h2]
  have h4 : (loopIndex c : ℂ) = (loopIndex d : ℂ) :=
    mul_right_cancel₀ two_pi_I_ne_zero h3
  exact Int.cast_inj.mp h4

/-- **Additivity of the index**: the index of a pointwise product of closed paths is the sum of
the indices. -/
theorem loopIndex_mul (u v : C(unitInterval, ℂ)) (hu : ∀ t, u t ≠ 0) (hv : ∀ t, v t ≠ 0)
    (hlu : u 0 = u 1) (hlv : v 0 = v 1) :
    loopIndex (u * v) = loopIndex u + loopIndex v := by
  have huv : ∀ t, (u * v) t ≠ 0 := fun t => mul_ne_zero (hu t) (hv t)
  have hluv : (u * v) 0 = (u * v) 1 := by simp only [ContinuousMap.mul_apply]; rw [hlu, hlv]
  obtain ⟨Λu, hΛu, -, -⟩ := argChangeLift u hu
  obtain ⟨Λv, hΛv, -, -⟩ := argChangeLift v hv
  have hsum : ∀ t, Complex.exp ((Λu + Λv) t) = (u * v) t := by
    intro t
    rw [ContinuousMap.add_apply, Complex.exp_add, hΛu t, hΛv t]
    rfl
  have h1 := loopIndex_spec (u * v) huv hluv (Λu + Λv) hsum
  have h2 := loopIndex_spec u hu hlu Λu hΛu
  have h3 := loopIndex_spec v hv hlv Λv hΛv
  have h4 : (Λu + Λv : C(unitInterval, ℂ)) 1 - (Λu + Λv) 0 =
      (Λu 1 - Λu 0) + (Λv 1 - Λv 0) := by
    simp only [ContinuousMap.add_apply]; ring
  rw [h4, h2, h3] at h1
  have h5 : ((loopIndex (u * v) : ℤ) : ℂ) * (2 * ↑Real.pi * Complex.I) =
      (((loopIndex u + loopIndex v : ℤ)) : ℂ) * (2 * ↑Real.pi * Complex.I) := by
    rw [← h1]
    push_cast
    ring
  exact Int.cast_inj.mp (mul_right_cancel₀ two_pi_I_ne_zero h5)

end Work.Smooth.SphereJordan
