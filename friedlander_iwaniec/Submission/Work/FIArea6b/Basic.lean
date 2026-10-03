import Mathlib

namespace Work.FIArea6b

open MeasureTheory Set

/-- The lattice embedding `ℤ × ℤ → ℝ × ℝ`. -/
noncomputable def phi (p : ℤ × ℤ) : ℝ × ℝ := ((p.1 : ℝ), (p.2 : ℝ))

/-- The convex hull of the image of `A` in `ℝ × ℝ`. -/
noncomputable def Kset (A : Finset (ℤ × ℤ)) : Set (ℝ × ℝ) :=
  convexHull ℝ ((A.image phi : Finset (ℝ × ℝ)) : Set (ℝ × ℝ))

/-- The set of `x`-coordinates (columns) of `A`. -/
noncomputable def cols (A : Finset (ℤ × ℤ)) : Finset ℤ := A.image (fun p => p.1)

/-- The set of `y`-coordinates of the points of `A` in column `t`. -/
noncomputable def ys (A : Finset (ℤ × ℤ)) (t : ℤ) : Finset ℤ :=
  (A.filter (fun p => p.1 = t)).image (fun p => p.2)

/-- The least `y` in column `t` (default `0`). -/
noncomputable def loOf (A : Finset (ℤ × ℤ)) (t : ℤ) : ℤ :=
  if h : (ys A t).Nonempty then (ys A t).min' h else 0

/-- The greatest `y` in column `t` (default `0`). -/
noncomputable def hiOf (A : Finset (ℤ × ℤ)) (t : ℤ) : ℤ :=
  if h : (ys A t).Nonempty then (ys A t).max' h else 0

/-- The vertical span of the points of `A` in column `t`. -/
noncomputable def spanOf (A : Finset (ℤ × ℤ)) (t : ℤ) : ℝ :=
  (hiOf A t : ℝ) - (loOf A t : ℝ)

/-- Successor of `t` in the finite set `T` of integers (`0` if there is none). -/
noncomputable def nxtOn (T : Finset ℤ) (t : ℤ) : ℤ :=
  if h : (T.filter (fun s => t < s)).Nonempty then (T.filter (fun s => t < s)).min' h else 0

/-- The trapezoidal region above column `t` and below column `t'`, spanned by the points of `A`. -/
noncomputable def trapRegion (A : Finset (ℤ × ℤ)) (t t' : ℤ) : Set (ℝ × ℝ) :=
  regionBetween
    (fun x : ℝ => (((t' : ℝ) - x) * (loOf A t : ℝ) + (x - (t : ℝ)) * (loOf A t' : ℝ))
      / ((t' : ℝ) - (t : ℝ)))
    (fun x : ℝ => (((t' : ℝ) - x) * (hiOf A t : ℝ) + (x - (t : ℝ)) * (hiOf A t' : ℝ))
      / ((t' : ℝ) - (t : ℝ)))
    (Set.Icc (t : ℝ) (t' : ℝ))

end Work.FIArea6b
