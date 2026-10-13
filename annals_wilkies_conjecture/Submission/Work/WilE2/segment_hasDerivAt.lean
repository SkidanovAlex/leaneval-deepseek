import Mathlib

namespace Work.WilE2

theorem segment_hasDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : E → E} {φ : E → ℝ → E} {δ s : ℝ} (hs : 0 ≤ s) (hsd : s < δ)
    (hφd : ∀ y : E, ∀ t ∈ Set.Ioo (-δ) δ, HasDerivAt (φ y) (v (φ y t)) t)
    (x : E) (m : ℕ) (u : ℝ) (h1 : (m : ℝ) * s ≤ u) (h2 : u ≤ (m : ℝ) * s + s) :
    HasDerivAt (fun w => φ ((fun y => φ y s)^[m] x) (w - (m : ℝ) * s))
      (v (φ ((fun y => φ y s)^[m] x) (u - (m : ℝ) * s))) u := by
  have hδ : 0 < δ := lt_of_le_of_lt hs hsd
  -- the point `u - m*s` lies in the interval `(-δ, δ)` on which `φ` solves the ODE
  have hmem : u - (m : ℝ) * s ∈ Set.Ioo (-δ) δ := by
    constructor
    · have h0 : 0 ≤ u - (m : ℝ) * s := by linarith
      linarith
    · have hle : u - (m : ℝ) * s ≤ s := by linarith
      linarith
  have hinner : HasDerivAt (fun w : ℝ => w - (m : ℝ) * s) 1 u :=
    (hasDerivAt_id u).sub_const ((m : ℝ) * s)
  have houter : HasDerivAt (φ ((fun y => φ y s)^[m] x))
      (v (φ ((fun y => φ y s)^[m] x) (u - (m : ℝ) * s))) (u - (m : ℝ) * s) :=
    hφd _ _ hmem
  have hcomp := HasDerivAt.scomp u houter hinner
  simpa only [Function.comp_def, one_smul] using hcomp

end Work.WilE2
