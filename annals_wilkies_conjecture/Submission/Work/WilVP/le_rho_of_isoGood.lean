import Mathlib
import Submission.Work.WilVP.Defs

namespace Work.WilVP

/-- A good radius is at most the iso-radius: if `r` is good at `x` (with the value `y₀`) then
`r ≤ ρ` for the GLB `ρ` of the bad radii (downward closure of `IsoGood` in the radius makes `r` a
lower bound of the bad set). -/
theorem le_rho_of_isoGood {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)} {K₀ : ℝ}
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), Fin.cons x (Fin.cons y c) ∈ Y →
      Fin.cons x (Fin.cons y' c) ∈ Y → y = y') {c : Fin k → ℝ} {x y₀ ρ r : ℝ}
    (hy : Fin.cons x (Fin.cons y₀ c) ∈ Y) (hρ : Work.WilVP.RhoVal Y K₀ c x ρ) (hr : 0 ≤ r)
    (hgood : Work.WilVP.IsoGood Y K₀ c x y₀ r) : r ≤ ρ := by
  -- `Y` is a graph, so the value `y₀'` supplied by `RhoVal` coincides with `y₀`.
  obtain ⟨y₀', hy', _hy'0, hglb⟩ := hρ
  have h_eq : y₀' = y₀ := hfun c x y₀' y₀ hy' hy
  subst h_eq
  -- `r` is a lower bound of the set of bad radii: if `s` were bad with `s < r`, then `s ≤ r`
  -- and the downward closure of `IsoGood` in the radius (`IsoGood.mono`) would make `s` good.
  refine hglb.2 ?_
  intro s hs
  by_contra hcon
  exact hs.2 (Work.WilVP.IsoGood.mono (le_of_lt (not_le.mp hcon)) hgood)

end Work.WilVP
