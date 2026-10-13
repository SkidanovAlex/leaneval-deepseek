import Mathlib
import Submission.Work.WilVP.Defs

namespace Work.WilVP

/-- Every radius strictly below the iso-radius is good: if `ρ` is the GLB of the bad radii of the
fibre (and the fibre is a graph, so the value is `y₀`), then `0 ≤ r < ρ` forces
`IsoGood Y K₀ c x y₀ r`. -/
theorem isoGood_of_lt_rho {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)} {K₀ : ℝ}
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), Fin.cons x (Fin.cons y c) ∈ Y →
      Fin.cons x (Fin.cons y' c) ∈ Y → y = y') {c : Fin k → ℝ} {x y₀ ρ r : ℝ}
    (hy : Fin.cons x (Fin.cons y₀ c) ∈ Y) (hρ : Work.WilVP.RhoVal Y K₀ c x ρ) (hr : 0 ≤ r)
    (hlt : r < ρ) : Work.WilVP.IsoGood Y K₀ c x y₀ r := by
  -- `hρ` gives a witness value `y₁` at `x`; functionality forces `y₁ = y₀`.
  obtain ⟨y₁, hy₁, _hy₁ne, hglb⟩ := hρ
  have hyy : y₁ = y₀ := hfun c x y₁ y₀ hy₁ hy
  rw [← hyy]
  -- `ρ` is a lower bound of the bad radii, so `r` cannot be bad.
  by_contra hbad
  have hmem : r ∈ {s : ℝ | 0 ≤ s ∧ ¬ IsoGood Y K₀ c x y₁ s} := ⟨hr, hbad⟩
  have := hglb.1 hmem
  linarith

end Work.WilVP
