import Mathlib
import Submission.Work.WilVP.Defs

namespace Work.WilVP

/-- The iso-radius exists and is unique on the fibre where the value is nonzero: the set of bad
radii `{r ≥ 0 : ¬ IsoGood Y K₀ c x y₀ r}` is nonempty (it contains a radius whose ball leaves the
domain, since the domain is contained in `[-R,R]`) and bounded below by `0`, so it has a GLB
(`IsGLB`, via `Real.exists_isGLB`/`sInf`); uniqueness is `IsGLB.unique` plus the functionality of
`Y` (which makes `y₀` unique, hence the bad set independent of the choice of witness `y₀`). -/
theorem rho_exists_unique {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)} {K₀ : ℝ}
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), Fin.cons x (Fin.cons y c) ∈ Y →
      Fin.cons x (Fin.cons y' c) ∈ Y → y = y')
    {c : Fin k → ℝ} {R : ℝ} (hbdd : ∀ x y : ℝ, Fin.cons x (Fin.cons y c) ∈ Y → |x| ≤ R)
    {x y₀ : ℝ} (hx : Fin.cons x (Fin.cons y₀ c) ∈ Y) (hy₀ : y₀ ≠ 0) :
    ∃! ρ : ℝ, Work.WilVP.RhoVal Y K₀ c x ρ := by
  -- The bad-radius set of the (given) value `y₀` at `x`.
  set S : Set ℝ := {r : ℝ | 0 ≤ r ∧ ¬ IsoGood Y K₀ c x y₀ r} with hS
  -- It is nonempty: a ball around `x` that reaches outside `[-R,R]` is not good, because the
  -- fibre has no value there.
  have hne : S.Nonempty := by
    refine ⟨|(|R| + 1) - x| + 1, ?_, ?_⟩
    · positivity
    · intro hgood
      have hlt : |(|R| + 1) - x| < |(|R| + 1) - x| + 1 := lt_add_one _
      obtain ⟨y, hy, _⟩ := hgood (|R| + 1) hlt
      have hb := hbdd (|R| + 1) y hy
      have hu : |(|R| + 1)| = |R| + 1 := by rw [abs_of_nonneg (by positivity)]
      have hlt2 : R < |R| + 1 := by
        have := le_abs_self R; linarith
      rw [hu] at hb
      linarith
  -- It is bounded below by `0`, so it has a GLB `ρ`.
  have hbddbelow : BddBelow S := ⟨0, fun a ha => ha.1⟩
  obtain ⟨ρ, hρ⟩ := Real.exists_isGLB hne hbddbelow
  refine ⟨ρ, ⟨y₀, hx, hy₀, hρ⟩, ?_⟩
  -- Uniqueness: any other `ρ'` is the GLB of the bad set of its own witness value `y₀'`, which
  -- functionality forces to equal `y₀`; hence `ρ' = ρ` by uniqueness of GLBs.
  intro ρ' hρ'
  obtain ⟨y₀', hy₀'mem, hy₀'ne, hglb'⟩ := hρ'
  have hyy : y₀' = y₀ := hfun c x y₀' y₀ hy₀'mem hx
  subst hyy
  exact hglb'.unique hρ

end Work.WilVP
