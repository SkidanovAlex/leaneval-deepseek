import Mathlib
import Submission.Work.Normal.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Normal

/-- A nonconstant polynomial map of the plane is continuous and tends to `∞` at `∞`.

Continuity is `Polynomial.continuous`.  For the growth at infinity we use the fact
(`Polynomial.tendsto_norm_atTop`) that a polynomial of positive degree pushes the
`cobounded` filter to `atTop`, and translate the resulting filter statement into the
`ε`–`S` form used by `IsCoerciveContinuous`. -/
theorem isCoerciveContinuous_of_isPolynomialMapOfDegree {d : ℕ} {f : ℂ → ℂ} (hd : 1 ≤ d)
    (hf : IsPolynomialMapOfDegree d f) : IsCoerciveContinuous f := by
  obtain ⟨P, hPd, hPf⟩ := hf
  -- `P` has positive degree, since its natural degree is `d ≥ 1`.
  have hdeg : 0 < P.degree :=
    Polynomial.natDegree_pos_iff_degree_pos.mp (by rw [hPd]; omega)
  -- A positive-degree polynomial blows up along the `cobounded` filter.
  have htend : Filter.Tendsto (fun z : ℂ => ‖P.eval z‖)
      (Filter.comap (fun z : ℂ => ‖z‖) Filter.atTop) Filter.atTop :=
    P.tendsto_norm_atTop hdeg Filter.tendsto_comap
  have hfuneq : f = fun z => P.eval z := funext hPf
  refine ⟨?_, ?_⟩
  · rw [hfuneq]; exact P.continuous
  · intro R
    -- `{z | R ≤ ‖P.eval z‖}` is a neighbourhood of infinity; unwrap the `comap` basis.
    have h1 : {z : ℂ | R ≤ ‖P.eval z‖} ∈ Filter.comap (fun z : ℂ => ‖z‖) Filter.atTop :=
      (Filter.tendsto_atTop.mp htend) R
    obtain ⟨t, ht, htsub⟩ := Filter.mem_comap.mp h1
    obtain ⟨S, hS⟩ := Filter.mem_atTop_sets.mp ht
    exact ⟨S, fun z hz => by simpa [hPf z] using htsub (hS ‖z‖ hz)⟩

end Work.Normal
