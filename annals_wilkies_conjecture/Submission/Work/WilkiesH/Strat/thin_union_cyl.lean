import Mathlib
import Submission.Work.WilkiesH.Strat.BadCell

namespace Work.WilkiesH.Strat

/-- A set `S ⊆ ℝⁿ⁺¹` with finite vertical fibres and a set `V ⊆ ℝⁿ` with empty interior
have, together with the cylinder `cyl V` over `V`, empty interior.

Indeed if `x ∈ int (S ∪ cyl V)` then a box `B` around `x` lies in `S ∪ cyl V`. Since
`int V = ∅`, there is a base point `u ∉ V` whose coordinates are close enough to `init x`
that the whole vertical fibre `{snoc u t | |t - x (last n)| < ε}` lies in `B`. As
`u ∉ V` none of these points lies in `cyl V`, so this infinite interval is contained in
the fibre `fibre u S`, contradicting finiteness. -/
theorem thin_union_cyl {n : ℕ} {S : Set (Fin (n + 1) → ℝ)} {V : Set (Fin n → ℝ)}
    (hS : ∀ u : Fin n → ℝ, (Work.WilkiesH.Strat.fibre u S).Finite)
    (hV : interior V = ∅) :
    interior (S ∪ Work.WilkiesH.Strat.cyl V) = ∅ := by
  rw [interior_eq_empty_iff]
  intro x ε hε
  -- `init x` is not an interior point of `V`, so there is a nearby point `u ∉ V`.
  have hmem : Fin.init x ∉ interior V := by
    rw [hV]; exact Set.notMem_empty _
  obtain ⟨u, hu, huV⟩ := not_mem_interior_iff.mp hmem ε hε
  -- `u ∉ V`, so the whole vertical fibre over `u` (below the box) must lie in `S`.
  -- That fibre is an infinite interval, contradicting finiteness of `fibre u S`.
  have hInf : (Set.Ioo (x (Fin.last n) - ε) (x (Fin.last n) + ε)).Infinite :=
    Set.Ioo_infinite (by linarith)
  obtain ⟨t, htI, htF⟩ := hInf.exists_notMem_finite (hS u)
  have ht' : |t - x (Fin.last n)| < ε := by
    rw [abs_lt]
    rw [Set.mem_Ioo] at htI
    exact ⟨by linarith [htI.1], by linarith [htI.2]⟩
  refine ⟨Fin.snoc u t, fun i => ?_, ?_⟩
  · refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using ht'
    · simpa using hu j
  · rintro (hyS | hyV)
    · exact htF hyS
    · exact huV (by simpa using (mem_cyl.mp hyV))

end Work.WilkiesH.Strat
