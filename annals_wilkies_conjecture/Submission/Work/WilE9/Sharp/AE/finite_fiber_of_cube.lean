/-
  WilE9 / Sharp / AE — finiteness of the fibre of a `ψV`-preimage set inside the cube.

  `Z ⊆ ℝ^{n+1}` is a set such that `graphOf f = psiV ⁻¹' Z`, i.e. the `ψ`-preimage of `Z` is
  exactly the graph of `f` (the situation of the geometric input, where `Z` is the union of the
  `ψ`-transported pieces).  `Y ⊆ Z ∩ cubeC (n+1)`.

  The point of the lemma is the fibre-finiteness proviso of `Work.WilE9G.EffStratAE`: over a base
  point `Fin.init y` strictly inside the open cube, `Y` has a *finite* fibre.  The reason is the
  one used by the lead's `Sharp/AE/PLAN.md` §5: every point of `Z` that lies in the *open* cube
  is of the form `psiV z` with `z ∈ graphOf f`, hence its last coordinate is determined by its
  first `n` coordinates; the only points of `Z ∩ cubeC (n+1)` that avoid this are those whose last
  coordinate is `±1` (the first `n` coordinates are fixed strictly inside).  So the fibre has at
  most three points, and it is finite.
-/
import Mathlib
import Submission.Work.WilE9.Sharp.Vocab
import Submission.Work.WilE9.Psi.psi_psiInv
import Submission.Work.WilE9.Psi.psiInv_psi

namespace Work.WilE9.Sharp.AE

/-- **The last coordinate of an interior point of `Z` is determined by its base.**  If
`graphOf f = psiV ⁻¹' Z` and `y' ∈ Z` lies in the open cube `(-1,1)^{n+1}`, then `y' = psiV z`
for `z = psiInvV y'`, and `z ∈ psiV ⁻¹' Z = graphOf f`, so
`y' (last) = ψ (z (last)) = ψ (f (init z)) = ψ (f (psiInvV (init y')))`. -/
theorem last_eq_of_mem_of_mem_ocube {n : ℕ} {f : (Fin n → ℝ) → ℝ} {Z : Set (Fin (n + 1) → ℝ)}
    (hZ : WilkiesDesign.graphOf f = WilkiesDesign.E.psiV ⁻¹' Z)
    {y' : Fin (n + 1) → ℝ} (hZ' : y' ∈ Z) (hoc : ∀ i, |y' i| < 1) :
    y' (Fin.last n) = WilkiesDesign.E.psi (f (Work.WilE9.Sharp.psiInvV (Fin.init y'))) := by
  -- `psiInvV` is the inverse of `psiV` on the open cube
  have hpsi : WilkiesDesign.E.psiV (Work.WilE9.Sharp.psiInvV y') = y' := by
    funext i
    exact Work.WilE9.Psi.psi_psiInv (y' i) (hoc i)
  -- hence `psiInvV y'` is a preimage of `y' ∈ Z` under `psiV`, i.e. lies in the graph
  have hmem : Work.WilE9.Sharp.psiInvV y' ∈ WilkiesDesign.graphOf f := by
    rw [hZ]
    show WilkiesDesign.E.psiV (Work.WilE9.Sharp.psiInvV y') ∈ Z
    rw [hpsi]
    exact hZ'
  have hgraph : (Work.WilE9.Sharp.psiInvV y') (Fin.last n) =
      f (Fin.init (Work.WilE9.Sharp.psiInvV y')) := by
    simpa only [WilkiesDesign.graphOf, Set.mem_ofPred_eq] using hmem
  have hinit : Fin.init (Work.WilE9.Sharp.psiInvV y') =
      Work.WilE9.Sharp.psiInvV (Fin.init y') := rfl
  rw [hinit] at hgraph
  have hlast : (Work.WilE9.Sharp.psiInvV y') (Fin.last n) =
      Work.WilE9.psiInv (y' (Fin.last n)) := rfl
  rw [hlast] at hgraph
  -- `psiInv (y' last) = f (psiInvV (init y'))`; apply `psi` and use `psi (psiInv y) = y`
  rw [← hgraph]
  exact (Work.WilE9.Psi.psi_psiInv (y' (Fin.last n)) (hoc (Fin.last n))).symm

/-- **Finiteness of the fibre of `Y ⊆ Z ∩ cubeC` over a base point of the open cube.**

Every `y' ∈ Y` with `Fin.init y' = Fin.init y` has all of its first `n` coordinates equal to
`Fin.init y`, which is strictly inside `(-1,1)^n` by `hy`; the last coordinate lies in `[-1,1]`
because `Y ⊆ cubeC`, so either it is strictly inside — and then
`last_eq_of_mem_of_mem_ocube` pins it down to the single value
`ψ (f (psiInvV (Fin.init y)))` — or it is `±1`.  Hence the fibre is contained in the three points
`Fin.snoc (Fin.init y) 1`, `Fin.snoc (Fin.init y) (-1)`, `Fin.snoc (Fin.init y) (ψ (f …))`. -/
theorem finite_fiber_of_cube {n : ℕ} {f : (Fin n → ℝ) → ℝ} {Z : Set (Fin (n + 1) → ℝ)}
    (hZ : WilkiesDesign.graphOf f = WilkiesDesign.E.psiV ⁻¹' Z)
    {Y : Set (Fin (n + 1) → ℝ)} (hYZ : Y ⊆ Z) (hYc : Y ⊆ WilkiesDesign.E.cubeC (n + 1))
    {y : Fin (n + 1) → ℝ} (hy : ∀ j : Fin n, |Fin.init y j| < 1) :
    {y' : Fin (n + 1) → ℝ | y' ∈ Y ∧ Fin.init y' = Fin.init y}.Finite := by
  set c : ℝ := WilkiesDesign.E.psi (f (Work.WilE9.Sharp.psiInvV (Fin.init y))) with hc
  -- the three candidate values of the last coordinate
  refine Set.Finite.subset
    (s := ({Fin.snoc (Fin.init y) 1, Fin.snoc (Fin.init y) (-1), Fin.snoc (Fin.init y) c} :
      Set (Fin (n + 1) → ℝ))) ?hT ?hsub
  · exact Set.Finite.insert _ (Set.Finite.insert _ (Set.finite_singleton _))
  · intro y' hy'
    rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    obtain ⟨hYy', hinit⟩ := hy'
    have hZ' : y' ∈ Z := hYZ hYy'
    have hcube : ∀ i, |y' i| ≤ 1 := hYc hYy'
    have hle : |y' (Fin.last n)| ≤ 1 := hcube (Fin.last n)
    -- the first `n` coordinates of `y'` agree with the strictly interior `Fin.init y`
    have hyinit : ∀ j : Fin n, |y' (Fin.castSucc j)| < 1 := by
      intro j
      have h : y' (Fin.castSucc j) = Fin.init y j := by rw [← hinit]; rfl
      rw [h]; exact hy j
    -- the point with a given last coordinate `s`
    have key : ∀ s : ℝ, y' (Fin.last n) = s → y' = Fin.snoc (Fin.init y) s := by
      intro s hs
      refine (Fin.snoc_init_self y').symm.trans ?_
      rw [hs, hinit]
    rcases lt_or_eq_of_le hle with hlt | heq
    · -- the last coordinate is strictly inside: all of `y'` is in the open cube
      right; right
      have hoc : ∀ i, |y' i| < 1 := by
        intro i
        refine Fin.lastCases ?_ ?_ i
        · simpa using hlt
        · intro j; exact hyinit j
      have hlastval : y' (Fin.last n) = c := by
        rw [last_eq_of_mem_of_mem_ocube hZ hZ' hoc, hc, ← hinit]
      exact key c hlastval
    · -- the last coordinate is on the boundary: `±1`
      rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp heq with h1 | h1
      · left; exact key 1 h1
      · right; left; exact key (-1) h1

end Work.WilE9.Sharp.AE
