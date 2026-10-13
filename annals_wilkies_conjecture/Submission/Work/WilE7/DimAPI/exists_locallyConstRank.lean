import Mathlib

/-!
# Local constancy of the rank of the derivative of a map analytic at a point

`Work.WilE7.DimAPI.exists_locallyConstRank`: for a map `g : (Fin K → ℝ) → (Fin P → ℝ)` which
is analytic at the origin and any neighbourhood `V` of `0`, there is a point `x ∈ V` at which
the numerical function `y ↦ finrank ℝ (fderiv ℝ g y).range` is eventually constant, with value
`M ≤ P`.

The argument is the standard one for lower semicontinuous, integer valued functions that take
their maximum on a neighbourhood:

* `fderiv ℝ g` is analytic at `0` (`AnalyticAt.fderiv`), so the set `A` of points at which
  `fderiv ℝ g` is analytic — and hence continuous — is an open neighbourhood of `0`
  (`isOpen_analyticAt`);
* for every `y`, `finrank ℝ (fderiv ℝ g y).range ≤ P`, since the range is a subspace of
  `Fin P → ℝ` (`Submodule.finrank_le`, `Module.finrank_fin_fun`);
* `M` is the maximum of the rank function on a small ball `B ⊆ V` around `0` (it exists by
  `Nat.findGreatest`, since the rank function is bounded by `P` and `B` is nonempty), and it is
  attained at some `x ∈ B`;
* `{z | M ≤ finrank ℝ z.range}` is open in the space of continuous linear maps
  (`isOpen_setOfPred_nat_le_rank`, the lower semicontinuity of the rank), so continuity of
  `fderiv ℝ g` at `x` makes `{y | M ≤ finrank ℝ (fderiv ℝ g y).range}` a neighbourhood of `x`;
  since the rank is at most `M` on `B`, the two give that the rank is exactly `M` on the
  neighbourhood `B ∩ {y | M ≤ finrank ℝ (fderiv ℝ g y).range}` of `x`.
-/

namespace Work.WilE7.DimAPI

/-- **Lower semicontinuity of the rank.** The continuous linear maps
`(Fin K → ℝ) →L[ℝ] (Fin P → ℝ)` whose range has dimension at least `M` form an open set. -/
theorem isOpen_le_finrank_range {K P : ℕ} (M : ℕ) :
    IsOpen {z : (Fin K → ℝ) →L[ℝ] (Fin P → ℝ) | M ≤ Module.finrank ℝ z.range} := by
  -- `isOpen_setOfPred_nat_le_rank` is the corresponding statement for the cardinal-valued
  -- `LinearMap.rank`; `LinearMap.rank f = Module.rank ℝ f.range` is the definition, and the
  -- cardinal `Module.rank ℝ S` is the same as the natural number `Module.finrank ℝ S`.
  have h := isOpen_setOfPred_nat_le_rank (𝕜 := ℝ) (E := Fin K → ℝ) (F := Fin P → ℝ) M
  convert h using 1
  ext z
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, LinearMap.rank, ← Module.finrank_eq_rank]
  exact (Nat.cast_le (α := Cardinal)).symm

theorem exists_locallyConstRank {K P : ℕ} (g : (Fin K → ℝ) → (Fin P → ℝ))
    (hg : AnalyticAt ℝ g 0) (V : Set (Fin K → ℝ)) (hV : V ∈ nhds (0 : Fin K → ℝ)) :
    ∃ x ∈ V, ∃ M : ℕ, M ≤ P ∧
      ∀ᶠ y in nhds x, Module.finrank ℝ (fderiv ℝ g y).range = M := by
  classical
  -- A ball around `0` contained in `V`.
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.mp hV
  -- The set on which `fderiv ℝ g` is analytic (hence continuous): open, and a neighbourhood of
  -- `0` because the derivative of an analytic map is analytic.
  set A : Set (Fin K → ℝ) := {y | AnalyticAt ℝ (fderiv ℝ g) y} with hAdef
  have hAopen : IsOpen A := isOpen_analyticAt ℝ (fderiv ℝ g)
  have hA0 : (0 : Fin K → ℝ) ∈ A := hg.fderiv
  -- The working neighbourhood `B = A ∩ ball 0 ε` of `0`, contained in `V`.
  set B : Set (Fin K → ℝ) := A ∩ Metric.ball (0 : Fin K → ℝ) ε with hBdef
  have hB0 : (0 : Fin K → ℝ) ∈ B := ⟨hA0, by rw [Metric.mem_ball, dist_self]; exact hε⟩
  have hBopen : IsOpen B := hAopen.inter Metric.isOpen_ball
  have hBsubV : B ⊆ V := fun _ hy => hεV hy.2
  -- The rank is bounded by `P`, the dimension of the target.
  have hrank_le : ∀ y : Fin K → ℝ, Module.finrank ℝ (fderiv ℝ g y).range ≤ P := by
    intro y
    have h := Submodule.finrank_le (s := (fderiv ℝ g y).range)
    rwa [Module.finrank_fin_fun] at h
  -- `M` is the maximum of the rank function on `B`; it is attained at some `x ∈ B`.
  set M : ℕ :=
    Nat.findGreatest (fun r => ∃ y ∈ B, r ≤ Module.finrank ℝ (fderiv ℝ g y).range) P with hMdef
  have hMprop : ∃ y ∈ B, M ≤ Module.finrank ℝ (fderiv ℝ g y).range := by
    rw [hMdef]
    exact Nat.findGreatest_spec (P := fun r => ∃ y ∈ B, r ≤ Module.finrank ℝ (fderiv ℝ g y).range)
      (m := 0) (Nat.zero_le P) ⟨0, hB0, Nat.zero_le _⟩
  obtain ⟨x, hxB, hxrank⟩ := hMprop
  have hMle : M ≤ P := by rw [hMdef]; exact Nat.findGreatest_le P
  have hmax : ∀ y ∈ B, Module.finrank ℝ (fderiv ℝ g y).range ≤ M := by
    intro y hy
    rw [hMdef]
    exact Nat.le_findGreatest (hrank_le y) ⟨y, hy, le_rfl⟩
  -- The rank is at least `M` on a neighbourhood of `x`, by continuity and openness.
  have hcontx : ContinuousAt (fderiv ℝ g) x := hxB.1.continuousAt
  have h1 : {y : Fin K → ℝ | M ≤ Module.finrank ℝ (fderiv ℝ g y).range} ∈ nhds x :=
    hcontx.preimage_mem_nhds ((isOpen_le_finrank_range M).mem_nhds hxrank)
  have h2 : ∀ᶠ y in nhds x, y ∈ B := hBopen.mem_nhds hxB
  refine ⟨x, hBsubV hxB, M, hMle, ?_⟩
  filter_upwards [h1, h2] with y hy hyB
  exact le_antisymm (hmax y hyB) hy

end Work.WilE7.DimAPI
