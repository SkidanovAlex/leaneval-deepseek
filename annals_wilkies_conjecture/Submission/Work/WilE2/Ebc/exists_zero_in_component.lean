import Mathlib

namespace Work.WilE2.Ebc

open Set Metric Filter

open scoped Topology

/-- A connected component of a **closed** set is closed in the ambient space.

`connectedComponentIn F x` is, by definition, the image of the connected component of `x` in the
subtype `F` under the inclusion `Subtype.val`.  When `F` is closed the inclusion is a closed map,
so the image of the closed set `connectedComponent …` is closed. -/
private theorem isClosed_connectedComponentIn_of_isClosed {α : Type*} [TopologicalSpace α]
    {F : Set α} (hF : IsClosed F) (x : α) :
    IsClosed (connectedComponentIn F x) := by
  rcases em (x ∈ F) with hx | hx
  · rw [connectedComponentIn_eq_image hx]
    exact hF.isClosedMap_subtype_val _ isClosed_connectedComponent
  · rw [connectedComponentIn_eq_empty hx]
    exact isClosed_empty

/-- **Every bounded connected component of a sublevel set of a continuous function meets the zero
level set.**

Let `F : ℝ^k → ℝ` be continuous and suppose the set `S = {x | F x ≤ 0}` is bounded (in the squared
`ℓ²`-norm).  Then any connected component `C` of `S` that contains a point `y` with `F y ≤ 0` also
contains a point `z` with `F z = 0`.

The proof is the classical "a bounded component must touch the boundary" argument.  `S` is closed
and bounded hence compact, so `C` is compact and thus a *proper* closed subset of `ℝ^k` (here the
hypothesis `0 < k` is used: `ℝ^k` is unbounded and nonempty).  Since `ℝ^k` is connected, `C` has a
nonempty frontier.  Take `w ∈ ∂C`; as `C` is closed, `w ∈ C`, so `F w ≤ 0`.  If `F w < 0`
then, by continuity, a whole ball `B` around `w` lies in `S`; the ball meets `C` (as `w ∈ closure C`),
so `C ∪ B` is a connected subset of `S` containing `y`, whence `B ⊆ C` by maximality of the
component, making `w` an interior point of `C` — contradicting `w ∈ ∂C`. -/
theorem exists_zero_in_component {k : ℕ} (hk : 0 < k) {F : (Fin k → ℝ) → ℝ}
    (hF : Continuous F) {y : Fin k → ℝ} (hy : F y ≤ 0)
    (hbdd : ∃ R : ℝ, ∀ x : Fin k → ℝ, F x ≤ 0 → ∑ i, (x i) ^ 2 ≤ R) :
    ∃ z ∈ connectedComponentIn {x : Fin k → ℝ | F x ≤ 0} y, F z = 0 := by
  classical
  set S : Set (Fin k → ℝ) := {x | F x ≤ 0} with hS
  have hSclosed : IsClosed S := isClosed_le hF continuous_const
  obtain ⟨R, hR⟩ := hbdd
  -- `R` bounds the square of every coordinate of every point of `S`
  have hcoord : ∀ x ∈ S, ∀ i, (x i) ^ 2 ≤ R := by
    intro x hx i
    have hs : (x i) ^ 2 ≤ ∑ j, (x j) ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    exact le_trans hs (hR x (show F x ≤ 0 from hx))
  -- the product of closed intervals containing `S`
  set P : Set (Fin k → ℝ) :=
    Set.univ.pi (fun _ : Fin k => Set.Icc (-(Real.sqrt R)) (Real.sqrt R)) with hP
  have hSP : S ⊆ P := by
    intro x hx
    rw [hP, Set.mem_univ_pi]
    intro i
    exact abs_le.mp (Real.abs_le_sqrt (hcoord x hx i))
  set C : Set (Fin k → ℝ) := connectedComponentIn S y with hC
  have hyC : y ∈ C := mem_connectedComponentIn hy
  have hCcl : IsClosed C := isClosed_connectedComponentIn_of_isClosed hSclosed y
  have hCpc : IsPreconnected C := isPreconnected_connectedComponentIn
  have hCsub : C ⊆ S := connectedComponentIn_subset S y
  -- `C` is a proper subset of `ℝ^k`
  have hCneuniv : C ≠ Set.univ := by
    intro hCe
    have i0 : Fin k := ⟨0, hk⟩
    have hmem : (fun _ : Fin k => Real.sqrt R + 1) ∈ P := by
      have : (fun _ : Fin k => Real.sqrt R + 1) ∈ C := by
        rw [hCe]; exact Set.mem_univ _
      exact hSP (hCsub this)
    rw [hP, Set.mem_univ_pi] at hmem
    have h2 := hmem i0
    rw [Set.mem_Icc] at h2
    linarith [h2.2]
  have hCne : C.Nonempty := ⟨y, hyC⟩
  obtain ⟨w, hw⟩ :=
    nonempty_frontier_iff.mpr (show C.Nonempty ∧ C ≠ Set.univ from ⟨hCne, hCneuniv⟩)
  rw [frontier, Set.mem_sdiff] at hw
  obtain ⟨hwcl, hwnint⟩ := hw
  -- `C` is closed, so a point of its closure lies in it
  have hwC : w ∈ C := hCcl.closure_eq ▸ hwcl
  have hwS : w ∈ S := hCsub hwC
  -- the decisive claim
  have hFw0 : F w = 0 := by
    rcases lt_trichotomy (F w) 0 with hlt | heq | hgt
    · exfalso
      have hev : ∀ᶠ x in 𝓝 w, F x < 0 := (isOpen_lt hF continuous_const).mem_nhds hlt
      rw [Metric.eventually_nhds_iff] at hev
      obtain ⟨ε, hεpos, hε⟩ := hev
      have hBsub : Metric.ball w ε ⊆ S := by
        intro x hx
        exact le_of_lt (hε (Metric.mem_ball.mp hx))
      have hBpc : IsPreconnected (Metric.ball w ε) := Metric.isPreconnected_ball
      have hinter : (Metric.ball w ε ∩ C).Nonempty := by
        obtain ⟨b, hbC, hbd⟩ := Metric.mem_closure_iff.mp hwcl ε hεpos
        exact ⟨b, Metric.mem_ball.mpr (dist_comm w b ▸ hbd), hbC⟩
      obtain ⟨b, hbB, hbC⟩ := hinter
      have hunion_pc : IsPreconnected (C ∪ Metric.ball w ε) :=
        IsPreconnected.union b hbC hbB hCpc hBpc
      have hunion_sub : C ∪ Metric.ball w ε ⊆ S := union_subset hCsub hBsub
      have hsubC : C ∪ Metric.ball w ε ⊆ C :=
        IsPreconnected.subset_connectedComponentIn hunion_pc (Or.inl hyC) hunion_sub
      have hBsubC : Metric.ball w ε ⊆ C := Set.subset_union_right.trans hsubC
      have hwint : w ∈ interior C := by
        rw [mem_interior_iff_mem_nhds]
        exact Filter.mem_of_superset (Metric.ball_mem_nhds w hεpos) hBsubC
      exact hwnint hwint
    · exact heq
    · exact absurd (show F w ≤ 0 from hwS) (not_le.mpr hgt)
  exact ⟨w, hwC, hFw0⟩

end Work.WilE2.Ebc
