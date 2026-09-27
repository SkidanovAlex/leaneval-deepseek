import Mathlib
import Submission.Work.Noncompact.CompressionTube.Notation

/-!
# The regions of the canal construction

For the canal data of `Work.Noncompact.Routing.twoRays_of_canal` (an open preconnected `W`,
a compact exhaustion `K` through the interiors, a decreasing family `D` of open preconnected
`K`-avoiding sets, a base point `b ∈ D N` and junctions `z i ∈ D (N+i) ∖ D (N+i+1)`),
we collect the elementary properties of the regions

  `R j := connectedComponentIn (D N \ K (N + j)) (z j)`.

They are open, preconnected, contained in `D N ⊓ (K (N+j))ᶜ`, nested, contain every `z i` with
`i ≥ j`, and their closures are non-compact; this is the cofinality used at every stage of the
two-ray construction.
-/

namespace Work.Noncompact.Routing

open Set Topology

/-- The region of the canal construction at level `j`. -/
def canalRegion (n : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (K : ℕ → Set M) (D : ℕ → Set M) (N : ℕ) (z : ℕ → M) (j : ℕ) : Set M :=
  connectedComponentIn (D N \ K (N + j)) (z j)

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [T2Space M]

/-- A monotone sequence of sets from a chain through the interiors. -/
theorem monotone_of_subset_interior {K : ℕ → Set M} (hK : ∀ i, K i ⊆ interior (K (i + 1))) :
    Monotone K :=
  monotone_nat_of_le_succ fun i => (hK i).trans interior_subset

/-- An `Antitone` sequence of sets. -/
theorem antitone_of_succ_subset {D : ℕ → Set M} (hD : ∀ i, D (i + 1) ⊆ D i) : Antitone D :=
  fun _ _ hab => by
    induction hab with
    | refl => exact subset_rfl
    | step _ ih => exact (hD _).trans ih

section

variable {K : ℕ → Set M} {D : ℕ → Set M} {N : ℕ} {z : ℕ → M}

/-- `z j` lies in the region at level `j`. -/
theorem mem_canalRegion (hDK : ∀ i, D i ⊆ (K i)ᶜ) (hDmono : ∀ i, D (i + 1) ⊆ D i)
    (hzD : ∀ i, z i ∈ D (N + i)) (j : ℕ) :
    z j ∈ canalRegion n K D N z j :=
  mem_connectedComponentIn
    (show z j ∈ D N \ K (N + j) from
      ⟨antitone_of_succ_subset hDmono (Nat.le_add_right N j) (hzD j),
        hDK (N + j) (hzD j)⟩)

/-- Every later junction lies in the region at level `j`. -/
theorem mem_canalRegion_of_le (hDK : ∀ i, D i ⊆ (K i)ᶜ) (hDpc : ∀ i, IsPreconnected (D i))
    (hDmono : ∀ i, D (i + 1) ⊆ D i) (hzD : ∀ i, z i ∈ D (N + i)) {i j : ℕ} (hij : j ≤ i) :
    z i ∈ canalRegion n K D N z j := by
  have hsub : D (N + j) ⊆ D N \ K (N + j) :=
    fun x hx => ⟨antitone_of_succ_subset hDmono (Nat.le_add_right N j) hx, hDK (N + j) hx⟩
  have hmem : z i ∈ D (N + j) := antitone_of_succ_subset hDmono (by omega) (hzD i)
  exact IsPreconnected.subset_connectedComponentIn (hDpc (N + j)) (hzD j) hsub hmem

/-- The region at level `j` is contained in `D N \ K (N+j)`. -/
theorem canalRegion_subset (j : ℕ) :
    canalRegion n K D N z j ⊆ D N \ K (N + j) :=
  connectedComponentIn_subset _ _

theorem canalRegion_subset_D (j : ℕ) : canalRegion n K D N z j ⊆ D N :=
  fun x hx => ((canalRegion_subset (n := n) (K := K) (D := D) (N := N) (z := z) j) hx).1

theorem canalRegion_subset_compl_K (j : ℕ) : canalRegion n K D N z j ⊆ (K (N + j))ᶜ :=
  fun x hx => ((canalRegion_subset (n := n) (K := K) (D := D) (N := N) (z := z) j) hx).2

theorem canalRegion_subset_W {W : Set M} (hDW : ∀ i, D i ⊆ W) (j : ℕ) :
    canalRegion n K D N z j ⊆ W :=
  (canalRegion_subset_D (n := n) (K := K) (D := D) (N := N) (z := z) j).trans (hDW N)

theorem isPreconnected_canalRegion (j : ℕ) : IsPreconnected (canalRegion n K D N z j) :=
  isPreconnected_connectedComponentIn

theorem isOpen_canalRegion (hDo : ∀ i, IsOpen (D i)) (hKc : ∀ i, IsCompact (K i)) (j : ℕ) :
    IsOpen (canalRegion n K D N z j) := by
  haveI : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin n)) M
  exact (hDo N |>.sdiff (hKc (N + j)).isClosed).connectedComponentIn

/-- **A preconnected set inside `D N \ K (N+j)` containing `z j` lies in the region.** -/
theorem subset_canalRegion {C : Set M} (j : ℕ) (hC : IsPreconnected C)
    (hsub : C ⊆ D N \ K (N + j)) (hz : z j ∈ C) : C ⊆ canalRegion n K D N z j :=
  IsPreconnected.subset_connectedComponentIn hC hz hsub

/-- The regions are nested. -/
theorem canalRegion_antitone (hKsub : ∀ i, K i ⊆ interior (K (i + 1))) (hDK : ∀ i, D i ⊆ (K i)ᶜ)
    (hDpc : ∀ i, IsPreconnected (D i)) (hDmono : ∀ i, D (i + 1) ⊆ D i)
    (hzD : ∀ i, z i ∈ D (N + i)) (j : ℕ) :
    canalRegion n K D N z (j + 1) ⊆ canalRegion n K D N z j := by
  have hKmono : Monotone K := monotone_of_subset_interior hKsub
  have hmem : z (j + 1) ∈ canalRegion n K D N z j :=
    mem_canalRegion_of_le (i := j + 1) (j := j) hDK hDpc hDmono hzD (Nat.le_succ j)
  have hmono : (D N \ K (N + (j + 1))) ⊆ (D N \ K (N + j)) := fun x hx =>
    ⟨hx.1, fun hc => hx.2 (hKmono (Nat.le_succ (N + j)) hc)⟩
  calc canalRegion n K D N z (j + 1)
      ⊆ connectedComponentIn (D N \ K (N + j)) (z (j + 1)) :=
        connectedComponentIn_mono _ hmono
    _ = connectedComponentIn (D N \ K (N + j)) (z j) := (connectedComponentIn_eq hmem).symm
    _ = canalRegion n K D N z j := rfl

/-- **Cofinality: the closures of the regions are non-compact.** -/
theorem not_isCompact_closure_canalRegion (hKc : ∀ i, IsCompact (K i))
    (hKsub : ∀ i, K i ⊆ interior (K (i + 1))) (hKuniv : (⋃ i, K i) = (Set.univ : Set M))
    (hDK : ∀ i, D i ⊆ (K i)ᶜ) (hDpc : ∀ i, IsPreconnected (D i)) (hDmono : ∀ i, D (i + 1) ⊆ D i)
    (hzD : ∀ i, z i ∈ D (N + i)) (hzK : ∀ i, z i ∉ K (N + i)) (j : ℕ) :
    ¬ IsCompact (closure (canalRegion n K D N z j)) := by
  have hKmono : Monotone K := monotone_of_subset_interior hKsub
  intro hc
  have hcover : (closure (canalRegion n K D N z j)) ⊆ ⋃ i, interior (K (i + 1)) := by
    intro x hx
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp (show x ∈ ⋃ i, K i by rw [hKuniv]; trivial)
    exact Set.mem_iUnion.mpr ⟨m, hKsub m hm⟩
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover (fun i : ℕ => interior (K (i + 1)))
    (fun i => isOpen_interior) hcover
  obtain ⟨i, hi⟩ : ∃ i : ℕ, j ≤ i ∧ t.sup (fun i => i + 1) ≤ N + i :=
    ⟨j + t.sup (fun i => i + 1), Nat.le_add_right _ _, by omega⟩
  have hzi : z i ∈ closure (canalRegion n K D N z j) :=
    subset_closure (mem_canalRegion_of_le (i := i) (j := j) hDK hDpc hDmono hzD hi.1)
  obtain ⟨m, hmt, hmem⟩ := Set.mem_iUnion₂.mp (ht hzi)
  have hle : m + 1 ≤ N + i := le_trans (Finset.le_sup (f := fun i => i + 1) hmt) hi.2
  have : z i ∈ K (N + i) := hKmono hle (interior_subset hmem)
  exact hzK i this

end


/-- **Base germ data.**  From `b ∈ D N` with `D N` open one gets a chart `c` in the maximal
atlas, a non-zero vector `w` and `e > 0` such that both straight germs
`c.symm (c b + t • w)` and `c.symm (c b + t • (-w))` lie in `D N` for `0 ≤ t ≤ e`.  These are the
two opposite germs of a pair of rays based at `b`. -/
theorem exists_base_germ {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder M]
    [T2Space M] {D : ℕ → Set M} {N : ℕ} (hDo : IsOpen (D N)) {b : M} (hb : b ∈ D N) :
    ∃ (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (w : EuclideanSpace ℝ (Fin n)) (e : ℝ), 0 < e ∧ w ≠ 0 ∧
      c ∈ IsManifold.maximalAtlas (Work.Noncompact.CompressionTube.MC n)
        Work.Noncompact.CompressionTube.smoothOrder M ∧ b ∈ c.source ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ e → c.symm (c b + t • w) ∈ D N) ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ e → c.symm (c b + t • (-w)) ∈ D N) := by
  classical
  have hn0 : 0 < n := by omega
  set c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
    chartAt (EuclideanSpace ℝ (Fin n)) b with hcdef
  set w : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single ⟨0, hn0⟩ 1 with hwdef
  have hwnorm : ‖w‖ = 1 := by
    rw [hwdef, PiLp.norm_single]; norm_num
  have hw : w ≠ 0 := by
    intro h; rw [h, norm_zero] at hwnorm; norm_num at hwnorm
  have hmem : c b ∈ c.target := c.map_source (mem_chart_source _ b)
  have hcont1 : ContinuousAt (fun t : ℝ => c.symm (c b + t • w)) 0 :=
    ContinuousAt.comp (g := ⇑c.symm) (f := fun t : ℝ => c b + t • w)
      (c.continuousOn_symm.continuousAt (c.open_target.mem_nhds (by simpa using hmem)))
      (by fun_prop)
  have hcont2 : ContinuousAt (fun t : ℝ => c.symm (c b + t • (-w))) 0 :=
    ContinuousAt.comp (g := ⇑c.symm) (f := fun t : ℝ => c b + t • (-w))
      (c.continuousOn_symm.continuousAt (c.open_target.mem_nhds (by simpa using hmem)))
      (by fun_prop)
  have hv1 : c.symm (c b + (0:ℝ) • w) = b := by
    rw [zero_smul, add_zero]; exact c.left_inv (mem_chart_source _ b)
  have hv2 : c.symm (c b + (0:ℝ) • (-w)) = b := by
    rw [zero_smul, add_zero]; exact c.left_inv (mem_chart_source _ b)
  obtain ⟨δ₁, hδ₁, h₁⟩ := Metric.mem_nhds_iff.mp
    (hcont1.preimage_mem_nhds (by rw [hv1]; exact hDo.mem_nhds hb))
  obtain ⟨δ₂, hδ₂, h₂⟩ := Metric.mem_nhds_iff.mp
    (hcont2.preimage_mem_nhds (by rw [hv2]; exact hDo.mem_nhds hb))
  refine ⟨c, w, min δ₁ δ₂ / 2, by positivity, hw,
    IsManifold.chart_mem_maximalAtlas (I := Work.Noncompact.CompressionTube.MC n)
      (n := Work.Noncompact.CompressionTube.smoothOrder) b,
    mem_chart_source _ b, ?_, ?_⟩
  · intro t ht hte
    have hlt : t < δ₁ := by
      have := min_le_left δ₁ δ₂; linarith
    exact h₁ (by rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht]; exact hlt)
  · intro t ht hte
    have hlt : t < δ₂ := by
      have := min_le_right δ₁ δ₂; linarith
    exact h₂ (by rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht]; exact hlt)

end Work.Noncompact.Routing

